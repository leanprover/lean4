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
lean_object* v___x_1551_; lean_object* v_env_1552_; lean_object* v___x_1553_; lean_object* v_toCold_1554_; lean_object* v_mctx_1555_; lean_object* v_lctx_1556_; lean_object* v_options_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; 
v___x_1551_ = lean_st_ref_get(v___y_1549_);
v_env_1552_ = lean_ctor_get(v___x_1551_, 0);
lean_inc_ref(v_env_1552_);
lean_dec(v___x_1551_);
v___x_1553_ = lean_st_ref_get(v___y_1547_);
v_toCold_1554_ = lean_ctor_get(v___y_1548_, 0);
v_mctx_1555_ = lean_ctor_get(v___x_1553_, 0);
lean_inc_ref(v_mctx_1555_);
lean_dec(v___x_1553_);
v_lctx_1556_ = lean_ctor_get(v___y_1546_, 2);
v_options_1557_ = lean_ctor_get(v_toCold_1554_, 2);
lean_inc_ref(v_options_1557_);
lean_inc_ref(v_lctx_1556_);
v___x_1558_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1558_, 0, v_env_1552_);
lean_ctor_set(v___x_1558_, 1, v_mctx_1555_);
lean_ctor_set(v___x_1558_, 2, v_lctx_1556_);
lean_ctor_set(v___x_1558_, 3, v_options_1557_);
v___x_1559_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1559_, 0, v___x_1558_);
lean_ctor_set(v___x_1559_, 1, v_msgData_1545_);
v___x_1560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1560_, 0, v___x_1559_);
return v___x_1560_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq_spec__0_spec__0___boxed(lean_object* v_msgData_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_){
_start:
{
lean_object* v_res_1567_; 
v_res_1567_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq_spec__0_spec__0(v_msgData_1561_, v___y_1562_, v___y_1563_, v___y_1564_, v___y_1565_);
lean_dec(v___y_1565_);
lean_dec_ref(v___y_1564_);
lean_dec(v___y_1563_);
lean_dec_ref(v___y_1562_);
return v_res_1567_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq_spec__0___redArg(lean_object* v_msg_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_){
_start:
{
lean_object* v_ref_1574_; lean_object* v___x_1575_; lean_object* v_a_1576_; lean_object* v___x_1578_; uint8_t v_isShared_1579_; uint8_t v_isSharedCheck_1584_; 
v_ref_1574_ = lean_ctor_get(v___y_1571_, 2);
v___x_1575_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq_spec__0_spec__0(v_msg_1568_, v___y_1569_, v___y_1570_, v___y_1571_, v___y_1572_);
v_a_1576_ = lean_ctor_get(v___x_1575_, 0);
v_isSharedCheck_1584_ = !lean_is_exclusive(v___x_1575_);
if (v_isSharedCheck_1584_ == 0)
{
v___x_1578_ = v___x_1575_;
v_isShared_1579_ = v_isSharedCheck_1584_;
goto v_resetjp_1577_;
}
else
{
lean_inc(v_a_1576_);
lean_dec(v___x_1575_);
v___x_1578_ = lean_box(0);
v_isShared_1579_ = v_isSharedCheck_1584_;
goto v_resetjp_1577_;
}
v_resetjp_1577_:
{
lean_object* v___x_1580_; lean_object* v___x_1582_; 
lean_inc(v_ref_1574_);
v___x_1580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1580_, 0, v_ref_1574_);
lean_ctor_set(v___x_1580_, 1, v_a_1576_);
if (v_isShared_1579_ == 0)
{
lean_ctor_set_tag(v___x_1578_, 1);
lean_ctor_set(v___x_1578_, 0, v___x_1580_);
v___x_1582_ = v___x_1578_;
goto v_reusejp_1581_;
}
else
{
lean_object* v_reuseFailAlloc_1583_; 
v_reuseFailAlloc_1583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1583_, 0, v___x_1580_);
v___x_1582_ = v_reuseFailAlloc_1583_;
goto v_reusejp_1581_;
}
v_reusejp_1581_:
{
return v___x_1582_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq_spec__0___redArg___boxed(lean_object* v_msg_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_){
_start:
{
lean_object* v_res_1591_; 
v_res_1591_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq_spec__0___redArg(v_msg_1585_, v___y_1586_, v___y_1587_, v___y_1588_, v___y_1589_);
lean_dec(v___y_1589_);
lean_dec_ref(v___y_1588_);
lean_dec(v___y_1587_);
lean_dec_ref(v___y_1586_);
return v_res_1591_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq___closed__1(void){
_start:
{
lean_object* v___x_1593_; lean_object* v___x_1594_; 
v___x_1593_ = ((lean_object*)(l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq___closed__0));
v___x_1594_ = l_Lean_stringToMessageData(v___x_1593_);
return v___x_1594_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq___closed__3(void){
_start:
{
lean_object* v___x_1596_; lean_object* v___x_1597_; 
v___x_1596_ = ((lean_object*)(l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq___closed__2));
v___x_1597_ = l_Lean_stringToMessageData(v___x_1596_);
return v___x_1597_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq(lean_object* v_t_1598_, lean_object* v_s_1599_, lean_object* v_a_1600_, lean_object* v_a_1601_, lean_object* v_a_1602_, lean_object* v_a_1603_, lean_object* v_a_1604_, lean_object* v_a_1605_, lean_object* v_a_1606_, lean_object* v_a_1607_){
_start:
{
size_t v___x_1609_; size_t v___x_1610_; uint8_t v___x_1611_; 
v___x_1609_ = lean_ptr_addr(v_t_1598_);
v___x_1610_ = lean_ptr_addr(v_s_1599_);
v___x_1611_ = lean_usize_dec_eq(v___x_1609_, v___x_1610_);
if (v___x_1611_ == 0)
{
lean_object* v___x_1612_; 
lean_inc_ref(v_s_1599_);
lean_inc_ref(v_t_1598_);
v___x_1612_ = l_Lean_Meta_isExprDefEq(v_t_1598_, v_s_1599_, v_a_1604_, v_a_1605_, v_a_1606_, v_a_1607_);
if (lean_obj_tag(v___x_1612_) == 0)
{
lean_object* v_a_1613_; lean_object* v___x_1615_; uint8_t v_isShared_1616_; uint8_t v_isSharedCheck_1630_; 
v_a_1613_ = lean_ctor_get(v___x_1612_, 0);
v_isSharedCheck_1630_ = !lean_is_exclusive(v___x_1612_);
if (v_isSharedCheck_1630_ == 0)
{
v___x_1615_ = v___x_1612_;
v_isShared_1616_ = v_isSharedCheck_1630_;
goto v_resetjp_1614_;
}
else
{
lean_inc(v_a_1613_);
lean_dec(v___x_1612_);
v___x_1615_ = lean_box(0);
v_isShared_1616_ = v_isSharedCheck_1630_;
goto v_resetjp_1614_;
}
v_resetjp_1614_:
{
uint8_t v___x_1617_; 
v___x_1617_ = lean_unbox(v_a_1613_);
lean_dec(v_a_1613_);
if (v___x_1617_ == 0)
{
lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; 
lean_del_object(v___x_1615_);
v___x_1618_ = lean_obj_once(&l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq___closed__1, &l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq___closed__1_once, _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq___closed__1);
v___x_1619_ = l_Lean_indentExpr(v_t_1598_);
v___x_1620_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1620_, 0, v___x_1618_);
lean_ctor_set(v___x_1620_, 1, v___x_1619_);
v___x_1621_ = lean_obj_once(&l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq___closed__3, &l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq___closed__3_once, _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq___closed__3);
v___x_1622_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1622_, 0, v___x_1620_);
lean_ctor_set(v___x_1622_, 1, v___x_1621_);
v___x_1623_ = l_Lean_indentExpr(v_s_1599_);
v___x_1624_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1624_, 0, v___x_1622_);
lean_ctor_set(v___x_1624_, 1, v___x_1623_);
v___x_1625_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq_spec__0___redArg(v___x_1624_, v_a_1604_, v_a_1605_, v_a_1606_, v_a_1607_);
return v___x_1625_;
}
else
{
lean_object* v___x_1626_; lean_object* v___x_1628_; 
lean_dec_ref(v_s_1599_);
lean_dec_ref(v_t_1598_);
v___x_1626_ = lean_box(0);
if (v_isShared_1616_ == 0)
{
lean_ctor_set(v___x_1615_, 0, v___x_1626_);
v___x_1628_ = v___x_1615_;
goto v_reusejp_1627_;
}
else
{
lean_object* v_reuseFailAlloc_1629_; 
v_reuseFailAlloc_1629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1629_, 0, v___x_1626_);
v___x_1628_ = v_reuseFailAlloc_1629_;
goto v_reusejp_1627_;
}
v_reusejp_1627_:
{
return v___x_1628_;
}
}
}
}
else
{
lean_object* v_a_1631_; lean_object* v___x_1633_; uint8_t v_isShared_1634_; uint8_t v_isSharedCheck_1638_; 
lean_dec_ref(v_s_1599_);
lean_dec_ref(v_t_1598_);
v_a_1631_ = lean_ctor_get(v___x_1612_, 0);
v_isSharedCheck_1638_ = !lean_is_exclusive(v___x_1612_);
if (v_isSharedCheck_1638_ == 0)
{
v___x_1633_ = v___x_1612_;
v_isShared_1634_ = v_isSharedCheck_1638_;
goto v_resetjp_1632_;
}
else
{
lean_inc(v_a_1631_);
lean_dec(v___x_1612_);
v___x_1633_ = lean_box(0);
v_isShared_1634_ = v_isSharedCheck_1638_;
goto v_resetjp_1632_;
}
v_resetjp_1632_:
{
lean_object* v___x_1636_; 
if (v_isShared_1634_ == 0)
{
v___x_1636_ = v___x_1633_;
goto v_reusejp_1635_;
}
else
{
lean_object* v_reuseFailAlloc_1637_; 
v_reuseFailAlloc_1637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1637_, 0, v_a_1631_);
v___x_1636_ = v_reuseFailAlloc_1637_;
goto v_reusejp_1635_;
}
v_reusejp_1635_:
{
return v___x_1636_;
}
}
}
}
else
{
lean_object* v___x_1639_; lean_object* v___x_1640_; 
lean_dec_ref(v_s_1599_);
lean_dec_ref(v_t_1598_);
v___x_1639_ = lean_box(0);
v___x_1640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1640_, 0, v___x_1639_);
return v___x_1640_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq___boxed(lean_object* v_t_1641_, lean_object* v_s_1642_, lean_object* v_a_1643_, lean_object* v_a_1644_, lean_object* v_a_1645_, lean_object* v_a_1646_, lean_object* v_a_1647_, lean_object* v_a_1648_, lean_object* v_a_1649_, lean_object* v_a_1650_, lean_object* v_a_1651_){
_start:
{
lean_object* v_res_1652_; 
v_res_1652_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq(v_t_1641_, v_s_1642_, v_a_1643_, v_a_1644_, v_a_1645_, v_a_1646_, v_a_1647_, v_a_1648_, v_a_1649_, v_a_1650_);
lean_dec(v_a_1650_);
lean_dec_ref(v_a_1649_);
lean_dec(v_a_1648_);
lean_dec_ref(v_a_1647_);
lean_dec(v_a_1646_);
lean_dec_ref(v_a_1645_);
lean_dec(v_a_1644_);
lean_dec_ref(v_a_1643_);
return v_res_1652_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq_spec__0(lean_object* v_00_u03b1_1653_, lean_object* v_msg_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_){
_start:
{
lean_object* v___x_1664_; 
v___x_1664_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq_spec__0___redArg(v_msg_1654_, v___y_1659_, v___y_1660_, v___y_1661_, v___y_1662_);
return v___x_1664_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq_spec__0___boxed(lean_object* v_00_u03b1_1665_, lean_object* v_msg_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_){
_start:
{
lean_object* v_res_1676_; 
v_res_1676_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq_spec__0(v_00_u03b1_1665_, v_msg_1666_, v___y_1667_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_, v___y_1674_);
lean_dec(v___y_1674_);
lean_dec_ref(v___y_1673_);
lean_dec(v___y_1672_);
lean_dec_ref(v___y_1671_);
lean_dec(v___y_1670_);
lean_dec_ref(v___y_1669_);
lean_dec(v___y_1668_);
lean_dec_ref(v___y_1667_);
return v_res_1676_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_ensureForall___redArg___closed__1(void){
_start:
{
lean_object* v___x_1678_; lean_object* v___x_1679_; 
v___x_1678_ = ((lean_object*)(l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_ensureForall___redArg___closed__0));
v___x_1679_ = l_Lean_stringToMessageData(v___x_1678_);
return v___x_1679_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_ensureForall___redArg(lean_object* v_type_1680_, lean_object* v_a_1681_, lean_object* v_a_1682_, lean_object* v_a_1683_, lean_object* v_a_1684_, lean_object* v_a_1685_, lean_object* v_a_1686_){
_start:
{
uint8_t v___x_1688_; 
v___x_1688_ = l_Lean_Expr_isForall(v_type_1680_);
if (v___x_1688_ == 0)
{
lean_object* v___x_1689_; 
lean_inc(v_a_1686_);
lean_inc_ref(v_a_1685_);
lean_inc(v_a_1684_);
lean_inc_ref(v_a_1683_);
v___x_1689_ = lean_whnf(v_type_1680_, v_a_1683_, v_a_1684_, v_a_1685_, v_a_1686_);
if (lean_obj_tag(v___x_1689_) == 0)
{
lean_object* v_a_1690_; uint8_t v___x_1691_; 
v_a_1690_ = lean_ctor_get(v___x_1689_, 0);
lean_inc(v_a_1690_);
lean_dec_ref_known(v___x_1689_, 1);
v___x_1691_ = l_Lean_Expr_isForall(v_a_1690_);
if (v___x_1691_ == 0)
{
lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v_a_1696_; lean_object* v___x_1698_; uint8_t v_isShared_1699_; uint8_t v_isSharedCheck_1703_; 
v___x_1692_ = lean_obj_once(&l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_ensureForall___redArg___closed__1, &l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_ensureForall___redArg___closed__1_once, _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_ensureForall___redArg___closed__1);
v___x_1693_ = l_Lean_indentExpr(v_a_1690_);
v___x_1694_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1694_, 0, v___x_1692_);
lean_ctor_set(v___x_1694_, 1, v___x_1693_);
v___x_1695_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq_spec__0___redArg(v___x_1694_, v_a_1683_, v_a_1684_, v_a_1685_, v_a_1686_);
v_a_1696_ = lean_ctor_get(v___x_1695_, 0);
v_isSharedCheck_1703_ = !lean_is_exclusive(v___x_1695_);
if (v_isSharedCheck_1703_ == 0)
{
v___x_1698_ = v___x_1695_;
v_isShared_1699_ = v_isSharedCheck_1703_;
goto v_resetjp_1697_;
}
else
{
lean_inc(v_a_1696_);
lean_dec(v___x_1695_);
v___x_1698_ = lean_box(0);
v_isShared_1699_ = v_isSharedCheck_1703_;
goto v_resetjp_1697_;
}
v_resetjp_1697_:
{
lean_object* v___x_1701_; 
if (v_isShared_1699_ == 0)
{
v___x_1701_ = v___x_1698_;
goto v_reusejp_1700_;
}
else
{
lean_object* v_reuseFailAlloc_1702_; 
v_reuseFailAlloc_1702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1702_, 0, v_a_1696_);
v___x_1701_ = v_reuseFailAlloc_1702_;
goto v_reusejp_1700_;
}
v_reusejp_1700_:
{
return v___x_1701_;
}
}
}
else
{
lean_object* v___x_1704_; 
v___x_1704_ = l_Lean_Meta_Sym_shareCommon(v_a_1690_, v_a_1681_, v_a_1682_, v_a_1683_, v_a_1684_, v_a_1685_, v_a_1686_);
return v___x_1704_;
}
}
else
{
return v___x_1689_;
}
}
else
{
lean_object* v___x_1705_; 
v___x_1705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1705_, 0, v_type_1680_);
return v___x_1705_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_ensureForall___redArg___boxed(lean_object* v_type_1706_, lean_object* v_a_1707_, lean_object* v_a_1708_, lean_object* v_a_1709_, lean_object* v_a_1710_, lean_object* v_a_1711_, lean_object* v_a_1712_, lean_object* v_a_1713_){
_start:
{
lean_object* v_res_1714_; 
v_res_1714_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_ensureForall___redArg(v_type_1706_, v_a_1707_, v_a_1708_, v_a_1709_, v_a_1710_, v_a_1711_, v_a_1712_);
lean_dec(v_a_1712_);
lean_dec_ref(v_a_1711_);
lean_dec(v_a_1710_);
lean_dec_ref(v_a_1709_);
lean_dec(v_a_1708_);
lean_dec_ref(v_a_1707_);
return v_res_1714_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_ensureForall(lean_object* v_type_1715_, lean_object* v_a_1716_, lean_object* v_a_1717_, lean_object* v_a_1718_, lean_object* v_a_1719_, lean_object* v_a_1720_, lean_object* v_a_1721_, lean_object* v_a_1722_, lean_object* v_a_1723_){
_start:
{
lean_object* v___x_1725_; 
v___x_1725_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_ensureForall___redArg(v_type_1715_, v_a_1718_, v_a_1719_, v_a_1720_, v_a_1721_, v_a_1722_, v_a_1723_);
return v___x_1725_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_ensureForall___boxed(lean_object* v_type_1726_, lean_object* v_a_1727_, lean_object* v_a_1728_, lean_object* v_a_1729_, lean_object* v_a_1730_, lean_object* v_a_1731_, lean_object* v_a_1732_, lean_object* v_a_1733_, lean_object* v_a_1734_, lean_object* v_a_1735_){
_start:
{
lean_object* v_res_1736_; 
v_res_1736_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_ensureForall(v_type_1726_, v_a_1727_, v_a_1728_, v_a_1729_, v_a_1730_, v_a_1731_, v_a_1732_, v_a_1733_, v_a_1734_);
lean_dec(v_a_1734_);
lean_dec_ref(v_a_1733_);
lean_dec(v_a_1732_);
lean_dec_ref(v_a_1731_);
lean_dec(v_a_1730_);
lean_dec_ref(v_a_1729_);
lean_dec(v_a_1728_);
lean_dec_ref(v_a_1727_);
return v_res_1736_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_isClean(lean_object* v_e_1737_, lean_object* v_ctx_1738_){
_start:
{
lean_object* v_cleanSuffix_1739_; lean_object* v___x_1740_; uint8_t v___x_1741_; 
v_cleanSuffix_1739_ = lean_ctor_get(v_ctx_1738_, 2);
v___x_1740_ = l_Lean_Expr_looseBVarRange(v_e_1737_);
v___x_1741_ = lean_nat_dec_le(v___x_1740_, v_cleanSuffix_1739_);
lean_dec(v___x_1740_);
return v___x_1741_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_isClean___boxed(lean_object* v_e_1742_, lean_object* v_ctx_1743_){
_start:
{
uint8_t v_res_1744_; lean_object* v_r_1745_; 
v_res_1744_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_isClean(v_e_1742_, v_ctx_1743_);
lean_dec_ref(v_ctx_1743_);
lean_dec_ref(v_e_1742_);
v_r_1745_ = lean_box(v_res_1744_);
return v_r_1745_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeFallback(lean_object* v_e_1746_, lean_object* v_a_1747_, lean_object* v_a_1748_, lean_object* v_a_1749_, lean_object* v_a_1750_, lean_object* v_a_1751_, lean_object* v_a_1752_, lean_object* v_a_1753_, lean_object* v_a_1754_){
_start:
{
lean_object* v___x_1756_; 
v___x_1756_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv(v_e_1746_, v_a_1747_, v_a_1748_, v_a_1749_, v_a_1750_, v_a_1751_, v_a_1752_, v_a_1753_, v_a_1754_);
if (lean_obj_tag(v___x_1756_) == 0)
{
lean_object* v_a_1757_; lean_object* v_keyedConfig_1758_; uint8_t v_trackZetaDelta_1759_; lean_object* v_zetaDeltaSet_1760_; lean_object* v_lctx_1761_; lean_object* v_localInstances_1762_; lean_object* v_defEqCtx_x3f_1763_; lean_object* v_synthPendingDepth_1764_; lean_object* v_customCanUnfoldPredicate_x3f_1765_; uint8_t v_univApprox_1766_; uint8_t v_inTypeClassResolution_1767_; uint8_t v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; 
v_a_1757_ = lean_ctor_get(v___x_1756_, 0);
lean_inc(v_a_1757_);
lean_dec_ref_known(v___x_1756_, 1);
v_keyedConfig_1758_ = lean_ctor_get(v_a_1751_, 0);
v_trackZetaDelta_1759_ = lean_ctor_get_uint8(v_a_1751_, sizeof(void*)*7);
v_zetaDeltaSet_1760_ = lean_ctor_get(v_a_1751_, 1);
v_lctx_1761_ = lean_ctor_get(v_a_1751_, 2);
v_localInstances_1762_ = lean_ctor_get(v_a_1751_, 3);
v_defEqCtx_x3f_1763_ = lean_ctor_get(v_a_1751_, 4);
v_synthPendingDepth_1764_ = lean_ctor_get(v_a_1751_, 5);
v_customCanUnfoldPredicate_x3f_1765_ = lean_ctor_get(v_a_1751_, 6);
v_univApprox_1766_ = lean_ctor_get_uint8(v_a_1751_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1767_ = lean_ctor_get_uint8(v_a_1751_, sizeof(void*)*7 + 2);
v___x_1768_ = 0;
lean_inc(v_customCanUnfoldPredicate_x3f_1765_);
lean_inc(v_synthPendingDepth_1764_);
lean_inc(v_defEqCtx_x3f_1763_);
lean_inc_ref(v_localInstances_1762_);
lean_inc_ref(v_lctx_1761_);
lean_inc(v_zetaDeltaSet_1760_);
lean_inc_ref(v_keyedConfig_1758_);
v___x_1769_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1769_, 0, v_keyedConfig_1758_);
lean_ctor_set(v___x_1769_, 1, v_zetaDeltaSet_1760_);
lean_ctor_set(v___x_1769_, 2, v_lctx_1761_);
lean_ctor_set(v___x_1769_, 3, v_localInstances_1762_);
lean_ctor_set(v___x_1769_, 4, v_defEqCtx_x3f_1763_);
lean_ctor_set(v___x_1769_, 5, v_synthPendingDepth_1764_);
lean_ctor_set(v___x_1769_, 6, v_customCanUnfoldPredicate_x3f_1765_);
lean_ctor_set_uint8(v___x_1769_, sizeof(void*)*7, v_trackZetaDelta_1759_);
lean_ctor_set_uint8(v___x_1769_, sizeof(void*)*7 + 1, v_univApprox_1766_);
lean_ctor_set_uint8(v___x_1769_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1767_);
lean_ctor_set_uint8(v___x_1769_, sizeof(void*)*7 + 3, v___x_1768_);
lean_inc(v_a_1754_);
lean_inc_ref(v_a_1753_);
lean_inc(v_a_1752_);
v___x_1770_ = lean_infer_type(v_a_1757_, v___x_1769_, v_a_1752_, v_a_1753_, v_a_1754_);
if (lean_obj_tag(v___x_1770_) == 0)
{
lean_object* v_a_1771_; lean_object* v___x_1772_; 
v_a_1771_ = lean_ctor_get(v___x_1770_, 0);
lean_inc(v_a_1771_);
lean_dec_ref_known(v___x_1770_, 1);
v___x_1772_ = l_Lean_Meta_Sym_shareCommon(v_a_1771_, v_a_1749_, v_a_1750_, v_a_1751_, v_a_1752_, v_a_1753_, v_a_1754_);
return v___x_1772_;
}
else
{
return v___x_1770_;
}
}
else
{
return v___x_1756_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeFallback___boxed(lean_object* v_e_1773_, lean_object* v_a_1774_, lean_object* v_a_1775_, lean_object* v_a_1776_, lean_object* v_a_1777_, lean_object* v_a_1778_, lean_object* v_a_1779_, lean_object* v_a_1780_, lean_object* v_a_1781_, lean_object* v_a_1782_){
_start:
{
lean_object* v_res_1783_; 
v_res_1783_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeFallback(v_e_1773_, v_a_1774_, v_a_1775_, v_a_1776_, v_a_1777_, v_a_1778_, v_a_1779_, v_a_1780_, v_a_1781_);
lean_dec(v_a_1781_);
lean_dec_ref(v_a_1780_);
lean_dec(v_a_1779_);
lean_dec_ref(v_a_1778_);
lean_dec(v_a_1777_);
lean_dec_ref(v_a_1776_);
lean_dec(v_a_1775_);
lean_dec_ref(v_a_1774_);
return v_res_1783_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1784_; 
v___x_1784_ = l_instMonadEIO(lean_box(0));
return v___x_1784_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO_spec__0(lean_object* v_msg_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_){
_start:
{
lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v_toApplicative_1801_; lean_object* v___x_1803_; uint8_t v_isShared_1804_; uint8_t v_isSharedCheck_1866_; 
v___x_1799_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO_spec__0___closed__0, &l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO_spec__0___closed__0);
v___x_1800_ = l_StateRefT_x27_instMonad___redArg(v___x_1799_);
v_toApplicative_1801_ = lean_ctor_get(v___x_1800_, 0);
v_isSharedCheck_1866_ = !lean_is_exclusive(v___x_1800_);
if (v_isSharedCheck_1866_ == 0)
{
lean_object* v_unused_1867_; 
v_unused_1867_ = lean_ctor_get(v___x_1800_, 1);
lean_dec(v_unused_1867_);
v___x_1803_ = v___x_1800_;
v_isShared_1804_ = v_isSharedCheck_1866_;
goto v_resetjp_1802_;
}
else
{
lean_inc(v_toApplicative_1801_);
lean_dec(v___x_1800_);
v___x_1803_ = lean_box(0);
v_isShared_1804_ = v_isSharedCheck_1866_;
goto v_resetjp_1802_;
}
v_resetjp_1802_:
{
lean_object* v_toFunctor_1805_; lean_object* v_toSeq_1806_; lean_object* v_toSeqLeft_1807_; lean_object* v_toSeqRight_1808_; lean_object* v___x_1810_; uint8_t v_isShared_1811_; uint8_t v_isSharedCheck_1864_; 
v_toFunctor_1805_ = lean_ctor_get(v_toApplicative_1801_, 0);
v_toSeq_1806_ = lean_ctor_get(v_toApplicative_1801_, 2);
v_toSeqLeft_1807_ = lean_ctor_get(v_toApplicative_1801_, 3);
v_toSeqRight_1808_ = lean_ctor_get(v_toApplicative_1801_, 4);
v_isSharedCheck_1864_ = !lean_is_exclusive(v_toApplicative_1801_);
if (v_isSharedCheck_1864_ == 0)
{
lean_object* v_unused_1865_; 
v_unused_1865_ = lean_ctor_get(v_toApplicative_1801_, 1);
lean_dec(v_unused_1865_);
v___x_1810_ = v_toApplicative_1801_;
v_isShared_1811_ = v_isSharedCheck_1864_;
goto v_resetjp_1809_;
}
else
{
lean_inc(v_toSeqRight_1808_);
lean_inc(v_toSeqLeft_1807_);
lean_inc(v_toSeq_1806_);
lean_inc(v_toFunctor_1805_);
lean_dec(v_toApplicative_1801_);
v___x_1810_ = lean_box(0);
v_isShared_1811_ = v_isSharedCheck_1864_;
goto v_resetjp_1809_;
}
v_resetjp_1809_:
{
lean_object* v___f_1812_; lean_object* v___f_1813_; lean_object* v___f_1814_; lean_object* v___f_1815_; lean_object* v___x_1816_; lean_object* v___f_1817_; lean_object* v___f_1818_; lean_object* v___f_1819_; lean_object* v___x_1821_; 
v___f_1812_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO_spec__0___closed__1));
v___f_1813_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO_spec__0___closed__2));
lean_inc_ref(v_toFunctor_1805_);
v___f_1814_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1814_, 0, v_toFunctor_1805_);
v___f_1815_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1815_, 0, v_toFunctor_1805_);
v___x_1816_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1816_, 0, v___f_1814_);
lean_ctor_set(v___x_1816_, 1, v___f_1815_);
v___f_1817_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1817_, 0, v_toSeqRight_1808_);
v___f_1818_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1818_, 0, v_toSeqLeft_1807_);
v___f_1819_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1819_, 0, v_toSeq_1806_);
if (v_isShared_1811_ == 0)
{
lean_ctor_set(v___x_1810_, 4, v___f_1817_);
lean_ctor_set(v___x_1810_, 3, v___f_1818_);
lean_ctor_set(v___x_1810_, 2, v___f_1819_);
lean_ctor_set(v___x_1810_, 1, v___f_1812_);
lean_ctor_set(v___x_1810_, 0, v___x_1816_);
v___x_1821_ = v___x_1810_;
goto v_reusejp_1820_;
}
else
{
lean_object* v_reuseFailAlloc_1863_; 
v_reuseFailAlloc_1863_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1863_, 0, v___x_1816_);
lean_ctor_set(v_reuseFailAlloc_1863_, 1, v___f_1812_);
lean_ctor_set(v_reuseFailAlloc_1863_, 2, v___f_1819_);
lean_ctor_set(v_reuseFailAlloc_1863_, 3, v___f_1818_);
lean_ctor_set(v_reuseFailAlloc_1863_, 4, v___f_1817_);
v___x_1821_ = v_reuseFailAlloc_1863_;
goto v_reusejp_1820_;
}
v_reusejp_1820_:
{
lean_object* v___x_1823_; 
if (v_isShared_1804_ == 0)
{
lean_ctor_set(v___x_1803_, 1, v___f_1813_);
lean_ctor_set(v___x_1803_, 0, v___x_1821_);
v___x_1823_ = v___x_1803_;
goto v_reusejp_1822_;
}
else
{
lean_object* v_reuseFailAlloc_1862_; 
v_reuseFailAlloc_1862_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1862_, 0, v___x_1821_);
lean_ctor_set(v_reuseFailAlloc_1862_, 1, v___f_1813_);
v___x_1823_ = v_reuseFailAlloc_1862_;
goto v_reusejp_1822_;
}
v_reusejp_1822_:
{
lean_object* v___x_1824_; lean_object* v_toApplicative_1825_; lean_object* v___x_1827_; uint8_t v_isShared_1828_; uint8_t v_isSharedCheck_1860_; 
v___x_1824_ = l_StateRefT_x27_instMonad___redArg(v___x_1823_);
v_toApplicative_1825_ = lean_ctor_get(v___x_1824_, 0);
v_isSharedCheck_1860_ = !lean_is_exclusive(v___x_1824_);
if (v_isSharedCheck_1860_ == 0)
{
lean_object* v_unused_1861_; 
v_unused_1861_ = lean_ctor_get(v___x_1824_, 1);
lean_dec(v_unused_1861_);
v___x_1827_ = v___x_1824_;
v_isShared_1828_ = v_isSharedCheck_1860_;
goto v_resetjp_1826_;
}
else
{
lean_inc(v_toApplicative_1825_);
lean_dec(v___x_1824_);
v___x_1827_ = lean_box(0);
v_isShared_1828_ = v_isSharedCheck_1860_;
goto v_resetjp_1826_;
}
v_resetjp_1826_:
{
lean_object* v_toFunctor_1829_; lean_object* v_toSeq_1830_; lean_object* v_toSeqLeft_1831_; lean_object* v_toSeqRight_1832_; lean_object* v___x_1834_; uint8_t v_isShared_1835_; uint8_t v_isSharedCheck_1858_; 
v_toFunctor_1829_ = lean_ctor_get(v_toApplicative_1825_, 0);
v_toSeq_1830_ = lean_ctor_get(v_toApplicative_1825_, 2);
v_toSeqLeft_1831_ = lean_ctor_get(v_toApplicative_1825_, 3);
v_toSeqRight_1832_ = lean_ctor_get(v_toApplicative_1825_, 4);
v_isSharedCheck_1858_ = !lean_is_exclusive(v_toApplicative_1825_);
if (v_isSharedCheck_1858_ == 0)
{
lean_object* v_unused_1859_; 
v_unused_1859_ = lean_ctor_get(v_toApplicative_1825_, 1);
lean_dec(v_unused_1859_);
v___x_1834_ = v_toApplicative_1825_;
v_isShared_1835_ = v_isSharedCheck_1858_;
goto v_resetjp_1833_;
}
else
{
lean_inc(v_toSeqRight_1832_);
lean_inc(v_toSeqLeft_1831_);
lean_inc(v_toSeq_1830_);
lean_inc(v_toFunctor_1829_);
lean_dec(v_toApplicative_1825_);
v___x_1834_ = lean_box(0);
v_isShared_1835_ = v_isSharedCheck_1858_;
goto v_resetjp_1833_;
}
v_resetjp_1833_:
{
lean_object* v___f_1836_; lean_object* v___f_1837_; lean_object* v___f_1838_; lean_object* v___f_1839_; lean_object* v___x_1840_; lean_object* v___f_1841_; lean_object* v___f_1842_; lean_object* v___f_1843_; lean_object* v___x_1845_; 
v___f_1836_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO_spec__0___closed__3));
v___f_1837_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO_spec__0___closed__4));
lean_inc_ref(v_toFunctor_1829_);
v___f_1838_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1838_, 0, v_toFunctor_1829_);
v___f_1839_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1839_, 0, v_toFunctor_1829_);
v___x_1840_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1840_, 0, v___f_1838_);
lean_ctor_set(v___x_1840_, 1, v___f_1839_);
v___f_1841_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1841_, 0, v_toSeqRight_1832_);
v___f_1842_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1842_, 0, v_toSeqLeft_1831_);
v___f_1843_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1843_, 0, v_toSeq_1830_);
if (v_isShared_1835_ == 0)
{
lean_ctor_set(v___x_1834_, 4, v___f_1841_);
lean_ctor_set(v___x_1834_, 3, v___f_1842_);
lean_ctor_set(v___x_1834_, 2, v___f_1843_);
lean_ctor_set(v___x_1834_, 1, v___f_1836_);
lean_ctor_set(v___x_1834_, 0, v___x_1840_);
v___x_1845_ = v___x_1834_;
goto v_reusejp_1844_;
}
else
{
lean_object* v_reuseFailAlloc_1857_; 
v_reuseFailAlloc_1857_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1857_, 0, v___x_1840_);
lean_ctor_set(v_reuseFailAlloc_1857_, 1, v___f_1836_);
lean_ctor_set(v_reuseFailAlloc_1857_, 2, v___f_1843_);
lean_ctor_set(v_reuseFailAlloc_1857_, 3, v___f_1842_);
lean_ctor_set(v_reuseFailAlloc_1857_, 4, v___f_1841_);
v___x_1845_ = v_reuseFailAlloc_1857_;
goto v_reusejp_1844_;
}
v_reusejp_1844_:
{
lean_object* v___x_1847_; 
if (v_isShared_1828_ == 0)
{
lean_ctor_set(v___x_1827_, 1, v___f_1837_);
lean_ctor_set(v___x_1827_, 0, v___x_1845_);
v___x_1847_ = v___x_1827_;
goto v_reusejp_1846_;
}
else
{
lean_object* v_reuseFailAlloc_1856_; 
v_reuseFailAlloc_1856_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1856_, 0, v___x_1845_);
lean_ctor_set(v_reuseFailAlloc_1856_, 1, v___f_1837_);
v___x_1847_ = v_reuseFailAlloc_1856_;
goto v_reusejp_1846_;
}
v_reusejp_1846_:
{
lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___f_1853_; lean_object* v___x_11696__overap_1854_; lean_object* v___x_1855_; 
v___x_1848_ = l_StateRefT_x27_instMonad___redArg(v___x_1847_);
v___x_1849_ = l_ReaderT_instMonad___redArg(v___x_1848_);
v___x_1850_ = l_StateRefT_x27_instMonad___redArg(v___x_1849_);
v___x_1851_ = l_Lean_instInhabitedExpr;
v___x_1852_ = l_instInhabitedOfMonad___redArg(v___x_1850_, v___x_1851_);
v___f_1853_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1853_, 0, v___x_1852_);
v___x_11696__overap_1854_ = lean_panic_fn_borrowed(v___f_1853_, v_msg_1789_);
lean_dec_ref(v___f_1853_);
lean_inc(v___y_1797_);
lean_inc_ref(v___y_1796_);
lean_inc(v___y_1795_);
lean_inc_ref(v___y_1794_);
lean_inc(v___y_1793_);
lean_inc_ref(v___y_1792_);
lean_inc(v___y_1791_);
lean_inc_ref(v___y_1790_);
v___x_1855_ = lean_apply_9(v___x_11696__overap_1854_, v___y_1790_, v___y_1791_, v___y_1792_, v___y_1793_, v___y_1794_, v___y_1795_, v___y_1796_, v___y_1797_, lean_box(0));
return v___x_1855_;
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
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO_spec__0___boxed(lean_object* v_msg_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_){
_start:
{
lean_object* v_res_1878_; 
v_res_1878_ = l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO_spec__0(v_msg_1868_, v___y_1869_, v___y_1870_, v___y_1871_, v___y_1872_, v___y_1873_, v___y_1874_, v___y_1875_, v___y_1876_);
lean_dec(v___y_1876_);
lean_dec_ref(v___y_1875_);
lean_dec(v___y_1874_);
lean_dec_ref(v___y_1873_);
lean_dec(v___y_1872_);
lean_dec_ref(v___y_1871_);
lean_dec(v___y_1870_);
lean_dec_ref(v___y_1869_);
return v_res_1878_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO___closed__2(void){
_start:
{
lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; 
v___x_1881_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0___closed__2));
v___x_1882_ = lean_unsigned_to_nat(44u);
v___x_1883_ = lean_unsigned_to_nat(367u);
v___x_1884_ = ((lean_object*)(l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO___closed__1));
v___x_1885_ = ((lean_object*)(l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO___closed__0));
v___x_1886_ = l_mkPanicMessageWithDecl(v___x_1885_, v___x_1884_, v___x_1883_, v___x_1882_, v___x_1881_);
return v___x_1886_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO(lean_object* v_e_1887_, lean_object* v_a_1888_, lean_object* v_a_1889_, lean_object* v_a_1890_, lean_object* v_a_1891_, lean_object* v_a_1892_, lean_object* v_a_1893_, lean_object* v_a_1894_, lean_object* v_a_1895_){
_start:
{
lean_object* v_type_1898_; lean_object* v___y_1899_; uint8_t v___x_1917_; 
v___x_1917_ = l_Lean_Expr_hasLooseBVars(v_e_1887_);
if (v___x_1917_ == 0)
{
lean_object* v___x_1918_; 
v___x_1918_ = l_Lean_Meta_Sym_inferType(v_e_1887_, v_a_1890_, v_a_1891_, v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_);
return v___x_1918_;
}
else
{
lean_object* v___x_1919_; lean_object* v___y_1921_; lean_object* v_types_1925_; lean_object* v___x_1926_; 
v___x_1919_ = lean_st_ref_get(v_a_1889_);
v_types_1925_ = lean_ctor_get(v___x_1919_, 1);
lean_inc_ref(v_types_1925_);
lean_dec(v___x_1919_);
v___x_1926_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__0___redArg(v_types_1925_, v_e_1887_);
lean_dec_ref(v_types_1925_);
if (lean_obj_tag(v___x_1926_) == 1)
{
lean_object* v_val_1927_; lean_object* v___x_1929_; uint8_t v_isShared_1930_; uint8_t v_isSharedCheck_1934_; 
lean_dec_ref(v_e_1887_);
v_val_1927_ = lean_ctor_get(v___x_1926_, 0);
v_isSharedCheck_1934_ = !lean_is_exclusive(v___x_1926_);
if (v_isSharedCheck_1934_ == 0)
{
v___x_1929_ = v___x_1926_;
v_isShared_1930_ = v_isSharedCheck_1934_;
goto v_resetjp_1928_;
}
else
{
lean_inc(v_val_1927_);
lean_dec(v___x_1926_);
v___x_1929_ = lean_box(0);
v_isShared_1930_ = v_isSharedCheck_1934_;
goto v_resetjp_1928_;
}
v_resetjp_1928_:
{
lean_object* v___x_1932_; 
if (v_isShared_1930_ == 0)
{
lean_ctor_set_tag(v___x_1929_, 0);
v___x_1932_ = v___x_1929_;
goto v_reusejp_1931_;
}
else
{
lean_object* v_reuseFailAlloc_1933_; 
v_reuseFailAlloc_1933_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1933_, 0, v_val_1927_);
v___x_1932_ = v_reuseFailAlloc_1933_;
goto v_reusejp_1931_;
}
v_reusejp_1931_:
{
return v___x_1932_;
}
}
}
else
{
lean_dec(v___x_1926_);
switch(lean_obj_tag(v_e_1887_))
{
case 0:
{
lean_object* v_xs_1935_; lean_object* v_deBruijnIndex_1936_; lean_object* v_size_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; uint8_t v___x_1942_; 
v_xs_1935_ = lean_ctor_get(v_a_1888_, 0);
v_deBruijnIndex_1936_ = lean_ctor_get(v_e_1887_, 0);
v_size_1937_ = lean_ctor_get(v_xs_1935_, 2);
v___x_1938_ = l_Lean_instInhabitedExpr;
v___x_1939_ = lean_nat_sub(v_size_1937_, v_deBruijnIndex_1936_);
v___x_1940_ = lean_unsigned_to_nat(1u);
v___x_1941_ = lean_nat_sub(v___x_1939_, v___x_1940_);
lean_dec(v___x_1939_);
v___x_1942_ = lean_nat_dec_lt(v___x_1941_, v_size_1937_);
if (v___x_1942_ == 0)
{
lean_object* v___x_1943_; 
lean_dec(v___x_1941_);
v___x_1943_ = l_outOfBounds___redArg(v___x_1938_);
v___y_1921_ = v___x_1943_;
goto v___jp_1920_;
}
else
{
lean_object* v___x_1944_; 
v___x_1944_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1938_, v_xs_1935_, v___x_1941_);
lean_dec(v___x_1941_);
v___y_1921_ = v___x_1944_;
goto v___jp_1920_;
}
}
case 10:
{
lean_object* v_expr_1945_; lean_object* v___x_1946_; 
v_expr_1945_ = lean_ctor_get(v_e_1887_, 1);
lean_inc_ref(v_expr_1945_);
v___x_1946_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO(v_expr_1945_, v_a_1888_, v_a_1889_, v_a_1890_, v_a_1891_, v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_);
if (lean_obj_tag(v___x_1946_) == 0)
{
lean_object* v_a_1947_; 
v_a_1947_ = lean_ctor_get(v___x_1946_, 0);
lean_inc(v_a_1947_);
lean_dec_ref_known(v___x_1946_, 1);
v_type_1898_ = v_a_1947_;
v___y_1899_ = v_a_1889_;
goto v___jp_1897_;
}
else
{
lean_dec_ref_known(v_e_1887_, 2);
return v___x_1946_;
}
}
case 5:
{
lean_object* v_fn_1948_; lean_object* v_arg_1949_; lean_object* v___x_1950_; 
v_fn_1948_ = lean_ctor_get(v_e_1887_, 0);
v_arg_1949_ = lean_ctor_get(v_e_1887_, 1);
lean_inc_ref(v_fn_1948_);
v___x_1950_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO(v_fn_1948_, v_a_1888_, v_a_1889_, v_a_1890_, v_a_1891_, v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_);
if (lean_obj_tag(v___x_1950_) == 0)
{
lean_object* v_a_1951_; lean_object* v___x_1952_; 
v_a_1951_ = lean_ctor_get(v___x_1950_, 0);
lean_inc(v_a_1951_);
lean_dec_ref_known(v___x_1950_, 1);
v___x_1952_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_ensureForall___redArg(v_a_1951_, v_a_1890_, v_a_1891_, v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_);
if (lean_obj_tag(v___x_1952_) == 0)
{
lean_object* v_a_1953_; 
v_a_1953_ = lean_ctor_get(v___x_1952_, 0);
lean_inc(v_a_1953_);
lean_dec_ref_known(v___x_1952_, 1);
if (lean_obj_tag(v_a_1953_) == 7)
{
lean_object* v_body_1954_; uint8_t v___x_1955_; 
v_body_1954_ = lean_ctor_get(v_a_1953_, 2);
lean_inc_ref(v_body_1954_);
lean_dec_ref_known(v_a_1953_, 3);
v___x_1955_ = l_Lean_Expr_hasLooseBVars(v_body_1954_);
if (v___x_1955_ == 0)
{
v_type_1898_ = v_body_1954_;
v___y_1899_ = v_a_1889_;
goto v___jp_1897_;
}
else
{
lean_object* v___x_1956_; 
lean_inc_ref(v_arg_1949_);
v___x_1956_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv(v_arg_1949_, v_a_1888_, v_a_1889_, v_a_1890_, v_a_1891_, v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_);
if (lean_obj_tag(v___x_1956_) == 0)
{
lean_object* v_a_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; 
v_a_1957_ = lean_ctor_get(v___x_1956_, 0);
lean_inc(v_a_1957_);
lean_dec_ref_known(v___x_1956_, 1);
v___x_1958_ = lean_expr_instantiate1(v_body_1954_, v_a_1957_);
lean_dec(v_a_1957_);
lean_dec_ref(v_body_1954_);
v___x_1959_ = l_Lean_Meta_Sym_shareCommonInc(v___x_1958_, v_a_1890_, v_a_1891_, v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_);
if (lean_obj_tag(v___x_1959_) == 0)
{
lean_object* v_a_1960_; 
v_a_1960_ = lean_ctor_get(v___x_1959_, 0);
lean_inc(v_a_1960_);
lean_dec_ref_known(v___x_1959_, 1);
v_type_1898_ = v_a_1960_;
v___y_1899_ = v_a_1889_;
goto v___jp_1897_;
}
else
{
lean_dec_ref_known(v_e_1887_, 2);
return v___x_1959_;
}
}
else
{
lean_dec_ref(v_body_1954_);
lean_dec_ref_known(v_e_1887_, 2);
return v___x_1956_;
}
}
}
else
{
lean_object* v___x_1961_; lean_object* v___x_1962_; 
lean_dec(v_a_1953_);
v___x_1961_ = lean_obj_once(&l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO___closed__2, &l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO___closed__2_once, _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO___closed__2);
v___x_1962_ = l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO_spec__0(v___x_1961_, v_a_1888_, v_a_1889_, v_a_1890_, v_a_1891_, v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_);
if (lean_obj_tag(v___x_1962_) == 0)
{
lean_object* v_a_1963_; 
v_a_1963_ = lean_ctor_get(v___x_1962_, 0);
lean_inc(v_a_1963_);
lean_dec_ref_known(v___x_1962_, 1);
v_type_1898_ = v_a_1963_;
v___y_1899_ = v_a_1889_;
goto v___jp_1897_;
}
else
{
lean_dec_ref_known(v_e_1887_, 2);
return v___x_1962_;
}
}
}
else
{
lean_dec_ref_known(v_e_1887_, 2);
return v___x_1952_;
}
}
else
{
lean_dec_ref_known(v_e_1887_, 2);
return v___x_1950_;
}
}
default: 
{
lean_object* v___x_1964_; 
lean_inc_ref(v_e_1887_);
v___x_1964_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeFallback(v_e_1887_, v_a_1888_, v_a_1889_, v_a_1890_, v_a_1891_, v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_);
if (lean_obj_tag(v___x_1964_) == 0)
{
lean_object* v_a_1965_; 
v_a_1965_ = lean_ctor_get(v___x_1964_, 0);
lean_inc(v_a_1965_);
lean_dec_ref_known(v___x_1964_, 1);
v_type_1898_ = v_a_1965_;
v___y_1899_ = v_a_1889_;
goto v___jp_1897_;
}
else
{
lean_dec_ref(v_e_1887_);
return v___x_1964_;
}
}
}
}
v___jp_1920_:
{
lean_object* v_lctx_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; 
v_lctx_1922_ = lean_ctor_get(v_a_1892_, 2);
lean_inc_ref(v_lctx_1922_);
v___x_1923_ = l_Lean_LocalContext_getFVar_x21(v_lctx_1922_, v___y_1921_);
lean_dec_ref(v___y_1921_);
v___x_1924_ = l_Lean_LocalDecl_type(v___x_1923_);
lean_dec_ref(v___x_1923_);
v_type_1898_ = v___x_1924_;
v___y_1899_ = v_a_1889_;
goto v___jp_1897_;
}
}
v___jp_1897_:
{
lean_object* v___x_1900_; lean_object* v_visited_1901_; lean_object* v_types_1902_; lean_object* v_subst_1903_; lean_object* v_visitedClosed_1904_; lean_object* v_hasDepLetCache_1905_; lean_object* v_numConverted_1906_; lean_object* v___x_1908_; uint8_t v_isShared_1909_; uint8_t v_isSharedCheck_1916_; 
v___x_1900_ = lean_st_ref_take(v___y_1899_);
v_visited_1901_ = lean_ctor_get(v___x_1900_, 0);
v_types_1902_ = lean_ctor_get(v___x_1900_, 1);
v_subst_1903_ = lean_ctor_get(v___x_1900_, 2);
v_visitedClosed_1904_ = lean_ctor_get(v___x_1900_, 3);
v_hasDepLetCache_1905_ = lean_ctor_get(v___x_1900_, 4);
v_numConverted_1906_ = lean_ctor_get(v___x_1900_, 5);
v_isSharedCheck_1916_ = !lean_is_exclusive(v___x_1900_);
if (v_isSharedCheck_1916_ == 0)
{
v___x_1908_ = v___x_1900_;
v_isShared_1909_ = v_isSharedCheck_1916_;
goto v_resetjp_1907_;
}
else
{
lean_inc(v_numConverted_1906_);
lean_inc(v_hasDepLetCache_1905_);
lean_inc(v_visitedClosed_1904_);
lean_inc(v_subst_1903_);
lean_inc(v_types_1902_);
lean_inc(v_visited_1901_);
lean_dec(v___x_1900_);
v___x_1908_ = lean_box(0);
v_isShared_1909_ = v_isSharedCheck_1916_;
goto v_resetjp_1907_;
}
v_resetjp_1907_:
{
lean_object* v___x_1910_; lean_object* v___x_1912_; 
lean_inc_ref(v_type_1898_);
v___x_1910_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__1___redArg(v_types_1902_, v_e_1887_, v_type_1898_);
if (v_isShared_1909_ == 0)
{
lean_ctor_set(v___x_1908_, 1, v___x_1910_);
v___x_1912_ = v___x_1908_;
goto v_reusejp_1911_;
}
else
{
lean_object* v_reuseFailAlloc_1915_; 
v_reuseFailAlloc_1915_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1915_, 0, v_visited_1901_);
lean_ctor_set(v_reuseFailAlloc_1915_, 1, v___x_1910_);
lean_ctor_set(v_reuseFailAlloc_1915_, 2, v_subst_1903_);
lean_ctor_set(v_reuseFailAlloc_1915_, 3, v_visitedClosed_1904_);
lean_ctor_set(v_reuseFailAlloc_1915_, 4, v_hasDepLetCache_1905_);
lean_ctor_set(v_reuseFailAlloc_1915_, 5, v_numConverted_1906_);
v___x_1912_ = v_reuseFailAlloc_1915_;
goto v_reusejp_1911_;
}
v_reusejp_1911_:
{
lean_object* v___x_1913_; lean_object* v___x_1914_; 
v___x_1913_ = lean_st_ref_put(v___y_1899_, v___x_1912_);
v___x_1914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1914_, 0, v_type_1898_);
return v___x_1914_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO___boxed(lean_object* v_e_1966_, lean_object* v_a_1967_, lean_object* v_a_1968_, lean_object* v_a_1969_, lean_object* v_a_1970_, lean_object* v_a_1971_, lean_object* v_a_1972_, lean_object* v_a_1973_, lean_object* v_a_1974_, lean_object* v_a_1975_){
_start:
{
lean_object* v_res_1976_; 
v_res_1976_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO(v_e_1966_, v_a_1967_, v_a_1968_, v_a_1969_, v_a_1970_, v_a_1971_, v_a_1972_, v_a_1973_, v_a_1974_);
lean_dec(v_a_1974_);
lean_dec_ref(v_a_1973_);
lean_dec(v_a_1972_);
lean_dec_ref(v_a_1971_);
lean_dec(v_a_1970_);
lean_dec_ref(v_a_1969_);
lean_dec(v_a_1968_);
lean_dec_ref(v_a_1967_);
return v_res_1976_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__1___redArg(lean_object* v_fvarId_1977_, lean_object* v___y_1978_){
_start:
{
lean_object* v___x_1980_; lean_object* v___x_1981_; 
v___x_1980_ = l_Lean_Expr_fvar___override(v_fvarId_1977_);
v___x_1981_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_1980_, v___y_1978_);
return v___x_1981_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__1___redArg___boxed(lean_object* v_fvarId_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_){
_start:
{
lean_object* v_res_1985_; 
v_res_1985_ = l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__1___redArg(v_fvarId_1982_, v___y_1983_);
lean_dec(v___y_1983_);
return v_res_1985_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__1(lean_object* v_fvarId_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_){
_start:
{
lean_object* v___x_1996_; 
v___x_1996_ = l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__1___redArg(v_fvarId_1986_, v___y_1990_);
return v___x_1996_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__1___boxed(lean_object* v_fvarId_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_){
_start:
{
lean_object* v_res_2007_; 
v_res_2007_ = l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__1(v_fvarId_1997_, v___y_1998_, v___y_1999_, v___y_2000_, v___y_2001_, v___y_2002_, v___y_2003_, v___y_2004_, v___y_2005_);
lean_dec(v___y_2005_);
lean_dec_ref(v___y_2004_);
lean_dec(v___y_2003_);
lean_dec_ref(v___y_2002_);
lean_dec(v___y_2001_);
lean_dec_ref(v___y_2000_);
lean_dec(v___y_1999_);
lean_dec_ref(v___y_1998_);
return v_res_2007_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__2___redArg___lam__0(lean_object* v_x_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_){
_start:
{
lean_object* v___x_2018_; 
lean_inc(v___y_2012_);
lean_inc_ref(v___y_2011_);
lean_inc(v___y_2010_);
lean_inc_ref(v___y_2009_);
v___x_2018_ = lean_apply_9(v_x_2008_, v___y_2009_, v___y_2010_, v___y_2011_, v___y_2012_, v___y_2013_, v___y_2014_, v___y_2015_, v___y_2016_, lean_box(0));
return v___x_2018_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__2___redArg___lam__0___boxed(lean_object* v_x_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_){
_start:
{
lean_object* v_res_2029_; 
v_res_2029_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__2___redArg___lam__0(v_x_2019_, v___y_2020_, v___y_2021_, v___y_2022_, v___y_2023_, v___y_2024_, v___y_2025_, v___y_2026_, v___y_2027_);
lean_dec(v___y_2023_);
lean_dec_ref(v___y_2022_);
lean_dec(v___y_2021_);
lean_dec_ref(v___y_2020_);
return v_res_2029_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__2___redArg(lean_object* v_lctx_2030_, lean_object* v_localInsts_2031_, lean_object* v_x_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_){
_start:
{
lean_object* v___f_2042_; lean_object* v___x_2043_; 
lean_inc(v___y_2036_);
lean_inc_ref(v___y_2035_);
lean_inc(v___y_2034_);
lean_inc_ref(v___y_2033_);
v___f_2042_ = lean_alloc_closure((void*)(l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__2___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_2042_, 0, v_x_2032_);
lean_closure_set(v___f_2042_, 1, v___y_2033_);
lean_closure_set(v___f_2042_, 2, v___y_2034_);
lean_closure_set(v___f_2042_, 3, v___y_2035_);
lean_closure_set(v___f_2042_, 4, v___y_2036_);
v___x_2043_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_2030_, v_localInsts_2031_, v___f_2042_, v___y_2037_, v___y_2038_, v___y_2039_, v___y_2040_);
if (lean_obj_tag(v___x_2043_) == 0)
{
return v___x_2043_;
}
else
{
lean_object* v_a_2044_; lean_object* v___x_2046_; uint8_t v_isShared_2047_; uint8_t v_isSharedCheck_2051_; 
v_a_2044_ = lean_ctor_get(v___x_2043_, 0);
v_isSharedCheck_2051_ = !lean_is_exclusive(v___x_2043_);
if (v_isSharedCheck_2051_ == 0)
{
v___x_2046_ = v___x_2043_;
v_isShared_2047_ = v_isSharedCheck_2051_;
goto v_resetjp_2045_;
}
else
{
lean_inc(v_a_2044_);
lean_dec(v___x_2043_);
v___x_2046_ = lean_box(0);
v_isShared_2047_ = v_isSharedCheck_2051_;
goto v_resetjp_2045_;
}
v_resetjp_2045_:
{
lean_object* v___x_2049_; 
if (v_isShared_2047_ == 0)
{
v___x_2049_ = v___x_2046_;
goto v_reusejp_2048_;
}
else
{
lean_object* v_reuseFailAlloc_2050_; 
v_reuseFailAlloc_2050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2050_, 0, v_a_2044_);
v___x_2049_ = v_reuseFailAlloc_2050_;
goto v_reusejp_2048_;
}
v_reusejp_2048_:
{
return v___x_2049_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__2___redArg___boxed(lean_object* v_lctx_2052_, lean_object* v_localInsts_2053_, lean_object* v_x_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_){
_start:
{
lean_object* v_res_2064_; 
v_res_2064_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__2___redArg(v_lctx_2052_, v_localInsts_2053_, v_x_2054_, v___y_2055_, v___y_2056_, v___y_2057_, v___y_2058_, v___y_2059_, v___y_2060_, v___y_2061_, v___y_2062_);
lean_dec(v___y_2062_);
lean_dec_ref(v___y_2061_);
lean_dec(v___y_2060_);
lean_dec_ref(v___y_2059_);
lean_dec(v___y_2058_);
lean_dec_ref(v___y_2057_);
lean_dec(v___y_2056_);
lean_dec_ref(v___y_2055_);
return v_res_2064_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__2(lean_object* v_00_u03b1_2065_, lean_object* v_lctx_2066_, lean_object* v_localInsts_2067_, lean_object* v_x_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_){
_start:
{
lean_object* v___x_2078_; 
v___x_2078_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__2___redArg(v_lctx_2066_, v_localInsts_2067_, v_x_2068_, v___y_2069_, v___y_2070_, v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_, v___y_2076_);
return v___x_2078_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__2___boxed(lean_object* v_00_u03b1_2079_, lean_object* v_lctx_2080_, lean_object* v_localInsts_2081_, lean_object* v_x_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_){
_start:
{
lean_object* v_res_2092_; 
v_res_2092_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__2(v_00_u03b1_2079_, v_lctx_2080_, v_localInsts_2081_, v_x_2082_, v___y_2083_, v___y_2084_, v___y_2085_, v___y_2086_, v___y_2087_, v___y_2088_, v___y_2089_, v___y_2090_);
lean_dec(v___y_2090_);
lean_dec_ref(v___y_2089_);
lean_dec(v___y_2088_);
lean_dec_ref(v___y_2087_);
lean_dec(v___y_2086_);
lean_dec_ref(v___y_2085_);
lean_dec(v___y_2084_);
lean_dec_ref(v___y_2083_);
return v_res_2092_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder___redArg___lam__0(lean_object* v___y_2093_, lean_object* v_visited_2094_, lean_object* v_types_2095_, lean_object* v_subst_2096_, lean_object* v_a_x3f_2097_){
_start:
{
lean_object* v___x_2099_; lean_object* v_visitedClosed_2100_; lean_object* v_hasDepLetCache_2101_; lean_object* v_numConverted_2102_; lean_object* v___x_2104_; uint8_t v_isShared_2105_; uint8_t v_isSharedCheck_2112_; 
v___x_2099_ = lean_st_ref_take(v___y_2093_);
v_visitedClosed_2100_ = lean_ctor_get(v___x_2099_, 3);
v_hasDepLetCache_2101_ = lean_ctor_get(v___x_2099_, 4);
v_numConverted_2102_ = lean_ctor_get(v___x_2099_, 5);
v_isSharedCheck_2112_ = !lean_is_exclusive(v___x_2099_);
if (v_isSharedCheck_2112_ == 0)
{
lean_object* v_unused_2113_; lean_object* v_unused_2114_; lean_object* v_unused_2115_; 
v_unused_2113_ = lean_ctor_get(v___x_2099_, 2);
lean_dec(v_unused_2113_);
v_unused_2114_ = lean_ctor_get(v___x_2099_, 1);
lean_dec(v_unused_2114_);
v_unused_2115_ = lean_ctor_get(v___x_2099_, 0);
lean_dec(v_unused_2115_);
v___x_2104_ = v___x_2099_;
v_isShared_2105_ = v_isSharedCheck_2112_;
goto v_resetjp_2103_;
}
else
{
lean_inc(v_numConverted_2102_);
lean_inc(v_hasDepLetCache_2101_);
lean_inc(v_visitedClosed_2100_);
lean_dec(v___x_2099_);
v___x_2104_ = lean_box(0);
v_isShared_2105_ = v_isSharedCheck_2112_;
goto v_resetjp_2103_;
}
v_resetjp_2103_:
{
lean_object* v___x_2107_; 
if (v_isShared_2105_ == 0)
{
lean_ctor_set(v___x_2104_, 2, v_subst_2096_);
lean_ctor_set(v___x_2104_, 1, v_types_2095_);
lean_ctor_set(v___x_2104_, 0, v_visited_2094_);
v___x_2107_ = v___x_2104_;
goto v_reusejp_2106_;
}
else
{
lean_object* v_reuseFailAlloc_2111_; 
v_reuseFailAlloc_2111_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2111_, 0, v_visited_2094_);
lean_ctor_set(v_reuseFailAlloc_2111_, 1, v_types_2095_);
lean_ctor_set(v_reuseFailAlloc_2111_, 2, v_subst_2096_);
lean_ctor_set(v_reuseFailAlloc_2111_, 3, v_visitedClosed_2100_);
lean_ctor_set(v_reuseFailAlloc_2111_, 4, v_hasDepLetCache_2101_);
lean_ctor_set(v_reuseFailAlloc_2111_, 5, v_numConverted_2102_);
v___x_2107_ = v_reuseFailAlloc_2111_;
goto v_reusejp_2106_;
}
v_reusejp_2106_:
{
lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; 
v___x_2108_ = lean_st_ref_put(v___y_2093_, v___x_2107_);
v___x_2109_ = lean_box(0);
v___x_2110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2110_, 0, v___x_2109_);
return v___x_2110_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder___redArg___lam__0___boxed(lean_object* v___y_2116_, lean_object* v_visited_2117_, lean_object* v_types_2118_, lean_object* v_subst_2119_, lean_object* v_a_x3f_2120_, lean_object* v___y_2121_){
_start:
{
lean_object* v_res_2122_; 
v_res_2122_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder___redArg___lam__0(v___y_2116_, v_visited_2117_, v_types_2118_, v_subst_2119_, v_a_x3f_2120_);
lean_dec(v_a_x3f_2120_);
lean_dec(v___y_2116_);
return v_res_2122_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder___redArg___lam__1(lean_object* v_k_2123_, lean_object* v_a_2124_, uint8_t v_tainted_2125_, uint8_t v_isCandidate_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_){
_start:
{
lean_object* v___y_2137_; lean_object* v_xs_2183_; lean_object* v_numCandidates_2184_; lean_object* v_cleanSuffix_2185_; lean_object* v___x_2187_; uint8_t v_isShared_2188_; uint8_t v_isSharedCheck_2204_; 
v_xs_2183_ = lean_ctor_get(v___y_2127_, 0);
v_numCandidates_2184_ = lean_ctor_get(v___y_2127_, 1);
v_cleanSuffix_2185_ = lean_ctor_get(v___y_2127_, 2);
v_isSharedCheck_2204_ = !lean_is_exclusive(v___y_2127_);
if (v_isSharedCheck_2204_ == 0)
{
v___x_2187_ = v___y_2127_;
v_isShared_2188_ = v_isSharedCheck_2204_;
goto v_resetjp_2186_;
}
else
{
lean_inc(v_cleanSuffix_2185_);
lean_inc(v_numCandidates_2184_);
lean_inc(v_xs_2183_);
lean_dec(v___y_2127_);
v___x_2187_ = lean_box(0);
v_isShared_2188_ = v_isSharedCheck_2204_;
goto v_resetjp_2186_;
}
v___jp_2136_:
{
lean_object* v___x_2138_; lean_object* v_visited_2139_; lean_object* v_types_2140_; lean_object* v_subst_2141_; lean_object* v_visitedClosed_2142_; lean_object* v_hasDepLetCache_2143_; lean_object* v_numConverted_2144_; lean_object* v___x_2146_; uint8_t v_isShared_2147_; uint8_t v_isSharedCheck_2182_; 
v___x_2138_ = lean_st_ref_take(v___y_2128_);
v_visited_2139_ = lean_ctor_get(v___x_2138_, 0);
v_types_2140_ = lean_ctor_get(v___x_2138_, 1);
v_subst_2141_ = lean_ctor_get(v___x_2138_, 2);
v_visitedClosed_2142_ = lean_ctor_get(v___x_2138_, 3);
v_hasDepLetCache_2143_ = lean_ctor_get(v___x_2138_, 4);
v_numConverted_2144_ = lean_ctor_get(v___x_2138_, 5);
v_isSharedCheck_2182_ = !lean_is_exclusive(v___x_2138_);
if (v_isSharedCheck_2182_ == 0)
{
v___x_2146_ = v___x_2138_;
v_isShared_2147_ = v_isSharedCheck_2182_;
goto v_resetjp_2145_;
}
else
{
lean_inc(v_numConverted_2144_);
lean_inc(v_hasDepLetCache_2143_);
lean_inc(v_visitedClosed_2142_);
lean_inc(v_subst_2141_);
lean_inc(v_types_2140_);
lean_inc(v_visited_2139_);
lean_dec(v___x_2138_);
v___x_2146_ = lean_box(0);
v_isShared_2147_ = v_isSharedCheck_2182_;
goto v_resetjp_2145_;
}
v_resetjp_2145_:
{
lean_object* v___x_2148_; lean_object* v___x_2150_; 
v___x_2148_ = lean_obj_once(&l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withNewScope___redArg___closed__1, &l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withNewScope___redArg___closed__1_once, _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withNewScope___redArg___closed__1);
if (v_isShared_2147_ == 0)
{
lean_ctor_set(v___x_2146_, 2, v___x_2148_);
lean_ctor_set(v___x_2146_, 1, v___x_2148_);
lean_ctor_set(v___x_2146_, 0, v___x_2148_);
v___x_2150_ = v___x_2146_;
goto v_reusejp_2149_;
}
else
{
lean_object* v_reuseFailAlloc_2181_; 
v_reuseFailAlloc_2181_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2181_, 0, v___x_2148_);
lean_ctor_set(v_reuseFailAlloc_2181_, 1, v___x_2148_);
lean_ctor_set(v_reuseFailAlloc_2181_, 2, v___x_2148_);
lean_ctor_set(v_reuseFailAlloc_2181_, 3, v_visitedClosed_2142_);
lean_ctor_set(v_reuseFailAlloc_2181_, 4, v_hasDepLetCache_2143_);
lean_ctor_set(v_reuseFailAlloc_2181_, 5, v_numConverted_2144_);
v___x_2150_ = v_reuseFailAlloc_2181_;
goto v_reusejp_2149_;
}
v_reusejp_2149_:
{
lean_object* v___x_2151_; lean_object* v_r_2152_; 
v___x_2151_ = lean_st_ref_put(v___y_2128_, v___x_2150_);
lean_inc(v___y_2134_);
lean_inc_ref(v___y_2133_);
lean_inc(v___y_2132_);
lean_inc_ref(v___y_2131_);
lean_inc(v___y_2130_);
lean_inc_ref(v___y_2129_);
lean_inc(v___y_2128_);
v_r_2152_ = lean_apply_10(v_k_2123_, v_a_2124_, v___y_2137_, v___y_2128_, v___y_2129_, v___y_2130_, v___y_2131_, v___y_2132_, v___y_2133_, v___y_2134_, lean_box(0));
if (lean_obj_tag(v_r_2152_) == 0)
{
lean_object* v_a_2153_; lean_object* v___x_2155_; uint8_t v_isShared_2156_; uint8_t v_isSharedCheck_2169_; 
v_a_2153_ = lean_ctor_get(v_r_2152_, 0);
v_isSharedCheck_2169_ = !lean_is_exclusive(v_r_2152_);
if (v_isSharedCheck_2169_ == 0)
{
v___x_2155_ = v_r_2152_;
v_isShared_2156_ = v_isSharedCheck_2169_;
goto v_resetjp_2154_;
}
else
{
lean_inc(v_a_2153_);
lean_dec(v_r_2152_);
v___x_2155_ = lean_box(0);
v_isShared_2156_ = v_isSharedCheck_2169_;
goto v_resetjp_2154_;
}
v_resetjp_2154_:
{
lean_object* v___x_2158_; 
lean_inc(v_a_2153_);
if (v_isShared_2156_ == 0)
{
lean_ctor_set_tag(v___x_2155_, 1);
v___x_2158_ = v___x_2155_;
goto v_reusejp_2157_;
}
else
{
lean_object* v_reuseFailAlloc_2168_; 
v_reuseFailAlloc_2168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2168_, 0, v_a_2153_);
v___x_2158_ = v_reuseFailAlloc_2168_;
goto v_reusejp_2157_;
}
v_reusejp_2157_:
{
lean_object* v___x_2159_; lean_object* v___x_2161_; uint8_t v_isShared_2162_; uint8_t v_isSharedCheck_2166_; 
v___x_2159_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder___redArg___lam__0(v___y_2128_, v_visited_2139_, v_types_2140_, v_subst_2141_, v___x_2158_);
lean_dec_ref(v___x_2158_);
v_isSharedCheck_2166_ = !lean_is_exclusive(v___x_2159_);
if (v_isSharedCheck_2166_ == 0)
{
lean_object* v_unused_2167_; 
v_unused_2167_ = lean_ctor_get(v___x_2159_, 0);
lean_dec(v_unused_2167_);
v___x_2161_ = v___x_2159_;
v_isShared_2162_ = v_isSharedCheck_2166_;
goto v_resetjp_2160_;
}
else
{
lean_dec(v___x_2159_);
v___x_2161_ = lean_box(0);
v_isShared_2162_ = v_isSharedCheck_2166_;
goto v_resetjp_2160_;
}
v_resetjp_2160_:
{
lean_object* v___x_2164_; 
if (v_isShared_2162_ == 0)
{
lean_ctor_set(v___x_2161_, 0, v_a_2153_);
v___x_2164_ = v___x_2161_;
goto v_reusejp_2163_;
}
else
{
lean_object* v_reuseFailAlloc_2165_; 
v_reuseFailAlloc_2165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2165_, 0, v_a_2153_);
v___x_2164_ = v_reuseFailAlloc_2165_;
goto v_reusejp_2163_;
}
v_reusejp_2163_:
{
return v___x_2164_;
}
}
}
}
}
else
{
lean_object* v_a_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2174_; uint8_t v_isShared_2175_; uint8_t v_isSharedCheck_2179_; 
v_a_2170_ = lean_ctor_get(v_r_2152_, 0);
lean_inc(v_a_2170_);
lean_dec_ref_known(v_r_2152_, 1);
v___x_2171_ = lean_box(0);
v___x_2172_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder___redArg___lam__0(v___y_2128_, v_visited_2139_, v_types_2140_, v_subst_2141_, v___x_2171_);
v_isSharedCheck_2179_ = !lean_is_exclusive(v___x_2172_);
if (v_isSharedCheck_2179_ == 0)
{
lean_object* v_unused_2180_; 
v_unused_2180_ = lean_ctor_get(v___x_2172_, 0);
lean_dec(v_unused_2180_);
v___x_2174_ = v___x_2172_;
v_isShared_2175_ = v_isSharedCheck_2179_;
goto v_resetjp_2173_;
}
else
{
lean_dec(v___x_2172_);
v___x_2174_ = lean_box(0);
v_isShared_2175_ = v_isSharedCheck_2179_;
goto v_resetjp_2173_;
}
v_resetjp_2173_:
{
lean_object* v___x_2177_; 
if (v_isShared_2175_ == 0)
{
lean_ctor_set_tag(v___x_2174_, 1);
lean_ctor_set(v___x_2174_, 0, v_a_2170_);
v___x_2177_ = v___x_2174_;
goto v_reusejp_2176_;
}
else
{
lean_object* v_reuseFailAlloc_2178_; 
v_reuseFailAlloc_2178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2178_, 0, v_a_2170_);
v___x_2177_ = v_reuseFailAlloc_2178_;
goto v_reusejp_2176_;
}
v_reusejp_2176_:
{
return v___x_2177_;
}
}
}
}
}
}
v_resetjp_2186_:
{
lean_object* v___x_2189_; lean_object* v___y_2191_; 
lean_inc_ref(v_a_2124_);
v___x_2189_ = l_Lean_PersistentArray_push___redArg(v_xs_2183_, v_a_2124_);
if (v_isCandidate_2126_ == 0)
{
lean_object* v___x_2202_; 
v___x_2202_ = lean_unsigned_to_nat(0u);
v___y_2191_ = v___x_2202_;
goto v___jp_2190_;
}
else
{
lean_object* v___x_2203_; 
v___x_2203_ = lean_unsigned_to_nat(1u);
v___y_2191_ = v___x_2203_;
goto v___jp_2190_;
}
v___jp_2190_:
{
lean_object* v___x_2192_; 
v___x_2192_ = lean_nat_add(v_numCandidates_2184_, v___y_2191_);
lean_dec(v_numCandidates_2184_);
if (v_tainted_2125_ == 0)
{
lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2196_; 
v___x_2193_ = lean_unsigned_to_nat(1u);
v___x_2194_ = lean_nat_add(v_cleanSuffix_2185_, v___x_2193_);
lean_dec(v_cleanSuffix_2185_);
if (v_isShared_2188_ == 0)
{
lean_ctor_set(v___x_2187_, 2, v___x_2194_);
lean_ctor_set(v___x_2187_, 1, v___x_2192_);
lean_ctor_set(v___x_2187_, 0, v___x_2189_);
v___x_2196_ = v___x_2187_;
goto v_reusejp_2195_;
}
else
{
lean_object* v_reuseFailAlloc_2197_; 
v_reuseFailAlloc_2197_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2197_, 0, v___x_2189_);
lean_ctor_set(v_reuseFailAlloc_2197_, 1, v___x_2192_);
lean_ctor_set(v_reuseFailAlloc_2197_, 2, v___x_2194_);
v___x_2196_ = v_reuseFailAlloc_2197_;
goto v_reusejp_2195_;
}
v_reusejp_2195_:
{
v___y_2137_ = v___x_2196_;
goto v___jp_2136_;
}
}
else
{
lean_object* v___x_2198_; lean_object* v___x_2200_; 
lean_dec(v_cleanSuffix_2185_);
v___x_2198_ = lean_unsigned_to_nat(0u);
if (v_isShared_2188_ == 0)
{
lean_ctor_set(v___x_2187_, 2, v___x_2198_);
lean_ctor_set(v___x_2187_, 1, v___x_2192_);
lean_ctor_set(v___x_2187_, 0, v___x_2189_);
v___x_2200_ = v___x_2187_;
goto v_reusejp_2199_;
}
else
{
lean_object* v_reuseFailAlloc_2201_; 
v_reuseFailAlloc_2201_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2201_, 0, v___x_2189_);
lean_ctor_set(v_reuseFailAlloc_2201_, 1, v___x_2192_);
lean_ctor_set(v_reuseFailAlloc_2201_, 2, v___x_2198_);
v___x_2200_ = v_reuseFailAlloc_2201_;
goto v_reusejp_2199_;
}
v_reusejp_2199_:
{
v___y_2137_ = v___x_2200_;
goto v___jp_2136_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder___redArg___lam__1___boxed(lean_object* v_k_2205_, lean_object* v_a_2206_, lean_object* v_tainted_2207_, lean_object* v_isCandidate_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_){
_start:
{
uint8_t v_tainted_boxed_2218_; uint8_t v_isCandidate_boxed_2219_; lean_object* v_res_2220_; 
v_tainted_boxed_2218_ = lean_unbox(v_tainted_2207_);
v_isCandidate_boxed_2219_ = lean_unbox(v_isCandidate_2208_);
v_res_2220_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder___redArg___lam__1(v_k_2205_, v_a_2206_, v_tainted_boxed_2218_, v_isCandidate_boxed_2219_, v___y_2209_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_, v___y_2214_, v___y_2215_, v___y_2216_);
lean_dec(v___y_2216_);
lean_dec_ref(v___y_2215_);
lean_dec(v___y_2214_);
lean_dec_ref(v___y_2213_);
lean_dec(v___y_2212_);
lean_dec_ref(v___y_2211_);
lean_dec(v___y_2210_);
return v_res_2220_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__0_spec__0___redArg(lean_object* v___y_2221_){
_start:
{
lean_object* v___x_2223_; lean_object* v_ngen_2224_; lean_object* v_namePrefix_2225_; lean_object* v_idx_2226_; lean_object* v___x_2228_; uint8_t v_isShared_2229_; uint8_t v_isSharedCheck_2255_; 
v___x_2223_ = lean_st_ref_get(v___y_2221_);
v_ngen_2224_ = lean_ctor_get(v___x_2223_, 2);
lean_inc_ref(v_ngen_2224_);
lean_dec(v___x_2223_);
v_namePrefix_2225_ = lean_ctor_get(v_ngen_2224_, 0);
v_idx_2226_ = lean_ctor_get(v_ngen_2224_, 1);
v_isSharedCheck_2255_ = !lean_is_exclusive(v_ngen_2224_);
if (v_isSharedCheck_2255_ == 0)
{
v___x_2228_ = v_ngen_2224_;
v_isShared_2229_ = v_isSharedCheck_2255_;
goto v_resetjp_2227_;
}
else
{
lean_inc(v_idx_2226_);
lean_inc(v_namePrefix_2225_);
lean_dec(v_ngen_2224_);
v___x_2228_ = lean_box(0);
v_isShared_2229_ = v_isSharedCheck_2255_;
goto v_resetjp_2227_;
}
v_resetjp_2227_:
{
lean_object* v___x_2230_; lean_object* v_env_2231_; lean_object* v_nextMacroScope_2232_; lean_object* v_auxDeclNGen_2233_; lean_object* v_traceState_2234_; lean_object* v_cache_2235_; lean_object* v_messages_2236_; lean_object* v_infoState_2237_; lean_object* v_snapshotTasks_2238_; lean_object* v___x_2240_; uint8_t v_isShared_2241_; uint8_t v_isSharedCheck_2253_; 
v___x_2230_ = lean_st_ref_take(v___y_2221_);
v_env_2231_ = lean_ctor_get(v___x_2230_, 0);
v_nextMacroScope_2232_ = lean_ctor_get(v___x_2230_, 1);
v_auxDeclNGen_2233_ = lean_ctor_get(v___x_2230_, 3);
v_traceState_2234_ = lean_ctor_get(v___x_2230_, 4);
v_cache_2235_ = lean_ctor_get(v___x_2230_, 5);
v_messages_2236_ = lean_ctor_get(v___x_2230_, 6);
v_infoState_2237_ = lean_ctor_get(v___x_2230_, 7);
v_snapshotTasks_2238_ = lean_ctor_get(v___x_2230_, 8);
v_isSharedCheck_2253_ = !lean_is_exclusive(v___x_2230_);
if (v_isSharedCheck_2253_ == 0)
{
lean_object* v_unused_2254_; 
v_unused_2254_ = lean_ctor_get(v___x_2230_, 2);
lean_dec(v_unused_2254_);
v___x_2240_ = v___x_2230_;
v_isShared_2241_ = v_isSharedCheck_2253_;
goto v_resetjp_2239_;
}
else
{
lean_inc(v_snapshotTasks_2238_);
lean_inc(v_infoState_2237_);
lean_inc(v_messages_2236_);
lean_inc(v_cache_2235_);
lean_inc(v_traceState_2234_);
lean_inc(v_auxDeclNGen_2233_);
lean_inc(v_nextMacroScope_2232_);
lean_inc(v_env_2231_);
lean_dec(v___x_2230_);
v___x_2240_ = lean_box(0);
v_isShared_2241_ = v_isSharedCheck_2253_;
goto v_resetjp_2239_;
}
v_resetjp_2239_:
{
lean_object* v_r_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2246_; 
lean_inc(v_idx_2226_);
lean_inc(v_namePrefix_2225_);
v_r_2242_ = l_Lean_Name_num___override(v_namePrefix_2225_, v_idx_2226_);
v___x_2243_ = lean_unsigned_to_nat(1u);
v___x_2244_ = lean_nat_add(v_idx_2226_, v___x_2243_);
lean_dec(v_idx_2226_);
if (v_isShared_2229_ == 0)
{
lean_ctor_set(v___x_2228_, 1, v___x_2244_);
v___x_2246_ = v___x_2228_;
goto v_reusejp_2245_;
}
else
{
lean_object* v_reuseFailAlloc_2252_; 
v_reuseFailAlloc_2252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2252_, 0, v_namePrefix_2225_);
lean_ctor_set(v_reuseFailAlloc_2252_, 1, v___x_2244_);
v___x_2246_ = v_reuseFailAlloc_2252_;
goto v_reusejp_2245_;
}
v_reusejp_2245_:
{
lean_object* v___x_2248_; 
if (v_isShared_2241_ == 0)
{
lean_ctor_set(v___x_2240_, 2, v___x_2246_);
v___x_2248_ = v___x_2240_;
goto v_reusejp_2247_;
}
else
{
lean_object* v_reuseFailAlloc_2251_; 
v_reuseFailAlloc_2251_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2251_, 0, v_env_2231_);
lean_ctor_set(v_reuseFailAlloc_2251_, 1, v_nextMacroScope_2232_);
lean_ctor_set(v_reuseFailAlloc_2251_, 2, v___x_2246_);
lean_ctor_set(v_reuseFailAlloc_2251_, 3, v_auxDeclNGen_2233_);
lean_ctor_set(v_reuseFailAlloc_2251_, 4, v_traceState_2234_);
lean_ctor_set(v_reuseFailAlloc_2251_, 5, v_cache_2235_);
lean_ctor_set(v_reuseFailAlloc_2251_, 6, v_messages_2236_);
lean_ctor_set(v_reuseFailAlloc_2251_, 7, v_infoState_2237_);
lean_ctor_set(v_reuseFailAlloc_2251_, 8, v_snapshotTasks_2238_);
v___x_2248_ = v_reuseFailAlloc_2251_;
goto v_reusejp_2247_;
}
v_reusejp_2247_:
{
lean_object* v___x_2249_; lean_object* v___x_2250_; 
v___x_2249_ = lean_st_ref_put(v___y_2221_, v___x_2248_);
v___x_2250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2250_, 0, v_r_2242_);
return v___x_2250_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__0_spec__0___redArg___boxed(lean_object* v___y_2256_, lean_object* v___y_2257_){
_start:
{
lean_object* v_res_2258_; 
v_res_2258_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__0_spec__0___redArg(v___y_2256_);
lean_dec(v___y_2256_);
return v_res_2258_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__0(lean_object* v___y_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_){
_start:
{
lean_object* v___x_2268_; lean_object* v_a_2269_; lean_object* v___x_2271_; uint8_t v_isShared_2272_; uint8_t v_isSharedCheck_2276_; 
v___x_2268_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__0_spec__0___redArg(v___y_2266_);
v_a_2269_ = lean_ctor_get(v___x_2268_, 0);
v_isSharedCheck_2276_ = !lean_is_exclusive(v___x_2268_);
if (v_isSharedCheck_2276_ == 0)
{
v___x_2271_ = v___x_2268_;
v_isShared_2272_ = v_isSharedCheck_2276_;
goto v_resetjp_2270_;
}
else
{
lean_inc(v_a_2269_);
lean_dec(v___x_2268_);
v___x_2271_ = lean_box(0);
v_isShared_2272_ = v_isSharedCheck_2276_;
goto v_resetjp_2270_;
}
v_resetjp_2270_:
{
lean_object* v___x_2274_; 
if (v_isShared_2272_ == 0)
{
v___x_2274_ = v___x_2271_;
goto v_reusejp_2273_;
}
else
{
lean_object* v_reuseFailAlloc_2275_; 
v_reuseFailAlloc_2275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2275_, 0, v_a_2269_);
v___x_2274_ = v_reuseFailAlloc_2275_;
goto v_reusejp_2273_;
}
v_reusejp_2273_:
{
return v___x_2274_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__0___boxed(lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_){
_start:
{
lean_object* v_res_2286_; 
v_res_2286_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__0(v___y_2277_, v___y_2278_, v___y_2279_, v___y_2280_, v___y_2281_, v___y_2282_, v___y_2283_, v___y_2284_);
lean_dec(v___y_2284_);
lean_dec_ref(v___y_2283_);
lean_dec(v___y_2282_);
lean_dec_ref(v___y_2281_);
lean_dec(v___y_2280_);
lean_dec_ref(v___y_2279_);
lean_dec(v___y_2278_);
lean_dec_ref(v___y_2277_);
return v_res_2286_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder___redArg(lean_object* v_n_2289_, lean_object* v_type_2290_, lean_object* v_value_x3f_2291_, uint8_t v_tainted_2292_, uint8_t v_isCandidate_2293_, lean_object* v_k_2294_, lean_object* v_a_2295_, lean_object* v_a_2296_, lean_object* v_a_2297_, lean_object* v_a_2298_, lean_object* v_a_2299_, lean_object* v_a_2300_, lean_object* v_a_2301_, lean_object* v_a_2302_){
_start:
{
lean_object* v___x_2304_; 
v___x_2304_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__0(v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_, v_a_2301_, v_a_2302_);
if (lean_obj_tag(v___x_2304_) == 0)
{
lean_object* v_a_2305_; lean_object* v___x_2306_; 
v_a_2305_ = lean_ctor_get(v___x_2304_, 0);
lean_inc_n(v_a_2305_, 2);
lean_dec_ref_known(v___x_2304_, 1);
v___x_2306_ = l_Lean_Meta_Sym_Internal_mkFVarS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__1___redArg(v_a_2305_, v_a_2298_);
if (lean_obj_tag(v___x_2306_) == 0)
{
lean_object* v_a_2307_; lean_object* v_lctx_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___f_2311_; lean_object* v___y_2313_; 
v_a_2307_ = lean_ctor_get(v___x_2306_, 0);
lean_inc(v_a_2307_);
lean_dec_ref_known(v___x_2306_, 1);
v_lctx_2308_ = lean_ctor_get(v_a_2299_, 2);
v___x_2309_ = lean_box(v_tainted_2292_);
v___x_2310_ = lean_box(v_isCandidate_2293_);
v___f_2311_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder___redArg___lam__1___boxed), 13, 4);
lean_closure_set(v___f_2311_, 0, v_k_2294_);
lean_closure_set(v___f_2311_, 1, v_a_2307_);
lean_closure_set(v___f_2311_, 2, v___x_2309_);
lean_closure_set(v___f_2311_, 3, v___x_2310_);
if (lean_obj_tag(v_value_x3f_2291_) == 0)
{
uint8_t v___x_2316_; uint8_t v___x_2317_; lean_object* v___x_2318_; 
v___x_2316_ = 0;
v___x_2317_ = 0;
lean_inc_ref(v_lctx_2308_);
v___x_2318_ = l_Lean_LocalContext_mkLocalDecl(v_lctx_2308_, v_a_2305_, v_n_2289_, v_type_2290_, v___x_2316_, v___x_2317_);
v___y_2313_ = v___x_2318_;
goto v___jp_2312_;
}
else
{
lean_object* v_val_2319_; lean_object* v_fst_2320_; lean_object* v_snd_2321_; uint8_t v___x_2322_; uint8_t v___x_2323_; lean_object* v___x_2324_; 
v_val_2319_ = lean_ctor_get(v_value_x3f_2291_, 0);
lean_inc(v_val_2319_);
lean_dec_ref_known(v_value_x3f_2291_, 1);
v_fst_2320_ = lean_ctor_get(v_val_2319_, 0);
lean_inc(v_fst_2320_);
v_snd_2321_ = lean_ctor_get(v_val_2319_, 1);
lean_inc(v_snd_2321_);
lean_dec(v_val_2319_);
v___x_2322_ = 0;
v___x_2323_ = lean_unbox(v_snd_2321_);
lean_dec(v_snd_2321_);
lean_inc_ref(v_lctx_2308_);
v___x_2324_ = l_Lean_LocalContext_mkLetDecl(v_lctx_2308_, v_a_2305_, v_n_2289_, v_type_2290_, v_fst_2320_, v___x_2323_, v___x_2322_);
v___y_2313_ = v___x_2324_;
goto v___jp_2312_;
}
v___jp_2312_:
{
lean_object* v___x_2314_; lean_object* v___x_2315_; 
v___x_2314_ = ((lean_object*)(l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder___redArg___closed__0));
v___x_2315_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__2___redArg(v___y_2313_, v___x_2314_, v___f_2311_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_, v_a_2301_, v_a_2302_);
return v___x_2315_;
}
}
else
{
lean_object* v_a_2325_; lean_object* v___x_2327_; uint8_t v_isShared_2328_; uint8_t v_isSharedCheck_2332_; 
lean_dec(v_a_2305_);
lean_dec_ref(v_k_2294_);
lean_dec(v_value_x3f_2291_);
lean_dec_ref(v_type_2290_);
lean_dec(v_n_2289_);
v_a_2325_ = lean_ctor_get(v___x_2306_, 0);
v_isSharedCheck_2332_ = !lean_is_exclusive(v___x_2306_);
if (v_isSharedCheck_2332_ == 0)
{
v___x_2327_ = v___x_2306_;
v_isShared_2328_ = v_isSharedCheck_2332_;
goto v_resetjp_2326_;
}
else
{
lean_inc(v_a_2325_);
lean_dec(v___x_2306_);
v___x_2327_ = lean_box(0);
v_isShared_2328_ = v_isSharedCheck_2332_;
goto v_resetjp_2326_;
}
v_resetjp_2326_:
{
lean_object* v___x_2330_; 
if (v_isShared_2328_ == 0)
{
v___x_2330_ = v___x_2327_;
goto v_reusejp_2329_;
}
else
{
lean_object* v_reuseFailAlloc_2331_; 
v_reuseFailAlloc_2331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2331_, 0, v_a_2325_);
v___x_2330_ = v_reuseFailAlloc_2331_;
goto v_reusejp_2329_;
}
v_reusejp_2329_:
{
return v___x_2330_;
}
}
}
}
else
{
lean_object* v_a_2333_; lean_object* v___x_2335_; uint8_t v_isShared_2336_; uint8_t v_isSharedCheck_2340_; 
lean_dec_ref(v_k_2294_);
lean_dec(v_value_x3f_2291_);
lean_dec_ref(v_type_2290_);
lean_dec(v_n_2289_);
v_a_2333_ = lean_ctor_get(v___x_2304_, 0);
v_isSharedCheck_2340_ = !lean_is_exclusive(v___x_2304_);
if (v_isSharedCheck_2340_ == 0)
{
v___x_2335_ = v___x_2304_;
v_isShared_2336_ = v_isSharedCheck_2340_;
goto v_resetjp_2334_;
}
else
{
lean_inc(v_a_2333_);
lean_dec(v___x_2304_);
v___x_2335_ = lean_box(0);
v_isShared_2336_ = v_isSharedCheck_2340_;
goto v_resetjp_2334_;
}
v_resetjp_2334_:
{
lean_object* v___x_2338_; 
if (v_isShared_2336_ == 0)
{
v___x_2338_ = v___x_2335_;
goto v_reusejp_2337_;
}
else
{
lean_object* v_reuseFailAlloc_2339_; 
v_reuseFailAlloc_2339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2339_, 0, v_a_2333_);
v___x_2338_ = v_reuseFailAlloc_2339_;
goto v_reusejp_2337_;
}
v_reusejp_2337_:
{
return v___x_2338_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder___redArg___boxed(lean_object* v_n_2341_, lean_object* v_type_2342_, lean_object* v_value_x3f_2343_, lean_object* v_tainted_2344_, lean_object* v_isCandidate_2345_, lean_object* v_k_2346_, lean_object* v_a_2347_, lean_object* v_a_2348_, lean_object* v_a_2349_, lean_object* v_a_2350_, lean_object* v_a_2351_, lean_object* v_a_2352_, lean_object* v_a_2353_, lean_object* v_a_2354_, lean_object* v_a_2355_){
_start:
{
uint8_t v_tainted_boxed_2356_; uint8_t v_isCandidate_boxed_2357_; lean_object* v_res_2358_; 
v_tainted_boxed_2356_ = lean_unbox(v_tainted_2344_);
v_isCandidate_boxed_2357_ = lean_unbox(v_isCandidate_2345_);
v_res_2358_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder___redArg(v_n_2341_, v_type_2342_, v_value_x3f_2343_, v_tainted_boxed_2356_, v_isCandidate_boxed_2357_, v_k_2346_, v_a_2347_, v_a_2348_, v_a_2349_, v_a_2350_, v_a_2351_, v_a_2352_, v_a_2353_, v_a_2354_);
lean_dec(v_a_2354_);
lean_dec_ref(v_a_2353_);
lean_dec(v_a_2352_);
lean_dec_ref(v_a_2351_);
lean_dec(v_a_2350_);
lean_dec_ref(v_a_2349_);
lean_dec(v_a_2348_);
lean_dec_ref(v_a_2347_);
return v_res_2358_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder(lean_object* v_00_u03b1_2359_, lean_object* v_n_2360_, lean_object* v_type_2361_, lean_object* v_value_x3f_2362_, uint8_t v_tainted_2363_, uint8_t v_isCandidate_2364_, lean_object* v_k_2365_, lean_object* v_a_2366_, lean_object* v_a_2367_, lean_object* v_a_2368_, lean_object* v_a_2369_, lean_object* v_a_2370_, lean_object* v_a_2371_, lean_object* v_a_2372_, lean_object* v_a_2373_){
_start:
{
lean_object* v___x_2375_; 
v___x_2375_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder___redArg(v_n_2360_, v_type_2361_, v_value_x3f_2362_, v_tainted_2363_, v_isCandidate_2364_, v_k_2365_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_, v_a_2371_, v_a_2372_, v_a_2373_);
return v___x_2375_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder___boxed(lean_object* v_00_u03b1_2376_, lean_object* v_n_2377_, lean_object* v_type_2378_, lean_object* v_value_x3f_2379_, lean_object* v_tainted_2380_, lean_object* v_isCandidate_2381_, lean_object* v_k_2382_, lean_object* v_a_2383_, lean_object* v_a_2384_, lean_object* v_a_2385_, lean_object* v_a_2386_, lean_object* v_a_2387_, lean_object* v_a_2388_, lean_object* v_a_2389_, lean_object* v_a_2390_, lean_object* v_a_2391_){
_start:
{
uint8_t v_tainted_boxed_2392_; uint8_t v_isCandidate_boxed_2393_; lean_object* v_res_2394_; 
v_tainted_boxed_2392_ = lean_unbox(v_tainted_2380_);
v_isCandidate_boxed_2393_ = lean_unbox(v_isCandidate_2381_);
v_res_2394_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder(v_00_u03b1_2376_, v_n_2377_, v_type_2378_, v_value_x3f_2379_, v_tainted_boxed_2392_, v_isCandidate_boxed_2393_, v_k_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_, v_a_2387_, v_a_2388_, v_a_2389_, v_a_2390_);
lean_dec(v_a_2390_);
lean_dec_ref(v_a_2389_);
lean_dec(v_a_2388_);
lean_dec_ref(v_a_2387_);
lean_dec(v_a_2386_);
lean_dec_ref(v_a_2385_);
lean_dec(v_a_2384_);
lean_dec_ref(v_a_2383_);
return v_res_2394_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__0_spec__0(lean_object* v___y_2395_, lean_object* v___y_2396_, lean_object* v___y_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_){
_start:
{
lean_object* v___x_2404_; 
v___x_2404_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__0_spec__0___redArg(v___y_2402_);
return v___x_2404_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__0_spec__0___boxed(lean_object* v___y_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_){
_start:
{
lean_object* v_res_2414_; 
v_res_2414_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder_spec__0_spec__0(v___y_2405_, v___y_2406_, v___y_2407_, v___y_2408_, v___y_2409_, v___y_2410_, v___y_2411_, v___y_2412_);
lean_dec(v___y_2412_);
lean_dec_ref(v___y_2411_);
lean_dec(v___y_2410_);
lean_dec_ref(v___y_2409_);
lean_dec(v___y_2408_);
lean_dec_ref(v___y_2407_);
lean_dec(v___y_2406_);
lean_dec_ref(v___y_2405_);
return v_res_2414_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkFun_spec__0(lean_object* v_msg_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_){
_start:
{
lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v_toApplicative_2427_; lean_object* v___x_2429_; uint8_t v_isShared_2430_; uint8_t v_isSharedCheck_2492_; 
v___x_2425_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO_spec__0___closed__0, &l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO_spec__0___closed__0);
v___x_2426_ = l_StateRefT_x27_instMonad___redArg(v___x_2425_);
v_toApplicative_2427_ = lean_ctor_get(v___x_2426_, 0);
v_isSharedCheck_2492_ = !lean_is_exclusive(v___x_2426_);
if (v_isSharedCheck_2492_ == 0)
{
lean_object* v_unused_2493_; 
v_unused_2493_ = lean_ctor_get(v___x_2426_, 1);
lean_dec(v_unused_2493_);
v___x_2429_ = v___x_2426_;
v_isShared_2430_ = v_isSharedCheck_2492_;
goto v_resetjp_2428_;
}
else
{
lean_inc(v_toApplicative_2427_);
lean_dec(v___x_2426_);
v___x_2429_ = lean_box(0);
v_isShared_2430_ = v_isSharedCheck_2492_;
goto v_resetjp_2428_;
}
v_resetjp_2428_:
{
lean_object* v_toFunctor_2431_; lean_object* v_toSeq_2432_; lean_object* v_toSeqLeft_2433_; lean_object* v_toSeqRight_2434_; lean_object* v___x_2436_; uint8_t v_isShared_2437_; uint8_t v_isSharedCheck_2490_; 
v_toFunctor_2431_ = lean_ctor_get(v_toApplicative_2427_, 0);
v_toSeq_2432_ = lean_ctor_get(v_toApplicative_2427_, 2);
v_toSeqLeft_2433_ = lean_ctor_get(v_toApplicative_2427_, 3);
v_toSeqRight_2434_ = lean_ctor_get(v_toApplicative_2427_, 4);
v_isSharedCheck_2490_ = !lean_is_exclusive(v_toApplicative_2427_);
if (v_isSharedCheck_2490_ == 0)
{
lean_object* v_unused_2491_; 
v_unused_2491_ = lean_ctor_get(v_toApplicative_2427_, 1);
lean_dec(v_unused_2491_);
v___x_2436_ = v_toApplicative_2427_;
v_isShared_2437_ = v_isSharedCheck_2490_;
goto v_resetjp_2435_;
}
else
{
lean_inc(v_toSeqRight_2434_);
lean_inc(v_toSeqLeft_2433_);
lean_inc(v_toSeq_2432_);
lean_inc(v_toFunctor_2431_);
lean_dec(v_toApplicative_2427_);
v___x_2436_ = lean_box(0);
v_isShared_2437_ = v_isSharedCheck_2490_;
goto v_resetjp_2435_;
}
v_resetjp_2435_:
{
lean_object* v___f_2438_; lean_object* v___f_2439_; lean_object* v___f_2440_; lean_object* v___f_2441_; lean_object* v___x_2442_; lean_object* v___f_2443_; lean_object* v___f_2444_; lean_object* v___f_2445_; lean_object* v___x_2447_; 
v___f_2438_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO_spec__0___closed__1));
v___f_2439_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO_spec__0___closed__2));
lean_inc_ref(v_toFunctor_2431_);
v___f_2440_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2440_, 0, v_toFunctor_2431_);
v___f_2441_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2441_, 0, v_toFunctor_2431_);
v___x_2442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2442_, 0, v___f_2440_);
lean_ctor_set(v___x_2442_, 1, v___f_2441_);
v___f_2443_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2443_, 0, v_toSeqRight_2434_);
v___f_2444_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2444_, 0, v_toSeqLeft_2433_);
v___f_2445_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2445_, 0, v_toSeq_2432_);
if (v_isShared_2437_ == 0)
{
lean_ctor_set(v___x_2436_, 4, v___f_2443_);
lean_ctor_set(v___x_2436_, 3, v___f_2444_);
lean_ctor_set(v___x_2436_, 2, v___f_2445_);
lean_ctor_set(v___x_2436_, 1, v___f_2438_);
lean_ctor_set(v___x_2436_, 0, v___x_2442_);
v___x_2447_ = v___x_2436_;
goto v_reusejp_2446_;
}
else
{
lean_object* v_reuseFailAlloc_2489_; 
v_reuseFailAlloc_2489_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2489_, 0, v___x_2442_);
lean_ctor_set(v_reuseFailAlloc_2489_, 1, v___f_2438_);
lean_ctor_set(v_reuseFailAlloc_2489_, 2, v___f_2445_);
lean_ctor_set(v_reuseFailAlloc_2489_, 3, v___f_2444_);
lean_ctor_set(v_reuseFailAlloc_2489_, 4, v___f_2443_);
v___x_2447_ = v_reuseFailAlloc_2489_;
goto v_reusejp_2446_;
}
v_reusejp_2446_:
{
lean_object* v___x_2449_; 
if (v_isShared_2430_ == 0)
{
lean_ctor_set(v___x_2429_, 1, v___f_2439_);
lean_ctor_set(v___x_2429_, 0, v___x_2447_);
v___x_2449_ = v___x_2429_;
goto v_reusejp_2448_;
}
else
{
lean_object* v_reuseFailAlloc_2488_; 
v_reuseFailAlloc_2488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2488_, 0, v___x_2447_);
lean_ctor_set(v_reuseFailAlloc_2488_, 1, v___f_2439_);
v___x_2449_ = v_reuseFailAlloc_2488_;
goto v_reusejp_2448_;
}
v_reusejp_2448_:
{
lean_object* v___x_2450_; lean_object* v_toApplicative_2451_; lean_object* v___x_2453_; uint8_t v_isShared_2454_; uint8_t v_isSharedCheck_2486_; 
v___x_2450_ = l_StateRefT_x27_instMonad___redArg(v___x_2449_);
v_toApplicative_2451_ = lean_ctor_get(v___x_2450_, 0);
v_isSharedCheck_2486_ = !lean_is_exclusive(v___x_2450_);
if (v_isSharedCheck_2486_ == 0)
{
lean_object* v_unused_2487_; 
v_unused_2487_ = lean_ctor_get(v___x_2450_, 1);
lean_dec(v_unused_2487_);
v___x_2453_ = v___x_2450_;
v_isShared_2454_ = v_isSharedCheck_2486_;
goto v_resetjp_2452_;
}
else
{
lean_inc(v_toApplicative_2451_);
lean_dec(v___x_2450_);
v___x_2453_ = lean_box(0);
v_isShared_2454_ = v_isSharedCheck_2486_;
goto v_resetjp_2452_;
}
v_resetjp_2452_:
{
lean_object* v_toFunctor_2455_; lean_object* v_toSeq_2456_; lean_object* v_toSeqLeft_2457_; lean_object* v_toSeqRight_2458_; lean_object* v___x_2460_; uint8_t v_isShared_2461_; uint8_t v_isSharedCheck_2484_; 
v_toFunctor_2455_ = lean_ctor_get(v_toApplicative_2451_, 0);
v_toSeq_2456_ = lean_ctor_get(v_toApplicative_2451_, 2);
v_toSeqLeft_2457_ = lean_ctor_get(v_toApplicative_2451_, 3);
v_toSeqRight_2458_ = lean_ctor_get(v_toApplicative_2451_, 4);
v_isSharedCheck_2484_ = !lean_is_exclusive(v_toApplicative_2451_);
if (v_isSharedCheck_2484_ == 0)
{
lean_object* v_unused_2485_; 
v_unused_2485_ = lean_ctor_get(v_toApplicative_2451_, 1);
lean_dec(v_unused_2485_);
v___x_2460_ = v_toApplicative_2451_;
v_isShared_2461_ = v_isSharedCheck_2484_;
goto v_resetjp_2459_;
}
else
{
lean_inc(v_toSeqRight_2458_);
lean_inc(v_toSeqLeft_2457_);
lean_inc(v_toSeq_2456_);
lean_inc(v_toFunctor_2455_);
lean_dec(v_toApplicative_2451_);
v___x_2460_ = lean_box(0);
v_isShared_2461_ = v_isSharedCheck_2484_;
goto v_resetjp_2459_;
}
v_resetjp_2459_:
{
lean_object* v___f_2462_; lean_object* v___f_2463_; lean_object* v___f_2464_; lean_object* v___f_2465_; lean_object* v___x_2466_; lean_object* v___f_2467_; lean_object* v___f_2468_; lean_object* v___f_2469_; lean_object* v___x_2471_; 
v___f_2462_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO_spec__0___closed__3));
v___f_2463_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO_spec__0___closed__4));
lean_inc_ref(v_toFunctor_2455_);
v___f_2464_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2464_, 0, v_toFunctor_2455_);
v___f_2465_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2465_, 0, v_toFunctor_2455_);
v___x_2466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2466_, 0, v___f_2464_);
lean_ctor_set(v___x_2466_, 1, v___f_2465_);
v___f_2467_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2467_, 0, v_toSeqRight_2458_);
v___f_2468_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2468_, 0, v_toSeqLeft_2457_);
v___f_2469_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2469_, 0, v_toSeq_2456_);
if (v_isShared_2461_ == 0)
{
lean_ctor_set(v___x_2460_, 4, v___f_2467_);
lean_ctor_set(v___x_2460_, 3, v___f_2468_);
lean_ctor_set(v___x_2460_, 2, v___f_2469_);
lean_ctor_set(v___x_2460_, 1, v___f_2462_);
lean_ctor_set(v___x_2460_, 0, v___x_2466_);
v___x_2471_ = v___x_2460_;
goto v_reusejp_2470_;
}
else
{
lean_object* v_reuseFailAlloc_2483_; 
v_reuseFailAlloc_2483_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2483_, 0, v___x_2466_);
lean_ctor_set(v_reuseFailAlloc_2483_, 1, v___f_2462_);
lean_ctor_set(v_reuseFailAlloc_2483_, 2, v___f_2469_);
lean_ctor_set(v_reuseFailAlloc_2483_, 3, v___f_2468_);
lean_ctor_set(v_reuseFailAlloc_2483_, 4, v___f_2467_);
v___x_2471_ = v_reuseFailAlloc_2483_;
goto v_reusejp_2470_;
}
v_reusejp_2470_:
{
lean_object* v___x_2473_; 
if (v_isShared_2454_ == 0)
{
lean_ctor_set(v___x_2453_, 1, v___f_2463_);
lean_ctor_set(v___x_2453_, 0, v___x_2471_);
v___x_2473_ = v___x_2453_;
goto v_reusejp_2472_;
}
else
{
lean_object* v_reuseFailAlloc_2482_; 
v_reuseFailAlloc_2482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2482_, 0, v___x_2471_);
lean_ctor_set(v_reuseFailAlloc_2482_, 1, v___f_2463_);
v___x_2473_ = v_reuseFailAlloc_2482_;
goto v_reusejp_2472_;
}
v_reusejp_2472_:
{
lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___f_2479_; lean_object* v___x_5629__overap_2480_; lean_object* v___x_2481_; 
v___x_2474_ = l_StateRefT_x27_instMonad___redArg(v___x_2473_);
v___x_2475_ = l_ReaderT_instMonad___redArg(v___x_2474_);
v___x_2476_ = l_StateRefT_x27_instMonad___redArg(v___x_2475_);
v___x_2477_ = lean_box(0);
v___x_2478_ = l_instInhabitedOfMonad___redArg(v___x_2476_, v___x_2477_);
v___f_2479_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2479_, 0, v___x_2478_);
v___x_5629__overap_2480_ = lean_panic_fn_borrowed(v___f_2479_, v_msg_2415_);
lean_dec_ref(v___f_2479_);
lean_inc(v___y_2423_);
lean_inc_ref(v___y_2422_);
lean_inc(v___y_2421_);
lean_inc_ref(v___y_2420_);
lean_inc(v___y_2419_);
lean_inc_ref(v___y_2418_);
lean_inc(v___y_2417_);
lean_inc_ref(v___y_2416_);
v___x_2481_ = lean_apply_9(v___x_5629__overap_2480_, v___y_2416_, v___y_2417_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_, v___y_2422_, v___y_2423_, lean_box(0));
return v___x_2481_;
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
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkFun_spec__0___boxed(lean_object* v_msg_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_){
_start:
{
lean_object* v_res_2504_; 
v_res_2504_ = l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkFun_spec__0(v_msg_2494_, v___y_2495_, v___y_2496_, v___y_2497_, v___y_2498_, v___y_2499_, v___y_2500_, v___y_2501_, v___y_2502_);
lean_dec(v___y_2502_);
lean_dec_ref(v___y_2501_);
lean_dec(v___y_2500_);
lean_dec_ref(v___y_2499_);
lean_dec(v___y_2498_);
lean_dec_ref(v___y_2497_);
lean_dec(v___y_2496_);
lean_dec_ref(v___y_2495_);
return v_res_2504_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkFun___lam__0___boxed(lean_object* v_body_2505_, lean_object* v_body_2506_, lean_object* v_x_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_){
_start:
{
lean_object* v_res_2517_; 
v_res_2517_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkFun___lam__0(v_body_2505_, v_body_2506_, v_x_2507_, v___y_2508_, v___y_2509_, v___y_2510_, v___y_2511_, v___y_2512_, v___y_2513_, v___y_2514_, v___y_2515_);
lean_dec(v___y_2515_);
lean_dec_ref(v___y_2514_);
lean_dec(v___y_2513_);
lean_dec_ref(v___y_2512_);
lean_dec(v___y_2511_);
lean_dec_ref(v___y_2510_);
lean_dec(v___y_2509_);
lean_dec_ref(v___y_2508_);
lean_dec_ref(v_x_2507_);
return v_res_2517_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkFun___closed__1(void){
_start:
{
lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; 
v___x_2519_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0___closed__2));
v___x_2520_ = lean_unsigned_to_nat(42u);
v___x_2521_ = lean_unsigned_to_nat(340u);
v___x_2522_ = ((lean_object*)(l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkFun___closed__0));
v___x_2523_ = ((lean_object*)(l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO___closed__0));
v___x_2524_ = l_mkPanicMessageWithDecl(v___x_2523_, v___x_2522_, v___x_2521_, v___x_2520_, v___x_2519_);
return v___x_2524_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkFun(lean_object* v_e_2525_, lean_object* v_expected_2526_, lean_object* v_a_2527_, lean_object* v_a_2528_, lean_object* v_a_2529_, lean_object* v_a_2530_, lean_object* v_a_2531_, lean_object* v_a_2532_, lean_object* v_a_2533_, lean_object* v_a_2534_){
_start:
{
if (lean_obj_tag(v_e_2525_) == 6)
{
lean_object* v_binderName_2536_; lean_object* v_binderType_2537_; lean_object* v_body_2538_; lean_object* v___x_2539_; 
v_binderName_2536_ = lean_ctor_get(v_e_2525_, 0);
lean_inc(v_binderName_2536_);
v_binderType_2537_ = lean_ctor_get(v_e_2525_, 1);
lean_inc_ref(v_binderType_2537_);
v_body_2538_ = lean_ctor_get(v_e_2525_, 2);
lean_inc_ref(v_body_2538_);
lean_dec_ref_known(v_e_2525_, 3);
v___x_2539_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_ensureForall___redArg(v_expected_2526_, v_a_2529_, v_a_2530_, v_a_2531_, v_a_2532_, v_a_2533_, v_a_2534_);
if (lean_obj_tag(v___x_2539_) == 0)
{
lean_object* v_a_2540_; 
v_a_2540_ = lean_ctor_get(v___x_2539_, 0);
lean_inc(v_a_2540_);
lean_dec_ref_known(v___x_2539_, 1);
if (lean_obj_tag(v_a_2540_) == 7)
{
lean_object* v_binderType_2541_; lean_object* v_body_2542_; lean_object* v___x_2543_; 
v_binderType_2541_ = lean_ctor_get(v_a_2540_, 1);
lean_inc_ref(v_binderType_2541_);
v_body_2542_ = lean_ctor_get(v_a_2540_, 2);
lean_inc_ref(v_body_2542_);
lean_dec_ref_known(v_a_2540_, 3);
lean_inc_ref(v_binderType_2537_);
v___x_2543_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv(v_binderType_2537_, v_a_2527_, v_a_2528_, v_a_2529_, v_a_2530_, v_a_2531_, v_a_2532_, v_a_2533_, v_a_2534_);
if (lean_obj_tag(v___x_2543_) == 0)
{
lean_object* v_a_2544_; lean_object* v___x_2545_; 
v_a_2544_ = lean_ctor_get(v___x_2543_, 0);
lean_inc_n(v_a_2544_, 2);
lean_dec_ref_known(v___x_2543_, 1);
v___x_2545_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq(v_a_2544_, v_binderType_2541_, v_a_2527_, v_a_2528_, v_a_2529_, v_a_2530_, v_a_2531_, v_a_2532_, v_a_2533_, v_a_2534_);
if (lean_obj_tag(v___x_2545_) == 0)
{
lean_object* v_cleanSuffix_2546_; lean_object* v___f_2547_; lean_object* v___x_2548_; uint8_t v___y_2550_; lean_object* v___x_2553_; uint8_t v___x_2554_; 
lean_dec_ref_known(v___x_2545_, 1);
v_cleanSuffix_2546_ = lean_ctor_get(v_a_2527_, 2);
v___f_2547_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkFun___lam__0___boxed), 12, 2);
lean_closure_set(v___f_2547_, 0, v_body_2542_);
lean_closure_set(v___f_2547_, 1, v_body_2538_);
v___x_2548_ = lean_box(0);
v___x_2553_ = l_Lean_Expr_looseBVarRange(v_binderType_2537_);
lean_dec_ref(v_binderType_2537_);
v___x_2554_ = lean_nat_dec_le(v___x_2553_, v_cleanSuffix_2546_);
lean_dec(v___x_2553_);
if (v___x_2554_ == 0)
{
uint8_t v___x_2555_; 
v___x_2555_ = 1;
v___y_2550_ = v___x_2555_;
goto v___jp_2549_;
}
else
{
uint8_t v___x_2556_; 
v___x_2556_ = 0;
v___y_2550_ = v___x_2556_;
goto v___jp_2549_;
}
v___jp_2549_:
{
uint8_t v___x_2551_; lean_object* v___x_2552_; 
v___x_2551_ = 0;
v___x_2552_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder___redArg(v_binderName_2536_, v_a_2544_, v___x_2548_, v___y_2550_, v___x_2551_, v___f_2547_, v_a_2527_, v_a_2528_, v_a_2529_, v_a_2530_, v_a_2531_, v_a_2532_, v_a_2533_, v_a_2534_);
return v___x_2552_;
}
}
else
{
lean_dec(v_a_2544_);
lean_dec_ref(v_body_2542_);
lean_dec_ref(v_body_2538_);
lean_dec_ref(v_binderType_2537_);
lean_dec(v_binderName_2536_);
return v___x_2545_;
}
}
else
{
lean_object* v_a_2557_; lean_object* v___x_2559_; uint8_t v_isShared_2560_; uint8_t v_isSharedCheck_2564_; 
lean_dec_ref(v_body_2542_);
lean_dec_ref(v_binderType_2541_);
lean_dec_ref(v_body_2538_);
lean_dec_ref(v_binderType_2537_);
lean_dec(v_binderName_2536_);
v_a_2557_ = lean_ctor_get(v___x_2543_, 0);
v_isSharedCheck_2564_ = !lean_is_exclusive(v___x_2543_);
if (v_isSharedCheck_2564_ == 0)
{
v___x_2559_ = v___x_2543_;
v_isShared_2560_ = v_isSharedCheck_2564_;
goto v_resetjp_2558_;
}
else
{
lean_inc(v_a_2557_);
lean_dec(v___x_2543_);
v___x_2559_ = lean_box(0);
v_isShared_2560_ = v_isSharedCheck_2564_;
goto v_resetjp_2558_;
}
v_resetjp_2558_:
{
lean_object* v___x_2562_; 
if (v_isShared_2560_ == 0)
{
v___x_2562_ = v___x_2559_;
goto v_reusejp_2561_;
}
else
{
lean_object* v_reuseFailAlloc_2563_; 
v_reuseFailAlloc_2563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2563_, 0, v_a_2557_);
v___x_2562_ = v_reuseFailAlloc_2563_;
goto v_reusejp_2561_;
}
v_reusejp_2561_:
{
return v___x_2562_;
}
}
}
}
else
{
lean_object* v___x_2565_; lean_object* v___x_2566_; 
lean_dec(v_a_2540_);
lean_dec_ref(v_body_2538_);
lean_dec_ref(v_binderType_2537_);
lean_dec(v_binderName_2536_);
v___x_2565_ = lean_obj_once(&l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkFun___closed__1, &l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkFun___closed__1_once, _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkFun___closed__1);
v___x_2566_ = l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkFun_spec__0(v___x_2565_, v_a_2527_, v_a_2528_, v_a_2529_, v_a_2530_, v_a_2531_, v_a_2532_, v_a_2533_, v_a_2534_);
return v___x_2566_;
}
}
else
{
lean_object* v_a_2567_; lean_object* v___x_2569_; uint8_t v_isShared_2570_; uint8_t v_isSharedCheck_2574_; 
lean_dec_ref(v_body_2538_);
lean_dec_ref(v_binderType_2537_);
lean_dec(v_binderName_2536_);
v_a_2567_ = lean_ctor_get(v___x_2539_, 0);
v_isSharedCheck_2574_ = !lean_is_exclusive(v___x_2539_);
if (v_isSharedCheck_2574_ == 0)
{
v___x_2569_ = v___x_2539_;
v_isShared_2570_ = v_isSharedCheck_2574_;
goto v_resetjp_2568_;
}
else
{
lean_inc(v_a_2567_);
lean_dec(v___x_2539_);
v___x_2569_ = lean_box(0);
v_isShared_2570_ = v_isSharedCheck_2574_;
goto v_resetjp_2568_;
}
v_resetjp_2568_:
{
lean_object* v___x_2572_; 
if (v_isShared_2570_ == 0)
{
v___x_2572_ = v___x_2569_;
goto v_reusejp_2571_;
}
else
{
lean_object* v_reuseFailAlloc_2573_; 
v_reuseFailAlloc_2573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2573_, 0, v_a_2567_);
v___x_2572_ = v_reuseFailAlloc_2573_;
goto v_reusejp_2571_;
}
v_reusejp_2571_:
{
return v___x_2572_;
}
}
}
}
else
{
lean_object* v___x_2575_; 
v___x_2575_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO(v_e_2525_, v_a_2527_, v_a_2528_, v_a_2529_, v_a_2530_, v_a_2531_, v_a_2532_, v_a_2533_, v_a_2534_);
if (lean_obj_tag(v___x_2575_) == 0)
{
lean_object* v_a_2576_; lean_object* v___x_2577_; 
v_a_2576_ = lean_ctor_get(v___x_2575_, 0);
lean_inc(v_a_2576_);
lean_dec_ref_known(v___x_2575_, 1);
v___x_2577_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq(v_a_2576_, v_expected_2526_, v_a_2527_, v_a_2528_, v_a_2529_, v_a_2530_, v_a_2531_, v_a_2532_, v_a_2533_, v_a_2534_);
return v___x_2577_;
}
else
{
lean_object* v_a_2578_; lean_object* v___x_2580_; uint8_t v_isShared_2581_; uint8_t v_isSharedCheck_2585_; 
lean_dec_ref(v_expected_2526_);
v_a_2578_ = lean_ctor_get(v___x_2575_, 0);
v_isSharedCheck_2585_ = !lean_is_exclusive(v___x_2575_);
if (v_isSharedCheck_2585_ == 0)
{
v___x_2580_ = v___x_2575_;
v_isShared_2581_ = v_isSharedCheck_2585_;
goto v_resetjp_2579_;
}
else
{
lean_inc(v_a_2578_);
lean_dec(v___x_2575_);
v___x_2580_ = lean_box(0);
v_isShared_2581_ = v_isSharedCheck_2585_;
goto v_resetjp_2579_;
}
v_resetjp_2579_:
{
lean_object* v___x_2583_; 
if (v_isShared_2581_ == 0)
{
v___x_2583_ = v___x_2580_;
goto v_reusejp_2582_;
}
else
{
lean_object* v_reuseFailAlloc_2584_; 
v_reuseFailAlloc_2584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2584_, 0, v_a_2578_);
v___x_2583_ = v_reuseFailAlloc_2584_;
goto v_reusejp_2582_;
}
v_reusejp_2582_:
{
return v___x_2583_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkFun___lam__0(lean_object* v_body_2586_, lean_object* v_body_2587_, lean_object* v_x_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_, lean_object* v___y_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_){
_start:
{
uint8_t v___x_2598_; 
v___x_2598_ = l_Lean_Expr_hasLooseBVars(v_body_2586_);
if (v___x_2598_ == 0)
{
lean_object* v___x_2599_; 
v___x_2599_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkFun(v_body_2587_, v_body_2586_, v___y_2589_, v___y_2590_, v___y_2591_, v___y_2592_, v___y_2593_, v___y_2594_, v___y_2595_, v___y_2596_);
return v___x_2599_;
}
else
{
lean_object* v___x_2600_; lean_object* v___x_2601_; 
v___x_2600_ = lean_expr_instantiate1(v_body_2586_, v_x_2588_);
lean_dec_ref(v_body_2586_);
v___x_2601_ = l_Lean_Meta_Sym_shareCommonInc(v___x_2600_, v___y_2591_, v___y_2592_, v___y_2593_, v___y_2594_, v___y_2595_, v___y_2596_);
if (lean_obj_tag(v___x_2601_) == 0)
{
lean_object* v_a_2602_; lean_object* v___x_2603_; 
v_a_2602_ = lean_ctor_get(v___x_2601_, 0);
lean_inc(v_a_2602_);
lean_dec_ref_known(v___x_2601_, 1);
v___x_2603_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkFun(v_body_2587_, v_a_2602_, v___y_2589_, v___y_2590_, v___y_2591_, v___y_2592_, v___y_2593_, v___y_2594_, v___y_2595_, v___y_2596_);
return v___x_2603_;
}
else
{
lean_object* v_a_2604_; lean_object* v___x_2606_; uint8_t v_isShared_2607_; uint8_t v_isSharedCheck_2611_; 
lean_dec_ref(v_body_2587_);
v_a_2604_ = lean_ctor_get(v___x_2601_, 0);
v_isSharedCheck_2611_ = !lean_is_exclusive(v___x_2601_);
if (v_isSharedCheck_2611_ == 0)
{
v___x_2606_ = v___x_2601_;
v_isShared_2607_ = v_isSharedCheck_2611_;
goto v_resetjp_2605_;
}
else
{
lean_inc(v_a_2604_);
lean_dec(v___x_2601_);
v___x_2606_ = lean_box(0);
v_isShared_2607_ = v_isSharedCheck_2611_;
goto v_resetjp_2605_;
}
v_resetjp_2605_:
{
lean_object* v___x_2609_; 
if (v_isShared_2607_ == 0)
{
v___x_2609_ = v___x_2606_;
goto v_reusejp_2608_;
}
else
{
lean_object* v_reuseFailAlloc_2610_; 
v_reuseFailAlloc_2610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2610_, 0, v_a_2604_);
v___x_2609_ = v_reuseFailAlloc_2610_;
goto v_reusejp_2608_;
}
v_reusejp_2608_:
{
return v___x_2609_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkFun___boxed(lean_object* v_e_2612_, lean_object* v_expected_2613_, lean_object* v_a_2614_, lean_object* v_a_2615_, lean_object* v_a_2616_, lean_object* v_a_2617_, lean_object* v_a_2618_, lean_object* v_a_2619_, lean_object* v_a_2620_, lean_object* v_a_2621_, lean_object* v_a_2622_){
_start:
{
lean_object* v_res_2623_; 
v_res_2623_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkFun(v_e_2612_, v_expected_2613_, v_a_2614_, v_a_2615_, v_a_2616_, v_a_2617_, v_a_2618_, v_a_2619_, v_a_2620_, v_a_2621_);
lean_dec(v_a_2621_);
lean_dec_ref(v_a_2620_);
lean_dec(v_a_2619_);
lean_dec_ref(v_a_2618_);
lean_dec(v_a_2617_);
lean_dec_ref(v_a_2616_);
lean_dec(v_a_2615_);
lean_dec_ref(v_a_2614_);
return v_res_2623_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDomain___redArg(lean_object* v_t_2624_, lean_object* v_tf_2625_, lean_object* v_a_2626_, lean_object* v_a_2627_, lean_object* v_a_2628_, lean_object* v_a_2629_, lean_object* v_a_2630_){
_start:
{
lean_object* v_numCandidates_2635_; lean_object* v_cleanSuffix_2636_; lean_object* v___x_2637_; uint8_t v___x_2638_; 
v_numCandidates_2635_ = lean_ctor_get(v_a_2626_, 1);
v_cleanSuffix_2636_ = lean_ctor_get(v_a_2626_, 2);
v___x_2637_ = lean_unsigned_to_nat(0u);
v___x_2638_ = lean_nat_dec_lt(v___x_2637_, v_numCandidates_2635_);
if (v___x_2638_ == 0)
{
lean_dec_ref(v_tf_2625_);
goto v___jp_2632_;
}
else
{
lean_object* v___x_2639_; uint8_t v___x_2640_; 
v___x_2639_ = l_Lean_Expr_looseBVarRange(v_t_2624_);
v___x_2640_ = lean_nat_dec_le(v___x_2639_, v_cleanSuffix_2636_);
lean_dec(v___x_2639_);
if (v___x_2640_ == 0)
{
lean_object* v___x_2641_; 
v___x_2641_ = l_Lean_Meta_getLevel(v_tf_2625_, v_a_2627_, v_a_2628_, v_a_2629_, v_a_2630_);
if (lean_obj_tag(v___x_2641_) == 0)
{
lean_object* v___x_2643_; uint8_t v_isShared_2644_; uint8_t v_isSharedCheck_2649_; 
v_isSharedCheck_2649_ = !lean_is_exclusive(v___x_2641_);
if (v_isSharedCheck_2649_ == 0)
{
lean_object* v_unused_2650_; 
v_unused_2650_ = lean_ctor_get(v___x_2641_, 0);
lean_dec(v_unused_2650_);
v___x_2643_ = v___x_2641_;
v_isShared_2644_ = v_isSharedCheck_2649_;
goto v_resetjp_2642_;
}
else
{
lean_dec(v___x_2641_);
v___x_2643_ = lean_box(0);
v_isShared_2644_ = v_isSharedCheck_2649_;
goto v_resetjp_2642_;
}
v_resetjp_2642_:
{
lean_object* v___x_2645_; lean_object* v___x_2647_; 
v___x_2645_ = lean_box(0);
if (v_isShared_2644_ == 0)
{
lean_ctor_set(v___x_2643_, 0, v___x_2645_);
v___x_2647_ = v___x_2643_;
goto v_reusejp_2646_;
}
else
{
lean_object* v_reuseFailAlloc_2648_; 
v_reuseFailAlloc_2648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2648_, 0, v___x_2645_);
v___x_2647_ = v_reuseFailAlloc_2648_;
goto v_reusejp_2646_;
}
v_reusejp_2646_:
{
return v___x_2647_;
}
}
}
else
{
lean_object* v_a_2651_; lean_object* v___x_2653_; uint8_t v_isShared_2654_; uint8_t v_isSharedCheck_2658_; 
v_a_2651_ = lean_ctor_get(v___x_2641_, 0);
v_isSharedCheck_2658_ = !lean_is_exclusive(v___x_2641_);
if (v_isSharedCheck_2658_ == 0)
{
v___x_2653_ = v___x_2641_;
v_isShared_2654_ = v_isSharedCheck_2658_;
goto v_resetjp_2652_;
}
else
{
lean_inc(v_a_2651_);
lean_dec(v___x_2641_);
v___x_2653_ = lean_box(0);
v_isShared_2654_ = v_isSharedCheck_2658_;
goto v_resetjp_2652_;
}
v_resetjp_2652_:
{
lean_object* v___x_2656_; 
if (v_isShared_2654_ == 0)
{
v___x_2656_ = v___x_2653_;
goto v_reusejp_2655_;
}
else
{
lean_object* v_reuseFailAlloc_2657_; 
v_reuseFailAlloc_2657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2657_, 0, v_a_2651_);
v___x_2656_ = v_reuseFailAlloc_2657_;
goto v_reusejp_2655_;
}
v_reusejp_2655_:
{
return v___x_2656_;
}
}
}
}
else
{
lean_dec_ref(v_tf_2625_);
goto v___jp_2632_;
}
}
v___jp_2632_:
{
lean_object* v___x_2633_; lean_object* v___x_2634_; 
v___x_2633_ = lean_box(0);
v___x_2634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2634_, 0, v___x_2633_);
return v___x_2634_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDomain___redArg___boxed(lean_object* v_t_2659_, lean_object* v_tf_2660_, lean_object* v_a_2661_, lean_object* v_a_2662_, lean_object* v_a_2663_, lean_object* v_a_2664_, lean_object* v_a_2665_, lean_object* v_a_2666_){
_start:
{
lean_object* v_res_2667_; 
v_res_2667_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDomain___redArg(v_t_2659_, v_tf_2660_, v_a_2661_, v_a_2662_, v_a_2663_, v_a_2664_, v_a_2665_);
lean_dec(v_a_2665_);
lean_dec_ref(v_a_2664_);
lean_dec(v_a_2663_);
lean_dec_ref(v_a_2662_);
lean_dec_ref(v_a_2661_);
lean_dec_ref(v_t_2659_);
return v_res_2667_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDomain(lean_object* v_t_2668_, lean_object* v_tf_2669_, lean_object* v_a_2670_, lean_object* v_a_2671_, lean_object* v_a_2672_, lean_object* v_a_2673_, lean_object* v_a_2674_, lean_object* v_a_2675_, lean_object* v_a_2676_, lean_object* v_a_2677_){
_start:
{
lean_object* v___x_2679_; 
v___x_2679_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDomain___redArg(v_t_2668_, v_tf_2669_, v_a_2670_, v_a_2674_, v_a_2675_, v_a_2676_, v_a_2677_);
return v___x_2679_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDomain___boxed(lean_object* v_t_2680_, lean_object* v_tf_2681_, lean_object* v_a_2682_, lean_object* v_a_2683_, lean_object* v_a_2684_, lean_object* v_a_2685_, lean_object* v_a_2686_, lean_object* v_a_2687_, lean_object* v_a_2688_, lean_object* v_a_2689_, lean_object* v_a_2690_){
_start:
{
lean_object* v_res_2691_; 
v_res_2691_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDomain(v_t_2680_, v_tf_2681_, v_a_2682_, v_a_2683_, v_a_2684_, v_a_2685_, v_a_2686_, v_a_2687_, v_a_2688_, v_a_2689_);
lean_dec(v_a_2689_);
lean_dec_ref(v_a_2688_);
lean_dec(v_a_2687_);
lean_dec_ref(v_a_2686_);
lean_dec(v_a_2685_);
lean_dec_ref(v_a_2684_);
lean_dec(v_a_2683_);
lean_dec_ref(v_a_2682_);
lean_dec_ref(v_t_2680_);
return v_res_2691_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkApp___closed__1(void){
_start:
{
lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; 
v___x_2693_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0___closed__2));
v___x_2694_ = lean_unsigned_to_nat(35u);
v___x_2695_ = lean_unsigned_to_nat(322u);
v___x_2696_ = ((lean_object*)(l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkApp___closed__0));
v___x_2697_ = ((lean_object*)(l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO___closed__0));
v___x_2698_ = l_mkPanicMessageWithDecl(v___x_2697_, v___x_2696_, v___x_2695_, v___x_2694_, v___x_2693_);
return v___x_2698_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkApp(lean_object* v_f_2699_, lean_object* v_a_2700_, lean_object* v_a_2701_, lean_object* v_a_2702_, lean_object* v_a_2703_, lean_object* v_a_2704_, lean_object* v_a_2705_, lean_object* v_a_2706_, lean_object* v_a_2707_, lean_object* v_a_2708_){
_start:
{
lean_object* v___x_2710_; 
v___x_2710_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO(v_f_2699_, v_a_2701_, v_a_2702_, v_a_2703_, v_a_2704_, v_a_2705_, v_a_2706_, v_a_2707_, v_a_2708_);
if (lean_obj_tag(v___x_2710_) == 0)
{
lean_object* v_a_2711_; lean_object* v___x_2712_; 
v_a_2711_ = lean_ctor_get(v___x_2710_, 0);
lean_inc(v_a_2711_);
lean_dec_ref_known(v___x_2710_, 1);
v___x_2712_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_ensureForall___redArg(v_a_2711_, v_a_2703_, v_a_2704_, v_a_2705_, v_a_2706_, v_a_2707_, v_a_2708_);
if (lean_obj_tag(v___x_2712_) == 0)
{
lean_object* v_a_2713_; lean_object* v___x_2715_; uint8_t v_isShared_2716_; uint8_t v_isSharedCheck_2740_; 
v_a_2713_ = lean_ctor_get(v___x_2712_, 0);
v_isSharedCheck_2740_ = !lean_is_exclusive(v___x_2712_);
if (v_isSharedCheck_2740_ == 0)
{
v___x_2715_ = v___x_2712_;
v_isShared_2716_ = v_isSharedCheck_2740_;
goto v_resetjp_2714_;
}
else
{
lean_inc(v_a_2713_);
lean_dec(v___x_2712_);
v___x_2715_ = lean_box(0);
v_isShared_2716_ = v_isSharedCheck_2740_;
goto v_resetjp_2714_;
}
v_resetjp_2714_:
{
if (lean_obj_tag(v_a_2713_) == 7)
{
lean_object* v_binderType_2717_; uint8_t v___x_2732_; 
v_binderType_2717_ = lean_ctor_get(v_a_2713_, 1);
lean_inc_ref(v_binderType_2717_);
lean_dec_ref_known(v_a_2713_, 3);
v___x_2732_ = l_Lean_Expr_hasLooseBVars(v_a_2700_);
if (v___x_2732_ == 0)
{
uint8_t v___x_2733_; 
v___x_2733_ = l_Lean_Expr_hasFVar(v_binderType_2717_);
if (v___x_2733_ == 0)
{
lean_object* v___x_2734_; lean_object* v___x_2736_; 
lean_dec_ref(v_binderType_2717_);
lean_dec_ref(v_a_2700_);
v___x_2734_ = lean_box(0);
if (v_isShared_2716_ == 0)
{
lean_ctor_set(v___x_2715_, 0, v___x_2734_);
v___x_2736_ = v___x_2715_;
goto v_reusejp_2735_;
}
else
{
lean_object* v_reuseFailAlloc_2737_; 
v_reuseFailAlloc_2737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2737_, 0, v___x_2734_);
v___x_2736_ = v_reuseFailAlloc_2737_;
goto v_reusejp_2735_;
}
v_reusejp_2735_:
{
return v___x_2736_;
}
}
else
{
lean_del_object(v___x_2715_);
goto v___jp_2718_;
}
}
else
{
lean_del_object(v___x_2715_);
goto v___jp_2718_;
}
v___jp_2718_:
{
uint8_t v___x_2719_; 
v___x_2719_ = l_Lean_Expr_isLambda(v_a_2700_);
if (v___x_2719_ == 0)
{
lean_object* v___x_2720_; 
v___x_2720_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO(v_a_2700_, v_a_2701_, v_a_2702_, v_a_2703_, v_a_2704_, v_a_2705_, v_a_2706_, v_a_2707_, v_a_2708_);
if (lean_obj_tag(v___x_2720_) == 0)
{
lean_object* v_a_2721_; lean_object* v___x_2722_; 
v_a_2721_ = lean_ctor_get(v___x_2720_, 0);
lean_inc(v_a_2721_);
lean_dec_ref_known(v___x_2720_, 1);
v___x_2722_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq(v_a_2721_, v_binderType_2717_, v_a_2701_, v_a_2702_, v_a_2703_, v_a_2704_, v_a_2705_, v_a_2706_, v_a_2707_, v_a_2708_);
return v___x_2722_;
}
else
{
lean_object* v_a_2723_; lean_object* v___x_2725_; uint8_t v_isShared_2726_; uint8_t v_isSharedCheck_2730_; 
lean_dec_ref(v_binderType_2717_);
v_a_2723_ = lean_ctor_get(v___x_2720_, 0);
v_isSharedCheck_2730_ = !lean_is_exclusive(v___x_2720_);
if (v_isSharedCheck_2730_ == 0)
{
v___x_2725_ = v___x_2720_;
v_isShared_2726_ = v_isSharedCheck_2730_;
goto v_resetjp_2724_;
}
else
{
lean_inc(v_a_2723_);
lean_dec(v___x_2720_);
v___x_2725_ = lean_box(0);
v_isShared_2726_ = v_isSharedCheck_2730_;
goto v_resetjp_2724_;
}
v_resetjp_2724_:
{
lean_object* v___x_2728_; 
if (v_isShared_2726_ == 0)
{
v___x_2728_ = v___x_2725_;
goto v_reusejp_2727_;
}
else
{
lean_object* v_reuseFailAlloc_2729_; 
v_reuseFailAlloc_2729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2729_, 0, v_a_2723_);
v___x_2728_ = v_reuseFailAlloc_2729_;
goto v_reusejp_2727_;
}
v_reusejp_2727_:
{
return v___x_2728_;
}
}
}
}
else
{
lean_object* v___x_2731_; 
v___x_2731_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkFun(v_a_2700_, v_binderType_2717_, v_a_2701_, v_a_2702_, v_a_2703_, v_a_2704_, v_a_2705_, v_a_2706_, v_a_2707_, v_a_2708_);
return v___x_2731_;
}
}
}
else
{
lean_object* v___x_2738_; lean_object* v___x_2739_; 
lean_del_object(v___x_2715_);
lean_dec(v_a_2713_);
lean_dec_ref(v_a_2700_);
v___x_2738_ = lean_obj_once(&l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkApp___closed__1, &l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkApp___closed__1_once, _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkApp___closed__1);
v___x_2739_ = l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkFun_spec__0(v___x_2738_, v_a_2701_, v_a_2702_, v_a_2703_, v_a_2704_, v_a_2705_, v_a_2706_, v_a_2707_, v_a_2708_);
return v___x_2739_;
}
}
}
else
{
lean_object* v_a_2741_; lean_object* v___x_2743_; uint8_t v_isShared_2744_; uint8_t v_isSharedCheck_2748_; 
lean_dec_ref(v_a_2700_);
v_a_2741_ = lean_ctor_get(v___x_2712_, 0);
v_isSharedCheck_2748_ = !lean_is_exclusive(v___x_2712_);
if (v_isSharedCheck_2748_ == 0)
{
v___x_2743_ = v___x_2712_;
v_isShared_2744_ = v_isSharedCheck_2748_;
goto v_resetjp_2742_;
}
else
{
lean_inc(v_a_2741_);
lean_dec(v___x_2712_);
v___x_2743_ = lean_box(0);
v_isShared_2744_ = v_isSharedCheck_2748_;
goto v_resetjp_2742_;
}
v_resetjp_2742_:
{
lean_object* v___x_2746_; 
if (v_isShared_2744_ == 0)
{
v___x_2746_ = v___x_2743_;
goto v_reusejp_2745_;
}
else
{
lean_object* v_reuseFailAlloc_2747_; 
v_reuseFailAlloc_2747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2747_, 0, v_a_2741_);
v___x_2746_ = v_reuseFailAlloc_2747_;
goto v_reusejp_2745_;
}
v_reusejp_2745_:
{
return v___x_2746_;
}
}
}
}
else
{
lean_object* v_a_2749_; lean_object* v___x_2751_; uint8_t v_isShared_2752_; uint8_t v_isSharedCheck_2756_; 
lean_dec_ref(v_a_2700_);
v_a_2749_ = lean_ctor_get(v___x_2710_, 0);
v_isSharedCheck_2756_ = !lean_is_exclusive(v___x_2710_);
if (v_isSharedCheck_2756_ == 0)
{
v___x_2751_ = v___x_2710_;
v_isShared_2752_ = v_isSharedCheck_2756_;
goto v_resetjp_2750_;
}
else
{
lean_inc(v_a_2749_);
lean_dec(v___x_2710_);
v___x_2751_ = lean_box(0);
v_isShared_2752_ = v_isSharedCheck_2756_;
goto v_resetjp_2750_;
}
v_resetjp_2750_:
{
lean_object* v___x_2754_; 
if (v_isShared_2752_ == 0)
{
v___x_2754_ = v___x_2751_;
goto v_reusejp_2753_;
}
else
{
lean_object* v_reuseFailAlloc_2755_; 
v_reuseFailAlloc_2755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2755_, 0, v_a_2749_);
v___x_2754_ = v_reuseFailAlloc_2755_;
goto v_reusejp_2753_;
}
v_reusejp_2753_:
{
return v___x_2754_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkApp___boxed(lean_object* v_f_2757_, lean_object* v_a_2758_, lean_object* v_a_2759_, lean_object* v_a_2760_, lean_object* v_a_2761_, lean_object* v_a_2762_, lean_object* v_a_2763_, lean_object* v_a_2764_, lean_object* v_a_2765_, lean_object* v_a_2766_, lean_object* v_a_2767_){
_start:
{
lean_object* v_res_2768_; 
v_res_2768_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkApp(v_f_2757_, v_a_2758_, v_a_2759_, v_a_2760_, v_a_2761_, v_a_2762_, v_a_2763_, v_a_2764_, v_a_2765_, v_a_2766_);
lean_dec(v_a_2766_);
lean_dec_ref(v_a_2765_);
lean_dec(v_a_2764_);
lean_dec_ref(v_a_2763_);
lean_dec(v_a_2762_);
lean_dec_ref(v_a_2761_);
lean_dec(v_a_2760_);
lean_dec_ref(v_a_2759_);
return v_res_2768_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__4___redArg(lean_object* v_x_2769_, uint8_t v_bi_2770_, lean_object* v_t_2771_, lean_object* v_b_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_){
_start:
{
lean_object* v___y_2781_; lean_object* v___x_2784_; uint8_t v_debug_2785_; 
v___x_2784_ = lean_st_ref_get(v___y_2774_);
v_debug_2785_ = lean_ctor_get_uint8(v___x_2784_, sizeof(void*)*11);
lean_dec(v___x_2784_);
if (v_debug_2785_ == 0)
{
v___y_2781_ = v___y_2774_;
goto v___jp_2780_;
}
else
{
lean_object* v___x_2786_; 
v___x_2786_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_t_2771_, v___y_2773_, v___y_2774_, v___y_2775_, v___y_2776_, v___y_2777_, v___y_2778_);
if (lean_obj_tag(v___x_2786_) == 0)
{
lean_object* v___x_2787_; 
lean_dec_ref_known(v___x_2786_, 1);
v___x_2787_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_b_2772_, v___y_2773_, v___y_2774_, v___y_2775_, v___y_2776_, v___y_2777_, v___y_2778_);
if (lean_obj_tag(v___x_2787_) == 0)
{
lean_dec_ref_known(v___x_2787_, 1);
v___y_2781_ = v___y_2774_;
goto v___jp_2780_;
}
else
{
lean_object* v_a_2788_; lean_object* v___x_2790_; uint8_t v_isShared_2791_; uint8_t v_isSharedCheck_2795_; 
lean_dec_ref(v_b_2772_);
lean_dec_ref(v_t_2771_);
lean_dec(v_x_2769_);
v_a_2788_ = lean_ctor_get(v___x_2787_, 0);
v_isSharedCheck_2795_ = !lean_is_exclusive(v___x_2787_);
if (v_isSharedCheck_2795_ == 0)
{
v___x_2790_ = v___x_2787_;
v_isShared_2791_ = v_isSharedCheck_2795_;
goto v_resetjp_2789_;
}
else
{
lean_inc(v_a_2788_);
lean_dec(v___x_2787_);
v___x_2790_ = lean_box(0);
v_isShared_2791_ = v_isSharedCheck_2795_;
goto v_resetjp_2789_;
}
v_resetjp_2789_:
{
lean_object* v___x_2793_; 
if (v_isShared_2791_ == 0)
{
v___x_2793_ = v___x_2790_;
goto v_reusejp_2792_;
}
else
{
lean_object* v_reuseFailAlloc_2794_; 
v_reuseFailAlloc_2794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2794_, 0, v_a_2788_);
v___x_2793_ = v_reuseFailAlloc_2794_;
goto v_reusejp_2792_;
}
v_reusejp_2792_:
{
return v___x_2793_;
}
}
}
}
else
{
lean_object* v_a_2796_; lean_object* v___x_2798_; uint8_t v_isShared_2799_; uint8_t v_isSharedCheck_2803_; 
lean_dec_ref(v_b_2772_);
lean_dec_ref(v_t_2771_);
lean_dec(v_x_2769_);
v_a_2796_ = lean_ctor_get(v___x_2786_, 0);
v_isSharedCheck_2803_ = !lean_is_exclusive(v___x_2786_);
if (v_isSharedCheck_2803_ == 0)
{
v___x_2798_ = v___x_2786_;
v_isShared_2799_ = v_isSharedCheck_2803_;
goto v_resetjp_2797_;
}
else
{
lean_inc(v_a_2796_);
lean_dec(v___x_2786_);
v___x_2798_ = lean_box(0);
v_isShared_2799_ = v_isSharedCheck_2803_;
goto v_resetjp_2797_;
}
v_resetjp_2797_:
{
lean_object* v___x_2801_; 
if (v_isShared_2799_ == 0)
{
v___x_2801_ = v___x_2798_;
goto v_reusejp_2800_;
}
else
{
lean_object* v_reuseFailAlloc_2802_; 
v_reuseFailAlloc_2802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2802_, 0, v_a_2796_);
v___x_2801_ = v_reuseFailAlloc_2802_;
goto v_reusejp_2800_;
}
v_reusejp_2800_:
{
return v___x_2801_;
}
}
}
}
v___jp_2780_:
{
lean_object* v___x_2782_; lean_object* v___x_2783_; 
v___x_2782_ = l_Lean_Expr_lam___override(v_x_2769_, v_t_2771_, v_b_2772_, v_bi_2770_);
v___x_2783_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_2782_, v___y_2781_);
return v___x_2783_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__4___redArg___boxed(lean_object* v_x_2804_, lean_object* v_bi_2805_, lean_object* v_t_2806_, lean_object* v_b_2807_, lean_object* v___y_2808_, lean_object* v___y_2809_, lean_object* v___y_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_){
_start:
{
uint8_t v_bi_boxed_2815_; lean_object* v_res_2816_; 
v_bi_boxed_2815_ = lean_unbox(v_bi_2805_);
v_res_2816_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__4___redArg(v_x_2804_, v_bi_boxed_2815_, v_t_2806_, v_b_2807_, v___y_2808_, v___y_2809_, v___y_2810_, v___y_2811_, v___y_2812_, v___y_2813_);
lean_dec(v___y_2813_);
lean_dec_ref(v___y_2812_);
lean_dec(v___y_2811_);
lean_dec_ref(v___y_2810_);
lean_dec(v___y_2809_);
lean_dec_ref(v___y_2808_);
return v_res_2816_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__5___redArg(lean_object* v_x_2817_, lean_object* v_t_2818_, lean_object* v_v_2819_, lean_object* v_b_2820_, uint8_t v_nondep_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_){
_start:
{
lean_object* v___y_2830_; lean_object* v___x_2833_; uint8_t v_debug_2834_; 
v___x_2833_ = lean_st_ref_get(v___y_2823_);
v_debug_2834_ = lean_ctor_get_uint8(v___x_2833_, sizeof(void*)*11);
lean_dec(v___x_2833_);
if (v_debug_2834_ == 0)
{
v___y_2830_ = v___y_2823_;
goto v___jp_2829_;
}
else
{
lean_object* v___x_2835_; 
v___x_2835_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_t_2818_, v___y_2822_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_);
if (lean_obj_tag(v___x_2835_) == 0)
{
lean_object* v___x_2836_; 
lean_dec_ref_known(v___x_2835_, 1);
v___x_2836_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_v_2819_, v___y_2822_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_);
if (lean_obj_tag(v___x_2836_) == 0)
{
lean_object* v___x_2837_; 
lean_dec_ref_known(v___x_2836_, 1);
v___x_2837_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_b_2820_, v___y_2822_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_);
if (lean_obj_tag(v___x_2837_) == 0)
{
lean_dec_ref_known(v___x_2837_, 1);
v___y_2830_ = v___y_2823_;
goto v___jp_2829_;
}
else
{
lean_object* v_a_2838_; lean_object* v___x_2840_; uint8_t v_isShared_2841_; uint8_t v_isSharedCheck_2845_; 
lean_dec_ref(v_b_2820_);
lean_dec_ref(v_v_2819_);
lean_dec_ref(v_t_2818_);
lean_dec(v_x_2817_);
v_a_2838_ = lean_ctor_get(v___x_2837_, 0);
v_isSharedCheck_2845_ = !lean_is_exclusive(v___x_2837_);
if (v_isSharedCheck_2845_ == 0)
{
v___x_2840_ = v___x_2837_;
v_isShared_2841_ = v_isSharedCheck_2845_;
goto v_resetjp_2839_;
}
else
{
lean_inc(v_a_2838_);
lean_dec(v___x_2837_);
v___x_2840_ = lean_box(0);
v_isShared_2841_ = v_isSharedCheck_2845_;
goto v_resetjp_2839_;
}
v_resetjp_2839_:
{
lean_object* v___x_2843_; 
if (v_isShared_2841_ == 0)
{
v___x_2843_ = v___x_2840_;
goto v_reusejp_2842_;
}
else
{
lean_object* v_reuseFailAlloc_2844_; 
v_reuseFailAlloc_2844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2844_, 0, v_a_2838_);
v___x_2843_ = v_reuseFailAlloc_2844_;
goto v_reusejp_2842_;
}
v_reusejp_2842_:
{
return v___x_2843_;
}
}
}
}
else
{
lean_object* v_a_2846_; lean_object* v___x_2848_; uint8_t v_isShared_2849_; uint8_t v_isSharedCheck_2853_; 
lean_dec_ref(v_b_2820_);
lean_dec_ref(v_v_2819_);
lean_dec_ref(v_t_2818_);
lean_dec(v_x_2817_);
v_a_2846_ = lean_ctor_get(v___x_2836_, 0);
v_isSharedCheck_2853_ = !lean_is_exclusive(v___x_2836_);
if (v_isSharedCheck_2853_ == 0)
{
v___x_2848_ = v___x_2836_;
v_isShared_2849_ = v_isSharedCheck_2853_;
goto v_resetjp_2847_;
}
else
{
lean_inc(v_a_2846_);
lean_dec(v___x_2836_);
v___x_2848_ = lean_box(0);
v_isShared_2849_ = v_isSharedCheck_2853_;
goto v_resetjp_2847_;
}
v_resetjp_2847_:
{
lean_object* v___x_2851_; 
if (v_isShared_2849_ == 0)
{
v___x_2851_ = v___x_2848_;
goto v_reusejp_2850_;
}
else
{
lean_object* v_reuseFailAlloc_2852_; 
v_reuseFailAlloc_2852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2852_, 0, v_a_2846_);
v___x_2851_ = v_reuseFailAlloc_2852_;
goto v_reusejp_2850_;
}
v_reusejp_2850_:
{
return v___x_2851_;
}
}
}
}
else
{
lean_object* v_a_2854_; lean_object* v___x_2856_; uint8_t v_isShared_2857_; uint8_t v_isSharedCheck_2861_; 
lean_dec_ref(v_b_2820_);
lean_dec_ref(v_v_2819_);
lean_dec_ref(v_t_2818_);
lean_dec(v_x_2817_);
v_a_2854_ = lean_ctor_get(v___x_2835_, 0);
v_isSharedCheck_2861_ = !lean_is_exclusive(v___x_2835_);
if (v_isSharedCheck_2861_ == 0)
{
v___x_2856_ = v___x_2835_;
v_isShared_2857_ = v_isSharedCheck_2861_;
goto v_resetjp_2855_;
}
else
{
lean_inc(v_a_2854_);
lean_dec(v___x_2835_);
v___x_2856_ = lean_box(0);
v_isShared_2857_ = v_isSharedCheck_2861_;
goto v_resetjp_2855_;
}
v_resetjp_2855_:
{
lean_object* v___x_2859_; 
if (v_isShared_2857_ == 0)
{
v___x_2859_ = v___x_2856_;
goto v_reusejp_2858_;
}
else
{
lean_object* v_reuseFailAlloc_2860_; 
v_reuseFailAlloc_2860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2860_, 0, v_a_2854_);
v___x_2859_ = v_reuseFailAlloc_2860_;
goto v_reusejp_2858_;
}
v_reusejp_2858_:
{
return v___x_2859_;
}
}
}
}
v___jp_2829_:
{
lean_object* v___x_2831_; lean_object* v___x_2832_; 
v___x_2831_ = l_Lean_Expr_letE___override(v_x_2817_, v_t_2818_, v_v_2819_, v_b_2820_, v_nondep_2821_);
v___x_2832_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_2831_, v___y_2830_);
return v___x_2832_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__5___redArg___boxed(lean_object* v_x_2862_, lean_object* v_t_2863_, lean_object* v_v_2864_, lean_object* v_b_2865_, lean_object* v_nondep_2866_, lean_object* v___y_2867_, lean_object* v___y_2868_, lean_object* v___y_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_){
_start:
{
uint8_t v_nondep_boxed_2874_; lean_object* v_res_2875_; 
v_nondep_boxed_2874_ = lean_unbox(v_nondep_2866_);
v_res_2875_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__5___redArg(v_x_2862_, v_t_2863_, v_v_2864_, v_b_2865_, v_nondep_boxed_2874_, v___y_2867_, v___y_2868_, v___y_2869_, v___y_2870_, v___y_2871_, v___y_2872_);
lean_dec(v___y_2872_);
lean_dec_ref(v___y_2871_);
lean_dec(v___y_2870_);
lean_dec_ref(v___y_2869_);
lean_dec(v___y_2868_);
lean_dec_ref(v___y_2867_);
return v_res_2875_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__6___redArg(lean_object* v_k_2876_, lean_object* v_t_2877_){
_start:
{
if (lean_obj_tag(v_t_2877_) == 0)
{
lean_object* v_k_2878_; lean_object* v_l_2879_; lean_object* v_r_2880_; uint8_t v___x_2881_; 
v_k_2878_ = lean_ctor_get(v_t_2877_, 1);
v_l_2879_ = lean_ctor_get(v_t_2877_, 3);
v_r_2880_ = lean_ctor_get(v_t_2877_, 4);
v___x_2881_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2876_, v_k_2878_);
switch(v___x_2881_)
{
case 0:
{
v_t_2877_ = v_l_2879_;
goto _start;
}
case 1:
{
uint8_t v___x_2883_; 
v___x_2883_ = 1;
return v___x_2883_;
}
default: 
{
v_t_2877_ = v_r_2880_;
goto _start;
}
}
}
else
{
uint8_t v___x_2885_; 
v___x_2885_ = 0;
return v___x_2885_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__6___redArg___boxed(lean_object* v_k_2886_, lean_object* v_t_2887_){
_start:
{
uint8_t v_res_2888_; lean_object* v_r_2889_; 
v_res_2888_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__6___redArg(v_k_2886_, v_t_2887_);
lean_dec(v_t_2887_);
lean_dec(v_k_2886_);
v_r_2889_ = lean_box(v_res_2888_);
return v_r_2889_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitForall_spec__8___redArg(lean_object* v_x_2890_, uint8_t v_bi_2891_, lean_object* v_t_2892_, lean_object* v_b_2893_, lean_object* v___y_2894_, lean_object* v___y_2895_, lean_object* v___y_2896_, lean_object* v___y_2897_, lean_object* v___y_2898_, lean_object* v___y_2899_){
_start:
{
lean_object* v___y_2902_; lean_object* v___x_2905_; uint8_t v_debug_2906_; 
v___x_2905_ = lean_st_ref_get(v___y_2895_);
v_debug_2906_ = lean_ctor_get_uint8(v___x_2905_, sizeof(void*)*11);
lean_dec(v___x_2905_);
if (v_debug_2906_ == 0)
{
v___y_2902_ = v___y_2895_;
goto v___jp_2901_;
}
else
{
lean_object* v___x_2907_; 
v___x_2907_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_t_2892_, v___y_2894_, v___y_2895_, v___y_2896_, v___y_2897_, v___y_2898_, v___y_2899_);
if (lean_obj_tag(v___x_2907_) == 0)
{
lean_object* v___x_2908_; 
lean_dec_ref_known(v___x_2907_, 1);
v___x_2908_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_b_2893_, v___y_2894_, v___y_2895_, v___y_2896_, v___y_2897_, v___y_2898_, v___y_2899_);
if (lean_obj_tag(v___x_2908_) == 0)
{
lean_dec_ref_known(v___x_2908_, 1);
v___y_2902_ = v___y_2895_;
goto v___jp_2901_;
}
else
{
lean_object* v_a_2909_; lean_object* v___x_2911_; uint8_t v_isShared_2912_; uint8_t v_isSharedCheck_2916_; 
lean_dec_ref(v_b_2893_);
lean_dec_ref(v_t_2892_);
lean_dec(v_x_2890_);
v_a_2909_ = lean_ctor_get(v___x_2908_, 0);
v_isSharedCheck_2916_ = !lean_is_exclusive(v___x_2908_);
if (v_isSharedCheck_2916_ == 0)
{
v___x_2911_ = v___x_2908_;
v_isShared_2912_ = v_isSharedCheck_2916_;
goto v_resetjp_2910_;
}
else
{
lean_inc(v_a_2909_);
lean_dec(v___x_2908_);
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
else
{
lean_object* v_a_2917_; lean_object* v___x_2919_; uint8_t v_isShared_2920_; uint8_t v_isSharedCheck_2924_; 
lean_dec_ref(v_b_2893_);
lean_dec_ref(v_t_2892_);
lean_dec(v_x_2890_);
v_a_2917_ = lean_ctor_get(v___x_2907_, 0);
v_isSharedCheck_2924_ = !lean_is_exclusive(v___x_2907_);
if (v_isSharedCheck_2924_ == 0)
{
v___x_2919_ = v___x_2907_;
v_isShared_2920_ = v_isSharedCheck_2924_;
goto v_resetjp_2918_;
}
else
{
lean_inc(v_a_2917_);
lean_dec(v___x_2907_);
v___x_2919_ = lean_box(0);
v_isShared_2920_ = v_isSharedCheck_2924_;
goto v_resetjp_2918_;
}
v_resetjp_2918_:
{
lean_object* v___x_2922_; 
if (v_isShared_2920_ == 0)
{
v___x_2922_ = v___x_2919_;
goto v_reusejp_2921_;
}
else
{
lean_object* v_reuseFailAlloc_2923_; 
v_reuseFailAlloc_2923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2923_, 0, v_a_2917_);
v___x_2922_ = v_reuseFailAlloc_2923_;
goto v_reusejp_2921_;
}
v_reusejp_2921_:
{
return v___x_2922_;
}
}
}
}
v___jp_2901_:
{
lean_object* v___x_2903_; lean_object* v___x_2904_; 
v___x_2903_ = l_Lean_Expr_forallE___override(v_x_2890_, v_t_2892_, v_b_2893_, v_bi_2891_);
v___x_2904_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_2903_, v___y_2902_);
return v___x_2904_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitForall_spec__8___redArg___boxed(lean_object* v_x_2925_, lean_object* v_bi_2926_, lean_object* v_t_2927_, lean_object* v_b_2928_, lean_object* v___y_2929_, lean_object* v___y_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_){
_start:
{
uint8_t v_bi_boxed_2936_; lean_object* v_res_2937_; 
v_bi_boxed_2936_ = lean_unbox(v_bi_2926_);
v_res_2937_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitForall_spec__8___redArg(v_x_2925_, v_bi_boxed_2936_, v_t_2927_, v_b_2928_, v___y_2929_, v___y_2930_, v___y_2931_, v___y_2932_, v___y_2933_, v___y_2934_);
lean_dec(v___y_2934_);
lean_dec_ref(v___y_2933_);
lean_dec(v___y_2932_);
lean_dec_ref(v___y_2931_);
lean_dec(v___y_2930_);
lean_dec_ref(v___y_2929_);
return v_res_2937_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__2___redArg(lean_object* v_d_2938_, lean_object* v_e_2939_, lean_object* v___y_2940_, lean_object* v___y_2941_, lean_object* v___y_2942_, lean_object* v___y_2943_, lean_object* v___y_2944_, lean_object* v___y_2945_){
_start:
{
lean_object* v___y_2948_; lean_object* v___x_2951_; uint8_t v_debug_2952_; 
v___x_2951_ = lean_st_ref_get(v___y_2941_);
v_debug_2952_ = lean_ctor_get_uint8(v___x_2951_, sizeof(void*)*11);
lean_dec(v___x_2951_);
if (v_debug_2952_ == 0)
{
v___y_2948_ = v___y_2941_;
goto v___jp_2947_;
}
else
{
lean_object* v___x_2953_; 
v___x_2953_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_e_2939_, v___y_2940_, v___y_2941_, v___y_2942_, v___y_2943_, v___y_2944_, v___y_2945_);
if (lean_obj_tag(v___x_2953_) == 0)
{
lean_dec_ref_known(v___x_2953_, 1);
v___y_2948_ = v___y_2941_;
goto v___jp_2947_;
}
else
{
lean_object* v_a_2954_; lean_object* v___x_2956_; uint8_t v_isShared_2957_; uint8_t v_isSharedCheck_2961_; 
lean_dec_ref(v_e_2939_);
lean_dec(v_d_2938_);
v_a_2954_ = lean_ctor_get(v___x_2953_, 0);
v_isSharedCheck_2961_ = !lean_is_exclusive(v___x_2953_);
if (v_isSharedCheck_2961_ == 0)
{
v___x_2956_ = v___x_2953_;
v_isShared_2957_ = v_isSharedCheck_2961_;
goto v_resetjp_2955_;
}
else
{
lean_inc(v_a_2954_);
lean_dec(v___x_2953_);
v___x_2956_ = lean_box(0);
v_isShared_2957_ = v_isSharedCheck_2961_;
goto v_resetjp_2955_;
}
v_resetjp_2955_:
{
lean_object* v___x_2959_; 
if (v_isShared_2957_ == 0)
{
v___x_2959_ = v___x_2956_;
goto v_reusejp_2958_;
}
else
{
lean_object* v_reuseFailAlloc_2960_; 
v_reuseFailAlloc_2960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2960_, 0, v_a_2954_);
v___x_2959_ = v_reuseFailAlloc_2960_;
goto v_reusejp_2958_;
}
v_reusejp_2958_:
{
return v___x_2959_;
}
}
}
}
v___jp_2947_:
{
lean_object* v___x_2949_; lean_object* v___x_2950_; 
v___x_2949_ = l_Lean_Expr_mdata___override(v_d_2938_, v_e_2939_);
v___x_2950_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_2949_, v___y_2948_);
return v___x_2950_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__2___redArg___boxed(lean_object* v_d_2962_, lean_object* v_e_2963_, lean_object* v___y_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_, lean_object* v___y_2968_, lean_object* v___y_2969_, lean_object* v___y_2970_){
_start:
{
lean_object* v_res_2971_; 
v_res_2971_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__2___redArg(v_d_2962_, v_e_2963_, v___y_2964_, v___y_2965_, v___y_2966_, v___y_2967_, v___y_2968_, v___y_2969_);
lean_dec(v___y_2969_);
lean_dec_ref(v___y_2968_);
lean_dec(v___y_2967_);
lean_dec_ref(v___y_2966_);
lean_dec(v___y_2965_);
lean_dec_ref(v___y_2964_);
return v_res_2971_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__3___redArg(lean_object* v_structName_2972_, lean_object* v_idx_2973_, lean_object* v_struct_2974_, lean_object* v___y_2975_, lean_object* v___y_2976_, lean_object* v___y_2977_, lean_object* v___y_2978_, lean_object* v___y_2979_, lean_object* v___y_2980_){
_start:
{
lean_object* v___y_2983_; lean_object* v___x_2986_; uint8_t v_debug_2987_; 
v___x_2986_ = lean_st_ref_get(v___y_2976_);
v_debug_2987_ = lean_ctor_get_uint8(v___x_2986_, sizeof(void*)*11);
lean_dec(v___x_2986_);
if (v_debug_2987_ == 0)
{
v___y_2983_ = v___y_2976_;
goto v___jp_2982_;
}
else
{
lean_object* v___x_2988_; 
v___x_2988_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_struct_2974_, v___y_2975_, v___y_2976_, v___y_2977_, v___y_2978_, v___y_2979_, v___y_2980_);
if (lean_obj_tag(v___x_2988_) == 0)
{
lean_dec_ref_known(v___x_2988_, 1);
v___y_2983_ = v___y_2976_;
goto v___jp_2982_;
}
else
{
lean_object* v_a_2989_; lean_object* v___x_2991_; uint8_t v_isShared_2992_; uint8_t v_isSharedCheck_2996_; 
lean_dec_ref(v_struct_2974_);
lean_dec(v_idx_2973_);
lean_dec(v_structName_2972_);
v_a_2989_ = lean_ctor_get(v___x_2988_, 0);
v_isSharedCheck_2996_ = !lean_is_exclusive(v___x_2988_);
if (v_isSharedCheck_2996_ == 0)
{
v___x_2991_ = v___x_2988_;
v_isShared_2992_ = v_isSharedCheck_2996_;
goto v_resetjp_2990_;
}
else
{
lean_inc(v_a_2989_);
lean_dec(v___x_2988_);
v___x_2991_ = lean_box(0);
v_isShared_2992_ = v_isSharedCheck_2996_;
goto v_resetjp_2990_;
}
v_resetjp_2990_:
{
lean_object* v___x_2994_; 
if (v_isShared_2992_ == 0)
{
v___x_2994_ = v___x_2991_;
goto v_reusejp_2993_;
}
else
{
lean_object* v_reuseFailAlloc_2995_; 
v_reuseFailAlloc_2995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2995_, 0, v_a_2989_);
v___x_2994_ = v_reuseFailAlloc_2995_;
goto v_reusejp_2993_;
}
v_reusejp_2993_:
{
return v___x_2994_;
}
}
}
}
v___jp_2982_:
{
lean_object* v___x_2984_; lean_object* v___x_2985_; 
v___x_2984_ = l_Lean_Expr_proj___override(v_structName_2972_, v_idx_2973_, v_struct_2974_);
v___x_2985_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_2984_, v___y_2983_);
return v___x_2985_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__3___redArg___boxed(lean_object* v_structName_2997_, lean_object* v_idx_2998_, lean_object* v_struct_2999_, lean_object* v___y_3000_, lean_object* v___y_3001_, lean_object* v___y_3002_, lean_object* v___y_3003_, lean_object* v___y_3004_, lean_object* v___y_3005_, lean_object* v___y_3006_){
_start:
{
lean_object* v_res_3007_; 
v_res_3007_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__3___redArg(v_structName_2997_, v_idx_2998_, v_struct_2999_, v___y_3000_, v___y_3001_, v___y_3002_, v___y_3003_, v___y_3004_, v___y_3005_);
lean_dec(v___y_3005_);
lean_dec_ref(v___y_3004_);
lean_dec(v___y_3003_);
lean_dec_ref(v___y_3002_);
lean_dec(v___y_3001_);
lean_dec_ref(v___y_3000_);
return v_res_3007_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__1___redArg(lean_object* v_f_3008_, lean_object* v_a_3009_, lean_object* v___y_3010_, lean_object* v___y_3011_, lean_object* v___y_3012_, lean_object* v___y_3013_, lean_object* v___y_3014_, lean_object* v___y_3015_){
_start:
{
lean_object* v___y_3018_; lean_object* v___x_3021_; uint8_t v_debug_3022_; 
v___x_3021_ = lean_st_ref_get(v___y_3011_);
v_debug_3022_ = lean_ctor_get_uint8(v___x_3021_, sizeof(void*)*11);
lean_dec(v___x_3021_);
if (v_debug_3022_ == 0)
{
v___y_3018_ = v___y_3011_;
goto v___jp_3017_;
}
else
{
lean_object* v___x_3023_; 
v___x_3023_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_f_3008_, v___y_3010_, v___y_3011_, v___y_3012_, v___y_3013_, v___y_3014_, v___y_3015_);
if (lean_obj_tag(v___x_3023_) == 0)
{
lean_object* v___x_3024_; 
lean_dec_ref_known(v___x_3023_, 1);
v___x_3024_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_a_3009_, v___y_3010_, v___y_3011_, v___y_3012_, v___y_3013_, v___y_3014_, v___y_3015_);
if (lean_obj_tag(v___x_3024_) == 0)
{
lean_dec_ref_known(v___x_3024_, 1);
v___y_3018_ = v___y_3011_;
goto v___jp_3017_;
}
else
{
lean_object* v_a_3025_; lean_object* v___x_3027_; uint8_t v_isShared_3028_; uint8_t v_isSharedCheck_3032_; 
lean_dec_ref(v_a_3009_);
lean_dec_ref(v_f_3008_);
v_a_3025_ = lean_ctor_get(v___x_3024_, 0);
v_isSharedCheck_3032_ = !lean_is_exclusive(v___x_3024_);
if (v_isSharedCheck_3032_ == 0)
{
v___x_3027_ = v___x_3024_;
v_isShared_3028_ = v_isSharedCheck_3032_;
goto v_resetjp_3026_;
}
else
{
lean_inc(v_a_3025_);
lean_dec(v___x_3024_);
v___x_3027_ = lean_box(0);
v_isShared_3028_ = v_isSharedCheck_3032_;
goto v_resetjp_3026_;
}
v_resetjp_3026_:
{
lean_object* v___x_3030_; 
if (v_isShared_3028_ == 0)
{
v___x_3030_ = v___x_3027_;
goto v_reusejp_3029_;
}
else
{
lean_object* v_reuseFailAlloc_3031_; 
v_reuseFailAlloc_3031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3031_, 0, v_a_3025_);
v___x_3030_ = v_reuseFailAlloc_3031_;
goto v_reusejp_3029_;
}
v_reusejp_3029_:
{
return v___x_3030_;
}
}
}
}
else
{
lean_object* v_a_3033_; lean_object* v___x_3035_; uint8_t v_isShared_3036_; uint8_t v_isSharedCheck_3040_; 
lean_dec_ref(v_a_3009_);
lean_dec_ref(v_f_3008_);
v_a_3033_ = lean_ctor_get(v___x_3023_, 0);
v_isSharedCheck_3040_ = !lean_is_exclusive(v___x_3023_);
if (v_isSharedCheck_3040_ == 0)
{
v___x_3035_ = v___x_3023_;
v_isShared_3036_ = v_isSharedCheck_3040_;
goto v_resetjp_3034_;
}
else
{
lean_inc(v_a_3033_);
lean_dec(v___x_3023_);
v___x_3035_ = lean_box(0);
v_isShared_3036_ = v_isSharedCheck_3040_;
goto v_resetjp_3034_;
}
v_resetjp_3034_:
{
lean_object* v___x_3038_; 
if (v_isShared_3036_ == 0)
{
v___x_3038_ = v___x_3035_;
goto v_reusejp_3037_;
}
else
{
lean_object* v_reuseFailAlloc_3039_; 
v_reuseFailAlloc_3039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3039_, 0, v_a_3033_);
v___x_3038_ = v_reuseFailAlloc_3039_;
goto v_reusejp_3037_;
}
v_reusejp_3037_:
{
return v___x_3038_;
}
}
}
}
v___jp_3017_:
{
lean_object* v___x_3019_; lean_object* v___x_3020_; 
v___x_3019_ = l_Lean_Expr_app___override(v_f_3008_, v_a_3009_);
v___x_3020_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_3019_, v___y_3018_);
return v___x_3020_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__1___redArg___boxed(lean_object* v_f_3041_, lean_object* v_a_3042_, lean_object* v___y_3043_, lean_object* v___y_3044_, lean_object* v___y_3045_, lean_object* v___y_3046_, lean_object* v___y_3047_, lean_object* v___y_3048_, lean_object* v___y_3049_){
_start:
{
lean_object* v_res_3050_; 
v_res_3050_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__1___redArg(v_f_3041_, v_a_3042_, v___y_3043_, v___y_3044_, v___y_3045_, v___y_3046_, v___y_3047_, v___y_3048_);
lean_dec(v___y_3048_);
lean_dec_ref(v___y_3047_);
lean_dec(v___y_3046_);
lean_dec_ref(v___y_3045_);
lean_dec(v___y_3044_);
lean_dec_ref(v___y_3043_);
return v_res_3050_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg___lam__0(lean_object* v_a_3051_, lean_object* v_visited_3052_, lean_object* v_types_3053_, lean_object* v_subst_3054_, lean_object* v_a_x3f_3055_){
_start:
{
lean_object* v___x_3057_; lean_object* v_visitedClosed_3058_; lean_object* v_hasDepLetCache_3059_; lean_object* v_numConverted_3060_; lean_object* v___x_3062_; uint8_t v_isShared_3063_; uint8_t v_isSharedCheck_3070_; 
v___x_3057_ = lean_st_ref_take(v_a_3051_);
v_visitedClosed_3058_ = lean_ctor_get(v___x_3057_, 3);
v_hasDepLetCache_3059_ = lean_ctor_get(v___x_3057_, 4);
v_numConverted_3060_ = lean_ctor_get(v___x_3057_, 5);
v_isSharedCheck_3070_ = !lean_is_exclusive(v___x_3057_);
if (v_isSharedCheck_3070_ == 0)
{
lean_object* v_unused_3071_; lean_object* v_unused_3072_; lean_object* v_unused_3073_; 
v_unused_3071_ = lean_ctor_get(v___x_3057_, 2);
lean_dec(v_unused_3071_);
v_unused_3072_ = lean_ctor_get(v___x_3057_, 1);
lean_dec(v_unused_3072_);
v_unused_3073_ = lean_ctor_get(v___x_3057_, 0);
lean_dec(v_unused_3073_);
v___x_3062_ = v___x_3057_;
v_isShared_3063_ = v_isSharedCheck_3070_;
goto v_resetjp_3061_;
}
else
{
lean_inc(v_numConverted_3060_);
lean_inc(v_hasDepLetCache_3059_);
lean_inc(v_visitedClosed_3058_);
lean_dec(v___x_3057_);
v___x_3062_ = lean_box(0);
v_isShared_3063_ = v_isSharedCheck_3070_;
goto v_resetjp_3061_;
}
v_resetjp_3061_:
{
lean_object* v___x_3065_; 
if (v_isShared_3063_ == 0)
{
lean_ctor_set(v___x_3062_, 2, v_subst_3054_);
lean_ctor_set(v___x_3062_, 1, v_types_3053_);
lean_ctor_set(v___x_3062_, 0, v_visited_3052_);
v___x_3065_ = v___x_3062_;
goto v_reusejp_3064_;
}
else
{
lean_object* v_reuseFailAlloc_3069_; 
v_reuseFailAlloc_3069_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3069_, 0, v_visited_3052_);
lean_ctor_set(v_reuseFailAlloc_3069_, 1, v_types_3053_);
lean_ctor_set(v_reuseFailAlloc_3069_, 2, v_subst_3054_);
lean_ctor_set(v_reuseFailAlloc_3069_, 3, v_visitedClosed_3058_);
lean_ctor_set(v_reuseFailAlloc_3069_, 4, v_hasDepLetCache_3059_);
lean_ctor_set(v_reuseFailAlloc_3069_, 5, v_numConverted_3060_);
v___x_3065_ = v_reuseFailAlloc_3069_;
goto v_reusejp_3064_;
}
v_reusejp_3064_:
{
lean_object* v___x_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; 
v___x_3066_ = lean_st_ref_put(v_a_3051_, v___x_3065_);
v___x_3067_ = lean_box(0);
v___x_3068_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3068_, 0, v___x_3067_);
return v___x_3068_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg___lam__0___boxed(lean_object* v_a_3074_, lean_object* v_visited_3075_, lean_object* v_types_3076_, lean_object* v_subst_3077_, lean_object* v_a_x3f_3078_, lean_object* v___y_3079_){
_start:
{
lean_object* v_res_3080_; 
v_res_3080_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg___lam__0(v_a_3074_, v_visited_3075_, v_types_3076_, v_subst_3077_, v_a_x3f_3078_);
lean_dec(v_a_x3f_3078_);
lean_dec(v_a_3074_);
return v_res_3080_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg___closed__0(void){
_start:
{
lean_object* v___x_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; 
v___x_3081_ = lean_unsigned_to_nat(32u);
v___x_3082_ = lean_mk_empty_array_with_capacity(v___x_3081_);
v___x_3083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3083_, 0, v___x_3082_);
return v___x_3083_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg___closed__1(void){
_start:
{
size_t v___x_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; 
v___x_3084_ = ((size_t)5ULL);
v___x_3085_ = lean_unsigned_to_nat(0u);
v___x_3086_ = lean_unsigned_to_nat(32u);
v___x_3087_ = lean_mk_empty_array_with_capacity(v___x_3086_);
v___x_3088_ = lean_obj_once(&l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg___closed__0, &l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg___closed__0);
v___x_3089_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3089_, 0, v___x_3088_);
lean_ctor_set(v___x_3089_, 1, v___x_3087_);
lean_ctor_set(v___x_3089_, 2, v___x_3085_);
lean_ctor_set(v___x_3089_, 3, v___x_3085_);
lean_ctor_set_usize(v___x_3089_, 4, v___x_3084_);
return v___x_3089_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg___closed__2(void){
_start:
{
lean_object* v___x_3090_; lean_object* v___x_3091_; lean_object* v___x_3092_; 
v___x_3090_ = lean_unsigned_to_nat(0u);
v___x_3091_ = lean_obj_once(&l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg___closed__1, &l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg___closed__1_once, _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg___closed__1);
v___x_3092_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3092_, 0, v___x_3091_);
lean_ctor_set(v___x_3092_, 1, v___x_3090_);
lean_ctor_set(v___x_3092_, 2, v___x_3090_);
return v___x_3092_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore___lam__0___boxed(lean_object* v_body_3093_, lean_object* v_binderType_3094_, lean_object* v_a_3095_, lean_object* v_binderName_3096_, lean_object* v_binderInfo_3097_, lean_object* v_e_3098_, lean_object* v_x_3099_, lean_object* v___y_3100_, lean_object* v___y_3101_, lean_object* v___y_3102_, lean_object* v___y_3103_, lean_object* v___y_3104_, lean_object* v___y_3105_, lean_object* v___y_3106_, lean_object* v___y_3107_, lean_object* v___y_3108_){
_start:
{
uint8_t v_binderInfo_76003__boxed_3109_; lean_object* v_res_3110_; 
v_binderInfo_76003__boxed_3109_ = lean_unbox(v_binderInfo_3097_);
v_res_3110_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore___lam__0(v_body_3093_, v_binderType_3094_, v_a_3095_, v_binderName_3096_, v_binderInfo_76003__boxed_3109_, v_e_3098_, v_x_3099_, v___y_3100_, v___y_3101_, v___y_3102_, v___y_3103_, v___y_3104_, v___y_3105_, v___y_3106_, v___y_3107_);
lean_dec(v___y_3107_);
lean_dec_ref(v___y_3106_);
lean_dec(v___y_3105_);
lean_dec_ref(v___y_3104_);
lean_dec(v___y_3103_);
lean_dec_ref(v___y_3102_);
lean_dec(v___y_3101_);
lean_dec_ref(v___y_3100_);
lean_dec_ref(v_x_3099_);
lean_dec_ref(v_binderType_3094_);
return v_res_3110_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitForall___lam__0(lean_object* v_body_3111_, lean_object* v_binderType_3112_, lean_object* v_a_3113_, lean_object* v_binderName_3114_, uint8_t v_binderInfo_3115_, lean_object* v_e_3116_, lean_object* v_x_3117_, lean_object* v___y_3118_, lean_object* v___y_3119_, lean_object* v___y_3120_, lean_object* v___y_3121_, lean_object* v___y_3122_, lean_object* v___y_3123_, lean_object* v___y_3124_, lean_object* v___y_3125_){
_start:
{
lean_object* v___x_3127_; 
lean_inc_ref(v_body_3111_);
v___x_3127_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitForall(v_body_3111_, v___y_3118_, v___y_3119_, v___y_3120_, v___y_3121_, v___y_3122_, v___y_3123_, v___y_3124_, v___y_3125_);
if (lean_obj_tag(v___x_3127_) == 0)
{
lean_object* v_a_3128_; lean_object* v___x_3130_; uint8_t v_isShared_3131_; uint8_t v_isSharedCheck_3143_; 
v_a_3128_ = lean_ctor_get(v___x_3127_, 0);
v_isSharedCheck_3143_ = !lean_is_exclusive(v___x_3127_);
if (v_isSharedCheck_3143_ == 0)
{
v___x_3130_ = v___x_3127_;
v_isShared_3131_ = v_isSharedCheck_3143_;
goto v_resetjp_3129_;
}
else
{
lean_inc(v_a_3128_);
lean_dec(v___x_3127_);
v___x_3130_ = lean_box(0);
v_isShared_3131_ = v_isSharedCheck_3143_;
goto v_resetjp_3129_;
}
v_resetjp_3129_:
{
size_t v___x_3132_; size_t v___x_3133_; uint8_t v___x_3134_; 
v___x_3132_ = lean_ptr_addr(v_binderType_3112_);
v___x_3133_ = lean_ptr_addr(v_a_3113_);
v___x_3134_ = lean_usize_dec_eq(v___x_3132_, v___x_3133_);
if (v___x_3134_ == 0)
{
lean_object* v___x_3135_; 
lean_del_object(v___x_3130_);
lean_dec_ref(v_e_3116_);
lean_dec_ref(v_body_3111_);
v___x_3135_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitForall_spec__8___redArg(v_binderName_3114_, v_binderInfo_3115_, v_a_3113_, v_a_3128_, v___y_3120_, v___y_3121_, v___y_3122_, v___y_3123_, v___y_3124_, v___y_3125_);
return v___x_3135_;
}
else
{
size_t v___x_3136_; size_t v___x_3137_; uint8_t v___x_3138_; 
v___x_3136_ = lean_ptr_addr(v_body_3111_);
lean_dec_ref(v_body_3111_);
v___x_3137_ = lean_ptr_addr(v_a_3128_);
v___x_3138_ = lean_usize_dec_eq(v___x_3136_, v___x_3137_);
if (v___x_3138_ == 0)
{
lean_object* v___x_3139_; 
lean_del_object(v___x_3130_);
lean_dec_ref(v_e_3116_);
v___x_3139_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitForall_spec__8___redArg(v_binderName_3114_, v_binderInfo_3115_, v_a_3113_, v_a_3128_, v___y_3120_, v___y_3121_, v___y_3122_, v___y_3123_, v___y_3124_, v___y_3125_);
return v___x_3139_;
}
else
{
lean_object* v___x_3141_; 
lean_dec(v_a_3128_);
lean_dec(v_binderName_3114_);
lean_dec_ref(v_a_3113_);
if (v_isShared_3131_ == 0)
{
lean_ctor_set(v___x_3130_, 0, v_e_3116_);
v___x_3141_ = v___x_3130_;
goto v_reusejp_3140_;
}
else
{
lean_object* v_reuseFailAlloc_3142_; 
v_reuseFailAlloc_3142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3142_, 0, v_e_3116_);
v___x_3141_ = v_reuseFailAlloc_3142_;
goto v_reusejp_3140_;
}
v_reusejp_3140_:
{
return v___x_3141_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_3116_);
lean_dec(v_binderName_3114_);
lean_dec_ref(v_a_3113_);
lean_dec_ref(v_body_3111_);
return v___x_3127_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitForall___lam__0___boxed(lean_object* v_body_3144_, lean_object* v_binderType_3145_, lean_object* v_a_3146_, lean_object* v_binderName_3147_, lean_object* v_binderInfo_3148_, lean_object* v_e_3149_, lean_object* v_x_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_, lean_object* v___y_3153_, lean_object* v___y_3154_, lean_object* v___y_3155_, lean_object* v___y_3156_, lean_object* v___y_3157_, lean_object* v___y_3158_, lean_object* v___y_3159_){
_start:
{
uint8_t v_binderInfo_76030__boxed_3160_; lean_object* v_res_3161_; 
v_binderInfo_76030__boxed_3160_ = lean_unbox(v_binderInfo_3148_);
v_res_3161_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitForall___lam__0(v_body_3144_, v_binderType_3145_, v_a_3146_, v_binderName_3147_, v_binderInfo_76030__boxed_3160_, v_e_3149_, v_x_3150_, v___y_3151_, v___y_3152_, v___y_3153_, v___y_3154_, v___y_3155_, v___y_3156_, v___y_3157_, v___y_3158_);
lean_dec(v___y_3158_);
lean_dec_ref(v___y_3157_);
lean_dec(v___y_3156_);
lean_dec_ref(v___y_3155_);
lean_dec(v___y_3154_);
lean_dec_ref(v___y_3153_);
lean_dec(v___y_3152_);
lean_dec_ref(v___y_3151_);
lean_dec_ref(v_x_3150_);
lean_dec_ref(v_binderType_3145_);
return v_res_3161_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitForall(lean_object* v_e_3162_, lean_object* v_a_3163_, lean_object* v_a_3164_, lean_object* v_a_3165_, lean_object* v_a_3166_, lean_object* v_a_3167_, lean_object* v_a_3168_, lean_object* v_a_3169_, lean_object* v_a_3170_){
_start:
{
if (lean_obj_tag(v_e_3162_) == 7)
{
lean_object* v_binderName_3172_; lean_object* v_binderType_3173_; lean_object* v_body_3174_; uint8_t v_binderInfo_3175_; lean_object* v___x_3176_; 
v_binderName_3172_ = lean_ctor_get(v_e_3162_, 0);
lean_inc(v_binderName_3172_);
v_binderType_3173_ = lean_ctor_get(v_e_3162_, 1);
lean_inc_ref_n(v_binderType_3173_, 2);
v_body_3174_ = lean_ctor_get(v_e_3162_, 2);
lean_inc_ref(v_body_3174_);
v_binderInfo_3175_ = lean_ctor_get_uint8(v_e_3162_, sizeof(void*)*3 + 8);
v___x_3176_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visit(v_binderType_3173_, v_a_3163_, v_a_3164_, v_a_3165_, v_a_3166_, v_a_3167_, v_a_3168_, v_a_3169_, v_a_3170_);
if (lean_obj_tag(v___x_3176_) == 0)
{
lean_object* v_a_3177_; lean_object* v___x_3178_; 
v_a_3177_ = lean_ctor_get(v___x_3176_, 0);
lean_inc_n(v_a_3177_, 2);
lean_dec_ref_known(v___x_3176_, 1);
v___x_3178_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv(v_a_3177_, v_a_3163_, v_a_3164_, v_a_3165_, v_a_3166_, v_a_3167_, v_a_3168_, v_a_3169_, v_a_3170_);
if (lean_obj_tag(v___x_3178_) == 0)
{
lean_object* v_a_3179_; lean_object* v___x_3180_; 
v_a_3179_ = lean_ctor_get(v___x_3178_, 0);
lean_inc_n(v_a_3179_, 2);
lean_dec_ref_known(v___x_3178_, 1);
v___x_3180_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDomain___redArg(v_binderType_3173_, v_a_3179_, v_a_3163_, v_a_3167_, v_a_3168_, v_a_3169_, v_a_3170_);
if (lean_obj_tag(v___x_3180_) == 0)
{
lean_object* v_cleanSuffix_3181_; lean_object* v___x_3182_; lean_object* v___f_3183_; lean_object* v___x_3184_; uint8_t v___y_3186_; lean_object* v___x_3189_; uint8_t v___x_3190_; 
lean_dec_ref_known(v___x_3180_, 1);
v_cleanSuffix_3181_ = lean_ctor_get(v_a_3163_, 2);
v___x_3182_ = lean_box(v_binderInfo_3175_);
lean_inc(v_binderName_3172_);
lean_inc_ref(v_binderType_3173_);
v___f_3183_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitForall___lam__0___boxed), 16, 6);
lean_closure_set(v___f_3183_, 0, v_body_3174_);
lean_closure_set(v___f_3183_, 1, v_binderType_3173_);
lean_closure_set(v___f_3183_, 2, v_a_3177_);
lean_closure_set(v___f_3183_, 3, v_binderName_3172_);
lean_closure_set(v___f_3183_, 4, v___x_3182_);
lean_closure_set(v___f_3183_, 5, v_e_3162_);
v___x_3184_ = lean_box(0);
v___x_3189_ = l_Lean_Expr_looseBVarRange(v_binderType_3173_);
lean_dec_ref(v_binderType_3173_);
v___x_3190_ = lean_nat_dec_le(v___x_3189_, v_cleanSuffix_3181_);
lean_dec(v___x_3189_);
if (v___x_3190_ == 0)
{
uint8_t v___x_3191_; 
v___x_3191_ = 1;
v___y_3186_ = v___x_3191_;
goto v___jp_3185_;
}
else
{
uint8_t v___x_3192_; 
v___x_3192_ = 0;
v___y_3186_ = v___x_3192_;
goto v___jp_3185_;
}
v___jp_3185_:
{
uint8_t v___x_3187_; lean_object* v___x_3188_; 
v___x_3187_ = 0;
v___x_3188_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder___redArg(v_binderName_3172_, v_a_3179_, v___x_3184_, v___y_3186_, v___x_3187_, v___f_3183_, v_a_3163_, v_a_3164_, v_a_3165_, v_a_3166_, v_a_3167_, v_a_3168_, v_a_3169_, v_a_3170_);
return v___x_3188_;
}
}
else
{
lean_object* v_a_3193_; lean_object* v___x_3195_; uint8_t v_isShared_3196_; uint8_t v_isSharedCheck_3200_; 
lean_dec(v_a_3179_);
lean_dec(v_a_3177_);
lean_dec_ref(v_body_3174_);
lean_dec_ref(v_binderType_3173_);
lean_dec(v_binderName_3172_);
lean_dec_ref_known(v_e_3162_, 3);
v_a_3193_ = lean_ctor_get(v___x_3180_, 0);
v_isSharedCheck_3200_ = !lean_is_exclusive(v___x_3180_);
if (v_isSharedCheck_3200_ == 0)
{
v___x_3195_ = v___x_3180_;
v_isShared_3196_ = v_isSharedCheck_3200_;
goto v_resetjp_3194_;
}
else
{
lean_inc(v_a_3193_);
lean_dec(v___x_3180_);
v___x_3195_ = lean_box(0);
v_isShared_3196_ = v_isSharedCheck_3200_;
goto v_resetjp_3194_;
}
v_resetjp_3194_:
{
lean_object* v___x_3198_; 
if (v_isShared_3196_ == 0)
{
v___x_3198_ = v___x_3195_;
goto v_reusejp_3197_;
}
else
{
lean_object* v_reuseFailAlloc_3199_; 
v_reuseFailAlloc_3199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3199_, 0, v_a_3193_);
v___x_3198_ = v_reuseFailAlloc_3199_;
goto v_reusejp_3197_;
}
v_reusejp_3197_:
{
return v___x_3198_;
}
}
}
}
else
{
lean_dec(v_a_3177_);
lean_dec_ref(v_body_3174_);
lean_dec_ref(v_binderType_3173_);
lean_dec_ref_known(v_e_3162_, 3);
lean_dec(v_binderName_3172_);
return v___x_3178_;
}
}
else
{
lean_dec_ref(v_body_3174_);
lean_dec_ref(v_binderType_3173_);
lean_dec_ref_known(v_e_3162_, 3);
lean_dec(v_binderName_3172_);
return v___x_3176_;
}
}
else
{
lean_object* v___x_3201_; 
lean_inc_ref(v_e_3162_);
v___x_3201_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visit(v_e_3162_, v_a_3163_, v_a_3164_, v_a_3165_, v_a_3166_, v_a_3167_, v_a_3168_, v_a_3169_, v_a_3170_);
if (lean_obj_tag(v___x_3201_) == 0)
{
lean_object* v_a_3202_; lean_object* v_numCandidates_3203_; lean_object* v_cleanSuffix_3204_; lean_object* v___x_3205_; uint8_t v___x_3206_; 
v_a_3202_ = lean_ctor_get(v___x_3201_, 0);
lean_inc(v_a_3202_);
v_numCandidates_3203_ = lean_ctor_get(v_a_3163_, 1);
v_cleanSuffix_3204_ = lean_ctor_get(v_a_3163_, 2);
v___x_3205_ = lean_unsigned_to_nat(0u);
v___x_3206_ = lean_nat_dec_lt(v___x_3205_, v_numCandidates_3203_);
if (v___x_3206_ == 0)
{
lean_dec(v_a_3202_);
lean_dec_ref(v_e_3162_);
return v___x_3201_;
}
else
{
lean_object* v___x_3207_; uint8_t v___x_3208_; 
v___x_3207_ = l_Lean_Expr_looseBVarRange(v_e_3162_);
lean_dec_ref(v_e_3162_);
v___x_3208_ = lean_nat_dec_le(v___x_3207_, v_cleanSuffix_3204_);
lean_dec(v___x_3207_);
if (v___x_3208_ == 0)
{
lean_object* v___x_3209_; 
lean_dec_ref_known(v___x_3201_, 1);
lean_inc(v_a_3202_);
v___x_3209_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv(v_a_3202_, v_a_3163_, v_a_3164_, v_a_3165_, v_a_3166_, v_a_3167_, v_a_3168_, v_a_3169_, v_a_3170_);
if (lean_obj_tag(v___x_3209_) == 0)
{
lean_object* v_a_3210_; lean_object* v___x_3211_; 
v_a_3210_ = lean_ctor_get(v___x_3209_, 0);
lean_inc(v_a_3210_);
lean_dec_ref_known(v___x_3209_, 1);
v___x_3211_ = l_Lean_Meta_getLevel(v_a_3210_, v_a_3167_, v_a_3168_, v_a_3169_, v_a_3170_);
if (lean_obj_tag(v___x_3211_) == 0)
{
lean_object* v___x_3213_; uint8_t v_isShared_3214_; uint8_t v_isSharedCheck_3218_; 
v_isSharedCheck_3218_ = !lean_is_exclusive(v___x_3211_);
if (v_isSharedCheck_3218_ == 0)
{
lean_object* v_unused_3219_; 
v_unused_3219_ = lean_ctor_get(v___x_3211_, 0);
lean_dec(v_unused_3219_);
v___x_3213_ = v___x_3211_;
v_isShared_3214_ = v_isSharedCheck_3218_;
goto v_resetjp_3212_;
}
else
{
lean_dec(v___x_3211_);
v___x_3213_ = lean_box(0);
v_isShared_3214_ = v_isSharedCheck_3218_;
goto v_resetjp_3212_;
}
v_resetjp_3212_:
{
lean_object* v___x_3216_; 
if (v_isShared_3214_ == 0)
{
lean_ctor_set(v___x_3213_, 0, v_a_3202_);
v___x_3216_ = v___x_3213_;
goto v_reusejp_3215_;
}
else
{
lean_object* v_reuseFailAlloc_3217_; 
v_reuseFailAlloc_3217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3217_, 0, v_a_3202_);
v___x_3216_ = v_reuseFailAlloc_3217_;
goto v_reusejp_3215_;
}
v_reusejp_3215_:
{
return v___x_3216_;
}
}
}
else
{
lean_object* v_a_3220_; lean_object* v___x_3222_; uint8_t v_isShared_3223_; uint8_t v_isSharedCheck_3227_; 
lean_dec(v_a_3202_);
v_a_3220_ = lean_ctor_get(v___x_3211_, 0);
v_isSharedCheck_3227_ = !lean_is_exclusive(v___x_3211_);
if (v_isSharedCheck_3227_ == 0)
{
v___x_3222_ = v___x_3211_;
v_isShared_3223_ = v_isSharedCheck_3227_;
goto v_resetjp_3221_;
}
else
{
lean_inc(v_a_3220_);
lean_dec(v___x_3211_);
v___x_3222_ = lean_box(0);
v_isShared_3223_ = v_isSharedCheck_3227_;
goto v_resetjp_3221_;
}
v_resetjp_3221_:
{
lean_object* v___x_3225_; 
if (v_isShared_3223_ == 0)
{
v___x_3225_ = v___x_3222_;
goto v_reusejp_3224_;
}
else
{
lean_object* v_reuseFailAlloc_3226_; 
v_reuseFailAlloc_3226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3226_, 0, v_a_3220_);
v___x_3225_ = v_reuseFailAlloc_3226_;
goto v_reusejp_3224_;
}
v_reusejp_3224_:
{
return v___x_3225_;
}
}
}
}
else
{
lean_dec(v_a_3202_);
return v___x_3209_;
}
}
else
{
lean_dec(v_a_3202_);
return v___x_3201_;
}
}
}
else
{
lean_dec_ref(v_e_3162_);
return v___x_3201_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore___lam__1(lean_object* v_body_3228_, lean_object* v_type_3229_, lean_object* v_a_3230_, lean_object* v_declName_3231_, lean_object* v_a_3232_, uint8_t v_nondep_3233_, lean_object* v_value_3234_, lean_object* v_e_3235_, uint8_t v___y_3236_, lean_object* v_x_3237_, lean_object* v___y_3238_, lean_object* v___y_3239_, lean_object* v___y_3240_, lean_object* v___y_3241_, lean_object* v___y_3242_, lean_object* v___y_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_){
_start:
{
lean_object* v___x_3247_; 
lean_inc_ref(v_body_3228_);
v___x_3247_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visit(v_body_3228_, v___y_3238_, v___y_3239_, v___y_3240_, v___y_3241_, v___y_3242_, v___y_3243_, v___y_3244_, v___y_3245_);
if (lean_obj_tag(v___x_3247_) == 0)
{
lean_object* v_a_3248_; lean_object* v___x_3250_; uint8_t v_isShared_3251_; uint8_t v_isSharedCheck_3314_; 
v_a_3248_ = lean_ctor_get(v___x_3247_, 0);
v_isSharedCheck_3314_ = !lean_is_exclusive(v___x_3247_);
if (v_isSharedCheck_3314_ == 0)
{
v___x_3250_ = v___x_3247_;
v_isShared_3251_ = v_isSharedCheck_3314_;
goto v_resetjp_3249_;
}
else
{
lean_inc(v_a_3248_);
lean_dec(v___x_3247_);
v___x_3250_ = lean_box(0);
v_isShared_3251_ = v_isSharedCheck_3314_;
goto v_resetjp_3249_;
}
v_resetjp_3249_:
{
lean_object* v___y_3253_; lean_object* v___y_3254_; lean_object* v___y_3255_; lean_object* v___y_3256_; lean_object* v___y_3257_; lean_object* v___y_3258_; uint8_t v_nondep_x27_3275_; lean_object* v___y_3276_; lean_object* v___y_3277_; lean_object* v___y_3278_; lean_object* v___y_3279_; lean_object* v___y_3280_; lean_object* v___y_3281_; lean_object* v___x_3284_; 
v___x_3284_ = l_Lean_Meta_getZetaDeltaFVarIds___redArg(v___y_3243_);
if (lean_obj_tag(v___x_3284_) == 0)
{
lean_object* v_a_3285_; uint8_t v___x_3286_; 
v_a_3285_ = lean_ctor_get(v___x_3284_, 0);
lean_inc(v_a_3285_);
lean_dec_ref_known(v___x_3284_, 1);
v___x_3286_ = 1;
if (v_nondep_3233_ == 0)
{
if (v___y_3236_ == 0)
{
lean_dec(v_a_3285_);
v_nondep_x27_3275_ = v_nondep_3233_;
v___y_3276_ = v___y_3240_;
v___y_3277_ = v___y_3241_;
v___y_3278_ = v___y_3242_;
v___y_3279_ = v___y_3243_;
v___y_3280_ = v___y_3244_;
v___y_3281_ = v___y_3245_;
goto v___jp_3274_;
}
else
{
lean_object* v___x_3287_; uint8_t v___x_3288_; 
v___x_3287_ = l_Lean_Expr_fvarId_x21(v_x_3237_);
v___x_3288_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__6___redArg(v___x_3287_, v_a_3285_);
lean_dec(v_a_3285_);
lean_dec(v___x_3287_);
if (v___x_3288_ == 0)
{
lean_object* v___x_3289_; lean_object* v_visited_3290_; lean_object* v_types_3291_; lean_object* v_subst_3292_; lean_object* v_visitedClosed_3293_; lean_object* v_hasDepLetCache_3294_; lean_object* v_numConverted_3295_; lean_object* v___x_3297_; uint8_t v_isShared_3298_; uint8_t v_isSharedCheck_3305_; 
v___x_3289_ = lean_st_ref_take(v___y_3239_);
v_visited_3290_ = lean_ctor_get(v___x_3289_, 0);
v_types_3291_ = lean_ctor_get(v___x_3289_, 1);
v_subst_3292_ = lean_ctor_get(v___x_3289_, 2);
v_visitedClosed_3293_ = lean_ctor_get(v___x_3289_, 3);
v_hasDepLetCache_3294_ = lean_ctor_get(v___x_3289_, 4);
v_numConverted_3295_ = lean_ctor_get(v___x_3289_, 5);
v_isSharedCheck_3305_ = !lean_is_exclusive(v___x_3289_);
if (v_isSharedCheck_3305_ == 0)
{
v___x_3297_ = v___x_3289_;
v_isShared_3298_ = v_isSharedCheck_3305_;
goto v_resetjp_3296_;
}
else
{
lean_inc(v_numConverted_3295_);
lean_inc(v_hasDepLetCache_3294_);
lean_inc(v_visitedClosed_3293_);
lean_inc(v_subst_3292_);
lean_inc(v_types_3291_);
lean_inc(v_visited_3290_);
lean_dec(v___x_3289_);
v___x_3297_ = lean_box(0);
v_isShared_3298_ = v_isSharedCheck_3305_;
goto v_resetjp_3296_;
}
v_resetjp_3296_:
{
lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3302_; 
v___x_3299_ = lean_unsigned_to_nat(1u);
v___x_3300_ = lean_nat_add(v_numConverted_3295_, v___x_3299_);
lean_dec(v_numConverted_3295_);
if (v_isShared_3298_ == 0)
{
lean_ctor_set(v___x_3297_, 5, v___x_3300_);
v___x_3302_ = v___x_3297_;
goto v_reusejp_3301_;
}
else
{
lean_object* v_reuseFailAlloc_3304_; 
v_reuseFailAlloc_3304_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3304_, 0, v_visited_3290_);
lean_ctor_set(v_reuseFailAlloc_3304_, 1, v_types_3291_);
lean_ctor_set(v_reuseFailAlloc_3304_, 2, v_subst_3292_);
lean_ctor_set(v_reuseFailAlloc_3304_, 3, v_visitedClosed_3293_);
lean_ctor_set(v_reuseFailAlloc_3304_, 4, v_hasDepLetCache_3294_);
lean_ctor_set(v_reuseFailAlloc_3304_, 5, v___x_3300_);
v___x_3302_ = v_reuseFailAlloc_3304_;
goto v_reusejp_3301_;
}
v_reusejp_3301_:
{
lean_object* v___x_3303_; 
v___x_3303_ = lean_st_ref_put(v___y_3239_, v___x_3302_);
v_nondep_x27_3275_ = v___x_3286_;
v___y_3276_ = v___y_3240_;
v___y_3277_ = v___y_3241_;
v___y_3278_ = v___y_3242_;
v___y_3279_ = v___y_3243_;
v___y_3280_ = v___y_3244_;
v___y_3281_ = v___y_3245_;
goto v___jp_3274_;
}
}
}
else
{
v_nondep_x27_3275_ = v_nondep_3233_;
v___y_3276_ = v___y_3240_;
v___y_3277_ = v___y_3241_;
v___y_3278_ = v___y_3242_;
v___y_3279_ = v___y_3243_;
v___y_3280_ = v___y_3244_;
v___y_3281_ = v___y_3245_;
goto v___jp_3274_;
}
}
}
else
{
lean_dec(v_a_3285_);
v_nondep_x27_3275_ = v___x_3286_;
v___y_3276_ = v___y_3240_;
v___y_3277_ = v___y_3241_;
v___y_3278_ = v___y_3242_;
v___y_3279_ = v___y_3243_;
v___y_3280_ = v___y_3244_;
v___y_3281_ = v___y_3245_;
goto v___jp_3274_;
}
}
else
{
lean_object* v_a_3306_; lean_object* v___x_3308_; uint8_t v_isShared_3309_; uint8_t v_isSharedCheck_3313_; 
lean_del_object(v___x_3250_);
lean_dec(v_a_3248_);
lean_dec_ref(v_e_3235_);
lean_dec_ref(v_a_3232_);
lean_dec(v_declName_3231_);
lean_dec_ref(v_a_3230_);
lean_dec_ref(v_body_3228_);
v_a_3306_ = lean_ctor_get(v___x_3284_, 0);
v_isSharedCheck_3313_ = !lean_is_exclusive(v___x_3284_);
if (v_isSharedCheck_3313_ == 0)
{
v___x_3308_ = v___x_3284_;
v_isShared_3309_ = v_isSharedCheck_3313_;
goto v_resetjp_3307_;
}
else
{
lean_inc(v_a_3306_);
lean_dec(v___x_3284_);
v___x_3308_ = lean_box(0);
v_isShared_3309_ = v_isSharedCheck_3313_;
goto v_resetjp_3307_;
}
v_resetjp_3307_:
{
lean_object* v___x_3311_; 
if (v_isShared_3309_ == 0)
{
v___x_3311_ = v___x_3308_;
goto v_reusejp_3310_;
}
else
{
lean_object* v_reuseFailAlloc_3312_; 
v_reuseFailAlloc_3312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3312_, 0, v_a_3306_);
v___x_3311_ = v_reuseFailAlloc_3312_;
goto v_reusejp_3310_;
}
v_reusejp_3310_:
{
return v___x_3311_;
}
}
}
v___jp_3252_:
{
size_t v___x_3259_; size_t v___x_3260_; uint8_t v___x_3261_; 
v___x_3259_ = lean_ptr_addr(v_type_3229_);
v___x_3260_ = lean_ptr_addr(v_a_3230_);
v___x_3261_ = lean_usize_dec_eq(v___x_3259_, v___x_3260_);
if (v___x_3261_ == 0)
{
lean_object* v___x_3262_; 
lean_del_object(v___x_3250_);
lean_dec_ref(v_e_3235_);
lean_dec_ref(v_body_3228_);
v___x_3262_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__5___redArg(v_declName_3231_, v_a_3230_, v_a_3232_, v_a_3248_, v_nondep_3233_, v___y_3256_, v___y_3253_, v___y_3257_, v___y_3255_, v___y_3258_, v___y_3254_);
return v___x_3262_;
}
else
{
size_t v___x_3263_; size_t v___x_3264_; uint8_t v___x_3265_; 
v___x_3263_ = lean_ptr_addr(v_value_3234_);
v___x_3264_ = lean_ptr_addr(v_a_3232_);
v___x_3265_ = lean_usize_dec_eq(v___x_3263_, v___x_3264_);
if (v___x_3265_ == 0)
{
lean_object* v___x_3266_; 
lean_del_object(v___x_3250_);
lean_dec_ref(v_e_3235_);
lean_dec_ref(v_body_3228_);
v___x_3266_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__5___redArg(v_declName_3231_, v_a_3230_, v_a_3232_, v_a_3248_, v_nondep_3233_, v___y_3256_, v___y_3253_, v___y_3257_, v___y_3255_, v___y_3258_, v___y_3254_);
return v___x_3266_;
}
else
{
size_t v___x_3267_; size_t v___x_3268_; uint8_t v___x_3269_; 
v___x_3267_ = lean_ptr_addr(v_body_3228_);
lean_dec_ref(v_body_3228_);
v___x_3268_ = lean_ptr_addr(v_a_3248_);
v___x_3269_ = lean_usize_dec_eq(v___x_3267_, v___x_3268_);
if (v___x_3269_ == 0)
{
lean_object* v___x_3270_; 
lean_del_object(v___x_3250_);
lean_dec_ref(v_e_3235_);
v___x_3270_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__5___redArg(v_declName_3231_, v_a_3230_, v_a_3232_, v_a_3248_, v_nondep_3233_, v___y_3256_, v___y_3253_, v___y_3257_, v___y_3255_, v___y_3258_, v___y_3254_);
return v___x_3270_;
}
else
{
lean_object* v___x_3272_; 
lean_dec(v_a_3248_);
lean_dec_ref(v_a_3232_);
lean_dec(v_declName_3231_);
lean_dec_ref(v_a_3230_);
if (v_isShared_3251_ == 0)
{
lean_ctor_set(v___x_3250_, 0, v_e_3235_);
v___x_3272_ = v___x_3250_;
goto v_reusejp_3271_;
}
else
{
lean_object* v_reuseFailAlloc_3273_; 
v_reuseFailAlloc_3273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3273_, 0, v_e_3235_);
v___x_3272_ = v_reuseFailAlloc_3273_;
goto v_reusejp_3271_;
}
v_reusejp_3271_:
{
return v___x_3272_;
}
}
}
}
}
v___jp_3274_:
{
if (v_nondep_3233_ == 0)
{
if (v_nondep_x27_3275_ == 0)
{
v___y_3253_ = v___y_3277_;
v___y_3254_ = v___y_3281_;
v___y_3255_ = v___y_3279_;
v___y_3256_ = v___y_3276_;
v___y_3257_ = v___y_3278_;
v___y_3258_ = v___y_3280_;
goto v___jp_3252_;
}
else
{
lean_object* v___x_3282_; 
lean_del_object(v___x_3250_);
lean_dec_ref(v_e_3235_);
lean_dec_ref(v_body_3228_);
v___x_3282_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__5___redArg(v_declName_3231_, v_a_3230_, v_a_3232_, v_a_3248_, v_nondep_x27_3275_, v___y_3276_, v___y_3277_, v___y_3278_, v___y_3279_, v___y_3280_, v___y_3281_);
return v___x_3282_;
}
}
else
{
if (v_nondep_x27_3275_ == 0)
{
lean_object* v___x_3283_; 
lean_del_object(v___x_3250_);
lean_dec_ref(v_e_3235_);
lean_dec_ref(v_body_3228_);
v___x_3283_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__5___redArg(v_declName_3231_, v_a_3230_, v_a_3232_, v_a_3248_, v_nondep_x27_3275_, v___y_3276_, v___y_3277_, v___y_3278_, v___y_3279_, v___y_3280_, v___y_3281_);
return v___x_3283_;
}
else
{
v___y_3253_ = v___y_3277_;
v___y_3254_ = v___y_3281_;
v___y_3255_ = v___y_3279_;
v___y_3256_ = v___y_3276_;
v___y_3257_ = v___y_3278_;
v___y_3258_ = v___y_3280_;
goto v___jp_3252_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_3235_);
lean_dec_ref(v_a_3232_);
lean_dec(v_declName_3231_);
lean_dec_ref(v_a_3230_);
lean_dec_ref(v_body_3228_);
return v___x_3247_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore___lam__1___boxed(lean_object** _args){
lean_object* v_body_3315_ = _args[0];
lean_object* v_type_3316_ = _args[1];
lean_object* v_a_3317_ = _args[2];
lean_object* v_declName_3318_ = _args[3];
lean_object* v_a_3319_ = _args[4];
lean_object* v_nondep_3320_ = _args[5];
lean_object* v_value_3321_ = _args[6];
lean_object* v_e_3322_ = _args[7];
lean_object* v___y_3323_ = _args[8];
lean_object* v_x_3324_ = _args[9];
lean_object* v___y_3325_ = _args[10];
lean_object* v___y_3326_ = _args[11];
lean_object* v___y_3327_ = _args[12];
lean_object* v___y_3328_ = _args[13];
lean_object* v___y_3329_ = _args[14];
lean_object* v___y_3330_ = _args[15];
lean_object* v___y_3331_ = _args[16];
lean_object* v___y_3332_ = _args[17];
lean_object* v___y_3333_ = _args[18];
_start:
{
uint8_t v_nondep_76186__boxed_3334_; uint8_t v___y_76188__boxed_3335_; lean_object* v_res_3336_; 
v_nondep_76186__boxed_3334_ = lean_unbox(v_nondep_3320_);
v___y_76188__boxed_3335_ = lean_unbox(v___y_3323_);
v_res_3336_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore___lam__1(v_body_3315_, v_type_3316_, v_a_3317_, v_declName_3318_, v_a_3319_, v_nondep_76186__boxed_3334_, v_value_3321_, v_e_3322_, v___y_76188__boxed_3335_, v_x_3324_, v___y_3325_, v___y_3326_, v___y_3327_, v___y_3328_, v___y_3329_, v___y_3330_, v___y_3331_, v___y_3332_);
lean_dec(v___y_3332_);
lean_dec_ref(v___y_3331_);
lean_dec(v___y_3330_);
lean_dec_ref(v___y_3329_);
lean_dec(v___y_3328_);
lean_dec_ref(v___y_3327_);
lean_dec(v___y_3326_);
lean_dec_ref(v___y_3325_);
lean_dec_ref(v_x_3324_);
lean_dec_ref(v_value_3321_);
lean_dec_ref(v_type_3316_);
return v_res_3336_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore___closed__1(void){
_start:
{
lean_object* v___x_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; 
v___x_3338_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv_spec__0___closed__2));
v___x_3339_ = lean_unsigned_to_nat(9u);
v___x_3340_ = lean_unsigned_to_nat(263u);
v___x_3341_ = ((lean_object*)(l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore___closed__0));
v___x_3342_ = ((lean_object*)(l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO___closed__0));
v___x_3343_ = l_mkPanicMessageWithDecl(v___x_3342_, v___x_3341_, v___x_3340_, v___x_3339_, v___x_3338_);
return v___x_3343_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore(lean_object* v_e_3344_, lean_object* v_a_3345_, lean_object* v_a_3346_, lean_object* v_a_3347_, lean_object* v_a_3348_, lean_object* v_a_3349_, lean_object* v_a_3350_, lean_object* v_a_3351_, lean_object* v_a_3352_){
_start:
{
switch(lean_obj_tag(v_e_3344_))
{
case 5:
{
lean_object* v_fn_3354_; lean_object* v_arg_3355_; lean_object* v___y_3357_; lean_object* v_a_3358_; lean_object* v___y_3380_; lean_object* v___x_3382_; 
v_fn_3354_ = lean_ctor_get(v_e_3344_, 0);
lean_inc_ref_n(v_fn_3354_, 2);
v_arg_3355_ = lean_ctor_get(v_e_3344_, 1);
lean_inc_ref(v_arg_3355_);
v___x_3382_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visit(v_fn_3354_, v_a_3345_, v_a_3346_, v_a_3347_, v_a_3348_, v_a_3349_, v_a_3350_, v_a_3351_, v_a_3352_);
if (lean_obj_tag(v___x_3382_) == 0)
{
lean_object* v_a_3383_; lean_object* v___x_3384_; 
v_a_3383_ = lean_ctor_get(v___x_3382_, 0);
lean_inc(v_a_3383_);
lean_dec_ref_known(v___x_3382_, 1);
lean_inc_ref(v_arg_3355_);
v___x_3384_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visit(v_arg_3355_, v_a_3345_, v_a_3346_, v_a_3347_, v_a_3348_, v_a_3349_, v_a_3350_, v_a_3351_, v_a_3352_);
if (lean_obj_tag(v___x_3384_) == 0)
{
lean_object* v_a_3385_; lean_object* v___x_3387_; uint8_t v_isShared_3388_; uint8_t v_isSharedCheck_3400_; 
v_a_3385_ = lean_ctor_get(v___x_3384_, 0);
v_isSharedCheck_3400_ = !lean_is_exclusive(v___x_3384_);
if (v_isSharedCheck_3400_ == 0)
{
v___x_3387_ = v___x_3384_;
v_isShared_3388_ = v_isSharedCheck_3400_;
goto v_resetjp_3386_;
}
else
{
lean_inc(v_a_3385_);
lean_dec(v___x_3384_);
v___x_3387_ = lean_box(0);
v_isShared_3388_ = v_isSharedCheck_3400_;
goto v_resetjp_3386_;
}
v_resetjp_3386_:
{
size_t v___x_3389_; size_t v___x_3390_; uint8_t v___x_3391_; 
v___x_3389_ = lean_ptr_addr(v_fn_3354_);
v___x_3390_ = lean_ptr_addr(v_a_3383_);
v___x_3391_ = lean_usize_dec_eq(v___x_3389_, v___x_3390_);
if (v___x_3391_ == 0)
{
lean_object* v___x_3392_; 
lean_del_object(v___x_3387_);
lean_dec_ref_known(v_e_3344_, 2);
v___x_3392_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__1___redArg(v_a_3383_, v_a_3385_, v_a_3347_, v_a_3348_, v_a_3349_, v_a_3350_, v_a_3351_, v_a_3352_);
v___y_3380_ = v___x_3392_;
goto v___jp_3379_;
}
else
{
size_t v___x_3393_; size_t v___x_3394_; uint8_t v___x_3395_; 
v___x_3393_ = lean_ptr_addr(v_arg_3355_);
v___x_3394_ = lean_ptr_addr(v_a_3385_);
v___x_3395_ = lean_usize_dec_eq(v___x_3393_, v___x_3394_);
if (v___x_3395_ == 0)
{
lean_object* v___x_3396_; 
lean_del_object(v___x_3387_);
lean_dec_ref_known(v_e_3344_, 2);
v___x_3396_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__1___redArg(v_a_3383_, v_a_3385_, v_a_3347_, v_a_3348_, v_a_3349_, v_a_3350_, v_a_3351_, v_a_3352_);
v___y_3380_ = v___x_3396_;
goto v___jp_3379_;
}
else
{
lean_object* v___x_3398_; 
lean_dec(v_a_3385_);
lean_dec(v_a_3383_);
lean_inc_ref(v_e_3344_);
if (v_isShared_3388_ == 0)
{
lean_ctor_set(v___x_3387_, 0, v_e_3344_);
v___x_3398_ = v___x_3387_;
goto v_reusejp_3397_;
}
else
{
lean_object* v_reuseFailAlloc_3399_; 
v_reuseFailAlloc_3399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3399_, 0, v_e_3344_);
v___x_3398_ = v_reuseFailAlloc_3399_;
goto v_reusejp_3397_;
}
v_reusejp_3397_:
{
v___y_3357_ = v___x_3398_;
v_a_3358_ = v_e_3344_;
goto v___jp_3356_;
}
}
}
}
}
else
{
lean_dec(v_a_3383_);
lean_dec_ref(v_arg_3355_);
lean_dec_ref_known(v_e_3344_, 2);
lean_dec_ref(v_fn_3354_);
return v___x_3384_;
}
}
else
{
lean_dec_ref(v_arg_3355_);
lean_dec_ref_known(v_e_3344_, 2);
lean_dec_ref(v_fn_3354_);
return v___x_3382_;
}
v___jp_3356_:
{
lean_object* v_numCandidates_3359_; lean_object* v___x_3360_; uint8_t v___x_3361_; 
v_numCandidates_3359_ = lean_ctor_get(v_a_3345_, 1);
v___x_3360_ = lean_unsigned_to_nat(0u);
v___x_3361_ = lean_nat_dec_lt(v___x_3360_, v_numCandidates_3359_);
if (v___x_3361_ == 0)
{
lean_dec_ref(v_a_3358_);
lean_dec_ref(v_arg_3355_);
lean_dec_ref(v_fn_3354_);
return v___y_3357_;
}
else
{
lean_object* v___x_3362_; 
lean_dec_ref(v___y_3357_);
v___x_3362_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkApp(v_fn_3354_, v_arg_3355_, v_a_3345_, v_a_3346_, v_a_3347_, v_a_3348_, v_a_3349_, v_a_3350_, v_a_3351_, v_a_3352_);
if (lean_obj_tag(v___x_3362_) == 0)
{
lean_object* v___x_3364_; uint8_t v_isShared_3365_; uint8_t v_isSharedCheck_3369_; 
v_isSharedCheck_3369_ = !lean_is_exclusive(v___x_3362_);
if (v_isSharedCheck_3369_ == 0)
{
lean_object* v_unused_3370_; 
v_unused_3370_ = lean_ctor_get(v___x_3362_, 0);
lean_dec(v_unused_3370_);
v___x_3364_ = v___x_3362_;
v_isShared_3365_ = v_isSharedCheck_3369_;
goto v_resetjp_3363_;
}
else
{
lean_dec(v___x_3362_);
v___x_3364_ = lean_box(0);
v_isShared_3365_ = v_isSharedCheck_3369_;
goto v_resetjp_3363_;
}
v_resetjp_3363_:
{
lean_object* v___x_3367_; 
if (v_isShared_3365_ == 0)
{
lean_ctor_set(v___x_3364_, 0, v_a_3358_);
v___x_3367_ = v___x_3364_;
goto v_reusejp_3366_;
}
else
{
lean_object* v_reuseFailAlloc_3368_; 
v_reuseFailAlloc_3368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3368_, 0, v_a_3358_);
v___x_3367_ = v_reuseFailAlloc_3368_;
goto v_reusejp_3366_;
}
v_reusejp_3366_:
{
return v___x_3367_;
}
}
}
else
{
lean_object* v_a_3371_; lean_object* v___x_3373_; uint8_t v_isShared_3374_; uint8_t v_isSharedCheck_3378_; 
lean_dec_ref(v_a_3358_);
v_a_3371_ = lean_ctor_get(v___x_3362_, 0);
v_isSharedCheck_3378_ = !lean_is_exclusive(v___x_3362_);
if (v_isSharedCheck_3378_ == 0)
{
v___x_3373_ = v___x_3362_;
v_isShared_3374_ = v_isSharedCheck_3378_;
goto v_resetjp_3372_;
}
else
{
lean_inc(v_a_3371_);
lean_dec(v___x_3362_);
v___x_3373_ = lean_box(0);
v_isShared_3374_ = v_isSharedCheck_3378_;
goto v_resetjp_3372_;
}
v_resetjp_3372_:
{
lean_object* v___x_3376_; 
if (v_isShared_3374_ == 0)
{
v___x_3376_ = v___x_3373_;
goto v_reusejp_3375_;
}
else
{
lean_object* v_reuseFailAlloc_3377_; 
v_reuseFailAlloc_3377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3377_, 0, v_a_3371_);
v___x_3376_ = v_reuseFailAlloc_3377_;
goto v_reusejp_3375_;
}
v_reusejp_3375_:
{
return v___x_3376_;
}
}
}
}
}
v___jp_3379_:
{
if (lean_obj_tag(v___y_3380_) == 0)
{
lean_object* v_a_3381_; 
v_a_3381_ = lean_ctor_get(v___y_3380_, 0);
lean_inc(v_a_3381_);
v___y_3357_ = v___y_3380_;
v_a_3358_ = v_a_3381_;
goto v___jp_3356_;
}
else
{
lean_dec_ref(v_arg_3355_);
lean_dec_ref(v_fn_3354_);
return v___y_3380_;
}
}
}
case 10:
{
lean_object* v_data_3401_; lean_object* v_expr_3402_; lean_object* v___x_3403_; 
v_data_3401_ = lean_ctor_get(v_e_3344_, 0);
v_expr_3402_ = lean_ctor_get(v_e_3344_, 1);
lean_inc_ref(v_expr_3402_);
v___x_3403_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visit(v_expr_3402_, v_a_3345_, v_a_3346_, v_a_3347_, v_a_3348_, v_a_3349_, v_a_3350_, v_a_3351_, v_a_3352_);
if (lean_obj_tag(v___x_3403_) == 0)
{
lean_object* v_a_3404_; lean_object* v___x_3406_; uint8_t v_isShared_3407_; uint8_t v_isSharedCheck_3415_; 
v_a_3404_ = lean_ctor_get(v___x_3403_, 0);
v_isSharedCheck_3415_ = !lean_is_exclusive(v___x_3403_);
if (v_isSharedCheck_3415_ == 0)
{
v___x_3406_ = v___x_3403_;
v_isShared_3407_ = v_isSharedCheck_3415_;
goto v_resetjp_3405_;
}
else
{
lean_inc(v_a_3404_);
lean_dec(v___x_3403_);
v___x_3406_ = lean_box(0);
v_isShared_3407_ = v_isSharedCheck_3415_;
goto v_resetjp_3405_;
}
v_resetjp_3405_:
{
size_t v___x_3408_; size_t v___x_3409_; uint8_t v___x_3410_; 
v___x_3408_ = lean_ptr_addr(v_expr_3402_);
v___x_3409_ = lean_ptr_addr(v_a_3404_);
v___x_3410_ = lean_usize_dec_eq(v___x_3408_, v___x_3409_);
if (v___x_3410_ == 0)
{
lean_object* v___x_3411_; 
lean_inc(v_data_3401_);
lean_del_object(v___x_3406_);
lean_dec_ref_known(v_e_3344_, 2);
v___x_3411_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__2___redArg(v_data_3401_, v_a_3404_, v_a_3347_, v_a_3348_, v_a_3349_, v_a_3350_, v_a_3351_, v_a_3352_);
return v___x_3411_;
}
else
{
lean_object* v___x_3413_; 
lean_dec(v_a_3404_);
if (v_isShared_3407_ == 0)
{
lean_ctor_set(v___x_3406_, 0, v_e_3344_);
v___x_3413_ = v___x_3406_;
goto v_reusejp_3412_;
}
else
{
lean_object* v_reuseFailAlloc_3414_; 
v_reuseFailAlloc_3414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3414_, 0, v_e_3344_);
v___x_3413_ = v_reuseFailAlloc_3414_;
goto v_reusejp_3412_;
}
v_reusejp_3412_:
{
return v___x_3413_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_3344_, 2);
return v___x_3403_;
}
}
case 11:
{
lean_object* v_typeName_3416_; lean_object* v_idx_3417_; lean_object* v_struct_3418_; lean_object* v___y_3420_; lean_object* v_a_3421_; lean_object* v___x_3437_; 
v_typeName_3416_ = lean_ctor_get(v_e_3344_, 0);
v_idx_3417_ = lean_ctor_get(v_e_3344_, 1);
v_struct_3418_ = lean_ctor_get(v_e_3344_, 2);
lean_inc_ref(v_struct_3418_);
v___x_3437_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visit(v_struct_3418_, v_a_3345_, v_a_3346_, v_a_3347_, v_a_3348_, v_a_3349_, v_a_3350_, v_a_3351_, v_a_3352_);
if (lean_obj_tag(v___x_3437_) == 0)
{
lean_object* v_a_3438_; lean_object* v___x_3440_; uint8_t v_isShared_3441_; uint8_t v_isSharedCheck_3450_; 
v_a_3438_ = lean_ctor_get(v___x_3437_, 0);
v_isSharedCheck_3450_ = !lean_is_exclusive(v___x_3437_);
if (v_isSharedCheck_3450_ == 0)
{
v___x_3440_ = v___x_3437_;
v_isShared_3441_ = v_isSharedCheck_3450_;
goto v_resetjp_3439_;
}
else
{
lean_inc(v_a_3438_);
lean_dec(v___x_3437_);
v___x_3440_ = lean_box(0);
v_isShared_3441_ = v_isSharedCheck_3450_;
goto v_resetjp_3439_;
}
v_resetjp_3439_:
{
size_t v___x_3442_; size_t v___x_3443_; uint8_t v___x_3444_; 
v___x_3442_ = lean_ptr_addr(v_struct_3418_);
v___x_3443_ = lean_ptr_addr(v_a_3438_);
v___x_3444_ = lean_usize_dec_eq(v___x_3442_, v___x_3443_);
if (v___x_3444_ == 0)
{
lean_object* v___x_3445_; 
lean_del_object(v___x_3440_);
lean_inc(v_idx_3417_);
lean_inc(v_typeName_3416_);
v___x_3445_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__3___redArg(v_typeName_3416_, v_idx_3417_, v_a_3438_, v_a_3347_, v_a_3348_, v_a_3349_, v_a_3350_, v_a_3351_, v_a_3352_);
if (lean_obj_tag(v___x_3445_) == 0)
{
lean_object* v_a_3446_; 
v_a_3446_ = lean_ctor_get(v___x_3445_, 0);
lean_inc(v_a_3446_);
v___y_3420_ = v___x_3445_;
v_a_3421_ = v_a_3446_;
goto v___jp_3419_;
}
else
{
lean_dec_ref_known(v_e_3344_, 3);
return v___x_3445_;
}
}
else
{
lean_object* v___x_3448_; 
lean_dec(v_a_3438_);
lean_inc_ref(v_e_3344_);
if (v_isShared_3441_ == 0)
{
lean_ctor_set(v___x_3440_, 0, v_e_3344_);
v___x_3448_ = v___x_3440_;
goto v_reusejp_3447_;
}
else
{
lean_object* v_reuseFailAlloc_3449_; 
v_reuseFailAlloc_3449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3449_, 0, v_e_3344_);
v___x_3448_ = v_reuseFailAlloc_3449_;
goto v_reusejp_3447_;
}
v_reusejp_3447_:
{
lean_inc_ref(v_e_3344_);
v___y_3420_ = v___x_3448_;
v_a_3421_ = v_e_3344_;
goto v___jp_3419_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_3344_, 3);
return v___x_3437_;
}
v___jp_3419_:
{
lean_object* v_numCandidates_3422_; lean_object* v_cleanSuffix_3423_; lean_object* v___x_3424_; uint8_t v___x_3425_; 
v_numCandidates_3422_ = lean_ctor_get(v_a_3345_, 1);
v_cleanSuffix_3423_ = lean_ctor_get(v_a_3345_, 2);
v___x_3424_ = lean_unsigned_to_nat(0u);
v___x_3425_ = lean_nat_dec_lt(v___x_3424_, v_numCandidates_3422_);
if (v___x_3425_ == 0)
{
lean_dec_ref(v_a_3421_);
lean_dec_ref_known(v_e_3344_, 3);
return v___y_3420_;
}
else
{
lean_object* v___x_3426_; uint8_t v___x_3427_; 
v___x_3426_ = l_Lean_Expr_looseBVarRange(v_struct_3418_);
v___x_3427_ = lean_nat_dec_le(v___x_3426_, v_cleanSuffix_3423_);
lean_dec(v___x_3426_);
if (v___x_3427_ == 0)
{
lean_object* v___x_3428_; 
lean_dec_ref(v___y_3420_);
v___x_3428_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeFallback(v_e_3344_, v_a_3345_, v_a_3346_, v_a_3347_, v_a_3348_, v_a_3349_, v_a_3350_, v_a_3351_, v_a_3352_);
if (lean_obj_tag(v___x_3428_) == 0)
{
lean_object* v___x_3430_; uint8_t v_isShared_3431_; uint8_t v_isSharedCheck_3435_; 
v_isSharedCheck_3435_ = !lean_is_exclusive(v___x_3428_);
if (v_isSharedCheck_3435_ == 0)
{
lean_object* v_unused_3436_; 
v_unused_3436_ = lean_ctor_get(v___x_3428_, 0);
lean_dec(v_unused_3436_);
v___x_3430_ = v___x_3428_;
v_isShared_3431_ = v_isSharedCheck_3435_;
goto v_resetjp_3429_;
}
else
{
lean_dec(v___x_3428_);
v___x_3430_ = lean_box(0);
v_isShared_3431_ = v_isSharedCheck_3435_;
goto v_resetjp_3429_;
}
v_resetjp_3429_:
{
lean_object* v___x_3433_; 
if (v_isShared_3431_ == 0)
{
lean_ctor_set(v___x_3430_, 0, v_a_3421_);
v___x_3433_ = v___x_3430_;
goto v_reusejp_3432_;
}
else
{
lean_object* v_reuseFailAlloc_3434_; 
v_reuseFailAlloc_3434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3434_, 0, v_a_3421_);
v___x_3433_ = v_reuseFailAlloc_3434_;
goto v_reusejp_3432_;
}
v_reusejp_3432_:
{
return v___x_3433_;
}
}
}
else
{
lean_dec_ref(v_a_3421_);
return v___x_3428_;
}
}
else
{
lean_dec_ref(v_a_3421_);
lean_dec_ref_known(v_e_3344_, 3);
return v___y_3420_;
}
}
}
}
case 6:
{
lean_object* v_binderName_3451_; lean_object* v_binderType_3452_; lean_object* v_body_3453_; uint8_t v_binderInfo_3454_; lean_object* v___x_3455_; 
v_binderName_3451_ = lean_ctor_get(v_e_3344_, 0);
lean_inc(v_binderName_3451_);
v_binderType_3452_ = lean_ctor_get(v_e_3344_, 1);
lean_inc_ref_n(v_binderType_3452_, 2);
v_body_3453_ = lean_ctor_get(v_e_3344_, 2);
lean_inc_ref(v_body_3453_);
v_binderInfo_3454_ = lean_ctor_get_uint8(v_e_3344_, sizeof(void*)*3 + 8);
v___x_3455_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visit(v_binderType_3452_, v_a_3345_, v_a_3346_, v_a_3347_, v_a_3348_, v_a_3349_, v_a_3350_, v_a_3351_, v_a_3352_);
if (lean_obj_tag(v___x_3455_) == 0)
{
lean_object* v_a_3456_; lean_object* v___x_3457_; 
v_a_3456_ = lean_ctor_get(v___x_3455_, 0);
lean_inc_n(v_a_3456_, 2);
lean_dec_ref_known(v___x_3455_, 1);
v___x_3457_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv(v_a_3456_, v_a_3345_, v_a_3346_, v_a_3347_, v_a_3348_, v_a_3349_, v_a_3350_, v_a_3351_, v_a_3352_);
if (lean_obj_tag(v___x_3457_) == 0)
{
lean_object* v_a_3458_; lean_object* v___x_3459_; 
v_a_3458_ = lean_ctor_get(v___x_3457_, 0);
lean_inc_n(v_a_3458_, 2);
lean_dec_ref_known(v___x_3457_, 1);
v___x_3459_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDomain___redArg(v_binderType_3452_, v_a_3458_, v_a_3345_, v_a_3349_, v_a_3350_, v_a_3351_, v_a_3352_);
if (lean_obj_tag(v___x_3459_) == 0)
{
lean_object* v_cleanSuffix_3460_; lean_object* v___x_3461_; lean_object* v___f_3462_; lean_object* v___x_3463_; uint8_t v___y_3465_; lean_object* v___x_3468_; uint8_t v___x_3469_; 
lean_dec_ref_known(v___x_3459_, 1);
v_cleanSuffix_3460_ = lean_ctor_get(v_a_3345_, 2);
v___x_3461_ = lean_box(v_binderInfo_3454_);
lean_inc(v_binderName_3451_);
lean_inc_ref(v_binderType_3452_);
v___f_3462_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore___lam__0___boxed), 16, 6);
lean_closure_set(v___f_3462_, 0, v_body_3453_);
lean_closure_set(v___f_3462_, 1, v_binderType_3452_);
lean_closure_set(v___f_3462_, 2, v_a_3456_);
lean_closure_set(v___f_3462_, 3, v_binderName_3451_);
lean_closure_set(v___f_3462_, 4, v___x_3461_);
lean_closure_set(v___f_3462_, 5, v_e_3344_);
v___x_3463_ = lean_box(0);
v___x_3468_ = l_Lean_Expr_looseBVarRange(v_binderType_3452_);
lean_dec_ref(v_binderType_3452_);
v___x_3469_ = lean_nat_dec_le(v___x_3468_, v_cleanSuffix_3460_);
lean_dec(v___x_3468_);
if (v___x_3469_ == 0)
{
uint8_t v___x_3470_; 
v___x_3470_ = 1;
v___y_3465_ = v___x_3470_;
goto v___jp_3464_;
}
else
{
uint8_t v___x_3471_; 
v___x_3471_ = 0;
v___y_3465_ = v___x_3471_;
goto v___jp_3464_;
}
v___jp_3464_:
{
uint8_t v___x_3466_; lean_object* v___x_3467_; 
v___x_3466_ = 0;
v___x_3467_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder___redArg(v_binderName_3451_, v_a_3458_, v___x_3463_, v___y_3465_, v___x_3466_, v___f_3462_, v_a_3345_, v_a_3346_, v_a_3347_, v_a_3348_, v_a_3349_, v_a_3350_, v_a_3351_, v_a_3352_);
return v___x_3467_;
}
}
else
{
lean_object* v_a_3472_; lean_object* v___x_3474_; uint8_t v_isShared_3475_; uint8_t v_isSharedCheck_3479_; 
lean_dec(v_a_3458_);
lean_dec(v_a_3456_);
lean_dec_ref(v_body_3453_);
lean_dec_ref(v_binderType_3452_);
lean_dec_ref_known(v_e_3344_, 3);
lean_dec(v_binderName_3451_);
v_a_3472_ = lean_ctor_get(v___x_3459_, 0);
v_isSharedCheck_3479_ = !lean_is_exclusive(v___x_3459_);
if (v_isSharedCheck_3479_ == 0)
{
v___x_3474_ = v___x_3459_;
v_isShared_3475_ = v_isSharedCheck_3479_;
goto v_resetjp_3473_;
}
else
{
lean_inc(v_a_3472_);
lean_dec(v___x_3459_);
v___x_3474_ = lean_box(0);
v_isShared_3475_ = v_isSharedCheck_3479_;
goto v_resetjp_3473_;
}
v_resetjp_3473_:
{
lean_object* v___x_3477_; 
if (v_isShared_3475_ == 0)
{
v___x_3477_ = v___x_3474_;
goto v_reusejp_3476_;
}
else
{
lean_object* v_reuseFailAlloc_3478_; 
v_reuseFailAlloc_3478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3478_, 0, v_a_3472_);
v___x_3477_ = v_reuseFailAlloc_3478_;
goto v_reusejp_3476_;
}
v_reusejp_3476_:
{
return v___x_3477_;
}
}
}
}
else
{
lean_dec(v_a_3456_);
lean_dec_ref(v_body_3453_);
lean_dec_ref(v_binderType_3452_);
lean_dec_ref_known(v_e_3344_, 3);
lean_dec(v_binderName_3451_);
return v___x_3457_;
}
}
else
{
lean_dec_ref(v_body_3453_);
lean_dec_ref(v_binderType_3452_);
lean_dec_ref_known(v_e_3344_, 3);
lean_dec(v_binderName_3451_);
return v___x_3455_;
}
}
case 7:
{
lean_object* v___x_3480_; 
v___x_3480_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitForall(v_e_3344_, v_a_3345_, v_a_3346_, v_a_3347_, v_a_3348_, v_a_3349_, v_a_3350_, v_a_3351_, v_a_3352_);
return v___x_3480_;
}
case 8:
{
lean_object* v_declName_3481_; lean_object* v_type_3482_; lean_object* v_value_3483_; lean_object* v_body_3484_; uint8_t v_nondep_3485_; lean_object* v___x_3486_; 
v_declName_3481_ = lean_ctor_get(v_e_3344_, 0);
lean_inc(v_declName_3481_);
v_type_3482_ = lean_ctor_get(v_e_3344_, 1);
lean_inc_ref_n(v_type_3482_, 2);
v_value_3483_ = lean_ctor_get(v_e_3344_, 2);
lean_inc_ref(v_value_3483_);
v_body_3484_ = lean_ctor_get(v_e_3344_, 3);
lean_inc_ref(v_body_3484_);
v_nondep_3485_ = lean_ctor_get_uint8(v_e_3344_, sizeof(void*)*4 + 8);
v___x_3486_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visit(v_type_3482_, v_a_3345_, v_a_3346_, v_a_3347_, v_a_3348_, v_a_3349_, v_a_3350_, v_a_3351_, v_a_3352_);
if (lean_obj_tag(v___x_3486_) == 0)
{
lean_object* v_a_3487_; lean_object* v___x_3488_; 
v_a_3487_ = lean_ctor_get(v___x_3486_, 0);
lean_inc(v_a_3487_);
lean_dec_ref_known(v___x_3486_, 1);
lean_inc_ref(v_value_3483_);
v___x_3488_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visit(v_value_3483_, v_a_3345_, v_a_3346_, v_a_3347_, v_a_3348_, v_a_3349_, v_a_3350_, v_a_3351_, v_a_3352_);
if (lean_obj_tag(v___x_3488_) == 0)
{
lean_object* v_a_3489_; lean_object* v___x_3490_; 
v_a_3489_ = lean_ctor_get(v___x_3488_, 0);
lean_inc(v_a_3489_);
lean_dec_ref_known(v___x_3488_, 1);
lean_inc(v_a_3487_);
v___x_3490_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv(v_a_3487_, v_a_3345_, v_a_3346_, v_a_3347_, v_a_3348_, v_a_3349_, v_a_3350_, v_a_3351_, v_a_3352_);
if (lean_obj_tag(v___x_3490_) == 0)
{
lean_object* v_a_3491_; lean_object* v___x_3493_; uint8_t v_isShared_3494_; uint8_t v_isSharedCheck_3575_; 
v_a_3491_ = lean_ctor_get(v___x_3490_, 0);
v_isSharedCheck_3575_ = !lean_is_exclusive(v___x_3490_);
if (v_isSharedCheck_3575_ == 0)
{
v___x_3493_ = v___x_3490_;
v_isShared_3494_ = v_isSharedCheck_3575_;
goto v_resetjp_3492_;
}
else
{
lean_inc(v_a_3491_);
lean_dec(v___x_3490_);
v___x_3493_ = lean_box(0);
v_isShared_3494_ = v_isSharedCheck_3575_;
goto v_resetjp_3492_;
}
v_resetjp_3492_:
{
lean_object* v_numCandidates_3495_; lean_object* v_cleanSuffix_3496_; lean_object* v___y_3498_; lean_object* v___y_3499_; lean_object* v___y_3500_; uint8_t v___y_3501_; lean_object* v___y_3502_; lean_object* v___y_3503_; lean_object* v___y_3504_; lean_object* v___y_3505_; lean_object* v___y_3506_; lean_object* v___y_3507_; uint8_t v___y_3508_; lean_object* v___y_3524_; lean_object* v___y_3525_; lean_object* v___y_3526_; lean_object* v___y_3527_; lean_object* v___y_3528_; lean_object* v___y_3529_; lean_object* v___y_3530_; lean_object* v___y_3531_; lean_object* v___x_3538_; uint8_t v___x_3539_; 
v_numCandidates_3495_ = lean_ctor_get(v_a_3345_, 1);
v_cleanSuffix_3496_ = lean_ctor_get(v_a_3345_, 2);
v___x_3538_ = lean_unsigned_to_nat(0u);
v___x_3539_ = lean_nat_dec_lt(v___x_3538_, v_numCandidates_3495_);
if (v___x_3539_ == 0)
{
v___y_3524_ = v_a_3345_;
v___y_3525_ = v_a_3346_;
v___y_3526_ = v_a_3347_;
v___y_3527_ = v_a_3348_;
v___y_3528_ = v_a_3349_;
v___y_3529_ = v_a_3350_;
v___y_3530_ = v_a_3351_;
v___y_3531_ = v_a_3352_;
goto v___jp_3523_;
}
else
{
lean_object* v___x_3540_; 
lean_inc(v_a_3491_);
v___x_3540_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDomain___redArg(v_type_3482_, v_a_3491_, v_a_3345_, v_a_3349_, v_a_3350_, v_a_3351_, v_a_3352_);
if (lean_obj_tag(v___x_3540_) == 0)
{
lean_object* v___x_3563_; uint8_t v___x_3564_; 
lean_dec_ref_known(v___x_3540_, 1);
v___x_3563_ = l_Lean_Expr_looseBVarRange(v_type_3482_);
v___x_3564_ = lean_nat_dec_le(v___x_3563_, v_cleanSuffix_3496_);
lean_dec(v___x_3563_);
if (v___x_3564_ == 0)
{
goto v___jp_3541_;
}
else
{
lean_object* v___x_3565_; uint8_t v___x_3566_; 
v___x_3565_ = l_Lean_Expr_looseBVarRange(v_value_3483_);
v___x_3566_ = lean_nat_dec_le(v___x_3565_, v_cleanSuffix_3496_);
lean_dec(v___x_3565_);
if (v___x_3566_ == 0)
{
goto v___jp_3541_;
}
else
{
v___y_3524_ = v_a_3345_;
v___y_3525_ = v_a_3346_;
v___y_3526_ = v_a_3347_;
v___y_3527_ = v_a_3348_;
v___y_3528_ = v_a_3349_;
v___y_3529_ = v_a_3350_;
v___y_3530_ = v_a_3351_;
v___y_3531_ = v_a_3352_;
goto v___jp_3523_;
}
}
v___jp_3541_:
{
uint8_t v___x_3542_; 
v___x_3542_ = l_Lean_Expr_isLambda(v_value_3483_);
if (v___x_3542_ == 0)
{
lean_object* v___x_3543_; 
lean_inc_ref(v_value_3483_);
v___x_3543_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO(v_value_3483_, v_a_3345_, v_a_3346_, v_a_3347_, v_a_3348_, v_a_3349_, v_a_3350_, v_a_3351_, v_a_3352_);
if (lean_obj_tag(v___x_3543_) == 0)
{
lean_object* v_a_3544_; lean_object* v___x_3545_; 
v_a_3544_ = lean_ctor_get(v___x_3543_, 0);
lean_inc(v_a_3544_);
lean_dec_ref_known(v___x_3543_, 1);
lean_inc(v_a_3491_);
v___x_3545_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq(v_a_3544_, v_a_3491_, v_a_3345_, v_a_3346_, v_a_3347_, v_a_3348_, v_a_3349_, v_a_3350_, v_a_3351_, v_a_3352_);
if (lean_obj_tag(v___x_3545_) == 0)
{
lean_dec_ref_known(v___x_3545_, 1);
v___y_3524_ = v_a_3345_;
v___y_3525_ = v_a_3346_;
v___y_3526_ = v_a_3347_;
v___y_3527_ = v_a_3348_;
v___y_3528_ = v_a_3349_;
v___y_3529_ = v_a_3350_;
v___y_3530_ = v_a_3351_;
v___y_3531_ = v_a_3352_;
goto v___jp_3523_;
}
else
{
lean_object* v_a_3546_; lean_object* v___x_3548_; uint8_t v_isShared_3549_; uint8_t v_isSharedCheck_3553_; 
lean_del_object(v___x_3493_);
lean_dec(v_a_3491_);
lean_dec(v_a_3489_);
lean_dec(v_a_3487_);
lean_dec_ref(v_body_3484_);
lean_dec_ref(v_value_3483_);
lean_dec_ref(v_type_3482_);
lean_dec_ref_known(v_e_3344_, 4);
lean_dec(v_declName_3481_);
v_a_3546_ = lean_ctor_get(v___x_3545_, 0);
v_isSharedCheck_3553_ = !lean_is_exclusive(v___x_3545_);
if (v_isSharedCheck_3553_ == 0)
{
v___x_3548_ = v___x_3545_;
v_isShared_3549_ = v_isSharedCheck_3553_;
goto v_resetjp_3547_;
}
else
{
lean_inc(v_a_3546_);
lean_dec(v___x_3545_);
v___x_3548_ = lean_box(0);
v_isShared_3549_ = v_isSharedCheck_3553_;
goto v_resetjp_3547_;
}
v_resetjp_3547_:
{
lean_object* v___x_3551_; 
if (v_isShared_3549_ == 0)
{
v___x_3551_ = v___x_3548_;
goto v_reusejp_3550_;
}
else
{
lean_object* v_reuseFailAlloc_3552_; 
v_reuseFailAlloc_3552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3552_, 0, v_a_3546_);
v___x_3551_ = v_reuseFailAlloc_3552_;
goto v_reusejp_3550_;
}
v_reusejp_3550_:
{
return v___x_3551_;
}
}
}
}
else
{
lean_del_object(v___x_3493_);
lean_dec(v_a_3491_);
lean_dec(v_a_3489_);
lean_dec(v_a_3487_);
lean_dec_ref(v_body_3484_);
lean_dec_ref(v_value_3483_);
lean_dec_ref(v_type_3482_);
lean_dec_ref_known(v_e_3344_, 4);
lean_dec(v_declName_3481_);
return v___x_3543_;
}
}
else
{
lean_object* v___x_3554_; 
lean_inc(v_a_3491_);
lean_inc_ref(v_value_3483_);
v___x_3554_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkFun(v_value_3483_, v_a_3491_, v_a_3345_, v_a_3346_, v_a_3347_, v_a_3348_, v_a_3349_, v_a_3350_, v_a_3351_, v_a_3352_);
if (lean_obj_tag(v___x_3554_) == 0)
{
lean_dec_ref_known(v___x_3554_, 1);
v___y_3524_ = v_a_3345_;
v___y_3525_ = v_a_3346_;
v___y_3526_ = v_a_3347_;
v___y_3527_ = v_a_3348_;
v___y_3528_ = v_a_3349_;
v___y_3529_ = v_a_3350_;
v___y_3530_ = v_a_3351_;
v___y_3531_ = v_a_3352_;
goto v___jp_3523_;
}
else
{
lean_object* v_a_3555_; lean_object* v___x_3557_; uint8_t v_isShared_3558_; uint8_t v_isSharedCheck_3562_; 
lean_del_object(v___x_3493_);
lean_dec(v_a_3491_);
lean_dec(v_a_3489_);
lean_dec(v_a_3487_);
lean_dec_ref(v_body_3484_);
lean_dec_ref(v_value_3483_);
lean_dec_ref(v_type_3482_);
lean_dec_ref_known(v_e_3344_, 4);
lean_dec(v_declName_3481_);
v_a_3555_ = lean_ctor_get(v___x_3554_, 0);
v_isSharedCheck_3562_ = !lean_is_exclusive(v___x_3554_);
if (v_isSharedCheck_3562_ == 0)
{
v___x_3557_ = v___x_3554_;
v_isShared_3558_ = v_isSharedCheck_3562_;
goto v_resetjp_3556_;
}
else
{
lean_inc(v_a_3555_);
lean_dec(v___x_3554_);
v___x_3557_ = lean_box(0);
v_isShared_3558_ = v_isSharedCheck_3562_;
goto v_resetjp_3556_;
}
v_resetjp_3556_:
{
lean_object* v___x_3560_; 
if (v_isShared_3558_ == 0)
{
v___x_3560_ = v___x_3557_;
goto v_reusejp_3559_;
}
else
{
lean_object* v_reuseFailAlloc_3561_; 
v_reuseFailAlloc_3561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3561_, 0, v_a_3555_);
v___x_3560_ = v_reuseFailAlloc_3561_;
goto v_reusejp_3559_;
}
v_reusejp_3559_:
{
return v___x_3560_;
}
}
}
}
}
}
else
{
lean_object* v_a_3567_; lean_object* v___x_3569_; uint8_t v_isShared_3570_; uint8_t v_isSharedCheck_3574_; 
lean_del_object(v___x_3493_);
lean_dec(v_a_3491_);
lean_dec(v_a_3489_);
lean_dec(v_a_3487_);
lean_dec_ref(v_body_3484_);
lean_dec_ref(v_value_3483_);
lean_dec_ref(v_type_3482_);
lean_dec_ref_known(v_e_3344_, 4);
lean_dec(v_declName_3481_);
v_a_3567_ = lean_ctor_get(v___x_3540_, 0);
v_isSharedCheck_3574_ = !lean_is_exclusive(v___x_3540_);
if (v_isSharedCheck_3574_ == 0)
{
v___x_3569_ = v___x_3540_;
v_isShared_3570_ = v_isSharedCheck_3574_;
goto v_resetjp_3568_;
}
else
{
lean_inc(v_a_3567_);
lean_dec(v___x_3540_);
v___x_3569_ = lean_box(0);
v_isShared_3570_ = v_isSharedCheck_3574_;
goto v_resetjp_3568_;
}
v_resetjp_3568_:
{
lean_object* v___x_3572_; 
if (v_isShared_3570_ == 0)
{
v___x_3572_ = v___x_3569_;
goto v_reusejp_3571_;
}
else
{
lean_object* v_reuseFailAlloc_3573_; 
v_reuseFailAlloc_3573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3573_, 0, v_a_3567_);
v___x_3572_ = v_reuseFailAlloc_3573_;
goto v_reusejp_3571_;
}
v_reusejp_3571_:
{
return v___x_3572_;
}
}
}
}
v___jp_3497_:
{
lean_object* v___x_3509_; lean_object* v___x_3510_; lean_object* v___f_3511_; lean_object* v___x_3512_; lean_object* v___x_3513_; lean_object* v___x_3515_; 
v___x_3509_ = lean_box(v_nondep_3485_);
v___x_3510_ = lean_box(v___y_3508_);
lean_inc(v_declName_3481_);
lean_inc_ref(v_type_3482_);
v___f_3511_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore___lam__1___boxed), 19, 9);
lean_closure_set(v___f_3511_, 0, v_body_3484_);
lean_closure_set(v___f_3511_, 1, v_type_3482_);
lean_closure_set(v___f_3511_, 2, v_a_3487_);
lean_closure_set(v___f_3511_, 3, v_declName_3481_);
lean_closure_set(v___f_3511_, 4, v_a_3489_);
lean_closure_set(v___f_3511_, 5, v___x_3509_);
lean_closure_set(v___f_3511_, 6, v_value_3483_);
lean_closure_set(v___f_3511_, 7, v_e_3344_);
lean_closure_set(v___f_3511_, 8, v___x_3510_);
v___x_3512_ = lean_box(v_nondep_3485_);
v___x_3513_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3513_, 0, v___y_3504_);
lean_ctor_set(v___x_3513_, 1, v___x_3512_);
if (v_isShared_3494_ == 0)
{
lean_ctor_set_tag(v___x_3493_, 1);
lean_ctor_set(v___x_3493_, 0, v___x_3513_);
v___x_3515_ = v___x_3493_;
goto v_reusejp_3514_;
}
else
{
lean_object* v_reuseFailAlloc_3522_; 
v_reuseFailAlloc_3522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3522_, 0, v___x_3513_);
v___x_3515_ = v_reuseFailAlloc_3522_;
goto v_reusejp_3514_;
}
v_reusejp_3514_:
{
if (v___y_3501_ == 0)
{
lean_object* v___x_3516_; uint8_t v___x_3517_; 
v___x_3516_ = l_Lean_Expr_looseBVarRange(v_type_3482_);
lean_dec_ref(v_type_3482_);
v___x_3517_ = lean_nat_dec_le(v___x_3516_, v_cleanSuffix_3496_);
lean_dec(v___x_3516_);
if (v___x_3517_ == 0)
{
uint8_t v___x_3518_; lean_object* v___x_3519_; 
v___x_3518_ = 1;
v___x_3519_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder___redArg(v_declName_3481_, v_a_3491_, v___x_3515_, v___x_3518_, v___y_3508_, v___f_3511_, v___y_3498_, v___y_3503_, v___y_3506_, v___y_3499_, v___y_3500_, v___y_3507_, v___y_3502_, v___y_3505_);
return v___x_3519_;
}
else
{
lean_object* v___x_3520_; 
v___x_3520_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder___redArg(v_declName_3481_, v_a_3491_, v___x_3515_, v___y_3501_, v___y_3508_, v___f_3511_, v___y_3498_, v___y_3503_, v___y_3506_, v___y_3499_, v___y_3500_, v___y_3507_, v___y_3502_, v___y_3505_);
return v___x_3520_;
}
}
else
{
lean_object* v___x_3521_; 
lean_dec_ref(v_type_3482_);
v___x_3521_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder___redArg(v_declName_3481_, v_a_3491_, v___x_3515_, v___y_3501_, v___y_3508_, v___f_3511_, v___y_3498_, v___y_3503_, v___y_3506_, v___y_3499_, v___y_3500_, v___y_3507_, v___y_3502_, v___y_3505_);
return v___x_3521_;
}
}
}
v___jp_3523_:
{
lean_object* v___x_3532_; 
lean_inc(v_a_3489_);
v___x_3532_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_substEnv(v_a_3489_, v___y_3524_, v___y_3525_, v___y_3526_, v___y_3527_, v___y_3528_, v___y_3529_, v___y_3530_, v___y_3531_);
if (lean_obj_tag(v___x_3532_) == 0)
{
if (v_nondep_3485_ == 0)
{
lean_object* v_a_3533_; uint8_t v___x_3534_; uint8_t v___x_3535_; 
v_a_3533_ = lean_ctor_get(v___x_3532_, 0);
lean_inc(v_a_3533_);
lean_dec_ref_known(v___x_3532_, 1);
v___x_3534_ = 1;
v___x_3535_ = l_Lean_Expr_hasExprMVar(v_e_3344_);
if (v___x_3535_ == 0)
{
v___y_3498_ = v___y_3524_;
v___y_3499_ = v___y_3527_;
v___y_3500_ = v___y_3528_;
v___y_3501_ = v___x_3534_;
v___y_3502_ = v___y_3530_;
v___y_3503_ = v___y_3525_;
v___y_3504_ = v_a_3533_;
v___y_3505_ = v___y_3531_;
v___y_3506_ = v___y_3526_;
v___y_3507_ = v___y_3529_;
v___y_3508_ = v___x_3534_;
goto v___jp_3497_;
}
else
{
v___y_3498_ = v___y_3524_;
v___y_3499_ = v___y_3527_;
v___y_3500_ = v___y_3528_;
v___y_3501_ = v___x_3534_;
v___y_3502_ = v___y_3530_;
v___y_3503_ = v___y_3525_;
v___y_3504_ = v_a_3533_;
v___y_3505_ = v___y_3531_;
v___y_3506_ = v___y_3526_;
v___y_3507_ = v___y_3529_;
v___y_3508_ = v_nondep_3485_;
goto v___jp_3497_;
}
}
else
{
lean_object* v_a_3536_; uint8_t v___x_3537_; 
v_a_3536_ = lean_ctor_get(v___x_3532_, 0);
lean_inc(v_a_3536_);
lean_dec_ref_known(v___x_3532_, 1);
v___x_3537_ = 0;
v___y_3498_ = v___y_3524_;
v___y_3499_ = v___y_3527_;
v___y_3500_ = v___y_3528_;
v___y_3501_ = v___x_3537_;
v___y_3502_ = v___y_3530_;
v___y_3503_ = v___y_3525_;
v___y_3504_ = v_a_3536_;
v___y_3505_ = v___y_3531_;
v___y_3506_ = v___y_3526_;
v___y_3507_ = v___y_3529_;
v___y_3508_ = v___x_3537_;
goto v___jp_3497_;
}
}
else
{
lean_del_object(v___x_3493_);
lean_dec(v_a_3491_);
lean_dec(v_a_3489_);
lean_dec(v_a_3487_);
lean_dec_ref(v_body_3484_);
lean_dec_ref(v_value_3483_);
lean_dec_ref(v_type_3482_);
lean_dec_ref_known(v_e_3344_, 4);
lean_dec(v_declName_3481_);
return v___x_3532_;
}
}
}
}
else
{
lean_dec(v_a_3489_);
lean_dec(v_a_3487_);
lean_dec_ref(v_body_3484_);
lean_dec_ref(v_value_3483_);
lean_dec_ref(v_type_3482_);
lean_dec_ref_known(v_e_3344_, 4);
lean_dec(v_declName_3481_);
return v___x_3490_;
}
}
else
{
lean_dec(v_a_3487_);
lean_dec_ref(v_body_3484_);
lean_dec_ref(v_value_3483_);
lean_dec_ref(v_type_3482_);
lean_dec_ref_known(v_e_3344_, 4);
lean_dec(v_declName_3481_);
return v___x_3488_;
}
}
else
{
lean_dec_ref(v_body_3484_);
lean_dec_ref(v_value_3483_);
lean_dec_ref(v_type_3482_);
lean_dec_ref_known(v_e_3344_, 4);
lean_dec(v_declName_3481_);
return v___x_3486_;
}
}
default: 
{
lean_object* v___x_3576_; lean_object* v___x_3577_; 
lean_dec_ref(v_e_3344_);
v___x_3576_ = lean_obj_once(&l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore___closed__1, &l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore___closed__1_once, _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore___closed__1);
v___x_3577_ = l_panic___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_inferTypeO_spec__0(v___x_3576_, v_a_3345_, v_a_3346_, v_a_3347_, v_a_3348_, v_a_3349_, v_a_3350_, v_a_3351_, v_a_3352_);
return v___x_3577_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg(lean_object* v_e_3578_, lean_object* v_a_3579_, lean_object* v_a_3580_, lean_object* v_a_3581_, lean_object* v_a_3582_, lean_object* v_a_3583_, lean_object* v_a_3584_, lean_object* v_a_3585_){
_start:
{
lean_object* v___x_3587_; lean_object* v_visitedClosed_3588_; lean_object* v___x_3589_; 
v___x_3587_ = lean_st_ref_get(v_a_3579_);
v_visitedClosed_3588_ = lean_ctor_get(v___x_3587_, 3);
lean_inc_ref(v_visitedClosed_3588_);
lean_dec(v___x_3587_);
v___x_3589_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__0___redArg(v_visitedClosed_3588_, v_e_3578_);
lean_dec_ref(v_visitedClosed_3588_);
if (lean_obj_tag(v___x_3589_) == 1)
{
lean_object* v_val_3590_; lean_object* v___x_3592_; uint8_t v_isShared_3593_; uint8_t v_isSharedCheck_3597_; 
lean_dec_ref(v_e_3578_);
v_val_3590_ = lean_ctor_get(v___x_3589_, 0);
v_isSharedCheck_3597_ = !lean_is_exclusive(v___x_3589_);
if (v_isSharedCheck_3597_ == 0)
{
v___x_3592_ = v___x_3589_;
v_isShared_3593_ = v_isSharedCheck_3597_;
goto v_resetjp_3591_;
}
else
{
lean_inc(v_val_3590_);
lean_dec(v___x_3589_);
v___x_3592_ = lean_box(0);
v_isShared_3593_ = v_isSharedCheck_3597_;
goto v_resetjp_3591_;
}
v_resetjp_3591_:
{
lean_object* v___x_3595_; 
if (v_isShared_3593_ == 0)
{
lean_ctor_set_tag(v___x_3592_, 0);
v___x_3595_ = v___x_3592_;
goto v_reusejp_3594_;
}
else
{
lean_object* v_reuseFailAlloc_3596_; 
v_reuseFailAlloc_3596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3596_, 0, v_val_3590_);
v___x_3595_ = v_reuseFailAlloc_3596_;
goto v_reusejp_3594_;
}
v_reusejp_3594_:
{
return v___x_3595_;
}
}
}
else
{
lean_object* v___x_3598_; lean_object* v___x_3599_; lean_object* v_visited_3600_; lean_object* v_types_3601_; lean_object* v_subst_3602_; lean_object* v_visitedClosed_3603_; lean_object* v_hasDepLetCache_3604_; lean_object* v_numConverted_3605_; lean_object* v___x_3607_; uint8_t v_isShared_3608_; uint8_t v_isSharedCheck_3675_; 
lean_dec(v___x_3589_);
v___x_3598_ = lean_obj_once(&l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg___closed__2, &l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg___closed__2_once, _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg___closed__2);
v___x_3599_ = lean_st_ref_take(v_a_3579_);
v_visited_3600_ = lean_ctor_get(v___x_3599_, 0);
v_types_3601_ = lean_ctor_get(v___x_3599_, 1);
v_subst_3602_ = lean_ctor_get(v___x_3599_, 2);
v_visitedClosed_3603_ = lean_ctor_get(v___x_3599_, 3);
v_hasDepLetCache_3604_ = lean_ctor_get(v___x_3599_, 4);
v_numConverted_3605_ = lean_ctor_get(v___x_3599_, 5);
v_isSharedCheck_3675_ = !lean_is_exclusive(v___x_3599_);
if (v_isSharedCheck_3675_ == 0)
{
v___x_3607_ = v___x_3599_;
v_isShared_3608_ = v_isSharedCheck_3675_;
goto v_resetjp_3606_;
}
else
{
lean_inc(v_numConverted_3605_);
lean_inc(v_hasDepLetCache_3604_);
lean_inc(v_visitedClosed_3603_);
lean_inc(v_subst_3602_);
lean_inc(v_types_3601_);
lean_inc(v_visited_3600_);
lean_dec(v___x_3599_);
v___x_3607_ = lean_box(0);
v_isShared_3608_ = v_isSharedCheck_3675_;
goto v_resetjp_3606_;
}
v_resetjp_3606_:
{
lean_object* v___x_3609_; lean_object* v___x_3611_; 
v___x_3609_ = lean_obj_once(&l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withNewScope___redArg___closed__1, &l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withNewScope___redArg___closed__1_once, _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withNewScope___redArg___closed__1);
if (v_isShared_3608_ == 0)
{
lean_ctor_set(v___x_3607_, 2, v___x_3609_);
lean_ctor_set(v___x_3607_, 1, v___x_3609_);
lean_ctor_set(v___x_3607_, 0, v___x_3609_);
v___x_3611_ = v___x_3607_;
goto v_reusejp_3610_;
}
else
{
lean_object* v_reuseFailAlloc_3674_; 
v_reuseFailAlloc_3674_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3674_, 0, v___x_3609_);
lean_ctor_set(v_reuseFailAlloc_3674_, 1, v___x_3609_);
lean_ctor_set(v_reuseFailAlloc_3674_, 2, v___x_3609_);
lean_ctor_set(v_reuseFailAlloc_3674_, 3, v_visitedClosed_3603_);
lean_ctor_set(v_reuseFailAlloc_3674_, 4, v_hasDepLetCache_3604_);
lean_ctor_set(v_reuseFailAlloc_3674_, 5, v_numConverted_3605_);
v___x_3611_ = v_reuseFailAlloc_3674_;
goto v_reusejp_3610_;
}
v_reusejp_3610_:
{
lean_object* v___x_3612_; lean_object* v_r_3613_; 
v___x_3612_ = lean_st_ref_put(v_a_3579_, v___x_3611_);
lean_inc_ref(v_e_3578_);
v_r_3613_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore(v_e_3578_, v___x_3598_, v_a_3579_, v_a_3580_, v_a_3581_, v_a_3582_, v_a_3583_, v_a_3584_, v_a_3585_);
if (lean_obj_tag(v_r_3613_) == 0)
{
lean_object* v_a_3614_; lean_object* v___x_3616_; uint8_t v_isShared_3617_; uint8_t v_isSharedCheck_3654_; 
v_a_3614_ = lean_ctor_get(v_r_3613_, 0);
v_isSharedCheck_3654_ = !lean_is_exclusive(v_r_3613_);
if (v_isSharedCheck_3654_ == 0)
{
v___x_3616_ = v_r_3613_;
v_isShared_3617_ = v_isSharedCheck_3654_;
goto v_resetjp_3615_;
}
else
{
lean_inc(v_a_3614_);
lean_dec(v_r_3613_);
v___x_3616_ = lean_box(0);
v_isShared_3617_ = v_isSharedCheck_3654_;
goto v_resetjp_3615_;
}
v_resetjp_3615_:
{
lean_object* v___x_3619_; 
lean_inc(v_a_3614_);
if (v_isShared_3617_ == 0)
{
lean_ctor_set_tag(v___x_3616_, 1);
v___x_3619_ = v___x_3616_;
goto v_reusejp_3618_;
}
else
{
lean_object* v_reuseFailAlloc_3653_; 
v_reuseFailAlloc_3653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3653_, 0, v_a_3614_);
v___x_3619_ = v_reuseFailAlloc_3653_;
goto v_reusejp_3618_;
}
v_reusejp_3618_:
{
lean_object* v___x_3620_; 
v___x_3620_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg___lam__0(v_a_3579_, v_visited_3600_, v_types_3601_, v_subst_3602_, v___x_3619_);
lean_dec_ref(v___x_3619_);
if (lean_obj_tag(v___x_3620_) == 0)
{
lean_object* v___x_3622_; uint8_t v_isShared_3623_; uint8_t v_isSharedCheck_3643_; 
v_isSharedCheck_3643_ = !lean_is_exclusive(v___x_3620_);
if (v_isSharedCheck_3643_ == 0)
{
lean_object* v_unused_3644_; 
v_unused_3644_ = lean_ctor_get(v___x_3620_, 0);
lean_dec(v_unused_3644_);
v___x_3622_ = v___x_3620_;
v_isShared_3623_ = v_isSharedCheck_3643_;
goto v_resetjp_3621_;
}
else
{
lean_dec(v___x_3620_);
v___x_3622_ = lean_box(0);
v_isShared_3623_ = v_isSharedCheck_3643_;
goto v_resetjp_3621_;
}
v_resetjp_3621_:
{
lean_object* v___x_3624_; lean_object* v_visited_3625_; lean_object* v_types_3626_; lean_object* v_subst_3627_; lean_object* v_visitedClosed_3628_; lean_object* v_hasDepLetCache_3629_; lean_object* v_numConverted_3630_; lean_object* v___x_3632_; uint8_t v_isShared_3633_; uint8_t v_isSharedCheck_3642_; 
v___x_3624_ = lean_st_ref_take(v_a_3579_);
v_visited_3625_ = lean_ctor_get(v___x_3624_, 0);
v_types_3626_ = lean_ctor_get(v___x_3624_, 1);
v_subst_3627_ = lean_ctor_get(v___x_3624_, 2);
v_visitedClosed_3628_ = lean_ctor_get(v___x_3624_, 3);
v_hasDepLetCache_3629_ = lean_ctor_get(v___x_3624_, 4);
v_numConverted_3630_ = lean_ctor_get(v___x_3624_, 5);
v_isSharedCheck_3642_ = !lean_is_exclusive(v___x_3624_);
if (v_isSharedCheck_3642_ == 0)
{
v___x_3632_ = v___x_3624_;
v_isShared_3633_ = v_isSharedCheck_3642_;
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
v_isShared_3633_ = v_isSharedCheck_3642_;
goto v_resetjp_3631_;
}
v_resetjp_3631_:
{
lean_object* v___x_3634_; lean_object* v___x_3636_; 
lean_inc(v_a_3614_);
v___x_3634_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__1___redArg(v_visitedClosed_3628_, v_e_3578_, v_a_3614_);
if (v_isShared_3633_ == 0)
{
lean_ctor_set(v___x_3632_, 3, v___x_3634_);
v___x_3636_ = v___x_3632_;
goto v_reusejp_3635_;
}
else
{
lean_object* v_reuseFailAlloc_3641_; 
v_reuseFailAlloc_3641_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3641_, 0, v_visited_3625_);
lean_ctor_set(v_reuseFailAlloc_3641_, 1, v_types_3626_);
lean_ctor_set(v_reuseFailAlloc_3641_, 2, v_subst_3627_);
lean_ctor_set(v_reuseFailAlloc_3641_, 3, v___x_3634_);
lean_ctor_set(v_reuseFailAlloc_3641_, 4, v_hasDepLetCache_3629_);
lean_ctor_set(v_reuseFailAlloc_3641_, 5, v_numConverted_3630_);
v___x_3636_ = v_reuseFailAlloc_3641_;
goto v_reusejp_3635_;
}
v_reusejp_3635_:
{
lean_object* v___x_3637_; lean_object* v___x_3639_; 
v___x_3637_ = lean_st_ref_put(v_a_3579_, v___x_3636_);
if (v_isShared_3623_ == 0)
{
lean_ctor_set(v___x_3622_, 0, v_a_3614_);
v___x_3639_ = v___x_3622_;
goto v_reusejp_3638_;
}
else
{
lean_object* v_reuseFailAlloc_3640_; 
v_reuseFailAlloc_3640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3640_, 0, v_a_3614_);
v___x_3639_ = v_reuseFailAlloc_3640_;
goto v_reusejp_3638_;
}
v_reusejp_3638_:
{
return v___x_3639_;
}
}
}
}
}
else
{
lean_object* v_a_3645_; lean_object* v___x_3647_; uint8_t v_isShared_3648_; uint8_t v_isSharedCheck_3652_; 
lean_dec(v_a_3614_);
lean_dec_ref(v_e_3578_);
v_a_3645_ = lean_ctor_get(v___x_3620_, 0);
v_isSharedCheck_3652_ = !lean_is_exclusive(v___x_3620_);
if (v_isSharedCheck_3652_ == 0)
{
v___x_3647_ = v___x_3620_;
v_isShared_3648_ = v_isSharedCheck_3652_;
goto v_resetjp_3646_;
}
else
{
lean_inc(v_a_3645_);
lean_dec(v___x_3620_);
v___x_3647_ = lean_box(0);
v_isShared_3648_ = v_isSharedCheck_3652_;
goto v_resetjp_3646_;
}
v_resetjp_3646_:
{
lean_object* v___x_3650_; 
if (v_isShared_3648_ == 0)
{
v___x_3650_ = v___x_3647_;
goto v_reusejp_3649_;
}
else
{
lean_object* v_reuseFailAlloc_3651_; 
v_reuseFailAlloc_3651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3651_, 0, v_a_3645_);
v___x_3650_ = v_reuseFailAlloc_3651_;
goto v_reusejp_3649_;
}
v_reusejp_3649_:
{
return v___x_3650_;
}
}
}
}
}
}
else
{
lean_object* v_a_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; 
lean_dec_ref(v_e_3578_);
v_a_3655_ = lean_ctor_get(v_r_3613_, 0);
lean_inc(v_a_3655_);
lean_dec_ref_known(v_r_3613_, 1);
v___x_3656_ = lean_box(0);
v___x_3657_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg___lam__0(v_a_3579_, v_visited_3600_, v_types_3601_, v_subst_3602_, v___x_3656_);
if (lean_obj_tag(v___x_3657_) == 0)
{
lean_object* v___x_3659_; uint8_t v_isShared_3660_; uint8_t v_isSharedCheck_3664_; 
v_isSharedCheck_3664_ = !lean_is_exclusive(v___x_3657_);
if (v_isSharedCheck_3664_ == 0)
{
lean_object* v_unused_3665_; 
v_unused_3665_ = lean_ctor_get(v___x_3657_, 0);
lean_dec(v_unused_3665_);
v___x_3659_ = v___x_3657_;
v_isShared_3660_ = v_isSharedCheck_3664_;
goto v_resetjp_3658_;
}
else
{
lean_dec(v___x_3657_);
v___x_3659_ = lean_box(0);
v_isShared_3660_ = v_isSharedCheck_3664_;
goto v_resetjp_3658_;
}
v_resetjp_3658_:
{
lean_object* v___x_3662_; 
if (v_isShared_3660_ == 0)
{
lean_ctor_set_tag(v___x_3659_, 1);
lean_ctor_set(v___x_3659_, 0, v_a_3655_);
v___x_3662_ = v___x_3659_;
goto v_reusejp_3661_;
}
else
{
lean_object* v_reuseFailAlloc_3663_; 
v_reuseFailAlloc_3663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3663_, 0, v_a_3655_);
v___x_3662_ = v_reuseFailAlloc_3663_;
goto v_reusejp_3661_;
}
v_reusejp_3661_:
{
return v___x_3662_;
}
}
}
else
{
lean_object* v_a_3666_; lean_object* v___x_3668_; uint8_t v_isShared_3669_; uint8_t v_isSharedCheck_3673_; 
lean_dec(v_a_3655_);
v_a_3666_ = lean_ctor_get(v___x_3657_, 0);
v_isSharedCheck_3673_ = !lean_is_exclusive(v___x_3657_);
if (v_isSharedCheck_3673_ == 0)
{
v___x_3668_ = v___x_3657_;
v_isShared_3669_ = v_isSharedCheck_3673_;
goto v_resetjp_3667_;
}
else
{
lean_inc(v_a_3666_);
lean_dec(v___x_3657_);
v___x_3668_ = lean_box(0);
v_isShared_3669_ = v_isSharedCheck_3673_;
goto v_resetjp_3667_;
}
v_resetjp_3667_:
{
lean_object* v___x_3671_; 
if (v_isShared_3669_ == 0)
{
v___x_3671_ = v___x_3668_;
goto v_reusejp_3670_;
}
else
{
lean_object* v_reuseFailAlloc_3672_; 
v_reuseFailAlloc_3672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3672_, 0, v_a_3666_);
v___x_3671_ = v_reuseFailAlloc_3672_;
goto v_reusejp_3670_;
}
v_reusejp_3670_:
{
return v___x_3671_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visit(lean_object* v_e_3676_, lean_object* v_a_3677_, lean_object* v_a_3678_, lean_object* v_a_3679_, lean_object* v_a_3680_, lean_object* v_a_3681_, lean_object* v_a_3682_, lean_object* v_a_3683_, lean_object* v_a_3684_){
_start:
{
lean_object* v___y_3687_; lean_object* v___y_3688_; lean_object* v___y_3689_; lean_object* v___y_3690_; lean_object* v___y_3691_; lean_object* v___y_3692_; lean_object* v___y_3693_; lean_object* v___y_3694_; 
switch(lean_obj_tag(v_e_3676_))
{
case 0:
{
lean_object* v___x_3752_; 
v___x_3752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3752_, 0, v_e_3676_);
return v___x_3752_;
}
case 1:
{
lean_object* v___x_3753_; 
v___x_3753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3753_, 0, v_e_3676_);
return v___x_3753_;
}
case 2:
{
lean_object* v___x_3754_; 
v___x_3754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3754_, 0, v_e_3676_);
return v___x_3754_;
}
case 3:
{
lean_object* v___x_3755_; 
v___x_3755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3755_, 0, v_e_3676_);
return v___x_3755_;
}
case 4:
{
lean_object* v___x_3756_; 
v___x_3756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3756_, 0, v_e_3676_);
return v___x_3756_;
}
case 9:
{
lean_object* v___x_3757_; 
v___x_3757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3757_, 0, v_e_3676_);
return v___x_3757_;
}
default: 
{
lean_object* v_numCandidates_3758_; lean_object* v_cleanSuffix_3759_; lean_object* v___x_3760_; uint8_t v___x_3761_; 
v_numCandidates_3758_ = lean_ctor_get(v_a_3677_, 1);
v_cleanSuffix_3759_ = lean_ctor_get(v_a_3677_, 2);
v___x_3760_ = lean_unsigned_to_nat(0u);
v___x_3761_ = lean_nat_dec_eq(v_numCandidates_3758_, v___x_3760_);
if (v___x_3761_ == 0)
{
lean_object* v___x_3762_; uint8_t v___x_3763_; 
v___x_3762_ = l_Lean_Expr_looseBVarRange(v_e_3676_);
v___x_3763_ = lean_nat_dec_le(v___x_3762_, v_cleanSuffix_3759_);
lean_dec(v___x_3762_);
if (v___x_3763_ == 0)
{
v___y_3687_ = v_a_3677_;
v___y_3688_ = v_a_3678_;
v___y_3689_ = v_a_3679_;
v___y_3690_ = v_a_3680_;
v___y_3691_ = v_a_3681_;
v___y_3692_ = v_a_3682_;
v___y_3693_ = v_a_3683_;
v___y_3694_ = v_a_3684_;
goto v___jp_3686_;
}
else
{
goto v___jp_3733_;
}
}
else
{
goto v___jp_3733_;
}
}
}
v___jp_3686_:
{
uint8_t v___x_3695_; 
v___x_3695_ = l_Lean_Expr_hasLooseBVars(v_e_3676_);
if (v___x_3695_ == 0)
{
lean_object* v___x_3696_; 
v___x_3696_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg(v_e_3676_, v___y_3688_, v___y_3689_, v___y_3690_, v___y_3691_, v___y_3692_, v___y_3693_, v___y_3694_);
return v___x_3696_;
}
else
{
lean_object* v___x_3697_; lean_object* v_visited_3698_; lean_object* v___x_3699_; 
v___x_3697_ = lean_st_ref_get(v___y_3688_);
v_visited_3698_ = lean_ctor_get(v___x_3697_, 0);
lean_inc_ref(v_visited_3698_);
lean_dec(v___x_3697_);
v___x_3699_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__0___redArg(v_visited_3698_, v_e_3676_);
lean_dec_ref(v_visited_3698_);
if (lean_obj_tag(v___x_3699_) == 1)
{
lean_object* v_val_3700_; lean_object* v___x_3702_; uint8_t v_isShared_3703_; uint8_t v_isSharedCheck_3707_; 
lean_dec_ref(v_e_3676_);
v_val_3700_ = lean_ctor_get(v___x_3699_, 0);
v_isSharedCheck_3707_ = !lean_is_exclusive(v___x_3699_);
if (v_isSharedCheck_3707_ == 0)
{
v___x_3702_ = v___x_3699_;
v_isShared_3703_ = v_isSharedCheck_3707_;
goto v_resetjp_3701_;
}
else
{
lean_inc(v_val_3700_);
lean_dec(v___x_3699_);
v___x_3702_ = lean_box(0);
v_isShared_3703_ = v_isSharedCheck_3707_;
goto v_resetjp_3701_;
}
v_resetjp_3701_:
{
lean_object* v___x_3705_; 
if (v_isShared_3703_ == 0)
{
lean_ctor_set_tag(v___x_3702_, 0);
v___x_3705_ = v___x_3702_;
goto v_reusejp_3704_;
}
else
{
lean_object* v_reuseFailAlloc_3706_; 
v_reuseFailAlloc_3706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3706_, 0, v_val_3700_);
v___x_3705_ = v_reuseFailAlloc_3706_;
goto v_reusejp_3704_;
}
v_reusejp_3704_:
{
return v___x_3705_;
}
}
}
else
{
lean_object* v___x_3708_; 
lean_dec(v___x_3699_);
lean_inc_ref(v_e_3676_);
v___x_3708_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore(v_e_3676_, v___y_3687_, v___y_3688_, v___y_3689_, v___y_3690_, v___y_3691_, v___y_3692_, v___y_3693_, v___y_3694_);
if (lean_obj_tag(v___x_3708_) == 0)
{
lean_object* v_a_3709_; lean_object* v___x_3711_; uint8_t v_isShared_3712_; uint8_t v_isSharedCheck_3732_; 
v_a_3709_ = lean_ctor_get(v___x_3708_, 0);
v_isSharedCheck_3732_ = !lean_is_exclusive(v___x_3708_);
if (v_isSharedCheck_3732_ == 0)
{
v___x_3711_ = v___x_3708_;
v_isShared_3712_ = v_isSharedCheck_3732_;
goto v_resetjp_3710_;
}
else
{
lean_inc(v_a_3709_);
lean_dec(v___x_3708_);
v___x_3711_ = lean_box(0);
v_isShared_3712_ = v_isSharedCheck_3732_;
goto v_resetjp_3710_;
}
v_resetjp_3710_:
{
lean_object* v___x_3713_; lean_object* v_visited_3714_; lean_object* v_types_3715_; lean_object* v_subst_3716_; lean_object* v_visitedClosed_3717_; lean_object* v_hasDepLetCache_3718_; lean_object* v_numConverted_3719_; lean_object* v___x_3721_; uint8_t v_isShared_3722_; uint8_t v_isSharedCheck_3731_; 
v___x_3713_ = lean_st_ref_take(v___y_3688_);
v_visited_3714_ = lean_ctor_get(v___x_3713_, 0);
v_types_3715_ = lean_ctor_get(v___x_3713_, 1);
v_subst_3716_ = lean_ctor_get(v___x_3713_, 2);
v_visitedClosed_3717_ = lean_ctor_get(v___x_3713_, 3);
v_hasDepLetCache_3718_ = lean_ctor_get(v___x_3713_, 4);
v_numConverted_3719_ = lean_ctor_get(v___x_3713_, 5);
v_isSharedCheck_3731_ = !lean_is_exclusive(v___x_3713_);
if (v_isSharedCheck_3731_ == 0)
{
v___x_3721_ = v___x_3713_;
v_isShared_3722_ = v_isSharedCheck_3731_;
goto v_resetjp_3720_;
}
else
{
lean_inc(v_numConverted_3719_);
lean_inc(v_hasDepLetCache_3718_);
lean_inc(v_visitedClosed_3717_);
lean_inc(v_subst_3716_);
lean_inc(v_types_3715_);
lean_inc(v_visited_3714_);
lean_dec(v___x_3713_);
v___x_3721_ = lean_box(0);
v_isShared_3722_ = v_isSharedCheck_3731_;
goto v_resetjp_3720_;
}
v_resetjp_3720_:
{
lean_object* v___x_3723_; lean_object* v___x_3725_; 
lean_inc(v_a_3709_);
v___x_3723_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet_cached_spec__1___redArg(v_visited_3714_, v_e_3676_, v_a_3709_);
if (v_isShared_3722_ == 0)
{
lean_ctor_set(v___x_3721_, 0, v___x_3723_);
v___x_3725_ = v___x_3721_;
goto v_reusejp_3724_;
}
else
{
lean_object* v_reuseFailAlloc_3730_; 
v_reuseFailAlloc_3730_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3730_, 0, v___x_3723_);
lean_ctor_set(v_reuseFailAlloc_3730_, 1, v_types_3715_);
lean_ctor_set(v_reuseFailAlloc_3730_, 2, v_subst_3716_);
lean_ctor_set(v_reuseFailAlloc_3730_, 3, v_visitedClosed_3717_);
lean_ctor_set(v_reuseFailAlloc_3730_, 4, v_hasDepLetCache_3718_);
lean_ctor_set(v_reuseFailAlloc_3730_, 5, v_numConverted_3719_);
v___x_3725_ = v_reuseFailAlloc_3730_;
goto v_reusejp_3724_;
}
v_reusejp_3724_:
{
lean_object* v___x_3726_; lean_object* v___x_3728_; 
v___x_3726_ = lean_st_ref_put(v___y_3688_, v___x_3725_);
if (v_isShared_3712_ == 0)
{
v___x_3728_ = v___x_3711_;
goto v_reusejp_3727_;
}
else
{
lean_object* v_reuseFailAlloc_3729_; 
v_reuseFailAlloc_3729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3729_, 0, v_a_3709_);
v___x_3728_ = v_reuseFailAlloc_3729_;
goto v_reusejp_3727_;
}
v_reusejp_3727_:
{
return v___x_3728_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_3676_);
return v___x_3708_;
}
}
}
}
v___jp_3733_:
{
lean_object* v___x_3734_; 
lean_inc_ref(v_e_3676_);
v___x_3734_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet(v_e_3676_, v_a_3677_, v_a_3678_, v_a_3679_, v_a_3680_, v_a_3681_, v_a_3682_, v_a_3683_, v_a_3684_);
if (lean_obj_tag(v___x_3734_) == 0)
{
lean_object* v_a_3735_; lean_object* v___x_3737_; uint8_t v_isShared_3738_; uint8_t v_isSharedCheck_3743_; 
v_a_3735_ = lean_ctor_get(v___x_3734_, 0);
v_isSharedCheck_3743_ = !lean_is_exclusive(v___x_3734_);
if (v_isSharedCheck_3743_ == 0)
{
v___x_3737_ = v___x_3734_;
v_isShared_3738_ = v_isSharedCheck_3743_;
goto v_resetjp_3736_;
}
else
{
lean_inc(v_a_3735_);
lean_dec(v___x_3734_);
v___x_3737_ = lean_box(0);
v_isShared_3738_ = v_isSharedCheck_3743_;
goto v_resetjp_3736_;
}
v_resetjp_3736_:
{
uint8_t v___x_3739_; 
v___x_3739_ = lean_unbox(v_a_3735_);
lean_dec(v_a_3735_);
if (v___x_3739_ == 0)
{
lean_object* v___x_3741_; 
if (v_isShared_3738_ == 0)
{
lean_ctor_set(v___x_3737_, 0, v_e_3676_);
v___x_3741_ = v___x_3737_;
goto v_reusejp_3740_;
}
else
{
lean_object* v_reuseFailAlloc_3742_; 
v_reuseFailAlloc_3742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3742_, 0, v_e_3676_);
v___x_3741_ = v_reuseFailAlloc_3742_;
goto v_reusejp_3740_;
}
v_reusejp_3740_:
{
return v___x_3741_;
}
}
else
{
lean_del_object(v___x_3737_);
v___y_3687_ = v_a_3677_;
v___y_3688_ = v_a_3678_;
v___y_3689_ = v_a_3679_;
v___y_3690_ = v_a_3680_;
v___y_3691_ = v_a_3681_;
v___y_3692_ = v_a_3682_;
v___y_3693_ = v_a_3683_;
v___y_3694_ = v_a_3684_;
goto v___jp_3686_;
}
}
}
else
{
lean_object* v_a_3744_; lean_object* v___x_3746_; uint8_t v_isShared_3747_; uint8_t v_isSharedCheck_3751_; 
lean_dec_ref(v_e_3676_);
v_a_3744_ = lean_ctor_get(v___x_3734_, 0);
v_isSharedCheck_3751_ = !lean_is_exclusive(v___x_3734_);
if (v_isSharedCheck_3751_ == 0)
{
v___x_3746_ = v___x_3734_;
v_isShared_3747_ = v_isSharedCheck_3751_;
goto v_resetjp_3745_;
}
else
{
lean_inc(v_a_3744_);
lean_dec(v___x_3734_);
v___x_3746_ = lean_box(0);
v_isShared_3747_ = v_isSharedCheck_3751_;
goto v_resetjp_3745_;
}
v_resetjp_3745_:
{
lean_object* v___x_3749_; 
if (v_isShared_3747_ == 0)
{
v___x_3749_ = v___x_3746_;
goto v_reusejp_3748_;
}
else
{
lean_object* v_reuseFailAlloc_3750_; 
v_reuseFailAlloc_3750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3750_, 0, v_a_3744_);
v___x_3749_ = v_reuseFailAlloc_3750_;
goto v_reusejp_3748_;
}
v_reusejp_3748_:
{
return v___x_3749_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore___lam__0(lean_object* v_body_3764_, lean_object* v_binderType_3765_, lean_object* v_a_3766_, lean_object* v_binderName_3767_, uint8_t v_binderInfo_3768_, lean_object* v_e_3769_, lean_object* v_x_3770_, lean_object* v___y_3771_, lean_object* v___y_3772_, lean_object* v___y_3773_, lean_object* v___y_3774_, lean_object* v___y_3775_, lean_object* v___y_3776_, lean_object* v___y_3777_, lean_object* v___y_3778_){
_start:
{
lean_object* v___x_3780_; 
lean_inc_ref(v_body_3764_);
v___x_3780_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visit(v_body_3764_, v___y_3771_, v___y_3772_, v___y_3773_, v___y_3774_, v___y_3775_, v___y_3776_, v___y_3777_, v___y_3778_);
if (lean_obj_tag(v___x_3780_) == 0)
{
lean_object* v_a_3781_; lean_object* v___x_3783_; uint8_t v_isShared_3784_; uint8_t v_isSharedCheck_3796_; 
v_a_3781_ = lean_ctor_get(v___x_3780_, 0);
v_isSharedCheck_3796_ = !lean_is_exclusive(v___x_3780_);
if (v_isSharedCheck_3796_ == 0)
{
v___x_3783_ = v___x_3780_;
v_isShared_3784_ = v_isSharedCheck_3796_;
goto v_resetjp_3782_;
}
else
{
lean_inc(v_a_3781_);
lean_dec(v___x_3780_);
v___x_3783_ = lean_box(0);
v_isShared_3784_ = v_isSharedCheck_3796_;
goto v_resetjp_3782_;
}
v_resetjp_3782_:
{
size_t v___x_3785_; size_t v___x_3786_; uint8_t v___x_3787_; 
v___x_3785_ = lean_ptr_addr(v_binderType_3765_);
v___x_3786_ = lean_ptr_addr(v_a_3766_);
v___x_3787_ = lean_usize_dec_eq(v___x_3785_, v___x_3786_);
if (v___x_3787_ == 0)
{
lean_object* v___x_3788_; 
lean_del_object(v___x_3783_);
lean_dec_ref(v_e_3769_);
lean_dec_ref(v_body_3764_);
v___x_3788_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__4___redArg(v_binderName_3767_, v_binderInfo_3768_, v_a_3766_, v_a_3781_, v___y_3773_, v___y_3774_, v___y_3775_, v___y_3776_, v___y_3777_, v___y_3778_);
return v___x_3788_;
}
else
{
size_t v___x_3789_; size_t v___x_3790_; uint8_t v___x_3791_; 
v___x_3789_ = lean_ptr_addr(v_body_3764_);
lean_dec_ref(v_body_3764_);
v___x_3790_ = lean_ptr_addr(v_a_3781_);
v___x_3791_ = lean_usize_dec_eq(v___x_3789_, v___x_3790_);
if (v___x_3791_ == 0)
{
lean_object* v___x_3792_; 
lean_del_object(v___x_3783_);
lean_dec_ref(v_e_3769_);
v___x_3792_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__4___redArg(v_binderName_3767_, v_binderInfo_3768_, v_a_3766_, v_a_3781_, v___y_3773_, v___y_3774_, v___y_3775_, v___y_3776_, v___y_3777_, v___y_3778_);
return v___x_3792_;
}
else
{
lean_object* v___x_3794_; 
lean_dec(v_a_3781_);
lean_dec(v_binderName_3767_);
lean_dec_ref(v_a_3766_);
if (v_isShared_3784_ == 0)
{
lean_ctor_set(v___x_3783_, 0, v_e_3769_);
v___x_3794_ = v___x_3783_;
goto v_reusejp_3793_;
}
else
{
lean_object* v_reuseFailAlloc_3795_; 
v_reuseFailAlloc_3795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3795_, 0, v_e_3769_);
v___x_3794_ = v_reuseFailAlloc_3795_;
goto v_reusejp_3793_;
}
v_reusejp_3793_:
{
return v___x_3794_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_3769_);
lean_dec(v_binderName_3767_);
lean_dec_ref(v_a_3766_);
lean_dec_ref(v_body_3764_);
return v___x_3780_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitForall___boxed(lean_object* v_e_3797_, lean_object* v_a_3798_, lean_object* v_a_3799_, lean_object* v_a_3800_, lean_object* v_a_3801_, lean_object* v_a_3802_, lean_object* v_a_3803_, lean_object* v_a_3804_, lean_object* v_a_3805_, lean_object* v_a_3806_){
_start:
{
lean_object* v_res_3807_; 
v_res_3807_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitForall(v_e_3797_, v_a_3798_, v_a_3799_, v_a_3800_, v_a_3801_, v_a_3802_, v_a_3803_, v_a_3804_, v_a_3805_);
lean_dec(v_a_3805_);
lean_dec_ref(v_a_3804_);
lean_dec(v_a_3803_);
lean_dec_ref(v_a_3802_);
lean_dec(v_a_3801_);
lean_dec_ref(v_a_3800_);
lean_dec(v_a_3799_);
lean_dec_ref(v_a_3798_);
return v_res_3807_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg___boxed(lean_object* v_e_3808_, lean_object* v_a_3809_, lean_object* v_a_3810_, lean_object* v_a_3811_, lean_object* v_a_3812_, lean_object* v_a_3813_, lean_object* v_a_3814_, lean_object* v_a_3815_, lean_object* v_a_3816_){
_start:
{
lean_object* v_res_3817_; 
v_res_3817_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg(v_e_3808_, v_a_3809_, v_a_3810_, v_a_3811_, v_a_3812_, v_a_3813_, v_a_3814_, v_a_3815_);
lean_dec(v_a_3815_);
lean_dec_ref(v_a_3814_);
lean_dec(v_a_3813_);
lean_dec_ref(v_a_3812_);
lean_dec(v_a_3811_);
lean_dec_ref(v_a_3810_);
lean_dec(v_a_3809_);
return v_res_3817_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visit___boxed(lean_object* v_e_3818_, lean_object* v_a_3819_, lean_object* v_a_3820_, lean_object* v_a_3821_, lean_object* v_a_3822_, lean_object* v_a_3823_, lean_object* v_a_3824_, lean_object* v_a_3825_, lean_object* v_a_3826_, lean_object* v_a_3827_){
_start:
{
lean_object* v_res_3828_; 
v_res_3828_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visit(v_e_3818_, v_a_3819_, v_a_3820_, v_a_3821_, v_a_3822_, v_a_3823_, v_a_3824_, v_a_3825_, v_a_3826_);
lean_dec(v_a_3826_);
lean_dec_ref(v_a_3825_);
lean_dec(v_a_3824_);
lean_dec_ref(v_a_3823_);
lean_dec(v_a_3822_);
lean_dec_ref(v_a_3821_);
lean_dec(v_a_3820_);
lean_dec_ref(v_a_3819_);
return v_res_3828_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore___boxed(lean_object* v_e_3829_, lean_object* v_a_3830_, lean_object* v_a_3831_, lean_object* v_a_3832_, lean_object* v_a_3833_, lean_object* v_a_3834_, lean_object* v_a_3835_, lean_object* v_a_3836_, lean_object* v_a_3837_, lean_object* v_a_3838_){
_start:
{
lean_object* v_res_3839_; 
v_res_3839_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore(v_e_3829_, v_a_3830_, v_a_3831_, v_a_3832_, v_a_3833_, v_a_3834_, v_a_3835_, v_a_3836_, v_a_3837_);
lean_dec(v_a_3837_);
lean_dec_ref(v_a_3836_);
lean_dec(v_a_3835_);
lean_dec_ref(v_a_3834_);
lean_dec(v_a_3833_);
lean_dec_ref(v_a_3832_);
lean_dec(v_a_3831_);
lean_dec_ref(v_a_3830_);
return v_res_3839_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__1(lean_object* v_f_3840_, lean_object* v_a_3841_, lean_object* v___y_3842_, lean_object* v___y_3843_, lean_object* v___y_3844_, lean_object* v___y_3845_, lean_object* v___y_3846_, lean_object* v___y_3847_, lean_object* v___y_3848_, lean_object* v___y_3849_){
_start:
{
lean_object* v___x_3851_; 
v___x_3851_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__1___redArg(v_f_3840_, v_a_3841_, v___y_3844_, v___y_3845_, v___y_3846_, v___y_3847_, v___y_3848_, v___y_3849_);
return v___x_3851_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__1___boxed(lean_object* v_f_3852_, lean_object* v_a_3853_, lean_object* v___y_3854_, lean_object* v___y_3855_, lean_object* v___y_3856_, lean_object* v___y_3857_, lean_object* v___y_3858_, lean_object* v___y_3859_, lean_object* v___y_3860_, lean_object* v___y_3861_, lean_object* v___y_3862_){
_start:
{
lean_object* v_res_3863_; 
v_res_3863_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__1(v_f_3852_, v_a_3853_, v___y_3854_, v___y_3855_, v___y_3856_, v___y_3857_, v___y_3858_, v___y_3859_, v___y_3860_, v___y_3861_);
lean_dec(v___y_3861_);
lean_dec_ref(v___y_3860_);
lean_dec(v___y_3859_);
lean_dec_ref(v___y_3858_);
lean_dec(v___y_3857_);
lean_dec_ref(v___y_3856_);
lean_dec(v___y_3855_);
lean_dec_ref(v___y_3854_);
return v_res_3863_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__2(lean_object* v_d_3864_, lean_object* v_e_3865_, lean_object* v___y_3866_, lean_object* v___y_3867_, lean_object* v___y_3868_, lean_object* v___y_3869_, lean_object* v___y_3870_, lean_object* v___y_3871_, lean_object* v___y_3872_, lean_object* v___y_3873_){
_start:
{
lean_object* v___x_3875_; 
v___x_3875_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__2___redArg(v_d_3864_, v_e_3865_, v___y_3868_, v___y_3869_, v___y_3870_, v___y_3871_, v___y_3872_, v___y_3873_);
return v___x_3875_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__2___boxed(lean_object* v_d_3876_, lean_object* v_e_3877_, lean_object* v___y_3878_, lean_object* v___y_3879_, lean_object* v___y_3880_, lean_object* v___y_3881_, lean_object* v___y_3882_, lean_object* v___y_3883_, lean_object* v___y_3884_, lean_object* v___y_3885_, lean_object* v___y_3886_){
_start:
{
lean_object* v_res_3887_; 
v_res_3887_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__2(v_d_3876_, v_e_3877_, v___y_3878_, v___y_3879_, v___y_3880_, v___y_3881_, v___y_3882_, v___y_3883_, v___y_3884_, v___y_3885_);
lean_dec(v___y_3885_);
lean_dec_ref(v___y_3884_);
lean_dec(v___y_3883_);
lean_dec_ref(v___y_3882_);
lean_dec(v___y_3881_);
lean_dec_ref(v___y_3880_);
lean_dec(v___y_3879_);
lean_dec_ref(v___y_3878_);
return v_res_3887_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__3(lean_object* v_structName_3888_, lean_object* v_idx_3889_, lean_object* v_struct_3890_, lean_object* v___y_3891_, lean_object* v___y_3892_, lean_object* v___y_3893_, lean_object* v___y_3894_, lean_object* v___y_3895_, lean_object* v___y_3896_, lean_object* v___y_3897_, lean_object* v___y_3898_){
_start:
{
lean_object* v___x_3900_; 
v___x_3900_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__3___redArg(v_structName_3888_, v_idx_3889_, v_struct_3890_, v___y_3893_, v___y_3894_, v___y_3895_, v___y_3896_, v___y_3897_, v___y_3898_);
return v___x_3900_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__3___boxed(lean_object* v_structName_3901_, lean_object* v_idx_3902_, lean_object* v_struct_3903_, lean_object* v___y_3904_, lean_object* v___y_3905_, lean_object* v___y_3906_, lean_object* v___y_3907_, lean_object* v___y_3908_, lean_object* v___y_3909_, lean_object* v___y_3910_, lean_object* v___y_3911_, lean_object* v___y_3912_){
_start:
{
lean_object* v_res_3913_; 
v_res_3913_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__3(v_structName_3901_, v_idx_3902_, v_struct_3903_, v___y_3904_, v___y_3905_, v___y_3906_, v___y_3907_, v___y_3908_, v___y_3909_, v___y_3910_, v___y_3911_);
lean_dec(v___y_3911_);
lean_dec_ref(v___y_3910_);
lean_dec(v___y_3909_);
lean_dec_ref(v___y_3908_);
lean_dec(v___y_3907_);
lean_dec_ref(v___y_3906_);
lean_dec(v___y_3905_);
lean_dec_ref(v___y_3904_);
return v_res_3913_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__4(lean_object* v_x_3914_, uint8_t v_bi_3915_, lean_object* v_t_3916_, lean_object* v_b_3917_, lean_object* v___y_3918_, lean_object* v___y_3919_, lean_object* v___y_3920_, lean_object* v___y_3921_, lean_object* v___y_3922_, lean_object* v___y_3923_, lean_object* v___y_3924_, lean_object* v___y_3925_){
_start:
{
lean_object* v___x_3927_; 
v___x_3927_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__4___redArg(v_x_3914_, v_bi_3915_, v_t_3916_, v_b_3917_, v___y_3920_, v___y_3921_, v___y_3922_, v___y_3923_, v___y_3924_, v___y_3925_);
return v___x_3927_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__4___boxed(lean_object* v_x_3928_, lean_object* v_bi_3929_, lean_object* v_t_3930_, lean_object* v_b_3931_, lean_object* v___y_3932_, lean_object* v___y_3933_, lean_object* v___y_3934_, lean_object* v___y_3935_, lean_object* v___y_3936_, lean_object* v___y_3937_, lean_object* v___y_3938_, lean_object* v___y_3939_, lean_object* v___y_3940_){
_start:
{
uint8_t v_bi_boxed_3941_; lean_object* v_res_3942_; 
v_bi_boxed_3941_ = lean_unbox(v_bi_3929_);
v_res_3942_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__4(v_x_3928_, v_bi_boxed_3941_, v_t_3930_, v_b_3931_, v___y_3932_, v___y_3933_, v___y_3934_, v___y_3935_, v___y_3936_, v___y_3937_, v___y_3938_, v___y_3939_);
lean_dec(v___y_3939_);
lean_dec_ref(v___y_3938_);
lean_dec(v___y_3937_);
lean_dec_ref(v___y_3936_);
lean_dec(v___y_3935_);
lean_dec_ref(v___y_3934_);
lean_dec(v___y_3933_);
lean_dec_ref(v___y_3932_);
return v_res_3942_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__5(lean_object* v_x_3943_, lean_object* v_t_3944_, lean_object* v_v_3945_, lean_object* v_b_3946_, uint8_t v_nondep_3947_, lean_object* v___y_3948_, lean_object* v___y_3949_, lean_object* v___y_3950_, lean_object* v___y_3951_, lean_object* v___y_3952_, lean_object* v___y_3953_, lean_object* v___y_3954_, lean_object* v___y_3955_){
_start:
{
lean_object* v___x_3957_; 
v___x_3957_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__5___redArg(v_x_3943_, v_t_3944_, v_v_3945_, v_b_3946_, v_nondep_3947_, v___y_3950_, v___y_3951_, v___y_3952_, v___y_3953_, v___y_3954_, v___y_3955_);
return v___x_3957_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__5___boxed(lean_object* v_x_3958_, lean_object* v_t_3959_, lean_object* v_v_3960_, lean_object* v_b_3961_, lean_object* v_nondep_3962_, lean_object* v___y_3963_, lean_object* v___y_3964_, lean_object* v___y_3965_, lean_object* v___y_3966_, lean_object* v___y_3967_, lean_object* v___y_3968_, lean_object* v___y_3969_, lean_object* v___y_3970_, lean_object* v___y_3971_){
_start:
{
uint8_t v_nondep_boxed_3972_; lean_object* v_res_3973_; 
v_nondep_boxed_3972_ = lean_unbox(v_nondep_3962_);
v_res_3973_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__5(v_x_3958_, v_t_3959_, v_v_3960_, v_b_3961_, v_nondep_boxed_3972_, v___y_3963_, v___y_3964_, v___y_3965_, v___y_3966_, v___y_3967_, v___y_3968_, v___y_3969_, v___y_3970_);
lean_dec(v___y_3970_);
lean_dec_ref(v___y_3969_);
lean_dec(v___y_3968_);
lean_dec_ref(v___y_3967_);
lean_dec(v___y_3966_);
lean_dec_ref(v___y_3965_);
lean_dec(v___y_3964_);
lean_dec_ref(v___y_3963_);
return v_res_3973_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitForall_spec__8(lean_object* v_x_3974_, uint8_t v_bi_3975_, lean_object* v_t_3976_, lean_object* v_b_3977_, lean_object* v___y_3978_, lean_object* v___y_3979_, lean_object* v___y_3980_, lean_object* v___y_3981_, lean_object* v___y_3982_, lean_object* v___y_3983_, lean_object* v___y_3984_, lean_object* v___y_3985_){
_start:
{
lean_object* v___x_3987_; 
v___x_3987_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitForall_spec__8___redArg(v_x_3974_, v_bi_3975_, v_t_3976_, v_b_3977_, v___y_3980_, v___y_3981_, v___y_3982_, v___y_3983_, v___y_3984_, v___y_3985_);
return v___x_3987_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitForall_spec__8___boxed(lean_object* v_x_3988_, lean_object* v_bi_3989_, lean_object* v_t_3990_, lean_object* v_b_3991_, lean_object* v___y_3992_, lean_object* v___y_3993_, lean_object* v___y_3994_, lean_object* v___y_3995_, lean_object* v___y_3996_, lean_object* v___y_3997_, lean_object* v___y_3998_, lean_object* v___y_3999_, lean_object* v___y_4000_){
_start:
{
uint8_t v_bi_boxed_4001_; lean_object* v_res_4002_; 
v_bi_boxed_4001_ = lean_unbox(v_bi_3989_);
v_res_4002_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitForall_spec__8(v_x_3988_, v_bi_boxed_4001_, v_t_3990_, v_b_3991_, v___y_3992_, v___y_3993_, v___y_3994_, v___y_3995_, v___y_3996_, v___y_3997_, v___y_3998_, v___y_3999_);
lean_dec(v___y_3999_);
lean_dec_ref(v___y_3998_);
lean_dec(v___y_3997_);
lean_dec_ref(v___y_3996_);
lean_dec(v___y_3995_);
lean_dec_ref(v___y_3994_);
lean_dec(v___y_3993_);
lean_dec_ref(v___y_3992_);
return v_res_4002_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed(lean_object* v_e_4003_, lean_object* v_a_4004_, lean_object* v_a_4005_, lean_object* v_a_4006_, lean_object* v_a_4007_, lean_object* v_a_4008_, lean_object* v_a_4009_, lean_object* v_a_4010_, lean_object* v_a_4011_){
_start:
{
lean_object* v___x_4013_; 
v___x_4013_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg(v_e_4003_, v_a_4005_, v_a_4006_, v_a_4007_, v_a_4008_, v_a_4009_, v_a_4010_, v_a_4011_);
return v___x_4013_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___boxed(lean_object* v_e_4014_, lean_object* v_a_4015_, lean_object* v_a_4016_, lean_object* v_a_4017_, lean_object* v_a_4018_, lean_object* v_a_4019_, lean_object* v_a_4020_, lean_object* v_a_4021_, lean_object* v_a_4022_, lean_object* v_a_4023_){
_start:
{
lean_object* v_res_4024_; 
v_res_4024_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed(v_e_4014_, v_a_4015_, v_a_4016_, v_a_4017_, v_a_4018_, v_a_4019_, v_a_4020_, v_a_4021_, v_a_4022_);
lean_dec(v_a_4022_);
lean_dec_ref(v_a_4021_);
lean_dec(v_a_4020_);
lean_dec_ref(v_a_4019_);
lean_dec(v_a_4018_);
lean_dec_ref(v_a_4017_);
lean_dec(v_a_4016_);
lean_dec_ref(v_a_4015_);
return v_res_4024_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__6(lean_object* v_00_u03b2_4025_, lean_object* v_k_4026_, lean_object* v_t_4027_){
_start:
{
uint8_t v___x_4028_; 
v___x_4028_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__6___redArg(v_k_4026_, v_t_4027_);
return v___x_4028_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__6___boxed(lean_object* v_00_u03b2_4029_, lean_object* v_k_4030_, lean_object* v_t_4031_){
_start:
{
uint8_t v_res_4032_; lean_object* v_r_4033_; 
v_res_4032_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitCore_spec__6(v_00_u03b2_4029_, v_k_4030_, v_t_4031_);
lean_dec(v_t_4031_);
lean_dec(v_k_4030_);
v_r_4033_ = lean_box(v_res_4032_);
return v_r_4033_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_Sym_letToHave_spec__0___redArg___lam__0(lean_object* v_x_4034_, lean_object* v___y_4035_, lean_object* v___y_4036_, lean_object* v___y_4037_, lean_object* v___y_4038_, lean_object* v___y_4039_, lean_object* v___y_4040_){
_start:
{
lean_object* v___x_4042_; 
lean_inc(v___y_4036_);
lean_inc_ref(v___y_4035_);
v___x_4042_ = lean_apply_7(v_x_4034_, v___y_4035_, v___y_4036_, v___y_4037_, v___y_4038_, v___y_4039_, v___y_4040_, lean_box(0));
return v___x_4042_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_Sym_letToHave_spec__0___redArg___lam__0___boxed(lean_object* v_x_4043_, lean_object* v___y_4044_, lean_object* v___y_4045_, lean_object* v___y_4046_, lean_object* v___y_4047_, lean_object* v___y_4048_, lean_object* v___y_4049_, lean_object* v___y_4050_){
_start:
{
lean_object* v_res_4051_; 
v_res_4051_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_Sym_letToHave_spec__0___redArg___lam__0(v_x_4043_, v___y_4044_, v___y_4045_, v___y_4046_, v___y_4047_, v___y_4048_, v___y_4049_);
lean_dec(v___y_4045_);
lean_dec_ref(v___y_4044_);
return v_res_4051_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_Sym_letToHave_spec__0___redArg(lean_object* v_lctx_4052_, lean_object* v_localInsts_4053_, lean_object* v_x_4054_, lean_object* v___y_4055_, lean_object* v___y_4056_, lean_object* v___y_4057_, lean_object* v___y_4058_, lean_object* v___y_4059_, lean_object* v___y_4060_){
_start:
{
lean_object* v___f_4062_; lean_object* v___x_4063_; 
lean_inc(v___y_4056_);
lean_inc_ref(v___y_4055_);
v___f_4062_ = lean_alloc_closure((void*)(l_Lean_Meta_withLCtx___at___00Lean_Meta_Sym_letToHave_spec__0___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_4062_, 0, v_x_4054_);
lean_closure_set(v___f_4062_, 1, v___y_4055_);
lean_closure_set(v___f_4062_, 2, v___y_4056_);
v___x_4063_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_4052_, v_localInsts_4053_, v___f_4062_, v___y_4057_, v___y_4058_, v___y_4059_, v___y_4060_);
if (lean_obj_tag(v___x_4063_) == 0)
{
return v___x_4063_;
}
else
{
lean_object* v_a_4064_; lean_object* v___x_4066_; uint8_t v_isShared_4067_; uint8_t v_isSharedCheck_4071_; 
v_a_4064_ = lean_ctor_get(v___x_4063_, 0);
v_isSharedCheck_4071_ = !lean_is_exclusive(v___x_4063_);
if (v_isSharedCheck_4071_ == 0)
{
v___x_4066_ = v___x_4063_;
v_isShared_4067_ = v_isSharedCheck_4071_;
goto v_resetjp_4065_;
}
else
{
lean_inc(v_a_4064_);
lean_dec(v___x_4063_);
v___x_4066_ = lean_box(0);
v_isShared_4067_ = v_isSharedCheck_4071_;
goto v_resetjp_4065_;
}
v_resetjp_4065_:
{
lean_object* v___x_4069_; 
if (v_isShared_4067_ == 0)
{
v___x_4069_ = v___x_4066_;
goto v_reusejp_4068_;
}
else
{
lean_object* v_reuseFailAlloc_4070_; 
v_reuseFailAlloc_4070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4070_, 0, v_a_4064_);
v___x_4069_ = v_reuseFailAlloc_4070_;
goto v_reusejp_4068_;
}
v_reusejp_4068_:
{
return v___x_4069_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_Sym_letToHave_spec__0___redArg___boxed(lean_object* v_lctx_4072_, lean_object* v_localInsts_4073_, lean_object* v_x_4074_, lean_object* v___y_4075_, lean_object* v___y_4076_, lean_object* v___y_4077_, lean_object* v___y_4078_, lean_object* v___y_4079_, lean_object* v___y_4080_, lean_object* v___y_4081_){
_start:
{
lean_object* v_res_4082_; 
v_res_4082_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_Sym_letToHave_spec__0___redArg(v_lctx_4072_, v_localInsts_4073_, v_x_4074_, v___y_4075_, v___y_4076_, v___y_4077_, v___y_4078_, v___y_4079_, v___y_4080_);
lean_dec(v___y_4080_);
lean_dec_ref(v___y_4079_);
lean_dec(v___y_4078_);
lean_dec_ref(v___y_4077_);
lean_dec(v___y_4076_);
lean_dec_ref(v___y_4075_);
return v_res_4082_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_Sym_letToHave_spec__0(lean_object* v_00_u03b1_4083_, lean_object* v_lctx_4084_, lean_object* v_localInsts_4085_, lean_object* v_x_4086_, lean_object* v___y_4087_, lean_object* v___y_4088_, lean_object* v___y_4089_, lean_object* v___y_4090_, lean_object* v___y_4091_, lean_object* v___y_4092_){
_start:
{
lean_object* v___x_4094_; 
v___x_4094_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_Sym_letToHave_spec__0___redArg(v_lctx_4084_, v_localInsts_4085_, v_x_4086_, v___y_4087_, v___y_4088_, v___y_4089_, v___y_4090_, v___y_4091_, v___y_4092_);
return v___x_4094_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_Sym_letToHave_spec__0___boxed(lean_object* v_00_u03b1_4095_, lean_object* v_lctx_4096_, lean_object* v_localInsts_4097_, lean_object* v_x_4098_, lean_object* v___y_4099_, lean_object* v___y_4100_, lean_object* v___y_4101_, lean_object* v___y_4102_, lean_object* v___y_4103_, lean_object* v___y_4104_, lean_object* v___y_4105_){
_start:
{
lean_object* v_res_4106_; 
v_res_4106_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_Sym_letToHave_spec__0(v_00_u03b1_4095_, v_lctx_4096_, v_localInsts_4097_, v_x_4098_, v___y_4099_, v___y_4100_, v___y_4101_, v___y_4102_, v___y_4103_, v___y_4104_);
lean_dec(v___y_4104_);
lean_dec_ref(v___y_4103_);
lean_dec(v___y_4102_);
lean_dec_ref(v___y_4101_);
lean_dec(v___y_4100_);
lean_dec_ref(v___y_4099_);
return v_res_4106_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_letToHave_spec__1___redArg___lam__0(lean_object* v_k_4107_, lean_object* v___y_4108_, lean_object* v___y_4109_, lean_object* v___y_4110_, lean_object* v___y_4111_, lean_object* v___y_4112_, lean_object* v___y_4113_){
_start:
{
lean_object* v___x_4115_; 
lean_inc(v___y_4109_);
lean_inc_ref(v___y_4108_);
v___x_4115_ = lean_apply_7(v_k_4107_, v___y_4108_, v___y_4109_, v___y_4110_, v___y_4111_, v___y_4112_, v___y_4113_, lean_box(0));
return v___x_4115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_letToHave_spec__1___redArg___lam__0___boxed(lean_object* v_k_4116_, lean_object* v___y_4117_, lean_object* v___y_4118_, lean_object* v___y_4119_, lean_object* v___y_4120_, lean_object* v___y_4121_, lean_object* v___y_4122_, lean_object* v___y_4123_){
_start:
{
lean_object* v_res_4124_; 
v_res_4124_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_letToHave_spec__1___redArg___lam__0(v_k_4116_, v___y_4117_, v___y_4118_, v___y_4119_, v___y_4120_, v___y_4121_, v___y_4122_);
lean_dec(v___y_4118_);
lean_dec_ref(v___y_4117_);
return v_res_4124_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_letToHave_spec__1___redArg(lean_object* v_k_4125_, uint8_t v_allowLevelAssignments_4126_, lean_object* v___y_4127_, lean_object* v___y_4128_, lean_object* v___y_4129_, lean_object* v___y_4130_, lean_object* v___y_4131_, lean_object* v___y_4132_){
_start:
{
lean_object* v___f_4134_; lean_object* v___x_4135_; 
lean_inc(v___y_4128_);
lean_inc_ref(v___y_4127_);
v___f_4134_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_letToHave_spec__1___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_4134_, 0, v_k_4125_);
lean_closure_set(v___f_4134_, 1, v___y_4127_);
lean_closure_set(v___f_4134_, 2, v___y_4128_);
v___x_4135_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_4126_, v___f_4134_, v___y_4129_, v___y_4130_, v___y_4131_, v___y_4132_);
if (lean_obj_tag(v___x_4135_) == 0)
{
return v___x_4135_;
}
else
{
lean_object* v_a_4136_; lean_object* v___x_4138_; uint8_t v_isShared_4139_; uint8_t v_isSharedCheck_4143_; 
v_a_4136_ = lean_ctor_get(v___x_4135_, 0);
v_isSharedCheck_4143_ = !lean_is_exclusive(v___x_4135_);
if (v_isSharedCheck_4143_ == 0)
{
v___x_4138_ = v___x_4135_;
v_isShared_4139_ = v_isSharedCheck_4143_;
goto v_resetjp_4137_;
}
else
{
lean_inc(v_a_4136_);
lean_dec(v___x_4135_);
v___x_4138_ = lean_box(0);
v_isShared_4139_ = v_isSharedCheck_4143_;
goto v_resetjp_4137_;
}
v_resetjp_4137_:
{
lean_object* v___x_4141_; 
if (v_isShared_4139_ == 0)
{
v___x_4141_ = v___x_4138_;
goto v_reusejp_4140_;
}
else
{
lean_object* v_reuseFailAlloc_4142_; 
v_reuseFailAlloc_4142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4142_, 0, v_a_4136_);
v___x_4141_ = v_reuseFailAlloc_4142_;
goto v_reusejp_4140_;
}
v_reusejp_4140_:
{
return v___x_4141_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_letToHave_spec__1___redArg___boxed(lean_object* v_k_4144_, lean_object* v_allowLevelAssignments_4145_, lean_object* v___y_4146_, lean_object* v___y_4147_, lean_object* v___y_4148_, lean_object* v___y_4149_, lean_object* v___y_4150_, lean_object* v___y_4151_, lean_object* v___y_4152_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_4153_; lean_object* v_res_4154_; 
v_allowLevelAssignments_boxed_4153_ = lean_unbox(v_allowLevelAssignments_4145_);
v_res_4154_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_letToHave_spec__1___redArg(v_k_4144_, v_allowLevelAssignments_boxed_4153_, v___y_4146_, v___y_4147_, v___y_4148_, v___y_4149_, v___y_4150_, v___y_4151_);
lean_dec(v___y_4151_);
lean_dec_ref(v___y_4150_);
lean_dec(v___y_4149_);
lean_dec_ref(v___y_4148_);
lean_dec(v___y_4147_);
lean_dec_ref(v___y_4146_);
return v_res_4154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_letToHave_spec__1(lean_object* v_00_u03b1_4155_, lean_object* v_k_4156_, uint8_t v_allowLevelAssignments_4157_, lean_object* v___y_4158_, lean_object* v___y_4159_, lean_object* v___y_4160_, lean_object* v___y_4161_, lean_object* v___y_4162_, lean_object* v___y_4163_){
_start:
{
lean_object* v___x_4165_; 
v___x_4165_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_letToHave_spec__1___redArg(v_k_4156_, v_allowLevelAssignments_4157_, v___y_4158_, v___y_4159_, v___y_4160_, v___y_4161_, v___y_4162_, v___y_4163_);
return v___x_4165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_letToHave_spec__1___boxed(lean_object* v_00_u03b1_4166_, lean_object* v_k_4167_, lean_object* v_allowLevelAssignments_4168_, lean_object* v___y_4169_, lean_object* v___y_4170_, lean_object* v___y_4171_, lean_object* v___y_4172_, lean_object* v___y_4173_, lean_object* v___y_4174_, lean_object* v___y_4175_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_4176_; lean_object* v_res_4177_; 
v_allowLevelAssignments_boxed_4176_ = lean_unbox(v_allowLevelAssignments_4168_);
v_res_4177_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_letToHave_spec__1(v_00_u03b1_4166_, v_k_4167_, v_allowLevelAssignments_boxed_4176_, v___y_4169_, v___y_4170_, v___y_4171_, v___y_4172_, v___y_4173_, v___y_4174_);
lean_dec(v___y_4174_);
lean_dec_ref(v___y_4173_);
lean_dec(v___y_4172_);
lean_dec_ref(v___y_4171_);
lean_dec(v___y_4170_);
lean_dec_ref(v___y_4169_);
return v_res_4177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_letToHave___lam__0(lean_object* v_cfg_4178_){
_start:
{
uint8_t v_foApprox_4179_; uint8_t v_ctxApprox_4180_; uint8_t v_quasiPatternApprox_4181_; uint8_t v_constApprox_4182_; uint8_t v_isDefEqStuckEx_4183_; uint8_t v_unificationHints_4184_; uint8_t v_proofIrrelevance_4185_; uint8_t v_assignSyntheticOpaque_4186_; uint8_t v_offsetCnstrs_4187_; uint8_t v_transparency_4188_; uint8_t v_univApprox_4189_; uint8_t v_zetaUnused_4190_; uint8_t v_canUnfoldPredicateConfig_4191_; lean_object* v___x_4193_; uint8_t v_isShared_4194_; uint8_t v_isSharedCheck_4201_; 
v_foApprox_4179_ = lean_ctor_get_uint8(v_cfg_4178_, 0);
v_ctxApprox_4180_ = lean_ctor_get_uint8(v_cfg_4178_, 1);
v_quasiPatternApprox_4181_ = lean_ctor_get_uint8(v_cfg_4178_, 2);
v_constApprox_4182_ = lean_ctor_get_uint8(v_cfg_4178_, 3);
v_isDefEqStuckEx_4183_ = lean_ctor_get_uint8(v_cfg_4178_, 4);
v_unificationHints_4184_ = lean_ctor_get_uint8(v_cfg_4178_, 5);
v_proofIrrelevance_4185_ = lean_ctor_get_uint8(v_cfg_4178_, 6);
v_assignSyntheticOpaque_4186_ = lean_ctor_get_uint8(v_cfg_4178_, 7);
v_offsetCnstrs_4187_ = lean_ctor_get_uint8(v_cfg_4178_, 8);
v_transparency_4188_ = lean_ctor_get_uint8(v_cfg_4178_, 9);
v_univApprox_4189_ = lean_ctor_get_uint8(v_cfg_4178_, 11);
v_zetaUnused_4190_ = lean_ctor_get_uint8(v_cfg_4178_, 17);
v_canUnfoldPredicateConfig_4191_ = lean_ctor_get_uint8(v_cfg_4178_, 19);
v_isSharedCheck_4201_ = !lean_is_exclusive(v_cfg_4178_);
if (v_isSharedCheck_4201_ == 0)
{
v___x_4193_ = v_cfg_4178_;
v_isShared_4194_ = v_isSharedCheck_4201_;
goto v_resetjp_4192_;
}
else
{
lean_dec(v_cfg_4178_);
v___x_4193_ = lean_box(0);
v_isShared_4194_ = v_isSharedCheck_4201_;
goto v_resetjp_4192_;
}
v_resetjp_4192_:
{
uint8_t v___x_4195_; uint8_t v___x_4196_; uint8_t v___x_4197_; lean_object* v___x_4199_; 
v___x_4195_ = 0;
v___x_4196_ = 1;
v___x_4197_ = 2;
if (v_isShared_4194_ == 0)
{
v___x_4199_ = v___x_4193_;
goto v_reusejp_4198_;
}
else
{
lean_object* v_reuseFailAlloc_4200_; 
v_reuseFailAlloc_4200_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v_reuseFailAlloc_4200_, 0, v_foApprox_4179_);
lean_ctor_set_uint8(v_reuseFailAlloc_4200_, 1, v_ctxApprox_4180_);
lean_ctor_set_uint8(v_reuseFailAlloc_4200_, 2, v_quasiPatternApprox_4181_);
lean_ctor_set_uint8(v_reuseFailAlloc_4200_, 3, v_constApprox_4182_);
lean_ctor_set_uint8(v_reuseFailAlloc_4200_, 4, v_isDefEqStuckEx_4183_);
lean_ctor_set_uint8(v_reuseFailAlloc_4200_, 5, v_unificationHints_4184_);
lean_ctor_set_uint8(v_reuseFailAlloc_4200_, 6, v_proofIrrelevance_4185_);
lean_ctor_set_uint8(v_reuseFailAlloc_4200_, 7, v_assignSyntheticOpaque_4186_);
lean_ctor_set_uint8(v_reuseFailAlloc_4200_, 8, v_offsetCnstrs_4187_);
lean_ctor_set_uint8(v_reuseFailAlloc_4200_, 9, v_transparency_4188_);
lean_ctor_set_uint8(v_reuseFailAlloc_4200_, 11, v_univApprox_4189_);
lean_ctor_set_uint8(v_reuseFailAlloc_4200_, 17, v_zetaUnused_4190_);
lean_ctor_set_uint8(v_reuseFailAlloc_4200_, 19, v_canUnfoldPredicateConfig_4191_);
v___x_4199_ = v_reuseFailAlloc_4200_;
goto v_reusejp_4198_;
}
v_reusejp_4198_:
{
lean_ctor_set_uint8(v___x_4199_, 10, v___x_4195_);
lean_ctor_set_uint8(v___x_4199_, 12, v___x_4196_);
lean_ctor_set_uint8(v___x_4199_, 13, v___x_4196_);
lean_ctor_set_uint8(v___x_4199_, 14, v___x_4197_);
lean_ctor_set_uint8(v___x_4199_, 15, v___x_4196_);
lean_ctor_set_uint8(v___x_4199_, 16, v___x_4196_);
lean_ctor_set_uint8(v___x_4199_, 18, v___x_4196_);
return v___x_4199_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_letToHave___lam__1(lean_object* v___x_4202_, lean_object* v_e_4203_, lean_object* v___x_4204_, lean_object* v___y_4205_, lean_object* v___y_4206_, lean_object* v___y_4207_, lean_object* v___y_4208_, lean_object* v___y_4209_, lean_object* v___y_4210_){
_start:
{
lean_object* v___x_4212_; lean_object* v_a_4214_; lean_object* v___x_4217_; 
v___x_4212_ = lean_st_mk_ref(v___x_4202_);
lean_inc_ref(v_e_4203_);
v___x_4217_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_hasDepLet(v_e_4203_, v___x_4204_, v___x_4212_, v___y_4205_, v___y_4206_, v___y_4207_, v___y_4208_, v___y_4209_, v___y_4210_);
if (lean_obj_tag(v___x_4217_) == 0)
{
lean_object* v_a_4218_; uint8_t v___x_4219_; 
v_a_4218_ = lean_ctor_get(v___x_4217_, 0);
lean_inc(v_a_4218_);
lean_dec_ref_known(v___x_4217_, 1);
v___x_4219_ = lean_unbox(v_a_4218_);
lean_dec(v_a_4218_);
if (v___x_4219_ == 0)
{
v_a_4214_ = v_e_4203_;
goto v___jp_4213_;
}
else
{
lean_object* v___x_4220_; 
v___x_4220_ = l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visit(v_e_4203_, v___x_4204_, v___x_4212_, v___y_4205_, v___y_4206_, v___y_4207_, v___y_4208_, v___y_4209_, v___y_4210_);
if (lean_obj_tag(v___x_4220_) == 0)
{
lean_object* v_a_4221_; 
v_a_4221_ = lean_ctor_get(v___x_4220_, 0);
lean_inc(v_a_4221_);
lean_dec_ref_known(v___x_4220_, 1);
v_a_4214_ = v_a_4221_;
goto v___jp_4213_;
}
else
{
lean_dec(v___x_4212_);
return v___x_4220_;
}
}
}
else
{
lean_object* v_a_4222_; lean_object* v___x_4224_; uint8_t v_isShared_4225_; uint8_t v_isSharedCheck_4229_; 
lean_dec(v___x_4212_);
lean_dec_ref(v_e_4203_);
v_a_4222_ = lean_ctor_get(v___x_4217_, 0);
v_isSharedCheck_4229_ = !lean_is_exclusive(v___x_4217_);
if (v_isSharedCheck_4229_ == 0)
{
v___x_4224_ = v___x_4217_;
v_isShared_4225_ = v_isSharedCheck_4229_;
goto v_resetjp_4223_;
}
else
{
lean_inc(v_a_4222_);
lean_dec(v___x_4217_);
v___x_4224_ = lean_box(0);
v_isShared_4225_ = v_isSharedCheck_4229_;
goto v_resetjp_4223_;
}
v_resetjp_4223_:
{
lean_object* v___x_4227_; 
if (v_isShared_4225_ == 0)
{
v___x_4227_ = v___x_4224_;
goto v_reusejp_4226_;
}
else
{
lean_object* v_reuseFailAlloc_4228_; 
v_reuseFailAlloc_4228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4228_, 0, v_a_4222_);
v___x_4227_ = v_reuseFailAlloc_4228_;
goto v_reusejp_4226_;
}
v_reusejp_4226_:
{
return v___x_4227_;
}
}
}
v___jp_4213_:
{
lean_object* v___x_4215_; lean_object* v___x_4216_; 
v___x_4215_ = lean_st_ref_get(v___x_4212_);
lean_dec(v___x_4212_);
lean_dec(v___x_4215_);
v___x_4216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4216_, 0, v_a_4214_);
return v___x_4216_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_letToHave___lam__1___boxed(lean_object* v___x_4230_, lean_object* v_e_4231_, lean_object* v___x_4232_, lean_object* v___y_4233_, lean_object* v___y_4234_, lean_object* v___y_4235_, lean_object* v___y_4236_, lean_object* v___y_4237_, lean_object* v___y_4238_, lean_object* v___y_4239_){
_start:
{
lean_object* v_res_4240_; 
v_res_4240_ = l_Lean_Meta_Sym_letToHave___lam__1(v___x_4230_, v_e_4231_, v___x_4232_, v___y_4233_, v___y_4234_, v___y_4235_, v___y_4236_, v___y_4237_, v___y_4238_);
lean_dec(v___y_4238_);
lean_dec_ref(v___y_4237_);
lean_dec(v___y_4236_);
lean_dec_ref(v___y_4235_);
lean_dec(v___y_4234_);
lean_dec_ref(v___y_4233_);
lean_dec_ref(v___x_4232_);
return v_res_4240_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_letToHave___lam__2___closed__0(void){
_start:
{
lean_object* v___x_4241_; lean_object* v___x_4242_; lean_object* v___x_4243_; 
v___x_4241_ = lean_unsigned_to_nat(0u);
v___x_4242_ = lean_obj_once(&l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withNewScope___redArg___closed__1, &l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withNewScope___redArg___closed__1_once, _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withNewScope___redArg___closed__1);
v___x_4243_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4243_, 0, v___x_4242_);
lean_ctor_set(v___x_4243_, 1, v___x_4242_);
lean_ctor_set(v___x_4243_, 2, v___x_4242_);
lean_ctor_set(v___x_4243_, 3, v___x_4242_);
lean_ctor_set(v___x_4243_, 4, v___x_4242_);
lean_ctor_set(v___x_4243_, 5, v___x_4241_);
return v___x_4243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_letToHave___lam__2(lean_object* v_e_4244_, lean_object* v_____do__lift_4245_, lean_object* v___y_4246_, lean_object* v___y_4247_, lean_object* v___y_4248_, lean_object* v___y_4249_, lean_object* v___y_4250_, lean_object* v___y_4251_){
_start:
{
lean_object* v___x_4253_; lean_object* v___x_4254_; lean_object* v___x_4255_; lean_object* v___f_4256_; lean_object* v___x_4257_; 
v___x_4253_ = ((lean_object*)(l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_withBinder___redArg___closed__0));
v___x_4254_ = lean_obj_once(&l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg___closed__2, &l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg___closed__2_once, _init_l___private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_visitClosed___redArg___closed__2);
v___x_4255_ = lean_obj_once(&l_Lean_Meta_Sym_letToHave___lam__2___closed__0, &l_Lean_Meta_Sym_letToHave___lam__2___closed__0_once, _init_l_Lean_Meta_Sym_letToHave___lam__2___closed__0);
v___f_4256_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_letToHave___lam__1___boxed), 10, 3);
lean_closure_set(v___f_4256_, 0, v___x_4255_);
lean_closure_set(v___f_4256_, 1, v_e_4244_);
lean_closure_set(v___f_4256_, 2, v___x_4254_);
v___x_4257_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_Sym_letToHave_spec__0___redArg(v_____do__lift_4245_, v___x_4253_, v___f_4256_, v___y_4246_, v___y_4247_, v___y_4248_, v___y_4249_, v___y_4250_, v___y_4251_);
return v___x_4257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_letToHave___lam__2___boxed(lean_object* v_e_4258_, lean_object* v_____do__lift_4259_, lean_object* v___y_4260_, lean_object* v___y_4261_, lean_object* v___y_4262_, lean_object* v___y_4263_, lean_object* v___y_4264_, lean_object* v___y_4265_, lean_object* v___y_4266_){
_start:
{
lean_object* v_res_4267_; 
v_res_4267_ = l_Lean_Meta_Sym_letToHave___lam__2(v_e_4258_, v_____do__lift_4259_, v___y_4260_, v___y_4261_, v___y_4262_, v___y_4263_, v___y_4264_, v___y_4265_);
lean_dec(v___y_4265_);
lean_dec_ref(v___y_4264_);
lean_dec(v___y_4263_);
lean_dec_ref(v___y_4262_);
lean_dec(v___y_4261_);
lean_dec_ref(v___y_4260_);
return v_res_4267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_letToHave___lam__3(lean_object* v___y_4268_, lean_object* v_zetaDeltaFVarIds_4269_, lean_object* v_a_x3f_4270_){
_start:
{
lean_object* v___x_4272_; lean_object* v_mctx_4273_; lean_object* v_cache_4274_; lean_object* v_postponed_4275_; lean_object* v_diag_4276_; lean_object* v___x_4278_; uint8_t v_isShared_4279_; uint8_t v_isSharedCheck_4286_; 
v___x_4272_ = lean_st_ref_take(v___y_4268_);
v_mctx_4273_ = lean_ctor_get(v___x_4272_, 0);
v_cache_4274_ = lean_ctor_get(v___x_4272_, 1);
v_postponed_4275_ = lean_ctor_get(v___x_4272_, 3);
v_diag_4276_ = lean_ctor_get(v___x_4272_, 4);
v_isSharedCheck_4286_ = !lean_is_exclusive(v___x_4272_);
if (v_isSharedCheck_4286_ == 0)
{
lean_object* v_unused_4287_; 
v_unused_4287_ = lean_ctor_get(v___x_4272_, 2);
lean_dec(v_unused_4287_);
v___x_4278_ = v___x_4272_;
v_isShared_4279_ = v_isSharedCheck_4286_;
goto v_resetjp_4277_;
}
else
{
lean_inc(v_diag_4276_);
lean_inc(v_postponed_4275_);
lean_inc(v_cache_4274_);
lean_inc(v_mctx_4273_);
lean_dec(v___x_4272_);
v___x_4278_ = lean_box(0);
v_isShared_4279_ = v_isSharedCheck_4286_;
goto v_resetjp_4277_;
}
v_resetjp_4277_:
{
lean_object* v___x_4281_; 
if (v_isShared_4279_ == 0)
{
lean_ctor_set(v___x_4278_, 2, v_zetaDeltaFVarIds_4269_);
v___x_4281_ = v___x_4278_;
goto v_reusejp_4280_;
}
else
{
lean_object* v_reuseFailAlloc_4285_; 
v_reuseFailAlloc_4285_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4285_, 0, v_mctx_4273_);
lean_ctor_set(v_reuseFailAlloc_4285_, 1, v_cache_4274_);
lean_ctor_set(v_reuseFailAlloc_4285_, 2, v_zetaDeltaFVarIds_4269_);
lean_ctor_set(v_reuseFailAlloc_4285_, 3, v_postponed_4275_);
lean_ctor_set(v_reuseFailAlloc_4285_, 4, v_diag_4276_);
v___x_4281_ = v_reuseFailAlloc_4285_;
goto v_reusejp_4280_;
}
v_reusejp_4280_:
{
lean_object* v___x_4282_; lean_object* v___x_4283_; lean_object* v___x_4284_; 
v___x_4282_ = lean_st_ref_put(v___y_4268_, v___x_4281_);
v___x_4283_ = lean_box(0);
v___x_4284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4284_, 0, v___x_4283_);
return v___x_4284_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_letToHave___lam__3___boxed(lean_object* v___y_4288_, lean_object* v_zetaDeltaFVarIds_4289_, lean_object* v_a_x3f_4290_, lean_object* v___y_4291_){
_start:
{
lean_object* v_res_4292_; 
v_res_4292_ = l_Lean_Meta_Sym_letToHave___lam__3(v___y_4288_, v_zetaDeltaFVarIds_4289_, v_a_x3f_4290_);
lean_dec(v_a_x3f_4290_);
lean_dec(v___y_4288_);
return v_res_4292_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_letToHave___lam__4(lean_object* v___y_4293_, lean_object* v_cache_4294_, lean_object* v_a_x3f_4295_){
_start:
{
lean_object* v___x_4297_; lean_object* v_mctx_4298_; lean_object* v_zetaDeltaFVarIds_4299_; lean_object* v_postponed_4300_; lean_object* v_diag_4301_; lean_object* v___x_4303_; uint8_t v_isShared_4304_; uint8_t v_isSharedCheck_4311_; 
v___x_4297_ = lean_st_ref_take(v___y_4293_);
v_mctx_4298_ = lean_ctor_get(v___x_4297_, 0);
v_zetaDeltaFVarIds_4299_ = lean_ctor_get(v___x_4297_, 2);
v_postponed_4300_ = lean_ctor_get(v___x_4297_, 3);
v_diag_4301_ = lean_ctor_get(v___x_4297_, 4);
v_isSharedCheck_4311_ = !lean_is_exclusive(v___x_4297_);
if (v_isSharedCheck_4311_ == 0)
{
lean_object* v_unused_4312_; 
v_unused_4312_ = lean_ctor_get(v___x_4297_, 1);
lean_dec(v_unused_4312_);
v___x_4303_ = v___x_4297_;
v_isShared_4304_ = v_isSharedCheck_4311_;
goto v_resetjp_4302_;
}
else
{
lean_inc(v_diag_4301_);
lean_inc(v_postponed_4300_);
lean_inc(v_zetaDeltaFVarIds_4299_);
lean_inc(v_mctx_4298_);
lean_dec(v___x_4297_);
v___x_4303_ = lean_box(0);
v_isShared_4304_ = v_isSharedCheck_4311_;
goto v_resetjp_4302_;
}
v_resetjp_4302_:
{
lean_object* v___x_4306_; 
if (v_isShared_4304_ == 0)
{
lean_ctor_set(v___x_4303_, 1, v_cache_4294_);
v___x_4306_ = v___x_4303_;
goto v_reusejp_4305_;
}
else
{
lean_object* v_reuseFailAlloc_4310_; 
v_reuseFailAlloc_4310_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4310_, 0, v_mctx_4298_);
lean_ctor_set(v_reuseFailAlloc_4310_, 1, v_cache_4294_);
lean_ctor_set(v_reuseFailAlloc_4310_, 2, v_zetaDeltaFVarIds_4299_);
lean_ctor_set(v_reuseFailAlloc_4310_, 3, v_postponed_4300_);
lean_ctor_set(v_reuseFailAlloc_4310_, 4, v_diag_4301_);
v___x_4306_ = v_reuseFailAlloc_4310_;
goto v_reusejp_4305_;
}
v_reusejp_4305_:
{
lean_object* v___x_4307_; lean_object* v___x_4308_; lean_object* v___x_4309_; 
v___x_4307_ = lean_st_ref_put(v___y_4293_, v___x_4306_);
v___x_4308_ = lean_box(0);
v___x_4309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4309_, 0, v___x_4308_);
return v___x_4309_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_letToHave___lam__4___boxed(lean_object* v___y_4313_, lean_object* v_cache_4314_, lean_object* v_a_x3f_4315_, lean_object* v___y_4316_){
_start:
{
lean_object* v_res_4317_; 
v_res_4317_ = l_Lean_Meta_Sym_letToHave___lam__4(v___y_4313_, v_cache_4314_, v_a_x3f_4315_);
lean_dec(v_a_x3f_4315_);
lean_dec(v___y_4313_);
return v_res_4317_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_letToHave___lam__5___closed__0(void){
_start:
{
lean_object* v___x_4318_; 
v___x_4318_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4318_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_letToHave___lam__5___closed__1(void){
_start:
{
lean_object* v___x_4319_; lean_object* v___x_4320_; 
v___x_4319_ = lean_obj_once(&l_Lean_Meta_Sym_letToHave___lam__5___closed__0, &l_Lean_Meta_Sym_letToHave___lam__5___closed__0_once, _init_l_Lean_Meta_Sym_letToHave___lam__5___closed__0);
v___x_4320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4320_, 0, v___x_4319_);
return v___x_4320_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_letToHave___lam__5___closed__2(void){
_start:
{
lean_object* v___x_4321_; lean_object* v___x_4322_; 
v___x_4321_ = lean_obj_once(&l_Lean_Meta_Sym_letToHave___lam__5___closed__1, &l_Lean_Meta_Sym_letToHave___lam__5___closed__1_once, _init_l_Lean_Meta_Sym_letToHave___lam__5___closed__1);
v___x_4322_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4322_, 0, v___x_4321_);
lean_ctor_set(v___x_4322_, 1, v___x_4321_);
lean_ctor_set(v___x_4322_, 2, v___x_4321_);
lean_ctor_set(v___x_4322_, 3, v___x_4321_);
lean_ctor_set(v___x_4322_, 4, v___x_4321_);
lean_ctor_set(v___x_4322_, 5, v___x_4321_);
return v___x_4322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_letToHave___lam__5(uint8_t v___x_4323_, lean_object* v___f_4324_, lean_object* v___f_4325_, lean_object* v___y_4326_, lean_object* v___y_4327_, lean_object* v___y_4328_, lean_object* v___y_4329_, lean_object* v___y_4330_, lean_object* v___y_4331_){
_start:
{
lean_object* v___x_4333_; lean_object* v___x_4334_; lean_object* v_mctx_4335_; lean_object* v_zetaDeltaFVarIds_4336_; lean_object* v_postponed_4337_; lean_object* v_diag_4338_; lean_object* v___x_4340_; uint8_t v_isShared_4341_; uint8_t v_isSharedCheck_4424_; 
v___x_4333_ = lean_st_ref_get(v___y_4329_);
v___x_4334_ = lean_st_ref_take(v___y_4329_);
v_mctx_4335_ = lean_ctor_get(v___x_4334_, 0);
v_zetaDeltaFVarIds_4336_ = lean_ctor_get(v___x_4334_, 2);
v_postponed_4337_ = lean_ctor_get(v___x_4334_, 3);
v_diag_4338_ = lean_ctor_get(v___x_4334_, 4);
v_isSharedCheck_4424_ = !lean_is_exclusive(v___x_4334_);
if (v_isSharedCheck_4424_ == 0)
{
lean_object* v_unused_4425_; 
v_unused_4425_ = lean_ctor_get(v___x_4334_, 1);
lean_dec(v_unused_4425_);
v___x_4340_ = v___x_4334_;
v_isShared_4341_ = v_isSharedCheck_4424_;
goto v_resetjp_4339_;
}
else
{
lean_inc(v_diag_4338_);
lean_inc(v_postponed_4337_);
lean_inc(v_zetaDeltaFVarIds_4336_);
lean_inc(v_mctx_4335_);
lean_dec(v___x_4334_);
v___x_4340_ = lean_box(0);
v_isShared_4341_ = v_isSharedCheck_4424_;
goto v_resetjp_4339_;
}
v_resetjp_4339_:
{
lean_object* v___x_4342_; lean_object* v___x_4344_; 
v___x_4342_ = lean_obj_once(&l_Lean_Meta_Sym_letToHave___lam__5___closed__2, &l_Lean_Meta_Sym_letToHave___lam__5___closed__2_once, _init_l_Lean_Meta_Sym_letToHave___lam__5___closed__2);
if (v_isShared_4341_ == 0)
{
lean_ctor_set(v___x_4340_, 1, v___x_4342_);
v___x_4344_ = v___x_4340_;
goto v_reusejp_4343_;
}
else
{
lean_object* v_reuseFailAlloc_4423_; 
v_reuseFailAlloc_4423_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4423_, 0, v_mctx_4335_);
lean_ctor_set(v_reuseFailAlloc_4423_, 1, v___x_4342_);
lean_ctor_set(v_reuseFailAlloc_4423_, 2, v_zetaDeltaFVarIds_4336_);
lean_ctor_set(v_reuseFailAlloc_4423_, 3, v_postponed_4337_);
lean_ctor_set(v_reuseFailAlloc_4423_, 4, v_diag_4338_);
v___x_4344_ = v_reuseFailAlloc_4423_;
goto v_reusejp_4343_;
}
v_reusejp_4343_:
{
lean_object* v___x_4345_; lean_object* v___x_4346_; lean_object* v_mctx_4347_; lean_object* v_cache_4348_; lean_object* v_zetaDeltaFVarIds_4349_; lean_object* v_postponed_4350_; lean_object* v_diag_4351_; lean_object* v___x_4353_; uint8_t v_isShared_4354_; uint8_t v_isSharedCheck_4422_; 
v___x_4345_ = lean_st_ref_put(v___y_4329_, v___x_4344_);
v___x_4346_ = lean_st_ref_take(v___y_4329_);
v_mctx_4347_ = lean_ctor_get(v___x_4346_, 0);
v_cache_4348_ = lean_ctor_get(v___x_4346_, 1);
v_zetaDeltaFVarIds_4349_ = lean_ctor_get(v___x_4346_, 2);
v_postponed_4350_ = lean_ctor_get(v___x_4346_, 3);
v_diag_4351_ = lean_ctor_get(v___x_4346_, 4);
v_isSharedCheck_4422_ = !lean_is_exclusive(v___x_4346_);
if (v_isSharedCheck_4422_ == 0)
{
v___x_4353_ = v___x_4346_;
v_isShared_4354_ = v_isSharedCheck_4422_;
goto v_resetjp_4352_;
}
else
{
lean_inc(v_diag_4351_);
lean_inc(v_postponed_4350_);
lean_inc(v_zetaDeltaFVarIds_4349_);
lean_inc(v_cache_4348_);
lean_inc(v_mctx_4347_);
lean_dec(v___x_4346_);
v___x_4353_ = lean_box(0);
v_isShared_4354_ = v_isSharedCheck_4422_;
goto v_resetjp_4352_;
}
v_resetjp_4352_:
{
lean_object* v___x_4355_; lean_object* v___x_4357_; 
v___x_4355_ = lean_box(1);
if (v_isShared_4354_ == 0)
{
lean_ctor_set(v___x_4353_, 2, v___x_4355_);
v___x_4357_ = v___x_4353_;
goto v_reusejp_4356_;
}
else
{
lean_object* v_reuseFailAlloc_4421_; 
v_reuseFailAlloc_4421_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4421_, 0, v_mctx_4347_);
lean_ctor_set(v_reuseFailAlloc_4421_, 1, v_cache_4348_);
lean_ctor_set(v_reuseFailAlloc_4421_, 2, v___x_4355_);
lean_ctor_set(v_reuseFailAlloc_4421_, 3, v_postponed_4350_);
lean_ctor_set(v_reuseFailAlloc_4421_, 4, v_diag_4351_);
v___x_4357_ = v_reuseFailAlloc_4421_;
goto v_reusejp_4356_;
}
v_reusejp_4356_:
{
lean_object* v___x_4358_; lean_object* v_cache_4359_; lean_object* v_keyedConfig_4360_; lean_object* v_zetaDeltaSet_4361_; lean_object* v_lctx_4362_; lean_object* v_localInstances_4363_; lean_object* v_defEqCtx_x3f_4364_; lean_object* v_synthPendingDepth_4365_; lean_object* v_customCanUnfoldPredicate_x3f_4366_; uint8_t v_univApprox_4367_; uint8_t v_inTypeClassResolution_4368_; uint8_t v_cacheInferType_4369_; uint8_t v___x_4370_; lean_object* v___x_4371_; lean_object* v___x_4372_; uint8_t v_transparency_4373_; lean_object* v_a_4375_; lean_object* v_a_4387_; lean_object* v_a_4400_; uint8_t v___x_4403_; 
v___x_4358_ = lean_st_ref_put(v___y_4329_, v___x_4357_);
v_cache_4359_ = lean_ctor_get(v___x_4333_, 1);
lean_inc_ref(v_cache_4359_);
lean_dec(v___x_4333_);
v_keyedConfig_4360_ = lean_ctor_get(v___y_4328_, 0);
v_zetaDeltaSet_4361_ = lean_ctor_get(v___y_4328_, 1);
v_lctx_4362_ = lean_ctor_get(v___y_4328_, 2);
v_localInstances_4363_ = lean_ctor_get(v___y_4328_, 3);
v_defEqCtx_x3f_4364_ = lean_ctor_get(v___y_4328_, 4);
v_synthPendingDepth_4365_ = lean_ctor_get(v___y_4328_, 5);
v_customCanUnfoldPredicate_x3f_4366_ = lean_ctor_get(v___y_4328_, 6);
v_univApprox_4367_ = lean_ctor_get_uint8(v___y_4328_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_4368_ = lean_ctor_get_uint8(v___y_4328_, sizeof(void*)*7 + 2);
v_cacheInferType_4369_ = lean_ctor_get_uint8(v___y_4328_, sizeof(void*)*7 + 3);
v___x_4370_ = 1;
lean_inc(v_customCanUnfoldPredicate_x3f_4366_);
lean_inc(v_synthPendingDepth_4365_);
lean_inc(v_defEqCtx_x3f_4364_);
lean_inc_ref(v_localInstances_4363_);
lean_inc_ref(v_lctx_4362_);
lean_inc(v_zetaDeltaSet_4361_);
lean_inc_ref(v_keyedConfig_4360_);
v___x_4371_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4371_, 0, v_keyedConfig_4360_);
lean_ctor_set(v___x_4371_, 1, v_zetaDeltaSet_4361_);
lean_ctor_set(v___x_4371_, 2, v_lctx_4362_);
lean_ctor_set(v___x_4371_, 3, v_localInstances_4363_);
lean_ctor_set(v___x_4371_, 4, v_defEqCtx_x3f_4364_);
lean_ctor_set(v___x_4371_, 5, v_synthPendingDepth_4365_);
lean_ctor_set(v___x_4371_, 6, v_customCanUnfoldPredicate_x3f_4366_);
lean_ctor_set_uint8(v___x_4371_, sizeof(void*)*7, v___x_4370_);
lean_ctor_set_uint8(v___x_4371_, sizeof(void*)*7 + 1, v_univApprox_4367_);
lean_ctor_set_uint8(v___x_4371_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4368_);
lean_ctor_set_uint8(v___x_4371_, sizeof(void*)*7 + 3, v_cacheInferType_4369_);
v___x_4372_ = l_Lean_Meta_Context_config(v___x_4371_);
lean_dec_ref_known(v___x_4371_, 7);
v_transparency_4373_ = lean_ctor_get_uint8(v___x_4372_, 9);
v___x_4403_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_4373_, v___x_4323_);
if (v___x_4403_ == 0)
{
lean_object* v___x_4404_; lean_object* v___x_4405_; lean_object* v___x_4406_; lean_object* v___x_4407_; uint64_t v___x_4408_; lean_object* v___x_4409_; lean_object* v___x_4410_; lean_object* v___x_4411_; 
lean_dec_ref(v___x_4372_);
lean_inc_ref(v_keyedConfig_4360_);
v___x_4404_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_4323_, v_keyedConfig_4360_);
lean_inc_n(v_customCanUnfoldPredicate_x3f_4366_, 2);
lean_inc_n(v_synthPendingDepth_4365_, 2);
lean_inc_n(v_defEqCtx_x3f_4364_, 2);
lean_inc_ref_n(v_localInstances_4363_, 2);
lean_inc_ref_n(v_lctx_4362_, 3);
lean_inc_n(v_zetaDeltaSet_4361_, 2);
v___x_4405_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4405_, 0, v___x_4404_);
lean_ctor_set(v___x_4405_, 1, v_zetaDeltaSet_4361_);
lean_ctor_set(v___x_4405_, 2, v_lctx_4362_);
lean_ctor_set(v___x_4405_, 3, v_localInstances_4363_);
lean_ctor_set(v___x_4405_, 4, v_defEqCtx_x3f_4364_);
lean_ctor_set(v___x_4405_, 5, v_synthPendingDepth_4365_);
lean_ctor_set(v___x_4405_, 6, v_customCanUnfoldPredicate_x3f_4366_);
lean_ctor_set_uint8(v___x_4405_, sizeof(void*)*7, v___x_4370_);
lean_ctor_set_uint8(v___x_4405_, sizeof(void*)*7 + 1, v_univApprox_4367_);
lean_ctor_set_uint8(v___x_4405_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4368_);
lean_ctor_set_uint8(v___x_4405_, sizeof(void*)*7 + 3, v_cacheInferType_4369_);
v___x_4406_ = l_Lean_Meta_Context_config(v___x_4405_);
lean_dec_ref_known(v___x_4405_, 7);
v___x_4407_ = lean_apply_1(v___f_4324_, v___x_4406_);
v___x_4408_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_4407_);
v___x_4409_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_4409_, 0, v___x_4407_);
lean_ctor_set_uint64(v___x_4409_, sizeof(void*)*1, v___x_4408_);
v___x_4410_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4410_, 0, v___x_4409_);
lean_ctor_set(v___x_4410_, 1, v_zetaDeltaSet_4361_);
lean_ctor_set(v___x_4410_, 2, v_lctx_4362_);
lean_ctor_set(v___x_4410_, 3, v_localInstances_4363_);
lean_ctor_set(v___x_4410_, 4, v_defEqCtx_x3f_4364_);
lean_ctor_set(v___x_4410_, 5, v_synthPendingDepth_4365_);
lean_ctor_set(v___x_4410_, 6, v_customCanUnfoldPredicate_x3f_4366_);
lean_ctor_set_uint8(v___x_4410_, sizeof(void*)*7, v___x_4370_);
lean_ctor_set_uint8(v___x_4410_, sizeof(void*)*7 + 1, v_univApprox_4367_);
lean_ctor_set_uint8(v___x_4410_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4368_);
lean_ctor_set_uint8(v___x_4410_, sizeof(void*)*7 + 3, v_cacheInferType_4369_);
lean_inc(v___y_4331_);
lean_inc_ref(v___y_4330_);
lean_inc(v___y_4329_);
lean_inc(v___y_4327_);
lean_inc_ref(v___y_4326_);
v___x_4411_ = lean_apply_8(v___f_4325_, v_lctx_4362_, v___y_4326_, v___y_4327_, v___x_4410_, v___y_4329_, v___y_4330_, v___y_4331_, lean_box(0));
if (lean_obj_tag(v___x_4411_) == 0)
{
lean_object* v_a_4412_; 
v_a_4412_ = lean_ctor_get(v___x_4411_, 0);
lean_inc(v_a_4412_);
lean_dec_ref_known(v___x_4411_, 1);
v_a_4387_ = v_a_4412_;
goto v___jp_4386_;
}
else
{
lean_object* v_a_4413_; 
v_a_4413_ = lean_ctor_get(v___x_4411_, 0);
lean_inc(v_a_4413_);
lean_dec_ref_known(v___x_4411_, 1);
v_a_4400_ = v_a_4413_;
goto v___jp_4399_;
}
}
else
{
lean_object* v___x_4414_; uint64_t v___x_4415_; lean_object* v___x_4416_; lean_object* v___x_4417_; lean_object* v___x_4418_; 
v___x_4414_ = lean_apply_1(v___f_4324_, v___x_4372_);
v___x_4415_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_4414_);
v___x_4416_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_4416_, 0, v___x_4414_);
lean_ctor_set_uint64(v___x_4416_, sizeof(void*)*1, v___x_4415_);
lean_inc(v_customCanUnfoldPredicate_x3f_4366_);
lean_inc(v_synthPendingDepth_4365_);
lean_inc(v_defEqCtx_x3f_4364_);
lean_inc_ref(v_localInstances_4363_);
lean_inc_ref_n(v_lctx_4362_, 2);
lean_inc(v_zetaDeltaSet_4361_);
v___x_4417_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4417_, 0, v___x_4416_);
lean_ctor_set(v___x_4417_, 1, v_zetaDeltaSet_4361_);
lean_ctor_set(v___x_4417_, 2, v_lctx_4362_);
lean_ctor_set(v___x_4417_, 3, v_localInstances_4363_);
lean_ctor_set(v___x_4417_, 4, v_defEqCtx_x3f_4364_);
lean_ctor_set(v___x_4417_, 5, v_synthPendingDepth_4365_);
lean_ctor_set(v___x_4417_, 6, v_customCanUnfoldPredicate_x3f_4366_);
lean_ctor_set_uint8(v___x_4417_, sizeof(void*)*7, v___x_4370_);
lean_ctor_set_uint8(v___x_4417_, sizeof(void*)*7 + 1, v_univApprox_4367_);
lean_ctor_set_uint8(v___x_4417_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4368_);
lean_ctor_set_uint8(v___x_4417_, sizeof(void*)*7 + 3, v_cacheInferType_4369_);
lean_inc(v___y_4331_);
lean_inc_ref(v___y_4330_);
lean_inc(v___y_4329_);
lean_inc(v___y_4327_);
lean_inc_ref(v___y_4326_);
v___x_4418_ = lean_apply_8(v___f_4325_, v_lctx_4362_, v___y_4326_, v___y_4327_, v___x_4417_, v___y_4329_, v___y_4330_, v___y_4331_, lean_box(0));
if (lean_obj_tag(v___x_4418_) == 0)
{
lean_object* v_a_4419_; 
v_a_4419_ = lean_ctor_get(v___x_4418_, 0);
lean_inc(v_a_4419_);
lean_dec_ref_known(v___x_4418_, 1);
v_a_4387_ = v_a_4419_;
goto v___jp_4386_;
}
else
{
lean_object* v_a_4420_; 
v_a_4420_ = lean_ctor_get(v___x_4418_, 0);
lean_inc(v_a_4420_);
lean_dec_ref_known(v___x_4418_, 1);
v_a_4400_ = v_a_4420_;
goto v___jp_4399_;
}
}
v___jp_4374_:
{
lean_object* v___x_4376_; lean_object* v___x_4377_; lean_object* v___x_4379_; uint8_t v_isShared_4380_; uint8_t v_isSharedCheck_4384_; 
v___x_4376_ = lean_box(0);
v___x_4377_ = l_Lean_Meta_Sym_letToHave___lam__4(v___y_4329_, v_cache_4359_, v___x_4376_);
v_isSharedCheck_4384_ = !lean_is_exclusive(v___x_4377_);
if (v_isSharedCheck_4384_ == 0)
{
lean_object* v_unused_4385_; 
v_unused_4385_ = lean_ctor_get(v___x_4377_, 0);
lean_dec(v_unused_4385_);
v___x_4379_ = v___x_4377_;
v_isShared_4380_ = v_isSharedCheck_4384_;
goto v_resetjp_4378_;
}
else
{
lean_dec(v___x_4377_);
v___x_4379_ = lean_box(0);
v_isShared_4380_ = v_isSharedCheck_4384_;
goto v_resetjp_4378_;
}
v_resetjp_4378_:
{
lean_object* v___x_4382_; 
if (v_isShared_4380_ == 0)
{
lean_ctor_set_tag(v___x_4379_, 1);
lean_ctor_set(v___x_4379_, 0, v_a_4375_);
v___x_4382_ = v___x_4379_;
goto v_reusejp_4381_;
}
else
{
lean_object* v_reuseFailAlloc_4383_; 
v_reuseFailAlloc_4383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4383_, 0, v_a_4375_);
v___x_4382_ = v_reuseFailAlloc_4383_;
goto v_reusejp_4381_;
}
v_reusejp_4381_:
{
return v___x_4382_;
}
}
}
v___jp_4386_:
{
lean_object* v___x_4388_; lean_object* v___x_4389_; lean_object* v___x_4390_; lean_object* v___x_4392_; uint8_t v_isShared_4393_; uint8_t v_isSharedCheck_4397_; 
lean_inc(v_a_4387_);
v___x_4388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4388_, 0, v_a_4387_);
v___x_4389_ = l_Lean_Meta_Sym_letToHave___lam__3(v___y_4329_, v_zetaDeltaFVarIds_4349_, v___x_4388_);
lean_dec_ref(v___x_4389_);
v___x_4390_ = l_Lean_Meta_Sym_letToHave___lam__4(v___y_4329_, v_cache_4359_, v___x_4388_);
lean_dec_ref_known(v___x_4388_, 1);
v_isSharedCheck_4397_ = !lean_is_exclusive(v___x_4390_);
if (v_isSharedCheck_4397_ == 0)
{
lean_object* v_unused_4398_; 
v_unused_4398_ = lean_ctor_get(v___x_4390_, 0);
lean_dec(v_unused_4398_);
v___x_4392_ = v___x_4390_;
v_isShared_4393_ = v_isSharedCheck_4397_;
goto v_resetjp_4391_;
}
else
{
lean_dec(v___x_4390_);
v___x_4392_ = lean_box(0);
v_isShared_4393_ = v_isSharedCheck_4397_;
goto v_resetjp_4391_;
}
v_resetjp_4391_:
{
lean_object* v___x_4395_; 
if (v_isShared_4393_ == 0)
{
lean_ctor_set(v___x_4392_, 0, v_a_4387_);
v___x_4395_ = v___x_4392_;
goto v_reusejp_4394_;
}
else
{
lean_object* v_reuseFailAlloc_4396_; 
v_reuseFailAlloc_4396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4396_, 0, v_a_4387_);
v___x_4395_ = v_reuseFailAlloc_4396_;
goto v_reusejp_4394_;
}
v_reusejp_4394_:
{
return v___x_4395_;
}
}
}
v___jp_4399_:
{
lean_object* v___x_4401_; lean_object* v___x_4402_; 
v___x_4401_ = lean_box(0);
v___x_4402_ = l_Lean_Meta_Sym_letToHave___lam__3(v___y_4329_, v_zetaDeltaFVarIds_4349_, v___x_4401_);
lean_dec_ref(v___x_4402_);
v_a_4375_ = v_a_4400_;
goto v___jp_4374_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_letToHave___lam__5___boxed(lean_object* v___x_4426_, lean_object* v___f_4427_, lean_object* v___f_4428_, lean_object* v___y_4429_, lean_object* v___y_4430_, lean_object* v___y_4431_, lean_object* v___y_4432_, lean_object* v___y_4433_, lean_object* v___y_4434_, lean_object* v___y_4435_){
_start:
{
uint8_t v___x_18476__boxed_4436_; lean_object* v_res_4437_; 
v___x_18476__boxed_4436_ = lean_unbox(v___x_4426_);
v_res_4437_ = l_Lean_Meta_Sym_letToHave___lam__5(v___x_18476__boxed_4436_, v___f_4427_, v___f_4428_, v___y_4429_, v___y_4430_, v___y_4431_, v___y_4432_, v___y_4433_, v___y_4434_);
lean_dec(v___y_4434_);
lean_dec_ref(v___y_4433_);
lean_dec(v___y_4432_);
lean_dec_ref(v___y_4431_);
lean_dec(v___y_4430_);
lean_dec_ref(v___y_4429_);
return v_res_4437_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_letToHave_spec__3___redArg(lean_object* v_msg_4438_, lean_object* v___y_4439_, lean_object* v___y_4440_, lean_object* v___y_4441_, lean_object* v___y_4442_){
_start:
{
lean_object* v_ref_4444_; lean_object* v___x_4445_; lean_object* v_a_4446_; lean_object* v___x_4448_; uint8_t v_isShared_4449_; uint8_t v_isSharedCheck_4454_; 
v_ref_4444_ = lean_ctor_get(v___y_4441_, 2);
v___x_4445_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_LetToHave_0__Lean_Meta_Sym_LetToHave_checkDefEq_spec__0_spec__0(v_msg_4438_, v___y_4439_, v___y_4440_, v___y_4441_, v___y_4442_);
v_a_4446_ = lean_ctor_get(v___x_4445_, 0);
v_isSharedCheck_4454_ = !lean_is_exclusive(v___x_4445_);
if (v_isSharedCheck_4454_ == 0)
{
v___x_4448_ = v___x_4445_;
v_isShared_4449_ = v_isSharedCheck_4454_;
goto v_resetjp_4447_;
}
else
{
lean_inc(v_a_4446_);
lean_dec(v___x_4445_);
v___x_4448_ = lean_box(0);
v_isShared_4449_ = v_isSharedCheck_4454_;
goto v_resetjp_4447_;
}
v_resetjp_4447_:
{
lean_object* v___x_4450_; lean_object* v___x_4452_; 
lean_inc(v_ref_4444_);
v___x_4450_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4450_, 0, v_ref_4444_);
lean_ctor_set(v___x_4450_, 1, v_a_4446_);
if (v_isShared_4449_ == 0)
{
lean_ctor_set_tag(v___x_4448_, 1);
lean_ctor_set(v___x_4448_, 0, v___x_4450_);
v___x_4452_ = v___x_4448_;
goto v_reusejp_4451_;
}
else
{
lean_object* v_reuseFailAlloc_4453_; 
v_reuseFailAlloc_4453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4453_, 0, v___x_4450_);
v___x_4452_ = v_reuseFailAlloc_4453_;
goto v_reusejp_4451_;
}
v_reusejp_4451_:
{
return v___x_4452_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_letToHave_spec__3___redArg___boxed(lean_object* v_msg_4455_, lean_object* v___y_4456_, lean_object* v___y_4457_, lean_object* v___y_4458_, lean_object* v___y_4459_, lean_object* v___y_4460_){
_start:
{
lean_object* v_res_4461_; 
v_res_4461_ = l_Lean_throwError___at___00Lean_Meta_Sym_letToHave_spec__3___redArg(v_msg_4455_, v___y_4456_, v___y_4457_, v___y_4458_, v___y_4459_);
lean_dec(v___y_4459_);
lean_dec_ref(v___y_4458_);
lean_dec(v___y_4457_);
lean_dec_ref(v___y_4456_);
return v_res_4461_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg___lam__0(lean_object* v___y_4462_, uint8_t v_isExporting_4463_, lean_object* v___x_4464_, lean_object* v___y_4465_, lean_object* v___x_4466_, lean_object* v_a_x3f_4467_){
_start:
{
lean_object* v___x_4469_; lean_object* v_env_4470_; lean_object* v_nextMacroScope_4471_; lean_object* v_ngen_4472_; lean_object* v_auxDeclNGen_4473_; lean_object* v_traceState_4474_; lean_object* v_messages_4475_; lean_object* v_infoState_4476_; lean_object* v_snapshotTasks_4477_; lean_object* v___x_4479_; uint8_t v_isShared_4480_; uint8_t v_isSharedCheck_4502_; 
v___x_4469_ = lean_st_ref_take(v___y_4462_);
v_env_4470_ = lean_ctor_get(v___x_4469_, 0);
v_nextMacroScope_4471_ = lean_ctor_get(v___x_4469_, 1);
v_ngen_4472_ = lean_ctor_get(v___x_4469_, 2);
v_auxDeclNGen_4473_ = lean_ctor_get(v___x_4469_, 3);
v_traceState_4474_ = lean_ctor_get(v___x_4469_, 4);
v_messages_4475_ = lean_ctor_get(v___x_4469_, 6);
v_infoState_4476_ = lean_ctor_get(v___x_4469_, 7);
v_snapshotTasks_4477_ = lean_ctor_get(v___x_4469_, 8);
v_isSharedCheck_4502_ = !lean_is_exclusive(v___x_4469_);
if (v_isSharedCheck_4502_ == 0)
{
lean_object* v_unused_4503_; 
v_unused_4503_ = lean_ctor_get(v___x_4469_, 5);
lean_dec(v_unused_4503_);
v___x_4479_ = v___x_4469_;
v_isShared_4480_ = v_isSharedCheck_4502_;
goto v_resetjp_4478_;
}
else
{
lean_inc(v_snapshotTasks_4477_);
lean_inc(v_infoState_4476_);
lean_inc(v_messages_4475_);
lean_inc(v_traceState_4474_);
lean_inc(v_auxDeclNGen_4473_);
lean_inc(v_ngen_4472_);
lean_inc(v_nextMacroScope_4471_);
lean_inc(v_env_4470_);
lean_dec(v___x_4469_);
v___x_4479_ = lean_box(0);
v_isShared_4480_ = v_isSharedCheck_4502_;
goto v_resetjp_4478_;
}
v_resetjp_4478_:
{
lean_object* v___x_4481_; lean_object* v___x_4483_; 
v___x_4481_ = l_Lean_Environment_setExporting(v_env_4470_, v_isExporting_4463_);
if (v_isShared_4480_ == 0)
{
lean_ctor_set(v___x_4479_, 5, v___x_4464_);
lean_ctor_set(v___x_4479_, 0, v___x_4481_);
v___x_4483_ = v___x_4479_;
goto v_reusejp_4482_;
}
else
{
lean_object* v_reuseFailAlloc_4501_; 
v_reuseFailAlloc_4501_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4501_, 0, v___x_4481_);
lean_ctor_set(v_reuseFailAlloc_4501_, 1, v_nextMacroScope_4471_);
lean_ctor_set(v_reuseFailAlloc_4501_, 2, v_ngen_4472_);
lean_ctor_set(v_reuseFailAlloc_4501_, 3, v_auxDeclNGen_4473_);
lean_ctor_set(v_reuseFailAlloc_4501_, 4, v_traceState_4474_);
lean_ctor_set(v_reuseFailAlloc_4501_, 5, v___x_4464_);
lean_ctor_set(v_reuseFailAlloc_4501_, 6, v_messages_4475_);
lean_ctor_set(v_reuseFailAlloc_4501_, 7, v_infoState_4476_);
lean_ctor_set(v_reuseFailAlloc_4501_, 8, v_snapshotTasks_4477_);
v___x_4483_ = v_reuseFailAlloc_4501_;
goto v_reusejp_4482_;
}
v_reusejp_4482_:
{
lean_object* v___x_4484_; lean_object* v___x_4485_; lean_object* v_mctx_4486_; lean_object* v_zetaDeltaFVarIds_4487_; lean_object* v_postponed_4488_; lean_object* v_diag_4489_; lean_object* v___x_4491_; uint8_t v_isShared_4492_; uint8_t v_isSharedCheck_4499_; 
v___x_4484_ = lean_st_ref_put(v___y_4462_, v___x_4483_);
v___x_4485_ = lean_st_ref_take(v___y_4465_);
v_mctx_4486_ = lean_ctor_get(v___x_4485_, 0);
v_zetaDeltaFVarIds_4487_ = lean_ctor_get(v___x_4485_, 2);
v_postponed_4488_ = lean_ctor_get(v___x_4485_, 3);
v_diag_4489_ = lean_ctor_get(v___x_4485_, 4);
v_isSharedCheck_4499_ = !lean_is_exclusive(v___x_4485_);
if (v_isSharedCheck_4499_ == 0)
{
lean_object* v_unused_4500_; 
v_unused_4500_ = lean_ctor_get(v___x_4485_, 1);
lean_dec(v_unused_4500_);
v___x_4491_ = v___x_4485_;
v_isShared_4492_ = v_isSharedCheck_4499_;
goto v_resetjp_4490_;
}
else
{
lean_inc(v_diag_4489_);
lean_inc(v_postponed_4488_);
lean_inc(v_zetaDeltaFVarIds_4487_);
lean_inc(v_mctx_4486_);
lean_dec(v___x_4485_);
v___x_4491_ = lean_box(0);
v_isShared_4492_ = v_isSharedCheck_4499_;
goto v_resetjp_4490_;
}
v_resetjp_4490_:
{
lean_object* v___x_4494_; 
if (v_isShared_4492_ == 0)
{
lean_ctor_set(v___x_4491_, 1, v___x_4466_);
v___x_4494_ = v___x_4491_;
goto v_reusejp_4493_;
}
else
{
lean_object* v_reuseFailAlloc_4498_; 
v_reuseFailAlloc_4498_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4498_, 0, v_mctx_4486_);
lean_ctor_set(v_reuseFailAlloc_4498_, 1, v___x_4466_);
lean_ctor_set(v_reuseFailAlloc_4498_, 2, v_zetaDeltaFVarIds_4487_);
lean_ctor_set(v_reuseFailAlloc_4498_, 3, v_postponed_4488_);
lean_ctor_set(v_reuseFailAlloc_4498_, 4, v_diag_4489_);
v___x_4494_ = v_reuseFailAlloc_4498_;
goto v_reusejp_4493_;
}
v_reusejp_4493_:
{
lean_object* v___x_4495_; lean_object* v___x_4496_; lean_object* v___x_4497_; 
v___x_4495_ = lean_st_ref_put(v___y_4465_, v___x_4494_);
v___x_4496_ = lean_box(0);
v___x_4497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4497_, 0, v___x_4496_);
return v___x_4497_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg___lam__0___boxed(lean_object* v___y_4504_, lean_object* v_isExporting_4505_, lean_object* v___x_4506_, lean_object* v___y_4507_, lean_object* v___x_4508_, lean_object* v_a_x3f_4509_, lean_object* v___y_4510_){
_start:
{
uint8_t v_isExporting_boxed_4511_; lean_object* v_res_4512_; 
v_isExporting_boxed_4511_ = lean_unbox(v_isExporting_4505_);
v_res_4512_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg___lam__0(v___y_4504_, v_isExporting_boxed_4511_, v___x_4506_, v___y_4507_, v___x_4508_, v_a_x3f_4509_);
lean_dec(v_a_x3f_4509_);
lean_dec(v___y_4507_);
lean_dec(v___y_4504_);
return v_res_4512_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_4513_; 
v___x_4513_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4513_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_4514_; lean_object* v___x_4515_; 
v___x_4514_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg___closed__0, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg___closed__0);
v___x_4515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4515_, 0, v___x_4514_);
return v___x_4515_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_4516_; lean_object* v___x_4517_; 
v___x_4516_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg___closed__1, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg___closed__1);
v___x_4517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4517_, 0, v___x_4516_);
lean_ctor_set(v___x_4517_, 1, v___x_4516_);
return v___x_4517_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_4518_; lean_object* v___x_4519_; 
v___x_4518_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg___closed__1, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg___closed__1);
v___x_4519_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4519_, 0, v___x_4518_);
lean_ctor_set(v___x_4519_, 1, v___x_4518_);
lean_ctor_set(v___x_4519_, 2, v___x_4518_);
lean_ctor_set(v___x_4519_, 3, v___x_4518_);
lean_ctor_set(v___x_4519_, 4, v___x_4518_);
lean_ctor_set(v___x_4519_, 5, v___x_4518_);
return v___x_4519_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg(lean_object* v_x_4520_, uint8_t v_isExporting_4521_, lean_object* v___y_4522_, lean_object* v___y_4523_, lean_object* v___y_4524_, lean_object* v___y_4525_, lean_object* v___y_4526_, lean_object* v___y_4527_){
_start:
{
lean_object* v___x_4529_; lean_object* v_env_4530_; lean_object* v___x_4531_; uint8_t v_isModule_4532_; 
v___x_4529_ = lean_st_ref_get(v___y_4527_);
v_env_4530_ = lean_ctor_get(v___x_4529_, 0);
lean_inc_ref(v_env_4530_);
lean_dec(v___x_4529_);
v___x_4531_ = l_Lean_Environment_header(v_env_4530_);
v_isModule_4532_ = lean_ctor_get_uint8(v___x_4531_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4531_);
if (v_isModule_4532_ == 0)
{
lean_object* v___x_4533_; 
lean_dec_ref(v_env_4530_);
lean_inc(v___y_4527_);
lean_inc_ref(v___y_4526_);
lean_inc(v___y_4525_);
lean_inc_ref(v___y_4524_);
lean_inc(v___y_4523_);
lean_inc_ref(v___y_4522_);
v___x_4533_ = lean_apply_7(v_x_4520_, v___y_4522_, v___y_4523_, v___y_4524_, v___y_4525_, v___y_4526_, v___y_4527_, lean_box(0));
return v___x_4533_;
}
else
{
uint8_t v_isExporting_4534_; 
v_isExporting_4534_ = lean_ctor_get_uint8(v_env_4530_, sizeof(void*)*8);
lean_dec_ref(v_env_4530_);
if (v_isExporting_4521_ == 0)
{
if (v_isExporting_4534_ == 0)
{
lean_object* v___x_4600_; 
lean_inc(v___y_4527_);
lean_inc_ref(v___y_4526_);
lean_inc(v___y_4525_);
lean_inc_ref(v___y_4524_);
lean_inc(v___y_4523_);
lean_inc_ref(v___y_4522_);
v___x_4600_ = lean_apply_7(v_x_4520_, v___y_4522_, v___y_4523_, v___y_4524_, v___y_4525_, v___y_4526_, v___y_4527_, lean_box(0));
return v___x_4600_;
}
else
{
goto v___jp_4535_;
}
}
else
{
if (v_isExporting_4534_ == 0)
{
goto v___jp_4535_;
}
else
{
lean_object* v___x_4601_; 
lean_inc(v___y_4527_);
lean_inc_ref(v___y_4526_);
lean_inc(v___y_4525_);
lean_inc_ref(v___y_4524_);
lean_inc(v___y_4523_);
lean_inc_ref(v___y_4522_);
v___x_4601_ = lean_apply_7(v_x_4520_, v___y_4522_, v___y_4523_, v___y_4524_, v___y_4525_, v___y_4526_, v___y_4527_, lean_box(0));
return v___x_4601_;
}
}
v___jp_4535_:
{
lean_object* v___x_4536_; lean_object* v_env_4537_; lean_object* v_nextMacroScope_4538_; lean_object* v_ngen_4539_; lean_object* v_auxDeclNGen_4540_; lean_object* v_traceState_4541_; lean_object* v_messages_4542_; lean_object* v_infoState_4543_; lean_object* v_snapshotTasks_4544_; lean_object* v___x_4546_; uint8_t v_isShared_4547_; uint8_t v_isSharedCheck_4598_; 
v___x_4536_ = lean_st_ref_take(v___y_4527_);
v_env_4537_ = lean_ctor_get(v___x_4536_, 0);
v_nextMacroScope_4538_ = lean_ctor_get(v___x_4536_, 1);
v_ngen_4539_ = lean_ctor_get(v___x_4536_, 2);
v_auxDeclNGen_4540_ = lean_ctor_get(v___x_4536_, 3);
v_traceState_4541_ = lean_ctor_get(v___x_4536_, 4);
v_messages_4542_ = lean_ctor_get(v___x_4536_, 6);
v_infoState_4543_ = lean_ctor_get(v___x_4536_, 7);
v_snapshotTasks_4544_ = lean_ctor_get(v___x_4536_, 8);
v_isSharedCheck_4598_ = !lean_is_exclusive(v___x_4536_);
if (v_isSharedCheck_4598_ == 0)
{
lean_object* v_unused_4599_; 
v_unused_4599_ = lean_ctor_get(v___x_4536_, 5);
lean_dec(v_unused_4599_);
v___x_4546_ = v___x_4536_;
v_isShared_4547_ = v_isSharedCheck_4598_;
goto v_resetjp_4545_;
}
else
{
lean_inc(v_snapshotTasks_4544_);
lean_inc(v_infoState_4543_);
lean_inc(v_messages_4542_);
lean_inc(v_traceState_4541_);
lean_inc(v_auxDeclNGen_4540_);
lean_inc(v_ngen_4539_);
lean_inc(v_nextMacroScope_4538_);
lean_inc(v_env_4537_);
lean_dec(v___x_4536_);
v___x_4546_ = lean_box(0);
v_isShared_4547_ = v_isSharedCheck_4598_;
goto v_resetjp_4545_;
}
v_resetjp_4545_:
{
lean_object* v___x_4548_; lean_object* v___x_4549_; lean_object* v___x_4551_; 
v___x_4548_ = l_Lean_Environment_setExporting(v_env_4537_, v_isExporting_4521_);
v___x_4549_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg___closed__2, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg___closed__2);
if (v_isShared_4547_ == 0)
{
lean_ctor_set(v___x_4546_, 5, v___x_4549_);
lean_ctor_set(v___x_4546_, 0, v___x_4548_);
v___x_4551_ = v___x_4546_;
goto v_reusejp_4550_;
}
else
{
lean_object* v_reuseFailAlloc_4597_; 
v_reuseFailAlloc_4597_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4597_, 0, v___x_4548_);
lean_ctor_set(v_reuseFailAlloc_4597_, 1, v_nextMacroScope_4538_);
lean_ctor_set(v_reuseFailAlloc_4597_, 2, v_ngen_4539_);
lean_ctor_set(v_reuseFailAlloc_4597_, 3, v_auxDeclNGen_4540_);
lean_ctor_set(v_reuseFailAlloc_4597_, 4, v_traceState_4541_);
lean_ctor_set(v_reuseFailAlloc_4597_, 5, v___x_4549_);
lean_ctor_set(v_reuseFailAlloc_4597_, 6, v_messages_4542_);
lean_ctor_set(v_reuseFailAlloc_4597_, 7, v_infoState_4543_);
lean_ctor_set(v_reuseFailAlloc_4597_, 8, v_snapshotTasks_4544_);
v___x_4551_ = v_reuseFailAlloc_4597_;
goto v_reusejp_4550_;
}
v_reusejp_4550_:
{
lean_object* v___x_4552_; lean_object* v___x_4553_; lean_object* v_mctx_4554_; lean_object* v_zetaDeltaFVarIds_4555_; lean_object* v_postponed_4556_; lean_object* v_diag_4557_; lean_object* v___x_4559_; uint8_t v_isShared_4560_; uint8_t v_isSharedCheck_4595_; 
v___x_4552_ = lean_st_ref_put(v___y_4527_, v___x_4551_);
v___x_4553_ = lean_st_ref_take(v___y_4525_);
v_mctx_4554_ = lean_ctor_get(v___x_4553_, 0);
v_zetaDeltaFVarIds_4555_ = lean_ctor_get(v___x_4553_, 2);
v_postponed_4556_ = lean_ctor_get(v___x_4553_, 3);
v_diag_4557_ = lean_ctor_get(v___x_4553_, 4);
v_isSharedCheck_4595_ = !lean_is_exclusive(v___x_4553_);
if (v_isSharedCheck_4595_ == 0)
{
lean_object* v_unused_4596_; 
v_unused_4596_ = lean_ctor_get(v___x_4553_, 1);
lean_dec(v_unused_4596_);
v___x_4559_ = v___x_4553_;
v_isShared_4560_ = v_isSharedCheck_4595_;
goto v_resetjp_4558_;
}
else
{
lean_inc(v_diag_4557_);
lean_inc(v_postponed_4556_);
lean_inc(v_zetaDeltaFVarIds_4555_);
lean_inc(v_mctx_4554_);
lean_dec(v___x_4553_);
v___x_4559_ = lean_box(0);
v_isShared_4560_ = v_isSharedCheck_4595_;
goto v_resetjp_4558_;
}
v_resetjp_4558_:
{
lean_object* v___x_4561_; lean_object* v___x_4563_; 
v___x_4561_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg___closed__3, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg___closed__3);
if (v_isShared_4560_ == 0)
{
lean_ctor_set(v___x_4559_, 1, v___x_4561_);
v___x_4563_ = v___x_4559_;
goto v_reusejp_4562_;
}
else
{
lean_object* v_reuseFailAlloc_4594_; 
v_reuseFailAlloc_4594_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4594_, 0, v_mctx_4554_);
lean_ctor_set(v_reuseFailAlloc_4594_, 1, v___x_4561_);
lean_ctor_set(v_reuseFailAlloc_4594_, 2, v_zetaDeltaFVarIds_4555_);
lean_ctor_set(v_reuseFailAlloc_4594_, 3, v_postponed_4556_);
lean_ctor_set(v_reuseFailAlloc_4594_, 4, v_diag_4557_);
v___x_4563_ = v_reuseFailAlloc_4594_;
goto v_reusejp_4562_;
}
v_reusejp_4562_:
{
lean_object* v___x_4564_; lean_object* v_r_4565_; 
v___x_4564_ = lean_st_ref_put(v___y_4525_, v___x_4563_);
lean_inc(v___y_4527_);
lean_inc_ref(v___y_4526_);
lean_inc(v___y_4525_);
lean_inc_ref(v___y_4524_);
lean_inc(v___y_4523_);
lean_inc_ref(v___y_4522_);
v_r_4565_ = lean_apply_7(v_x_4520_, v___y_4522_, v___y_4523_, v___y_4524_, v___y_4525_, v___y_4526_, v___y_4527_, lean_box(0));
if (lean_obj_tag(v_r_4565_) == 0)
{
lean_object* v_a_4566_; lean_object* v___x_4568_; uint8_t v_isShared_4569_; uint8_t v_isSharedCheck_4582_; 
v_a_4566_ = lean_ctor_get(v_r_4565_, 0);
v_isSharedCheck_4582_ = !lean_is_exclusive(v_r_4565_);
if (v_isSharedCheck_4582_ == 0)
{
v___x_4568_ = v_r_4565_;
v_isShared_4569_ = v_isSharedCheck_4582_;
goto v_resetjp_4567_;
}
else
{
lean_inc(v_a_4566_);
lean_dec(v_r_4565_);
v___x_4568_ = lean_box(0);
v_isShared_4569_ = v_isSharedCheck_4582_;
goto v_resetjp_4567_;
}
v_resetjp_4567_:
{
lean_object* v___x_4571_; 
lean_inc(v_a_4566_);
if (v_isShared_4569_ == 0)
{
lean_ctor_set_tag(v___x_4568_, 1);
v___x_4571_ = v___x_4568_;
goto v_reusejp_4570_;
}
else
{
lean_object* v_reuseFailAlloc_4581_; 
v_reuseFailAlloc_4581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4581_, 0, v_a_4566_);
v___x_4571_ = v_reuseFailAlloc_4581_;
goto v_reusejp_4570_;
}
v_reusejp_4570_:
{
lean_object* v___x_4572_; lean_object* v___x_4574_; uint8_t v_isShared_4575_; uint8_t v_isSharedCheck_4579_; 
v___x_4572_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg___lam__0(v___y_4527_, v_isExporting_4534_, v___x_4549_, v___y_4525_, v___x_4561_, v___x_4571_);
lean_dec_ref(v___x_4571_);
v_isSharedCheck_4579_ = !lean_is_exclusive(v___x_4572_);
if (v_isSharedCheck_4579_ == 0)
{
lean_object* v_unused_4580_; 
v_unused_4580_ = lean_ctor_get(v___x_4572_, 0);
lean_dec(v_unused_4580_);
v___x_4574_ = v___x_4572_;
v_isShared_4575_ = v_isSharedCheck_4579_;
goto v_resetjp_4573_;
}
else
{
lean_dec(v___x_4572_);
v___x_4574_ = lean_box(0);
v_isShared_4575_ = v_isSharedCheck_4579_;
goto v_resetjp_4573_;
}
v_resetjp_4573_:
{
lean_object* v___x_4577_; 
if (v_isShared_4575_ == 0)
{
lean_ctor_set(v___x_4574_, 0, v_a_4566_);
v___x_4577_ = v___x_4574_;
goto v_reusejp_4576_;
}
else
{
lean_object* v_reuseFailAlloc_4578_; 
v_reuseFailAlloc_4578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4578_, 0, v_a_4566_);
v___x_4577_ = v_reuseFailAlloc_4578_;
goto v_reusejp_4576_;
}
v_reusejp_4576_:
{
return v___x_4577_;
}
}
}
}
}
else
{
lean_object* v_a_4583_; lean_object* v___x_4584_; lean_object* v___x_4585_; lean_object* v___x_4587_; uint8_t v_isShared_4588_; uint8_t v_isSharedCheck_4592_; 
v_a_4583_ = lean_ctor_get(v_r_4565_, 0);
lean_inc(v_a_4583_);
lean_dec_ref_known(v_r_4565_, 1);
v___x_4584_ = lean_box(0);
v___x_4585_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg___lam__0(v___y_4527_, v_isExporting_4534_, v___x_4549_, v___y_4525_, v___x_4561_, v___x_4584_);
v_isSharedCheck_4592_ = !lean_is_exclusive(v___x_4585_);
if (v_isSharedCheck_4592_ == 0)
{
lean_object* v_unused_4593_; 
v_unused_4593_ = lean_ctor_get(v___x_4585_, 0);
lean_dec(v_unused_4593_);
v___x_4587_ = v___x_4585_;
v_isShared_4588_ = v_isSharedCheck_4592_;
goto v_resetjp_4586_;
}
else
{
lean_dec(v___x_4585_);
v___x_4587_ = lean_box(0);
v_isShared_4588_ = v_isSharedCheck_4592_;
goto v_resetjp_4586_;
}
v_resetjp_4586_:
{
lean_object* v___x_4590_; 
if (v_isShared_4588_ == 0)
{
lean_ctor_set_tag(v___x_4587_, 1);
lean_ctor_set(v___x_4587_, 0, v_a_4583_);
v___x_4590_ = v___x_4587_;
goto v_reusejp_4589_;
}
else
{
lean_object* v_reuseFailAlloc_4591_; 
v_reuseFailAlloc_4591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4591_, 0, v_a_4583_);
v___x_4590_ = v_reuseFailAlloc_4591_;
goto v_reusejp_4589_;
}
v_reusejp_4589_:
{
return v___x_4590_;
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
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg___boxed(lean_object* v_x_4602_, lean_object* v_isExporting_4603_, lean_object* v___y_4604_, lean_object* v___y_4605_, lean_object* v___y_4606_, lean_object* v___y_4607_, lean_object* v___y_4608_, lean_object* v___y_4609_, lean_object* v___y_4610_){
_start:
{
uint8_t v_isExporting_boxed_4611_; lean_object* v_res_4612_; 
v_isExporting_boxed_4611_ = lean_unbox(v_isExporting_4603_);
v_res_4612_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg(v_x_4602_, v_isExporting_boxed_4611_, v___y_4604_, v___y_4605_, v___y_4606_, v___y_4607_, v___y_4608_, v___y_4609_);
lean_dec(v___y_4609_);
lean_dec_ref(v___y_4608_);
lean_dec(v___y_4607_);
lean_dec_ref(v___y_4606_);
lean_dec(v___y_4605_);
lean_dec_ref(v___y_4604_);
return v_res_4612_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2___redArg(lean_object* v_x_4613_, uint8_t v_when_4614_, lean_object* v___y_4615_, lean_object* v___y_4616_, lean_object* v___y_4617_, lean_object* v___y_4618_, lean_object* v___y_4619_, lean_object* v___y_4620_){
_start:
{
if (v_when_4614_ == 0)
{
lean_object* v___x_4622_; 
lean_inc(v___y_4620_);
lean_inc_ref(v___y_4619_);
lean_inc(v___y_4618_);
lean_inc_ref(v___y_4617_);
lean_inc(v___y_4616_);
lean_inc_ref(v___y_4615_);
v___x_4622_ = lean_apply_7(v_x_4613_, v___y_4615_, v___y_4616_, v___y_4617_, v___y_4618_, v___y_4619_, v___y_4620_, lean_box(0));
return v___x_4622_;
}
else
{
uint8_t v___x_4623_; lean_object* v___x_4624_; 
v___x_4623_ = 0;
v___x_4624_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg(v_x_4613_, v___x_4623_, v___y_4615_, v___y_4616_, v___y_4617_, v___y_4618_, v___y_4619_, v___y_4620_);
return v___x_4624_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2___redArg___boxed(lean_object* v_x_4625_, lean_object* v_when_4626_, lean_object* v___y_4627_, lean_object* v___y_4628_, lean_object* v___y_4629_, lean_object* v___y_4630_, lean_object* v___y_4631_, lean_object* v___y_4632_, lean_object* v___y_4633_){
_start:
{
uint8_t v_when_boxed_4634_; lean_object* v_res_4635_; 
v_when_boxed_4634_ = lean_unbox(v_when_4626_);
v_res_4635_ = l_Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2___redArg(v_x_4625_, v_when_boxed_4634_, v___y_4627_, v___y_4628_, v___y_4629_, v___y_4630_, v___y_4631_, v___y_4632_);
lean_dec(v___y_4632_);
lean_dec_ref(v___y_4631_);
lean_dec(v___y_4630_);
lean_dec_ref(v___y_4629_);
lean_dec(v___y_4628_);
lean_dec_ref(v___y_4627_);
return v_res_4635_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_letToHave___closed__2(void){
_start:
{
lean_object* v___x_4638_; lean_object* v___x_4639_; 
v___x_4638_ = ((lean_object*)(l_Lean_Meta_Sym_letToHave___closed__1));
v___x_4639_ = l_Lean_stringToMessageData(v___x_4638_);
return v___x_4639_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_letToHave(lean_object* v_e_4640_, lean_object* v_a_4641_, lean_object* v_a_4642_, lean_object* v_a_4643_, lean_object* v_a_4644_, lean_object* v_a_4645_, lean_object* v_a_4646_){
_start:
{
lean_object* v___f_4648_; lean_object* v___f_4649_; lean_object* v___y_4651_; lean_object* v___y_4652_; lean_object* v___y_4653_; lean_object* v___y_4654_; lean_object* v___y_4655_; lean_object* v___y_4656_; uint8_t v___x_4665_; 
v___f_4648_ = ((lean_object*)(l_Lean_Meta_Sym_letToHave___closed__0));
lean_inc_ref(v_e_4640_);
v___f_4649_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_letToHave___lam__2___boxed), 9, 1);
lean_closure_set(v___f_4649_, 0, v_e_4640_);
v___x_4665_ = l_Lean_Expr_hasLooseBVars(v_e_4640_);
lean_dec_ref(v_e_4640_);
if (v___x_4665_ == 0)
{
v___y_4651_ = v_a_4641_;
v___y_4652_ = v_a_4642_;
v___y_4653_ = v_a_4643_;
v___y_4654_ = v_a_4644_;
v___y_4655_ = v_a_4645_;
v___y_4656_ = v_a_4646_;
goto v___jp_4650_;
}
else
{
lean_object* v___x_4666_; lean_object* v___x_4667_; lean_object* v_a_4668_; lean_object* v___x_4670_; uint8_t v_isShared_4671_; uint8_t v_isSharedCheck_4675_; 
lean_dec_ref(v___f_4649_);
v___x_4666_ = lean_obj_once(&l_Lean_Meta_Sym_letToHave___closed__2, &l_Lean_Meta_Sym_letToHave___closed__2_once, _init_l_Lean_Meta_Sym_letToHave___closed__2);
v___x_4667_ = l_Lean_throwError___at___00Lean_Meta_Sym_letToHave_spec__3___redArg(v___x_4666_, v_a_4643_, v_a_4644_, v_a_4645_, v_a_4646_);
v_a_4668_ = lean_ctor_get(v___x_4667_, 0);
v_isSharedCheck_4675_ = !lean_is_exclusive(v___x_4667_);
if (v_isSharedCheck_4675_ == 0)
{
v___x_4670_ = v___x_4667_;
v_isShared_4671_ = v_isSharedCheck_4675_;
goto v_resetjp_4669_;
}
else
{
lean_inc(v_a_4668_);
lean_dec(v___x_4667_);
v___x_4670_ = lean_box(0);
v_isShared_4671_ = v_isSharedCheck_4675_;
goto v_resetjp_4669_;
}
v_resetjp_4669_:
{
lean_object* v___x_4673_; 
if (v_isShared_4671_ == 0)
{
v___x_4673_ = v___x_4670_;
goto v_reusejp_4672_;
}
else
{
lean_object* v_reuseFailAlloc_4674_; 
v_reuseFailAlloc_4674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4674_, 0, v_a_4668_);
v___x_4673_ = v_reuseFailAlloc_4674_;
goto v_reusejp_4672_;
}
v_reusejp_4672_:
{
return v___x_4673_;
}
}
}
v___jp_4650_:
{
uint8_t v___x_4657_; lean_object* v___x_4658_; lean_object* v___f_4659_; uint8_t v___x_4660_; lean_object* v___x_4661_; lean_object* v___x_4662_; uint8_t v___x_4663_; lean_object* v___x_4664_; 
v___x_4657_ = 0;
v___x_4658_ = lean_box(v___x_4657_);
v___f_4659_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_letToHave___lam__5___boxed), 10, 3);
lean_closure_set(v___f_4659_, 0, v___x_4658_);
lean_closure_set(v___f_4659_, 1, v___f_4648_);
lean_closure_set(v___f_4659_, 2, v___f_4649_);
v___x_4660_ = 0;
v___x_4661_ = lean_box(v___x_4660_);
v___x_4662_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_letToHave_spec__1___boxed), 10, 3);
lean_closure_set(v___x_4662_, 0, lean_box(0));
lean_closure_set(v___x_4662_, 1, v___f_4659_);
lean_closure_set(v___x_4662_, 2, v___x_4661_);
v___x_4663_ = 1;
v___x_4664_ = l_Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2___redArg(v___x_4662_, v___x_4663_, v___y_4651_, v___y_4652_, v___y_4653_, v___y_4654_, v___y_4655_, v___y_4656_);
return v___x_4664_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_letToHave___boxed(lean_object* v_e_4676_, lean_object* v_a_4677_, lean_object* v_a_4678_, lean_object* v_a_4679_, lean_object* v_a_4680_, lean_object* v_a_4681_, lean_object* v_a_4682_, lean_object* v_a_4683_){
_start:
{
lean_object* v_res_4684_; 
v_res_4684_ = l_Lean_Meta_Sym_letToHave(v_e_4676_, v_a_4677_, v_a_4678_, v_a_4679_, v_a_4680_, v_a_4681_, v_a_4682_);
lean_dec(v_a_4682_);
lean_dec_ref(v_a_4681_);
lean_dec(v_a_4680_);
lean_dec_ref(v_a_4679_);
lean_dec(v_a_4678_);
lean_dec_ref(v_a_4677_);
return v_res_4684_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2(lean_object* v_00_u03b1_4685_, lean_object* v_x_4686_, uint8_t v_isExporting_4687_, lean_object* v___y_4688_, lean_object* v___y_4689_, lean_object* v___y_4690_, lean_object* v___y_4691_, lean_object* v___y_4692_, lean_object* v___y_4693_){
_start:
{
lean_object* v___x_4695_; 
v___x_4695_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___redArg(v_x_4686_, v_isExporting_4687_, v___y_4688_, v___y_4689_, v___y_4690_, v___y_4691_, v___y_4692_, v___y_4693_);
return v___x_4695_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2___boxed(lean_object* v_00_u03b1_4696_, lean_object* v_x_4697_, lean_object* v_isExporting_4698_, lean_object* v___y_4699_, lean_object* v___y_4700_, lean_object* v___y_4701_, lean_object* v___y_4702_, lean_object* v___y_4703_, lean_object* v___y_4704_, lean_object* v___y_4705_){
_start:
{
uint8_t v_isExporting_boxed_4706_; lean_object* v_res_4707_; 
v_isExporting_boxed_4706_ = lean_unbox(v_isExporting_4698_);
v_res_4707_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2_spec__2(v_00_u03b1_4696_, v_x_4697_, v_isExporting_boxed_4706_, v___y_4699_, v___y_4700_, v___y_4701_, v___y_4702_, v___y_4703_, v___y_4704_);
lean_dec(v___y_4704_);
lean_dec_ref(v___y_4703_);
lean_dec(v___y_4702_);
lean_dec_ref(v___y_4701_);
lean_dec(v___y_4700_);
lean_dec_ref(v___y_4699_);
return v_res_4707_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2(lean_object* v_00_u03b1_4708_, lean_object* v_x_4709_, uint8_t v_when_4710_, lean_object* v___y_4711_, lean_object* v___y_4712_, lean_object* v___y_4713_, lean_object* v___y_4714_, lean_object* v___y_4715_, lean_object* v___y_4716_){
_start:
{
lean_object* v___x_4718_; 
v___x_4718_ = l_Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2___redArg(v_x_4709_, v_when_4710_, v___y_4711_, v___y_4712_, v___y_4713_, v___y_4714_, v___y_4715_, v___y_4716_);
return v___x_4718_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2___boxed(lean_object* v_00_u03b1_4719_, lean_object* v_x_4720_, lean_object* v_when_4721_, lean_object* v___y_4722_, lean_object* v___y_4723_, lean_object* v___y_4724_, lean_object* v___y_4725_, lean_object* v___y_4726_, lean_object* v___y_4727_, lean_object* v___y_4728_){
_start:
{
uint8_t v_when_boxed_4729_; lean_object* v_res_4730_; 
v_when_boxed_4729_ = lean_unbox(v_when_4721_);
v_res_4730_ = l_Lean_withoutExporting___at___00Lean_Meta_Sym_letToHave_spec__2(v_00_u03b1_4719_, v_x_4720_, v_when_boxed_4729_, v___y_4722_, v___y_4723_, v___y_4724_, v___y_4725_, v___y_4726_, v___y_4727_);
lean_dec(v___y_4727_);
lean_dec_ref(v___y_4726_);
lean_dec(v___y_4725_);
lean_dec_ref(v___y_4724_);
lean_dec(v___y_4723_);
lean_dec_ref(v___y_4722_);
return v_res_4730_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_letToHave_spec__3(lean_object* v_00_u03b1_4731_, lean_object* v_msg_4732_, lean_object* v___y_4733_, lean_object* v___y_4734_, lean_object* v___y_4735_, lean_object* v___y_4736_, lean_object* v___y_4737_, lean_object* v___y_4738_){
_start:
{
lean_object* v___x_4740_; 
v___x_4740_ = l_Lean_throwError___at___00Lean_Meta_Sym_letToHave_spec__3___redArg(v_msg_4732_, v___y_4735_, v___y_4736_, v___y_4737_, v___y_4738_);
return v___x_4740_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_letToHave_spec__3___boxed(lean_object* v_00_u03b1_4741_, lean_object* v_msg_4742_, lean_object* v___y_4743_, lean_object* v___y_4744_, lean_object* v___y_4745_, lean_object* v___y_4746_, lean_object* v___y_4747_, lean_object* v___y_4748_, lean_object* v___y_4749_){
_start:
{
lean_object* v_res_4750_; 
v_res_4750_ = l_Lean_throwError___at___00Lean_Meta_Sym_letToHave_spec__3(v_00_u03b1_4741_, v_msg_4742_, v___y_4743_, v___y_4744_, v___y_4745_, v___y_4746_, v___y_4747_, v___y_4748_);
lean_dec(v___y_4748_);
lean_dec_ref(v___y_4747_);
lean_dec(v___y_4746_);
lean_dec_ref(v___y_4745_);
lean_dec(v___y_4744_);
lean_dec_ref(v___y_4743_);
return v_res_4750_;
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
