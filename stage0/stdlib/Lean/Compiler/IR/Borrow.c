// Lean compiler output
// Module: Lean.Compiler.IR.Borrow
// Imports: Lean.Compiler.ExportAttr Lean.Compiler.IR.CompilerM Lean.Compiler.IR.NormIds
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
LEAN_EXPORT uint8_t l_Lean_IR_Borrow_OwnedSet_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_ApplyParamMap_visitFnBody(lean_object*, lean_object*, lean_object*);
lean_object* lean_format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_Borrow_InitParamMap_visitFnBody_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_Borrow_OwnedSet_insert_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_ownArgsUsingParams___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_Borrow_OwnedSet_insert_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RBNode_insert___at___Lean_IR_mkIndexSet_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_preserveTailCall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_Borrow_instToFormatParamMap___closed__0;
static lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Lean_IR_Borrow_ParamMap_fmt_spec__0___closed__4;
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_getParamInfo(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_markModified(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_forM_loop___at___Lean_IR_Borrow_ownParamsUsingArgs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_inferBorrow___redArg(lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_Borrow_infer___closed__0;
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_InitParamMap_visitDecls___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_Borrow_OwnedSet_insert_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_Borrow_InitParamMap_visitFnBody_spec__0___redArg(lean_object*, lean_object*);
static lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Lean_IR_Borrow_ParamMap_fmt_spec__0___closed__2;
lean_object* lean_ir_find_env_decl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_markModified___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_IR_Borrow_mkInitParamMap___closed__0;
static lean_object* l_Lean_IR_Borrow_mkInitParamMap___closed__2;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_Borrow_InitParamMap_visitFnBody_spec__1_spec__1_spec__1___redArg(lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_Borrow_ApplyParamMap_visitDecls_spec__0___closed__1;
uint64_t lean_uint64_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_Borrow_ownArgsIfParam_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_ApplyParamMap_visitDecls___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_updateParamMap(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_ownArgsUsingParams(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_Borrow_InitParamMap_initBorrow_spec__0(size_t, size_t, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_Borrow_ApplyParamMap_visitDecls_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT uint64_t l_Lean_IR_Borrow_OwnedSet_getHash(lean_object*);
static lean_object* l_Lean_IR_Borrow_ParamMap_fmt___closed__4;
static lean_object* l_Lean_IR_Borrow_ParamMap_fmt___closed__1;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_Borrow_ApplyParamMap_visitFnBody_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_Borrow_ApplyParamMap_visitFnBody_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_IR_Borrow_ApplyParamMap_visitFnBody_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_instToStringParamMap___lam__0___boxed(lean_object*);
static lean_object* l_Lean_IR_Borrow_mkInitParamMap___closed__3;
static lean_object* l_panic___at___Lean_IR_Borrow_getParamInfo_spec__0___closed__5;
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_ParamMap_beqKey____x40_Lean_Compiler_IR_Borrow___hyg_214____boxed(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_ParamMap_fmt___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_Borrow_InitParamMap_visitFnBody_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_inferBorrow(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_Borrow_OwnedSet_instHashableKey___closed__0;
static lean_object* l_Lean_IR_Borrow_infer___closed__1;
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_Borrow_ownArgs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_Borrow_InitParamMap_visitFnBody_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_Borrow_InitParamMap_visitFnBody_spec__5(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_FnBody_isTerminal(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_Borrow_ParamMap_fmt_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_updateParamSet___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_IR_Borrow_InitParamMap_visitFnBody_spec__4___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at___Lean_IR_Borrow_getParamInfo_spec__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_ownArgs(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_Borrow_collectFnBody_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_whileModifing(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_preserveTailCall___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_Borrow_getParamInfo___closed__1;
extern lean_object* l_Lean_IR_instInhabitedParam;
LEAN_EXPORT lean_object* l_Nat_forM_loop___at___Lean_IR_Borrow_ownArgsUsingParams_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_forM_loop___at___Lean_IR_Borrow_ownParamsUsingArgs_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_mkInitParamMap___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_Borrow_ParamMap_beqKey____x40_Lean_Compiler_IR_Borrow___hyg_214_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_Borrow_InitParamMap_visitDecls_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_forM_loop___at___Lean_IR_Borrow_ownArgsUsingParams_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_IR_Borrow_InitParamMap_visitFnBody_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_isOwned(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_Borrow_ownArgs_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at___Lean_IR_Borrow_getParamInfo_spec__0___closed__3;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_Borrow_ApplyParamMap_visitDecls_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* l_Nat_forM_loop___at___Lean_IR_Borrow_ownArgsUsingParams_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_Borrow_ParamMap_instBEqKey___closed__0;
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_Borrow_collectFnBody_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Lean_IR_Borrow_ParamMap_getHash(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_IR_Borrow_OwnedSet_insert_spec__4___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at___Lean_IR_Borrow_getParamInfo_spec__0___closed__4;
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_OwnedSet_insert(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_Borrow_updateParamSet_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isExport(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_isOwned___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Lean_IR_Borrow_ParamMap_fmt_spec__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_ownArgsIfParam(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_ParamMap_fmt___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_Borrow_OwnedSet_insert_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_collectDecls___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_ownParamsUsingArgs(lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_ownParamsUsingArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Array_empty(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_getCurrFn___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_Borrow_InitParamMap_visitFnBody_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_inferBorrow___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_ApplyParamMap_visitFnBody___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_Borrow_InitParamMap_visitDecls_spec__0___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_applyParamMap___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Lean_IR_Borrow_ParamMap_fmt_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_InitParamMap_initBorrowIfNotExported___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_InitParamMap_initBorrowIfNotExported(uint8_t, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_instInhabitedForall___redArg___lam__0___boxed(lean_object*, lean_object*);
uint8_t l_Lean_IR_IRType_isObj(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_instToFormatParamMap;
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_markModified___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_OwnedSet_getHash___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_Borrow_OwnedSet_contains(lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_ownVar___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_ParamMap_getHash___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_InitParamMap_initBorrow(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_ownArgsIfParam___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_ownArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_Borrow_ParamMap_fmt___closed__0;
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_Borrow_InitParamMap_initBorrow_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_Borrow_OwnedSet_insert_spec__1___redArg(lean_object*);
lean_object* l_StateT_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_forM_loop___at___Lean_IR_Borrow_ownParamsUsingArgs_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_Borrow_mkInitParamMap___closed__4;
lean_object* l_panic___at___Lean_IR_Decl_updateBody_x21_spec__0(lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_Borrow_ParamMap_fmt___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_Borrow_OwnedSet_insert_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_updateParamMap___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_Borrow_ApplyParamMap_visitFnBody___closed__3;
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_ParamMap_instHashableKey;
static lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Lean_IR_Borrow_ParamMap_fmt_spec__0___closed__1;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_Borrow_InitParamMap_visitDecls_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_OwnedSet_beq___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_IR_Borrow_ApplyParamMap_visitFnBody_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_InitParamMap_visitDecls(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_InitParamMap_visitFnBody(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_IR_FnBody_setBody(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_ParamMap_fmt(lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_Borrow_OwnedSet_insert_spec__1_spec__1_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_forM_loop___at___Lean_IR_Borrow_ownArgsUsingParams_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_Borrow_InitParamMap_visitFnBody_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_instToStringParamMap___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_Borrow_updateParamMap_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_Borrow_collectDecls_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_Borrow_ParamMap_fmt_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_applyParamMap(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_collectDecl(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_Borrow_ApplyParamMap_visitFnBody___closed__2;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_ownArgs___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at___Lean_IR_Borrow_getParamInfo_spec__0___closed__2;
static lean_object* l_Lean_IR_Borrow_OwnedSet_instBEqKey___closed__0;
static lean_object* l_panic___at___Lean_IR_Borrow_getParamInfo_spec__0___closed__7;
lean_object* l_Lean_IR_formatArray___at___Lean_IR_formatParams_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_IR_Borrow_OwnedSet_insert_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_collectDecls___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Name_hash___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_mkInitParamMap(lean_object*, lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_collectDecls(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
static lean_object* l_Lean_IR_Borrow_ApplyParamMap_visitFnBody___closed__1;
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_ParamMap_instBEqKey;
static lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_Borrow_ApplyParamMap_visitDecls_spec__0___closed__0;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_IR_Borrow_ApplyParamMap_visitFnBody_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_OwnedSet_instHashableKey;
size_t lean_usize_sub(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_collectFnBody(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_Borrow_getParamInfo___closed__0;
static lean_object* l_panic___at___Lean_IR_Borrow_getParamInfo_spec__0___closed__6;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_Borrow_updateParamMap_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_Borrow_mkInitParamMap___closed__1;
size_t lean_usize_add(size_t, size_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_Borrow_OwnedSet_insert_spec__0___boxed(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_Borrow_OwnedSet_insert_spec__1_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_ownVar(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_Borrow_OwnedSet_insert_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_Borrow_collectDecls_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_forM_loop___at___Lean_IR_Borrow_ownParamsUsingArgs_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_Borrow_InitParamMap_visitFnBody_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_IR_Borrow_ApplyParamMap_visitFnBody_spec__1(lean_object*);
static lean_object* l_Lean_IR_Borrow_getParamInfo___closed__2;
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_instToStringParamMap;
lean_object* l_Lean_IR_getEnv___redArg(lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_Borrow_InitParamMap_visitDecls_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
static lean_object* l_panic___at___Lean_IR_Borrow_getParamInfo_spec__0___closed__0;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_IR_Borrow_getParamInfo_spec__0(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_OwnedSet_instBEqKey;
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_updateParamSet(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_Borrow_ownArgsIfParam_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_infer(lean_object*, lean_object*);
static lean_object* l_Lean_IR_Borrow_ParamMap_fmt___closed__3;
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_OwnedSet_contains___boxed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_getCurrFn(lean_object*, lean_object*);
static lean_object* l_Lean_IR_Borrow_ParamMap_fmt___closed__2;
lean_object* l_StateT_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_Borrow_updateParamSet_spec__0(lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lean_IR_Borrow_ParamMap_instHashableKey___closed__0;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_IR_Borrow_ApplyParamMap_visitFnBody_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Lean_IR_Borrow_ParamMap_fmt_spec__0___closed__3;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_Borrow_InitParamMap_visitFnBody_spec__1_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_collectExpr(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_Borrow_InitParamMap_visitFnBody_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_ownArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_Borrow_ApplyParamMap_visitFnBody___closed__0;
lean_object* l_Lean_RBNode_findCore___at___Lean_IR_UniqueIds_checkId_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
lean_object* l_StateT_pure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_Borrow_InitParamMap_visitFnBody_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_ApplyParamMap_visitDecls(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_Borrow_OwnedSet_beq(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_name_eq(x_3, x_5);
if (x_7 == 0)
{
return x_7;
}
else
{
uint8_t x_8; 
x_8 = lean_nat_dec_eq(x_4, x_6);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_OwnedSet_beq___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_IR_Borrow_OwnedSet_beq(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_IR_Borrow_OwnedSet_instBEqKey___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_IR_Borrow_OwnedSet_beq___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_Borrow_OwnedSet_instBEqKey() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_IR_Borrow_OwnedSet_instBEqKey___closed__0;
return x_1;
}
}
LEAN_EXPORT uint64_t l_Lean_IR_Borrow_OwnedSet_getHash(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint64_t x_4; uint64_t x_5; uint64_t x_6; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = l_Lean_Name_hash___override(x_2);
x_5 = lean_uint64_of_nat(x_3);
x_6 = lean_uint64_mix_hash(x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_OwnedSet_getHash___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_Lean_IR_Borrow_OwnedSet_getHash(x_1);
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_Borrow_OwnedSet_instHashableKey___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_IR_Borrow_OwnedSet_getHash___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_Borrow_OwnedSet_instHashableKey() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_IR_Borrow_OwnedSet_instHashableKey___closed__0;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_Borrow_OwnedSet_insert_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_box(0);
x_4 = lean_unbox(x_3);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 2);
x_7 = l_Lean_IR_Borrow_OwnedSet_beq(x_5, x_1);
if (x_7 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
return x_7;
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_Borrow_OwnedSet_insert_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_Borrow_OwnedSet_insert_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_Borrow_OwnedSet_insert_spec__1_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
x_7 = l_Lean_IR_Borrow_OwnedSet_getHash(x_4);
x_8 = 32;
x_9 = lean_uint64_shift_right(x_7, x_8);
x_10 = lean_uint64_xor(x_7, x_9);
x_11 = 16;
x_12 = lean_uint64_shift_right(x_10, x_11);
x_13 = lean_uint64_xor(x_10, x_12);
x_14 = lean_uint64_to_usize(x_13);
x_15 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_16 = 1;
x_17 = lean_usize_sub(x_15, x_16);
x_18 = lean_usize_land(x_14, x_17);
x_19 = lean_array_uget(x_1, x_18);
lean_ctor_set(x_2, 2, x_19);
x_20 = lean_array_uset(x_1, x_18, x_2);
x_1 = x_20;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint64_t x_26; uint64_t x_27; uint64_t x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; size_t x_33; size_t x_34; size_t x_35; size_t x_36; size_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_22 = lean_ctor_get(x_2, 0);
x_23 = lean_ctor_get(x_2, 1);
x_24 = lean_ctor_get(x_2, 2);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_2);
x_25 = lean_array_get_size(x_1);
x_26 = l_Lean_IR_Borrow_OwnedSet_getHash(x_22);
x_27 = 32;
x_28 = lean_uint64_shift_right(x_26, x_27);
x_29 = lean_uint64_xor(x_26, x_28);
x_30 = 16;
x_31 = lean_uint64_shift_right(x_29, x_30);
x_32 = lean_uint64_xor(x_29, x_31);
x_33 = lean_uint64_to_usize(x_32);
x_34 = lean_usize_of_nat(x_25);
lean_dec(x_25);
x_35 = 1;
x_36 = lean_usize_sub(x_34, x_35);
x_37 = lean_usize_land(x_33, x_36);
x_38 = lean_array_uget(x_1, x_37);
x_39 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_39, 0, x_22);
lean_ctor_set(x_39, 1, x_23);
lean_ctor_set(x_39, 2, x_38);
x_40 = lean_array_uset(x_1, x_37, x_39);
x_1 = x_40;
x_2 = x_24;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_Borrow_OwnedSet_insert_spec__1_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_Borrow_OwnedSet_insert_spec__1_spec__1_spec__1___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_Borrow_OwnedSet_insert_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_1, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_box(0);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_Borrow_OwnedSet_insert_spec__1_spec__1_spec__1___redArg(x_3, x_6);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_1, x_10);
lean_dec(x_1);
x_1 = x_11;
x_2 = x_8;
x_3 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_Borrow_OwnedSet_insert_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_Borrow_OwnedSet_insert_spec__1_spec__1___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_Borrow_OwnedSet_insert_spec__1___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(2u);
x_4 = lean_nat_mul(x_2, x_3);
lean_dec(x_2);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_box(0);
x_7 = lean_mk_array(x_4, x_6);
x_8 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_Borrow_OwnedSet_insert_spec__1_spec__1___redArg(x_5, x_1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_Borrow_OwnedSet_insert_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_Borrow_OwnedSet_insert_spec__1___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_IR_Borrow_OwnedSet_insert_spec__4___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_3, 2);
x_8 = l_Lean_IR_Borrow_OwnedSet_beq(x_5, x_1);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_IR_Borrow_OwnedSet_insert_spec__4___redArg(x_1, x_2, x_7);
lean_ctor_set(x_3, 2, x_9);
return x_3;
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 1);
x_12 = lean_ctor_get(x_3, 2);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_3);
x_13 = l_Lean_IR_Borrow_OwnedSet_beq(x_10, x_1);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_IR_Borrow_OwnedSet_insert_spec__4___redArg(x_1, x_2, x_12);
x_15 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_11);
lean_ctor_set(x_15, 2, x_14);
return x_15;
}
else
{
lean_object* x_16; 
lean_dec(x_11);
lean_dec(x_10);
x_16 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_2);
lean_ctor_set(x_16, 2, x_12);
return x_16;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_IR_Borrow_OwnedSet_insert_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_IR_Borrow_OwnedSet_insert_spec__4___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_OwnedSet_insert(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; size_t x_15; size_t x_16; size_t x_17; size_t x_18; size_t x_19; lean_object* x_20; uint8_t x_21; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_box(0);
x_7 = lean_array_get_size(x_5);
x_8 = l_Lean_IR_Borrow_OwnedSet_getHash(x_2);
x_9 = 32;
x_10 = lean_uint64_shift_right(x_8, x_9);
x_11 = lean_uint64_xor(x_8, x_10);
x_12 = 16;
x_13 = lean_uint64_shift_right(x_11, x_12);
x_14 = lean_uint64_xor(x_11, x_13);
x_15 = lean_uint64_to_usize(x_14);
x_16 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_17 = 1;
x_18 = lean_usize_sub(x_16, x_17);
x_19 = lean_usize_land(x_15, x_18);
x_20 = lean_array_uget(x_5, x_19);
x_21 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_Borrow_OwnedSet_insert_spec__0___redArg(x_2, x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_add(x_4, x_22);
lean_dec(x_4);
x_24 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_24, 0, x_2);
lean_ctor_set(x_24, 1, x_6);
lean_ctor_set(x_24, 2, x_20);
x_25 = lean_array_uset(x_5, x_19, x_24);
x_26 = lean_unsigned_to_nat(4u);
x_27 = lean_nat_mul(x_23, x_26);
x_28 = lean_unsigned_to_nat(3u);
x_29 = lean_nat_div(x_27, x_28);
lean_dec(x_27);
x_30 = lean_array_get_size(x_25);
x_31 = lean_nat_dec_le(x_29, x_30);
lean_dec(x_30);
lean_dec(x_29);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_Borrow_OwnedSet_insert_spec__1___redArg(x_25);
lean_ctor_set(x_1, 1, x_32);
lean_ctor_set(x_1, 0, x_23);
return x_1;
}
else
{
lean_ctor_set(x_1, 1, x_25);
lean_ctor_set(x_1, 0, x_23);
return x_1;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_box(0);
x_34 = lean_array_uset(x_5, x_19, x_33);
x_35 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_IR_Borrow_OwnedSet_insert_spec__4___redArg(x_2, x_6, x_20);
x_36 = lean_array_uset(x_34, x_19, x_35);
lean_ctor_set(x_1, 1, x_36);
return x_1;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint64_t x_41; uint64_t x_42; uint64_t x_43; uint64_t x_44; uint64_t x_45; uint64_t x_46; uint64_t x_47; size_t x_48; size_t x_49; size_t x_50; size_t x_51; size_t x_52; lean_object* x_53; uint8_t x_54; 
x_37 = lean_ctor_get(x_1, 0);
x_38 = lean_ctor_get(x_1, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_1);
x_39 = lean_box(0);
x_40 = lean_array_get_size(x_38);
x_41 = l_Lean_IR_Borrow_OwnedSet_getHash(x_2);
x_42 = 32;
x_43 = lean_uint64_shift_right(x_41, x_42);
x_44 = lean_uint64_xor(x_41, x_43);
x_45 = 16;
x_46 = lean_uint64_shift_right(x_44, x_45);
x_47 = lean_uint64_xor(x_44, x_46);
x_48 = lean_uint64_to_usize(x_47);
x_49 = lean_usize_of_nat(x_40);
lean_dec(x_40);
x_50 = 1;
x_51 = lean_usize_sub(x_49, x_50);
x_52 = lean_usize_land(x_48, x_51);
x_53 = lean_array_uget(x_38, x_52);
x_54 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_Borrow_OwnedSet_insert_spec__0___redArg(x_2, x_53);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_55 = lean_unsigned_to_nat(1u);
x_56 = lean_nat_add(x_37, x_55);
lean_dec(x_37);
x_57 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_57, 0, x_2);
lean_ctor_set(x_57, 1, x_39);
lean_ctor_set(x_57, 2, x_53);
x_58 = lean_array_uset(x_38, x_52, x_57);
x_59 = lean_unsigned_to_nat(4u);
x_60 = lean_nat_mul(x_56, x_59);
x_61 = lean_unsigned_to_nat(3u);
x_62 = lean_nat_div(x_60, x_61);
lean_dec(x_60);
x_63 = lean_array_get_size(x_58);
x_64 = lean_nat_dec_le(x_62, x_63);
lean_dec(x_63);
lean_dec(x_62);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; 
x_65 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_Borrow_OwnedSet_insert_spec__1___redArg(x_58);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_56);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
else
{
lean_object* x_67; 
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_56);
lean_ctor_set(x_67, 1, x_58);
return x_67;
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_68 = lean_box(0);
x_69 = lean_array_uset(x_38, x_52, x_68);
x_70 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_IR_Borrow_OwnedSet_insert_spec__4___redArg(x_2, x_39, x_53);
x_71 = lean_array_uset(x_69, x_52, x_70);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_37);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_Borrow_OwnedSet_insert_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_Borrow_OwnedSet_insert_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_Borrow_OwnedSet_insert_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_Borrow_OwnedSet_insert_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_Borrow_OwnedSet_contains(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint64_t x_5; uint64_t x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; size_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; lean_object* x_17; uint8_t x_18; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Lean_IR_Borrow_OwnedSet_getHash(x_2);
x_6 = 32;
x_7 = lean_uint64_shift_right(x_5, x_6);
x_8 = lean_uint64_xor(x_5, x_7);
x_9 = 16;
x_10 = lean_uint64_shift_right(x_8, x_9);
x_11 = lean_uint64_xor(x_8, x_10);
x_12 = lean_uint64_to_usize(x_11);
x_13 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_14 = 1;
x_15 = lean_usize_sub(x_13, x_14);
x_16 = lean_usize_land(x_12, x_15);
x_17 = lean_array_uget(x_3, x_16);
x_18 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_Borrow_OwnedSet_insert_spec__0___redArg(x_2, x_17);
lean_dec(x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_OwnedSet_contains___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_IR_Borrow_OwnedSet_contains(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_Borrow_ParamMap_beqKey____x40_Lean_Compiler_IR_Borrow___hyg_214_(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_name_eq(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_box(0);
x_7 = lean_unbox(x_6);
return x_7;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_box(0);
x_9 = lean_unbox(x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 1);
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_ctor_get(x_2, 1);
x_14 = lean_name_eq(x_10, x_12);
if (x_14 == 0)
{
return x_14;
}
else
{
uint8_t x_15; 
x_15 = lean_nat_dec_eq(x_11, x_13);
return x_15;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_ParamMap_beqKey____x40_Lean_Compiler_IR_Borrow___hyg_214____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_IR_Borrow_ParamMap_beqKey____x40_Lean_Compiler_IR_Borrow___hyg_214_(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_IR_Borrow_ParamMap_instBEqKey___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_IR_Borrow_ParamMap_beqKey____x40_Lean_Compiler_IR_Borrow___hyg_214____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_Borrow_ParamMap_instBEqKey() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_IR_Borrow_ParamMap_instBEqKey___closed__0;
return x_1;
}
}
LEAN_EXPORT uint64_t l_Lean_IR_Borrow_ParamMap_getHash(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; uint64_t x_3; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = l_Lean_Name_hash___override(x_2);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint64_t x_6; uint64_t x_7; uint64_t x_8; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = l_Lean_Name_hash___override(x_4);
x_7 = lean_uint64_of_nat(x_5);
x_8 = lean_uint64_mix_hash(x_6, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_ParamMap_getHash___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_Lean_IR_Borrow_ParamMap_getHash(x_1);
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_Borrow_ParamMap_instHashableKey___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_IR_Borrow_ParamMap_getHash___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_Borrow_ParamMap_instHashableKey() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_IR_Borrow_ParamMap_instHashableKey___closed__0;
return x_1;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___Lean_IR_Borrow_ParamMap_fmt_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" -> ", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___Lean_IR_Borrow_ParamMap_fmt_spec__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Lean_IR_Borrow_ParamMap_fmt_spec__0___closed__0;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___Lean_IR_Borrow_ParamMap_fmt_spec__0___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(":", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___Lean_IR_Borrow_ParamMap_fmt_spec__0___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Lean_IR_Borrow_ParamMap_fmt_spec__0___closed__2;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___Lean_IR_Borrow_ParamMap_fmt_spec__0___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("block_", 6, 6);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Lean_IR_Borrow_ParamMap_fmt_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 2);
lean_inc(x_7);
lean_dec(x_4);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_5);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_5, 0);
x_20 = lean_box(1);
x_21 = lean_unbox(x_20);
lean_inc(x_1);
x_22 = l_Lean_Name_toString(x_19, x_21, x_1);
lean_ctor_set_tag(x_5, 3);
lean_ctor_set(x_5, 0, x_22);
x_8 = x_5;
goto block_17;
}
else
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_5, 0);
lean_inc(x_23);
lean_dec(x_5);
x_24 = lean_box(1);
x_25 = lean_unbox(x_24);
lean_inc(x_1);
x_26 = l_Lean_Name_toString(x_23, x_25, x_1);
x_27 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_8 = x_27;
goto block_17;
}
}
else
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_5);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_29 = lean_ctor_get(x_5, 0);
x_30 = lean_ctor_get(x_5, 1);
x_31 = lean_box(1);
x_32 = lean_unbox(x_31);
lean_inc(x_2);
x_33 = l_Lean_Name_toString(x_29, x_32, x_2);
x_34 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_34, 0, x_33);
x_35 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Lean_IR_Borrow_ParamMap_fmt_spec__0___closed__3;
lean_ctor_set_tag(x_5, 5);
lean_ctor_set(x_5, 1, x_35);
lean_ctor_set(x_5, 0, x_34);
x_36 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Lean_IR_Borrow_ParamMap_fmt_spec__0___closed__4;
x_37 = l_Nat_reprFast(x_30);
x_38 = lean_string_append(x_36, x_37);
lean_dec(x_37);
x_39 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_39, 0, x_38);
x_40 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_40, 0, x_5);
lean_ctor_set(x_40, 1, x_39);
x_8 = x_40;
goto block_17;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_41 = lean_ctor_get(x_5, 0);
x_42 = lean_ctor_get(x_5, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_5);
x_43 = lean_box(1);
x_44 = lean_unbox(x_43);
lean_inc(x_2);
x_45 = l_Lean_Name_toString(x_41, x_44, x_2);
x_46 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_46, 0, x_45);
x_47 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Lean_IR_Borrow_ParamMap_fmt_spec__0___closed__3;
x_48 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
x_49 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Lean_IR_Borrow_ParamMap_fmt_spec__0___closed__4;
x_50 = l_Nat_reprFast(x_42);
x_51 = lean_string_append(x_49, x_50);
lean_dec(x_50);
x_52 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_52, 0, x_51);
x_53 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_53, 0, x_48);
lean_ctor_set(x_53, 1, x_52);
x_8 = x_53;
goto block_17;
}
}
block_17:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_box(1);
x_10 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_10, 0, x_3);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_8);
x_12 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Lean_IR_Borrow_ParamMap_fmt_spec__0___closed__1;
x_13 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = l_Lean_IR_formatArray___at___Lean_IR_formatParams_spec__0(x_6);
lean_dec(x_6);
x_15 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_3 = x_15;
x_4 = x_7;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_Borrow_ParamMap_fmt_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_4, x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; 
x_8 = lean_array_uget(x_3, x_4);
lean_inc(x_2);
lean_inc(x_1);
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Lean_IR_Borrow_ParamMap_fmt_spec__0(x_1, x_2, x_6, x_8);
x_10 = 1;
x_11 = lean_usize_add(x_4, x_10);
x_4 = x_11;
x_6 = x_9;
goto _start;
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
}
LEAN_EXPORT uint8_t l_Lean_IR_Borrow_ParamMap_fmt___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(0);
x_3 = lean_unbox(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_Borrow_ParamMap_fmt___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("{", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_Borrow_ParamMap_fmt___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_Borrow_ParamMap_fmt___closed__0;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_Borrow_ParamMap_fmt___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_Borrow_ParamMap_fmt___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("}", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_Borrow_ParamMap_fmt___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_Borrow_ParamMap_fmt___closed__3;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_ParamMap_fmt(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_ctor_get(x_1, 1);
x_11 = lean_box(0);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_array_get_size(x_10);
x_14 = lean_nat_dec_lt(x_12, x_13);
if (x_14 == 0)
{
lean_dec(x_13);
x_2 = x_11;
goto block_9;
}
else
{
uint8_t x_15; 
x_15 = lean_nat_dec_le(x_13, x_13);
if (x_15 == 0)
{
lean_dec(x_13);
x_2 = x_11;
goto block_9;
}
else
{
lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; 
x_16 = lean_alloc_closure((void*)(l_Lean_IR_Borrow_ParamMap_fmt___lam__0___boxed), 1, 0);
x_17 = 0;
x_18 = lean_usize_of_nat(x_13);
lean_dec(x_13);
lean_inc(x_16);
x_19 = l_Array_foldlMUnsafe_fold___at___Lean_IR_Borrow_ParamMap_fmt_spec__1(x_16, x_16, x_10, x_17, x_18, x_11);
x_2 = x_19;
goto block_9;
}
}
block_9:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = l_Lean_IR_Borrow_ParamMap_fmt___closed__1;
x_4 = l_Lean_IR_Borrow_ParamMap_fmt___closed__2;
x_5 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
x_6 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_5);
x_7 = l_Lean_IR_Borrow_ParamMap_fmt___closed__4;
x_8 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_Borrow_ParamMap_fmt_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_Array_foldlMUnsafe_fold___at___Lean_IR_Borrow_ParamMap_fmt_spec__1(x_1, x_2, x_3, x_7, x_8, x_6);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_ParamMap_fmt___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_IR_Borrow_ParamMap_fmt___lam__0(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_ParamMap_fmt___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_IR_Borrow_ParamMap_fmt(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_Borrow_instToFormatParamMap___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_IR_Borrow_ParamMap_fmt___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_Borrow_instToFormatParamMap() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_IR_Borrow_instToFormatParamMap___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_instToStringParamMap___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_IR_Borrow_ParamMap_fmt(x_1);
x_3 = lean_unsigned_to_nat(120u);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_format_pretty(x_2, x_3, x_4, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_IR_Borrow_instToStringParamMap() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_IR_Borrow_instToStringParamMap___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_instToStringParamMap___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_IR_Borrow_instToStringParamMap___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_Borrow_InitParamMap_initBorrow_spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; size_t x_11; size_t x_12; lean_object* x_13; 
x_7 = lean_ctor_get(x_5, 1);
x_8 = lean_box(0);
x_9 = lean_array_uset(x_3, x_2, x_8);
x_10 = l_Lean_IR_IRType_isObj(x_7);
lean_ctor_set_uint8(x_5, sizeof(void*)*2, x_10);
x_11 = 1;
x_12 = lean_usize_add(x_2, x_11);
x_13 = lean_array_uset(x_9, x_2, x_5);
x_2 = x_12;
x_3 = x_13;
goto _start;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; size_t x_21; size_t x_22; lean_object* x_23; 
x_15 = lean_ctor_get(x_5, 0);
x_16 = lean_ctor_get(x_5, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_5);
x_17 = lean_box(0);
x_18 = lean_array_uset(x_3, x_2, x_17);
x_19 = l_Lean_IR_IRType_isObj(x_16);
x_20 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_20, 0, x_15);
lean_ctor_set(x_20, 1, x_16);
lean_ctor_set_uint8(x_20, sizeof(void*)*2, x_19);
x_21 = 1;
x_22 = lean_usize_add(x_2, x_21);
x_23 = lean_array_uset(x_18, x_2, x_20);
x_2 = x_22;
x_3 = x_23;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_InitParamMap_initBorrow(lean_object* x_1) {
_start:
{
size_t x_2; size_t x_3; lean_object* x_4; 
x_2 = lean_array_size(x_1);
x_3 = 0;
x_4 = l_Array_mapMUnsafe_map___at___Lean_IR_Borrow_InitParamMap_initBorrow_spec__0(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_Borrow_InitParamMap_initBorrow_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___Lean_IR_Borrow_InitParamMap_initBorrow_spec__0(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_InitParamMap_initBorrowIfNotExported(uint8_t x_1, lean_object* x_2) {
_start:
{
if (x_1 == 0)
{
lean_object* x_3; 
x_3 = l_Lean_IR_Borrow_InitParamMap_initBorrow(x_2);
return x_3;
}
else
{
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_InitParamMap_initBorrowIfNotExported___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lean_IR_Borrow_InitParamMap_initBorrowIfNotExported(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_Borrow_InitParamMap_visitFnBody_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_box(0);
x_4 = lean_unbox(x_3);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 2);
x_7 = l_Lean_IR_Borrow_ParamMap_beqKey____x40_Lean_Compiler_IR_Borrow___hyg_214_(x_5, x_1);
if (x_7 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
return x_7;
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_Borrow_InitParamMap_visitFnBody_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_Borrow_InitParamMap_visitFnBody_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_Borrow_InitParamMap_visitFnBody_spec__1_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
x_7 = l_Lean_IR_Borrow_ParamMap_getHash(x_4);
x_8 = 32;
x_9 = lean_uint64_shift_right(x_7, x_8);
x_10 = lean_uint64_xor(x_7, x_9);
x_11 = 16;
x_12 = lean_uint64_shift_right(x_10, x_11);
x_13 = lean_uint64_xor(x_10, x_12);
x_14 = lean_uint64_to_usize(x_13);
x_15 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_16 = 1;
x_17 = lean_usize_sub(x_15, x_16);
x_18 = lean_usize_land(x_14, x_17);
x_19 = lean_array_uget(x_1, x_18);
lean_ctor_set(x_2, 2, x_19);
x_20 = lean_array_uset(x_1, x_18, x_2);
x_1 = x_20;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint64_t x_26; uint64_t x_27; uint64_t x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; size_t x_33; size_t x_34; size_t x_35; size_t x_36; size_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_22 = lean_ctor_get(x_2, 0);
x_23 = lean_ctor_get(x_2, 1);
x_24 = lean_ctor_get(x_2, 2);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_2);
x_25 = lean_array_get_size(x_1);
x_26 = l_Lean_IR_Borrow_ParamMap_getHash(x_22);
x_27 = 32;
x_28 = lean_uint64_shift_right(x_26, x_27);
x_29 = lean_uint64_xor(x_26, x_28);
x_30 = 16;
x_31 = lean_uint64_shift_right(x_29, x_30);
x_32 = lean_uint64_xor(x_29, x_31);
x_33 = lean_uint64_to_usize(x_32);
x_34 = lean_usize_of_nat(x_25);
lean_dec(x_25);
x_35 = 1;
x_36 = lean_usize_sub(x_34, x_35);
x_37 = lean_usize_land(x_33, x_36);
x_38 = lean_array_uget(x_1, x_37);
x_39 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_39, 0, x_22);
lean_ctor_set(x_39, 1, x_23);
lean_ctor_set(x_39, 2, x_38);
x_40 = lean_array_uset(x_1, x_37, x_39);
x_1 = x_40;
x_2 = x_24;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_Borrow_InitParamMap_visitFnBody_spec__1_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_Borrow_InitParamMap_visitFnBody_spec__1_spec__1_spec__1___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_Borrow_InitParamMap_visitFnBody_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_1, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_box(0);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_Borrow_InitParamMap_visitFnBody_spec__1_spec__1_spec__1___redArg(x_3, x_6);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_1, x_10);
lean_dec(x_1);
x_1 = x_11;
x_2 = x_8;
x_3 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_Borrow_InitParamMap_visitFnBody_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_Borrow_InitParamMap_visitFnBody_spec__1_spec__1___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_Borrow_InitParamMap_visitFnBody_spec__1___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(2u);
x_4 = lean_nat_mul(x_2, x_3);
lean_dec(x_2);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_box(0);
x_7 = lean_mk_array(x_4, x_6);
x_8 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_Borrow_InitParamMap_visitFnBody_spec__1_spec__1___redArg(x_5, x_1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_Borrow_InitParamMap_visitFnBody_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_Borrow_InitParamMap_visitFnBody_spec__1___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_IR_Borrow_InitParamMap_visitFnBody_spec__4___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_3, 2);
x_8 = l_Lean_IR_Borrow_ParamMap_beqKey____x40_Lean_Compiler_IR_Borrow___hyg_214_(x_5, x_1);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_IR_Borrow_InitParamMap_visitFnBody_spec__4___redArg(x_1, x_2, x_7);
lean_ctor_set(x_3, 2, x_9);
return x_3;
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 1);
x_12 = lean_ctor_get(x_3, 2);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_3);
x_13 = l_Lean_IR_Borrow_ParamMap_beqKey____x40_Lean_Compiler_IR_Borrow___hyg_214_(x_10, x_1);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_IR_Borrow_InitParamMap_visitFnBody_spec__4___redArg(x_1, x_2, x_12);
x_15 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_11);
lean_ctor_set(x_15, 2, x_14);
return x_15;
}
else
{
lean_object* x_16; 
lean_dec(x_11);
lean_dec(x_10);
x_16 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_2);
lean_ctor_set(x_16, 2, x_12);
return x_16;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_IR_Borrow_InitParamMap_visitFnBody_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_IR_Borrow_InitParamMap_visitFnBody_spec__4___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_Borrow_InitParamMap_visitFnBody_spec__5(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_14; 
x_14 = lean_usize_dec_eq(x_3, x_4);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_5);
x_15 = lean_array_uget(x_2, x_3);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
lean_inc(x_1);
x_17 = l_Lean_IR_Borrow_InitParamMap_visitFnBody(x_1, x_16, x_6);
x_7 = x_17;
goto block_13;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_18);
lean_dec(x_15);
lean_inc(x_1);
x_19 = l_Lean_IR_Borrow_InitParamMap_visitFnBody(x_1, x_18, x_6);
x_7 = x_19;
goto block_13;
}
}
else
{
lean_object* x_20; 
lean_dec(x_1);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_5);
lean_ctor_set(x_20, 1, x_6);
return x_20;
}
block_13:
{
lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = 1;
x_11 = lean_usize_add(x_3, x_10);
x_3 = x_11;
x_5 = x_8;
x_6 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_InitParamMap_visitFnBody(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 1:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_13; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 3);
lean_inc(x_7);
lean_dec(x_2);
x_13 = !lean_is_exclusive(x_3);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint64_t x_19; uint64_t x_20; uint64_t x_21; uint64_t x_22; uint64_t x_23; uint64_t x_24; uint64_t x_25; size_t x_26; size_t x_27; size_t x_28; size_t x_29; size_t x_30; lean_object* x_31; uint8_t x_32; 
x_14 = lean_ctor_get(x_3, 0);
x_15 = lean_ctor_get(x_3, 1);
lean_inc(x_1);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_4);
x_17 = l_Lean_IR_Borrow_InitParamMap_initBorrow(x_5);
x_18 = lean_array_get_size(x_15);
x_19 = l_Lean_IR_Borrow_ParamMap_getHash(x_16);
x_20 = 32;
x_21 = lean_uint64_shift_right(x_19, x_20);
x_22 = lean_uint64_xor(x_19, x_21);
x_23 = 16;
x_24 = lean_uint64_shift_right(x_22, x_23);
x_25 = lean_uint64_xor(x_22, x_24);
x_26 = lean_uint64_to_usize(x_25);
x_27 = lean_usize_of_nat(x_18);
lean_dec(x_18);
x_28 = 1;
x_29 = lean_usize_sub(x_27, x_28);
x_30 = lean_usize_land(x_26, x_29);
x_31 = lean_array_uget(x_15, x_30);
x_32 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_Borrow_InitParamMap_visitFnBody_spec__0___redArg(x_16, x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_33 = lean_unsigned_to_nat(1u);
x_34 = lean_nat_add(x_14, x_33);
lean_dec(x_14);
x_35 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_35, 0, x_16);
lean_ctor_set(x_35, 1, x_17);
lean_ctor_set(x_35, 2, x_31);
x_36 = lean_array_uset(x_15, x_30, x_35);
x_37 = lean_unsigned_to_nat(4u);
x_38 = lean_nat_mul(x_34, x_37);
x_39 = lean_unsigned_to_nat(3u);
x_40 = lean_nat_div(x_38, x_39);
lean_dec(x_38);
x_41 = lean_array_get_size(x_36);
x_42 = lean_nat_dec_le(x_40, x_41);
lean_dec(x_41);
lean_dec(x_40);
if (x_42 == 0)
{
lean_object* x_43; 
x_43 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_Borrow_InitParamMap_visitFnBody_spec__1___redArg(x_36);
lean_ctor_set(x_3, 1, x_43);
lean_ctor_set(x_3, 0, x_34);
x_8 = x_3;
goto block_12;
}
else
{
lean_ctor_set(x_3, 1, x_36);
lean_ctor_set(x_3, 0, x_34);
x_8 = x_3;
goto block_12;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_44 = lean_box(0);
x_45 = lean_array_uset(x_15, x_30, x_44);
x_46 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_IR_Borrow_InitParamMap_visitFnBody_spec__4___redArg(x_16, x_17, x_31);
x_47 = lean_array_uset(x_45, x_30, x_46);
lean_ctor_set(x_3, 1, x_47);
x_8 = x_3;
goto block_12;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint64_t x_53; uint64_t x_54; uint64_t x_55; uint64_t x_56; uint64_t x_57; uint64_t x_58; uint64_t x_59; size_t x_60; size_t x_61; size_t x_62; size_t x_63; size_t x_64; lean_object* x_65; uint8_t x_66; 
x_48 = lean_ctor_get(x_3, 0);
x_49 = lean_ctor_get(x_3, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_3);
lean_inc(x_1);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_1);
lean_ctor_set(x_50, 1, x_4);
x_51 = l_Lean_IR_Borrow_InitParamMap_initBorrow(x_5);
x_52 = lean_array_get_size(x_49);
x_53 = l_Lean_IR_Borrow_ParamMap_getHash(x_50);
x_54 = 32;
x_55 = lean_uint64_shift_right(x_53, x_54);
x_56 = lean_uint64_xor(x_53, x_55);
x_57 = 16;
x_58 = lean_uint64_shift_right(x_56, x_57);
x_59 = lean_uint64_xor(x_56, x_58);
x_60 = lean_uint64_to_usize(x_59);
x_61 = lean_usize_of_nat(x_52);
lean_dec(x_52);
x_62 = 1;
x_63 = lean_usize_sub(x_61, x_62);
x_64 = lean_usize_land(x_60, x_63);
x_65 = lean_array_uget(x_49, x_64);
x_66 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_Borrow_InitParamMap_visitFnBody_spec__0___redArg(x_50, x_65);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_67 = lean_unsigned_to_nat(1u);
x_68 = lean_nat_add(x_48, x_67);
lean_dec(x_48);
x_69 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_69, 0, x_50);
lean_ctor_set(x_69, 1, x_51);
lean_ctor_set(x_69, 2, x_65);
x_70 = lean_array_uset(x_49, x_64, x_69);
x_71 = lean_unsigned_to_nat(4u);
x_72 = lean_nat_mul(x_68, x_71);
x_73 = lean_unsigned_to_nat(3u);
x_74 = lean_nat_div(x_72, x_73);
lean_dec(x_72);
x_75 = lean_array_get_size(x_70);
x_76 = lean_nat_dec_le(x_74, x_75);
lean_dec(x_75);
lean_dec(x_74);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; 
x_77 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_Borrow_InitParamMap_visitFnBody_spec__1___redArg(x_70);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_68);
lean_ctor_set(x_78, 1, x_77);
x_8 = x_78;
goto block_12;
}
else
{
lean_object* x_79; 
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_68);
lean_ctor_set(x_79, 1, x_70);
x_8 = x_79;
goto block_12;
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_80 = lean_box(0);
x_81 = lean_array_uset(x_49, x_64, x_80);
x_82 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_IR_Borrow_InitParamMap_visitFnBody_spec__4___redArg(x_50, x_51, x_65);
x_83 = lean_array_uset(x_81, x_64, x_82);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_48);
lean_ctor_set(x_84, 1, x_83);
x_8 = x_84;
goto block_12;
}
}
block_12:
{
lean_object* x_9; lean_object* x_10; 
lean_inc(x_1);
x_9 = l_Lean_IR_Borrow_InitParamMap_visitFnBody(x_1, x_6, x_8);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_2 = x_7;
x_3 = x_10;
goto _start;
}
}
case 10:
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_85 = lean_ctor_get(x_2, 3);
lean_inc(x_85);
lean_dec(x_2);
x_86 = lean_unsigned_to_nat(0u);
x_87 = lean_array_get_size(x_85);
x_88 = lean_box(0);
x_89 = lean_nat_dec_lt(x_86, x_87);
if (x_89 == 0)
{
lean_object* x_90; 
lean_dec(x_87);
lean_dec(x_85);
lean_dec(x_1);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_3);
return x_90;
}
else
{
uint8_t x_91; 
x_91 = lean_nat_dec_le(x_87, x_87);
if (x_91 == 0)
{
lean_object* x_92; 
lean_dec(x_87);
lean_dec(x_85);
lean_dec(x_1);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_88);
lean_ctor_set(x_92, 1, x_3);
return x_92;
}
else
{
size_t x_93; size_t x_94; lean_object* x_95; 
x_93 = 0;
x_94 = lean_usize_of_nat(x_87);
lean_dec(x_87);
x_95 = l_Array_foldlMUnsafe_fold___at___Lean_IR_Borrow_InitParamMap_visitFnBody_spec__5(x_1, x_85, x_93, x_94, x_88, x_3);
lean_dec(x_85);
return x_95;
}
}
}
default: 
{
uint8_t x_96; 
x_96 = l_Lean_IR_FnBody_isTerminal(x_2);
if (x_96 == 0)
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_97; 
x_97 = lean_ctor_get(x_2, 3);
lean_inc(x_97);
lean_dec(x_2);
x_2 = x_97;
goto _start;
}
case 1:
{
lean_object* x_99; 
x_99 = lean_ctor_get(x_2, 3);
lean_inc(x_99);
lean_dec(x_2);
x_2 = x_99;
goto _start;
}
case 2:
{
lean_object* x_101; 
x_101 = lean_ctor_get(x_2, 3);
lean_inc(x_101);
lean_dec(x_2);
x_2 = x_101;
goto _start;
}
case 3:
{
lean_object* x_103; 
x_103 = lean_ctor_get(x_2, 2);
lean_inc(x_103);
lean_dec(x_2);
x_2 = x_103;
goto _start;
}
case 4:
{
lean_object* x_105; 
x_105 = lean_ctor_get(x_2, 3);
lean_inc(x_105);
lean_dec(x_2);
x_2 = x_105;
goto _start;
}
case 5:
{
lean_object* x_107; 
x_107 = lean_ctor_get(x_2, 5);
lean_inc(x_107);
lean_dec(x_2);
x_2 = x_107;
goto _start;
}
case 6:
{
lean_object* x_109; 
x_109 = lean_ctor_get(x_2, 2);
lean_inc(x_109);
lean_dec(x_2);
x_2 = x_109;
goto _start;
}
case 7:
{
lean_object* x_111; 
x_111 = lean_ctor_get(x_2, 2);
lean_inc(x_111);
lean_dec(x_2);
x_2 = x_111;
goto _start;
}
case 8:
{
lean_object* x_113; 
x_113 = lean_ctor_get(x_2, 1);
lean_inc(x_113);
lean_dec(x_2);
x_2 = x_113;
goto _start;
}
case 9:
{
lean_object* x_115; 
x_115 = lean_ctor_get(x_2, 1);
lean_inc(x_115);
lean_dec(x_2);
x_2 = x_115;
goto _start;
}
default: 
{
goto _start;
}
}
}
else
{
lean_object* x_118; lean_object* x_119; 
lean_dec(x_2);
lean_dec(x_1);
x_118 = lean_box(0);
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_3);
return x_119;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_Borrow_InitParamMap_visitFnBody_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_Borrow_InitParamMap_visitFnBody_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_Borrow_InitParamMap_visitFnBody_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_Borrow_InitParamMap_visitFnBody_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_Borrow_InitParamMap_visitFnBody_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l_Array_foldlMUnsafe_fold___at___Lean_IR_Borrow_InitParamMap_visitFnBody_spec__5(x_1, x_2, x_7, x_8, x_5, x_6);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_Borrow_InitParamMap_visitDecls_spec__0___redArg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_13; 
x_13 = lean_usize_dec_eq(x_3, x_4);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_5);
x_14 = lean_array_uget(x_2, x_3);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_23; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_14, 3);
lean_inc(x_17);
lean_dec(x_14);
x_23 = !lean_is_exclusive(x_6);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; uint64_t x_33; uint64_t x_34; uint64_t x_35; uint64_t x_36; size_t x_37; size_t x_38; size_t x_39; size_t x_40; size_t x_41; lean_object* x_42; uint8_t x_43; 
x_24 = lean_ctor_get(x_6, 0);
x_25 = lean_ctor_get(x_6, 1);
lean_inc(x_15);
lean_inc(x_1);
x_26 = l_Lean_isExport(x_1, x_15);
lean_inc(x_15);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_15);
x_28 = l_Lean_IR_Borrow_InitParamMap_initBorrowIfNotExported(x_26, x_16);
x_29 = lean_array_get_size(x_25);
x_30 = l_Lean_IR_Borrow_ParamMap_getHash(x_27);
x_31 = 32;
x_32 = lean_uint64_shift_right(x_30, x_31);
x_33 = lean_uint64_xor(x_30, x_32);
x_34 = 16;
x_35 = lean_uint64_shift_right(x_33, x_34);
x_36 = lean_uint64_xor(x_33, x_35);
x_37 = lean_uint64_to_usize(x_36);
x_38 = lean_usize_of_nat(x_29);
lean_dec(x_29);
x_39 = 1;
x_40 = lean_usize_sub(x_38, x_39);
x_41 = lean_usize_land(x_37, x_40);
x_42 = lean_array_uget(x_25, x_41);
x_43 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_Borrow_InitParamMap_visitFnBody_spec__0___redArg(x_27, x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_44 = lean_unsigned_to_nat(1u);
x_45 = lean_nat_add(x_24, x_44);
lean_dec(x_24);
x_46 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_46, 0, x_27);
lean_ctor_set(x_46, 1, x_28);
lean_ctor_set(x_46, 2, x_42);
x_47 = lean_array_uset(x_25, x_41, x_46);
x_48 = lean_unsigned_to_nat(4u);
x_49 = lean_nat_mul(x_45, x_48);
x_50 = lean_unsigned_to_nat(3u);
x_51 = lean_nat_div(x_49, x_50);
lean_dec(x_49);
x_52 = lean_array_get_size(x_47);
x_53 = lean_nat_dec_le(x_51, x_52);
lean_dec(x_52);
lean_dec(x_51);
if (x_53 == 0)
{
lean_object* x_54; 
x_54 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_Borrow_InitParamMap_visitFnBody_spec__1___redArg(x_47);
lean_ctor_set(x_6, 1, x_54);
lean_ctor_set(x_6, 0, x_45);
x_18 = x_6;
goto block_22;
}
else
{
lean_ctor_set(x_6, 1, x_47);
lean_ctor_set(x_6, 0, x_45);
x_18 = x_6;
goto block_22;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_55 = lean_box(0);
x_56 = lean_array_uset(x_25, x_41, x_55);
x_57 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_IR_Borrow_InitParamMap_visitFnBody_spec__4___redArg(x_27, x_28, x_42);
x_58 = lean_array_uset(x_56, x_41, x_57);
lean_ctor_set(x_6, 1, x_58);
x_18 = x_6;
goto block_22;
}
}
else
{
lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint64_t x_65; uint64_t x_66; uint64_t x_67; uint64_t x_68; uint64_t x_69; uint64_t x_70; uint64_t x_71; size_t x_72; size_t x_73; size_t x_74; size_t x_75; size_t x_76; lean_object* x_77; uint8_t x_78; 
x_59 = lean_ctor_get(x_6, 0);
x_60 = lean_ctor_get(x_6, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_6);
lean_inc(x_15);
lean_inc(x_1);
x_61 = l_Lean_isExport(x_1, x_15);
lean_inc(x_15);
x_62 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_62, 0, x_15);
x_63 = l_Lean_IR_Borrow_InitParamMap_initBorrowIfNotExported(x_61, x_16);
x_64 = lean_array_get_size(x_60);
x_65 = l_Lean_IR_Borrow_ParamMap_getHash(x_62);
x_66 = 32;
x_67 = lean_uint64_shift_right(x_65, x_66);
x_68 = lean_uint64_xor(x_65, x_67);
x_69 = 16;
x_70 = lean_uint64_shift_right(x_68, x_69);
x_71 = lean_uint64_xor(x_68, x_70);
x_72 = lean_uint64_to_usize(x_71);
x_73 = lean_usize_of_nat(x_64);
lean_dec(x_64);
x_74 = 1;
x_75 = lean_usize_sub(x_73, x_74);
x_76 = lean_usize_land(x_72, x_75);
x_77 = lean_array_uget(x_60, x_76);
x_78 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_Borrow_InitParamMap_visitFnBody_spec__0___redArg(x_62, x_77);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_79 = lean_unsigned_to_nat(1u);
x_80 = lean_nat_add(x_59, x_79);
lean_dec(x_59);
x_81 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_81, 0, x_62);
lean_ctor_set(x_81, 1, x_63);
lean_ctor_set(x_81, 2, x_77);
x_82 = lean_array_uset(x_60, x_76, x_81);
x_83 = lean_unsigned_to_nat(4u);
x_84 = lean_nat_mul(x_80, x_83);
x_85 = lean_unsigned_to_nat(3u);
x_86 = lean_nat_div(x_84, x_85);
lean_dec(x_84);
x_87 = lean_array_get_size(x_82);
x_88 = lean_nat_dec_le(x_86, x_87);
lean_dec(x_87);
lean_dec(x_86);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; 
x_89 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_Borrow_InitParamMap_visitFnBody_spec__1___redArg(x_82);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_80);
lean_ctor_set(x_90, 1, x_89);
x_18 = x_90;
goto block_22;
}
else
{
lean_object* x_91; 
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_80);
lean_ctor_set(x_91, 1, x_82);
x_18 = x_91;
goto block_22;
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_92 = lean_box(0);
x_93 = lean_array_uset(x_60, x_76, x_92);
x_94 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_IR_Borrow_InitParamMap_visitFnBody_spec__4___redArg(x_62, x_63, x_77);
x_95 = lean_array_uset(x_93, x_76, x_94);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_59);
lean_ctor_set(x_96, 1, x_95);
x_18 = x_96;
goto block_22;
}
}
block_22:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = l_Lean_IR_Borrow_InitParamMap_visitFnBody(x_15, x_17, x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_7 = x_20;
x_8 = x_21;
goto block_12;
}
}
else
{
lean_object* x_97; 
lean_dec(x_14);
x_97 = lean_box(0);
x_7 = x_97;
x_8 = x_6;
goto block_12;
}
}
else
{
lean_object* x_98; 
lean_dec(x_1);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_5);
lean_ctor_set(x_98, 1, x_6);
return x_98;
}
block_12:
{
size_t x_9; size_t x_10; 
x_9 = 1;
x_10 = lean_usize_add(x_3, x_9);
x_3 = x_10;
x_5 = x_7;
x_6 = x_8;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_Borrow_InitParamMap_visitDecls_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Array_foldlMUnsafe_fold___at___Lean_IR_Borrow_InitParamMap_visitDecls_spec__0___redArg(x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_InitParamMap_visitDecls(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_array_get_size(x_2);
x_6 = lean_box(0);
x_7 = lean_nat_dec_lt(x_4, x_5);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_5);
lean_dec(x_1);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = lean_nat_dec_le(x_5, x_5);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_5);
lean_dec(x_1);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_3);
return x_10;
}
else
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = 0;
x_12 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_13 = l_Array_foldlMUnsafe_fold___at___Lean_IR_Borrow_InitParamMap_visitDecls_spec__0___redArg(x_1, x_2, x_11, x_12, x_6, x_3);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_Borrow_InitParamMap_visitDecls_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l_Array_foldlMUnsafe_fold___at___Lean_IR_Borrow_InitParamMap_visitDecls_spec__0___redArg(x_1, x_2, x_7, x_8, x_5, x_6);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_Borrow_InitParamMap_visitDecls_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_10 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_11 = l_Array_foldlMUnsafe_fold___at___Lean_IR_Borrow_InitParamMap_visitDecls_spec__0(x_1, x_2, x_3, x_4, x_9, x_10, x_7, x_8);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_InitParamMap_visitDecls___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_Borrow_InitParamMap_visitDecls(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_IR_Borrow_mkInitParamMap___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_unsigned_to_nat(8u);
x_3 = lean_nat_mul(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_Borrow_mkInitParamMap___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = l_Lean_IR_Borrow_mkInitParamMap___closed__0;
x_3 = lean_nat_div(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_Borrow_mkInitParamMap___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_Borrow_mkInitParamMap___closed__1;
x_2 = l_Nat_nextPowerOfTwo(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_Borrow_mkInitParamMap___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_IR_Borrow_mkInitParamMap___closed__2;
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_Borrow_mkInitParamMap___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_Borrow_mkInitParamMap___closed__3;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_mkInitParamMap(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Lean_IR_Borrow_mkInitParamMap___closed__4;
x_4 = l_Lean_IR_Borrow_InitParamMap_visitDecls(x_1, x_2, x_3);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_mkInitParamMap___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_Borrow_mkInitParamMap(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_IR_Borrow_ApplyParamMap_visitFnBody_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
x_7 = l_Lean_IR_Borrow_ParamMap_beqKey____x40_Lean_Compiler_IR_Borrow___hyg_214_(x_4, x_1);
if (x_7 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
lean_object* x_9; 
lean_inc(x_5);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_5);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_IR_Borrow_ApplyParamMap_visitFnBody_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_IR_Borrow_ApplyParamMap_visitFnBody_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_IR_Borrow_ApplyParamMap_visitFnBody_spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(13);
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_Borrow_ApplyParamMap_visitFnBody_spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_lt(x_4, x_3);
if (x_6 == 0)
{
lean_dec(x_1);
return x_5;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_array_uget(x_5, x_4);
x_8 = lean_box(0);
x_9 = lean_array_uset(x_5, x_4, x_8);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_7);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_7, 1);
lean_inc(x_1);
x_18 = l_Lean_IR_Borrow_ApplyParamMap_visitFnBody(x_1, x_2, x_17);
lean_ctor_set(x_7, 1, x_18);
x_10 = x_7;
goto block_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_7, 0);
x_20 = lean_ctor_get(x_7, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_7);
lean_inc(x_1);
x_21 = l_Lean_IR_Borrow_ApplyParamMap_visitFnBody(x_1, x_2, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_21);
x_10 = x_22;
goto block_15;
}
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_7);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_7, 0);
lean_inc(x_1);
x_25 = l_Lean_IR_Borrow_ApplyParamMap_visitFnBody(x_1, x_2, x_24);
lean_ctor_set(x_7, 0, x_25);
x_10 = x_7;
goto block_15;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_7, 0);
lean_inc(x_26);
lean_dec(x_7);
lean_inc(x_1);
x_27 = l_Lean_IR_Borrow_ApplyParamMap_visitFnBody(x_1, x_2, x_26);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_10 = x_28;
goto block_15;
}
}
block_15:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = 1;
x_12 = lean_usize_add(x_4, x_11);
x_13 = lean_array_uset(x_9, x_4, x_10);
x_4 = x_12;
x_5 = x_13;
goto _start;
}
}
}
}
static lean_object* _init_l_Lean_IR_Borrow_ApplyParamMap_visitFnBody___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Compiler.IR.Borrow", 23, 23);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_Borrow_ApplyParamMap_visitFnBody___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.IR.Borrow.ApplyParamMap.visitFnBody", 40, 40);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_Borrow_ApplyParamMap_visitFnBody___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_Borrow_ApplyParamMap_visitFnBody___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_IR_Borrow_ApplyParamMap_visitFnBody___closed__2;
x_2 = lean_unsigned_to_nat(17u);
x_3 = lean_unsigned_to_nat(114u);
x_4 = l_Lean_IR_Borrow_ApplyParamMap_visitFnBody___closed__1;
x_5 = l_Lean_IR_Borrow_ApplyParamMap_visitFnBody___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_ApplyParamMap_visitFnBody(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
switch (lean_obj_tag(x_3)) {
case 1:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint64_t x_18; uint64_t x_19; uint64_t x_20; uint64_t x_21; uint64_t x_22; uint64_t x_23; uint64_t x_24; size_t x_25; size_t x_26; size_t x_27; size_t x_28; size_t x_29; lean_object* x_30; lean_object* x_31; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 2);
x_13 = lean_ctor_get(x_3, 3);
x_14 = lean_ctor_get(x_3, 1);
lean_dec(x_14);
x_15 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
lean_inc(x_1);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_11);
x_17 = lean_array_get_size(x_15);
x_18 = l_Lean_IR_Borrow_ParamMap_getHash(x_16);
x_19 = 32;
x_20 = lean_uint64_shift_right(x_18, x_19);
x_21 = lean_uint64_xor(x_18, x_20);
x_22 = 16;
x_23 = lean_uint64_shift_right(x_21, x_22);
x_24 = lean_uint64_xor(x_21, x_23);
x_25 = lean_uint64_to_usize(x_24);
x_26 = lean_usize_of_nat(x_17);
lean_dec(x_17);
x_27 = 1;
x_28 = lean_usize_sub(x_26, x_27);
x_29 = lean_usize_land(x_25, x_28);
x_30 = lean_array_uget(x_15, x_29);
x_31 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_IR_Borrow_ApplyParamMap_visitFnBody_spec__0___redArg(x_16, x_30);
lean_dec(x_30);
lean_dec(x_16);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; 
lean_free_object(x_3);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_1);
x_32 = l_Lean_IR_Borrow_ApplyParamMap_visitFnBody___closed__3;
x_33 = l_panic___at___Lean_IR_Borrow_ApplyParamMap_visitFnBody_spec__1(x_32);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_31, 0);
lean_inc(x_34);
lean_dec(x_31);
lean_inc(x_1);
x_35 = l_Lean_IR_Borrow_ApplyParamMap_visitFnBody(x_1, x_2, x_12);
x_36 = l_Lean_IR_Borrow_ApplyParamMap_visitFnBody(x_1, x_2, x_13);
lean_ctor_set(x_3, 3, x_36);
lean_ctor_set(x_3, 2, x_35);
lean_ctor_set(x_3, 1, x_34);
return x_3;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint64_t x_43; uint64_t x_44; uint64_t x_45; uint64_t x_46; uint64_t x_47; uint64_t x_48; uint64_t x_49; size_t x_50; size_t x_51; size_t x_52; size_t x_53; size_t x_54; lean_object* x_55; lean_object* x_56; 
x_37 = lean_ctor_get(x_3, 0);
x_38 = lean_ctor_get(x_3, 2);
x_39 = lean_ctor_get(x_3, 3);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_3);
x_40 = lean_ctor_get(x_2, 1);
lean_inc(x_37);
lean_inc(x_1);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_1);
lean_ctor_set(x_41, 1, x_37);
x_42 = lean_array_get_size(x_40);
x_43 = l_Lean_IR_Borrow_ParamMap_getHash(x_41);
x_44 = 32;
x_45 = lean_uint64_shift_right(x_43, x_44);
x_46 = lean_uint64_xor(x_43, x_45);
x_47 = 16;
x_48 = lean_uint64_shift_right(x_46, x_47);
x_49 = lean_uint64_xor(x_46, x_48);
x_50 = lean_uint64_to_usize(x_49);
x_51 = lean_usize_of_nat(x_42);
lean_dec(x_42);
x_52 = 1;
x_53 = lean_usize_sub(x_51, x_52);
x_54 = lean_usize_land(x_50, x_53);
x_55 = lean_array_uget(x_40, x_54);
x_56 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_IR_Borrow_ApplyParamMap_visitFnBody_spec__0___redArg(x_41, x_55);
lean_dec(x_55);
lean_dec(x_41);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; 
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_1);
x_57 = l_Lean_IR_Borrow_ApplyParamMap_visitFnBody___closed__3;
x_58 = l_panic___at___Lean_IR_Borrow_ApplyParamMap_visitFnBody_spec__1(x_57);
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_59 = lean_ctor_get(x_56, 0);
lean_inc(x_59);
lean_dec(x_56);
lean_inc(x_1);
x_60 = l_Lean_IR_Borrow_ApplyParamMap_visitFnBody(x_1, x_2, x_38);
x_61 = l_Lean_IR_Borrow_ApplyParamMap_visitFnBody(x_1, x_2, x_39);
x_62 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_62, 0, x_37);
lean_ctor_set(x_62, 1, x_59);
lean_ctor_set(x_62, 2, x_60);
lean_ctor_set(x_62, 3, x_61);
return x_62;
}
}
}
case 10:
{
uint8_t x_63; 
x_63 = !lean_is_exclusive(x_3);
if (x_63 == 0)
{
lean_object* x_64; size_t x_65; size_t x_66; lean_object* x_67; 
x_64 = lean_ctor_get(x_3, 3);
x_65 = lean_array_size(x_64);
x_66 = 0;
x_67 = l_Array_mapMUnsafe_map___at___Lean_IR_Borrow_ApplyParamMap_visitFnBody_spec__2(x_1, x_2, x_65, x_66, x_64);
lean_ctor_set(x_3, 3, x_67);
return x_3;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; size_t x_72; size_t x_73; lean_object* x_74; lean_object* x_75; 
x_68 = lean_ctor_get(x_3, 0);
x_69 = lean_ctor_get(x_3, 1);
x_70 = lean_ctor_get(x_3, 2);
x_71 = lean_ctor_get(x_3, 3);
lean_inc(x_71);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_3);
x_72 = lean_array_size(x_71);
x_73 = 0;
x_74 = l_Array_mapMUnsafe_map___at___Lean_IR_Borrow_ApplyParamMap_visitFnBody_spec__2(x_1, x_2, x_72, x_73, x_71);
x_75 = lean_alloc_ctor(10, 4, 0);
lean_ctor_set(x_75, 0, x_68);
lean_ctor_set(x_75, 1, x_69);
lean_ctor_set(x_75, 2, x_70);
lean_ctor_set(x_75, 3, x_74);
return x_75;
}
}
default: 
{
uint8_t x_76; 
x_76 = l_Lean_IR_FnBody_isTerminal(x_3);
if (x_76 == 0)
{
switch (lean_obj_tag(x_3)) {
case 0:
{
lean_object* x_77; 
x_77 = lean_ctor_get(x_3, 3);
lean_inc(x_77);
x_4 = x_77;
goto block_9;
}
case 1:
{
lean_object* x_78; 
x_78 = lean_ctor_get(x_3, 3);
lean_inc(x_78);
x_4 = x_78;
goto block_9;
}
case 2:
{
lean_object* x_79; 
x_79 = lean_ctor_get(x_3, 3);
lean_inc(x_79);
x_4 = x_79;
goto block_9;
}
case 3:
{
lean_object* x_80; 
x_80 = lean_ctor_get(x_3, 2);
lean_inc(x_80);
x_4 = x_80;
goto block_9;
}
case 4:
{
lean_object* x_81; 
x_81 = lean_ctor_get(x_3, 3);
lean_inc(x_81);
x_4 = x_81;
goto block_9;
}
case 5:
{
lean_object* x_82; 
x_82 = lean_ctor_get(x_3, 5);
lean_inc(x_82);
x_4 = x_82;
goto block_9;
}
case 6:
{
lean_object* x_83; 
x_83 = lean_ctor_get(x_3, 2);
lean_inc(x_83);
x_4 = x_83;
goto block_9;
}
case 7:
{
lean_object* x_84; 
x_84 = lean_ctor_get(x_3, 2);
lean_inc(x_84);
x_4 = x_84;
goto block_9;
}
case 8:
{
lean_object* x_85; 
x_85 = lean_ctor_get(x_3, 1);
lean_inc(x_85);
x_4 = x_85;
goto block_9;
}
case 9:
{
lean_object* x_86; 
x_86 = lean_ctor_get(x_3, 1);
lean_inc(x_86);
x_4 = x_86;
goto block_9;
}
default: 
{
lean_inc(x_3);
x_4 = x_3;
goto block_9;
}
}
}
else
{
lean_dec(x_1);
return x_3;
}
}
}
block_9:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_box(13);
x_6 = l_Lean_IR_FnBody_setBody(x_3, x_5);
x_7 = l_Lean_IR_Borrow_ApplyParamMap_visitFnBody(x_1, x_2, x_4);
x_8 = l_Lean_IR_FnBody_setBody(x_6, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_IR_Borrow_ApplyParamMap_visitFnBody_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_IR_Borrow_ApplyParamMap_visitFnBody_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_IR_Borrow_ApplyParamMap_visitFnBody_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_IR_Borrow_ApplyParamMap_visitFnBody_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_Borrow_ApplyParamMap_visitFnBody_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_mapMUnsafe_map___at___Lean_IR_Borrow_ApplyParamMap_visitFnBody_spec__2(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_ApplyParamMap_visitFnBody___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_Borrow_ApplyParamMap_visitFnBody(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at___Lean_IR_Borrow_ApplyParamMap_visitDecls_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.IR.Borrow.ApplyParamMap.visitDecls", 39, 39);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at___Lean_IR_Borrow_ApplyParamMap_visitDecls_spec__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_IR_Borrow_ApplyParamMap_visitFnBody___closed__2;
x_2 = lean_unsigned_to_nat(19u);
x_3 = lean_unsigned_to_nat(130u);
x_4 = l_Array_mapMUnsafe_map___at___Lean_IR_Borrow_ApplyParamMap_visitDecls_spec__0___closed__0;
x_5 = l_Lean_IR_Borrow_ApplyParamMap_visitFnBody___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_Borrow_ApplyParamMap_visitDecls_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_3, x_2);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_array_uget(x_4, x_3);
x_7 = lean_box(0);
x_8 = lean_array_uset(x_4, x_3, x_7);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_6);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint64_t x_24; uint64_t x_25; uint64_t x_26; uint64_t x_27; uint64_t x_28; uint64_t x_29; uint64_t x_30; size_t x_31; size_t x_32; size_t x_33; size_t x_34; size_t x_35; lean_object* x_36; lean_object* x_37; 
x_16 = lean_ctor_get(x_6, 0);
x_17 = lean_ctor_get(x_6, 2);
x_18 = lean_ctor_get(x_6, 3);
x_19 = lean_ctor_get(x_6, 4);
x_20 = lean_ctor_get(x_6, 1);
lean_dec(x_20);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_16);
x_23 = lean_array_get_size(x_21);
x_24 = l_Lean_IR_Borrow_ParamMap_getHash(x_22);
x_25 = 32;
x_26 = lean_uint64_shift_right(x_24, x_25);
x_27 = lean_uint64_xor(x_24, x_26);
x_28 = 16;
x_29 = lean_uint64_shift_right(x_27, x_28);
x_30 = lean_uint64_xor(x_27, x_29);
x_31 = lean_uint64_to_usize(x_30);
x_32 = lean_usize_of_nat(x_23);
lean_dec(x_23);
x_33 = 1;
x_34 = lean_usize_sub(x_32, x_33);
x_35 = lean_usize_land(x_31, x_34);
x_36 = lean_array_uget(x_21, x_35);
x_37 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_IR_Borrow_ApplyParamMap_visitFnBody_spec__0___redArg(x_22, x_36);
lean_dec(x_36);
lean_dec(x_22);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; 
lean_free_object(x_6);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
x_38 = l_Array_mapMUnsafe_map___at___Lean_IR_Borrow_ApplyParamMap_visitDecls_spec__0___closed__1;
x_39 = l_panic___at___Lean_IR_Decl_updateBody_x21_spec__0(x_38);
x_9 = x_39;
goto block_14;
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_37, 0);
lean_inc(x_40);
lean_dec(x_37);
lean_inc(x_16);
x_41 = l_Lean_IR_Borrow_ApplyParamMap_visitFnBody(x_16, x_1, x_18);
lean_ctor_set(x_6, 3, x_41);
lean_ctor_set(x_6, 1, x_40);
x_9 = x_6;
goto block_14;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint64_t x_49; uint64_t x_50; uint64_t x_51; uint64_t x_52; uint64_t x_53; uint64_t x_54; uint64_t x_55; size_t x_56; size_t x_57; size_t x_58; size_t x_59; size_t x_60; lean_object* x_61; lean_object* x_62; 
x_42 = lean_ctor_get(x_6, 0);
x_43 = lean_ctor_get(x_6, 2);
x_44 = lean_ctor_get(x_6, 3);
x_45 = lean_ctor_get(x_6, 4);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_6);
x_46 = lean_ctor_get(x_1, 1);
lean_inc(x_42);
x_47 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_47, 0, x_42);
x_48 = lean_array_get_size(x_46);
x_49 = l_Lean_IR_Borrow_ParamMap_getHash(x_47);
x_50 = 32;
x_51 = lean_uint64_shift_right(x_49, x_50);
x_52 = lean_uint64_xor(x_49, x_51);
x_53 = 16;
x_54 = lean_uint64_shift_right(x_52, x_53);
x_55 = lean_uint64_xor(x_52, x_54);
x_56 = lean_uint64_to_usize(x_55);
x_57 = lean_usize_of_nat(x_48);
lean_dec(x_48);
x_58 = 1;
x_59 = lean_usize_sub(x_57, x_58);
x_60 = lean_usize_land(x_56, x_59);
x_61 = lean_array_uget(x_46, x_60);
x_62 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_IR_Borrow_ApplyParamMap_visitFnBody_spec__0___redArg(x_47, x_61);
lean_dec(x_61);
lean_dec(x_47);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_42);
x_63 = l_Array_mapMUnsafe_map___at___Lean_IR_Borrow_ApplyParamMap_visitDecls_spec__0___closed__1;
x_64 = l_panic___at___Lean_IR_Decl_updateBody_x21_spec__0(x_63);
x_9 = x_64;
goto block_14;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_62, 0);
lean_inc(x_65);
lean_dec(x_62);
lean_inc(x_42);
x_66 = l_Lean_IR_Borrow_ApplyParamMap_visitFnBody(x_42, x_1, x_44);
x_67 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_67, 0, x_42);
lean_ctor_set(x_67, 1, x_65);
lean_ctor_set(x_67, 2, x_43);
lean_ctor_set(x_67, 3, x_66);
lean_ctor_set(x_67, 4, x_45);
x_9 = x_67;
goto block_14;
}
}
}
else
{
x_9 = x_6;
goto block_14;
}
block_14:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = 1;
x_11 = lean_usize_add(x_3, x_10);
x_12 = lean_array_uset(x_8, x_3, x_9);
x_3 = x_11;
x_4 = x_12;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_ApplyParamMap_visitDecls(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; size_t x_4; lean_object* x_5; 
x_3 = lean_array_size(x_1);
x_4 = 0;
x_5 = l_Array_mapMUnsafe_map___at___Lean_IR_Borrow_ApplyParamMap_visitDecls_spec__0(x_2, x_3, x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_Borrow_ApplyParamMap_visitDecls_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at___Lean_IR_Borrow_ApplyParamMap_visitDecls_spec__0(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_ApplyParamMap_visitDecls___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_Borrow_ApplyParamMap_visitDecls(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_applyParamMap(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_Borrow_ApplyParamMap_visitDecls(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_applyParamMap___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_Borrow_applyParamMap(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_getCurrFn(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 2);
lean_inc(x_3);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_getCurrFn___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_Borrow_getCurrFn(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_markModified___redArg(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_box(0);
x_4 = lean_box(1);
x_5 = lean_unbox(x_4);
lean_ctor_set_uint8(x_1, sizeof(void*)*2, x_5);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_1);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_1);
x_9 = lean_box(0);
x_10 = lean_box(1);
x_11 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_8);
x_12 = lean_unbox(x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*2, x_12);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_markModified(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_Borrow_markModified___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_markModified___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_Borrow_markModified(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_ownVar(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_IR_Borrow_getCurrFn(x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_4, 1);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
x_9 = lean_box(0);
lean_ctor_set(x_4, 1, x_1);
x_10 = l_Lean_IR_Borrow_OwnedSet_contains(x_7, x_4);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_6);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_6, 1);
lean_dec(x_12);
x_13 = lean_ctor_get(x_6, 0);
lean_dec(x_13);
x_14 = lean_box(1);
x_15 = l_Lean_IR_Borrow_OwnedSet_insert(x_7, x_4);
lean_ctor_set(x_6, 0, x_15);
x_16 = lean_unbox(x_14);
lean_ctor_set_uint8(x_6, sizeof(void*)*2, x_16);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_9);
lean_ctor_set(x_17, 1, x_6);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; 
lean_dec(x_6);
x_18 = lean_box(1);
x_19 = l_Lean_IR_Borrow_OwnedSet_insert(x_7, x_4);
x_20 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_8);
x_21 = lean_unbox(x_18);
lean_ctor_set_uint8(x_20, sizeof(void*)*2, x_21);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_9);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
else
{
lean_object* x_23; 
lean_dec(x_4);
lean_dec(x_8);
lean_dec(x_7);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_9);
lean_ctor_set(x_23, 1, x_6);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_24 = lean_ctor_get(x_4, 1);
x_25 = lean_ctor_get(x_4, 0);
lean_inc(x_24);
lean_inc(x_25);
lean_dec(x_4);
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_25);
lean_ctor_set(x_29, 1, x_1);
x_30 = l_Lean_IR_Borrow_OwnedSet_contains(x_26, x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; 
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_31 = x_24;
} else {
 lean_dec_ref(x_24);
 x_31 = lean_box(0);
}
x_32 = lean_box(1);
x_33 = l_Lean_IR_Borrow_OwnedSet_insert(x_26, x_29);
if (lean_is_scalar(x_31)) {
 x_34 = lean_alloc_ctor(0, 2, 1);
} else {
 x_34 = x_31;
}
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_27);
x_35 = lean_unbox(x_32);
lean_ctor_set_uint8(x_34, sizeof(void*)*2, x_35);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_28);
lean_ctor_set(x_36, 1, x_34);
return x_36;
}
else
{
lean_object* x_37; 
lean_dec(x_29);
lean_dec(x_27);
lean_dec(x_26);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_28);
lean_ctor_set(x_37, 1, x_24);
return x_37;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_ownVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_Borrow_ownVar(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_ownArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = l_Lean_IR_Borrow_ownVar(x_4, x_2, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_ownArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_Borrow_ownArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_Borrow_ownArgs_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_2, x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; 
lean_dec(x_4);
x_8 = lean_array_uget(x_1, x_2);
x_9 = l_Lean_IR_Borrow_ownArg(x_8, x_5, x_6);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = 1;
x_13 = lean_usize_add(x_2, x_12);
x_2 = x_13;
x_4 = x_10;
x_6 = x_11;
goto _start;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_4);
lean_ctor_set(x_15, 1, x_6);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_ownArgs(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_array_get_size(x_1);
x_6 = lean_box(0);
x_7 = lean_nat_dec_lt(x_4, x_5);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_5);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = lean_nat_dec_le(x_5, x_5);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_5);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_3);
return x_10;
}
else
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = 0;
x_12 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_13 = l_Array_foldlMUnsafe_fold___at___Lean_IR_Borrow_ownArgs_spec__0(x_1, x_11, x_12, x_6, x_2, x_3);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_Borrow_ownArgs_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l_Array_foldlMUnsafe_fold___at___Lean_IR_Borrow_ownArgs_spec__0(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_ownArgs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_Borrow_ownArgs(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_isOwned(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_IR_Borrow_getCurrFn(x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_4, 1);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_ctor_set(x_4, 1, x_1);
x_8 = l_Lean_IR_Borrow_OwnedSet_contains(x_7, x_4);
lean_dec(x_4);
lean_dec(x_7);
x_9 = lean_box(x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_6);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_4, 1);
x_12 = lean_ctor_get(x_4, 0);
lean_inc(x_11);
lean_inc(x_12);
lean_dec(x_4);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_1);
x_15 = l_Lean_IR_Borrow_OwnedSet_contains(x_13, x_14);
lean_dec(x_14);
lean_dec(x_13);
x_16 = lean_box(x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_11);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_isOwned___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_Borrow_isOwned(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_Borrow_updateParamMap_spec__0(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_lt(x_2, x_1);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = lean_array_uget(x_3, x_2);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get_uint8(x_8, sizeof(void*)*2);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
x_12 = lean_box(0);
x_13 = lean_array_uset(x_3, x_2, x_12);
if (x_10 == 0)
{
lean_dec(x_11);
lean_dec(x_9);
x_14 = x_8;
x_15 = x_5;
goto block_20;
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
lean_inc(x_9);
x_21 = l_Lean_IR_Borrow_isOwned(x_9, x_4, x_5);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_unbox(x_22);
lean_dec(x_22);
if (x_23 == 0)
{
lean_object* x_24; 
lean_dec(x_11);
lean_dec(x_9);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_14 = x_8;
x_15 = x_24;
goto block_20;
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_8);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_26 = lean_ctor_get(x_8, 1);
lean_dec(x_26);
x_27 = lean_ctor_get(x_8, 0);
lean_dec(x_27);
x_28 = lean_ctor_get(x_21, 1);
lean_inc(x_28);
lean_dec(x_21);
x_29 = l_Lean_IR_Borrow_markModified___redArg(x_28);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_31 = lean_box(0);
x_32 = lean_unbox(x_31);
lean_ctor_set_uint8(x_8, sizeof(void*)*2, x_32);
x_14 = x_8;
x_15 = x_30;
goto block_20;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
lean_dec(x_8);
x_33 = lean_ctor_get(x_21, 1);
lean_inc(x_33);
lean_dec(x_21);
x_34 = l_Lean_IR_Borrow_markModified___redArg(x_33);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_37, 0, x_9);
lean_ctor_set(x_37, 1, x_11);
x_38 = lean_unbox(x_36);
lean_ctor_set_uint8(x_37, sizeof(void*)*2, x_38);
x_14 = x_37;
x_15 = x_35;
goto block_20;
}
}
}
block_20:
{
size_t x_16; size_t x_17; lean_object* x_18; 
x_16 = 1;
x_17 = lean_usize_add(x_2, x_16);
x_18 = lean_array_uset(x_13, x_2, x_14);
x_2 = x_17;
x_3 = x_18;
x_5 = x_15;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_updateParamMap(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; size_t x_16; size_t x_17; size_t x_18; size_t x_19; size_t x_20; lean_object* x_21; lean_object* x_22; 
x_6 = lean_ctor_get(x_4, 1);
x_7 = lean_ctor_get(x_4, 0);
lean_dec(x_7);
x_8 = lean_array_get_size(x_6);
x_9 = l_Lean_IR_Borrow_ParamMap_getHash(x_1);
x_10 = 32;
x_11 = lean_uint64_shift_right(x_9, x_10);
x_12 = lean_uint64_xor(x_9, x_11);
x_13 = 16;
x_14 = lean_uint64_shift_right(x_12, x_13);
x_15 = lean_uint64_xor(x_12, x_14);
x_16 = lean_uint64_to_usize(x_15);
x_17 = lean_usize_of_nat(x_8);
lean_dec(x_8);
x_18 = 1;
x_19 = lean_usize_sub(x_17, x_18);
x_20 = lean_usize_land(x_16, x_19);
x_21 = lean_array_uget(x_6, x_20);
lean_dec(x_6);
x_22 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_IR_Borrow_ApplyParamMap_visitFnBody_spec__0___redArg(x_1, x_21);
lean_dec(x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
lean_dec(x_1);
x_23 = lean_box(0);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set(x_4, 0, x_23);
return x_4;
}
else
{
lean_object* x_24; size_t x_25; size_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; uint8_t x_35; 
lean_free_object(x_4);
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_array_size(x_24);
x_26 = 0;
x_27 = l_Array_mapMUnsafe_map___at___Lean_IR_Borrow_updateParamMap_spec__0(x_25, x_26, x_24, x_2, x_3);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
x_30 = lean_ctor_get(x_27, 0);
lean_inc(x_30);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_31 = x_27;
} else {
 lean_dec_ref(x_27);
 x_31 = lean_box(0);
}
x_32 = lean_ctor_get(x_28, 0);
lean_inc(x_32);
x_33 = lean_ctor_get_uint8(x_28, sizeof(void*)*2);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_34 = x_28;
} else {
 lean_dec_ref(x_28);
 x_34 = lean_box(0);
}
x_35 = !lean_is_exclusive(x_29);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_43; size_t x_44; size_t x_45; size_t x_46; lean_object* x_47; uint8_t x_48; 
x_36 = lean_ctor_get(x_29, 0);
x_37 = lean_ctor_get(x_29, 1);
x_38 = lean_box(0);
x_43 = lean_array_get_size(x_37);
x_44 = lean_usize_of_nat(x_43);
lean_dec(x_43);
x_45 = lean_usize_sub(x_44, x_18);
x_46 = lean_usize_land(x_16, x_45);
x_47 = lean_array_uget(x_37, x_46);
x_48 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_Borrow_InitParamMap_visitFnBody_spec__0___redArg(x_1, x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_49 = lean_unsigned_to_nat(1u);
x_50 = lean_nat_add(x_36, x_49);
lean_dec(x_36);
x_51 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_51, 0, x_1);
lean_ctor_set(x_51, 1, x_30);
lean_ctor_set(x_51, 2, x_47);
x_52 = lean_array_uset(x_37, x_46, x_51);
x_53 = lean_unsigned_to_nat(4u);
x_54 = lean_nat_mul(x_50, x_53);
x_55 = lean_unsigned_to_nat(3u);
x_56 = lean_nat_div(x_54, x_55);
lean_dec(x_54);
x_57 = lean_array_get_size(x_52);
x_58 = lean_nat_dec_le(x_56, x_57);
lean_dec(x_57);
lean_dec(x_56);
if (x_58 == 0)
{
lean_object* x_59; 
x_59 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_Borrow_InitParamMap_visitFnBody_spec__1___redArg(x_52);
lean_ctor_set(x_29, 1, x_59);
lean_ctor_set(x_29, 0, x_50);
x_39 = x_29;
goto block_42;
}
else
{
lean_ctor_set(x_29, 1, x_52);
lean_ctor_set(x_29, 0, x_50);
x_39 = x_29;
goto block_42;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_60 = lean_box(0);
x_61 = lean_array_uset(x_37, x_46, x_60);
x_62 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_IR_Borrow_InitParamMap_visitFnBody_spec__4___redArg(x_1, x_30, x_47);
x_63 = lean_array_uset(x_61, x_46, x_62);
lean_ctor_set(x_29, 1, x_63);
x_39 = x_29;
goto block_42;
}
block_42:
{
lean_object* x_40; lean_object* x_41; 
if (lean_is_scalar(x_34)) {
 x_40 = lean_alloc_ctor(0, 2, 1);
} else {
 x_40 = x_34;
}
lean_ctor_set(x_40, 0, x_32);
lean_ctor_set(x_40, 1, x_39);
lean_ctor_set_uint8(x_40, sizeof(void*)*2, x_33);
if (lean_is_scalar(x_31)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_31;
}
lean_ctor_set(x_41, 0, x_38);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_71; size_t x_72; size_t x_73; size_t x_74; lean_object* x_75; uint8_t x_76; 
x_64 = lean_ctor_get(x_29, 0);
x_65 = lean_ctor_get(x_29, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_29);
x_66 = lean_box(0);
x_71 = lean_array_get_size(x_65);
x_72 = lean_usize_of_nat(x_71);
lean_dec(x_71);
x_73 = lean_usize_sub(x_72, x_18);
x_74 = lean_usize_land(x_16, x_73);
x_75 = lean_array_uget(x_65, x_74);
x_76 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_Borrow_InitParamMap_visitFnBody_spec__0___redArg(x_1, x_75);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_77 = lean_unsigned_to_nat(1u);
x_78 = lean_nat_add(x_64, x_77);
lean_dec(x_64);
x_79 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_79, 0, x_1);
lean_ctor_set(x_79, 1, x_30);
lean_ctor_set(x_79, 2, x_75);
x_80 = lean_array_uset(x_65, x_74, x_79);
x_81 = lean_unsigned_to_nat(4u);
x_82 = lean_nat_mul(x_78, x_81);
x_83 = lean_unsigned_to_nat(3u);
x_84 = lean_nat_div(x_82, x_83);
lean_dec(x_82);
x_85 = lean_array_get_size(x_80);
x_86 = lean_nat_dec_le(x_84, x_85);
lean_dec(x_85);
lean_dec(x_84);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; 
x_87 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_Borrow_InitParamMap_visitFnBody_spec__1___redArg(x_80);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_78);
lean_ctor_set(x_88, 1, x_87);
x_67 = x_88;
goto block_70;
}
else
{
lean_object* x_89; 
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_78);
lean_ctor_set(x_89, 1, x_80);
x_67 = x_89;
goto block_70;
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_90 = lean_box(0);
x_91 = lean_array_uset(x_65, x_74, x_90);
x_92 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_IR_Borrow_InitParamMap_visitFnBody_spec__4___redArg(x_1, x_30, x_75);
x_93 = lean_array_uset(x_91, x_74, x_92);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_64);
lean_ctor_set(x_94, 1, x_93);
x_67 = x_94;
goto block_70;
}
block_70:
{
lean_object* x_68; lean_object* x_69; 
if (lean_is_scalar(x_34)) {
 x_68 = lean_alloc_ctor(0, 2, 1);
} else {
 x_68 = x_34;
}
lean_ctor_set(x_68, 0, x_32);
lean_ctor_set(x_68, 1, x_67);
lean_ctor_set_uint8(x_68, sizeof(void*)*2, x_33);
if (lean_is_scalar(x_31)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_31;
}
lean_ctor_set(x_69, 0, x_66);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
}
else
{
lean_object* x_95; lean_object* x_96; uint64_t x_97; uint64_t x_98; uint64_t x_99; uint64_t x_100; uint64_t x_101; uint64_t x_102; uint64_t x_103; size_t x_104; size_t x_105; size_t x_106; size_t x_107; size_t x_108; lean_object* x_109; lean_object* x_110; 
x_95 = lean_ctor_get(x_4, 1);
lean_inc(x_95);
lean_dec(x_4);
x_96 = lean_array_get_size(x_95);
x_97 = l_Lean_IR_Borrow_ParamMap_getHash(x_1);
x_98 = 32;
x_99 = lean_uint64_shift_right(x_97, x_98);
x_100 = lean_uint64_xor(x_97, x_99);
x_101 = 16;
x_102 = lean_uint64_shift_right(x_100, x_101);
x_103 = lean_uint64_xor(x_100, x_102);
x_104 = lean_uint64_to_usize(x_103);
x_105 = lean_usize_of_nat(x_96);
lean_dec(x_96);
x_106 = 1;
x_107 = lean_usize_sub(x_105, x_106);
x_108 = lean_usize_land(x_104, x_107);
x_109 = lean_array_uget(x_95, x_108);
lean_dec(x_95);
x_110 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_IR_Borrow_ApplyParamMap_visitFnBody_spec__0___redArg(x_1, x_109);
lean_dec(x_109);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; lean_object* x_112; 
lean_dec(x_1);
x_111 = lean_box(0);
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_3);
return x_112;
}
else
{
lean_object* x_113; size_t x_114; size_t x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; uint8_t x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_132; size_t x_133; size_t x_134; size_t x_135; lean_object* x_136; uint8_t x_137; 
x_113 = lean_ctor_get(x_110, 0);
lean_inc(x_113);
lean_dec(x_110);
x_114 = lean_array_size(x_113);
x_115 = 0;
x_116 = l_Array_mapMUnsafe_map___at___Lean_IR_Borrow_updateParamMap_spec__0(x_114, x_115, x_113, x_2, x_3);
x_117 = lean_ctor_get(x_116, 1);
lean_inc(x_117);
x_118 = lean_ctor_get(x_117, 1);
lean_inc(x_118);
x_119 = lean_ctor_get(x_116, 0);
lean_inc(x_119);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_120 = x_116;
} else {
 lean_dec_ref(x_116);
 x_120 = lean_box(0);
}
x_121 = lean_ctor_get(x_117, 0);
lean_inc(x_121);
x_122 = lean_ctor_get_uint8(x_117, sizeof(void*)*2);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 x_123 = x_117;
} else {
 lean_dec_ref(x_117);
 x_123 = lean_box(0);
}
x_124 = lean_ctor_get(x_118, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_118, 1);
lean_inc(x_125);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 lean_ctor_release(x_118, 1);
 x_126 = x_118;
} else {
 lean_dec_ref(x_118);
 x_126 = lean_box(0);
}
x_127 = lean_box(0);
x_132 = lean_array_get_size(x_125);
x_133 = lean_usize_of_nat(x_132);
lean_dec(x_132);
x_134 = lean_usize_sub(x_133, x_106);
x_135 = lean_usize_land(x_104, x_134);
x_136 = lean_array_uget(x_125, x_135);
x_137 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_Borrow_InitParamMap_visitFnBody_spec__0___redArg(x_1, x_136);
if (x_137 == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; 
x_138 = lean_unsigned_to_nat(1u);
x_139 = lean_nat_add(x_124, x_138);
lean_dec(x_124);
x_140 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_140, 0, x_1);
lean_ctor_set(x_140, 1, x_119);
lean_ctor_set(x_140, 2, x_136);
x_141 = lean_array_uset(x_125, x_135, x_140);
x_142 = lean_unsigned_to_nat(4u);
x_143 = lean_nat_mul(x_139, x_142);
x_144 = lean_unsigned_to_nat(3u);
x_145 = lean_nat_div(x_143, x_144);
lean_dec(x_143);
x_146 = lean_array_get_size(x_141);
x_147 = lean_nat_dec_le(x_145, x_146);
lean_dec(x_146);
lean_dec(x_145);
if (x_147 == 0)
{
lean_object* x_148; lean_object* x_149; 
x_148 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_Borrow_InitParamMap_visitFnBody_spec__1___redArg(x_141);
if (lean_is_scalar(x_126)) {
 x_149 = lean_alloc_ctor(0, 2, 0);
} else {
 x_149 = x_126;
}
lean_ctor_set(x_149, 0, x_139);
lean_ctor_set(x_149, 1, x_148);
x_128 = x_149;
goto block_131;
}
else
{
lean_object* x_150; 
if (lean_is_scalar(x_126)) {
 x_150 = lean_alloc_ctor(0, 2, 0);
} else {
 x_150 = x_126;
}
lean_ctor_set(x_150, 0, x_139);
lean_ctor_set(x_150, 1, x_141);
x_128 = x_150;
goto block_131;
}
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_151 = lean_box(0);
x_152 = lean_array_uset(x_125, x_135, x_151);
x_153 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_IR_Borrow_InitParamMap_visitFnBody_spec__4___redArg(x_1, x_119, x_136);
x_154 = lean_array_uset(x_152, x_135, x_153);
if (lean_is_scalar(x_126)) {
 x_155 = lean_alloc_ctor(0, 2, 0);
} else {
 x_155 = x_126;
}
lean_ctor_set(x_155, 0, x_124);
lean_ctor_set(x_155, 1, x_154);
x_128 = x_155;
goto block_131;
}
block_131:
{
lean_object* x_129; lean_object* x_130; 
if (lean_is_scalar(x_123)) {
 x_129 = lean_alloc_ctor(0, 2, 1);
} else {
 x_129 = x_123;
}
lean_ctor_set(x_129, 0, x_121);
lean_ctor_set(x_129, 1, x_128);
lean_ctor_set_uint8(x_129, sizeof(void*)*2, x_122);
if (lean_is_scalar(x_120)) {
 x_130 = lean_alloc_ctor(0, 2, 0);
} else {
 x_130 = x_120;
}
lean_ctor_set(x_130, 0, x_127);
lean_ctor_set(x_130, 1, x_129);
return x_130;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_Borrow_updateParamMap_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = l_Array_mapMUnsafe_map___at___Lean_IR_Borrow_updateParamMap_spec__0(x_6, x_7, x_3, x_4, x_5);
lean_dec(x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_updateParamMap___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_Borrow_updateParamMap(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_panic___at___Lean_IR_Borrow_getParamInfo_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__0), 4, 0);
return x_1;
}
}
static lean_object* _init_l_panic___at___Lean_IR_Borrow_getParamInfo_spec__0___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__1___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_panic___at___Lean_IR_Borrow_getParamInfo_spec__0___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__2___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_panic___at___Lean_IR_Borrow_getParamInfo_spec__0___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__3), 4, 0);
return x_1;
}
}
static lean_object* _init_l_panic___at___Lean_IR_Borrow_getParamInfo_spec__0___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__4___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_panic___at___Lean_IR_Borrow_getParamInfo_spec__0___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__5___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_panic___at___Lean_IR_Borrow_getParamInfo_spec__0___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__6), 4, 0);
return x_1;
}
}
static lean_object* _init_l_panic___at___Lean_IR_Borrow_getParamInfo_spec__0___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_empty(lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_IR_Borrow_getParamInfo_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_4 = l_panic___at___Lean_IR_Borrow_getParamInfo_spec__0___closed__0;
x_5 = l_panic___at___Lean_IR_Borrow_getParamInfo_spec__0___closed__1;
x_6 = l_panic___at___Lean_IR_Borrow_getParamInfo_spec__0___closed__2;
x_7 = l_panic___at___Lean_IR_Borrow_getParamInfo_spec__0___closed__3;
x_8 = l_panic___at___Lean_IR_Borrow_getParamInfo_spec__0___closed__4;
x_9 = l_panic___at___Lean_IR_Borrow_getParamInfo_spec__0___closed__5;
x_10 = l_panic___at___Lean_IR_Borrow_getParamInfo_spec__0___closed__6;
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_4);
lean_ctor_set(x_11, 1, x_5);
x_12 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_6);
lean_ctor_set(x_12, 2, x_7);
lean_ctor_set(x_12, 3, x_8);
lean_ctor_set(x_12, 4, x_9);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
lean_inc(x_13);
x_14 = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_14, 0, x_13);
lean_inc(x_13);
x_15 = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_15, 0, x_13);
lean_inc(x_13);
x_16 = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(x_16, 0, x_13);
lean_inc(x_13);
x_17 = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(x_17, 0, x_13);
lean_inc(x_13);
x_18 = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(x_18, 0, lean_box(0));
lean_closure_set(x_18, 1, lean_box(0));
lean_closure_set(x_18, 2, x_13);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_14);
lean_inc(x_13);
x_20 = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(x_20, 0, lean_box(0));
lean_closure_set(x_20, 1, lean_box(0));
lean_closure_set(x_20, 2, x_13);
x_21 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
lean_ctor_set(x_21, 2, x_15);
lean_ctor_set(x_21, 3, x_16);
lean_ctor_set(x_21, 4, x_17);
x_22 = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(x_22, 0, lean_box(0));
lean_closure_set(x_22, 1, lean_box(0));
lean_closure_set(x_22, 2, x_13);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_panic___at___Lean_IR_Borrow_getParamInfo_spec__0___closed__7;
x_25 = l_instInhabitedOfMonad___redArg(x_23, x_24);
x_26 = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_26, 0, x_25);
x_27 = lean_panic_fn(x_26, x_1);
x_28 = lean_apply_2(x_27, x_2, x_3);
return x_28;
}
}
static lean_object* _init_l_Lean_IR_Borrow_getParamInfo___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.IR.Borrow.getParamInfo", 27, 27);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_Borrow_getParamInfo___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_IR_Borrow_ApplyParamMap_visitFnBody___closed__2;
x_2 = lean_unsigned_to_nat(21u);
x_3 = lean_unsigned_to_nat(203u);
x_4 = l_Lean_IR_Borrow_getParamInfo___closed__0;
x_5 = l_Lean_IR_Borrow_ApplyParamMap_visitFnBody___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_IR_Borrow_getParamInfo___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_IR_Borrow_ApplyParamMap_visitFnBody___closed__2;
x_2 = lean_unsigned_to_nat(11u);
x_3 = lean_unsigned_to_nat(204u);
x_4 = l_Lean_IR_Borrow_getParamInfo___closed__0;
x_5 = l_Lean_IR_Borrow_ApplyParamMap_visitFnBody___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_getParamInfo(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; size_t x_16; size_t x_17; size_t x_18; size_t x_19; size_t x_20; lean_object* x_21; lean_object* x_22; 
x_6 = lean_ctor_get(x_4, 1);
x_7 = lean_ctor_get(x_4, 0);
lean_dec(x_7);
x_8 = lean_array_get_size(x_6);
x_9 = l_Lean_IR_Borrow_ParamMap_getHash(x_1);
x_10 = 32;
x_11 = lean_uint64_shift_right(x_9, x_10);
x_12 = lean_uint64_xor(x_9, x_11);
x_13 = 16;
x_14 = lean_uint64_shift_right(x_12, x_13);
x_15 = lean_uint64_xor(x_12, x_14);
x_16 = lean_uint64_to_usize(x_15);
x_17 = lean_usize_of_nat(x_8);
lean_dec(x_8);
x_18 = 1;
x_19 = lean_usize_sub(x_17, x_18);
x_20 = lean_usize_land(x_16, x_19);
x_21 = lean_array_uget(x_6, x_20);
lean_dec(x_6);
x_22 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_IR_Borrow_ApplyParamMap_visitFnBody_spec__0___redArg(x_1, x_21);
lean_dec(x_21);
if (lean_obj_tag(x_22) == 0)
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_1, 0);
lean_inc(x_23);
lean_dec(x_1);
x_24 = lean_ctor_get(x_2, 0);
lean_inc(x_24);
x_25 = lean_ir_find_env_decl(x_24, x_23);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; 
lean_free_object(x_4);
x_26 = l_Lean_IR_Borrow_getParamInfo___closed__1;
x_27 = l_panic___at___Lean_IR_Borrow_getParamInfo_spec__0(x_26, x_2, x_3);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_2);
x_28 = lean_ctor_get(x_25, 0);
lean_inc(x_28);
lean_dec(x_25);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set(x_4, 0, x_29);
return x_4;
}
}
else
{
lean_object* x_30; lean_object* x_31; 
lean_free_object(x_4);
lean_dec(x_1);
x_30 = l_Lean_IR_Borrow_getParamInfo___closed__2;
x_31 = l_panic___at___Lean_IR_Borrow_getParamInfo_spec__0(x_30, x_2, x_3);
return x_31;
}
}
else
{
lean_object* x_32; 
lean_dec(x_2);
lean_dec(x_1);
x_32 = lean_ctor_get(x_22, 0);
lean_inc(x_32);
lean_dec(x_22);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set(x_4, 0, x_32);
return x_4;
}
}
else
{
lean_object* x_33; lean_object* x_34; uint64_t x_35; uint64_t x_36; uint64_t x_37; uint64_t x_38; uint64_t x_39; uint64_t x_40; uint64_t x_41; size_t x_42; size_t x_43; size_t x_44; size_t x_45; size_t x_46; lean_object* x_47; lean_object* x_48; 
x_33 = lean_ctor_get(x_4, 1);
lean_inc(x_33);
lean_dec(x_4);
x_34 = lean_array_get_size(x_33);
x_35 = l_Lean_IR_Borrow_ParamMap_getHash(x_1);
x_36 = 32;
x_37 = lean_uint64_shift_right(x_35, x_36);
x_38 = lean_uint64_xor(x_35, x_37);
x_39 = 16;
x_40 = lean_uint64_shift_right(x_38, x_39);
x_41 = lean_uint64_xor(x_38, x_40);
x_42 = lean_uint64_to_usize(x_41);
x_43 = lean_usize_of_nat(x_34);
lean_dec(x_34);
x_44 = 1;
x_45 = lean_usize_sub(x_43, x_44);
x_46 = lean_usize_land(x_42, x_45);
x_47 = lean_array_uget(x_33, x_46);
lean_dec(x_33);
x_48 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_IR_Borrow_ApplyParamMap_visitFnBody_spec__0___redArg(x_1, x_47);
lean_dec(x_47);
if (lean_obj_tag(x_48) == 0)
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_1, 0);
lean_inc(x_49);
lean_dec(x_1);
x_50 = lean_ctor_get(x_2, 0);
lean_inc(x_50);
x_51 = lean_ir_find_env_decl(x_50, x_49);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; 
x_52 = l_Lean_IR_Borrow_getParamInfo___closed__1;
x_53 = l_panic___at___Lean_IR_Borrow_getParamInfo_spec__0(x_52, x_2, x_3);
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_2);
x_54 = lean_ctor_get(x_51, 0);
lean_inc(x_54);
lean_dec(x_51);
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
lean_dec(x_54);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_3);
return x_56;
}
}
else
{
lean_object* x_57; lean_object* x_58; 
lean_dec(x_1);
x_57 = l_Lean_IR_Borrow_getParamInfo___closed__2;
x_58 = l_panic___at___Lean_IR_Borrow_getParamInfo_spec__0(x_57, x_2, x_3);
return x_58;
}
}
else
{
lean_object* x_59; lean_object* x_60; 
lean_dec(x_2);
lean_dec(x_1);
x_59 = lean_ctor_get(x_48, 0);
lean_inc(x_59);
lean_dec(x_48);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_3);
return x_60;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_forM_loop___at___Lean_IR_Borrow_ownArgsUsingParams_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_5, x_8);
if (x_9 == 1)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
lean_dec(x_1);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_7);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_sub(x_5, x_12);
lean_dec(x_5);
x_14 = lean_nat_sub(x_4, x_13);
x_15 = lean_nat_sub(x_14, x_12);
lean_dec(x_14);
lean_inc(x_1);
x_16 = lean_array_get(x_1, x_2, x_15);
x_17 = lean_ctor_get_uint8(x_16, sizeof(void*)*2);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_array_fget(x_3, x_15);
lean_dec(x_15);
x_19 = l_Lean_IR_Borrow_ownArg(x_18, x_6, x_7);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_5 = x_13;
x_7 = x_20;
goto _start;
}
else
{
lean_dec(x_15);
x_5 = x_13;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_forM_loop___at___Lean_IR_Borrow_ownArgsUsingParams_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Nat_forM_loop___at___Lean_IR_Borrow_ownArgsUsingParams_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_ownArgsUsingParams(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = l_Lean_IR_instInhabitedParam;
x_6 = lean_array_get_size(x_1);
lean_inc(x_6);
x_7 = l_Nat_forM_loop___at___Lean_IR_Borrow_ownArgsUsingParams_spec__0___redArg(x_5, x_2, x_1, x_6, x_6, x_3, x_4);
lean_dec(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Nat_forM_loop___at___Lean_IR_Borrow_ownArgsUsingParams_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Nat_forM_loop___at___Lean_IR_Borrow_ownArgsUsingParams_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Nat_forM_loop___at___Lean_IR_Borrow_ownArgsUsingParams_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Nat_forM_loop___at___Lean_IR_Borrow_ownArgsUsingParams_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_ownArgsUsingParams___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_Borrow_ownArgsUsingParams(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Nat_forM_loop___at___Lean_IR_Borrow_ownParamsUsingArgs_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_5, x_8);
if (x_9 == 1)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
lean_dec(x_2);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_7);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_sub(x_5, x_12);
lean_dec(x_5);
x_14 = lean_nat_sub(x_4, x_13);
x_15 = lean_nat_sub(x_14, x_12);
lean_dec(x_14);
x_16 = lean_array_fget(x_1, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
x_18 = l_Lean_IR_Borrow_isOwned(x_17, x_6, x_7);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_unbox(x_19);
lean_dec(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_15);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_5 = x_13;
x_7 = x_21;
goto _start;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_18, 1);
lean_inc(x_23);
lean_dec(x_18);
lean_inc(x_2);
x_24 = lean_array_get(x_2, x_3, x_15);
lean_dec(x_15);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec(x_24);
x_26 = l_Lean_IR_Borrow_ownVar(x_25, x_6, x_23);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_5 = x_13;
x_7 = x_27;
goto _start;
}
}
else
{
lean_dec(x_15);
x_5 = x_13;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_forM_loop___at___Lean_IR_Borrow_ownParamsUsingArgs_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Nat_forM_loop___at___Lean_IR_Borrow_ownParamsUsingArgs_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_ownParamsUsingArgs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = l_Lean_IR_instInhabitedParam;
x_6 = lean_array_get_size(x_1);
lean_inc(x_6);
x_7 = l_Nat_forM_loop___at___Lean_IR_Borrow_ownParamsUsingArgs_spec__0___redArg(x_1, x_5, x_2, x_6, x_6, x_3, x_4);
lean_dec(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Nat_forM_loop___at___Lean_IR_Borrow_ownParamsUsingArgs_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Nat_forM_loop___at___Lean_IR_Borrow_ownParamsUsingArgs_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Nat_forM_loop___at___Lean_IR_Borrow_ownParamsUsingArgs_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Nat_forM_loop___at___Lean_IR_Borrow_ownParamsUsingArgs_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_ownParamsUsingArgs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_Borrow_ownParamsUsingArgs(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_Borrow_ownArgsIfParam_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_14; 
x_14 = lean_usize_dec_eq(x_3, x_4);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_5);
x_15 = lean_array_uget(x_2, x_3);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_ctor_get(x_1, 3);
x_18 = l_Lean_RBNode_findCore___at___Lean_IR_UniqueIds_checkId_spec__0___redArg(x_17, x_16);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
lean_dec(x_16);
x_19 = lean_box(0);
x_8 = x_19;
x_9 = x_7;
goto block_13;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_18);
x_20 = l_Lean_IR_Borrow_ownVar(x_16, x_6, x_7);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_8 = x_21;
x_9 = x_22;
goto block_13;
}
}
else
{
lean_object* x_23; 
x_23 = lean_box(0);
x_8 = x_23;
x_9 = x_7;
goto block_13;
}
}
else
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_5);
lean_ctor_set(x_24, 1, x_7);
return x_24;
}
block_13:
{
size_t x_10; size_t x_11; 
x_10 = 1;
x_11 = lean_usize_add(x_3, x_10);
x_3 = x_11;
x_5 = x_8;
x_7 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_ownArgsIfParam(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_array_get_size(x_1);
x_6 = lean_box(0);
x_7 = lean_nat_dec_lt(x_4, x_5);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_5);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = lean_nat_dec_le(x_5, x_5);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_5);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_3);
return x_10;
}
else
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = 0;
x_12 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_13 = l_Array_foldlMUnsafe_fold___at___Lean_IR_Borrow_ownArgsIfParam_spec__0(x_2, x_1, x_11, x_12, x_6, x_2, x_3);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_Borrow_ownArgsIfParam_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = l_Array_foldlMUnsafe_fold___at___Lean_IR_Borrow_ownArgsIfParam_spec__0(x_1, x_2, x_8, x_9, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_ownArgsIfParam___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_Borrow_ownArgsIfParam(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_collectExpr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_6 = l_Lean_IR_Borrow_ownVar(x_1, x_3, x_4);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = l_Lean_IR_Borrow_ownArgsIfParam(x_5, x_3, x_7);
lean_dec(x_3);
lean_dec(x_5);
return x_8;
}
case 1:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
lean_dec(x_2);
x_10 = l_Lean_IR_Borrow_ownVar(x_1, x_3, x_4);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = l_Lean_IR_Borrow_ownVar(x_9, x_3, x_11);
lean_dec(x_3);
return x_12;
}
case 2:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_ctor_get(x_2, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_2, 2);
lean_inc(x_14);
lean_dec(x_2);
x_15 = l_Lean_IR_Borrow_ownVar(x_1, x_3, x_4);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = l_Lean_IR_Borrow_ownVar(x_13, x_3, x_16);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = l_Lean_IR_Borrow_ownArgsIfParam(x_14, x_3, x_18);
lean_dec(x_3);
lean_dec(x_14);
return x_19;
}
case 3:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_20 = lean_ctor_get(x_2, 1);
lean_inc(x_20);
lean_dec(x_2);
lean_inc(x_20);
x_35 = l_Lean_IR_Borrow_isOwned(x_20, x_3, x_4);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_unbox(x_36);
lean_dec(x_36);
if (x_37 == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_dec(x_35);
x_21 = x_3;
x_22 = x_38;
goto block_34;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_35, 1);
lean_inc(x_39);
lean_dec(x_35);
lean_inc(x_1);
x_40 = l_Lean_IR_Borrow_ownVar(x_1, x_3, x_39);
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec(x_40);
x_21 = x_3;
x_22 = x_41;
goto block_34;
}
block_34:
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = l_Lean_IR_Borrow_isOwned(x_1, x_21, x_22);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_unbox(x_24);
lean_dec(x_24);
if (x_25 == 0)
{
uint8_t x_26; 
lean_dec(x_21);
lean_dec(x_20);
x_26 = !lean_is_exclusive(x_23);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_23, 0);
lean_dec(x_27);
x_28 = lean_box(0);
lean_ctor_set(x_23, 0, x_28);
return x_23;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_23, 1);
lean_inc(x_29);
lean_dec(x_23);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_23, 1);
lean_inc(x_32);
lean_dec(x_23);
x_33 = l_Lean_IR_Borrow_ownVar(x_20, x_21, x_32);
lean_dec(x_21);
return x_33;
}
}
}
case 6:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_42 = lean_ctor_get(x_2, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_2, 1);
lean_inc(x_43);
lean_dec(x_2);
x_44 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_44, 0, x_42);
lean_inc(x_3);
x_45 = l_Lean_IR_Borrow_getParamInfo(x_44, x_3, x_4);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = l_Lean_IR_Borrow_ownVar(x_1, x_3, x_47);
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
lean_dec(x_48);
x_50 = l_Lean_IR_Borrow_ownArgsUsingParams(x_43, x_46, x_3, x_49);
lean_dec(x_3);
lean_dec(x_46);
lean_dec(x_43);
return x_50;
}
case 7:
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_51 = lean_ctor_get(x_2, 1);
lean_inc(x_51);
lean_dec(x_2);
x_52 = l_Lean_IR_Borrow_ownVar(x_1, x_3, x_4);
x_53 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
lean_dec(x_52);
x_54 = l_Lean_IR_Borrow_ownArgs(x_51, x_3, x_53);
lean_dec(x_3);
lean_dec(x_51);
return x_54;
}
case 8:
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_55 = lean_ctor_get(x_2, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_2, 1);
lean_inc(x_56);
lean_dec(x_2);
x_57 = l_Lean_IR_Borrow_ownVar(x_1, x_3, x_4);
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
lean_dec(x_57);
x_59 = l_Lean_IR_Borrow_ownVar(x_55, x_3, x_58);
x_60 = lean_ctor_get(x_59, 1);
lean_inc(x_60);
lean_dec(x_59);
x_61 = l_Lean_IR_Borrow_ownArgs(x_56, x_3, x_60);
lean_dec(x_3);
lean_dec(x_56);
return x_61;
}
default: 
{
lean_object* x_62; lean_object* x_63; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_62 = lean_box(0);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_4);
return x_63;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_preserveTailCall(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
if (lean_obj_tag(x_2) == 6)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_12 = x_2;
} else {
 lean_dec_ref(x_2);
 x_12 = lean_box(0);
}
if (lean_obj_tag(x_3) == 11)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_3, 0);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_22, 0);
x_24 = lean_ctor_get(x_4, 2);
lean_inc(x_24);
x_25 = lean_name_eq(x_24, x_10);
lean_dec(x_24);
if (x_25 == 0)
{
x_13 = x_25;
goto block_21;
}
else
{
uint8_t x_26; 
x_26 = lean_nat_dec_eq(x_1, x_23);
x_13 = x_26;
goto block_21;
}
}
else
{
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_4);
x_6 = x_5;
goto block_9;
}
}
else
{
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_4);
x_6 = x_5;
goto block_9;
}
block_21:
{
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_4);
x_14 = lean_box(0);
if (lean_is_scalar(x_12)) {
 x_15 = lean_alloc_ctor(0, 2, 0);
} else {
 x_15 = x_12;
 lean_ctor_set_tag(x_15, 0);
}
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_5);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_12);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_10);
lean_inc(x_4);
x_17 = l_Lean_IR_Borrow_getParamInfo(x_16, x_4, x_5);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_IR_Borrow_ownParamsUsingArgs(x_11, x_18, x_4, x_19);
lean_dec(x_4);
lean_dec(x_18);
lean_dec(x_11);
return x_20;
}
}
}
else
{
lean_dec(x_4);
lean_dec(x_2);
x_6 = x_5;
goto block_9;
}
block_9:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_preserveTailCall___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_Borrow_preserveTailCall(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_Borrow_updateParamSet_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_box(0);
x_9 = l_Lean_RBNode_insert___at___Lean_IR_mkIndexSet_spec__0___redArg(x_4, x_7, x_8);
x_10 = 1;
x_11 = lean_usize_add(x_2, x_10);
x_2 = x_11;
x_4 = x_9;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_updateParamSet(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 3);
lean_inc(x_6);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_get_size(x_2);
x_9 = lean_nat_dec_lt(x_7, x_8);
if (x_9 == 0)
{
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_1;
}
else
{
uint8_t x_10; 
x_10 = lean_nat_dec_le(x_8, x_8);
if (x_10 == 0)
{
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_1;
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_1);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_1, 3);
lean_dec(x_12);
x_13 = lean_ctor_get(x_1, 2);
lean_dec(x_13);
x_14 = lean_ctor_get(x_1, 1);
lean_dec(x_14);
x_15 = lean_ctor_get(x_1, 0);
lean_dec(x_15);
x_16 = 0;
x_17 = lean_usize_of_nat(x_8);
lean_dec(x_8);
x_18 = l_Array_foldlMUnsafe_fold___at___Lean_IR_Borrow_updateParamSet_spec__0(x_2, x_16, x_17, x_6);
lean_ctor_set(x_1, 3, x_18);
return x_1;
}
else
{
size_t x_19; size_t x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_1);
x_19 = 0;
x_20 = lean_usize_of_nat(x_8);
lean_dec(x_8);
x_21 = l_Array_foldlMUnsafe_fold___at___Lean_IR_Borrow_updateParamSet_spec__0(x_2, x_19, x_20, x_6);
x_22 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_22, 0, x_3);
lean_ctor_set(x_22, 1, x_4);
lean_ctor_set(x_22, 2, x_5);
lean_ctor_set(x_22, 3, x_21);
return x_22;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_Borrow_updateParamSet_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___Lean_IR_Borrow_updateParamSet_spec__0(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_updateParamSet___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_Borrow_updateParamSet(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_Borrow_collectFnBody_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_14; 
x_14 = lean_usize_dec_eq(x_2, x_3);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_4);
x_15 = lean_array_uget(x_1, x_2);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
lean_inc(x_5);
x_17 = l_Lean_IR_Borrow_collectFnBody(x_16, x_5, x_6);
x_7 = x_17;
goto block_13;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_18);
lean_dec(x_15);
lean_inc(x_5);
x_19 = l_Lean_IR_Borrow_collectFnBody(x_18, x_5, x_6);
x_7 = x_19;
goto block_13;
}
}
else
{
lean_object* x_20; 
lean_dec(x_5);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_4);
lean_ctor_set(x_20, 1, x_6);
return x_20;
}
block_13:
{
lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = 1;
x_11 = lean_usize_add(x_2, x_10);
x_2 = x_11;
x_4 = x_8;
x_6 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_collectFnBody(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 3);
lean_inc(x_6);
lean_dec(x_1);
lean_inc(x_2);
lean_inc(x_6);
x_7 = l_Lean_IR_Borrow_collectFnBody(x_6, x_2, x_3);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
lean_inc(x_2);
lean_inc(x_5);
lean_inc(x_4);
x_9 = l_Lean_IR_Borrow_collectExpr(x_4, x_5, x_2, x_8);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = l_Lean_IR_Borrow_preserveTailCall(x_4, x_5, x_6, x_2, x_10);
lean_dec(x_6);
lean_dec(x_4);
return x_11;
}
case 1:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 2);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 3);
lean_inc(x_15);
lean_dec(x_1);
lean_inc(x_2);
x_16 = l_Lean_IR_Borrow_updateParamSet(x_2, x_13);
lean_dec(x_13);
x_17 = l_Lean_IR_Borrow_collectFnBody(x_14, x_16, x_3);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_17, 1);
x_20 = lean_ctor_get(x_17, 0);
lean_dec(x_20);
x_21 = lean_ctor_get(x_2, 2);
lean_inc(x_21);
lean_ctor_set_tag(x_17, 1);
lean_ctor_set(x_17, 1, x_12);
lean_ctor_set(x_17, 0, x_21);
x_22 = l_Lean_IR_Borrow_updateParamMap(x_17, x_2, x_19);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_1 = x_15;
x_3 = x_23;
goto _start;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_17, 1);
lean_inc(x_25);
lean_dec(x_17);
x_26 = lean_ctor_get(x_2, 2);
lean_inc(x_26);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_12);
x_28 = l_Lean_IR_Borrow_updateParamMap(x_27, x_2, x_25);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_1 = x_15;
x_3 = x_29;
goto _start;
}
}
case 10:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_31 = lean_ctor_get(x_1, 3);
lean_inc(x_31);
lean_dec(x_1);
x_32 = lean_unsigned_to_nat(0u);
x_33 = lean_array_get_size(x_31);
x_34 = lean_box(0);
x_35 = lean_nat_dec_lt(x_32, x_33);
if (x_35 == 0)
{
lean_object* x_36; 
lean_dec(x_33);
lean_dec(x_31);
lean_dec(x_2);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_3);
return x_36;
}
else
{
uint8_t x_37; 
x_37 = lean_nat_dec_le(x_33, x_33);
if (x_37 == 0)
{
lean_object* x_38; 
lean_dec(x_33);
lean_dec(x_31);
lean_dec(x_2);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_34);
lean_ctor_set(x_38, 1, x_3);
return x_38;
}
else
{
size_t x_39; size_t x_40; lean_object* x_41; 
x_39 = 0;
x_40 = lean_usize_of_nat(x_33);
lean_dec(x_33);
x_41 = l_Array_foldlMUnsafe_fold___at___Lean_IR_Borrow_collectFnBody_spec__0(x_31, x_39, x_40, x_34, x_2, x_3);
lean_dec(x_31);
return x_41;
}
}
}
case 12:
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_1);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_43 = lean_ctor_get(x_1, 0);
x_44 = lean_ctor_get(x_1, 1);
x_45 = lean_ctor_get(x_2, 2);
lean_inc(x_45);
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 1, x_43);
lean_ctor_set(x_1, 0, x_45);
lean_inc(x_2);
x_46 = l_Lean_IR_Borrow_getParamInfo(x_1, x_2, x_3);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = l_Lean_IR_Borrow_ownArgsUsingParams(x_44, x_47, x_2, x_48);
x_50 = lean_ctor_get(x_49, 1);
lean_inc(x_50);
lean_dec(x_49);
x_51 = l_Lean_IR_Borrow_ownParamsUsingArgs(x_44, x_47, x_2, x_50);
lean_dec(x_2);
lean_dec(x_47);
lean_dec(x_44);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_52 = lean_ctor_get(x_1, 0);
x_53 = lean_ctor_get(x_1, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_1);
x_54 = lean_ctor_get(x_2, 2);
lean_inc(x_54);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_52);
lean_inc(x_2);
x_56 = l_Lean_IR_Borrow_getParamInfo(x_55, x_2, x_3);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = l_Lean_IR_Borrow_ownArgsUsingParams(x_53, x_57, x_2, x_58);
x_60 = lean_ctor_get(x_59, 1);
lean_inc(x_60);
lean_dec(x_59);
x_61 = l_Lean_IR_Borrow_ownParamsUsingArgs(x_53, x_57, x_2, x_60);
lean_dec(x_2);
lean_dec(x_57);
lean_dec(x_53);
return x_61;
}
}
default: 
{
uint8_t x_62; 
x_62 = l_Lean_IR_FnBody_isTerminal(x_1);
if (x_62 == 0)
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_63; 
x_63 = lean_ctor_get(x_1, 3);
lean_inc(x_63);
lean_dec(x_1);
x_1 = x_63;
goto _start;
}
case 1:
{
lean_object* x_65; 
x_65 = lean_ctor_get(x_1, 3);
lean_inc(x_65);
lean_dec(x_1);
x_1 = x_65;
goto _start;
}
case 2:
{
lean_object* x_67; 
x_67 = lean_ctor_get(x_1, 3);
lean_inc(x_67);
lean_dec(x_1);
x_1 = x_67;
goto _start;
}
case 3:
{
lean_object* x_69; 
x_69 = lean_ctor_get(x_1, 2);
lean_inc(x_69);
lean_dec(x_1);
x_1 = x_69;
goto _start;
}
case 4:
{
lean_object* x_71; 
x_71 = lean_ctor_get(x_1, 3);
lean_inc(x_71);
lean_dec(x_1);
x_1 = x_71;
goto _start;
}
case 5:
{
lean_object* x_73; 
x_73 = lean_ctor_get(x_1, 5);
lean_inc(x_73);
lean_dec(x_1);
x_1 = x_73;
goto _start;
}
case 6:
{
lean_object* x_75; 
x_75 = lean_ctor_get(x_1, 2);
lean_inc(x_75);
lean_dec(x_1);
x_1 = x_75;
goto _start;
}
case 7:
{
lean_object* x_77; 
x_77 = lean_ctor_get(x_1, 2);
lean_inc(x_77);
lean_dec(x_1);
x_1 = x_77;
goto _start;
}
case 8:
{
lean_object* x_79; 
x_79 = lean_ctor_get(x_1, 1);
lean_inc(x_79);
lean_dec(x_1);
x_1 = x_79;
goto _start;
}
case 9:
{
lean_object* x_81; 
x_81 = lean_ctor_get(x_1, 1);
lean_inc(x_81);
lean_dec(x_1);
x_1 = x_81;
goto _start;
}
default: 
{
goto _start;
}
}
}
else
{
lean_object* x_84; lean_object* x_85; 
lean_dec(x_2);
lean_dec(x_1);
x_84 = lean_box(0);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_3);
return x_85;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_Borrow_collectFnBody_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l_Array_foldlMUnsafe_fold___at___Lean_IR_Borrow_collectFnBody_spec__0(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_collectDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 3);
lean_inc(x_6);
lean_dec(x_1);
x_7 = l_Lean_IR_Borrow_updateParamSet(x_2, x_5);
lean_dec(x_5);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_7, 2);
lean_dec(x_9);
lean_inc(x_4);
lean_ctor_set(x_7, 2, x_4);
lean_inc(x_7);
x_10 = l_Lean_IR_Borrow_collectFnBody(x_6, x_7, x_3);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_4);
x_13 = l_Lean_IR_Borrow_updateParamMap(x_12, x_7, x_11);
lean_dec(x_7);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_14 = lean_ctor_get(x_7, 0);
x_15 = lean_ctor_get(x_7, 1);
x_16 = lean_ctor_get(x_7, 3);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_7);
lean_inc(x_4);
x_17 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_15);
lean_ctor_set(x_17, 2, x_4);
lean_ctor_set(x_17, 3, x_16);
lean_inc(x_17);
x_18 = l_Lean_IR_Borrow_collectFnBody(x_6, x_17, x_3);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_4);
x_21 = l_Lean_IR_Borrow_updateParamMap(x_20, x_17, x_19);
lean_dec(x_17);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_2);
lean_dec(x_1);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_3);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_whileModifing(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_box(0);
x_6 = lean_unbox(x_5);
lean_ctor_set_uint8(x_3, sizeof(void*)*2, x_6);
lean_inc(x_1);
lean_inc(x_2);
x_7 = lean_apply_2(x_1, x_2, x_3);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_7, 1);
x_10 = lean_ctor_get(x_7, 0);
lean_dec(x_10);
x_11 = lean_ctor_get_uint8(x_9, sizeof(void*)*2);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_box(0);
lean_ctor_set(x_7, 0, x_12);
return x_7;
}
else
{
lean_free_object(x_7);
x_3 = x_9;
goto _start;
}
}
else
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_7, 1);
lean_inc(x_14);
lean_dec(x_7);
x_15 = lean_ctor_get_uint8(x_14, sizeof(void*)*2);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_2);
lean_dec(x_1);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_14);
return x_17;
}
else
{
x_3 = x_14;
goto _start;
}
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_19 = lean_ctor_get(x_3, 0);
x_20 = lean_ctor_get(x_3, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_3);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_20);
x_23 = lean_unbox(x_21);
lean_ctor_set_uint8(x_22, sizeof(void*)*2, x_23);
lean_inc(x_1);
lean_inc(x_2);
x_24 = lean_apply_2(x_1, x_2, x_22);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_26 = x_24;
} else {
 lean_dec_ref(x_24);
 x_26 = lean_box(0);
}
x_27 = lean_ctor_get_uint8(x_25, sizeof(void*)*2);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_2);
lean_dec(x_1);
x_28 = lean_box(0);
if (lean_is_scalar(x_26)) {
 x_29 = lean_alloc_ctor(0, 2, 0);
} else {
 x_29 = x_26;
}
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_25);
return x_29;
}
else
{
lean_dec(x_26);
x_3 = x_25;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_Borrow_collectDecls_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_2, x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; 
lean_dec(x_4);
x_8 = lean_array_uget(x_1, x_2);
lean_inc(x_5);
x_9 = l_Lean_IR_Borrow_collectDecl(x_8, x_5, x_6);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = 1;
x_13 = lean_usize_add(x_2, x_12);
x_2 = x_13;
x_4 = x_10;
x_6 = x_11;
goto _start;
}
else
{
lean_object* x_15; 
lean_dec(x_5);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_4);
lean_ctor_set(x_15, 1, x_6);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_collectDecls___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_box(0);
x_7 = lean_nat_dec_lt(x_1, x_2);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_5);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = lean_nat_dec_le(x_2, x_2);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_4);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_5);
return x_10;
}
else
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = 0;
x_12 = lean_usize_of_nat(x_2);
x_13 = l_Array_foldlMUnsafe_fold___at___Lean_IR_Borrow_collectDecls_spec__0(x_3, x_11, x_12, x_6, x_4, x_5);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_collectDecls(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_array_get_size(x_3);
x_6 = lean_alloc_closure((void*)(l_Lean_IR_Borrow_collectDecls___lam__0___boxed), 5, 3);
lean_closure_set(x_6, 0, x_4);
lean_closure_set(x_6, 1, x_5);
lean_closure_set(x_6, 2, x_3);
x_7 = l_Lean_IR_Borrow_whileModifing(x_6, x_1, x_2);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_7, 1);
x_10 = lean_ctor_get(x_7, 0);
lean_dec(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_ctor_set(x_7, 0, x_11);
return x_7;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_12);
lean_dec(x_7);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_Borrow_collectDecls_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l_Array_foldlMUnsafe_fold___at___Lean_IR_Borrow_collectDecls_spec__0(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_collectDecls___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_Borrow_collectDecls___lam__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_IR_Borrow_infer___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_IR_Borrow_mkInitParamMap___closed__2;
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_Borrow_infer___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_Borrow_infer___closed__0;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_infer(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_3 = lean_box(0);
x_4 = lean_box(0);
lean_inc(x_2);
lean_inc(x_1);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
x_6 = l_Lean_IR_Borrow_infer___closed__1;
x_7 = lean_box(0);
x_8 = l_Lean_IR_Borrow_mkInitParamMap(x_1, x_2);
lean_dec(x_2);
x_9 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unbox(x_7);
lean_ctor_set_uint8(x_9, sizeof(void*)*2, x_10);
x_11 = l_Lean_IR_Borrow_collectDecls(x_5, x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_inferBorrow___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lean_IR_getEnv___redArg(x_2);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_1);
x_6 = l_Lean_IR_Borrow_infer(x_5, x_1);
x_7 = l_Lean_IR_Borrow_ApplyParamMap_visitDecls(x_1, x_6);
lean_dec(x_6);
lean_ctor_set(x_3, 0, x_7);
return x_3;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_3, 0);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_3);
lean_inc(x_1);
x_10 = l_Lean_IR_Borrow_infer(x_8, x_1);
x_11 = l_Lean_IR_Borrow_ApplyParamMap_visitDecls(x_1, x_10);
lean_dec(x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_inferBorrow(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_inferBorrow___redArg(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_inferBorrow___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_inferBorrow(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* initialize_Lean_Compiler_ExportAttr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_IR_CompilerM(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_IR_NormIds(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_IR_Borrow(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_ExportAttr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_CompilerM(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_NormIds(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_IR_Borrow_OwnedSet_instBEqKey___closed__0 = _init_l_Lean_IR_Borrow_OwnedSet_instBEqKey___closed__0();
lean_mark_persistent(l_Lean_IR_Borrow_OwnedSet_instBEqKey___closed__0);
l_Lean_IR_Borrow_OwnedSet_instBEqKey = _init_l_Lean_IR_Borrow_OwnedSet_instBEqKey();
lean_mark_persistent(l_Lean_IR_Borrow_OwnedSet_instBEqKey);
l_Lean_IR_Borrow_OwnedSet_instHashableKey___closed__0 = _init_l_Lean_IR_Borrow_OwnedSet_instHashableKey___closed__0();
lean_mark_persistent(l_Lean_IR_Borrow_OwnedSet_instHashableKey___closed__0);
l_Lean_IR_Borrow_OwnedSet_instHashableKey = _init_l_Lean_IR_Borrow_OwnedSet_instHashableKey();
lean_mark_persistent(l_Lean_IR_Borrow_OwnedSet_instHashableKey);
l_Lean_IR_Borrow_ParamMap_instBEqKey___closed__0 = _init_l_Lean_IR_Borrow_ParamMap_instBEqKey___closed__0();
lean_mark_persistent(l_Lean_IR_Borrow_ParamMap_instBEqKey___closed__0);
l_Lean_IR_Borrow_ParamMap_instBEqKey = _init_l_Lean_IR_Borrow_ParamMap_instBEqKey();
lean_mark_persistent(l_Lean_IR_Borrow_ParamMap_instBEqKey);
l_Lean_IR_Borrow_ParamMap_instHashableKey___closed__0 = _init_l_Lean_IR_Borrow_ParamMap_instHashableKey___closed__0();
lean_mark_persistent(l_Lean_IR_Borrow_ParamMap_instHashableKey___closed__0);
l_Lean_IR_Borrow_ParamMap_instHashableKey = _init_l_Lean_IR_Borrow_ParamMap_instHashableKey();
lean_mark_persistent(l_Lean_IR_Borrow_ParamMap_instHashableKey);
l_Std_DHashMap_Internal_AssocList_foldlM___at___Lean_IR_Borrow_ParamMap_fmt_spec__0___closed__0 = _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___Lean_IR_Borrow_ParamMap_fmt_spec__0___closed__0();
lean_mark_persistent(l_Std_DHashMap_Internal_AssocList_foldlM___at___Lean_IR_Borrow_ParamMap_fmt_spec__0___closed__0);
l_Std_DHashMap_Internal_AssocList_foldlM___at___Lean_IR_Borrow_ParamMap_fmt_spec__0___closed__1 = _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___Lean_IR_Borrow_ParamMap_fmt_spec__0___closed__1();
lean_mark_persistent(l_Std_DHashMap_Internal_AssocList_foldlM___at___Lean_IR_Borrow_ParamMap_fmt_spec__0___closed__1);
l_Std_DHashMap_Internal_AssocList_foldlM___at___Lean_IR_Borrow_ParamMap_fmt_spec__0___closed__2 = _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___Lean_IR_Borrow_ParamMap_fmt_spec__0___closed__2();
lean_mark_persistent(l_Std_DHashMap_Internal_AssocList_foldlM___at___Lean_IR_Borrow_ParamMap_fmt_spec__0___closed__2);
l_Std_DHashMap_Internal_AssocList_foldlM___at___Lean_IR_Borrow_ParamMap_fmt_spec__0___closed__3 = _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___Lean_IR_Borrow_ParamMap_fmt_spec__0___closed__3();
lean_mark_persistent(l_Std_DHashMap_Internal_AssocList_foldlM___at___Lean_IR_Borrow_ParamMap_fmt_spec__0___closed__3);
l_Std_DHashMap_Internal_AssocList_foldlM___at___Lean_IR_Borrow_ParamMap_fmt_spec__0___closed__4 = _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___Lean_IR_Borrow_ParamMap_fmt_spec__0___closed__4();
lean_mark_persistent(l_Std_DHashMap_Internal_AssocList_foldlM___at___Lean_IR_Borrow_ParamMap_fmt_spec__0___closed__4);
l_Lean_IR_Borrow_ParamMap_fmt___closed__0 = _init_l_Lean_IR_Borrow_ParamMap_fmt___closed__0();
lean_mark_persistent(l_Lean_IR_Borrow_ParamMap_fmt___closed__0);
l_Lean_IR_Borrow_ParamMap_fmt___closed__1 = _init_l_Lean_IR_Borrow_ParamMap_fmt___closed__1();
lean_mark_persistent(l_Lean_IR_Borrow_ParamMap_fmt___closed__1);
l_Lean_IR_Borrow_ParamMap_fmt___closed__2 = _init_l_Lean_IR_Borrow_ParamMap_fmt___closed__2();
lean_mark_persistent(l_Lean_IR_Borrow_ParamMap_fmt___closed__2);
l_Lean_IR_Borrow_ParamMap_fmt___closed__3 = _init_l_Lean_IR_Borrow_ParamMap_fmt___closed__3();
lean_mark_persistent(l_Lean_IR_Borrow_ParamMap_fmt___closed__3);
l_Lean_IR_Borrow_ParamMap_fmt___closed__4 = _init_l_Lean_IR_Borrow_ParamMap_fmt___closed__4();
lean_mark_persistent(l_Lean_IR_Borrow_ParamMap_fmt___closed__4);
l_Lean_IR_Borrow_instToFormatParamMap___closed__0 = _init_l_Lean_IR_Borrow_instToFormatParamMap___closed__0();
lean_mark_persistent(l_Lean_IR_Borrow_instToFormatParamMap___closed__0);
l_Lean_IR_Borrow_instToFormatParamMap = _init_l_Lean_IR_Borrow_instToFormatParamMap();
lean_mark_persistent(l_Lean_IR_Borrow_instToFormatParamMap);
l_Lean_IR_Borrow_instToStringParamMap = _init_l_Lean_IR_Borrow_instToStringParamMap();
lean_mark_persistent(l_Lean_IR_Borrow_instToStringParamMap);
l_Lean_IR_Borrow_mkInitParamMap___closed__0 = _init_l_Lean_IR_Borrow_mkInitParamMap___closed__0();
lean_mark_persistent(l_Lean_IR_Borrow_mkInitParamMap___closed__0);
l_Lean_IR_Borrow_mkInitParamMap___closed__1 = _init_l_Lean_IR_Borrow_mkInitParamMap___closed__1();
lean_mark_persistent(l_Lean_IR_Borrow_mkInitParamMap___closed__1);
l_Lean_IR_Borrow_mkInitParamMap___closed__2 = _init_l_Lean_IR_Borrow_mkInitParamMap___closed__2();
lean_mark_persistent(l_Lean_IR_Borrow_mkInitParamMap___closed__2);
l_Lean_IR_Borrow_mkInitParamMap___closed__3 = _init_l_Lean_IR_Borrow_mkInitParamMap___closed__3();
lean_mark_persistent(l_Lean_IR_Borrow_mkInitParamMap___closed__3);
l_Lean_IR_Borrow_mkInitParamMap___closed__4 = _init_l_Lean_IR_Borrow_mkInitParamMap___closed__4();
lean_mark_persistent(l_Lean_IR_Borrow_mkInitParamMap___closed__4);
l_Lean_IR_Borrow_ApplyParamMap_visitFnBody___closed__0 = _init_l_Lean_IR_Borrow_ApplyParamMap_visitFnBody___closed__0();
lean_mark_persistent(l_Lean_IR_Borrow_ApplyParamMap_visitFnBody___closed__0);
l_Lean_IR_Borrow_ApplyParamMap_visitFnBody___closed__1 = _init_l_Lean_IR_Borrow_ApplyParamMap_visitFnBody___closed__1();
lean_mark_persistent(l_Lean_IR_Borrow_ApplyParamMap_visitFnBody___closed__1);
l_Lean_IR_Borrow_ApplyParamMap_visitFnBody___closed__2 = _init_l_Lean_IR_Borrow_ApplyParamMap_visitFnBody___closed__2();
lean_mark_persistent(l_Lean_IR_Borrow_ApplyParamMap_visitFnBody___closed__2);
l_Lean_IR_Borrow_ApplyParamMap_visitFnBody___closed__3 = _init_l_Lean_IR_Borrow_ApplyParamMap_visitFnBody___closed__3();
lean_mark_persistent(l_Lean_IR_Borrow_ApplyParamMap_visitFnBody___closed__3);
l_Array_mapMUnsafe_map___at___Lean_IR_Borrow_ApplyParamMap_visitDecls_spec__0___closed__0 = _init_l_Array_mapMUnsafe_map___at___Lean_IR_Borrow_ApplyParamMap_visitDecls_spec__0___closed__0();
lean_mark_persistent(l_Array_mapMUnsafe_map___at___Lean_IR_Borrow_ApplyParamMap_visitDecls_spec__0___closed__0);
l_Array_mapMUnsafe_map___at___Lean_IR_Borrow_ApplyParamMap_visitDecls_spec__0___closed__1 = _init_l_Array_mapMUnsafe_map___at___Lean_IR_Borrow_ApplyParamMap_visitDecls_spec__0___closed__1();
lean_mark_persistent(l_Array_mapMUnsafe_map___at___Lean_IR_Borrow_ApplyParamMap_visitDecls_spec__0___closed__1);
l_panic___at___Lean_IR_Borrow_getParamInfo_spec__0___closed__0 = _init_l_panic___at___Lean_IR_Borrow_getParamInfo_spec__0___closed__0();
lean_mark_persistent(l_panic___at___Lean_IR_Borrow_getParamInfo_spec__0___closed__0);
l_panic___at___Lean_IR_Borrow_getParamInfo_spec__0___closed__1 = _init_l_panic___at___Lean_IR_Borrow_getParamInfo_spec__0___closed__1();
lean_mark_persistent(l_panic___at___Lean_IR_Borrow_getParamInfo_spec__0___closed__1);
l_panic___at___Lean_IR_Borrow_getParamInfo_spec__0___closed__2 = _init_l_panic___at___Lean_IR_Borrow_getParamInfo_spec__0___closed__2();
lean_mark_persistent(l_panic___at___Lean_IR_Borrow_getParamInfo_spec__0___closed__2);
l_panic___at___Lean_IR_Borrow_getParamInfo_spec__0___closed__3 = _init_l_panic___at___Lean_IR_Borrow_getParamInfo_spec__0___closed__3();
lean_mark_persistent(l_panic___at___Lean_IR_Borrow_getParamInfo_spec__0___closed__3);
l_panic___at___Lean_IR_Borrow_getParamInfo_spec__0___closed__4 = _init_l_panic___at___Lean_IR_Borrow_getParamInfo_spec__0___closed__4();
lean_mark_persistent(l_panic___at___Lean_IR_Borrow_getParamInfo_spec__0___closed__4);
l_panic___at___Lean_IR_Borrow_getParamInfo_spec__0___closed__5 = _init_l_panic___at___Lean_IR_Borrow_getParamInfo_spec__0___closed__5();
lean_mark_persistent(l_panic___at___Lean_IR_Borrow_getParamInfo_spec__0___closed__5);
l_panic___at___Lean_IR_Borrow_getParamInfo_spec__0___closed__6 = _init_l_panic___at___Lean_IR_Borrow_getParamInfo_spec__0___closed__6();
lean_mark_persistent(l_panic___at___Lean_IR_Borrow_getParamInfo_spec__0___closed__6);
l_panic___at___Lean_IR_Borrow_getParamInfo_spec__0___closed__7 = _init_l_panic___at___Lean_IR_Borrow_getParamInfo_spec__0___closed__7();
lean_mark_persistent(l_panic___at___Lean_IR_Borrow_getParamInfo_spec__0___closed__7);
l_Lean_IR_Borrow_getParamInfo___closed__0 = _init_l_Lean_IR_Borrow_getParamInfo___closed__0();
lean_mark_persistent(l_Lean_IR_Borrow_getParamInfo___closed__0);
l_Lean_IR_Borrow_getParamInfo___closed__1 = _init_l_Lean_IR_Borrow_getParamInfo___closed__1();
lean_mark_persistent(l_Lean_IR_Borrow_getParamInfo___closed__1);
l_Lean_IR_Borrow_getParamInfo___closed__2 = _init_l_Lean_IR_Borrow_getParamInfo___closed__2();
lean_mark_persistent(l_Lean_IR_Borrow_getParamInfo___closed__2);
l_Lean_IR_Borrow_infer___closed__0 = _init_l_Lean_IR_Borrow_infer___closed__0();
lean_mark_persistent(l_Lean_IR_Borrow_infer___closed__0);
l_Lean_IR_Borrow_infer___closed__1 = _init_l_Lean_IR_Borrow_infer___closed__1();
lean_mark_persistent(l_Lean_IR_Borrow_infer___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
