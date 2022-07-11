// Lean compiler output
// Module: Lean.Compiler.IR.Borrow
// Imports: Init Lean.Compiler.ExportAttr Lean.Compiler.IR.CompilerM Lean.Compiler.IR.NormIds
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
static lean_object* l_Lean_IR_Borrow_ParamMap_fmt___closed__1;
LEAN_EXPORT lean_object* l_Std_AssocList_replace___at_Lean_IR_Borrow_OwnedSet_insert___spec__6(lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Std_HashMap_insert___at_Lean_IR_Borrow_InitParamMap_visitFnBody___spec__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_Borrow_ParamMap_fmt___closed__2;
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_updateParamMap___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_Borrow_OwnedSet_beq(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l___private_Std_Data_HashMap_0__Std_numBucketsForCapacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_inferBorrow___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_Borrow_ParamMap_fmt___closed__5;
LEAN_EXPORT lean_object* l_ReaderT_pure___at_Lean_IR_Borrow_collectDecls___spec__1___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_BorrowInfCtx_paramSet___default;
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_isOwned(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_mkInitParamMap(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMapImp_expand___at_Lean_IR_Borrow_InitParamMap_visitFnBody___spec__3(lean_object*, lean_object*);
static lean_object* l_Lean_IR_Borrow_ParamMap_fmt___closed__3;
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_ParamMap_instBEqKey;
extern lean_object* l_Std_Format_defWidth;
static lean_object* l_Lean_IR_Borrow_OwnedSet_instHashableKey___closed__1;
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_IR_Borrow_preserveTailCall___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_Borrow_ownArgs___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_forM_loop___at_Lean_IR_Borrow_ownParamsUsingArgs___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_Borrow_ParamMap_fmt___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_IR_Borrow_ApplyParamMap_visitFnBody___spec__3(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_updateParamSet___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_IR_Borrow_ParamMap_fmt___closed__6;
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_InitParamMap_visitDecls(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_OwnedSet_contains___boxed(lean_object*, lean_object*);
lean_object* l_Std_RBNode_findCore___at_Lean_IR_UniqueIds_checkId___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_AssocList_foldlM___at_Lean_IR_Borrow_OwnedSet_insert___spec__5(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_ownArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_InitParamMap_initBorrowIfNotExported(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_collectFnBody(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_ownArgsUsingParams___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_getEnv___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_OwnedSet_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_IR_formatArray___at_Lean_IR_formatParams___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_mkInitParamMap___boxed(lean_object*, lean_object*);
static lean_object* l_Nat_forM_loop___at_Lean_IR_Borrow_ownArgsUsingParams___spec__2___closed__3;
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_instToStringParamMap___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_AssocList_contains___at_Lean_IR_Borrow_InitParamMap_visitFnBody___spec__2___boxed(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
uint8_t l_Lean_IR_IRType_isObj(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_insert___at_Lean_IR_Borrow_OwnedSet_insert___spec__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_Borrow_ApplyParamMap_visitFnBody___closed__3;
static lean_object* l_Nat_forM_loop___at_Lean_IR_Borrow_ownArgsUsingParams___spec__2___closed__1;
lean_object* l_Lean_IR_Decl_name(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_Borrow_InitParamMap_visitDecls___spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_Borrow_updateParamMap___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_BorrowInfState_owned___default;
LEAN_EXPORT lean_object* l_panic___at_Lean_IR_Borrow_getParamInfo___spec__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_Borrow_instToFormatParamMap___closed__1;
LEAN_EXPORT lean_object* l_Std_AssocList_find_x3f___at_Lean_IR_Borrow_ApplyParamMap_visitFnBody___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_Borrow_InitParamMap_visitFnBody___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
static lean_object* l_Std_AssocList_foldlM___at_Lean_IR_Borrow_ParamMap_fmt___spec__1___closed__1;
lean_object* l_panic___at_Lean_IR_Decl_updateBody_x21___spec__1(lean_object*);
lean_object* l_Lean_IR_AltCore_body(lean_object*);
LEAN_EXPORT lean_object* l_Nat_forM_loop___at_Lean_IR_Borrow_ownArgsUsingParams___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Name_hash___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_ParamMap_getHash___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_Borrow_updateParamMap___spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_pure___at_Lean_IR_Borrow_collectDecls___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_collectExpr(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_IR_Borrow_0__Lean_IR_Borrow_ParamMap_beqKey____x40_Lean_Compiler_IR_Borrow___hyg_175_(lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_Borrow_ApplyParamMap_visitDecls___spec__1___closed__2;
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_getCurrFn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_ApplyParamMap_visitFnBody(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_Borrow_ownArgsIfParam___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_Borrow_updateParamSet___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_Borrow_ParamMap_fmt___closed__7;
LEAN_EXPORT uint64_t l_Lean_IR_Borrow_ParamMap_getHash(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_Borrow_collectFnBody___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_HashMapImp_contains___at_Lean_IR_Borrow_OwnedSet_contains___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_ParamMap_instHashableKey;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_Borrow_ownArgs___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_Borrow_getParamInfo___closed__3;
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_mkHashMapImp___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Nat_forM_loop___at_Lean_IR_Borrow_ownArgsUsingParams___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabited___rarg(lean_object*, lean_object*);
uint8_t l_Lean_IR_FnBody_isTerminal(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMapImp_find_x3f___at_Lean_IR_Borrow_ApplyParamMap_visitFnBody___spec__1(lean_object*, lean_object*);
lean_object* l_Nat_repr(lean_object*);
LEAN_EXPORT lean_object* l_Std_AssocList_replace___at_Lean_IR_Borrow_InitParamMap_visitFnBody___spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_ParamMap_fmt(lean_object*);
static lean_object* l_panic___at_Lean_IR_Borrow_getParamInfo___spec__1___closed__3;
static lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_Borrow_ApplyParamMap_visitDecls___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_Borrow_ApplyParamMap_visitDecls___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_format_pretty(lean_object*, lean_object*);
extern lean_object* l_Lean_IR_instInhabitedFnBody;
static lean_object* l_Nat_forM_loop___at_Lean_IR_Borrow_ownArgsUsingParams___spec__2___closed__4;
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_collectDecl(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_Borrow_ApplyParamMap_visitFnBody___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_ownArgs(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_InitParamMap_initBorrow(lean_object*);
LEAN_EXPORT lean_object* l_Nat_forM_loop___at_Lean_IR_Borrow_ownParamsUsingArgs___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_infer(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_InitParamMap_visitDecls___boxed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_modn(size_t, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_updateParamMap(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_IR_Borrow_ownArgsUsingParams___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_AssocList_foldlM___at_Lean_IR_Borrow_ParamMap_fmt___spec__1(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_AssocList_contains___at_Lean_IR_Borrow_OwnedSet_insert___spec__2(lean_object*, lean_object*);
static lean_object* l_Lean_IR_Borrow_ParamMap_instHashableKey___closed__1;
LEAN_EXPORT lean_object* l_ReaderT_pure___at_Lean_IR_Borrow_collectDecls___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_Borrow_ownArgsIfParam___spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_Borrow_InitParamMap_visitFnBody___spec__7(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_mkHashMap___at_Lean_IR_Borrow_BorrowInfState_owned___default___spec__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_whileModifing(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_ownParamsUsingArgs(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_collectExpr___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMapImp_expand___at_Lean_IR_Borrow_OwnedSet_insert___spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_Borrow_InitParamMap_initBorrow___spec__1___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isExport(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_OwnedSet_instHashableKey;
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_markModified(lean_object*);
LEAN_EXPORT uint64_t l_Lean_IR_Borrow_OwnedSet_getHash(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_Borrow_collectDecls___spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_Borrow_collectDecls___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_applyParamMap(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_ownParamsUsingArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at_Lean_IR_Borrow_getParamInfo___spec__1___closed__1;
static lean_object* l_Lean_IR_Borrow_getParamInfo___closed__1;
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_OwnedSet_instBEqKey;
lean_object* l_Lean_IR_FnBody_setBody(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_mkHashMap___at_Lean_IR_Borrow_mkInitParamMap___spec__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_AssocList_find_x3f___at_Lean_IR_Borrow_ApplyParamMap_visitFnBody___spec__2___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_IR_Borrow_ParamMap_fmt___closed__4;
extern lean_object* l_Id_instMonadId;
static lean_object* l_Nat_forM_loop___at_Lean_IR_Borrow_ownArgsUsingParams___spec__2___closed__2;
LEAN_EXPORT lean_object* l_Std_AssocList_contains___at_Lean_IR_Borrow_OwnedSet_insert___spec__2___boxed(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* l_Lean_IR_Borrow_getParamInfo___closed__2;
LEAN_EXPORT lean_object* l_Std_AssocList_foldlM___at_Lean_IR_Borrow_InitParamMap_visitFnBody___spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_markModified___rarg(lean_object*);
lean_object* l_instInhabitedReaderT___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_collectExpr___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at_Lean_IR_Borrow_getParamInfo___spec__1___closed__2;
LEAN_EXPORT lean_object* l_Std_HashMapImp_moveEntries___at_Lean_IR_Borrow_OwnedSet_insert___spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_AssocList_contains___at_Lean_IR_Borrow_InitParamMap_visitFnBody___spec__2(lean_object*, lean_object*);
static lean_object* l_Lean_IR_Borrow_ParamMap_fmt___closed__8;
static lean_object* l_Std_AssocList_foldlM___at_Lean_IR_Borrow_ParamMap_fmt___spec__1___closed__2;
static lean_object* l_Std_AssocList_foldlM___at_Lean_IR_Borrow_ParamMap_fmt___spec__1___closed__4;
LEAN_EXPORT lean_object* l_Std_HashMapImp_contains___at_Lean_IR_Borrow_OwnedSet_contains___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_Borrow_ParamMap_fmt___spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_inferBorrow(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_Borrow_OwnedSet_instBEqKey___closed__1;
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_isOwned___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_Borrow_ApplyParamMap_visitFnBody___spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_ApplyParamMap_visitDecls(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l_Std_AssocList_foldlM___at_Lean_IR_Borrow_ParamMap_fmt___spec__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_ownArgsIfParam(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_ownArgsUsingParams(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_ownArgsIfParam___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMapImp_moveEntries___at_Lean_IR_Borrow_InitParamMap_visitFnBody___spec__4(lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_StateT_instMonadStateT___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_InitParamMap_visitFnBody(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_InitParamMap_initBorrowIfNotExported___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_markModified___boxed(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Std_mkHashMap___at_Lean_IR_Borrow_BorrowInfState_owned___default___spec__1(lean_object*);
lean_object* lean_ir_find_env_decl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_ownArgs___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_IR_instInhabitedArg;
static lean_object* l_Lean_IR_Borrow_ApplyParamMap_visitFnBody___closed__2;
static lean_object* l_Lean_IR_Borrow_ApplyParamMap_visitFnBody___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Borrow_0__Lean_IR_Borrow_ParamMap_beqKey____x40_Lean_Compiler_IR_Borrow___hyg_175____boxed(lean_object*, lean_object*);
static lean_object* l_panic___at_Lean_IR_Borrow_getParamInfo___spec__1___closed__4;
static lean_object* l_Std_AssocList_foldlM___at_Lean_IR_Borrow_ParamMap_fmt___spec__1___closed__5;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_Borrow_InitParamMap_visitDecls___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_BorrowInfCtx_currFn___default;
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_preserveTailCall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_Borrow_updateParamSet___spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_OwnedSet_insert(lean_object*, lean_object*);
static lean_object* l_Lean_IR_Borrow_infer___closed__1;
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_collectDecls___boxed__const__1;
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_ownVar___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_preserveTailCall___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_Borrow_ApplyParamMap_visitFnBody___closed__4;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_Borrow_collectFnBody___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_Borrow_OwnedSet_contains(lean_object*, lean_object*);
lean_object* l_Lean_IR_FnBody_body(lean_object*);
lean_object* l_panic___at_Lean_IR_addParamsRename___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_updateParamSet(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_ownArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_mkHashMap___at_Lean_IR_Borrow_mkInitParamMap___spec__1(lean_object*);
lean_object* l_Lean_IR_Decl_params(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_instToStringParamMap(lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_Borrow_BorrowInfState_modified___default;
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_IR_Borrow_preserveTailCall___spec__1(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_OwnedSet_getHash___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_instToFormatParamMap;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_Borrow_ApplyParamMap_visitDecls___spec__1(lean_object*, size_t, size_t, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_collectDecls(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_getParamInfo(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_getCurrFn___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_ownVar(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_ParamMap_fmt___boxed(lean_object*);
lean_object* l_Std_RBNode_insert___at_Lean_IR_mkIndexSet___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_Borrow_InitParamMap_initBorrow___spec__1(size_t, size_t, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Lean_IR_Borrow_ParamMap_instBEqKey___closed__1;
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
uint8_t x_8; 
x_8 = 0;
return x_8;
}
else
{
uint8_t x_9; 
x_9 = lean_nat_dec_eq(x_4, x_6);
return x_9;
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
static lean_object* _init_l_Lean_IR_Borrow_OwnedSet_instBEqKey___closed__1() {
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
x_1 = l_Lean_IR_Borrow_OwnedSet_instBEqKey___closed__1;
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
static lean_object* _init_l_Lean_IR_Borrow_OwnedSet_instHashableKey___closed__1() {
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
x_1 = l_Lean_IR_Borrow_OwnedSet_instHashableKey___closed__1;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Std_AssocList_contains___at_Lean_IR_Borrow_OwnedSet_insert___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = l_Lean_IR_Borrow_OwnedSet_beq(x_4, x_1);
if (x_6 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
uint8_t x_8; 
x_8 = 1;
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_AssocList_foldlM___at_Lean_IR_Borrow_OwnedSet_insert___spec__5(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; size_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
x_7 = l_Lean_IR_Borrow_OwnedSet_getHash(x_4);
x_8 = lean_uint64_to_usize(x_7);
x_9 = lean_usize_modn(x_8, x_6);
lean_dec(x_6);
x_10 = lean_array_uget(x_1, x_9);
lean_ctor_set(x_2, 2, x_10);
x_11 = lean_array_uset(x_1, x_9, x_2);
x_1 = x_11;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint64_t x_17; size_t x_18; size_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_13 = lean_ctor_get(x_2, 0);
x_14 = lean_ctor_get(x_2, 1);
x_15 = lean_ctor_get(x_2, 2);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_2);
x_16 = lean_array_get_size(x_1);
x_17 = l_Lean_IR_Borrow_OwnedSet_getHash(x_13);
x_18 = lean_uint64_to_usize(x_17);
x_19 = lean_usize_modn(x_18, x_16);
lean_dec(x_16);
x_20 = lean_array_uget(x_1, x_19);
x_21 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_21, 0, x_13);
lean_ctor_set(x_21, 1, x_14);
lean_ctor_set(x_21, 2, x_20);
x_22 = lean_array_uset(x_1, x_19, x_21);
x_1 = x_22;
x_2 = x_15;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMapImp_moveEntries___at_Lean_IR_Borrow_OwnedSet_insert___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_Std_AssocList_foldlM___at_Lean_IR_Borrow_OwnedSet_insert___spec__5(x_3, x_6);
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
LEAN_EXPORT lean_object* l_Std_HashMapImp_expand___at_Lean_IR_Borrow_OwnedSet_insert___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_unsigned_to_nat(2u);
x_5 = lean_nat_mul(x_3, x_4);
lean_dec(x_3);
x_6 = lean_box(0);
x_7 = lean_mk_array(x_5, x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Std_HashMapImp_moveEntries___at_Lean_IR_Borrow_OwnedSet_insert___spec__4(x_8, x_2, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_AssocList_replace___at_Lean_IR_Borrow_OwnedSet_insert___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(0);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 1);
x_8 = lean_ctor_get(x_3, 2);
x_9 = l_Lean_IR_Borrow_OwnedSet_beq(x_6, x_1);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = l_Std_AssocList_replace___at_Lean_IR_Borrow_OwnedSet_insert___spec__6(x_1, x_2, x_8);
lean_ctor_set(x_3, 2, x_10);
return x_3;
}
else
{
lean_dec(x_7);
lean_dec(x_6);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
x_13 = lean_ctor_get(x_3, 2);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_3);
x_14 = l_Lean_IR_Borrow_OwnedSet_beq(x_11, x_1);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = l_Std_AssocList_replace___at_Lean_IR_Borrow_OwnedSet_insert___spec__6(x_1, x_2, x_13);
x_16 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_16, 0, x_11);
lean_ctor_set(x_16, 1, x_12);
lean_ctor_set(x_16, 2, x_15);
return x_16;
}
else
{
lean_object* x_17; 
lean_dec(x_12);
lean_dec(x_11);
x_17 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_2);
lean_ctor_set(x_17, 2, x_13);
return x_17;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_insert___at_Lean_IR_Borrow_OwnedSet_insert___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint64_t x_8; size_t x_9; size_t x_10; lean_object* x_11; uint8_t x_12; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_array_get_size(x_6);
x_8 = l_Lean_IR_Borrow_OwnedSet_getHash(x_2);
x_9 = lean_uint64_to_usize(x_8);
x_10 = lean_usize_modn(x_9, x_7);
x_11 = lean_array_uget(x_6, x_10);
x_12 = l_Std_AssocList_contains___at_Lean_IR_Borrow_OwnedSet_insert___spec__2(x_2, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_5, x_13);
lean_dec(x_5);
x_15 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_15, 0, x_2);
lean_ctor_set(x_15, 1, x_3);
lean_ctor_set(x_15, 2, x_11);
x_16 = lean_array_uset(x_6, x_10, x_15);
x_17 = l___private_Std_Data_HashMap_0__Std_numBucketsForCapacity(x_14);
x_18 = lean_nat_dec_le(x_17, x_7);
lean_dec(x_7);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
lean_free_object(x_1);
x_19 = l_Std_HashMapImp_expand___at_Lean_IR_Borrow_OwnedSet_insert___spec__3(x_14, x_16);
return x_19;
}
else
{
lean_ctor_set(x_1, 1, x_16);
lean_ctor_set(x_1, 0, x_14);
return x_1;
}
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_7);
x_20 = l_Std_AssocList_replace___at_Lean_IR_Borrow_OwnedSet_insert___spec__6(x_2, x_3, x_11);
x_21 = lean_array_uset(x_6, x_10, x_20);
lean_ctor_set(x_1, 1, x_21);
return x_1;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint64_t x_25; size_t x_26; size_t x_27; lean_object* x_28; uint8_t x_29; 
x_22 = lean_ctor_get(x_1, 0);
x_23 = lean_ctor_get(x_1, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_1);
x_24 = lean_array_get_size(x_23);
x_25 = l_Lean_IR_Borrow_OwnedSet_getHash(x_2);
x_26 = lean_uint64_to_usize(x_25);
x_27 = lean_usize_modn(x_26, x_24);
x_28 = lean_array_uget(x_23, x_27);
x_29 = l_Std_AssocList_contains___at_Lean_IR_Borrow_OwnedSet_insert___spec__2(x_2, x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_nat_add(x_22, x_30);
lean_dec(x_22);
x_32 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_32, 0, x_2);
lean_ctor_set(x_32, 1, x_3);
lean_ctor_set(x_32, 2, x_28);
x_33 = lean_array_uset(x_23, x_27, x_32);
x_34 = l___private_Std_Data_HashMap_0__Std_numBucketsForCapacity(x_31);
x_35 = lean_nat_dec_le(x_34, x_24);
lean_dec(x_24);
lean_dec(x_34);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = l_Std_HashMapImp_expand___at_Lean_IR_Borrow_OwnedSet_insert___spec__3(x_31, x_33);
return x_36;
}
else
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_31);
lean_ctor_set(x_37, 1, x_33);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_24);
x_38 = l_Std_AssocList_replace___at_Lean_IR_Borrow_OwnedSet_insert___spec__6(x_2, x_3, x_28);
x_39 = lean_array_uset(x_23, x_27, x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_22);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_OwnedSet_insert(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(0);
x_4 = l_Std_HashMap_insert___at_Lean_IR_Borrow_OwnedSet_insert___spec__1(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_AssocList_contains___at_Lean_IR_Borrow_OwnedSet_insert___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_AssocList_contains___at_Lean_IR_Borrow_OwnedSet_insert___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Std_HashMapImp_contains___at_Lean_IR_Borrow_OwnedSet_contains___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint64_t x_5; size_t x_6; size_t x_7; lean_object* x_8; uint8_t x_9; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Lean_IR_Borrow_OwnedSet_getHash(x_2);
x_6 = lean_uint64_to_usize(x_5);
x_7 = lean_usize_modn(x_6, x_4);
lean_dec(x_4);
x_8 = lean_array_uget(x_3, x_7);
x_9 = l_Std_AssocList_contains___at_Lean_IR_Borrow_OwnedSet_insert___spec__2(x_2, x_8);
lean_dec(x_8);
return x_9;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_Borrow_OwnedSet_contains(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Std_HashMapImp_contains___at_Lean_IR_Borrow_OwnedSet_contains___spec__1(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_HashMapImp_contains___at_Lean_IR_Borrow_OwnedSet_contains___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_HashMapImp_contains___at_Lean_IR_Borrow_OwnedSet_contains___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
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
LEAN_EXPORT uint8_t l___private_Lean_Compiler_IR_Borrow_0__Lean_IR_Borrow_ParamMap_beqKey____x40_Lean_Compiler_IR_Borrow___hyg_175_(lean_object* x_1, lean_object* x_2) {
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
uint8_t x_6; 
x_6 = 0;
return x_6;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_7; 
x_7 = 0;
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_2, 1);
x_12 = lean_name_eq(x_8, x_10);
if (x_12 == 0)
{
uint8_t x_13; 
x_13 = 0;
return x_13;
}
else
{
uint8_t x_14; 
x_14 = lean_nat_dec_eq(x_9, x_11);
return x_14;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Borrow_0__Lean_IR_Borrow_ParamMap_beqKey____x40_Lean_Compiler_IR_Borrow___hyg_175____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Compiler_IR_Borrow_0__Lean_IR_Borrow_ParamMap_beqKey____x40_Lean_Compiler_IR_Borrow___hyg_175_(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_IR_Borrow_ParamMap_instBEqKey___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Compiler_IR_Borrow_0__Lean_IR_Borrow_ParamMap_beqKey____x40_Lean_Compiler_IR_Borrow___hyg_175____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_Borrow_ParamMap_instBEqKey() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_IR_Borrow_ParamMap_instBEqKey___closed__1;
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
static lean_object* _init_l_Lean_IR_Borrow_ParamMap_instHashableKey___closed__1() {
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
x_1 = l_Lean_IR_Borrow_ParamMap_instHashableKey___closed__1;
return x_1;
}
}
static lean_object* _init_l_Std_AssocList_foldlM___at_Lean_IR_Borrow_ParamMap_fmt___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" -> ", 4);
return x_1;
}
}
static lean_object* _init_l_Std_AssocList_foldlM___at_Lean_IR_Borrow_ParamMap_fmt___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_AssocList_foldlM___at_Lean_IR_Borrow_ParamMap_fmt___spec__1___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Std_AssocList_foldlM___at_Lean_IR_Borrow_ParamMap_fmt___spec__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(":", 1);
return x_1;
}
}
static lean_object* _init_l_Std_AssocList_foldlM___at_Lean_IR_Borrow_ParamMap_fmt___spec__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_AssocList_foldlM___at_Lean_IR_Borrow_ParamMap_fmt___spec__1___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Std_AssocList_foldlM___at_Lean_IR_Borrow_ParamMap_fmt___spec__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("block_", 6);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_AssocList_foldlM___at_Lean_IR_Borrow_ParamMap_fmt___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_box(1);
x_7 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_6);
x_8 = l_Lean_IR_formatArray___at_Lean_IR_formatParams___spec__1(x_4);
lean_dec(x_4);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_9 = lean_ctor_get(x_3, 0);
lean_inc(x_9);
lean_dec(x_3);
x_10 = 1;
x_11 = l_Lean_Name_toString(x_9, x_10);
x_12 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_13, 0, x_7);
lean_ctor_set(x_13, 1, x_12);
x_14 = l_Std_AssocList_foldlM___at_Lean_IR_Borrow_ParamMap_fmt___spec__1___closed__2;
x_15 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_8);
x_1 = x_16;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_18 = lean_ctor_get(x_3, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_3, 1);
lean_inc(x_19);
lean_dec(x_3);
x_20 = 1;
x_21 = l_Lean_Name_toString(x_18, x_20);
x_22 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = l_Std_AssocList_foldlM___at_Lean_IR_Borrow_ParamMap_fmt___spec__1___closed__4;
x_24 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Nat_repr(x_19);
x_26 = l_Std_AssocList_foldlM___at_Lean_IR_Borrow_ParamMap_fmt___spec__1___closed__5;
x_27 = lean_string_append(x_26, x_25);
lean_dec(x_25);
x_28 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_29, 0, x_24);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_30, 0, x_7);
lean_ctor_set(x_30, 1, x_29);
x_31 = l_Std_AssocList_foldlM___at_Lean_IR_Borrow_ParamMap_fmt___spec__1___closed__2;
x_32 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_8);
x_1 = x_33;
x_2 = x_5;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_Borrow_ParamMap_fmt___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Std_AssocList_foldlM___at_Lean_IR_Borrow_ParamMap_fmt___spec__1(x_4, x_6);
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
x_2 = x_9;
x_4 = x_7;
goto _start;
}
else
{
return x_4;
}
}
}
static lean_object* _init_l_Lean_IR_Borrow_ParamMap_fmt___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("{", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_Borrow_ParamMap_fmt___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_Borrow_ParamMap_fmt___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_Borrow_ParamMap_fmt___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_Borrow_ParamMap_fmt___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("}", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_Borrow_ParamMap_fmt___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_Borrow_ParamMap_fmt___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_Borrow_ParamMap_fmt___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_Borrow_ParamMap_fmt___closed__3;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_Borrow_ParamMap_fmt___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_Borrow_ParamMap_fmt___closed__2;
x_2 = l_Lean_IR_Borrow_ParamMap_fmt___closed__6;
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_Borrow_ParamMap_fmt___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_Borrow_ParamMap_fmt___closed__7;
x_2 = l_Lean_IR_Borrow_ParamMap_fmt___closed__5;
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_ParamMap_fmt(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = lean_array_get_size(x_2);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_lt(x_4, x_3);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_3);
x_6 = l_Lean_IR_Borrow_ParamMap_fmt___closed__8;
return x_6;
}
else
{
uint8_t x_7; 
x_7 = lean_nat_dec_le(x_3, x_3);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_3);
x_8 = l_Lean_IR_Borrow_ParamMap_fmt___closed__8;
return x_8;
}
else
{
size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_9 = 0;
x_10 = lean_usize_of_nat(x_3);
lean_dec(x_3);
x_11 = lean_box(0);
x_12 = l_Array_foldlMUnsafe_fold___at_Lean_IR_Borrow_ParamMap_fmt___spec__2(x_2, x_9, x_10, x_11);
x_13 = l_Lean_IR_Borrow_ParamMap_fmt___closed__3;
x_14 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
x_15 = l_Lean_IR_Borrow_ParamMap_fmt___closed__2;
x_16 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
x_17 = l_Lean_IR_Borrow_ParamMap_fmt___closed__5;
x_18 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_Borrow_ParamMap_fmt___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lean_IR_Borrow_ParamMap_fmt___spec__2(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
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
static lean_object* _init_l_Lean_IR_Borrow_instToFormatParamMap___closed__1() {
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
x_1 = l_Lean_IR_Borrow_instToFormatParamMap___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_instToStringParamMap(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_IR_Borrow_ParamMap_fmt(x_1);
x_3 = l_Std_Format_defWidth;
x_4 = lean_format_pretty(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_instToStringParamMap___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_IR_Borrow_instToStringParamMap(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_Borrow_InitParamMap_initBorrow___spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; size_t x_11; size_t x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_5, 1);
x_10 = l_Lean_IR_IRType_isObj(x_9);
lean_ctor_set_uint8(x_5, sizeof(void*)*2, x_10);
x_11 = 1;
x_12 = lean_usize_add(x_2, x_11);
x_13 = lean_array_uset(x_7, x_2, x_5);
x_2 = x_12;
x_3 = x_13;
goto _start;
}
else
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; 
x_15 = lean_ctor_get(x_5, 0);
x_16 = lean_ctor_get(x_5, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_5);
x_17 = l_Lean_IR_IRType_isObj(x_16);
x_18 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_16);
lean_ctor_set_uint8(x_18, sizeof(void*)*2, x_17);
x_19 = 1;
x_20 = lean_usize_add(x_2, x_19);
x_21 = lean_array_uset(x_7, x_2, x_18);
x_2 = x_20;
x_3 = x_21;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_InitParamMap_initBorrow(lean_object* x_1) {
_start:
{
lean_object* x_2; size_t x_3; size_t x_4; lean_object* x_5; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_usize_of_nat(x_2);
lean_dec(x_2);
x_4 = 0;
x_5 = l_Array_mapMUnsafe_map___at_Lean_IR_Borrow_InitParamMap_initBorrow___spec__1(x_3, x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_Borrow_InitParamMap_initBorrow___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lean_IR_Borrow_InitParamMap_initBorrow___spec__1(x_4, x_5, x_3);
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
LEAN_EXPORT uint8_t l_Std_AssocList_contains___at_Lean_IR_Borrow_InitParamMap_visitFnBody___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = l___private_Lean_Compiler_IR_Borrow_0__Lean_IR_Borrow_ParamMap_beqKey____x40_Lean_Compiler_IR_Borrow___hyg_175_(x_4, x_1);
if (x_6 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
uint8_t x_8; 
x_8 = 1;
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_AssocList_foldlM___at_Lean_IR_Borrow_InitParamMap_visitFnBody___spec__5(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; size_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
x_7 = l_Lean_IR_Borrow_ParamMap_getHash(x_4);
x_8 = lean_uint64_to_usize(x_7);
x_9 = lean_usize_modn(x_8, x_6);
lean_dec(x_6);
x_10 = lean_array_uget(x_1, x_9);
lean_ctor_set(x_2, 2, x_10);
x_11 = lean_array_uset(x_1, x_9, x_2);
x_1 = x_11;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint64_t x_17; size_t x_18; size_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_13 = lean_ctor_get(x_2, 0);
x_14 = lean_ctor_get(x_2, 1);
x_15 = lean_ctor_get(x_2, 2);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_2);
x_16 = lean_array_get_size(x_1);
x_17 = l_Lean_IR_Borrow_ParamMap_getHash(x_13);
x_18 = lean_uint64_to_usize(x_17);
x_19 = lean_usize_modn(x_18, x_16);
lean_dec(x_16);
x_20 = lean_array_uget(x_1, x_19);
x_21 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_21, 0, x_13);
lean_ctor_set(x_21, 1, x_14);
lean_ctor_set(x_21, 2, x_20);
x_22 = lean_array_uset(x_1, x_19, x_21);
x_1 = x_22;
x_2 = x_15;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMapImp_moveEntries___at_Lean_IR_Borrow_InitParamMap_visitFnBody___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_Std_AssocList_foldlM___at_Lean_IR_Borrow_InitParamMap_visitFnBody___spec__5(x_3, x_6);
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
LEAN_EXPORT lean_object* l_Std_HashMapImp_expand___at_Lean_IR_Borrow_InitParamMap_visitFnBody___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_unsigned_to_nat(2u);
x_5 = lean_nat_mul(x_3, x_4);
lean_dec(x_3);
x_6 = lean_box(0);
x_7 = lean_mk_array(x_5, x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Std_HashMapImp_moveEntries___at_Lean_IR_Borrow_InitParamMap_visitFnBody___spec__4(x_8, x_2, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_AssocList_replace___at_Lean_IR_Borrow_InitParamMap_visitFnBody___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(0);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 1);
x_8 = lean_ctor_get(x_3, 2);
x_9 = l___private_Lean_Compiler_IR_Borrow_0__Lean_IR_Borrow_ParamMap_beqKey____x40_Lean_Compiler_IR_Borrow___hyg_175_(x_6, x_1);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = l_Std_AssocList_replace___at_Lean_IR_Borrow_InitParamMap_visitFnBody___spec__6(x_1, x_2, x_8);
lean_ctor_set(x_3, 2, x_10);
return x_3;
}
else
{
lean_dec(x_7);
lean_dec(x_6);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
x_13 = lean_ctor_get(x_3, 2);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_3);
x_14 = l___private_Lean_Compiler_IR_Borrow_0__Lean_IR_Borrow_ParamMap_beqKey____x40_Lean_Compiler_IR_Borrow___hyg_175_(x_11, x_1);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = l_Std_AssocList_replace___at_Lean_IR_Borrow_InitParamMap_visitFnBody___spec__6(x_1, x_2, x_13);
x_16 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_16, 0, x_11);
lean_ctor_set(x_16, 1, x_12);
lean_ctor_set(x_16, 2, x_15);
return x_16;
}
else
{
lean_object* x_17; 
lean_dec(x_12);
lean_dec(x_11);
x_17 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_2);
lean_ctor_set(x_17, 2, x_13);
return x_17;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_insert___at_Lean_IR_Borrow_InitParamMap_visitFnBody___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint64_t x_8; size_t x_9; size_t x_10; lean_object* x_11; uint8_t x_12; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_array_get_size(x_6);
x_8 = l_Lean_IR_Borrow_ParamMap_getHash(x_2);
x_9 = lean_uint64_to_usize(x_8);
x_10 = lean_usize_modn(x_9, x_7);
x_11 = lean_array_uget(x_6, x_10);
x_12 = l_Std_AssocList_contains___at_Lean_IR_Borrow_InitParamMap_visitFnBody___spec__2(x_2, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_5, x_13);
lean_dec(x_5);
x_15 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_15, 0, x_2);
lean_ctor_set(x_15, 1, x_3);
lean_ctor_set(x_15, 2, x_11);
x_16 = lean_array_uset(x_6, x_10, x_15);
x_17 = l___private_Std_Data_HashMap_0__Std_numBucketsForCapacity(x_14);
x_18 = lean_nat_dec_le(x_17, x_7);
lean_dec(x_7);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
lean_free_object(x_1);
x_19 = l_Std_HashMapImp_expand___at_Lean_IR_Borrow_InitParamMap_visitFnBody___spec__3(x_14, x_16);
return x_19;
}
else
{
lean_ctor_set(x_1, 1, x_16);
lean_ctor_set(x_1, 0, x_14);
return x_1;
}
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_7);
x_20 = l_Std_AssocList_replace___at_Lean_IR_Borrow_InitParamMap_visitFnBody___spec__6(x_2, x_3, x_11);
x_21 = lean_array_uset(x_6, x_10, x_20);
lean_ctor_set(x_1, 1, x_21);
return x_1;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint64_t x_25; size_t x_26; size_t x_27; lean_object* x_28; uint8_t x_29; 
x_22 = lean_ctor_get(x_1, 0);
x_23 = lean_ctor_get(x_1, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_1);
x_24 = lean_array_get_size(x_23);
x_25 = l_Lean_IR_Borrow_ParamMap_getHash(x_2);
x_26 = lean_uint64_to_usize(x_25);
x_27 = lean_usize_modn(x_26, x_24);
x_28 = lean_array_uget(x_23, x_27);
x_29 = l_Std_AssocList_contains___at_Lean_IR_Borrow_InitParamMap_visitFnBody___spec__2(x_2, x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_nat_add(x_22, x_30);
lean_dec(x_22);
x_32 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_32, 0, x_2);
lean_ctor_set(x_32, 1, x_3);
lean_ctor_set(x_32, 2, x_28);
x_33 = lean_array_uset(x_23, x_27, x_32);
x_34 = l___private_Std_Data_HashMap_0__Std_numBucketsForCapacity(x_31);
x_35 = lean_nat_dec_le(x_34, x_24);
lean_dec(x_24);
lean_dec(x_34);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = l_Std_HashMapImp_expand___at_Lean_IR_Borrow_InitParamMap_visitFnBody___spec__3(x_31, x_33);
return x_36;
}
else
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_31);
lean_ctor_set(x_37, 1, x_33);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_24);
x_38 = l_Std_AssocList_replace___at_Lean_IR_Borrow_InitParamMap_visitFnBody___spec__6(x_2, x_3, x_28);
x_39 = lean_array_uset(x_23, x_27, x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_22);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_Borrow_InitParamMap_visitFnBody___spec__7(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_3, x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; 
lean_dec(x_5);
x_8 = lean_array_uget(x_2, x_3);
x_9 = l_Lean_IR_AltCore_body(x_8);
lean_dec(x_8);
lean_inc(x_1);
x_10 = l_Lean_IR_Borrow_InitParamMap_visitFnBody(x_1, x_9, x_6);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = 1;
x_14 = lean_usize_add(x_3, x_13);
x_3 = x_14;
x_5 = x_11;
x_6 = x_12;
goto _start;
}
else
{
lean_object* x_16; 
lean_dec(x_1);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_5);
lean_ctor_set(x_16, 1, x_6);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_InitParamMap_visitFnBody(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 1:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 3);
lean_inc(x_7);
lean_dec(x_2);
lean_inc(x_1);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_4);
x_9 = l_Lean_IR_Borrow_InitParamMap_initBorrow(x_5);
x_10 = l_Std_HashMap_insert___at_Lean_IR_Borrow_InitParamMap_visitFnBody___spec__1(x_3, x_8, x_9);
lean_inc(x_1);
x_11 = l_Lean_IR_Borrow_InitParamMap_visitFnBody(x_1, x_6, x_10);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_2 = x_7;
x_3 = x_12;
goto _start;
}
case 10:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_2, 3);
lean_inc(x_14);
lean_dec(x_2);
x_15 = lean_array_get_size(x_14);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_nat_dec_lt(x_16, x_15);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_1);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_3);
return x_19;
}
else
{
uint8_t x_20; 
x_20 = lean_nat_dec_le(x_15, x_15);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_1);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_3);
return x_22;
}
else
{
size_t x_23; size_t x_24; lean_object* x_25; lean_object* x_26; 
x_23 = 0;
x_24 = lean_usize_of_nat(x_15);
lean_dec(x_15);
x_25 = lean_box(0);
x_26 = l_Array_foldlMUnsafe_fold___at_Lean_IR_Borrow_InitParamMap_visitFnBody___spec__7(x_1, x_14, x_23, x_24, x_25, x_3);
lean_dec(x_14);
return x_26;
}
}
}
default: 
{
uint8_t x_27; 
x_27 = l_Lean_IR_FnBody_isTerminal(x_2);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = l_Lean_IR_FnBody_body(x_2);
lean_dec(x_2);
x_2 = x_28;
goto _start;
}
else
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_2);
lean_dec(x_1);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_3);
return x_31;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_AssocList_contains___at_Lean_IR_Borrow_InitParamMap_visitFnBody___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_AssocList_contains___at_Lean_IR_Borrow_InitParamMap_visitFnBody___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_Borrow_InitParamMap_visitFnBody___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l_Array_foldlMUnsafe_fold___at_Lean_IR_Borrow_InitParamMap_visitFnBody___spec__7(x_1, x_2, x_7, x_8, x_5, x_6);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_Borrow_InitParamMap_visitDecls___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_3, x_4);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_5);
x_8 = lean_array_uget(x_2, x_3);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_8, 3);
lean_inc(x_11);
lean_dec(x_8);
lean_inc(x_9);
lean_inc(x_1);
x_12 = l_Lean_isExport(x_1, x_9);
lean_inc(x_9);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_9);
x_14 = l_Lean_IR_Borrow_InitParamMap_initBorrowIfNotExported(x_12, x_10);
x_15 = l_Std_HashMap_insert___at_Lean_IR_Borrow_InitParamMap_visitFnBody___spec__1(x_6, x_13, x_14);
x_16 = l_Lean_IR_Borrow_InitParamMap_visitFnBody(x_9, x_11, x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = 1;
x_20 = lean_usize_add(x_3, x_19);
x_3 = x_20;
x_5 = x_17;
x_6 = x_18;
goto _start;
}
else
{
size_t x_22; size_t x_23; lean_object* x_24; 
lean_dec(x_8);
x_22 = 1;
x_23 = lean_usize_add(x_3, x_22);
x_24 = lean_box(0);
x_3 = x_23;
x_5 = x_24;
goto _start;
}
}
else
{
lean_object* x_26; 
lean_dec(x_1);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_5);
lean_ctor_set(x_26, 1, x_6);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_InitParamMap_visitDecls(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_1);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = lean_nat_dec_le(x_4, x_4);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_4);
lean_dec(x_1);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_3);
return x_11;
}
else
{
size_t x_12; size_t x_13; lean_object* x_14; lean_object* x_15; 
x_12 = 0;
x_13 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_14 = lean_box(0);
x_15 = l_Array_foldlMUnsafe_fold___at_Lean_IR_Borrow_InitParamMap_visitDecls___spec__1(x_1, x_2, x_12, x_13, x_14, x_3);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_Borrow_InitParamMap_visitDecls___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l_Array_foldlMUnsafe_fold___at_Lean_IR_Borrow_InitParamMap_visitDecls___spec__1(x_1, x_2, x_7, x_8, x_5, x_6);
lean_dec(x_2);
return x_9;
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
LEAN_EXPORT lean_object* l_Std_mkHashMap___at_Lean_IR_Borrow_mkInitParamMap___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_mkHashMapImp___rarg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_mkInitParamMap(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Std_mkHashMapImp___rarg(x_3);
x_5 = l_Lean_IR_Borrow_InitParamMap_visitDecls(x_1, x_2, x_4);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_mkHashMap___at_Lean_IR_Borrow_mkInitParamMap___spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_mkHashMap___at_Lean_IR_Borrow_mkInitParamMap___spec__1(x_1);
lean_dec(x_1);
return x_2;
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
LEAN_EXPORT lean_object* l_Std_AssocList_find_x3f___at_Lean_IR_Borrow_ApplyParamMap_visitFnBody___spec__2(lean_object* x_1, lean_object* x_2) {
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
x_7 = l___private_Lean_Compiler_IR_Borrow_0__Lean_IR_Borrow_ParamMap_beqKey____x40_Lean_Compiler_IR_Borrow___hyg_175_(x_4, x_1);
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
LEAN_EXPORT lean_object* l_Std_HashMapImp_find_x3f___at_Lean_IR_Borrow_ApplyParamMap_visitFnBody___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint64_t x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Lean_IR_Borrow_ParamMap_getHash(x_2);
x_6 = lean_uint64_to_usize(x_5);
x_7 = lean_usize_modn(x_6, x_4);
lean_dec(x_4);
x_8 = lean_array_uget(x_3, x_7);
lean_dec(x_3);
x_9 = l_Std_AssocList_find_x3f___at_Lean_IR_Borrow_ApplyParamMap_visitFnBody___spec__2(x_2, x_8);
lean_dec(x_8);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_IR_Borrow_ApplyParamMap_visitFnBody___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_IR_instInhabitedFnBody;
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_Borrow_ApplyParamMap_visitFnBody___spec__4(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_lt(x_4, x_3);
if (x_6 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; 
x_7 = lean_array_uget(x_5, x_4);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_uset(x_5, x_4, x_8);
x_10 = 1;
x_11 = lean_usize_add(x_4, x_10);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_7);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_7, 1);
lean_inc(x_2);
lean_inc(x_1);
x_14 = l_Lean_IR_Borrow_ApplyParamMap_visitFnBody(x_1, x_2, x_13);
lean_ctor_set(x_7, 1, x_14);
x_15 = lean_array_uset(x_9, x_4, x_7);
x_4 = x_11;
x_5 = x_15;
goto _start;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_7, 0);
x_18 = lean_ctor_get(x_7, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_7);
lean_inc(x_2);
lean_inc(x_1);
x_19 = l_Lean_IR_Borrow_ApplyParamMap_visitFnBody(x_1, x_2, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_17);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_array_uset(x_9, x_4, x_20);
x_4 = x_11;
x_5 = x_21;
goto _start;
}
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_7);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_7, 0);
lean_inc(x_2);
lean_inc(x_1);
x_25 = l_Lean_IR_Borrow_ApplyParamMap_visitFnBody(x_1, x_2, x_24);
lean_ctor_set(x_7, 0, x_25);
x_26 = lean_array_uset(x_9, x_4, x_7);
x_4 = x_11;
x_5 = x_26;
goto _start;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_7, 0);
lean_inc(x_28);
lean_dec(x_7);
lean_inc(x_2);
lean_inc(x_1);
x_29 = l_Lean_IR_Borrow_ApplyParamMap_visitFnBody(x_1, x_2, x_28);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = lean_array_uset(x_9, x_4, x_30);
x_4 = x_11;
x_5 = x_31;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_IR_Borrow_ApplyParamMap_visitFnBody___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Compiler.IR.Borrow", 23);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_Borrow_ApplyParamMap_visitFnBody___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.IR.Borrow.ApplyParamMap.visitFnBody", 40);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_Borrow_ApplyParamMap_visitFnBody___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unreachable code has been reached", 33);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_Borrow_ApplyParamMap_visitFnBody___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_IR_Borrow_ApplyParamMap_visitFnBody___closed__1;
x_2 = l_Lean_IR_Borrow_ApplyParamMap_visitFnBody___closed__2;
x_3 = lean_unsigned_to_nat(113u);
x_4 = lean_unsigned_to_nat(17u);
x_5 = l_Lean_IR_Borrow_ApplyParamMap_visitFnBody___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_ApplyParamMap_visitFnBody(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_3)) {
case 1:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 2);
x_7 = lean_ctor_get(x_3, 3);
x_8 = lean_ctor_get(x_3, 1);
lean_dec(x_8);
lean_inc(x_2);
lean_inc(x_1);
x_9 = l_Lean_IR_Borrow_ApplyParamMap_visitFnBody(x_1, x_2, x_6);
lean_inc(x_2);
lean_inc(x_1);
x_10 = l_Lean_IR_Borrow_ApplyParamMap_visitFnBody(x_1, x_2, x_7);
lean_inc(x_5);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_5);
x_12 = l_Std_HashMapImp_find_x3f___at_Lean_IR_Borrow_ApplyParamMap_visitFnBody___spec__1(x_2, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_10);
lean_dec(x_9);
lean_free_object(x_3);
lean_dec(x_5);
x_13 = l_Lean_IR_Borrow_ApplyParamMap_visitFnBody___closed__4;
x_14 = l_panic___at_Lean_IR_Borrow_ApplyParamMap_visitFnBody___spec__3(x_13);
return x_14;
}
else
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
lean_dec(x_12);
lean_ctor_set(x_3, 3, x_10);
lean_ctor_set(x_3, 2, x_9);
lean_ctor_set(x_3, 1, x_15);
return x_3;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_ctor_get(x_3, 0);
x_17 = lean_ctor_get(x_3, 2);
x_18 = lean_ctor_get(x_3, 3);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_19 = l_Lean_IR_Borrow_ApplyParamMap_visitFnBody(x_1, x_2, x_17);
lean_inc(x_2);
lean_inc(x_1);
x_20 = l_Lean_IR_Borrow_ApplyParamMap_visitFnBody(x_1, x_2, x_18);
lean_inc(x_16);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_1);
lean_ctor_set(x_21, 1, x_16);
x_22 = l_Std_HashMapImp_find_x3f___at_Lean_IR_Borrow_ApplyParamMap_visitFnBody___spec__1(x_2, x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_16);
x_23 = l_Lean_IR_Borrow_ApplyParamMap_visitFnBody___closed__4;
x_24 = l_panic___at_Lean_IR_Borrow_ApplyParamMap_visitFnBody___spec__3(x_23);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_22, 0);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_26, 0, x_16);
lean_ctor_set(x_26, 1, x_25);
lean_ctor_set(x_26, 2, x_19);
lean_ctor_set(x_26, 3, x_20);
return x_26;
}
}
}
case 10:
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_3);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; size_t x_30; size_t x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_3, 3);
x_29 = lean_array_get_size(x_28);
x_30 = lean_usize_of_nat(x_29);
lean_dec(x_29);
x_31 = 0;
x_32 = l_Array_mapMUnsafe_map___at_Lean_IR_Borrow_ApplyParamMap_visitFnBody___spec__4(x_1, x_2, x_30, x_31, x_28);
lean_ctor_set(x_3, 3, x_32);
return x_3;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; size_t x_38; size_t x_39; lean_object* x_40; lean_object* x_41; 
x_33 = lean_ctor_get(x_3, 0);
x_34 = lean_ctor_get(x_3, 1);
x_35 = lean_ctor_get(x_3, 2);
x_36 = lean_ctor_get(x_3, 3);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_3);
x_37 = lean_array_get_size(x_36);
x_38 = lean_usize_of_nat(x_37);
lean_dec(x_37);
x_39 = 0;
x_40 = l_Array_mapMUnsafe_map___at_Lean_IR_Borrow_ApplyParamMap_visitFnBody___spec__4(x_1, x_2, x_38, x_39, x_36);
x_41 = lean_alloc_ctor(10, 4, 0);
lean_ctor_set(x_41, 0, x_33);
lean_ctor_set(x_41, 1, x_34);
lean_ctor_set(x_41, 2, x_35);
lean_ctor_set(x_41, 3, x_40);
return x_41;
}
}
default: 
{
uint8_t x_42; 
x_42 = l_Lean_IR_FnBody_isTerminal(x_3);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_43 = l_Lean_IR_FnBody_body(x_3);
x_44 = lean_box(13);
x_45 = l_Lean_IR_FnBody_setBody(x_3, x_44);
x_46 = l_Lean_IR_Borrow_ApplyParamMap_visitFnBody(x_1, x_2, x_43);
x_47 = l_Lean_IR_FnBody_setBody(x_45, x_46);
return x_47;
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_AssocList_find_x3f___at_Lean_IR_Borrow_ApplyParamMap_visitFnBody___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_AssocList_find_x3f___at_Lean_IR_Borrow_ApplyParamMap_visitFnBody___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_Borrow_ApplyParamMap_visitFnBody___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_mapMUnsafe_map___at_Lean_IR_Borrow_ApplyParamMap_visitFnBody___spec__4(x_1, x_2, x_6, x_7, x_5);
return x_8;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_IR_Borrow_ApplyParamMap_visitDecls___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.IR.Borrow.ApplyParamMap.visitDecls", 39);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_IR_Borrow_ApplyParamMap_visitDecls___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_IR_Borrow_ApplyParamMap_visitFnBody___closed__1;
x_2 = l_Array_mapMUnsafe_map___at_Lean_IR_Borrow_ApplyParamMap_visitDecls___spec__1___closed__1;
x_3 = lean_unsigned_to_nat(129u);
x_4 = lean_unsigned_to_nat(19u);
x_5 = l_Lean_IR_Borrow_ApplyParamMap_visitFnBody___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_Borrow_ApplyParamMap_visitDecls___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_3, x_2);
if (x_5 == 0)
{
lean_dec(x_1);
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; 
x_6 = lean_array_uget(x_4, x_3);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_4, x_3, x_7);
x_9 = 1;
x_10 = lean_usize_add(x_3, x_9);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_6);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_ctor_get(x_6, 0);
x_13 = lean_ctor_get(x_6, 2);
x_14 = lean_ctor_get(x_6, 3);
x_15 = lean_ctor_get(x_6, 4);
x_16 = lean_ctor_get(x_6, 1);
lean_dec(x_16);
lean_inc(x_1);
lean_inc(x_12);
x_17 = l_Lean_IR_Borrow_ApplyParamMap_visitFnBody(x_12, x_1, x_14);
lean_inc(x_12);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_12);
lean_inc(x_1);
x_19 = l_Std_HashMapImp_find_x3f___at_Lean_IR_Borrow_ApplyParamMap_visitFnBody___spec__1(x_1, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_17);
lean_free_object(x_6);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
x_20 = l_Array_mapMUnsafe_map___at_Lean_IR_Borrow_ApplyParamMap_visitDecls___spec__1___closed__2;
x_21 = l_panic___at_Lean_IR_Decl_updateBody_x21___spec__1(x_20);
x_22 = lean_array_uset(x_8, x_3, x_21);
x_3 = x_10;
x_4 = x_22;
goto _start;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_19, 0);
lean_inc(x_24);
lean_dec(x_19);
lean_ctor_set(x_6, 3, x_17);
lean_ctor_set(x_6, 1, x_24);
x_25 = lean_array_uset(x_8, x_3, x_6);
x_3 = x_10;
x_4 = x_25;
goto _start;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_27 = lean_ctor_get(x_6, 0);
x_28 = lean_ctor_get(x_6, 2);
x_29 = lean_ctor_get(x_6, 3);
x_30 = lean_ctor_get(x_6, 4);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_6);
lean_inc(x_1);
lean_inc(x_27);
x_31 = l_Lean_IR_Borrow_ApplyParamMap_visitFnBody(x_27, x_1, x_29);
lean_inc(x_27);
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_27);
lean_inc(x_1);
x_33 = l_Std_HashMapImp_find_x3f___at_Lean_IR_Borrow_ApplyParamMap_visitFnBody___spec__1(x_1, x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_28);
lean_dec(x_27);
x_34 = l_Array_mapMUnsafe_map___at_Lean_IR_Borrow_ApplyParamMap_visitDecls___spec__1___closed__2;
x_35 = l_panic___at_Lean_IR_Decl_updateBody_x21___spec__1(x_34);
x_36 = lean_array_uset(x_8, x_3, x_35);
x_3 = x_10;
x_4 = x_36;
goto _start;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_33, 0);
lean_inc(x_38);
lean_dec(x_33);
x_39 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_39, 0, x_27);
lean_ctor_set(x_39, 1, x_38);
lean_ctor_set(x_39, 2, x_28);
lean_ctor_set(x_39, 3, x_31);
lean_ctor_set(x_39, 4, x_30);
x_40 = lean_array_uset(x_8, x_3, x_39);
x_3 = x_10;
x_4 = x_40;
goto _start;
}
}
}
else
{
lean_object* x_42; 
x_42 = lean_array_uset(x_8, x_3, x_6);
x_3 = x_10;
x_4 = x_42;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_ApplyParamMap_visitDecls(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; size_t x_4; size_t x_5; lean_object* x_6; 
x_3 = lean_array_get_size(x_1);
x_4 = lean_usize_of_nat(x_3);
lean_dec(x_3);
x_5 = 0;
x_6 = l_Array_mapMUnsafe_map___at_Lean_IR_Borrow_ApplyParamMap_visitDecls___spec__1(x_2, x_4, x_5, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_Borrow_ApplyParamMap_visitDecls___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at_Lean_IR_Borrow_ApplyParamMap_visitDecls___spec__1(x_1, x_5, x_6, x_4);
return x_7;
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
static lean_object* _init_l_Lean_IR_Borrow_BorrowInfCtx_currFn___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_Borrow_BorrowInfCtx_paramSet___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_mkHashMap___at_Lean_IR_Borrow_BorrowInfState_owned___default___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_mkHashMapImp___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_Borrow_BorrowInfState_owned___default() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Std_mkHashMapImp___rarg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_mkHashMap___at_Lean_IR_Borrow_BorrowInfState_owned___default___spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_mkHashMap___at_Lean_IR_Borrow_BorrowInfState_owned___default___spec__1(x_1);
lean_dec(x_1);
return x_2;
}
}
static uint8_t _init_l_Lean_IR_Borrow_BorrowInfState_modified___default() {
_start:
{
uint8_t x_1; 
x_1 = 0;
return x_1;
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
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_markModified___rarg(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_3 = 1;
lean_ctor_set_uint8(x_1, sizeof(void*)*2, x_3);
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_1);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_1);
x_8 = 1;
x_9 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_7);
lean_ctor_set_uint8(x_9, sizeof(void*)*2, x_8);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_markModified(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_IR_Borrow_markModified___rarg), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_markModified___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_IR_Borrow_markModified(x_1);
lean_dec(x_1);
return x_2;
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_4, 1);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_ctor_set(x_4, 1, x_1);
x_9 = l_Std_HashMapImp_contains___at_Lean_IR_Borrow_OwnedSet_contains___spec__1(x_7, x_4);
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_6);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_6, 1);
lean_dec(x_11);
x_12 = lean_ctor_get(x_6, 0);
lean_dec(x_12);
x_13 = lean_box(0);
x_14 = l_Std_HashMap_insert___at_Lean_IR_Borrow_OwnedSet_insert___spec__1(x_7, x_4, x_13);
x_15 = 1;
lean_ctor_set(x_6, 0, x_14);
lean_ctor_set_uint8(x_6, sizeof(void*)*2, x_15);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_6);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_6);
x_17 = lean_box(0);
x_18 = l_Std_HashMap_insert___at_Lean_IR_Borrow_OwnedSet_insert___spec__1(x_7, x_4, x_17);
x_19 = 1;
x_20 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_8);
lean_ctor_set_uint8(x_20, sizeof(void*)*2, x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_17);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_4);
lean_dec(x_8);
lean_dec(x_7);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_6);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_24 = lean_ctor_get(x_4, 1);
x_25 = lean_ctor_get(x_4, 0);
lean_inc(x_24);
lean_inc(x_25);
lean_dec(x_4);
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_25);
lean_ctor_set(x_28, 1, x_1);
x_29 = l_Std_HashMapImp_contains___at_Lean_IR_Borrow_OwnedSet_contains___spec__1(x_26, x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; 
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_30 = x_24;
} else {
 lean_dec_ref(x_24);
 x_30 = lean_box(0);
}
x_31 = lean_box(0);
x_32 = l_Std_HashMap_insert___at_Lean_IR_Borrow_OwnedSet_insert___spec__1(x_26, x_28, x_31);
x_33 = 1;
if (lean_is_scalar(x_30)) {
 x_34 = lean_alloc_ctor(0, 2, 1);
} else {
 x_34 = x_30;
}
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_27);
lean_ctor_set_uint8(x_34, sizeof(void*)*2, x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_31);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_Borrow_ownArgs___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_array_get_size(x_1);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_2);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = lean_nat_dec_le(x_4, x_4);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_4);
lean_dec(x_2);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_3);
return x_11;
}
else
{
size_t x_12; size_t x_13; lean_object* x_14; lean_object* x_15; 
x_12 = 0;
x_13 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_14 = lean_box(0);
x_15 = l_Array_foldlMUnsafe_fold___at_Lean_IR_Borrow_ownArgs___spec__1(x_1, x_12, x_13, x_14, x_2, x_3);
lean_dec(x_2);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_Borrow_ownArgs___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l_Array_foldlMUnsafe_fold___at_Lean_IR_Borrow_ownArgs___spec__1(x_1, x_7, x_8, x_4, x_5, x_6);
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
x_8 = l_Std_HashMapImp_contains___at_Lean_IR_Borrow_OwnedSet_contains___spec__1(x_7, x_4);
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
x_11 = lean_ctor_get(x_4, 0);
x_12 = lean_ctor_get(x_4, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_4);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_1);
x_15 = l_Std_HashMapImp_contains___at_Lean_IR_Borrow_OwnedSet_contains___spec__1(x_13, x_14);
lean_dec(x_14);
lean_dec(x_13);
x_16 = lean_box(x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_12);
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_Borrow_updateParamMap___spec__1(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_array_uget(x_3, x_2);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_array_uset(x_3, x_2, x_9);
x_11 = lean_ctor_get_uint8(x_8, sizeof(void*)*2);
if (x_11 == 0)
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = 1;
x_13 = lean_usize_add(x_2, x_12);
x_14 = lean_array_uset(x_10, x_2, x_8);
x_2 = x_13;
x_3 = x_14;
goto _start;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_16 = lean_ctor_get(x_8, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_8, 1);
lean_inc(x_17);
lean_inc(x_16);
x_18 = l_Lean_IR_Borrow_isOwned(x_16, x_4, x_5);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_unbox(x_19);
lean_dec(x_19);
if (x_20 == 0)
{
lean_object* x_21; size_t x_22; size_t x_23; lean_object* x_24; 
lean_dec(x_17);
lean_dec(x_16);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = 1;
x_23 = lean_usize_add(x_2, x_22);
x_24 = lean_array_uset(x_10, x_2, x_8);
x_2 = x_23;
x_3 = x_24;
x_5 = x_21;
goto _start;
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_8);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; size_t x_33; size_t x_34; lean_object* x_35; 
x_27 = lean_ctor_get(x_8, 1);
lean_dec(x_27);
x_28 = lean_ctor_get(x_8, 0);
lean_dec(x_28);
x_29 = lean_ctor_get(x_18, 1);
lean_inc(x_29);
lean_dec(x_18);
x_30 = l_Lean_IR_Borrow_markModified___rarg(x_29);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec(x_30);
x_32 = 0;
lean_ctor_set_uint8(x_8, sizeof(void*)*2, x_32);
x_33 = 1;
x_34 = lean_usize_add(x_2, x_33);
x_35 = lean_array_uset(x_10, x_2, x_8);
x_2 = x_34;
x_3 = x_35;
x_5 = x_31;
goto _start;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; size_t x_42; size_t x_43; lean_object* x_44; 
lean_dec(x_8);
x_37 = lean_ctor_get(x_18, 1);
lean_inc(x_37);
lean_dec(x_18);
x_38 = l_Lean_IR_Borrow_markModified___rarg(x_37);
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
lean_dec(x_38);
x_40 = 0;
x_41 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_41, 0, x_16);
lean_ctor_set(x_41, 1, x_17);
lean_ctor_set_uint8(x_41, sizeof(void*)*2, x_40);
x_42 = 1;
x_43 = lean_usize_add(x_2, x_42);
x_44 = lean_array_uset(x_10, x_2, x_41);
x_2 = x_43;
x_3 = x_44;
x_5 = x_39;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_updateParamMap(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_inc(x_1);
x_5 = l_Std_HashMapImp_find_x3f___at_Lean_IR_Borrow_ApplyParamMap_visitFnBody___spec__1(x_4, x_1);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_1);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; uint8_t x_13; 
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
lean_dec(x_5);
x_9 = lean_array_get_size(x_8);
x_10 = lean_usize_of_nat(x_9);
lean_dec(x_9);
x_11 = 0;
x_12 = l_Array_mapMUnsafe_map___at_Lean_IR_Borrow_updateParamMap___spec__1(x_10, x_11, x_8, x_2, x_3);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_12, 1);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_12, 0);
x_17 = lean_ctor_get(x_14, 1);
x_18 = l_Std_HashMap_insert___at_Lean_IR_Borrow_InitParamMap_visitFnBody___spec__1(x_17, x_1, x_16);
lean_ctor_set(x_14, 1, x_18);
x_19 = lean_box(0);
lean_ctor_set(x_12, 0, x_19);
return x_12;
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_20 = lean_ctor_get(x_12, 0);
x_21 = lean_ctor_get(x_14, 0);
x_22 = lean_ctor_get_uint8(x_14, sizeof(void*)*2);
x_23 = lean_ctor_get(x_14, 1);
lean_inc(x_23);
lean_inc(x_21);
lean_dec(x_14);
x_24 = l_Std_HashMap_insert___at_Lean_IR_Borrow_InitParamMap_visitFnBody___spec__1(x_23, x_1, x_20);
x_25 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_25, 0, x_21);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set_uint8(x_25, sizeof(void*)*2, x_22);
x_26 = lean_box(0);
lean_ctor_set(x_12, 1, x_25);
lean_ctor_set(x_12, 0, x_26);
return x_12;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_27 = lean_ctor_get(x_12, 1);
x_28 = lean_ctor_get(x_12, 0);
lean_inc(x_27);
lean_inc(x_28);
lean_dec(x_12);
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
x_30 = lean_ctor_get_uint8(x_27, sizeof(void*)*2);
x_31 = lean_ctor_get(x_27, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_32 = x_27;
} else {
 lean_dec_ref(x_27);
 x_32 = lean_box(0);
}
x_33 = l_Std_HashMap_insert___at_Lean_IR_Borrow_InitParamMap_visitFnBody___spec__1(x_31, x_1, x_28);
if (lean_is_scalar(x_32)) {
 x_34 = lean_alloc_ctor(0, 2, 1);
} else {
 x_34 = x_32;
}
lean_ctor_set(x_34, 0, x_29);
lean_ctor_set(x_34, 1, x_33);
lean_ctor_set_uint8(x_34, sizeof(void*)*2, x_30);
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
return x_36;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_Borrow_updateParamMap___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = l_Array_mapMUnsafe_map___at_Lean_IR_Borrow_updateParamMap___spec__1(x_6, x_7, x_3, x_4, x_5);
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
static lean_object* _init_l_panic___at_Lean_IR_Borrow_getParamInfo___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Id_instMonadId;
x_2 = l_StateT_instMonadStateT___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_panic___at_Lean_IR_Borrow_getParamInfo___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_panic___at_Lean_IR_Borrow_getParamInfo___spec__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_panic___at_Lean_IR_Borrow_getParamInfo___spec__1___closed__1;
x_2 = l_panic___at_Lean_IR_Borrow_getParamInfo___spec__1___closed__2;
x_3 = l_instInhabited___rarg(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_panic___at_Lean_IR_Borrow_getParamInfo___spec__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_panic___at_Lean_IR_Borrow_getParamInfo___spec__1___closed__3;
x_2 = lean_alloc_closure((void*)(l_instInhabitedReaderT___rarg___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_IR_Borrow_getParamInfo___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = l_panic___at_Lean_IR_Borrow_getParamInfo___spec__1___closed__4;
x_5 = lean_panic_fn(x_4, x_1);
x_6 = lean_apply_2(x_5, x_2, x_3);
return x_6;
}
}
static lean_object* _init_l_Lean_IR_Borrow_getParamInfo___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.IR.Borrow.getParamInfo", 27);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_Borrow_getParamInfo___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_IR_Borrow_ApplyParamMap_visitFnBody___closed__1;
x_2 = l_Lean_IR_Borrow_getParamInfo___closed__1;
x_3 = lean_unsigned_to_nat(202u);
x_4 = lean_unsigned_to_nat(21u);
x_5 = l_Lean_IR_Borrow_ApplyParamMap_visitFnBody___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_IR_Borrow_getParamInfo___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_IR_Borrow_ApplyParamMap_visitFnBody___closed__1;
x_2 = l_Lean_IR_Borrow_getParamInfo___closed__1;
x_3 = lean_unsigned_to_nat(203u);
x_4 = lean_unsigned_to_nat(11u);
x_5 = l_Lean_IR_Borrow_ApplyParamMap_visitFnBody___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_getParamInfo(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_inc(x_1);
x_5 = l_Std_HashMapImp_find_x3f___at_Lean_IR_Borrow_ApplyParamMap_visitFnBody___spec__1(x_4, x_1);
if (lean_obj_tag(x_5) == 0)
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
x_8 = lean_ir_find_env_decl(x_7, x_6);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = l_Lean_IR_Borrow_getParamInfo___closed__2;
x_10 = l_panic___at_Lean_IR_Borrow_getParamInfo___spec__1(x_9, x_2, x_3);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_2);
x_11 = lean_ctor_get(x_8, 0);
lean_inc(x_11);
lean_dec(x_8);
x_12 = l_Lean_IR_Decl_params(x_11);
lean_dec(x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_3);
return x_13;
}
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_1);
x_14 = l_Lean_IR_Borrow_getParamInfo___closed__3;
x_15 = l_panic___at_Lean_IR_Borrow_getParamInfo___spec__1(x_14, x_2, x_3);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_2);
lean_dec(x_1);
x_16 = lean_ctor_get(x_5, 0);
lean_inc(x_16);
lean_dec(x_5);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_3);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_IR_Borrow_ownArgsUsingParams___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_IR_instInhabitedArg;
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Nat_forM_loop___at_Lean_IR_Borrow_ownArgsUsingParams___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Init.Util", 9);
return x_1;
}
}
static lean_object* _init_l_Nat_forM_loop___at_Lean_IR_Borrow_ownArgsUsingParams___spec__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("getElem!", 8);
return x_1;
}
}
static lean_object* _init_l_Nat_forM_loop___at_Lean_IR_Borrow_ownArgsUsingParams___spec__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("index out of bounds", 19);
return x_1;
}
}
static lean_object* _init_l_Nat_forM_loop___at_Lean_IR_Borrow_ownArgsUsingParams___spec__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Nat_forM_loop___at_Lean_IR_Borrow_ownArgsUsingParams___spec__2___closed__1;
x_2 = l_Nat_forM_loop___at_Lean_IR_Borrow_ownArgsUsingParams___spec__2___closed__2;
x_3 = lean_unsigned_to_nat(62u);
x_4 = lean_unsigned_to_nat(36u);
x_5 = l_Nat_forM_loop___at_Lean_IR_Borrow_ownArgsUsingParams___spec__2___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Nat_forM_loop___at_Lean_IR_Borrow_ownArgsUsingParams___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_5, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; uint8_t x_16; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_sub(x_5, x_10);
lean_dec(x_5);
x_12 = lean_nat_sub(x_4, x_11);
x_13 = lean_nat_sub(x_12, x_10);
lean_dec(x_12);
x_14 = lean_nat_dec_lt(x_13, x_3);
x_15 = lean_array_get_size(x_2);
x_16 = lean_nat_dec_lt(x_13, x_15);
lean_dec(x_15);
if (x_14 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = l_Nat_forM_loop___at_Lean_IR_Borrow_ownArgsUsingParams___spec__2___closed__4;
x_18 = l_panic___at_Lean_IR_Borrow_ownArgsUsingParams___spec__1(x_17);
if (x_16 == 0)
{
lean_object* x_19; uint8_t x_20; 
lean_dec(x_13);
x_19 = l_panic___at_Lean_IR_addParamsRename___spec__1(x_17);
x_20 = lean_ctor_get_uint8(x_19, sizeof(void*)*2);
lean_dec(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = l_Lean_IR_Borrow_ownArg(x_18, x_6, x_7);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_5 = x_11;
x_7 = x_22;
goto _start;
}
else
{
lean_dec(x_18);
x_5 = x_11;
goto _start;
}
}
else
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_array_fget(x_2, x_13);
lean_dec(x_13);
x_26 = lean_ctor_get_uint8(x_25, sizeof(void*)*2);
lean_dec(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = l_Lean_IR_Borrow_ownArg(x_18, x_6, x_7);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_5 = x_11;
x_7 = x_28;
goto _start;
}
else
{
lean_dec(x_18);
x_5 = x_11;
goto _start;
}
}
}
else
{
lean_object* x_31; 
x_31 = lean_array_fget(x_1, x_13);
if (x_16 == 0)
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
lean_dec(x_13);
x_32 = l_Nat_forM_loop___at_Lean_IR_Borrow_ownArgsUsingParams___spec__2___closed__4;
x_33 = l_panic___at_Lean_IR_addParamsRename___spec__1(x_32);
x_34 = lean_ctor_get_uint8(x_33, sizeof(void*)*2);
lean_dec(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = l_Lean_IR_Borrow_ownArg(x_31, x_6, x_7);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
x_5 = x_11;
x_7 = x_36;
goto _start;
}
else
{
lean_dec(x_31);
x_5 = x_11;
goto _start;
}
}
else
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_array_fget(x_2, x_13);
lean_dec(x_13);
x_40 = lean_ctor_get_uint8(x_39, sizeof(void*)*2);
lean_dec(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = l_Lean_IR_Borrow_ownArg(x_31, x_6, x_7);
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
lean_dec(x_41);
x_5 = x_11;
x_7 = x_42;
goto _start;
}
else
{
lean_dec(x_31);
x_5 = x_11;
goto _start;
}
}
}
}
else
{
lean_object* x_45; lean_object* x_46; 
lean_dec(x_5);
x_45 = lean_box(0);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_7);
return x_46;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_ownArgsUsingParams(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_array_get_size(x_1);
lean_inc(x_5);
x_6 = l_Nat_forM_loop___at_Lean_IR_Borrow_ownArgsUsingParams___spec__2(x_1, x_2, x_5, x_5, x_5, x_3, x_4);
lean_dec(x_3);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Nat_forM_loop___at_Lean_IR_Borrow_ownArgsUsingParams___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Nat_forM_loop___at_Lean_IR_Borrow_ownArgsUsingParams___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_ownArgsUsingParams___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_Borrow_ownArgsUsingParams(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Nat_forM_loop___at_Lean_IR_Borrow_ownParamsUsingArgs___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_5, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; uint8_t x_16; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_sub(x_5, x_10);
lean_dec(x_5);
x_12 = lean_nat_sub(x_4, x_11);
x_13 = lean_nat_sub(x_12, x_10);
lean_dec(x_12);
x_14 = lean_nat_dec_lt(x_13, x_3);
x_15 = lean_array_get_size(x_2);
x_16 = lean_nat_dec_lt(x_13, x_15);
lean_dec(x_15);
if (x_14 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = l_Nat_forM_loop___at_Lean_IR_Borrow_ownArgsUsingParams___spec__2___closed__4;
x_18 = l_panic___at_Lean_IR_Borrow_ownArgsUsingParams___spec__1(x_17);
if (x_16 == 0)
{
lean_dec(x_13);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec(x_18);
x_20 = l_panic___at_Lean_IR_addParamsRename___spec__1(x_17);
x_21 = l_Lean_IR_Borrow_isOwned(x_19, x_6, x_7);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_unbox(x_22);
lean_dec(x_22);
if (x_23 == 0)
{
lean_object* x_24; 
lean_dec(x_20);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_5 = x_11;
x_7 = x_24;
goto _start;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_21, 1);
lean_inc(x_26);
lean_dec(x_21);
x_27 = lean_ctor_get(x_20, 0);
lean_inc(x_27);
lean_dec(x_20);
x_28 = l_Lean_IR_Borrow_ownVar(x_27, x_6, x_26);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_5 = x_11;
x_7 = x_29;
goto _start;
}
}
else
{
x_5 = x_11;
goto _start;
}
}
else
{
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_32 = lean_ctor_get(x_18, 0);
lean_inc(x_32);
lean_dec(x_18);
x_33 = lean_array_fget(x_2, x_13);
lean_dec(x_13);
x_34 = l_Lean_IR_Borrow_isOwned(x_32, x_6, x_7);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_unbox(x_35);
lean_dec(x_35);
if (x_36 == 0)
{
lean_object* x_37; 
lean_dec(x_33);
x_37 = lean_ctor_get(x_34, 1);
lean_inc(x_37);
lean_dec(x_34);
x_5 = x_11;
x_7 = x_37;
goto _start;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_39 = lean_ctor_get(x_34, 1);
lean_inc(x_39);
lean_dec(x_34);
x_40 = lean_ctor_get(x_33, 0);
lean_inc(x_40);
lean_dec(x_33);
x_41 = l_Lean_IR_Borrow_ownVar(x_40, x_6, x_39);
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
lean_dec(x_41);
x_5 = x_11;
x_7 = x_42;
goto _start;
}
}
else
{
lean_dec(x_13);
x_5 = x_11;
goto _start;
}
}
}
else
{
lean_object* x_45; 
x_45 = lean_array_fget(x_1, x_13);
if (x_16 == 0)
{
lean_dec(x_13);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
lean_dec(x_45);
x_47 = l_Nat_forM_loop___at_Lean_IR_Borrow_ownArgsUsingParams___spec__2___closed__4;
x_48 = l_panic___at_Lean_IR_addParamsRename___spec__1(x_47);
x_49 = l_Lean_IR_Borrow_isOwned(x_46, x_6, x_7);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_unbox(x_50);
lean_dec(x_50);
if (x_51 == 0)
{
lean_object* x_52; 
lean_dec(x_48);
x_52 = lean_ctor_get(x_49, 1);
lean_inc(x_52);
lean_dec(x_49);
x_5 = x_11;
x_7 = x_52;
goto _start;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_54 = lean_ctor_get(x_49, 1);
lean_inc(x_54);
lean_dec(x_49);
x_55 = lean_ctor_get(x_48, 0);
lean_inc(x_55);
lean_dec(x_48);
x_56 = l_Lean_IR_Borrow_ownVar(x_55, x_6, x_54);
x_57 = lean_ctor_get(x_56, 1);
lean_inc(x_57);
lean_dec(x_56);
x_5 = x_11;
x_7 = x_57;
goto _start;
}
}
else
{
x_5 = x_11;
goto _start;
}
}
else
{
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_60 = lean_ctor_get(x_45, 0);
lean_inc(x_60);
lean_dec(x_45);
x_61 = lean_array_fget(x_2, x_13);
lean_dec(x_13);
x_62 = l_Lean_IR_Borrow_isOwned(x_60, x_6, x_7);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_unbox(x_63);
lean_dec(x_63);
if (x_64 == 0)
{
lean_object* x_65; 
lean_dec(x_61);
x_65 = lean_ctor_get(x_62, 1);
lean_inc(x_65);
lean_dec(x_62);
x_5 = x_11;
x_7 = x_65;
goto _start;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_67 = lean_ctor_get(x_62, 1);
lean_inc(x_67);
lean_dec(x_62);
x_68 = lean_ctor_get(x_61, 0);
lean_inc(x_68);
lean_dec(x_61);
x_69 = l_Lean_IR_Borrow_ownVar(x_68, x_6, x_67);
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
lean_dec(x_69);
x_5 = x_11;
x_7 = x_70;
goto _start;
}
}
else
{
lean_dec(x_13);
x_5 = x_11;
goto _start;
}
}
}
}
else
{
lean_object* x_73; lean_object* x_74; 
lean_dec(x_5);
x_73 = lean_box(0);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_7);
return x_74;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_ownParamsUsingArgs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_array_get_size(x_1);
lean_inc(x_5);
x_6 = l_Nat_forM_loop___at_Lean_IR_Borrow_ownParamsUsingArgs___spec__1(x_1, x_2, x_5, x_5, x_5, x_3, x_4);
lean_dec(x_3);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Nat_forM_loop___at_Lean_IR_Borrow_ownParamsUsingArgs___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Nat_forM_loop___at_Lean_IR_Borrow_ownParamsUsingArgs___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_ownParamsUsingArgs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_Borrow_ownParamsUsingArgs(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_Borrow_ownArgsIfParam___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_eq(x_3, x_4);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_5);
x_9 = lean_array_uget(x_2, x_3);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_ctor_get(x_1, 3);
x_12 = l_Std_RBNode_findCore___at_Lean_IR_UniqueIds_checkId___spec__1(x_11, x_10);
if (lean_obj_tag(x_12) == 0)
{
size_t x_13; size_t x_14; lean_object* x_15; 
lean_dec(x_10);
x_13 = 1;
x_14 = lean_usize_add(x_3, x_13);
x_15 = lean_box(0);
x_3 = x_14;
x_5 = x_15;
goto _start;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; 
lean_dec(x_12);
x_17 = l_Lean_IR_Borrow_ownVar(x_10, x_6, x_7);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = 1;
x_21 = lean_usize_add(x_3, x_20);
x_3 = x_21;
x_5 = x_18;
x_7 = x_19;
goto _start;
}
}
else
{
size_t x_23; size_t x_24; lean_object* x_25; 
x_23 = 1;
x_24 = lean_usize_add(x_3, x_23);
x_25 = lean_box(0);
x_3 = x_24;
x_5 = x_25;
goto _start;
}
}
else
{
lean_object* x_27; 
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_5);
lean_ctor_set(x_27, 1, x_7);
return x_27;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_ownArgsIfParam(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_array_get_size(x_1);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = lean_nat_dec_le(x_4, x_4);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_4);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_3);
return x_11;
}
else
{
size_t x_12; size_t x_13; lean_object* x_14; lean_object* x_15; 
x_12 = 0;
x_13 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_14 = lean_box(0);
x_15 = l_Array_foldlMUnsafe_fold___at_Lean_IR_Borrow_ownArgsIfParam___spec__1(x_2, x_1, x_12, x_13, x_14, x_2, x_3);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_Borrow_ownArgsIfParam___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = l_Array_foldlMUnsafe_fold___at_Lean_IR_Borrow_ownArgsIfParam___spec__1(x_1, x_2, x_8, x_9, x_5, x_6, x_7);
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
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_collectExpr___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = l_Lean_IR_Borrow_isOwned(x_1, x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_unbox(x_7);
lean_dec(x_7);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_2);
x_9 = !lean_is_exclusive(x_6);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_6, 0);
lean_dec(x_10);
x_11 = lean_box(0);
lean_ctor_set(x_6, 0, x_11);
return x_6;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_6, 1);
lean_inc(x_12);
lean_dec(x_6);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_6, 1);
lean_inc(x_15);
lean_dec(x_6);
x_16 = l_Lean_IR_Borrow_ownVar(x_2, x_4, x_15);
return x_16;
}
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
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_ctor_get(x_2, 1);
lean_inc(x_20);
lean_dec(x_2);
lean_inc(x_20);
x_21 = l_Lean_IR_Borrow_isOwned(x_20, x_3, x_4);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_unbox(x_22);
lean_dec(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_box(0);
x_26 = l_Lean_IR_Borrow_collectExpr___lambda__1(x_1, x_20, x_25, x_3, x_24);
lean_dec(x_3);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = lean_ctor_get(x_21, 1);
lean_inc(x_27);
lean_dec(x_21);
lean_inc(x_1);
x_28 = l_Lean_IR_Borrow_ownVar(x_1, x_3, x_27);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = l_Lean_IR_Borrow_collectExpr___lambda__1(x_1, x_20, x_29, x_3, x_30);
lean_dec(x_3);
lean_dec(x_29);
return x_31;
}
}
case 6:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_32 = lean_ctor_get(x_2, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_2, 1);
lean_inc(x_33);
lean_dec(x_2);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_32);
lean_inc(x_3);
x_35 = l_Lean_IR_Borrow_getParamInfo(x_34, x_3, x_4);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = l_Lean_IR_Borrow_ownVar(x_1, x_3, x_37);
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
lean_dec(x_38);
x_40 = l_Lean_IR_Borrow_ownArgsUsingParams(x_33, x_36, x_3, x_39);
lean_dec(x_36);
lean_dec(x_33);
return x_40;
}
case 7:
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_ctor_get(x_2, 1);
lean_inc(x_41);
lean_dec(x_2);
x_42 = l_Lean_IR_Borrow_ownVar(x_1, x_3, x_4);
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec(x_42);
x_44 = l_Lean_IR_Borrow_ownArgs(x_41, x_3, x_43);
lean_dec(x_41);
return x_44;
}
case 8:
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_45 = lean_ctor_get(x_2, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_2, 1);
lean_inc(x_46);
lean_dec(x_2);
x_47 = l_Lean_IR_Borrow_ownVar(x_1, x_3, x_4);
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
lean_dec(x_47);
x_49 = l_Lean_IR_Borrow_ownVar(x_45, x_3, x_48);
x_50 = lean_ctor_get(x_49, 1);
lean_inc(x_50);
lean_dec(x_49);
x_51 = l_Lean_IR_Borrow_ownArgs(x_46, x_3, x_50);
lean_dec(x_46);
return x_51;
}
default: 
{
lean_object* x_52; lean_object* x_53; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_52 = lean_box(0);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_4);
return x_53;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_collectExpr___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_Borrow_collectExpr___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_IR_Borrow_preserveTailCall___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = l_Lean_IR_Decl_name(x_6);
lean_dec(x_6);
x_8 = lean_name_eq(x_7, x_1);
lean_dec(x_7);
if (x_8 == 0)
{
size_t x_9; size_t x_10; 
x_9 = 1;
x_10 = lean_usize_add(x_3, x_9);
x_3 = x_10;
goto _start;
}
else
{
uint8_t x_12; 
x_12 = 1;
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = 0;
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_preserveTailCall(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_2) == 6)
{
if (lean_obj_tag(x_3) == 11)
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_3, 0);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_ctor_get(x_2, 1);
x_9 = lean_ctor_get(x_6, 0);
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
x_11 = lean_array_get_size(x_10);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_nat_dec_lt(x_12, x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_4);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_5);
return x_15;
}
else
{
uint8_t x_16; 
x_16 = lean_nat_dec_le(x_11, x_11);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_4);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_5);
return x_18;
}
else
{
size_t x_19; size_t x_20; uint8_t x_21; 
x_19 = 0;
x_20 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_21 = l_Array_anyMUnsafe_any___at_Lean_IR_Borrow_preserveTailCall___spec__1(x_7, x_10, x_19, x_20);
lean_dec(x_10);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_4);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_5);
return x_23;
}
else
{
uint8_t x_24; 
x_24 = lean_nat_dec_eq(x_1, x_9);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_4);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_5);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_inc(x_7);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_7);
lean_inc(x_4);
x_28 = l_Lean_IR_Borrow_getParamInfo(x_27, x_4, x_5);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = l_Lean_IR_Borrow_ownParamsUsingArgs(x_8, x_29, x_4, x_30);
lean_dec(x_29);
return x_31;
}
}
}
}
}
else
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_4);
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_5);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_4);
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_5);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_4);
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_5);
return x_37;
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_IR_Borrow_preserveTailCall___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at_Lean_IR_Borrow_preserveTailCall___spec__1(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_preserveTailCall___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_Borrow_preserveTailCall(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_Borrow_updateParamSet___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
x_10 = lean_box(0);
x_11 = l_Std_RBNode_insert___at_Lean_IR_mkIndexSet___spec__1(x_4, x_7, x_10);
x_2 = x_9;
x_4 = x_11;
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
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_1, 3);
x_5 = lean_array_get_size(x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_lt(x_6, x_5);
if (x_7 == 0)
{
lean_dec(x_5);
return x_1;
}
else
{
uint8_t x_8; 
x_8 = lean_nat_dec_le(x_5, x_5);
if (x_8 == 0)
{
lean_dec(x_5);
return x_1;
}
else
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = 0;
x_10 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_11 = l_Array_foldlMUnsafe_fold___at_Lean_IR_Borrow_updateParamSet___spec__1(x_2, x_9, x_10, x_4);
lean_ctor_set(x_1, 3, x_11);
return x_1;
}
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_ctor_get(x_1, 1);
x_14 = lean_ctor_get(x_1, 2);
x_15 = lean_ctor_get(x_1, 3);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_1);
x_16 = lean_array_get_size(x_2);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_nat_dec_lt(x_17, x_16);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_16);
x_19 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_19, 0, x_12);
lean_ctor_set(x_19, 1, x_13);
lean_ctor_set(x_19, 2, x_14);
lean_ctor_set(x_19, 3, x_15);
return x_19;
}
else
{
uint8_t x_20; 
x_20 = lean_nat_dec_le(x_16, x_16);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_16);
x_21 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_21, 0, x_12);
lean_ctor_set(x_21, 1, x_13);
lean_ctor_set(x_21, 2, x_14);
lean_ctor_set(x_21, 3, x_15);
return x_21;
}
else
{
size_t x_22; size_t x_23; lean_object* x_24; lean_object* x_25; 
x_22 = 0;
x_23 = lean_usize_of_nat(x_16);
lean_dec(x_16);
x_24 = l_Array_foldlMUnsafe_fold___at_Lean_IR_Borrow_updateParamSet___spec__1(x_2, x_22, x_23, x_15);
x_25 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_25, 0, x_12);
lean_ctor_set(x_25, 1, x_13);
lean_ctor_set(x_25, 2, x_14);
lean_ctor_set(x_25, 3, x_24);
return x_25;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_Borrow_updateParamSet___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lean_IR_Borrow_updateParamSet___spec__1(x_1, x_5, x_6, x_4);
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_Borrow_collectFnBody___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_2, x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; 
lean_dec(x_4);
x_8 = lean_array_uget(x_1, x_2);
x_9 = l_Lean_IR_AltCore_body(x_8);
lean_dec(x_8);
lean_inc(x_5);
x_10 = l_Lean_IR_Borrow_collectFnBody(x_9, x_5, x_6);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = 1;
x_14 = lean_usize_add(x_2, x_13);
x_2 = x_14;
x_4 = x_11;
x_6 = x_12;
goto _start;
}
else
{
lean_object* x_16; 
lean_dec(x_5);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_4);
lean_ctor_set(x_16, 1, x_6);
return x_16;
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
lean_dec(x_5);
lean_dec(x_4);
return x_11;
}
case 1:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
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
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_ctor_get(x_2, 2);
lean_inc(x_19);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_12);
x_21 = l_Lean_IR_Borrow_updateParamMap(x_20, x_2, x_18);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_1 = x_15;
x_3 = x_22;
goto _start;
}
case 10:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_ctor_get(x_1, 3);
lean_inc(x_24);
lean_dec(x_1);
x_25 = lean_array_get_size(x_24);
x_26 = lean_unsigned_to_nat(0u);
x_27 = lean_nat_dec_lt(x_26, x_25);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_2);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_3);
return x_29;
}
else
{
uint8_t x_30; 
x_30 = lean_nat_dec_le(x_25, x_25);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_2);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_3);
return x_32;
}
else
{
size_t x_33; size_t x_34; lean_object* x_35; lean_object* x_36; 
x_33 = 0;
x_34 = lean_usize_of_nat(x_25);
lean_dec(x_25);
x_35 = lean_box(0);
x_36 = l_Array_foldlMUnsafe_fold___at_Lean_IR_Borrow_collectFnBody___spec__1(x_24, x_33, x_34, x_35, x_2, x_3);
lean_dec(x_24);
return x_36;
}
}
}
case 12:
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_37 = lean_ctor_get(x_1, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_1, 1);
lean_inc(x_38);
lean_dec(x_1);
x_39 = lean_ctor_get(x_2, 2);
lean_inc(x_39);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_37);
lean_inc(x_2);
x_41 = l_Lean_IR_Borrow_getParamInfo(x_40, x_2, x_3);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
lean_inc(x_2);
x_44 = l_Lean_IR_Borrow_ownArgsUsingParams(x_38, x_42, x_2, x_43);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
x_46 = l_Lean_IR_Borrow_ownParamsUsingArgs(x_38, x_42, x_2, x_45);
lean_dec(x_42);
lean_dec(x_38);
return x_46;
}
default: 
{
uint8_t x_47; 
x_47 = l_Lean_IR_FnBody_isTerminal(x_1);
if (x_47 == 0)
{
lean_object* x_48; 
x_48 = l_Lean_IR_FnBody_body(x_1);
lean_dec(x_1);
x_1 = x_48;
goto _start;
}
else
{
lean_object* x_50; lean_object* x_51; 
lean_dec(x_2);
lean_dec(x_1);
x_50 = lean_box(0);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_3);
return x_51;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_Borrow_collectFnBody___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l_Array_foldlMUnsafe_fold___at_Lean_IR_Borrow_collectFnBody___spec__1(x_1, x_7, x_8, x_4, x_5, x_6);
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
uint8_t x_5; lean_object* x_6; uint8_t x_7; 
x_5 = 0;
lean_ctor_set_uint8(x_3, sizeof(void*)*2, x_5);
lean_inc(x_1);
lean_inc(x_2);
x_6 = lean_apply_2(x_1, x_2, x_3);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_6, 1);
x_9 = lean_ctor_get(x_6, 0);
lean_dec(x_9);
x_10 = lean_ctor_get_uint8(x_8, sizeof(void*)*2);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_2);
lean_dec(x_1);
x_11 = lean_box(0);
lean_ctor_set(x_6, 0, x_11);
return x_6;
}
else
{
lean_free_object(x_6);
x_3 = x_8;
goto _start;
}
}
else
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_6, 1);
lean_inc(x_13);
lean_dec(x_6);
x_14 = lean_ctor_get_uint8(x_13, sizeof(void*)*2);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_2);
lean_dec(x_1);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_13);
return x_16;
}
else
{
x_3 = x_13;
goto _start;
}
}
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_18 = lean_ctor_get(x_3, 0);
x_19 = lean_ctor_get(x_3, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_3);
x_20 = 0;
x_21 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_19);
lean_ctor_set_uint8(x_21, sizeof(void*)*2, x_20);
lean_inc(x_1);
lean_inc(x_2);
x_22 = lean_apply_2(x_1, x_2, x_21);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_24 = x_22;
} else {
 lean_dec_ref(x_22);
 x_24 = lean_box(0);
}
x_25 = lean_ctor_get_uint8(x_23, sizeof(void*)*2);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_2);
lean_dec(x_1);
x_26 = lean_box(0);
if (lean_is_scalar(x_24)) {
 x_27 = lean_alloc_ctor(0, 2, 0);
} else {
 x_27 = x_24;
}
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_23);
return x_27;
}
else
{
lean_dec(x_24);
x_3 = x_23;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_ReaderT_pure___at_Lean_IR_Borrow_collectDecls___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_ReaderT_pure___at_Lean_IR_Borrow_collectDecls___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_ReaderT_pure___at_Lean_IR_Borrow_collectDecls___spec__1___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_Borrow_collectDecls___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
static lean_object* _init_l_Lean_IR_Borrow_collectDecls___boxed__const__1() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_usize(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_collectDecls(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_array_get_size(x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
lean_dec(x_4);
lean_dec(x_3);
x_7 = lean_box(0);
x_8 = lean_alloc_closure((void*)(l_ReaderT_pure___at_Lean_IR_Borrow_collectDecls___spec__1___rarg___boxed), 3, 1);
lean_closure_set(x_8, 0, x_7);
x_9 = l_Lean_IR_Borrow_whileModifing(x_8, x_1, x_2);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_9, 1);
x_12 = lean_ctor_get(x_9, 0);
lean_dec(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_ctor_set(x_9, 0, x_13);
return x_9;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_dec(x_9);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = lean_nat_dec_le(x_4, x_4);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
lean_dec(x_4);
lean_dec(x_3);
x_18 = lean_box(0);
x_19 = lean_alloc_closure((void*)(l_ReaderT_pure___at_Lean_IR_Borrow_collectDecls___spec__1___rarg___boxed), 3, 1);
lean_closure_set(x_19, 0, x_18);
x_20 = l_Lean_IR_Borrow_whileModifing(x_19, x_1, x_2);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_20, 1);
x_23 = lean_ctor_get(x_20, 0);
lean_dec(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_ctor_set(x_20, 0, x_24);
return x_20;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_20, 1);
lean_inc(x_25);
lean_dec(x_20);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
else
{
size_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_28 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_29 = lean_box(0);
x_30 = l_Lean_IR_Borrow_collectDecls___boxed__const__1;
x_31 = lean_box_usize(x_28);
x_32 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lean_IR_Borrow_collectDecls___spec__2___boxed), 6, 4);
lean_closure_set(x_32, 0, x_3);
lean_closure_set(x_32, 1, x_30);
lean_closure_set(x_32, 2, x_31);
lean_closure_set(x_32, 3, x_29);
x_33 = l_Lean_IR_Borrow_whileModifing(x_32, x_1, x_2);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_33, 1);
x_36 = lean_ctor_get(x_33, 0);
lean_dec(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_ctor_set(x_33, 0, x_37);
return x_33;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_33, 1);
lean_inc(x_38);
lean_dec(x_33);
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
return x_40;
}
}
}
}
}
LEAN_EXPORT lean_object* l_ReaderT_pure___at_Lean_IR_Borrow_collectDecls___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_ReaderT_pure___at_Lean_IR_Borrow_collectDecls___spec__1___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_Borrow_collectDecls___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l_Array_foldlMUnsafe_fold___at_Lean_IR_Borrow_collectDecls___spec__2(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec(x_1);
return x_9;
}
}
static lean_object* _init_l_Lean_IR_Borrow_infer___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Std_mkHashMapImp___rarg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Borrow_infer(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_3 = lean_box(0);
x_4 = lean_box(0);
lean_inc(x_2);
lean_inc(x_1);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_4);
lean_ctor_set(x_5, 3, x_3);
x_6 = l_Lean_IR_Borrow_mkInitParamMap(x_1, x_2);
lean_dec(x_2);
x_7 = l_Lean_IR_Borrow_infer___closed__1;
x_8 = 0;
x_9 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_6);
lean_ctor_set_uint8(x_9, sizeof(void*)*2, x_8);
x_10 = l_Lean_IR_Borrow_collectDecls(x_5, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_inferBorrow(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_IR_getEnv___rarg(x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_1);
x_7 = l_Lean_IR_Borrow_infer(x_6, x_1);
x_8 = l_Lean_IR_Borrow_ApplyParamMap_visitDecls(x_1, x_7);
lean_ctor_set(x_4, 0, x_8);
return x_4;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_4);
lean_inc(x_1);
x_11 = l_Lean_IR_Borrow_infer(x_9, x_1);
x_12 = l_Lean_IR_Borrow_ApplyParamMap_visitDecls(x_1, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
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
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_ExportAttr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_IR_CompilerM(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_IR_NormIds(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_IR_Borrow(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_ExportAttr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_CompilerM(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_NormIds(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_IR_Borrow_OwnedSet_instBEqKey___closed__1 = _init_l_Lean_IR_Borrow_OwnedSet_instBEqKey___closed__1();
lean_mark_persistent(l_Lean_IR_Borrow_OwnedSet_instBEqKey___closed__1);
l_Lean_IR_Borrow_OwnedSet_instBEqKey = _init_l_Lean_IR_Borrow_OwnedSet_instBEqKey();
lean_mark_persistent(l_Lean_IR_Borrow_OwnedSet_instBEqKey);
l_Lean_IR_Borrow_OwnedSet_instHashableKey___closed__1 = _init_l_Lean_IR_Borrow_OwnedSet_instHashableKey___closed__1();
lean_mark_persistent(l_Lean_IR_Borrow_OwnedSet_instHashableKey___closed__1);
l_Lean_IR_Borrow_OwnedSet_instHashableKey = _init_l_Lean_IR_Borrow_OwnedSet_instHashableKey();
lean_mark_persistent(l_Lean_IR_Borrow_OwnedSet_instHashableKey);
l_Lean_IR_Borrow_ParamMap_instBEqKey___closed__1 = _init_l_Lean_IR_Borrow_ParamMap_instBEqKey___closed__1();
lean_mark_persistent(l_Lean_IR_Borrow_ParamMap_instBEqKey___closed__1);
l_Lean_IR_Borrow_ParamMap_instBEqKey = _init_l_Lean_IR_Borrow_ParamMap_instBEqKey();
lean_mark_persistent(l_Lean_IR_Borrow_ParamMap_instBEqKey);
l_Lean_IR_Borrow_ParamMap_instHashableKey___closed__1 = _init_l_Lean_IR_Borrow_ParamMap_instHashableKey___closed__1();
lean_mark_persistent(l_Lean_IR_Borrow_ParamMap_instHashableKey___closed__1);
l_Lean_IR_Borrow_ParamMap_instHashableKey = _init_l_Lean_IR_Borrow_ParamMap_instHashableKey();
lean_mark_persistent(l_Lean_IR_Borrow_ParamMap_instHashableKey);
l_Std_AssocList_foldlM___at_Lean_IR_Borrow_ParamMap_fmt___spec__1___closed__1 = _init_l_Std_AssocList_foldlM___at_Lean_IR_Borrow_ParamMap_fmt___spec__1___closed__1();
lean_mark_persistent(l_Std_AssocList_foldlM___at_Lean_IR_Borrow_ParamMap_fmt___spec__1___closed__1);
l_Std_AssocList_foldlM___at_Lean_IR_Borrow_ParamMap_fmt___spec__1___closed__2 = _init_l_Std_AssocList_foldlM___at_Lean_IR_Borrow_ParamMap_fmt___spec__1___closed__2();
lean_mark_persistent(l_Std_AssocList_foldlM___at_Lean_IR_Borrow_ParamMap_fmt___spec__1___closed__2);
l_Std_AssocList_foldlM___at_Lean_IR_Borrow_ParamMap_fmt___spec__1___closed__3 = _init_l_Std_AssocList_foldlM___at_Lean_IR_Borrow_ParamMap_fmt___spec__1___closed__3();
lean_mark_persistent(l_Std_AssocList_foldlM___at_Lean_IR_Borrow_ParamMap_fmt___spec__1___closed__3);
l_Std_AssocList_foldlM___at_Lean_IR_Borrow_ParamMap_fmt___spec__1___closed__4 = _init_l_Std_AssocList_foldlM___at_Lean_IR_Borrow_ParamMap_fmt___spec__1___closed__4();
lean_mark_persistent(l_Std_AssocList_foldlM___at_Lean_IR_Borrow_ParamMap_fmt___spec__1___closed__4);
l_Std_AssocList_foldlM___at_Lean_IR_Borrow_ParamMap_fmt___spec__1___closed__5 = _init_l_Std_AssocList_foldlM___at_Lean_IR_Borrow_ParamMap_fmt___spec__1___closed__5();
lean_mark_persistent(l_Std_AssocList_foldlM___at_Lean_IR_Borrow_ParamMap_fmt___spec__1___closed__5);
l_Lean_IR_Borrow_ParamMap_fmt___closed__1 = _init_l_Lean_IR_Borrow_ParamMap_fmt___closed__1();
lean_mark_persistent(l_Lean_IR_Borrow_ParamMap_fmt___closed__1);
l_Lean_IR_Borrow_ParamMap_fmt___closed__2 = _init_l_Lean_IR_Borrow_ParamMap_fmt___closed__2();
lean_mark_persistent(l_Lean_IR_Borrow_ParamMap_fmt___closed__2);
l_Lean_IR_Borrow_ParamMap_fmt___closed__3 = _init_l_Lean_IR_Borrow_ParamMap_fmt___closed__3();
lean_mark_persistent(l_Lean_IR_Borrow_ParamMap_fmt___closed__3);
l_Lean_IR_Borrow_ParamMap_fmt___closed__4 = _init_l_Lean_IR_Borrow_ParamMap_fmt___closed__4();
lean_mark_persistent(l_Lean_IR_Borrow_ParamMap_fmt___closed__4);
l_Lean_IR_Borrow_ParamMap_fmt___closed__5 = _init_l_Lean_IR_Borrow_ParamMap_fmt___closed__5();
lean_mark_persistent(l_Lean_IR_Borrow_ParamMap_fmt___closed__5);
l_Lean_IR_Borrow_ParamMap_fmt___closed__6 = _init_l_Lean_IR_Borrow_ParamMap_fmt___closed__6();
lean_mark_persistent(l_Lean_IR_Borrow_ParamMap_fmt___closed__6);
l_Lean_IR_Borrow_ParamMap_fmt___closed__7 = _init_l_Lean_IR_Borrow_ParamMap_fmt___closed__7();
lean_mark_persistent(l_Lean_IR_Borrow_ParamMap_fmt___closed__7);
l_Lean_IR_Borrow_ParamMap_fmt___closed__8 = _init_l_Lean_IR_Borrow_ParamMap_fmt___closed__8();
lean_mark_persistent(l_Lean_IR_Borrow_ParamMap_fmt___closed__8);
l_Lean_IR_Borrow_instToFormatParamMap___closed__1 = _init_l_Lean_IR_Borrow_instToFormatParamMap___closed__1();
lean_mark_persistent(l_Lean_IR_Borrow_instToFormatParamMap___closed__1);
l_Lean_IR_Borrow_instToFormatParamMap = _init_l_Lean_IR_Borrow_instToFormatParamMap();
lean_mark_persistent(l_Lean_IR_Borrow_instToFormatParamMap);
l_Lean_IR_Borrow_ApplyParamMap_visitFnBody___closed__1 = _init_l_Lean_IR_Borrow_ApplyParamMap_visitFnBody___closed__1();
lean_mark_persistent(l_Lean_IR_Borrow_ApplyParamMap_visitFnBody___closed__1);
l_Lean_IR_Borrow_ApplyParamMap_visitFnBody___closed__2 = _init_l_Lean_IR_Borrow_ApplyParamMap_visitFnBody___closed__2();
lean_mark_persistent(l_Lean_IR_Borrow_ApplyParamMap_visitFnBody___closed__2);
l_Lean_IR_Borrow_ApplyParamMap_visitFnBody___closed__3 = _init_l_Lean_IR_Borrow_ApplyParamMap_visitFnBody___closed__3();
lean_mark_persistent(l_Lean_IR_Borrow_ApplyParamMap_visitFnBody___closed__3);
l_Lean_IR_Borrow_ApplyParamMap_visitFnBody___closed__4 = _init_l_Lean_IR_Borrow_ApplyParamMap_visitFnBody___closed__4();
lean_mark_persistent(l_Lean_IR_Borrow_ApplyParamMap_visitFnBody___closed__4);
l_Array_mapMUnsafe_map___at_Lean_IR_Borrow_ApplyParamMap_visitDecls___spec__1___closed__1 = _init_l_Array_mapMUnsafe_map___at_Lean_IR_Borrow_ApplyParamMap_visitDecls___spec__1___closed__1();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_IR_Borrow_ApplyParamMap_visitDecls___spec__1___closed__1);
l_Array_mapMUnsafe_map___at_Lean_IR_Borrow_ApplyParamMap_visitDecls___spec__1___closed__2 = _init_l_Array_mapMUnsafe_map___at_Lean_IR_Borrow_ApplyParamMap_visitDecls___spec__1___closed__2();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_IR_Borrow_ApplyParamMap_visitDecls___spec__1___closed__2);
l_Lean_IR_Borrow_BorrowInfCtx_currFn___default = _init_l_Lean_IR_Borrow_BorrowInfCtx_currFn___default();
lean_mark_persistent(l_Lean_IR_Borrow_BorrowInfCtx_currFn___default);
l_Lean_IR_Borrow_BorrowInfCtx_paramSet___default = _init_l_Lean_IR_Borrow_BorrowInfCtx_paramSet___default();
lean_mark_persistent(l_Lean_IR_Borrow_BorrowInfCtx_paramSet___default);
l_Lean_IR_Borrow_BorrowInfState_owned___default = _init_l_Lean_IR_Borrow_BorrowInfState_owned___default();
lean_mark_persistent(l_Lean_IR_Borrow_BorrowInfState_owned___default);
l_Lean_IR_Borrow_BorrowInfState_modified___default = _init_l_Lean_IR_Borrow_BorrowInfState_modified___default();
l_panic___at_Lean_IR_Borrow_getParamInfo___spec__1___closed__1 = _init_l_panic___at_Lean_IR_Borrow_getParamInfo___spec__1___closed__1();
lean_mark_persistent(l_panic___at_Lean_IR_Borrow_getParamInfo___spec__1___closed__1);
l_panic___at_Lean_IR_Borrow_getParamInfo___spec__1___closed__2 = _init_l_panic___at_Lean_IR_Borrow_getParamInfo___spec__1___closed__2();
lean_mark_persistent(l_panic___at_Lean_IR_Borrow_getParamInfo___spec__1___closed__2);
l_panic___at_Lean_IR_Borrow_getParamInfo___spec__1___closed__3 = _init_l_panic___at_Lean_IR_Borrow_getParamInfo___spec__1___closed__3();
lean_mark_persistent(l_panic___at_Lean_IR_Borrow_getParamInfo___spec__1___closed__3);
l_panic___at_Lean_IR_Borrow_getParamInfo___spec__1___closed__4 = _init_l_panic___at_Lean_IR_Borrow_getParamInfo___spec__1___closed__4();
lean_mark_persistent(l_panic___at_Lean_IR_Borrow_getParamInfo___spec__1___closed__4);
l_Lean_IR_Borrow_getParamInfo___closed__1 = _init_l_Lean_IR_Borrow_getParamInfo___closed__1();
lean_mark_persistent(l_Lean_IR_Borrow_getParamInfo___closed__1);
l_Lean_IR_Borrow_getParamInfo___closed__2 = _init_l_Lean_IR_Borrow_getParamInfo___closed__2();
lean_mark_persistent(l_Lean_IR_Borrow_getParamInfo___closed__2);
l_Lean_IR_Borrow_getParamInfo___closed__3 = _init_l_Lean_IR_Borrow_getParamInfo___closed__3();
lean_mark_persistent(l_Lean_IR_Borrow_getParamInfo___closed__3);
l_Nat_forM_loop___at_Lean_IR_Borrow_ownArgsUsingParams___spec__2___closed__1 = _init_l_Nat_forM_loop___at_Lean_IR_Borrow_ownArgsUsingParams___spec__2___closed__1();
lean_mark_persistent(l_Nat_forM_loop___at_Lean_IR_Borrow_ownArgsUsingParams___spec__2___closed__1);
l_Nat_forM_loop___at_Lean_IR_Borrow_ownArgsUsingParams___spec__2___closed__2 = _init_l_Nat_forM_loop___at_Lean_IR_Borrow_ownArgsUsingParams___spec__2___closed__2();
lean_mark_persistent(l_Nat_forM_loop___at_Lean_IR_Borrow_ownArgsUsingParams___spec__2___closed__2);
l_Nat_forM_loop___at_Lean_IR_Borrow_ownArgsUsingParams___spec__2___closed__3 = _init_l_Nat_forM_loop___at_Lean_IR_Borrow_ownArgsUsingParams___spec__2___closed__3();
lean_mark_persistent(l_Nat_forM_loop___at_Lean_IR_Borrow_ownArgsUsingParams___spec__2___closed__3);
l_Nat_forM_loop___at_Lean_IR_Borrow_ownArgsUsingParams___spec__2___closed__4 = _init_l_Nat_forM_loop___at_Lean_IR_Borrow_ownArgsUsingParams___spec__2___closed__4();
lean_mark_persistent(l_Nat_forM_loop___at_Lean_IR_Borrow_ownArgsUsingParams___spec__2___closed__4);
l_Lean_IR_Borrow_collectDecls___boxed__const__1 = _init_l_Lean_IR_Borrow_collectDecls___boxed__const__1();
lean_mark_persistent(l_Lean_IR_Borrow_collectDecls___boxed__const__1);
l_Lean_IR_Borrow_infer___closed__1 = _init_l_Lean_IR_Borrow_infer___closed__1();
lean_mark_persistent(l_Lean_IR_Borrow_infer___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
