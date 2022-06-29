// Lean compiler output
// Module: Lean.Compiler.IR.EmitC
// Imports: Init Lean.Runtime Lean.Compiler.NameMangling Lean.Compiler.ExportAttr Lean.Compiler.InitAttr Lean.Compiler.IR.CompilerM Lean.Compiler.IR.EmitUtil Lean.Compiler.IR.NormIds Lean.Compiler.IR.SimpCase Lean.Compiler.IR.Boxing
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
LEAN_EXPORT lean_object* l_Nat_forM_loop___at_Lean_IR_EmitC_emitDeclAux___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitFnBody___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_revFold___at_Lean_IR_EmitC_emitFnDecls___spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_EmitC_emitFileHeader___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitMarkPersistent___closed__1;
static lean_object* l_Lean_IR_EmitC_emitCase___closed__1;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitBlock___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_argToCString___closed__1;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitReuse___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitSSet___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_toStringArgs(lean_object*);
static lean_object* l_Lean_IR_EmitC_emitSProj___closed__4;
static lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_EmitC_emitFileHeader___spec__1___closed__1;
static lean_object* l_Lean_IR_EmitC_toCType___closed__7;
static lean_object* l_Lean_IR_EmitC_emitFileHeader___closed__1;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitCInitName(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_toCName___closed__3;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitInc___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_List_forM___at_Lean_IR_EmitC_emitFnDecls___spec__5___closed__2;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitMarkPersistent___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Std_HashMapImp_find_x3f___at_Lean_IR_EmitC_getJPParams___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitUnbox___closed__4;
static lean_object* l_Lean_IR_EmitC_emitFileHeader___closed__4;
static lean_object* l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__19;
static lean_object* l_Lean_IR_EmitC_emitInc___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_quoteString___lambda__1(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitSetTag(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at_Lean_IR_EmitC_emitMainFn___spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitProj(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__11;
static lean_object* l_Lean_IR_EmitC_emitMainFn___lambda__3___closed__3;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitDel___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitMainFn___lambda__4___closed__1;
static lean_object* l_Lean_IR_EmitC_emitMainFn___closed__1;
static lean_object* l_Lean_IR_EmitC_emitFileHeader___closed__8;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitFileHeader___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitDeclAux___lambda__1___closed__1;
static lean_object* l_Lean_IR_EmitC_emitDel___closed__1;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emit(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at_Lean_IR_EmitC_emitFnDecls___spec__1(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_IR_EmitC_emitFileHeader___closed__17;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitDeclAux___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitIsShared(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_throwUnknownVar___rarg___closed__1;
lean_object* l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitMainFn___lambda__4___closed__2;
static lean_object* l_Lean_IR_EmitC_emitInitFn___closed__10;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_declareVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitCase___closed__2;
LEAN_EXPORT lean_object* l_List_foldl___at_Lean_IR_EmitC_emitFnDecls___spec__1___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitFileHeader___closed__11;
extern lean_object* l_Lean_builtinInitAttr;
LEAN_EXPORT lean_object* l_Nat_anyAux___at_Lean_IR_EmitC_overwriteParam___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitFnDeclAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitAllocCtor___closed__1;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitCName___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitFnDeclAux(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_forM_loop___at_Lean_IR_EmitC_emitFnDeclAux___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitMainFn___closed__2;
lean_object* lean_name_mk_string(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitCtor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Nat_foldM_loop___at_Lean_IR_EmitC_emitSimpleExternalCall___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitAllocCtor___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_toCType___closed__3;
static lean_object* l_Lean_IR_EmitC_emitInc___closed__3;
static lean_object* l_Lean_IR_EmitC_emitFileHeader___closed__9;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_getDecl___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_toHexDigit(lean_object*);
static lean_object* l_Lean_IR_EmitC_emitDeclInit___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitJmp___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_imports(lean_object*);
static lean_object* l_Lean_IR_EmitC_getDecl___closed__1;
static lean_object* l_Lean_IR_EmitC_emitSProj___closed__2;
static lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_EmitC_emitFileHeader___spec__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_throwUnknownVar___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_forM_loop___at_Lean_IR_EmitC_emitArgs___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_collectUsedDecls(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitSSet___closed__6;
static lean_object* l_Lean_IR_EmitC_emitInc___closed__5;
static lean_object* l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__20;
LEAN_EXPORT lean_object* l_Nat_forM_loop___at_Lean_IR_EmitC_emitDeclAux___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_getDecl___closed__2;
static lean_object* l_Lean_IR_EmitC_emitSProj___closed__1;
static lean_object* l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__10;
static lean_object* l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitSProj(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_forM_loop___at_Lean_IR_EmitC_emitJmp___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_environment_find(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_getEnv___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_toCType___closed__5;
static lean_object* l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__7;
static lean_object* l_Lean_IR_EmitC_emitUnbox___closed__2;
static lean_object* l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__8;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitVDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitDeclAux___lambda__2___closed__1;
lean_object* l_Lean_expandExternPattern(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitDel(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_closureMaxArgs;
uint8_t l_Lean_IR_IRType_isIrrelevant(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitMarkPersistent(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitMainFn___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitFnDeclAux___closed__2;
static lean_object* l_Lean_IR_EmitC_emitApp___closed__3;
static lean_object* l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__17;
LEAN_EXPORT lean_object* lean_ir_emit_c(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Nat_anyAux___at_Lean_IR_EmitC_overwriteParam___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitApp___closed__5;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitLhs___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitMainFn___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitBlock___closed__2;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_Context_mainFn___default;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitUnbox___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitReset___closed__4;
static lean_object* l_Lean_IR_EmitC_emitFileHeader___closed__19;
static lean_object* l_Lean_IR_EmitC_emitFnDeclAux___closed__1;
static lean_object* l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__9;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitSProj___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitLn___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__3;
lean_object* lean_array_get_size(lean_object*);
static lean_object* l_Lean_IR_EmitC_emitReuse___closed__2;
lean_object* lean_string_append(lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitBlock___closed__1;
static lean_object* l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__16;
static lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_EmitC_emitCase___spec__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitFnDecl(lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_quoteString___closed__2;
lean_object* l_Lean_getExternNameFor(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_quoteString___closed__1;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_quoteString___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitSet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_EmitC_emitCase___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_forM_loop___at_Lean_IR_EmitC_emitCtorSetArgs___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_EmitC_emitCase___spec__1___closed__1;
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_hasMainFn___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitMainFn___lambda__4___closed__3;
lean_object* lean_string_utf8_byte_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitCtorScalarSize(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_isTailCallTo(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_throwUnknownVar___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_EmitC_emitInitFn___spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitInitFn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_declareVars(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_forM_loop___at_Lean_IR_EmitC_emitFnDeclAux___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitCtorSetArgs(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitUnbox___closed__1;
uint8_t l_Lean_IR_IRType_isObj(lean_object*);
LEAN_EXPORT lean_object* l_Nat_forM_loop___at_Lean_IR_EmitC_emitDeclAux___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Nat_forM_loop___at_Lean_IR_EmitC_emitJmp___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Std_AssocList_find_x3f___at_Lean_IR_EmitC_getJPParams___spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitFnDeclAux___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitFnDecls(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_forM_loop___at_Lean_IR_EmitC_emitReset___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitOffset___closed__2;
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitApp___closed__4;
LEAN_EXPORT lean_object* l_Nat_foldM_loop___at_Lean_IR_EmitC_emitSimpleExternalCall___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitMainFn___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_forM_loop___at_Lean_IR_EmitC_emitTailCall___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_toCType___closed__6;
lean_object* l_Lean_IR_Decl_resultType(lean_object*);
static lean_object* l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__13;
static lean_object* l_Lean_IR_EmitC_emitMainFn___lambda__3___closed__1;
lean_object* l_Lean_IR_Decl_name(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitUnbox___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitFnBody___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitInc___closed__2;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_toCInitName___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitLns___at_Lean_IR_EmitC_emitMainFn___spec__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitFileHeader___closed__25;
LEAN_EXPORT lean_object* l_List_forM___at_Lean_IR_EmitC_emitFnDecls___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitJmp___closed__1;
static lean_object* l_Lean_IR_EmitC_emitFnDeclAux___lambda__3___closed__4;
size_t lean_uint64_to_usize(uint64_t);
static lean_object* l_Lean_IR_EmitC_toCInitName___closed__1;
static lean_object* l_Lean_IR_EmitC_leanMainFn___closed__1;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_main(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emit___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_forM_loop___at_Lean_IR_EmitC_emitFnDeclAux___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitIf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitReset(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__26;
lean_object* l_Lean_IR_AltCore_body(lean_object*);
LEAN_EXPORT lean_object* l_Nat_forM_loop___at_Lean_IR_EmitC_emitCtorSetArgs___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Nat_anyAux___at_Lean_IR_EmitC_overwriteParam___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_argToCString(lean_object*);
static lean_object* l_Lean_IR_EmitC_emitFileHeader___closed__6;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitMainFn___lambda__3(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitReset___closed__3;
LEAN_EXPORT lean_object* l_List_forM___at_Lean_IR_EmitC_emitLns___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isExternC(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitFnDeclAux___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitInc___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_isIf___boxed(lean_object*);
lean_object* lean_get_init_fn_name_for(lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_argToCString___closed__2;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitCtorScalarSize___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitCtorScalarSize___closed__1;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitApp___closed__2;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_EmitC_emitCase___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitDeclAux___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_toCInitName(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_overwriteParam___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitTailCall___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_800____at_Lean_IR_IRType_beq___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitTag___closed__1;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitTailCall(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_getDecls(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitUProj(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitFnDeclAux___lambda__3___closed__3;
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitTag___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitApp___closed__1;
static lean_object* l_Lean_IR_EmitC_emitInitFn___closed__5;
static lean_object* l_Lean_IR_EmitC_toCType___closed__2;
static lean_object* l_Lean_IR_EmitC_emitTailCall___lambda__2___closed__2;
static lean_object* l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__31;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitDeclInit___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_forM_loop___at_Lean_IR_EmitC_emitFnDeclAux___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitExternCall___closed__1;
LEAN_EXPORT lean_object* l_Nat_forM_loop___at_Lean_IR_EmitC_emitTailCall___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_toHexDigit___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Nat_anyAux___at_Lean_IR_EmitC_overwriteParam___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitNumLit___closed__3;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitFnDeclAux___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_Context_mainParams___default;
LEAN_EXPORT lean_object* l_List_forM___at_Lean_IR_EmitC_emitInitFn___spec__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitCtor___closed__1;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitExternCall___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitLns___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitLhs(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitCtor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitSimpleExternalCall___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitBoxFn___closed__4;
lean_object* l_panic___at_Lean_TSyntax_getString___spec__1(lean_object*);
static lean_object* l_Lean_IR_EmitC_emitMainFn___lambda__3___closed__2;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitJmp(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__6;
lean_object* l_Std_mkHashMapImp___rarg(lean_object*);
static lean_object* l_Lean_IR_EmitC_toCName___closed__4;
static lean_object* l_Lean_IR_EmitC_emitDeclAux___lambda__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitMainFnIfNeeded(lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitFileHeader___closed__13;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_hasMainFn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitOffset___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_forM_loop___at_Lean_IR_EmitC_emitJmp___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_FnBody_isTerminal(lean_object*);
static lean_object* l_Lean_IR_EmitC_emitTailCall___lambda__2___closed__1;
static lean_object* l_Lean_IR_EmitC_emitUnbox___closed__5;
static lean_object* l_Lean_IR_EmitC_emitFileHeader___closed__23;
static lean_object* l_Lean_IR_EmitC_emitIf___closed__2;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitArgs(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_Context_mainParams___default___closed__1;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitPartialApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitBox___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at_Lean_IR_EmitC_emitLns___spec__1(lean_object*);
static lean_object* l_Lean_IR_EmitC_toCName___closed__1;
lean_object* l_Nat_repr(lean_object*);
static lean_object* l_Lean_IR_EmitC_toCType___closed__8;
static lean_object* l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__1;
static lean_object* l_Lean_IR_EmitC_emitDeclInit___closed__2;
static lean_object* l_Lean_IR_EmitC_emitSet___closed__1;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitBox(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_EmitC_emitInitFn___spec__2___closed__1;
static lean_object* l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitSet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitReset___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitOffset___closed__1;
static lean_object* l_Lean_IR_EmitC_emitLn___rarg___closed__1;
static lean_object* l_Lean_IR_EmitC_toCName___closed__2;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_EmitC_emitInitFn___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitDeclInit___closed__1;
static lean_object* l_Lean_IR_EmitC_emitIf___closed__3;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitArgs___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_toCType___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitLn___at_Lean_IR_EmitC_emitMainFn___spec__2(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitReset___closed__1;
static lean_object* l_Lean_IR_EmitC_emitSProj___closed__3;
static lean_object* l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__11;
static lean_object* l_Lean_IR_EmitC_emitFileHeader___closed__21;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_toCName(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitJPs___closed__1;
static lean_object* l_Lean_IR_EmitC_emitInitFn___closed__7;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitDeclInit(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitMainFn___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__12;
static lean_object* l_Lean_IR_EmitC_emitIf___closed__1;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_toCName___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitFnDeclAux___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitFileHeader___closed__2;
static lean_object* l_Lean_IR_EmitC_toCType___closed__1;
static lean_object* l_Lean_IR_EmitC_emitFnDeclAux___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitInc(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_leanMainFn;
static lean_object* l_Nat_forM_loop___at_Lean_IR_EmitC_emitFnDeclAux___spec__1___closed__1;
uint64_t lean_uint64_of_nat(lean_object*);
static lean_object* l_Lean_IR_EmitC_emitNumLit___closed__4;
static lean_object* l_Lean_IR_EmitC_emitDecl___closed__1;
uint32_t l_Nat_digitChar(lean_object*);
static lean_object* l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__15;
size_t lean_usize_modn(size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_throwInvalidExportName(lean_object*);
static lean_object* l_Lean_IR_EmitC_emitFileHeader___closed__16;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_declareVar(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_toCType___closed__9;
uint8_t l_Array_isEmpty___rarg(lean_object*);
extern lean_object* l_Lean_IR_instInhabitedParam;
LEAN_EXPORT lean_object* l_Std_AssocList_find_x3f___at_Lean_IR_EmitC_getJPParams___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_forM_loop___at_Lean_IR_EmitC_emitReset___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitIsShared___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitInitFn___closed__1;
static lean_object* l_Lean_IR_EmitC_emitIsTaggedPtr___closed__1;
static lean_object* l_Lean_IR_EmitC_Context_jpMap___default___closed__1;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitMainFn___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedConstantInfo;
LEAN_EXPORT lean_object* l_panic___at_Lean_IR_EmitC_emitMainFn___spec__4(lean_object*);
static lean_object* l_Lean_IR_EmitC_emitBoxFn___closed__2;
static lean_object* l_Lean_IR_EmitC_toCType___closed__4;
LEAN_EXPORT lean_object* l_Std_RBTree_toList___at_Lean_IR_EmitC_emitFnDecls___spec__3(lean_object*);
static lean_object* l_Lean_IR_EmitC_emitProj___closed__1;
static lean_object* l_Lean_IR_EmitC_emitIsShared___closed__1;
static lean_object* l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__5;
static lean_object* l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitMainFn(lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__18;
static lean_object* l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__17;
static lean_object* l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__14;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_EmitC_emitFileHeader___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitDeclAux___lambda__3___closed__2;
static lean_object* l_Lean_IR_EmitC_quoteString___lambda__1___closed__5;
static lean_object* l_Lean_IR_EmitC_emitFileHeader___closed__14;
static lean_object* l_Lean_IR_EmitC_emitFileHeader___closed__7;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitUProj___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldr___at_Lean_IR_EmitC_hasMainFn___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitCInitName___boxed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitReuse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_NameSet_empty;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitFnBody(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitMainFn___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_foldr___at_Lean_IR_EmitC_hasMainFn___spec__1(uint8_t, lean_object*);
lean_object* l_Lean_IR_ensureHasDefault(lean_object*);
LEAN_EXPORT lean_object* l_Nat_forM_loop___at_Lean_IR_EmitC_emitArgs___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitUProj___closed__1;
static lean_object* l_Lean_IR_EmitC_emitUnbox___closed__3;
static lean_object* l_Lean_IR_EmitC_emitBoxFn___closed__3;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitNumLit(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitExternCall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitTailCall___lambda__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitMainFn___lambda__4___closed__4;
lean_object* lean_ir_decl_to_string(lean_object*);
static lean_object* l_Lean_IR_EmitC_quoteString___lambda__1___closed__3;
uint8_t l_Lean_hasInitAttr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_forM_loop___at_Lean_IR_EmitC_emitFnDeclAux___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_Context_jpMap___default;
extern lean_object* l_Lean_exportAttr;
static lean_object* l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__21;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitSimpleExternalCall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitUSet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitFnDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_declareParams(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at_Lean_IR_EmitC_emitFnDecls___spec__2(lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_EmitC_emitInitFn___spec__3___closed__1;
static lean_object* l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__2;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_EmitC_emitInitFn___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitReset___closed__2;
static lean_object* l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitAllocCtor(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitLn___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_quoteString___lambda__1___boxed(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitTailCall___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitLit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_quoteString___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitJmp___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__16;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitTailCall___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitExternDeclAux(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at_Lean_IR_EmitC_emitLns___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_quoteString___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_declareParams___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitJmp___lambda__1___closed__1;
static lean_object* l_Lean_IR_EmitC_emitFileHeader___closed__15;
static lean_object* l_Lean_IR_EmitC_emitDec___closed__2;
static lean_object* l_Lean_IR_EmitC_emitSetTag___closed__1;
static lean_object* l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__7;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitFnDeclAux___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitSetTag___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitSProj___closed__5;
static lean_object* l_Lean_IR_EmitC_emitTailCall___lambda__1___closed__1;
lean_object* lean_mk_module_initialization_function_name(lean_object*);
static lean_object* l_Lean_IR_EmitC_toCType___closed__11;
static lean_object* l_Lean_IR_EmitC_emitFnDeclAux___lambda__2___closed__1;
static lean_object* l_Lean_IR_EmitC_emitFileHeader___closed__3;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitReuse(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitLns(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_paramEqArg___boxed(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__19;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_EmitC_emitFnDeclAux___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitFileHeader(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitDeclAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitNumLit___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitUSet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitInitFn___closed__3;
static lean_object* l_Lean_IR_EmitC_emitBoxFn___closed__1;
static lean_object* l_Lean_IR_EmitC_emitInc___closed__4;
static lean_object* l_Lean_IR_EmitC_quoteString___lambda__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitDeclAux___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitFileHeader___closed__5;
static lean_object* l_Nat_forM_loop___at_Lean_IR_EmitC_emitReset___spec__1___closed__1;
static lean_object* l_Lean_IR_EmitC_emitUSet___closed__1;
static lean_object* l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__8;
LEAN_EXPORT lean_object* l_Nat_forM_loop___at_Lean_IR_EmitC_emitTailCall___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitNumLit___closed__2;
static lean_object* l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__9;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_isTailCall___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitBoxFn___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitFileHeader___closed__22;
static lean_object* l_Lean_IR_EmitC_emitFileFooter___closed__1;
lean_object* l_Lean_ParametricAttribute_getParam___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_foldlAux_loop___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitFileHeader___closed__18;
uint8_t l_Lean_IR_ExplicitBoxing_isBoxedName(lean_object*);
static lean_object* l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__4;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitIsTaggedPtr(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitInitFn___closed__6;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitProj___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_EmitC_overwriteParam(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at_Lean_IR_EmitC_emitFns___spec__1(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isIOUnitInitFn(lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__27;
lean_object* l_Lean_getExternEntryFor(lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitNumLit___closed__1;
static lean_object* l_Lean_IR_EmitC_emitSSet___closed__5;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTRAux___at_Lean_IR_EmitC_toStringArgs___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_forM_loop___at_Lean_IR_EmitC_emitArgs___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldM_loop___at_Lean_IR_EmitC_emitSimpleExternalCall___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldM_loop___at_Lean_IR_EmitC_emitSimpleExternalCall___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitTag(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitInitFn___closed__11;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitDecl(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_throwUnknownVar(lean_object*);
static lean_object* l_Lean_IR_EmitC_emitDeclInit___lambda__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_isIf(lean_object*);
extern lean_object* l_Lean_instInhabitedName;
static lean_object* l_Lean_IR_EmitC_emitTailCall___closed__2;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitBlock(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_constName_x3f(lean_object*);
static lean_object* l_Lean_IR_EmitC_emitSSet___closed__3;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitBoxFn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_isTailCall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_throwInvalidExportName___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitFileFooter___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_forM_loop___at_Lean_IR_EmitC_emitDeclAux___spec__2___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitFnDeclAux___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitFnDeclAux___lambda__3___closed__1;
static lean_object* l_Lean_IR_EmitC_quoteString___lambda__1___closed__6;
static lean_object* l_Lean_IR_EmitC_throwInvalidExportName___rarg___closed__1;
LEAN_EXPORT lean_object* l_Nat_forM_loop___at_Lean_IR_EmitC_emitArgs___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_getModName___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitFnDeclAux___lambda__3___closed__2;
static lean_object* l_Lean_IR_EmitC_toCType___closed__12;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitInc___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_forM_loop___at_Lean_IR_EmitC_emitTailCall___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Nat_forM_loop___at_Lean_IR_EmitC_emitTailCall___spec__3___closed__1;
static lean_object* l_Lean_IR_EmitC_emitTailCall___closed__1;
static lean_object* l_Lean_IR_EmitC_emitInc___closed__1;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emit___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitLit___closed__1;
static lean_object* l_Lean_IR_EmitC_emitFileFooter___closed__2;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitDec(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitDec___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitLit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isClosedTermName(lean_object*, lean_object*);
extern lean_object* l_Lean_IR_instInhabitedAlt;
static lean_object* l_Lean_IR_EmitC_emitFileHeader___closed__12;
extern lean_object* l_UInt32_size;
LEAN_EXPORT lean_object* l_Nat_forM_loop___at_Lean_IR_EmitC_emitFnDeclAux___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_getJPParams___closed__1;
lean_object* lean_ir_find_env_decl(lean_object*, lean_object*);
lean_object* lean_name_mangle(lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitDec___closed__1;
extern lean_object* l_Lean_IR_instInhabitedArg;
lean_object* l_Lean_IR_mkVarJPMaps(lean_object*);
static lean_object* l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__5;
static lean_object* l_Lean_IR_EmitC_emitPartialApp___closed__2;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitFns(lean_object*, lean_object*);
static lean_object* l_Nat_forM_loop___at_Lean_IR_EmitC_emitDeclAux___spec__1___closed__3;
static lean_object* l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__24;
lean_object* l_Lean_Expr_getForallBody(lean_object*);
lean_object* l_Lean_IR_Decl_normalizeIds(lean_object*);
static lean_object* l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__15;
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitCName(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_forM_loop___at_Lean_IR_EmitC_emitDeclAux___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__18;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitReuse___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitFullApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_usesModuleFrom(lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__30;
static lean_object* l_Lean_IR_EmitC_declareVar___closed__1;
static lean_object* l_Lean_IR_EmitC_emitFnDeclAux___closed__3;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_declareVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitSSet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitFileFooter(lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_toCType___closed__10;
static lean_object* l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__22;
static lean_object* l_Lean_IR_EmitC_emitJmp___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitUnbox(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitJPs(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__6;
static lean_object* l_Nat_forM_loop___at_Lean_IR_EmitC_emitTailCall___spec__2___closed__1;
static lean_object* l_Nat_forM_loop___at_Lean_IR_EmitC_emitDeclAux___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Std_RBNode_revFold___at_Lean_IR_EmitC_emitFnDecls___spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitOffset(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_EmitC_emitInitFn___spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitSSet___closed__4;
LEAN_EXPORT lean_object* l_Nat_forM_loop___at_Lean_IR_EmitC_emitTailCall___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitInitFn___closed__2;
LEAN_EXPORT lean_object* l_List_forM___at_Lean_IR_EmitC_emitMainFn___spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitLn(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitSSet___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_EmitC_declareParams___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getInitFnNameForCore_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_FnBody_body(lean_object*);
static lean_object* l_Lean_IR_EmitC_emitReuse___closed__1;
LEAN_EXPORT lean_object* l_Nat_forM_loop___at_Lean_IR_EmitC_emitTailCall___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__12;
LEAN_EXPORT lean_object* l_Nat_forM_loop___at_Lean_IR_EmitC_emitPartialApp___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitLns___at_Lean_IR_EmitC_emitMainFn___spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_forM_loop___at_Lean_IR_EmitC_emitDeclAux___spec__2___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__13;
static lean_object* l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__23;
static lean_object* l_Lean_IR_EmitC_emitFileHeader___closed__24;
static lean_object* l_Lean_IR_EmitC_emitSSet___closed__1;
static lean_object* l_Lean_IR_EmitC_emitInitFn___closed__8;
lean_object* l_Lean_IR_Decl_params(lean_object*);
static lean_object* l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__25;
lean_object* lean_uint32_to_nat(uint32_t);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_throwInvalidExportName___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitInitFn___closed__4;
static lean_object* l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__29;
LEAN_EXPORT uint8_t l_Lean_IR_EmitC_paramEqArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitLn___at_Lean_IR_EmitC_emitMainFn___spec__2___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__20;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitCase(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitSSet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitLns___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__10;
static lean_object* l_Lean_IR_EmitC_emitFileHeader___closed__10;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_getModName(lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitSSet___closed__2;
static lean_object* l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__28;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_quoteString(lean_object*);
static lean_object* l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__14;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitDeclAux___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Nat_forM_loop___at_Lean_IR_EmitC_emitDeclAux___spec__1___closed__2;
LEAN_EXPORT lean_object* l_Nat_forM_loop___at_Lean_IR_EmitC_emitDeclAux___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_toCType(lean_object*);
static lean_object* l_Lean_IR_EmitC_emitInitFn___closed__9;
LEAN_EXPORT lean_object* l_List_forM___at_Lean_IR_EmitC_emitFnDecls___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitFileHeader___closed__20;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_EmitC_emitFnDeclAux___spec__3(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_getEnv(lean_object*, lean_object*);
static lean_object* l_List_forM___at_Lean_IR_EmitC_emitFnDecls___spec__5___closed__1;
LEAN_EXPORT lean_object* l_Nat_forM_loop___at_Lean_IR_EmitC_emitPartialApp___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_getJPParams(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitBoxFn___closed__5;
static lean_object* l_Lean_IR_EmitC_emitPartialApp___closed__1;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitSProj___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Nat_forM_loop___at_Lean_IR_EmitC_emitPartialApp___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitIsTaggedPtr___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitCtorSetArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitDeclInit___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_forM_loop___at_Lean_IR_EmitC_emitDeclAux___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_getDecl(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_EmitC_declareParams___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_EmitC_emitDeclInit___lambda__1___closed__1;
static lean_object* _init_l_Lean_IR_EmitC_leanMainFn___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_lean_main", 10);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_leanMainFn() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_IR_EmitC_leanMainFn___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_Context_jpMap___default___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Std_mkHashMapImp___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_EmitC_Context_jpMap___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_IR_EmitC_Context_jpMap___default___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_Context_mainFn___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_Context_mainParams___default___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_EmitC_Context_mainParams___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_IR_EmitC_Context_mainParams___default___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_getEnv(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_getEnv___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_EmitC_getEnv(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_getModName(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_getModName___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_EmitC_getModName(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_EmitC_getDecl___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unknown declaration '", 21);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_getDecl___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("'", 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_getDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_IR_EmitC_getEnv(x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_1);
x_7 = lean_ir_find_env_decl(x_6, x_1);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = 1;
x_9 = l_Lean_Name_toString(x_1, x_8);
x_10 = l_Lean_IR_EmitC_getDecl___closed__1;
x_11 = lean_string_append(x_10, x_9);
lean_dec(x_9);
x_12 = l_Lean_IR_EmitC_getDecl___closed__2;
x_13 = lean_string_append(x_11, x_12);
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_13);
return x_4;
}
else
{
lean_object* x_14; 
lean_dec(x_1);
x_14 = lean_ctor_get(x_7, 0);
lean_inc(x_14);
lean_dec(x_7);
lean_ctor_set(x_4, 0, x_14);
return x_4;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_4, 0);
x_16 = lean_ctor_get(x_4, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_4);
lean_inc(x_1);
x_17 = lean_ir_find_env_decl(x_15, x_1);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_18 = 1;
x_19 = l_Lean_Name_toString(x_1, x_18);
x_20 = l_Lean_IR_EmitC_getDecl___closed__1;
x_21 = lean_string_append(x_20, x_19);
lean_dec(x_19);
x_22 = l_Lean_IR_EmitC_getDecl___closed__2;
x_23 = lean_string_append(x_21, x_22);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_16);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_1);
x_25 = lean_ctor_get(x_17, 0);
lean_inc(x_25);
lean_dec(x_17);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_16);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_getDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_EmitC_getDecl(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emit___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_apply_1(x_1, x_2);
x_6 = lean_string_append(x_4, x_5);
lean_dec(x_5);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emit(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_IR_EmitC_emit___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emit___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_EmitC_emit___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitLn___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("\n", 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitLn___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_apply_1(x_1, x_2);
x_6 = lean_string_append(x_4, x_5);
lean_dec(x_5);
x_7 = l_Lean_IR_EmitC_emitLn___rarg___closed__1;
x_8 = lean_string_append(x_6, x_7);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitLn(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_IR_EmitC_emitLn___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitLn___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_EmitC_emitLn___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_forM___at_Lean_IR_EmitC_emitLns___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_1);
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
lean_dec(x_2);
lean_inc(x_1);
x_9 = lean_apply_1(x_1, x_7);
x_10 = lean_string_append(x_4, x_9);
lean_dec(x_9);
x_11 = l_Lean_IR_EmitC_emitLn___rarg___closed__1;
x_12 = lean_string_append(x_10, x_11);
x_2 = x_8;
x_4 = x_12;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at_Lean_IR_EmitC_emitLns___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_forM___at_Lean_IR_EmitC_emitLns___spec__1___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitLns___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_forM___at_Lean_IR_EmitC_emitLns___spec__1___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitLns(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_IR_EmitC_emitLns___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_forM___at_Lean_IR_EmitC_emitLns___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_forM___at_Lean_IR_EmitC_emitLns___spec__1___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitLns___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_EmitC_emitLns___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_IR_EmitC_argToCString___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("x_", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_argToCString___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("lean_box(0)", 11);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_argToCString(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec(x_1);
x_3 = l_Nat_repr(x_2);
x_4 = l_Lean_IR_EmitC_argToCString___closed__1;
x_5 = lean_string_append(x_4, x_3);
lean_dec(x_3);
return x_5;
}
else
{
lean_object* x_6; 
x_6 = l_Lean_IR_EmitC_argToCString___closed__2;
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = l_Lean_IR_EmitC_argToCString(x_1);
x_5 = lean_string_append(x_3, x_4);
lean_dec(x_4);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_EmitC_emitArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_IR_EmitC_toCType___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("double", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_toCType___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("uint8_t", 7);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_toCType___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("uint16_t", 8);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_toCType___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("uint32_t", 8);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_toCType___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("uint64_t", 8);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_toCType___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("size_t", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_toCType___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("lean_object*", 12);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_toCType___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Compiler.IR.EmitC", 22);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_toCType___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.IR.EmitC.toCType", 21);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_toCType___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("not implemented yet", 19);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_toCType___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_IR_EmitC_toCType___closed__8;
x_2 = l_Lean_IR_EmitC_toCType___closed__9;
x_3 = lean_unsigned_to_nat(65u);
x_4 = lean_unsigned_to_nat(25u);
x_5 = l_Lean_IR_EmitC_toCType___closed__10;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_IR_EmitC_toCType___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_IR_EmitC_toCType___closed__8;
x_2 = l_Lean_IR_EmitC_toCType___closed__9;
x_3 = lean_unsigned_to_nat(66u);
x_4 = lean_unsigned_to_nat(25u);
x_5 = l_Lean_IR_EmitC_toCType___closed__10;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_toCType(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; 
x_2 = l_Lean_IR_EmitC_toCType___closed__1;
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = l_Lean_IR_EmitC_toCType___closed__2;
return x_3;
}
case 2:
{
lean_object* x_4; 
x_4 = l_Lean_IR_EmitC_toCType___closed__3;
return x_4;
}
case 3:
{
lean_object* x_5; 
x_5 = l_Lean_IR_EmitC_toCType___closed__4;
return x_5;
}
case 4:
{
lean_object* x_6; 
x_6 = l_Lean_IR_EmitC_toCType___closed__5;
return x_6;
}
case 5:
{
lean_object* x_7; 
x_7 = l_Lean_IR_EmitC_toCType___closed__6;
return x_7;
}
case 9:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_IR_EmitC_toCType___closed__11;
x_9 = l_panic___at_Lean_TSyntax_getString___spec__1(x_8);
return x_9;
}
case 10:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lean_IR_EmitC_toCType___closed__12;
x_11 = l_panic___at_Lean_TSyntax_getString___spec__1(x_10);
return x_11;
}
default: 
{
lean_object* x_12; 
x_12 = l_Lean_IR_EmitC_toCType___closed__7;
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_toCType___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_IR_EmitC_toCType(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_EmitC_throwInvalidExportName___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("invalid export name '", 21);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_throwInvalidExportName___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = 1;
x_5 = l_Lean_Name_toString(x_1, x_4);
x_6 = l_Lean_IR_EmitC_throwInvalidExportName___rarg___closed__1;
x_7 = lean_string_append(x_6, x_5);
lean_dec(x_5);
x_8 = l_Lean_IR_EmitC_getDecl___closed__2;
x_9 = lean_string_append(x_7, x_8);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_throwInvalidExportName(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_IR_EmitC_throwInvalidExportName___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_throwInvalidExportName___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_EmitC_throwInvalidExportName___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_IR_EmitC_toCName___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_exportAttr;
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_toCName___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("main", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_toCName___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_IR_EmitC_toCName___closed__2;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_EmitC_toCName___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("l_", 2);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_toCName(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_IR_EmitC_getEnv(x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = l_Lean_instInhabitedName;
x_9 = l_Lean_IR_EmitC_toCName___closed__1;
lean_inc(x_1);
x_10 = l_Lean_ParametricAttribute_getParam___rarg(x_8, x_9, x_6, x_1);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Lean_IR_EmitC_toCName___closed__3;
x_12 = lean_name_eq(x_1, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = l_Lean_IR_EmitC_toCName___closed__4;
x_14 = lean_name_mangle(x_1, x_13);
lean_ctor_set(x_4, 0, x_14);
return x_4;
}
else
{
lean_object* x_15; 
lean_dec(x_1);
x_15 = l_Lean_IR_EmitC_leanMainFn;
lean_ctor_set(x_4, 0, x_15);
return x_4;
}
}
else
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_10, 0);
lean_inc(x_16);
lean_dec(x_10);
if (lean_obj_tag(x_16) == 1)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
lean_dec(x_1);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
lean_ctor_set(x_4, 0, x_18);
return x_4;
}
else
{
lean_object* x_19; 
lean_dec(x_17);
lean_dec(x_16);
lean_free_object(x_4);
x_19 = l_Lean_IR_EmitC_throwInvalidExportName___rarg(x_1, x_2, x_7);
return x_19;
}
}
else
{
lean_object* x_20; 
lean_dec(x_16);
lean_free_object(x_4);
x_20 = l_Lean_IR_EmitC_throwInvalidExportName___rarg(x_1, x_2, x_7);
return x_20;
}
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_4, 0);
x_22 = lean_ctor_get(x_4, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_4);
x_23 = l_Lean_instInhabitedName;
x_24 = l_Lean_IR_EmitC_toCName___closed__1;
lean_inc(x_1);
x_25 = l_Lean_ParametricAttribute_getParam___rarg(x_23, x_24, x_21, x_1);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; uint8_t x_27; 
x_26 = l_Lean_IR_EmitC_toCName___closed__3;
x_27 = lean_name_eq(x_1, x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = l_Lean_IR_EmitC_toCName___closed__4;
x_29 = lean_name_mangle(x_1, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_22);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_1);
x_31 = l_Lean_IR_EmitC_leanMainFn;
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_22);
return x_32;
}
}
else
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_25, 0);
lean_inc(x_33);
lean_dec(x_25);
if (lean_obj_tag(x_33) == 1)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_1);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_22);
return x_36;
}
else
{
lean_object* x_37; 
lean_dec(x_34);
lean_dec(x_33);
x_37 = l_Lean_IR_EmitC_throwInvalidExportName___rarg(x_1, x_2, x_22);
return x_37;
}
}
else
{
lean_object* x_38; 
lean_dec(x_33);
x_38 = l_Lean_IR_EmitC_throwInvalidExportName___rarg(x_1, x_2, x_22);
return x_38;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_toCName___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_EmitC_toCName(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitCName(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_EmitC_toCName(x_1, x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_string_append(x_7, x_6);
lean_dec(x_6);
x_9 = lean_box(0);
lean_ctor_set(x_4, 1, x_8);
lean_ctor_set(x_4, 0, x_9);
return x_4;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_4, 0);
x_11 = lean_ctor_get(x_4, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_4);
x_12 = lean_string_append(x_11, x_10);
lean_dec(x_10);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_4);
if (x_15 == 0)
{
return x_4;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_4, 0);
x_17 = lean_ctor_get(x_4, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_4);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitCName___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_EmitC_emitCName(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_IR_EmitC_toCInitName___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_init_", 6);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_toCInitName(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_IR_EmitC_getEnv(x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = l_Lean_instInhabitedName;
x_9 = l_Lean_IR_EmitC_toCName___closed__1;
lean_inc(x_1);
x_10 = l_Lean_ParametricAttribute_getParam___rarg(x_8, x_9, x_6, x_1);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = l_Lean_IR_EmitC_toCName___closed__4;
x_12 = lean_name_mangle(x_1, x_11);
x_13 = l_Lean_IR_EmitC_toCInitName___closed__1;
x_14 = lean_string_append(x_13, x_12);
lean_dec(x_12);
lean_ctor_set(x_4, 0, x_14);
return x_4;
}
else
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_10, 0);
lean_inc(x_15);
lean_dec(x_10);
if (lean_obj_tag(x_15) == 1)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_1);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_IR_EmitC_toCInitName___closed__1;
x_19 = lean_string_append(x_18, x_17);
lean_dec(x_17);
lean_ctor_set(x_4, 0, x_19);
return x_4;
}
else
{
lean_object* x_20; 
lean_dec(x_16);
lean_dec(x_15);
lean_free_object(x_4);
x_20 = l_Lean_IR_EmitC_throwInvalidExportName___rarg(x_1, x_2, x_7);
return x_20;
}
}
else
{
lean_object* x_21; 
lean_dec(x_15);
lean_free_object(x_4);
x_21 = l_Lean_IR_EmitC_throwInvalidExportName___rarg(x_1, x_2, x_7);
return x_21;
}
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_4, 0);
x_23 = lean_ctor_get(x_4, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_4);
x_24 = l_Lean_instInhabitedName;
x_25 = l_Lean_IR_EmitC_toCName___closed__1;
lean_inc(x_1);
x_26 = l_Lean_ParametricAttribute_getParam___rarg(x_24, x_25, x_22, x_1);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = l_Lean_IR_EmitC_toCName___closed__4;
x_28 = lean_name_mangle(x_1, x_27);
x_29 = l_Lean_IR_EmitC_toCInitName___closed__1;
x_30 = lean_string_append(x_29, x_28);
lean_dec(x_28);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_23);
return x_31;
}
else
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_26, 0);
lean_inc(x_32);
lean_dec(x_26);
if (lean_obj_tag(x_32) == 1)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_1);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = l_Lean_IR_EmitC_toCInitName___closed__1;
x_36 = lean_string_append(x_35, x_34);
lean_dec(x_34);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_23);
return x_37;
}
else
{
lean_object* x_38; 
lean_dec(x_33);
lean_dec(x_32);
x_38 = l_Lean_IR_EmitC_throwInvalidExportName___rarg(x_1, x_2, x_23);
return x_38;
}
}
else
{
lean_object* x_39; 
lean_dec(x_32);
x_39 = l_Lean_IR_EmitC_throwInvalidExportName___rarg(x_1, x_2, x_23);
return x_39;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_toCInitName___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_EmitC_toCInitName(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitCInitName(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_EmitC_toCInitName(x_1, x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_string_append(x_7, x_6);
lean_dec(x_6);
x_9 = lean_box(0);
lean_ctor_set(x_4, 1, x_8);
lean_ctor_set(x_4, 0, x_9);
return x_4;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_4, 0);
x_11 = lean_ctor_get(x_4, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_4);
x_12 = lean_string_append(x_11, x_10);
lean_dec(x_10);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_4);
if (x_15 == 0)
{
return x_4;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_4, 0);
x_17 = lean_ctor_get(x_4, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_4);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitCInitName___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_EmitC_emitCInitName(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Nat_forM_loop___at_Lean_IR_EmitC_emitFnDeclAux___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = l_Lean_IR_instInhabitedParam;
x_7 = lean_array_get(x_6, x_1, x_2);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_Lean_IR_EmitC_toCType(x_8);
lean_dec(x_8);
x_10 = lean_string_append(x_5, x_9);
lean_dec(x_9);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
static lean_object* _init_l_Nat_forM_loop___at_Lean_IR_EmitC_emitFnDeclAux___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(", ", 2);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Nat_forM_loop___at_Lean_IR_EmitC_emitFnDeclAux___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_3, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_3, x_8);
lean_dec(x_3);
x_10 = lean_nat_sub(x_2, x_9);
x_11 = lean_nat_sub(x_10, x_8);
lean_dec(x_10);
x_12 = lean_nat_dec_lt(x_6, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_box(0);
x_14 = l_Nat_forM_loop___at_Lean_IR_EmitC_emitFnDeclAux___spec__1___lambda__1(x_1, x_11, x_13, x_4, x_5);
lean_dec(x_11);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_3 = x_9;
x_5 = x_15;
goto _start;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = l_Nat_forM_loop___at_Lean_IR_EmitC_emitFnDeclAux___spec__1___closed__1;
x_18 = lean_string_append(x_5, x_17);
x_19 = lean_box(0);
x_20 = l_Nat_forM_loop___at_Lean_IR_EmitC_emitFnDeclAux___spec__1___lambda__1(x_1, x_11, x_19, x_4, x_18);
lean_dec(x_11);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_3 = x_9;
x_5 = x_21;
goto _start;
}
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_3);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_5);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Nat_forM_loop___at_Lean_IR_EmitC_emitFnDeclAux___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_3, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_3, x_8);
lean_dec(x_3);
x_10 = lean_nat_sub(x_2, x_9);
x_11 = lean_nat_sub(x_10, x_8);
lean_dec(x_10);
x_12 = lean_nat_dec_lt(x_6, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_box(0);
x_14 = l_Nat_forM_loop___at_Lean_IR_EmitC_emitFnDeclAux___spec__1___lambda__1(x_1, x_11, x_13, x_4, x_5);
lean_dec(x_11);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_3 = x_9;
x_5 = x_15;
goto _start;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = l_Nat_forM_loop___at_Lean_IR_EmitC_emitFnDeclAux___spec__1___closed__1;
x_18 = lean_string_append(x_5, x_17);
x_19 = lean_box(0);
x_20 = l_Nat_forM_loop___at_Lean_IR_EmitC_emitFnDeclAux___spec__1___lambda__1(x_1, x_11, x_19, x_4, x_18);
lean_dec(x_11);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_3 = x_9;
x_5 = x_21;
goto _start;
}
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_3);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_5);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_EmitC_emitFnDeclAux___spec__3(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; size_t x_9; size_t x_10; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
x_8 = l_Lean_IR_IRType_isIrrelevant(x_7);
lean_dec(x_7);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
if (x_8 == 0)
{
lean_object* x_11; 
x_11 = lean_array_push(x_4, x_6);
x_2 = x_10;
x_4 = x_11;
goto _start;
}
else
{
lean_dec(x_6);
x_2 = x_10;
goto _start;
}
}
else
{
return x_4;
}
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitFnDeclAux___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(";", 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitFnDeclAux___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = l_Lean_IR_EmitC_emitFnDeclAux___lambda__1___closed__1;
x_5 = lean_string_append(x_3, x_4);
x_6 = l_Lean_IR_EmitC_emitLn___rarg___closed__1;
x_7 = lean_string_append(x_5, x_6);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitFnDeclAux___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(")", 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitFnDeclAux___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = l_Lean_IR_EmitC_emitFnDeclAux___lambda__2___closed__1;
x_6 = lean_string_append(x_4, x_5);
x_7 = lean_box(0);
x_8 = lean_apply_3(x_1, x_7, x_3, x_6);
return x_8;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitFnDeclAux___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" ", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitFnDeclAux___lambda__3___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_IR_EmitC_emitFnDeclAux___lambda__1___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitFnDeclAux___lambda__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("(", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitFnDeclAux___lambda__3___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("lean_object**", 13);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitFnDeclAux___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_8 = l_Lean_IR_Decl_resultType(x_1);
x_9 = l_Lean_IR_EmitC_toCType(x_8);
lean_dec(x_8);
x_10 = l_Lean_IR_EmitC_emitFnDeclAux___lambda__3___closed__1;
x_11 = lean_string_append(x_9, x_10);
x_12 = lean_string_append(x_11, x_2);
lean_dec(x_2);
x_13 = lean_string_append(x_7, x_12);
lean_dec(x_12);
x_14 = l_Lean_IR_EmitC_emitFnDeclAux___lambda__3___closed__2;
x_15 = l_Array_isEmpty___rarg(x_3);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_16 = l_Lean_IR_EmitC_emitFnDeclAux___lambda__3___closed__3;
x_17 = lean_string_append(x_13, x_16);
x_18 = l_Lean_IR_Decl_name(x_1);
lean_dec(x_1);
lean_inc(x_18);
x_19 = l_Lean_isExternC(x_4, x_18);
if (x_19 == 0)
{
x_20 = x_3;
goto block_37;
}
else
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_38 = lean_array_get_size(x_3);
x_39 = lean_unsigned_to_nat(0u);
x_40 = lean_nat_dec_lt(x_39, x_38);
if (x_40 == 0)
{
lean_object* x_41; 
lean_dec(x_38);
lean_dec(x_3);
x_41 = l_Lean_IR_EmitC_Context_mainParams___default___closed__1;
x_20 = x_41;
goto block_37;
}
else
{
uint8_t x_42; 
x_42 = lean_nat_dec_le(x_38, x_38);
if (x_42 == 0)
{
lean_object* x_43; 
lean_dec(x_38);
lean_dec(x_3);
x_43 = l_Lean_IR_EmitC_Context_mainParams___default___closed__1;
x_20 = x_43;
goto block_37;
}
else
{
size_t x_44; size_t x_45; lean_object* x_46; lean_object* x_47; 
x_44 = 0;
x_45 = lean_usize_of_nat(x_38);
lean_dec(x_38);
x_46 = l_Lean_IR_EmitC_Context_mainParams___default___closed__1;
x_47 = l_Array_foldlMUnsafe_fold___at_Lean_IR_EmitC_emitFnDeclAux___spec__3(x_3, x_44, x_45, x_46);
lean_dec(x_3);
x_20 = x_47;
goto block_37;
}
}
}
block_37:
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_array_get_size(x_20);
x_22 = l_Lean_closureMaxArgs;
x_23 = lean_nat_dec_lt(x_22, x_21);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_18);
lean_inc(x_21);
x_24 = l_Nat_forM_loop___at_Lean_IR_EmitC_emitFnDeclAux___spec__1(x_20, x_21, x_21, x_6, x_17);
lean_dec(x_21);
lean_dec(x_20);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_Lean_IR_EmitC_emitFnDeclAux___lambda__2(x_14, x_25, x_6, x_26);
lean_dec(x_25);
return x_27;
}
else
{
uint8_t x_28; 
x_28 = l_Lean_IR_ExplicitBoxing_isBoxedName(x_18);
lean_dec(x_18);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_inc(x_21);
x_29 = l_Nat_forM_loop___at_Lean_IR_EmitC_emitFnDeclAux___spec__2(x_20, x_21, x_21, x_6, x_17);
lean_dec(x_21);
lean_dec(x_20);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l_Lean_IR_EmitC_emitFnDeclAux___lambda__2(x_14, x_30, x_6, x_31);
lean_dec(x_30);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_21);
lean_dec(x_20);
x_33 = l_Lean_IR_EmitC_emitFnDeclAux___lambda__3___closed__4;
x_34 = lean_string_append(x_17, x_33);
x_35 = lean_box(0);
x_36 = l_Lean_IR_EmitC_emitFnDeclAux___lambda__2(x_14, x_35, x_6, x_34);
return x_36;
}
}
}
}
else
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_48 = lean_box(0);
x_49 = lean_apply_3(x_14, x_48, x_6, x_13);
return x_49;
}
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitFnDeclAux___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("LEAN_EXPORT ", 12);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitFnDeclAux___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("extern ", 7);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitFnDeclAux___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("static ", 7);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitFnDeclAux(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = l_Lean_IR_Decl_params(x_1);
x_7 = l_Lean_IR_EmitC_getEnv(x_4, x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Array_isEmpty___rarg(x_6);
if (x_10 == 0)
{
if (x_3 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = l_Lean_IR_EmitC_emitFnDeclAux___closed__1;
x_12 = lean_string_append(x_9, x_11);
x_13 = lean_box(0);
x_14 = l_Lean_IR_EmitC_emitFnDeclAux___lambda__3(x_1, x_2, x_6, x_8, x_13, x_4, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_box(0);
x_16 = l_Lean_IR_EmitC_emitFnDeclAux___lambda__3(x_1, x_2, x_6, x_8, x_15, x_4, x_9);
return x_16;
}
}
else
{
lean_object* x_17; uint8_t x_18; 
x_17 = l_Lean_IR_Decl_name(x_1);
x_18 = l_Lean_isClosedTermName(x_8, x_17);
lean_dec(x_17);
if (x_18 == 0)
{
if (x_3 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = l_Lean_IR_EmitC_emitFnDeclAux___closed__1;
x_20 = lean_string_append(x_9, x_19);
x_21 = lean_box(0);
x_22 = l_Lean_IR_EmitC_emitFnDeclAux___lambda__3(x_1, x_2, x_6, x_8, x_21, x_4, x_20);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = l_Lean_IR_EmitC_emitFnDeclAux___closed__2;
x_24 = lean_string_append(x_9, x_23);
x_25 = lean_box(0);
x_26 = l_Lean_IR_EmitC_emitFnDeclAux___lambda__3(x_1, x_2, x_6, x_8, x_25, x_4, x_24);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = l_Lean_IR_EmitC_emitFnDeclAux___closed__3;
x_28 = lean_string_append(x_9, x_27);
x_29 = lean_box(0);
x_30 = l_Lean_IR_EmitC_emitFnDeclAux___lambda__3(x_1, x_2, x_6, x_8, x_29, x_4, x_28);
return x_30;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_forM_loop___at_Lean_IR_EmitC_emitFnDeclAux___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Nat_forM_loop___at_Lean_IR_EmitC_emitFnDeclAux___spec__1___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Nat_forM_loop___at_Lean_IR_EmitC_emitFnDeclAux___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Nat_forM_loop___at_Lean_IR_EmitC_emitFnDeclAux___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Nat_forM_loop___at_Lean_IR_EmitC_emitFnDeclAux___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Nat_forM_loop___at_Lean_IR_EmitC_emitFnDeclAux___spec__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_EmitC_emitFnDeclAux___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lean_IR_EmitC_emitFnDeclAux___spec__3(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitFnDeclAux___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_EmitC_emitFnDeclAux___lambda__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitFnDeclAux___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_EmitC_emitFnDeclAux___lambda__2(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitFnDeclAux___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_IR_EmitC_emitFnDeclAux___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitFnDeclAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_3);
lean_dec(x_3);
x_7 = l_Lean_IR_EmitC_emitFnDeclAux(x_1, x_2, x_6, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitFnDecl(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_IR_Decl_name(x_1);
x_6 = l_Lean_IR_EmitC_toCName(x_5, x_3, x_4);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_IR_EmitC_emitFnDeclAux(x_1, x_7, x_2, x_3, x_8);
return x_9;
}
else
{
uint8_t x_10; 
lean_dec(x_3);
lean_dec(x_1);
x_10 = !lean_is_exclusive(x_6);
if (x_10 == 0)
{
return x_6;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_6, 0);
x_12 = lean_ctor_get(x_6, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_6);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitFnDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Lean_IR_EmitC_emitFnDecl(x_1, x_5, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitExternDeclAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_5 = l_Lean_IR_EmitC_getEnv(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l_Lean_IR_Decl_name(x_1);
x_9 = l_Lean_isExternC(x_6, x_8);
x_10 = l_Lean_IR_EmitC_emitFnDeclAux(x_1, x_2, x_9, x_3, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at_Lean_IR_EmitC_emitFnDecls___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = l_Lean_IR_Decl_name(x_3);
x_6 = lean_box(0);
x_7 = l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_1, x_5, x_6);
x_1 = x_7;
x_2 = x_4;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at_Lean_IR_EmitC_emitFnDecls___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = l_Lean_IR_Decl_name(x_4);
x_7 = lean_box(0);
x_8 = l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_2, x_6, x_7);
lean_inc(x_1);
x_9 = l_Lean_IR_collectUsedDecls(x_1, x_4, x_8);
x_2 = x_9;
x_3 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_revFold___at_Lean_IR_EmitC_emitFnDecls___spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_2, 3);
x_6 = l_Std_RBNode_revFold___at_Lean_IR_EmitC_emitFnDecls___spec__4(x_1, x_5);
lean_inc(x_4);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_6);
x_1 = x_7;
x_2 = x_3;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_RBTree_toList___at_Lean_IR_EmitC_emitFnDecls___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = l_Std_RBNode_revFold___at_Lean_IR_EmitC_emitFnDecls___spec__4(x_2, x_1);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_List_forM___at_Lean_IR_EmitC_emitFnDecls___spec__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("c", 1);
return x_1;
}
}
static lean_object* _init_l_List_forM___at_Lean_IR_EmitC_emitFnDecls___spec__5___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_List_forM___at_Lean_IR_EmitC_emitFnDecls___spec__5___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_forM___at_Lean_IR_EmitC_emitFnDecls___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_4);
lean_dec(x_1);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
lean_dec(x_3);
lean_inc(x_8);
x_10 = l_Lean_IR_EmitC_getDecl(x_8, x_4, x_5);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_IR_Decl_name(x_11);
x_14 = l_List_forM___at_Lean_IR_EmitC_emitFnDecls___spec__5___closed__2;
lean_inc(x_1);
x_15 = l_Lean_getExternNameFor(x_1, x_14, x_13);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = l_Lean_NameSet_contains(x_2, x_8);
lean_dec(x_8);
if (x_16 == 0)
{
uint8_t x_17; lean_object* x_18; 
x_17 = 1;
lean_inc(x_4);
x_18 = l_Lean_IR_EmitC_emitFnDecl(x_11, x_17, x_4, x_12);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_3 = x_9;
x_5 = x_19;
goto _start;
}
else
{
uint8_t x_21; 
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_18);
if (x_21 == 0)
{
return x_18;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_18, 0);
x_23 = lean_ctor_get(x_18, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_18);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
else
{
uint8_t x_25; lean_object* x_26; 
x_25 = 0;
lean_inc(x_4);
x_26 = l_Lean_IR_EmitC_emitFnDecl(x_11, x_25, x_4, x_12);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_3 = x_9;
x_5 = x_27;
goto _start;
}
else
{
uint8_t x_29; 
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_26);
if (x_29 == 0)
{
return x_26;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_26, 0);
x_31 = lean_ctor_get(x_26, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_26);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
else
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_8);
x_33 = lean_ctor_get(x_15, 0);
lean_inc(x_33);
lean_dec(x_15);
lean_inc(x_4);
x_34 = l_Lean_IR_EmitC_emitExternDeclAux(x_11, x_33, x_4, x_12);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
x_3 = x_9;
x_5 = x_35;
goto _start;
}
else
{
uint8_t x_37; 
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_1);
x_37 = !lean_is_exclusive(x_34);
if (x_37 == 0)
{
return x_34;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_34, 0);
x_39 = lean_ctor_get(x_34, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_34);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
else
{
uint8_t x_41; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_1);
x_41 = !lean_is_exclusive(x_10);
if (x_41 == 0)
{
return x_10;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_10, 0);
x_43 = lean_ctor_get(x_10, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_10);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitFnDecls(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_3 = l_Lean_IR_EmitC_getEnv(x_1, x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = l_Lean_IR_getDecls(x_4);
x_7 = l_Lean_NameSet_empty;
x_8 = l_List_foldl___at_Lean_IR_EmitC_emitFnDecls___spec__1(x_7, x_6);
lean_inc(x_4);
x_9 = l_List_foldl___at_Lean_IR_EmitC_emitFnDecls___spec__2(x_4, x_7, x_6);
x_10 = l_Std_RBTree_toList___at_Lean_IR_EmitC_emitFnDecls___spec__3(x_9);
x_11 = l_List_forM___at_Lean_IR_EmitC_emitFnDecls___spec__5(x_4, x_8, x_10, x_1, x_5);
lean_dec(x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at_Lean_IR_EmitC_emitFnDecls___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_foldl___at_Lean_IR_EmitC_emitFnDecls___spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_revFold___at_Lean_IR_EmitC_emitFnDecls___spec__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_RBNode_revFold___at_Lean_IR_EmitC_emitFnDecls___spec__4(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_forM___at_Lean_IR_EmitC_emitFnDecls___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_List_forM___at_Lean_IR_EmitC_emitFnDecls___spec__5(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitLn___at_Lean_IR_EmitC_emitMainFn___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_string_append(x_3, x_1);
x_5 = l_Lean_IR_EmitC_emitLn___rarg___closed__1;
x_6 = lean_string_append(x_4, x_5);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_List_forM___at_Lean_IR_EmitC_emitMainFn___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = l_Lean_IR_EmitC_emitLn___at_Lean_IR_EmitC_emitMainFn___spec__2(x_6, x_2, x_3);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_1 = x_7;
x_3 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitLns___at_Lean_IR_EmitC_emitMainFn___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_forM___at_Lean_IR_EmitC_emitMainFn___spec__3(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_IR_EmitC_emitMainFn___spec__4(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_instInhabitedConstantInfo;
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("}", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("UInt32", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__2;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__3;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("  return 1;", 11);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("  lean_dec_ref(res);", 20);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("  lean_io_result_show_error(res);", 33);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("} else {", 8);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("  return ret;", 13);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("  int ret = ", 12);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("0;", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__10;
x_2 = l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__11;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("if (lean_io_result_is_ok(res)) {", 32);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("lean_finalize_task_manager();", 29);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("lean_unbox_uint32(lean_io_result_get_value(res));", 49);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__10;
x_2 = l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__15;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Init.Data.Option.BasicAux", 25);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__18() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Option.get!", 11);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("value is none", 13);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__17;
x_2 = l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__18;
x_3 = lean_unsigned_to_nat(16u);
x_4 = lean_unsigned_to_nat(14u);
x_5 = l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__19;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitMainFn___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_7 = l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__1;
x_8 = lean_string_append(x_6, x_7);
x_9 = l_Lean_IR_EmitC_emitLn___rarg___closed__1;
x_10 = lean_string_append(x_8, x_9);
x_11 = lean_environment_find(x_1, x_2);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_7);
lean_ctor_set(x_12, 1, x_3);
x_13 = l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__5;
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
x_15 = l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__6;
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
x_17 = l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__7;
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__8;
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
x_21 = l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__9;
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_15);
lean_ctor_set(x_23, 1, x_22);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_68; lean_object* x_69; 
x_68 = l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__20;
x_69 = l_panic___at_Lean_IR_EmitC_emitMainFn___spec__4(x_68);
x_24 = x_69;
goto block_67;
}
else
{
lean_object* x_70; 
x_70 = lean_ctor_get(x_11, 0);
lean_inc(x_70);
lean_dec(x_11);
x_24 = x_70;
goto block_67;
}
block_67:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_25 = l_Lean_ConstantInfo_type(x_24);
lean_dec(x_24);
x_26 = l_Lean_Expr_getForallBody(x_25);
lean_dec(x_25);
x_27 = l_Lean_Expr_appArg_x21(x_26);
lean_dec(x_26);
x_28 = l_Lean_Expr_constName_x3f(x_27);
lean_dec(x_27);
x_29 = l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__4;
x_30 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_800____at_Lean_IR_IRType_beq___spec__1(x_28, x_29);
lean_dec(x_28);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_31 = l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__12;
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_23);
x_33 = l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__13;
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
x_35 = l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__14;
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
x_37 = l_List_forM___at_Lean_IR_EmitC_emitMainFn___spec__3(x_36, x_5, x_10);
lean_dec(x_36);
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_39 = lean_ctor_get(x_37, 1);
x_40 = lean_ctor_get(x_37, 0);
lean_dec(x_40);
x_41 = lean_string_append(x_39, x_7);
x_42 = lean_string_append(x_41, x_9);
x_43 = lean_box(0);
lean_ctor_set(x_37, 1, x_42);
lean_ctor_set(x_37, 0, x_43);
return x_37;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_44 = lean_ctor_get(x_37, 1);
lean_inc(x_44);
lean_dec(x_37);
x_45 = lean_string_append(x_44, x_7);
x_46 = lean_string_append(x_45, x_9);
x_47 = lean_box(0);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_49 = l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__16;
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_23);
x_51 = l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__13;
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_50);
x_53 = l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__14;
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_52);
x_55 = l_List_forM___at_Lean_IR_EmitC_emitMainFn___spec__3(x_54, x_5, x_10);
lean_dec(x_54);
x_56 = !lean_is_exclusive(x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_57 = lean_ctor_get(x_55, 1);
x_58 = lean_ctor_get(x_55, 0);
lean_dec(x_58);
x_59 = lean_string_append(x_57, x_7);
x_60 = lean_string_append(x_59, x_9);
x_61 = lean_box(0);
lean_ctor_set(x_55, 1, x_60);
lean_ctor_set(x_55, 0, x_61);
return x_55;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_62 = lean_ctor_get(x_55, 1);
lean_inc(x_62);
lean_dec(x_55);
x_63 = lean_string_append(x_62, x_7);
x_64 = lean_string_append(x_63, x_9);
x_65 = lean_box(0);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_64);
return x_66;
}
}
}
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("lean_set_panic_messages(false);", 31);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("res = ", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("(1 /* builtin */, lean_io_mk_world());", 38);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("lean_set_panic_messages(true);", 30);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("lean_init_task_manager();", 25);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__5;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("lean_dec_ref(res);", 18);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__7;
x_2 = l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__6;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__13;
x_2 = l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__8;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("lean_io_mark_end_initialization();", 34);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__10;
x_2 = l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__9;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__2;
x_2 = l_Lean_IR_EmitC_leanMainFn;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("(lean_io_mk_world());", 21);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__12;
x_2 = l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__13;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" in = n;", 8);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__16;
x_2 = l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__15;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__18() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" n = lean_alloc_ctor(1,2,0); lean_ctor_set(n, 0, lean_mk_string(argv[i])); lean_ctor_set(n, 1, in);", 99);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__18;
x_2 = l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__17;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__20() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" i--;", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__20;
x_2 = l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__19;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__22() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" lean_object* n;", 16);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__22;
x_2 = l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__21;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__24() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("while (i > 1) {", 15);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__24;
x_2 = l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__23;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__26() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("int i = argc;", 13);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__26;
x_2 = l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__25;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__28() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("in = lean_box(0);", 17);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__29() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__28;
x_2 = l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__27;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__30() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("(in, lean_io_mk_world());", 25);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__31() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__12;
x_2 = l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__30;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitMainFn___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
lean_dec(x_4);
x_7 = l_Lean_IR_EmitC_getModName(x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__1;
x_11 = lean_string_append(x_9, x_10);
x_12 = l_Lean_IR_EmitC_emitLn___rarg___closed__1;
x_13 = lean_string_append(x_11, x_12);
x_14 = lean_mk_module_initialization_function_name(x_8);
x_15 = l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__2;
x_16 = lean_string_append(x_15, x_14);
lean_dec(x_14);
x_17 = l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__3;
x_18 = lean_string_append(x_16, x_17);
x_19 = lean_string_append(x_13, x_18);
lean_dec(x_18);
x_20 = lean_string_append(x_19, x_12);
x_21 = l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__4;
x_22 = lean_string_append(x_20, x_21);
x_23 = lean_string_append(x_22, x_12);
x_24 = lean_box(0);
x_25 = l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__11;
x_26 = l_List_forM___at_Lean_IR_EmitC_emitMainFn___spec__3(x_25, x_5, x_23);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_array_get_size(x_3);
lean_dec(x_3);
x_29 = lean_unsigned_to_nat(2u);
x_30 = lean_nat_dec_eq(x_28, x_29);
lean_dec(x_28);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_31 = l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__14;
x_32 = lean_string_append(x_27, x_31);
x_33 = lean_string_append(x_32, x_12);
x_34 = lean_box(0);
x_35 = l_Lean_IR_EmitC_emitMainFn___lambda__1(x_1, x_2, x_24, x_34, x_5, x_33);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_36 = l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__29;
x_37 = l_List_forM___at_Lean_IR_EmitC_emitMainFn___spec__3(x_36, x_5, x_27);
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
lean_dec(x_37);
x_39 = l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__31;
x_40 = lean_string_append(x_38, x_39);
x_41 = lean_string_append(x_40, x_12);
x_42 = lean_box(0);
x_43 = l_Lean_IR_EmitC_emitMainFn___lambda__1(x_1, x_2, x_24, x_42, x_5, x_41);
return x_43;
}
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitMainFn___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("\n  #if defined(WIN32) || defined(_WIN32)\n  #include <windows.h>\n  #endif\n\n  int main(int argc, char ** argv) {\n  #if defined(WIN32) || defined(_WIN32)\n  SetErrorMode(SEM_FAILCRITICALERRORS);\n  #endif\n  lean_object* in; lean_object* res;", 236);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitMainFn___lambda__3___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("lean_initialize_runtime_module();", 33);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitMainFn___lambda__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("lean_initialize();", 18);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitMainFn___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
x_8 = l_Lean_IR_EmitC_emitMainFn___lambda__3___closed__1;
x_9 = lean_string_append(x_7, x_8);
x_10 = l_Lean_IR_EmitC_emitLn___rarg___closed__1;
x_11 = lean_string_append(x_9, x_10);
if (x_4 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = l_Lean_IR_EmitC_emitMainFn___lambda__3___closed__2;
x_13 = lean_string_append(x_11, x_12);
x_14 = lean_string_append(x_13, x_10);
x_15 = lean_box(0);
x_16 = l_Lean_IR_EmitC_emitMainFn___lambda__2(x_1, x_2, x_3, x_15, x_6, x_14);
lean_dec(x_6);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = l_Lean_IR_EmitC_emitMainFn___lambda__3___closed__3;
x_18 = lean_string_append(x_11, x_17);
x_19 = lean_string_append(x_18, x_10);
x_20 = lean_box(0);
x_21 = l_Lean_IR_EmitC_emitMainFn___lambda__2(x_1, x_2, x_3, x_20, x_6, x_19);
lean_dec(x_6);
return x_21;
}
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitMainFn___lambda__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitMainFn___lambda__4___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_IR_EmitC_emitMainFn___lambda__4___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitMainFn___lambda__4___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("void lean_initialize_runtime_module();", 38);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitMainFn___lambda__4___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("void lean_initialize();", 23);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitMainFn___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
lean_dec(x_3);
x_6 = l_Lean_IR_EmitC_getEnv(x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_IR_EmitC_emitMainFn___lambda__4___closed__2;
lean_inc(x_7);
x_10 = l_Lean_IR_usesModuleFrom(x_7, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = l_Lean_IR_EmitC_emitMainFn___lambda__4___closed__3;
x_12 = lean_string_append(x_8, x_11);
x_13 = l_Lean_IR_EmitC_emitLn___rarg___closed__1;
x_14 = lean_string_append(x_12, x_13);
x_15 = lean_box(0);
x_16 = l_Lean_IR_EmitC_emitMainFn___lambda__3(x_7, x_1, x_2, x_10, x_15, x_4, x_14);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_17 = l_Lean_IR_EmitC_emitMainFn___lambda__4___closed__4;
x_18 = lean_string_append(x_8, x_17);
x_19 = l_Lean_IR_EmitC_emitLn___rarg___closed__1;
x_20 = lean_string_append(x_18, x_19);
x_21 = lean_box(0);
x_22 = l_Lean_IR_EmitC_emitMainFn___lambda__3(x_7, x_1, x_2, x_10, x_21, x_4, x_20);
return x_22;
}
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("invalid main function, incorrect arity when generating code", 59);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("function declaration expected", 29);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitMainFn(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_IR_EmitC_toCName___closed__3;
x_4 = l_Lean_IR_EmitC_getDecl(x_3, x_1, x_2);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_ctor_get(x_4, 0);
lean_dec(x_8);
x_9 = lean_ctor_get(x_5, 1);
lean_inc(x_9);
lean_dec(x_5);
x_10 = lean_array_get_size(x_9);
x_11 = lean_unsigned_to_nat(2u);
x_12 = lean_nat_dec_eq(x_10, x_11);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_dec_eq(x_10, x_13);
lean_dec(x_10);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_9);
lean_dec(x_1);
x_15 = l_Lean_IR_EmitC_emitMainFn___closed__1;
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_15);
return x_4;
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_free_object(x_4);
x_16 = lean_box(0);
x_17 = l_Lean_IR_EmitC_emitMainFn___lambda__4(x_3, x_9, x_16, x_1, x_7);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_10);
lean_free_object(x_4);
x_18 = lean_box(0);
x_19 = l_Lean_IR_EmitC_emitMainFn___lambda__4(x_3, x_9, x_18, x_1, x_7);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_20 = lean_ctor_get(x_4, 1);
lean_inc(x_20);
lean_dec(x_4);
x_21 = lean_ctor_get(x_5, 1);
lean_inc(x_21);
lean_dec(x_5);
x_22 = lean_array_get_size(x_21);
x_23 = lean_unsigned_to_nat(2u);
x_24 = lean_nat_dec_eq(x_22, x_23);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_dec_eq(x_22, x_25);
lean_dec(x_22);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_21);
lean_dec(x_1);
x_27 = l_Lean_IR_EmitC_emitMainFn___closed__1;
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_20);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_box(0);
x_30 = l_Lean_IR_EmitC_emitMainFn___lambda__4(x_3, x_21, x_29, x_1, x_20);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_22);
x_31 = lean_box(0);
x_32 = l_Lean_IR_EmitC_emitMainFn___lambda__4(x_3, x_21, x_31, x_1, x_20);
return x_32;
}
}
}
else
{
uint8_t x_33; 
lean_dec(x_5);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_4);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_4, 0);
lean_dec(x_34);
x_35 = l_Lean_IR_EmitC_emitMainFn___closed__2;
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_35);
return x_4;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_4, 1);
lean_inc(x_36);
lean_dec(x_4);
x_37 = l_Lean_IR_EmitC_emitMainFn___closed__2;
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
}
else
{
uint8_t x_39; 
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_4);
if (x_39 == 0)
{
return x_4;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_4, 0);
x_41 = lean_ctor_get(x_4, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_4);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitLn___at_Lean_IR_EmitC_emitMainFn___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_EmitC_emitLn___at_Lean_IR_EmitC_emitMainFn___spec__2(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_forM___at_Lean_IR_EmitC_emitMainFn___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_forM___at_Lean_IR_EmitC_emitMainFn___spec__3(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitLns___at_Lean_IR_EmitC_emitMainFn___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_EmitC_emitLns___at_Lean_IR_EmitC_emitMainFn___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitMainFn___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_IR_EmitC_emitMainFn___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitMainFn___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_IR_EmitC_emitMainFn___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitMainFn___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_4);
lean_dec(x_4);
x_9 = l_Lean_IR_EmitC_emitMainFn___lambda__3(x_1, x_2, x_3, x_8, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT uint8_t l_List_foldr___at_Lean_IR_EmitC_hasMainFn___spec__1(uint8_t x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = l_List_foldr___at_Lean_IR_EmitC_hasMainFn___spec__1(x_1, x_4);
x_6 = l_Lean_IR_Decl_name(x_3);
x_7 = l_Lean_IR_EmitC_toCName___closed__3;
x_8 = lean_name_eq(x_6, x_7);
lean_dec(x_6);
if (x_8 == 0)
{
return x_5;
}
else
{
uint8_t x_9; 
x_9 = 1;
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_hasMainFn(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lean_IR_EmitC_getEnv(x_1, x_2);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = l_Lean_IR_getDecls(x_5);
lean_dec(x_5);
x_7 = 0;
x_8 = l_List_foldr___at_Lean_IR_EmitC_hasMainFn___spec__1(x_7, x_6);
lean_dec(x_6);
x_9 = lean_box(x_8);
lean_ctor_set(x_3, 0, x_9);
return x_3;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_3);
x_12 = l_Lean_IR_getDecls(x_10);
lean_dec(x_10);
x_13 = 0;
x_14 = l_List_foldr___at_Lean_IR_EmitC_hasMainFn___spec__1(x_13, x_12);
lean_dec(x_12);
x_15 = lean_box(x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_11);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_List_foldr___at_Lean_IR_EmitC_hasMainFn___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_List_foldr___at_Lean_IR_EmitC_hasMainFn___spec__1(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_hasMainFn___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_EmitC_hasMainFn(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitMainFnIfNeeded(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_IR_EmitC_hasMainFn(x_1, x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_unbox(x_4);
lean_dec(x_4);
if (x_5 == 0)
{
uint8_t x_6; 
lean_dec(x_1);
x_6 = !lean_is_exclusive(x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_3, 0);
lean_dec(x_7);
x_8 = lean_box(0);
lean_ctor_set(x_3, 0, x_8);
return x_3;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
lean_dec(x_3);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
lean_dec(x_3);
x_13 = l_Lean_IR_EmitC_emitMainFn(x_1, x_12);
return x_13;
}
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lean_IR_EmitC_emitFileHeader___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("", 0);
return x_1;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lean_IR_EmitC_emitFileHeader___spec__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" (runtime)", 10);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_EmitC_emitFileHeader___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_2, x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; uint8_t x_12; 
lean_dec(x_4);
x_8 = lean_array_uget(x_1, x_2);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = 1;
x_11 = l_Lean_Name_toString(x_9, x_10);
x_12 = lean_ctor_get_uint8(x_8, sizeof(void*)*1);
lean_dec(x_8);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; 
x_13 = l_Array_foldlMUnsafe_fold___at_Lean_IR_EmitC_emitFileHeader___spec__1___closed__1;
x_14 = lean_string_append(x_11, x_13);
x_15 = l_Lean_IR_EmitC_emitFnDeclAux___lambda__3___closed__1;
x_16 = lean_string_append(x_15, x_14);
lean_dec(x_14);
x_17 = lean_string_append(x_6, x_16);
lean_dec(x_16);
x_18 = 1;
x_19 = lean_usize_add(x_2, x_18);
x_20 = lean_box(0);
x_2 = x_19;
x_4 = x_20;
x_6 = x_17;
goto _start;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; size_t x_27; size_t x_28; lean_object* x_29; 
x_22 = l_Array_foldlMUnsafe_fold___at_Lean_IR_EmitC_emitFileHeader___spec__1___closed__2;
x_23 = lean_string_append(x_11, x_22);
x_24 = l_Lean_IR_EmitC_emitFnDeclAux___lambda__3___closed__1;
x_25 = lean_string_append(x_24, x_23);
lean_dec(x_23);
x_26 = lean_string_append(x_6, x_25);
lean_dec(x_25);
x_27 = 1;
x_28 = lean_usize_add(x_2, x_27);
x_29 = lean_box(0);
x_2 = x_28;
x_4 = x_29;
x_6 = x_26;
goto _start;
}
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_4);
lean_ctor_set(x_31, 1, x_6);
return x_31;
}
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitFileHeader___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("#include <lean/lean.h>", 22);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitFileHeader___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("#endif", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitFileHeader___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_IR_EmitC_emitFileHeader___closed__2;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitFileHeader___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("extern \"C\" {", 12);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitFileHeader___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_EmitC_emitFileHeader___closed__4;
x_2 = l_Lean_IR_EmitC_emitFileHeader___closed__3;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitFileHeader___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("#ifdef __cplusplus", 18);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitFileHeader___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_EmitC_emitFileHeader___closed__6;
x_2 = l_Lean_IR_EmitC_emitFileHeader___closed__5;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitFileHeader___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_EmitC_emitFileHeader___closed__2;
x_2 = l_Lean_IR_EmitC_emitFileHeader___closed__7;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitFileHeader___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("#pragma GCC diagnostic ignored \"-Wunused-but-set-variable\"", 58);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitFileHeader___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_EmitC_emitFileHeader___closed__9;
x_2 = l_Lean_IR_EmitC_emitFileHeader___closed__8;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitFileHeader___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("#pragma GCC diagnostic ignored \"-Wunused-label\"", 47);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitFileHeader___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_EmitC_emitFileHeader___closed__11;
x_2 = l_Lean_IR_EmitC_emitFileHeader___closed__10;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitFileHeader___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("#pragma GCC diagnostic ignored \"-Wunused-parameter\"", 51);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitFileHeader___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_EmitC_emitFileHeader___closed__13;
x_2 = l_Lean_IR_EmitC_emitFileHeader___closed__12;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitFileHeader___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("#elif defined(__GNUC__) && !defined(__CLANG__)", 46);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitFileHeader___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_EmitC_emitFileHeader___closed__15;
x_2 = l_Lean_IR_EmitC_emitFileHeader___closed__14;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitFileHeader___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("#pragma clang diagnostic ignored \"-Wunused-label\"", 49);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitFileHeader___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_EmitC_emitFileHeader___closed__17;
x_2 = l_Lean_IR_EmitC_emitFileHeader___closed__16;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitFileHeader___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("#pragma clang diagnostic ignored \"-Wunused-parameter\"", 53);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitFileHeader___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_EmitC_emitFileHeader___closed__19;
x_2 = l_Lean_IR_EmitC_emitFileHeader___closed__18;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitFileHeader___closed__21() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("#if defined(__clang__)", 22);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitFileHeader___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_EmitC_emitFileHeader___closed__21;
x_2 = l_Lean_IR_EmitC_emitFileHeader___closed__20;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitFileHeader___closed__23() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("// Lean compiler output", 23);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitFileHeader___closed__24() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("// Module: ", 11);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitFileHeader___closed__25() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("// Imports:", 11);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitFileHeader(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_14 = l_Lean_IR_EmitC_getEnv(x_1, x_2);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_IR_EmitC_getModName(x_1, x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_IR_EmitC_emitFileHeader___closed__23;
x_21 = lean_string_append(x_19, x_20);
x_22 = l_Lean_IR_EmitC_emitLn___rarg___closed__1;
x_23 = lean_string_append(x_21, x_22);
x_24 = 1;
x_25 = l_Lean_Name_toString(x_18, x_24);
x_26 = l_Lean_IR_EmitC_emitFileHeader___closed__24;
x_27 = lean_string_append(x_26, x_25);
lean_dec(x_25);
x_28 = lean_string_append(x_23, x_27);
lean_dec(x_27);
x_29 = lean_string_append(x_28, x_22);
x_30 = l_Lean_IR_EmitC_emitFileHeader___closed__25;
x_31 = lean_string_append(x_29, x_30);
x_32 = l_Lean_Environment_imports(x_15);
lean_dec(x_15);
x_33 = lean_array_get_size(x_32);
x_34 = lean_unsigned_to_nat(0u);
x_35 = lean_nat_dec_lt(x_34, x_33);
if (x_35 == 0)
{
lean_dec(x_33);
lean_dec(x_32);
x_3 = x_31;
goto block_13;
}
else
{
uint8_t x_36; 
x_36 = lean_nat_dec_le(x_33, x_33);
if (x_36 == 0)
{
lean_dec(x_33);
lean_dec(x_32);
x_3 = x_31;
goto block_13;
}
else
{
size_t x_37; size_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_37 = 0;
x_38 = lean_usize_of_nat(x_33);
lean_dec(x_33);
x_39 = lean_box(0);
x_40 = l_Array_foldlMUnsafe_fold___at_Lean_IR_EmitC_emitFileHeader___spec__1(x_32, x_37, x_38, x_39, x_1, x_31);
lean_dec(x_32);
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec(x_40);
x_3 = x_41;
goto block_13;
}
}
block_13:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_4 = l_Array_foldlMUnsafe_fold___at_Lean_IR_EmitC_emitFileHeader___spec__1___closed__1;
x_5 = lean_string_append(x_3, x_4);
x_6 = l_Lean_IR_EmitC_emitLn___rarg___closed__1;
x_7 = lean_string_append(x_5, x_6);
x_8 = l_Lean_IR_EmitC_emitFileHeader___closed__1;
x_9 = lean_string_append(x_7, x_8);
x_10 = lean_string_append(x_9, x_6);
x_11 = l_Lean_IR_EmitC_emitFileHeader___closed__22;
x_12 = l_List_forM___at_Lean_IR_EmitC_emitMainFn___spec__3(x_11, x_1, x_10);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_EmitC_emitFileHeader___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l_Array_foldlMUnsafe_fold___at_Lean_IR_EmitC_emitFileHeader___spec__1(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitFileHeader___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_EmitC_emitFileHeader(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitFileFooter___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__1;
x_2 = l_Lean_IR_EmitC_emitFileHeader___closed__3;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitFileFooter___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_EmitC_emitFileHeader___closed__6;
x_2 = l_Lean_IR_EmitC_emitFileFooter___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitFileFooter(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_IR_EmitC_emitFileFooter___closed__2;
x_4 = l_List_forM___at_Lean_IR_EmitC_emitMainFn___spec__3(x_3, x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitFileFooter___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_EmitC_emitFileFooter(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_EmitC_throwUnknownVar___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unknown variable '", 18);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_throwUnknownVar___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = l_Nat_repr(x_1);
x_5 = l_Lean_IR_EmitC_argToCString___closed__1;
x_6 = lean_string_append(x_5, x_4);
lean_dec(x_4);
x_7 = l_Lean_IR_EmitC_throwUnknownVar___rarg___closed__1;
x_8 = lean_string_append(x_7, x_6);
lean_dec(x_6);
x_9 = l_Lean_IR_EmitC_getDecl___closed__2;
x_10 = lean_string_append(x_8, x_9);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_throwUnknownVar(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_IR_EmitC_throwUnknownVar___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_throwUnknownVar___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_EmitC_throwUnknownVar___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_AssocList_find_x3f___at_Lean_IR_EmitC_getJPParams___spec__2(lean_object* x_1, lean_object* x_2) {
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
x_7 = lean_nat_dec_eq(x_4, x_1);
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
LEAN_EXPORT lean_object* l_Std_HashMapImp_find_x3f___at_Lean_IR_EmitC_getJPParams___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint64_t x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_array_get_size(x_3);
x_5 = lean_uint64_of_nat(x_2);
x_6 = lean_uint64_to_usize(x_5);
x_7 = lean_usize_modn(x_6, x_4);
lean_dec(x_4);
x_8 = lean_array_uget(x_3, x_7);
lean_dec(x_3);
x_9 = l_Std_AssocList_find_x3f___at_Lean_IR_EmitC_getJPParams___spec__2(x_2, x_8);
lean_dec(x_8);
lean_dec(x_2);
return x_9;
}
}
static lean_object* _init_l_Lean_IR_EmitC_getJPParams___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unknown join point", 18);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_getJPParams(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 2);
lean_inc(x_4);
lean_dec(x_2);
x_5 = l_Std_HashMapImp_find_x3f___at_Lean_IR_EmitC_getJPParams___spec__1(x_4, x_1);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_IR_EmitC_getJPParams___closed__1;
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
lean_dec(x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_3);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Std_AssocList_find_x3f___at_Lean_IR_EmitC_getJPParams___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_AssocList_find_x3f___at_Lean_IR_EmitC_getJPParams___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_EmitC_declareVar___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("; ", 2);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_declareVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_5 = l_Lean_IR_EmitC_toCType(x_2);
x_6 = lean_string_append(x_4, x_5);
lean_dec(x_5);
x_7 = l_Lean_IR_EmitC_emitFnDeclAux___lambda__3___closed__1;
x_8 = lean_string_append(x_6, x_7);
x_9 = l_Nat_repr(x_1);
x_10 = l_Lean_IR_EmitC_argToCString___closed__1;
x_11 = lean_string_append(x_10, x_9);
lean_dec(x_9);
x_12 = lean_string_append(x_8, x_11);
lean_dec(x_11);
x_13 = l_Lean_IR_EmitC_declareVar___closed__1;
x_14 = lean_string_append(x_12, x_13);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_declareVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_EmitC_declareVar(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_EmitC_declareParams___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_2, x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; 
lean_dec(x_4);
x_8 = lean_array_uget(x_1, x_2);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_IR_EmitC_declareVar(x_9, x_10, x_5, x_6);
lean_dec(x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = 1;
x_15 = lean_usize_add(x_2, x_14);
x_2 = x_15;
x_4 = x_12;
x_6 = x_13;
goto _start;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_4);
lean_ctor_set(x_17, 1, x_6);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_declareParams(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_15 = l_Array_foldlMUnsafe_fold___at_Lean_IR_EmitC_declareParams___spec__1(x_1, x_12, x_13, x_14, x_2, x_3);
lean_dec(x_2);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_EmitC_declareParams___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l_Array_foldlMUnsafe_fold___at_Lean_IR_EmitC_declareParams___spec__1(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_declareParams___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_EmitC_declareParams(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_declareVars(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 3);
lean_inc(x_7);
x_8 = lean_ctor_get(x_3, 3);
lean_inc(x_8);
x_9 = l_Lean_IR_isTailCallTo(x_8, x_1);
lean_dec(x_1);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = l_Lean_IR_EmitC_declareVar(x_5, x_6, x_3, x_4);
lean_dec(x_6);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = 1;
x_1 = x_7;
x_2 = x_12;
x_4 = x_11;
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_14 = lean_box(x_2);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_4);
return x_15;
}
}
case 1:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_1, 3);
lean_inc(x_17);
lean_dec(x_1);
lean_inc(x_3);
x_18 = l_Lean_IR_EmitC_declareParams(x_16, x_3, x_4);
if (x_2 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_array_get_size(x_16);
lean_dec(x_16);
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_nat_dec_lt(x_21, x_20);
lean_dec(x_20);
x_1 = x_17;
x_2 = x_22;
x_4 = x_19;
goto _start;
}
else
{
lean_object* x_24; uint8_t x_25; 
lean_dec(x_16);
x_24 = lean_ctor_get(x_18, 1);
lean_inc(x_24);
lean_dec(x_18);
x_25 = 1;
x_1 = x_17;
x_2 = x_25;
x_4 = x_24;
goto _start;
}
}
default: 
{
uint8_t x_27; 
x_27 = l_Lean_IR_FnBody_isTerminal(x_1);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = l_Lean_IR_FnBody_body(x_1);
lean_dec(x_1);
x_1 = x_28;
goto _start;
}
else
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_3);
lean_dec(x_1);
x_30 = lean_box(x_2);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_4);
return x_31;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_declareVars___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Lean_IR_EmitC_declareVars(x_1, x_5, x_3, x_4);
return x_6;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitTag___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("lean_obj_tag(", 13);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitTag(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Lean_IR_IRType_isObj(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = l_Nat_repr(x_1);
x_7 = l_Lean_IR_EmitC_argToCString___closed__1;
x_8 = lean_string_append(x_7, x_6);
lean_dec(x_6);
x_9 = lean_string_append(x_4, x_8);
lean_dec(x_8);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_12 = l_Lean_IR_EmitC_emitTag___closed__1;
x_13 = lean_string_append(x_4, x_12);
x_14 = l_Nat_repr(x_1);
x_15 = l_Lean_IR_EmitC_argToCString___closed__1;
x_16 = lean_string_append(x_15, x_14);
lean_dec(x_14);
x_17 = lean_string_append(x_13, x_16);
lean_dec(x_16);
x_18 = l_Lean_IR_EmitC_emitFnDeclAux___lambda__2___closed__1;
x_19 = lean_string_append(x_17, x_18);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitTag___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_EmitC_emitTag(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_isIf(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(2u);
x_4 = lean_nat_dec_eq(x_2, x_3);
lean_dec(x_2);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_box(0);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Lean_IR_instInhabitedAlt;
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_get(x_6, x_1, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_array_get(x_6, x_1, x_12);
x_14 = l_Lean_IR_AltCore_body(x_13);
lean_dec(x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_11);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
else
{
lean_object* x_18; 
lean_dec(x_8);
x_18 = lean_box(0);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_isIf___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_IR_EmitC_isIf(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitInc___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(");", 2);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitInc___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = l_Lean_IR_EmitC_emitInc___lambda__1___closed__1;
x_5 = lean_string_append(x_3, x_4);
x_6 = l_Lean_IR_EmitC_emitLn___rarg___closed__1;
x_7 = lean_string_append(x_5, x_6);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitInc___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_IR_EmitC_emitInc___lambda__1___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitInc___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("lean_inc_ref_n", 14);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitInc___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("lean_inc_ref", 12);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitInc___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("lean_inc_n", 10);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitInc___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("lean_inc", 8);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitInc(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_6 = l_Nat_repr(x_1);
x_7 = l_Lean_IR_EmitC_argToCString___closed__1;
x_8 = lean_string_append(x_7, x_6);
lean_dec(x_6);
x_9 = l_Lean_IR_EmitC_emitInc___closed__1;
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_dec_eq(x_2, x_10);
if (x_3 == 0)
{
if (x_11 == 0)
{
lean_object* x_26; 
x_26 = l_Lean_IR_EmitC_emitInc___closed__2;
x_12 = x_26;
goto block_25;
}
else
{
lean_object* x_27; 
x_27 = l_Lean_IR_EmitC_emitInc___closed__3;
x_12 = x_27;
goto block_25;
}
}
else
{
if (x_11 == 0)
{
lean_object* x_28; 
x_28 = l_Lean_IR_EmitC_emitInc___closed__4;
x_12 = x_28;
goto block_25;
}
else
{
lean_object* x_29; 
x_29 = l_Lean_IR_EmitC_emitInc___closed__5;
x_12 = x_29;
goto block_25;
}
}
block_25:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_string_append(x_5, x_12);
lean_dec(x_12);
x_14 = l_Lean_IR_EmitC_emitFnDeclAux___lambda__3___closed__3;
x_15 = lean_string_append(x_13, x_14);
x_16 = lean_string_append(x_15, x_8);
lean_dec(x_8);
if (x_11 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_17 = l_Nat_forM_loop___at_Lean_IR_EmitC_emitFnDeclAux___spec__1___closed__1;
x_18 = lean_string_append(x_16, x_17);
x_19 = l_Nat_repr(x_2);
x_20 = lean_string_append(x_18, x_19);
lean_dec(x_19);
x_21 = lean_box(0);
x_22 = lean_apply_3(x_9, x_21, x_4, x_20);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_2);
x_23 = lean_box(0);
x_24 = lean_apply_3(x_9, x_23, x_4, x_16);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitInc___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_EmitC_emitInc___lambda__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitInc___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_3);
lean_dec(x_3);
x_7 = l_Lean_IR_EmitC_emitInc(x_1, x_2, x_6, x_4, x_5);
return x_7;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitDec___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("lean_dec_ref", 12);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitDec___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("lean_dec", 8);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitDec(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_6 = l_Nat_repr(x_1);
x_7 = l_Lean_IR_EmitC_argToCString___closed__1;
x_8 = lean_string_append(x_7, x_6);
lean_dec(x_6);
x_9 = l_Lean_IR_EmitC_emitInc___closed__1;
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_dec_eq(x_2, x_10);
if (x_3 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = l_Lean_IR_EmitC_emitDec___closed__1;
x_13 = lean_string_append(x_5, x_12);
x_14 = l_Lean_IR_EmitC_emitFnDeclAux___lambda__3___closed__3;
x_15 = lean_string_append(x_13, x_14);
x_16 = lean_string_append(x_15, x_8);
lean_dec(x_8);
if (x_11 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_17 = l_Nat_forM_loop___at_Lean_IR_EmitC_emitFnDeclAux___spec__1___closed__1;
x_18 = lean_string_append(x_16, x_17);
x_19 = l_Nat_repr(x_2);
x_20 = lean_string_append(x_18, x_19);
lean_dec(x_19);
x_21 = lean_box(0);
x_22 = lean_apply_3(x_9, x_21, x_4, x_20);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_2);
x_23 = lean_box(0);
x_24 = lean_apply_3(x_9, x_23, x_4, x_16);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = l_Lean_IR_EmitC_emitDec___closed__2;
x_26 = lean_string_append(x_5, x_25);
x_27 = l_Lean_IR_EmitC_emitFnDeclAux___lambda__3___closed__3;
x_28 = lean_string_append(x_26, x_27);
x_29 = lean_string_append(x_28, x_8);
lean_dec(x_8);
if (x_11 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_30 = l_Nat_forM_loop___at_Lean_IR_EmitC_emitFnDeclAux___spec__1___closed__1;
x_31 = lean_string_append(x_29, x_30);
x_32 = l_Nat_repr(x_2);
x_33 = lean_string_append(x_31, x_32);
lean_dec(x_32);
x_34 = lean_box(0);
x_35 = lean_apply_3(x_9, x_34, x_4, x_33);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_2);
x_36 = lean_box(0);
x_37 = lean_apply_3(x_9, x_36, x_4, x_29);
return x_37;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitDec___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_3);
lean_dec(x_3);
x_7 = l_Lean_IR_EmitC_emitDec(x_1, x_2, x_6, x_4, x_5);
return x_7;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitDel___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("lean_free_object(", 17);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitDel(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_4 = l_Lean_IR_EmitC_emitDel___closed__1;
x_5 = lean_string_append(x_3, x_4);
x_6 = l_Nat_repr(x_1);
x_7 = l_Lean_IR_EmitC_argToCString___closed__1;
x_8 = lean_string_append(x_7, x_6);
lean_dec(x_6);
x_9 = lean_string_append(x_5, x_8);
lean_dec(x_8);
x_10 = l_Lean_IR_EmitC_emitInc___lambda__1___closed__1;
x_11 = lean_string_append(x_9, x_10);
x_12 = l_Lean_IR_EmitC_emitLn___rarg___closed__1;
x_13 = lean_string_append(x_11, x_12);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitDel___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_EmitC_emitDel(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitSetTag___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("lean_ctor_set_tag(", 18);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitSetTag(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_5 = l_Lean_IR_EmitC_emitSetTag___closed__1;
x_6 = lean_string_append(x_4, x_5);
x_7 = l_Nat_repr(x_1);
x_8 = l_Lean_IR_EmitC_argToCString___closed__1;
x_9 = lean_string_append(x_8, x_7);
lean_dec(x_7);
x_10 = lean_string_append(x_6, x_9);
lean_dec(x_9);
x_11 = l_Nat_forM_loop___at_Lean_IR_EmitC_emitFnDeclAux___spec__1___closed__1;
x_12 = lean_string_append(x_10, x_11);
x_13 = l_Nat_repr(x_2);
x_14 = lean_string_append(x_12, x_13);
lean_dec(x_13);
x_15 = l_Lean_IR_EmitC_emitInc___lambda__1___closed__1;
x_16 = lean_string_append(x_14, x_15);
x_17 = l_Lean_IR_EmitC_emitLn___rarg___closed__1;
x_18 = lean_string_append(x_16, x_17);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitSetTag___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_EmitC_emitSetTag(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitSet___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("lean_ctor_set(", 14);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitSet(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_6 = l_Lean_IR_EmitC_emitSet___closed__1;
x_7 = lean_string_append(x_5, x_6);
x_8 = l_Nat_repr(x_1);
x_9 = l_Lean_IR_EmitC_argToCString___closed__1;
x_10 = lean_string_append(x_9, x_8);
lean_dec(x_8);
x_11 = lean_string_append(x_7, x_10);
lean_dec(x_10);
x_12 = l_Nat_forM_loop___at_Lean_IR_EmitC_emitFnDeclAux___spec__1___closed__1;
x_13 = lean_string_append(x_11, x_12);
x_14 = l_Nat_repr(x_2);
x_15 = lean_string_append(x_13, x_14);
lean_dec(x_14);
x_16 = lean_string_append(x_15, x_12);
x_17 = l_Lean_IR_EmitC_emitArg(x_3, x_4, x_16);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_19 = lean_ctor_get(x_17, 1);
x_20 = lean_ctor_get(x_17, 0);
lean_dec(x_20);
x_21 = l_Lean_IR_EmitC_emitInc___lambda__1___closed__1;
x_22 = lean_string_append(x_19, x_21);
x_23 = l_Lean_IR_EmitC_emitLn___rarg___closed__1;
x_24 = lean_string_append(x_22, x_23);
x_25 = lean_box(0);
lean_ctor_set(x_17, 1, x_24);
lean_ctor_set(x_17, 0, x_25);
return x_17;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_26 = lean_ctor_get(x_17, 1);
lean_inc(x_26);
lean_dec(x_17);
x_27 = l_Lean_IR_EmitC_emitInc___lambda__1___closed__1;
x_28 = lean_string_append(x_26, x_27);
x_29 = l_Lean_IR_EmitC_emitLn___rarg___closed__1;
x_30 = lean_string_append(x_28, x_29);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitSet___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_EmitC_emitSet(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitOffset___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("sizeof(void*)*", 14);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitOffset___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" + ", 3);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitOffset(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_lt(x_5, x_1);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_1);
x_7 = l_Nat_repr(x_2);
x_8 = lean_string_append(x_4, x_7);
lean_dec(x_7);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = l_Lean_IR_EmitC_emitOffset___closed__1;
x_12 = lean_string_append(x_4, x_11);
x_13 = l_Nat_repr(x_1);
x_14 = lean_string_append(x_12, x_13);
lean_dec(x_13);
x_15 = lean_nat_dec_lt(x_5, x_2);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_2);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_14);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_18 = l_Lean_IR_EmitC_emitOffset___closed__2;
x_19 = lean_string_append(x_14, x_18);
x_20 = l_Nat_repr(x_2);
x_21 = lean_string_append(x_19, x_20);
lean_dec(x_20);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitOffset___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_EmitC_emitOffset(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitUSet___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("lean_ctor_set_usize(", 20);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitUSet(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_6 = l_Lean_IR_EmitC_emitUSet___closed__1;
x_7 = lean_string_append(x_5, x_6);
x_8 = l_Nat_repr(x_1);
x_9 = l_Lean_IR_EmitC_argToCString___closed__1;
x_10 = lean_string_append(x_9, x_8);
lean_dec(x_8);
x_11 = lean_string_append(x_7, x_10);
lean_dec(x_10);
x_12 = l_Nat_forM_loop___at_Lean_IR_EmitC_emitFnDeclAux___spec__1___closed__1;
x_13 = lean_string_append(x_11, x_12);
x_14 = l_Nat_repr(x_2);
x_15 = lean_string_append(x_13, x_14);
lean_dec(x_14);
x_16 = lean_string_append(x_15, x_12);
x_17 = l_Nat_repr(x_3);
x_18 = lean_string_append(x_9, x_17);
lean_dec(x_17);
x_19 = lean_string_append(x_16, x_18);
lean_dec(x_18);
x_20 = l_Lean_IR_EmitC_emitInc___lambda__1___closed__1;
x_21 = lean_string_append(x_19, x_20);
x_22 = l_Lean_IR_EmitC_emitLn___rarg___closed__1;
x_23 = lean_string_append(x_21, x_22);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitUSet___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_EmitC_emitUSet(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitSSet___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_8 = l_Lean_IR_EmitC_emitFnDeclAux___lambda__3___closed__3;
x_9 = lean_string_append(x_7, x_8);
x_10 = l_Nat_repr(x_1);
x_11 = l_Lean_IR_EmitC_argToCString___closed__1;
x_12 = lean_string_append(x_11, x_10);
lean_dec(x_10);
x_13 = lean_string_append(x_9, x_12);
lean_dec(x_12);
x_14 = l_Nat_forM_loop___at_Lean_IR_EmitC_emitFnDeclAux___spec__1___closed__1;
x_15 = lean_string_append(x_13, x_14);
x_16 = l_Lean_IR_EmitC_emitOffset(x_2, x_3, x_6, x_15);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_18 = lean_ctor_get(x_16, 1);
x_19 = lean_ctor_get(x_16, 0);
lean_dec(x_19);
x_20 = lean_string_append(x_18, x_14);
x_21 = l_Nat_repr(x_4);
x_22 = lean_string_append(x_11, x_21);
lean_dec(x_21);
x_23 = lean_string_append(x_20, x_22);
lean_dec(x_22);
x_24 = l_Lean_IR_EmitC_emitInc___lambda__1___closed__1;
x_25 = lean_string_append(x_23, x_24);
x_26 = l_Lean_IR_EmitC_emitLn___rarg___closed__1;
x_27 = lean_string_append(x_25, x_26);
x_28 = lean_box(0);
lean_ctor_set(x_16, 1, x_27);
lean_ctor_set(x_16, 0, x_28);
return x_16;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_29 = lean_ctor_get(x_16, 1);
lean_inc(x_29);
lean_dec(x_16);
x_30 = lean_string_append(x_29, x_14);
x_31 = l_Nat_repr(x_4);
x_32 = lean_string_append(x_11, x_31);
lean_dec(x_31);
x_33 = lean_string_append(x_30, x_32);
lean_dec(x_32);
x_34 = l_Lean_IR_EmitC_emitInc___lambda__1___closed__1;
x_35 = lean_string_append(x_33, x_34);
x_36 = l_Lean_IR_EmitC_emitLn___rarg___closed__1;
x_37 = lean_string_append(x_35, x_36);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitSSet___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("lean_ctor_set_float", 19);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitSSet___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("lean_ctor_set_uint8", 19);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitSSet___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("lean_ctor_set_uint16", 20);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitSSet___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("lean_ctor_set_uint32", 20);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitSSet___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("lean_ctor_set_uint64", 20);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitSSet___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("invalid instruction", 19);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitSSet(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
switch (lean_obj_tag(x_5)) {
case 0:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = l_Lean_IR_EmitC_emitSSet___closed__1;
x_9 = lean_string_append(x_7, x_8);
x_10 = lean_box(0);
x_11 = l_Lean_IR_EmitC_emitSSet___lambda__1(x_1, x_2, x_3, x_4, x_10, x_6, x_9);
return x_11;
}
case 1:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = l_Lean_IR_EmitC_emitSSet___closed__2;
x_13 = lean_string_append(x_7, x_12);
x_14 = lean_box(0);
x_15 = l_Lean_IR_EmitC_emitSSet___lambda__1(x_1, x_2, x_3, x_4, x_14, x_6, x_13);
return x_15;
}
case 2:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = l_Lean_IR_EmitC_emitSSet___closed__3;
x_17 = lean_string_append(x_7, x_16);
x_18 = lean_box(0);
x_19 = l_Lean_IR_EmitC_emitSSet___lambda__1(x_1, x_2, x_3, x_4, x_18, x_6, x_17);
return x_19;
}
case 3:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = l_Lean_IR_EmitC_emitSSet___closed__4;
x_21 = lean_string_append(x_7, x_20);
x_22 = lean_box(0);
x_23 = l_Lean_IR_EmitC_emitSSet___lambda__1(x_1, x_2, x_3, x_4, x_22, x_6, x_21);
return x_23;
}
case 4:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = l_Lean_IR_EmitC_emitSSet___closed__5;
x_25 = lean_string_append(x_7, x_24);
x_26 = lean_box(0);
x_27 = l_Lean_IR_EmitC_emitSSet___lambda__1(x_1, x_2, x_3, x_4, x_26, x_6, x_25);
return x_27;
}
default: 
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_28 = l_Lean_IR_EmitC_emitSSet___closed__6;
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_7);
return x_29;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitSSet___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_IR_EmitC_emitSSet___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitSSet___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_IR_EmitC_emitSSet(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
return x_8;
}
}
static lean_object* _init_l_Nat_forM_loop___at_Lean_IR_EmitC_emitJmp___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" = ", 3);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Nat_forM_loop___at_Lean_IR_EmitC_emitJmp___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_eq(x_4, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_sub(x_4, x_9);
lean_dec(x_4);
x_11 = lean_nat_sub(x_3, x_10);
x_12 = lean_nat_sub(x_11, x_9);
lean_dec(x_11);
x_13 = l_Lean_IR_instInhabitedParam;
x_14 = lean_array_get(x_13, x_2, x_12);
x_15 = l_Lean_IR_instInhabitedArg;
x_16 = lean_array_get(x_15, x_1, x_12);
lean_dec(x_12);
x_17 = lean_ctor_get(x_14, 0);
lean_inc(x_17);
lean_dec(x_14);
x_18 = l_Nat_repr(x_17);
x_19 = l_Lean_IR_EmitC_argToCString___closed__1;
x_20 = lean_string_append(x_19, x_18);
lean_dec(x_18);
x_21 = lean_string_append(x_6, x_20);
lean_dec(x_20);
x_22 = l_Nat_forM_loop___at_Lean_IR_EmitC_emitJmp___spec__1___closed__1;
x_23 = lean_string_append(x_21, x_22);
x_24 = l_Lean_IR_EmitC_emitArg(x_16, x_5, x_23);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_26 = l_Lean_IR_EmitC_emitFnDeclAux___lambda__1___closed__1;
x_27 = lean_string_append(x_25, x_26);
x_28 = l_Lean_IR_EmitC_emitLn___rarg___closed__1;
x_29 = lean_string_append(x_27, x_28);
x_4 = x_10;
x_6 = x_29;
goto _start;
}
else
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_4);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_6);
return x_32;
}
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitJmp___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("goto ", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitJmp___lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("block_", 6);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitJmp___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_array_get_size(x_1);
lean_inc(x_7);
x_8 = l_Nat_forM_loop___at_Lean_IR_EmitC_emitJmp___spec__1(x_1, x_2, x_7, x_7, x_5, x_6);
lean_dec(x_7);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_10 = lean_ctor_get(x_8, 1);
x_11 = lean_ctor_get(x_8, 0);
lean_dec(x_11);
x_12 = l_Lean_IR_EmitC_emitJmp___lambda__1___closed__1;
x_13 = lean_string_append(x_10, x_12);
x_14 = l_Nat_repr(x_3);
x_15 = l_Lean_IR_EmitC_emitJmp___lambda__1___closed__2;
x_16 = lean_string_append(x_15, x_14);
lean_dec(x_14);
x_17 = lean_string_append(x_13, x_16);
lean_dec(x_16);
x_18 = l_Lean_IR_EmitC_emitFnDeclAux___lambda__1___closed__1;
x_19 = lean_string_append(x_17, x_18);
x_20 = l_Lean_IR_EmitC_emitLn___rarg___closed__1;
x_21 = lean_string_append(x_19, x_20);
x_22 = lean_box(0);
lean_ctor_set(x_8, 1, x_21);
lean_ctor_set(x_8, 0, x_22);
return x_8;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_23 = lean_ctor_get(x_8, 1);
lean_inc(x_23);
lean_dec(x_8);
x_24 = l_Lean_IR_EmitC_emitJmp___lambda__1___closed__1;
x_25 = lean_string_append(x_23, x_24);
x_26 = l_Nat_repr(x_3);
x_27 = l_Lean_IR_EmitC_emitJmp___lambda__1___closed__2;
x_28 = lean_string_append(x_27, x_26);
lean_dec(x_26);
x_29 = lean_string_append(x_25, x_28);
lean_dec(x_28);
x_30 = l_Lean_IR_EmitC_emitFnDeclAux___lambda__1___closed__1;
x_31 = lean_string_append(x_29, x_30);
x_32 = l_Lean_IR_EmitC_emitLn___rarg___closed__1;
x_33 = lean_string_append(x_31, x_32);
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
return x_35;
}
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitJmp___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("invalid goto", 12);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitJmp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_3);
lean_inc(x_1);
x_5 = l_Lean_IR_EmitC_getJPParams(x_1, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
x_9 = lean_array_get_size(x_2);
x_10 = lean_array_get_size(x_7);
x_11 = lean_nat_dec_eq(x_9, x_10);
lean_dec(x_10);
lean_dec(x_9);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_12 = l_Lean_IR_EmitC_emitJmp___closed__1;
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 0, x_12);
return x_5;
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_free_object(x_5);
x_13 = lean_box(0);
x_14 = l_Lean_IR_EmitC_emitJmp___lambda__1(x_2, x_7, x_1, x_13, x_3, x_8);
lean_dec(x_3);
lean_dec(x_7);
lean_dec(x_2);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_15 = lean_ctor_get(x_5, 0);
x_16 = lean_ctor_get(x_5, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_5);
x_17 = lean_array_get_size(x_2);
x_18 = lean_array_get_size(x_15);
x_19 = lean_nat_dec_eq(x_17, x_18);
lean_dec(x_18);
lean_dec(x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_15);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_20 = l_Lean_IR_EmitC_emitJmp___closed__1;
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_16);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_box(0);
x_23 = l_Lean_IR_EmitC_emitJmp___lambda__1(x_2, x_15, x_1, x_22, x_3, x_16);
lean_dec(x_3);
lean_dec(x_15);
lean_dec(x_2);
return x_23;
}
}
}
else
{
uint8_t x_24; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_5);
if (x_24 == 0)
{
return x_5;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_5, 0);
x_26 = lean_ctor_get(x_5, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_5);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_forM_loop___at_Lean_IR_EmitC_emitJmp___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Nat_forM_loop___at_Lean_IR_EmitC_emitJmp___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitJmp___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_IR_EmitC_emitJmp___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitLhs(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = l_Nat_repr(x_1);
x_5 = l_Lean_IR_EmitC_argToCString___closed__1;
x_6 = lean_string_append(x_5, x_4);
lean_dec(x_4);
x_7 = lean_string_append(x_3, x_6);
lean_dec(x_6);
x_8 = l_Nat_forM_loop___at_Lean_IR_EmitC_emitJmp___spec__1___closed__1;
x_9 = lean_string_append(x_7, x_8);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitLhs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_EmitC_emitLhs(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Nat_forM_loop___at_Lean_IR_EmitC_emitArgs___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Lean_IR_instInhabitedArg;
x_7 = lean_array_get(x_6, x_1, x_2);
x_8 = l_Lean_IR_EmitC_emitArg(x_7, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Nat_forM_loop___at_Lean_IR_EmitC_emitArgs___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_3, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_3, x_8);
lean_dec(x_3);
x_10 = lean_nat_sub(x_2, x_9);
x_11 = lean_nat_sub(x_10, x_8);
lean_dec(x_10);
x_12 = lean_nat_dec_lt(x_6, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_box(0);
x_14 = l_Nat_forM_loop___at_Lean_IR_EmitC_emitArgs___spec__1___lambda__1(x_1, x_11, x_13, x_4, x_5);
lean_dec(x_11);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_3 = x_9;
x_5 = x_15;
goto _start;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = l_Nat_forM_loop___at_Lean_IR_EmitC_emitFnDeclAux___spec__1___closed__1;
x_18 = lean_string_append(x_5, x_17);
x_19 = lean_box(0);
x_20 = l_Nat_forM_loop___at_Lean_IR_EmitC_emitArgs___spec__1___lambda__1(x_1, x_11, x_19, x_4, x_18);
lean_dec(x_11);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_3 = x_9;
x_5 = x_21;
goto _start;
}
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_3);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_5);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitArgs(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_array_get_size(x_1);
lean_inc(x_4);
x_5 = l_Nat_forM_loop___at_Lean_IR_EmitC_emitArgs___spec__1(x_1, x_4, x_4, x_2, x_3);
lean_dec(x_2);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Nat_forM_loop___at_Lean_IR_EmitC_emitArgs___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Nat_forM_loop___at_Lean_IR_EmitC_emitArgs___spec__1___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Nat_forM_loop___at_Lean_IR_EmitC_emitArgs___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Nat_forM_loop___at_Lean_IR_EmitC_emitArgs___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitArgs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_EmitC_emitArgs(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitCtorScalarSize___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("sizeof(size_t)*", 15);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitCtorScalarSize(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_1, x_5);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = lean_nat_dec_eq(x_2, x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_8 = l_Lean_IR_EmitC_emitCtorScalarSize___closed__1;
x_9 = lean_string_append(x_4, x_8);
x_10 = l_Nat_repr(x_1);
x_11 = lean_string_append(x_9, x_10);
lean_dec(x_10);
x_12 = l_Lean_IR_EmitC_emitOffset___closed__2;
x_13 = lean_string_append(x_11, x_12);
x_14 = l_Nat_repr(x_2);
x_15 = lean_string_append(x_13, x_14);
lean_dec(x_14);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_2);
x_18 = l_Lean_IR_EmitC_emitCtorScalarSize___closed__1;
x_19 = lean_string_append(x_4, x_18);
x_20 = l_Nat_repr(x_1);
x_21 = lean_string_append(x_19, x_20);
lean_dec(x_20);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_1);
x_24 = l_Nat_repr(x_2);
x_25 = lean_string_append(x_4, x_24);
lean_dec(x_24);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitCtorScalarSize___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_EmitC_emitCtorScalarSize(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitAllocCtor___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("lean_alloc_ctor(", 16);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitAllocCtor(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_4 = l_Lean_IR_EmitC_emitAllocCtor___closed__1;
x_5 = lean_string_append(x_3, x_4);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = l_Nat_repr(x_6);
x_8 = lean_string_append(x_5, x_7);
lean_dec(x_7);
x_9 = l_Nat_forM_loop___at_Lean_IR_EmitC_emitFnDeclAux___spec__1___closed__1;
x_10 = lean_string_append(x_8, x_9);
x_11 = lean_ctor_get(x_1, 2);
lean_inc(x_11);
x_12 = l_Nat_repr(x_11);
x_13 = lean_string_append(x_10, x_12);
lean_dec(x_12);
x_14 = lean_string_append(x_13, x_9);
x_15 = lean_ctor_get(x_1, 3);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 4);
lean_inc(x_16);
lean_dec(x_1);
x_17 = l_Lean_IR_EmitC_emitCtorScalarSize(x_15, x_16, x_2, x_14);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_19 = lean_ctor_get(x_17, 1);
x_20 = lean_ctor_get(x_17, 0);
lean_dec(x_20);
x_21 = l_Lean_IR_EmitC_emitInc___lambda__1___closed__1;
x_22 = lean_string_append(x_19, x_21);
x_23 = l_Lean_IR_EmitC_emitLn___rarg___closed__1;
x_24 = lean_string_append(x_22, x_23);
x_25 = lean_box(0);
lean_ctor_set(x_17, 1, x_24);
lean_ctor_set(x_17, 0, x_25);
return x_17;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_26 = lean_ctor_get(x_17, 1);
lean_inc(x_26);
lean_dec(x_17);
x_27 = l_Lean_IR_EmitC_emitInc___lambda__1___closed__1;
x_28 = lean_string_append(x_26, x_27);
x_29 = l_Lean_IR_EmitC_emitLn___rarg___closed__1;
x_30 = lean_string_append(x_28, x_29);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitAllocCtor___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_EmitC_emitAllocCtor(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Nat_forM_loop___at_Lean_IR_EmitC_emitCtorSetArgs___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_eq(x_4, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_sub(x_4, x_9);
lean_dec(x_4);
x_11 = lean_nat_sub(x_3, x_10);
x_12 = lean_nat_sub(x_11, x_9);
lean_dec(x_11);
x_13 = l_Lean_IR_EmitC_emitSet___closed__1;
x_14 = lean_string_append(x_6, x_13);
lean_inc(x_1);
x_15 = l_Nat_repr(x_1);
x_16 = l_Lean_IR_EmitC_argToCString___closed__1;
x_17 = lean_string_append(x_16, x_15);
lean_dec(x_15);
x_18 = lean_string_append(x_14, x_17);
lean_dec(x_17);
x_19 = l_Nat_forM_loop___at_Lean_IR_EmitC_emitFnDeclAux___spec__1___closed__1;
x_20 = lean_string_append(x_18, x_19);
lean_inc(x_12);
x_21 = l_Nat_repr(x_12);
x_22 = lean_string_append(x_20, x_21);
lean_dec(x_21);
x_23 = lean_string_append(x_22, x_19);
x_24 = l_Lean_IR_instInhabitedArg;
x_25 = lean_array_get(x_24, x_2, x_12);
lean_dec(x_12);
x_26 = l_Lean_IR_EmitC_emitArg(x_25, x_5, x_23);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = l_Lean_IR_EmitC_emitInc___lambda__1___closed__1;
x_29 = lean_string_append(x_27, x_28);
x_30 = l_Lean_IR_EmitC_emitLn___rarg___closed__1;
x_31 = lean_string_append(x_29, x_30);
x_4 = x_10;
x_6 = x_31;
goto _start;
}
else
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_4);
lean_dec(x_1);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_6);
return x_34;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitCtorSetArgs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_array_get_size(x_2);
lean_inc(x_5);
x_6 = l_Nat_forM_loop___at_Lean_IR_EmitC_emitCtorSetArgs___spec__1(x_1, x_2, x_5, x_5, x_3, x_4);
lean_dec(x_3);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Nat_forM_loop___at_Lean_IR_EmitC_emitCtorSetArgs___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Nat_forM_loop___at_Lean_IR_EmitC_emitCtorSetArgs___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitCtorSetArgs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_EmitC_emitCtorSetArgs(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitCtor___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("lean_box(", 9);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitCtor(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
lean_inc(x_1);
x_6 = l_Lean_IR_EmitC_emitLhs(x_1, x_4, x_5);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = lean_ctor_get(x_6, 1);
x_9 = lean_ctor_get(x_6, 0);
lean_dec(x_9);
x_10 = lean_ctor_get(x_2, 2);
lean_inc(x_10);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_nat_dec_eq(x_10, x_11);
lean_dec(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_free_object(x_6);
x_13 = l_Lean_IR_EmitC_emitAllocCtor(x_2, x_4, x_8);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = l_Lean_IR_EmitC_emitCtorSetArgs(x_1, x_3, x_4, x_14);
return x_15;
}
else
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_2, 3);
lean_inc(x_16);
x_17 = lean_nat_dec_eq(x_16, x_11);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_free_object(x_6);
x_18 = l_Lean_IR_EmitC_emitAllocCtor(x_2, x_4, x_8);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = l_Lean_IR_EmitC_emitCtorSetArgs(x_1, x_3, x_4, x_19);
return x_20;
}
else
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_2, 4);
lean_inc(x_21);
x_22 = lean_nat_dec_eq(x_21, x_11);
lean_dec(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_free_object(x_6);
x_23 = l_Lean_IR_EmitC_emitAllocCtor(x_2, x_4, x_8);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = l_Lean_IR_EmitC_emitCtorSetArgs(x_1, x_3, x_4, x_24);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_4);
lean_dec(x_1);
x_26 = l_Lean_IR_EmitC_emitCtor___closed__1;
x_27 = lean_string_append(x_8, x_26);
x_28 = lean_ctor_get(x_2, 1);
lean_inc(x_28);
lean_dec(x_2);
x_29 = l_Nat_repr(x_28);
x_30 = lean_string_append(x_27, x_29);
lean_dec(x_29);
x_31 = l_Lean_IR_EmitC_emitInc___lambda__1___closed__1;
x_32 = lean_string_append(x_30, x_31);
x_33 = l_Lean_IR_EmitC_emitLn___rarg___closed__1;
x_34 = lean_string_append(x_32, x_33);
x_35 = lean_box(0);
lean_ctor_set(x_6, 1, x_34);
lean_ctor_set(x_6, 0, x_35);
return x_6;
}
}
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_36 = lean_ctor_get(x_6, 1);
lean_inc(x_36);
lean_dec(x_6);
x_37 = lean_ctor_get(x_2, 2);
lean_inc(x_37);
x_38 = lean_unsigned_to_nat(0u);
x_39 = lean_nat_dec_eq(x_37, x_38);
lean_dec(x_37);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = l_Lean_IR_EmitC_emitAllocCtor(x_2, x_4, x_36);
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec(x_40);
x_42 = l_Lean_IR_EmitC_emitCtorSetArgs(x_1, x_3, x_4, x_41);
return x_42;
}
else
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_ctor_get(x_2, 3);
lean_inc(x_43);
x_44 = lean_nat_dec_eq(x_43, x_38);
lean_dec(x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = l_Lean_IR_EmitC_emitAllocCtor(x_2, x_4, x_36);
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
lean_dec(x_45);
x_47 = l_Lean_IR_EmitC_emitCtorSetArgs(x_1, x_3, x_4, x_46);
return x_47;
}
else
{
lean_object* x_48; uint8_t x_49; 
x_48 = lean_ctor_get(x_2, 4);
lean_inc(x_48);
x_49 = lean_nat_dec_eq(x_48, x_38);
lean_dec(x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = l_Lean_IR_EmitC_emitAllocCtor(x_2, x_4, x_36);
x_51 = lean_ctor_get(x_50, 1);
lean_inc(x_51);
lean_dec(x_50);
x_52 = l_Lean_IR_EmitC_emitCtorSetArgs(x_1, x_3, x_4, x_51);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_4);
lean_dec(x_1);
x_53 = l_Lean_IR_EmitC_emitCtor___closed__1;
x_54 = lean_string_append(x_36, x_53);
x_55 = lean_ctor_get(x_2, 1);
lean_inc(x_55);
lean_dec(x_2);
x_56 = l_Nat_repr(x_55);
x_57 = lean_string_append(x_54, x_56);
lean_dec(x_56);
x_58 = l_Lean_IR_EmitC_emitInc___lambda__1___closed__1;
x_59 = lean_string_append(x_57, x_58);
x_60 = l_Lean_IR_EmitC_emitLn___rarg___closed__1;
x_61 = lean_string_append(x_59, x_60);
x_62 = lean_box(0);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_61);
return x_63;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitCtor___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_EmitC_emitCtor(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
return x_6;
}
}
static lean_object* _init_l_Nat_forM_loop___at_Lean_IR_EmitC_emitReset___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" lean_ctor_release(", 19);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Nat_forM_loop___at_Lean_IR_EmitC_emitReset___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_3, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_3, x_8);
lean_dec(x_3);
x_10 = lean_nat_sub(x_2, x_9);
x_11 = lean_nat_sub(x_10, x_8);
lean_dec(x_10);
x_12 = l_Nat_forM_loop___at_Lean_IR_EmitC_emitReset___spec__1___closed__1;
x_13 = lean_string_append(x_5, x_12);
x_14 = lean_string_append(x_13, x_1);
x_15 = l_Nat_forM_loop___at_Lean_IR_EmitC_emitFnDeclAux___spec__1___closed__1;
x_16 = lean_string_append(x_14, x_15);
x_17 = l_Nat_repr(x_11);
x_18 = lean_string_append(x_16, x_17);
lean_dec(x_17);
x_19 = l_Lean_IR_EmitC_emitInc___lambda__1___closed__1;
x_20 = lean_string_append(x_18, x_19);
x_21 = l_Lean_IR_EmitC_emitLn___rarg___closed__1;
x_22 = lean_string_append(x_20, x_21);
x_3 = x_9;
x_5 = x_22;
goto _start;
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_3);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_5);
return x_25;
}
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitReset___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("if (lean_is_exclusive(", 22);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitReset___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(")) {", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitReset___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" lean_dec_ref(", 14);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitReset___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("lean_box(0);", 12);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitReset(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_6 = l_Lean_IR_EmitC_emitReset___closed__1;
x_7 = lean_string_append(x_5, x_6);
x_8 = l_Nat_repr(x_3);
x_9 = l_Lean_IR_EmitC_argToCString___closed__1;
x_10 = lean_string_append(x_9, x_8);
lean_dec(x_8);
x_11 = lean_string_append(x_7, x_10);
x_12 = l_Lean_IR_EmitC_emitReset___closed__2;
x_13 = lean_string_append(x_11, x_12);
x_14 = l_Lean_IR_EmitC_emitLn___rarg___closed__1;
x_15 = lean_string_append(x_13, x_14);
lean_inc(x_2);
x_16 = l_Nat_forM_loop___at_Lean_IR_EmitC_emitReset___spec__1(x_10, x_2, x_2, x_4, x_15);
lean_dec(x_2);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = l_Lean_IR_EmitC_emitFnDeclAux___lambda__3___closed__1;
x_19 = lean_string_append(x_17, x_18);
lean_inc(x_1);
x_20 = l_Lean_IR_EmitC_emitLhs(x_1, x_4, x_19);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_string_append(x_21, x_10);
x_23 = l_Lean_IR_EmitC_emitFnDeclAux___lambda__1___closed__1;
x_24 = lean_string_append(x_22, x_23);
x_25 = lean_string_append(x_24, x_14);
x_26 = l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__8;
x_27 = lean_string_append(x_25, x_26);
x_28 = lean_string_append(x_27, x_14);
x_29 = l_Lean_IR_EmitC_emitReset___closed__3;
x_30 = lean_string_append(x_28, x_29);
x_31 = lean_string_append(x_30, x_10);
lean_dec(x_10);
x_32 = l_Lean_IR_EmitC_emitInc___lambda__1___closed__1;
x_33 = lean_string_append(x_31, x_32);
x_34 = lean_string_append(x_33, x_14);
x_35 = lean_string_append(x_34, x_18);
x_36 = l_Lean_IR_EmitC_emitLhs(x_1, x_4, x_35);
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_38 = lean_ctor_get(x_36, 1);
x_39 = lean_ctor_get(x_36, 0);
lean_dec(x_39);
x_40 = l_Lean_IR_EmitC_emitReset___closed__4;
x_41 = lean_string_append(x_38, x_40);
x_42 = lean_string_append(x_41, x_14);
x_43 = l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__1;
x_44 = lean_string_append(x_42, x_43);
x_45 = lean_string_append(x_44, x_14);
x_46 = lean_box(0);
lean_ctor_set(x_36, 1, x_45);
lean_ctor_set(x_36, 0, x_46);
return x_36;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_47 = lean_ctor_get(x_36, 1);
lean_inc(x_47);
lean_dec(x_36);
x_48 = l_Lean_IR_EmitC_emitReset___closed__4;
x_49 = lean_string_append(x_47, x_48);
x_50 = lean_string_append(x_49, x_14);
x_51 = l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__1;
x_52 = lean_string_append(x_50, x_51);
x_53 = lean_string_append(x_52, x_14);
x_54 = lean_box(0);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_53);
return x_55;
}
}
}
LEAN_EXPORT lean_object* l_Nat_forM_loop___at_Lean_IR_EmitC_emitReset___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Nat_forM_loop___at_Lean_IR_EmitC_emitReset___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitReset___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_EmitC_emitReset(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitReuse___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__1;
x_7 = lean_string_append(x_5, x_6);
x_8 = l_Lean_IR_EmitC_emitLn___rarg___closed__1;
x_9 = lean_string_append(x_7, x_8);
x_10 = l_Lean_IR_EmitC_emitCtorSetArgs(x_1, x_2, x_4, x_9);
return x_10;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitReuse___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("if (lean_is_scalar(", 19);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitReuse___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" lean_ctor_set_tag(", 19);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitReuse(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_8 = l_Lean_IR_EmitC_emitReuse___closed__1;
x_9 = lean_string_append(x_7, x_8);
x_10 = l_Nat_repr(x_2);
x_11 = l_Lean_IR_EmitC_argToCString___closed__1;
x_12 = lean_string_append(x_11, x_10);
lean_dec(x_10);
x_13 = lean_string_append(x_9, x_12);
x_14 = l_Lean_IR_EmitC_emitReset___closed__2;
x_15 = lean_string_append(x_13, x_14);
x_16 = l_Lean_IR_EmitC_emitLn___rarg___closed__1;
x_17 = lean_string_append(x_15, x_16);
x_18 = l_Lean_IR_EmitC_emitFnDeclAux___lambda__3___closed__1;
x_19 = lean_string_append(x_17, x_18);
lean_inc(x_1);
x_20 = l_Lean_IR_EmitC_emitLhs(x_1, x_6, x_19);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
lean_inc(x_3);
x_22 = l_Lean_IR_EmitC_emitAllocCtor(x_3, x_6, x_21);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__8;
x_25 = lean_string_append(x_23, x_24);
x_26 = lean_string_append(x_25, x_16);
x_27 = lean_string_append(x_26, x_18);
lean_inc(x_1);
x_28 = l_Lean_IR_EmitC_emitLhs(x_1, x_6, x_27);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = lean_string_append(x_29, x_12);
lean_dec(x_12);
x_31 = l_Lean_IR_EmitC_emitFnDeclAux___lambda__1___closed__1;
x_32 = lean_string_append(x_30, x_31);
x_33 = lean_string_append(x_32, x_16);
if (x_4 == 0)
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_3);
x_34 = lean_box(0);
x_35 = l_Lean_IR_EmitC_emitReuse___lambda__1(x_1, x_5, x_34, x_6, x_33);
lean_dec(x_5);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_36 = l_Lean_IR_EmitC_emitReuse___closed__2;
x_37 = lean_string_append(x_33, x_36);
lean_inc(x_1);
x_38 = l_Nat_repr(x_1);
x_39 = lean_string_append(x_11, x_38);
lean_dec(x_38);
x_40 = lean_string_append(x_37, x_39);
lean_dec(x_39);
x_41 = l_Nat_forM_loop___at_Lean_IR_EmitC_emitFnDeclAux___spec__1___closed__1;
x_42 = lean_string_append(x_40, x_41);
x_43 = lean_ctor_get(x_3, 1);
lean_inc(x_43);
lean_dec(x_3);
x_44 = l_Nat_repr(x_43);
x_45 = lean_string_append(x_42, x_44);
lean_dec(x_44);
x_46 = l_Lean_IR_EmitC_emitInc___lambda__1___closed__1;
x_47 = lean_string_append(x_45, x_46);
x_48 = lean_string_append(x_47, x_16);
x_49 = lean_box(0);
x_50 = l_Lean_IR_EmitC_emitReuse___lambda__1(x_1, x_5, x_49, x_6, x_48);
lean_dec(x_5);
return x_50;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitReuse___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_EmitC_emitReuse___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitReuse___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_4);
lean_dec(x_4);
x_9 = l_Lean_IR_EmitC_emitReuse(x_1, x_2, x_3, x_8, x_5, x_6, x_7);
return x_9;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitProj___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("lean_ctor_get(", 14);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitProj(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = l_Lean_IR_EmitC_emitLhs(x_1, x_4, x_5);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_8 = lean_ctor_get(x_6, 1);
x_9 = lean_ctor_get(x_6, 0);
lean_dec(x_9);
x_10 = l_Lean_IR_EmitC_emitProj___closed__1;
x_11 = lean_string_append(x_8, x_10);
x_12 = l_Nat_repr(x_3);
x_13 = l_Lean_IR_EmitC_argToCString___closed__1;
x_14 = lean_string_append(x_13, x_12);
lean_dec(x_12);
x_15 = lean_string_append(x_11, x_14);
lean_dec(x_14);
x_16 = l_Nat_forM_loop___at_Lean_IR_EmitC_emitFnDeclAux___spec__1___closed__1;
x_17 = lean_string_append(x_15, x_16);
x_18 = l_Nat_repr(x_2);
x_19 = lean_string_append(x_17, x_18);
lean_dec(x_18);
x_20 = l_Lean_IR_EmitC_emitInc___lambda__1___closed__1;
x_21 = lean_string_append(x_19, x_20);
x_22 = l_Lean_IR_EmitC_emitLn___rarg___closed__1;
x_23 = lean_string_append(x_21, x_22);
x_24 = lean_box(0);
lean_ctor_set(x_6, 1, x_23);
lean_ctor_set(x_6, 0, x_24);
return x_6;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_25 = lean_ctor_get(x_6, 1);
lean_inc(x_25);
lean_dec(x_6);
x_26 = l_Lean_IR_EmitC_emitProj___closed__1;
x_27 = lean_string_append(x_25, x_26);
x_28 = l_Nat_repr(x_3);
x_29 = l_Lean_IR_EmitC_argToCString___closed__1;
x_30 = lean_string_append(x_29, x_28);
lean_dec(x_28);
x_31 = lean_string_append(x_27, x_30);
lean_dec(x_30);
x_32 = l_Nat_forM_loop___at_Lean_IR_EmitC_emitFnDeclAux___spec__1___closed__1;
x_33 = lean_string_append(x_31, x_32);
x_34 = l_Nat_repr(x_2);
x_35 = lean_string_append(x_33, x_34);
lean_dec(x_34);
x_36 = l_Lean_IR_EmitC_emitInc___lambda__1___closed__1;
x_37 = lean_string_append(x_35, x_36);
x_38 = l_Lean_IR_EmitC_emitLn___rarg___closed__1;
x_39 = lean_string_append(x_37, x_38);
x_40 = lean_box(0);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
return x_41;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitProj___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_EmitC_emitProj(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitUProj___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("lean_ctor_get_usize(", 20);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitUProj(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = l_Lean_IR_EmitC_emitLhs(x_1, x_4, x_5);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_8 = lean_ctor_get(x_6, 1);
x_9 = lean_ctor_get(x_6, 0);
lean_dec(x_9);
x_10 = l_Lean_IR_EmitC_emitUProj___closed__1;
x_11 = lean_string_append(x_8, x_10);
x_12 = l_Nat_repr(x_3);
x_13 = l_Lean_IR_EmitC_argToCString___closed__1;
x_14 = lean_string_append(x_13, x_12);
lean_dec(x_12);
x_15 = lean_string_append(x_11, x_14);
lean_dec(x_14);
x_16 = l_Nat_forM_loop___at_Lean_IR_EmitC_emitFnDeclAux___spec__1___closed__1;
x_17 = lean_string_append(x_15, x_16);
x_18 = l_Nat_repr(x_2);
x_19 = lean_string_append(x_17, x_18);
lean_dec(x_18);
x_20 = l_Lean_IR_EmitC_emitInc___lambda__1___closed__1;
x_21 = lean_string_append(x_19, x_20);
x_22 = l_Lean_IR_EmitC_emitLn___rarg___closed__1;
x_23 = lean_string_append(x_21, x_22);
x_24 = lean_box(0);
lean_ctor_set(x_6, 1, x_23);
lean_ctor_set(x_6, 0, x_24);
return x_6;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_25 = lean_ctor_get(x_6, 1);
lean_inc(x_25);
lean_dec(x_6);
x_26 = l_Lean_IR_EmitC_emitUProj___closed__1;
x_27 = lean_string_append(x_25, x_26);
x_28 = l_Nat_repr(x_3);
x_29 = l_Lean_IR_EmitC_argToCString___closed__1;
x_30 = lean_string_append(x_29, x_28);
lean_dec(x_28);
x_31 = lean_string_append(x_27, x_30);
lean_dec(x_30);
x_32 = l_Nat_forM_loop___at_Lean_IR_EmitC_emitFnDeclAux___spec__1___closed__1;
x_33 = lean_string_append(x_31, x_32);
x_34 = l_Nat_repr(x_2);
x_35 = lean_string_append(x_33, x_34);
lean_dec(x_34);
x_36 = l_Lean_IR_EmitC_emitInc___lambda__1___closed__1;
x_37 = lean_string_append(x_35, x_36);
x_38 = l_Lean_IR_EmitC_emitLn___rarg___closed__1;
x_39 = lean_string_append(x_37, x_38);
x_40 = lean_box(0);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
return x_41;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitUProj___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_EmitC_emitUProj(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitSProj___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_7 = l_Lean_IR_EmitC_emitFnDeclAux___lambda__3___closed__3;
x_8 = lean_string_append(x_6, x_7);
x_9 = l_Nat_repr(x_1);
x_10 = l_Lean_IR_EmitC_argToCString___closed__1;
x_11 = lean_string_append(x_10, x_9);
lean_dec(x_9);
x_12 = lean_string_append(x_8, x_11);
lean_dec(x_11);
x_13 = l_Nat_forM_loop___at_Lean_IR_EmitC_emitFnDeclAux___spec__1___closed__1;
x_14 = lean_string_append(x_12, x_13);
x_15 = l_Lean_IR_EmitC_emitOffset(x_2, x_3, x_5, x_14);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_17 = lean_ctor_get(x_15, 1);
x_18 = lean_ctor_get(x_15, 0);
lean_dec(x_18);
x_19 = l_Lean_IR_EmitC_emitInc___lambda__1___closed__1;
x_20 = lean_string_append(x_17, x_19);
x_21 = l_Lean_IR_EmitC_emitLn___rarg___closed__1;
x_22 = lean_string_append(x_20, x_21);
x_23 = lean_box(0);
lean_ctor_set(x_15, 1, x_22);
lean_ctor_set(x_15, 0, x_23);
return x_15;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_24 = lean_ctor_get(x_15, 1);
lean_inc(x_24);
lean_dec(x_15);
x_25 = l_Lean_IR_EmitC_emitInc___lambda__1___closed__1;
x_26 = lean_string_append(x_24, x_25);
x_27 = l_Lean_IR_EmitC_emitLn___rarg___closed__1;
x_28 = lean_string_append(x_26, x_27);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitSProj___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("lean_ctor_get_float", 19);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitSProj___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("lean_ctor_get_uint8", 19);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitSProj___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("lean_ctor_get_uint16", 20);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitSProj___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("lean_ctor_get_uint32", 20);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitSProj___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("lean_ctor_get_uint64", 20);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitSProj(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_IR_EmitC_emitLhs(x_1, x_6, x_7);
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = l_Lean_IR_EmitC_emitSProj___closed__1;
x_11 = lean_string_append(x_9, x_10);
x_12 = lean_box(0);
x_13 = l_Lean_IR_EmitC_emitSProj___lambda__1(x_5, x_3, x_4, x_12, x_6, x_11);
lean_dec(x_6);
return x_13;
}
case 1:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_8, 1);
lean_inc(x_14);
lean_dec(x_8);
x_15 = l_Lean_IR_EmitC_emitSProj___closed__2;
x_16 = lean_string_append(x_14, x_15);
x_17 = lean_box(0);
x_18 = l_Lean_IR_EmitC_emitSProj___lambda__1(x_5, x_3, x_4, x_17, x_6, x_16);
lean_dec(x_6);
return x_18;
}
case 2:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_8, 1);
lean_inc(x_19);
lean_dec(x_8);
x_20 = l_Lean_IR_EmitC_emitSProj___closed__3;
x_21 = lean_string_append(x_19, x_20);
x_22 = lean_box(0);
x_23 = l_Lean_IR_EmitC_emitSProj___lambda__1(x_5, x_3, x_4, x_22, x_6, x_21);
lean_dec(x_6);
return x_23;
}
case 3:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_8, 1);
lean_inc(x_24);
lean_dec(x_8);
x_25 = l_Lean_IR_EmitC_emitSProj___closed__4;
x_26 = lean_string_append(x_24, x_25);
x_27 = lean_box(0);
x_28 = l_Lean_IR_EmitC_emitSProj___lambda__1(x_5, x_3, x_4, x_27, x_6, x_26);
lean_dec(x_6);
return x_28;
}
case 4:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_8, 1);
lean_inc(x_29);
lean_dec(x_8);
x_30 = l_Lean_IR_EmitC_emitSProj___closed__5;
x_31 = lean_string_append(x_29, x_30);
x_32 = lean_box(0);
x_33 = l_Lean_IR_EmitC_emitSProj___lambda__1(x_5, x_3, x_4, x_32, x_6, x_31);
lean_dec(x_6);
return x_33;
}
default: 
{
uint8_t x_34; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_34 = !lean_is_exclusive(x_8);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_8, 0);
lean_dec(x_35);
x_36 = l_Lean_IR_EmitC_emitSSet___closed__6;
lean_ctor_set_tag(x_8, 1);
lean_ctor_set(x_8, 0, x_36);
return x_8;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_8, 1);
lean_inc(x_37);
lean_dec(x_8);
x_38 = l_Lean_IR_EmitC_emitSSet___closed__6;
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitSProj___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_IR_EmitC_emitSProj___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_List_mapTRAux___at_Lean_IR_EmitC_toStringArgs___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___rarg(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_Lean_IR_EmitC_argToCString(x_5);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_7);
{
lean_object* _tmp_0 = x_6;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_1);
x_11 = l_Lean_IR_EmitC_argToCString(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_2);
x_1 = x_10;
x_2 = x_12;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_toStringArgs(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_array_to_list(lean_box(0), x_1);
x_3 = lean_box(0);
x_4 = l_List_mapTRAux___at_Lean_IR_EmitC_toStringArgs___spec__1(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Nat_foldM_loop___at_Lean_IR_EmitC_emitSimpleExternalCall___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = l_Lean_IR_instInhabitedArg;
x_7 = lean_array_get(x_6, x_1, x_2);
x_8 = l_Lean_IR_EmitC_emitArg(x_7, x_4, x_5);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_8, 0);
lean_dec(x_10);
x_11 = 0;
x_12 = lean_box(x_11);
lean_ctor_set(x_8, 0, x_12);
return x_8;
}
else
{
lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_dec(x_8);
x_14 = 0;
x_15 = lean_box(x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_13);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldM_loop___at_Lean_IR_EmitC_emitSimpleExternalCall___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_4, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_sub(x_4, x_10);
lean_dec(x_4);
x_12 = lean_nat_sub(x_3, x_11);
x_13 = lean_nat_sub(x_12, x_10);
lean_dec(x_12);
x_14 = l_Lean_IR_instInhabitedParam;
x_15 = lean_array_get(x_14, x_1, x_13);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = l_Lean_IR_IRType_isIrrelevant(x_16);
lean_dec(x_16);
if (x_17 == 0)
{
if (x_5 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_18 = l_Nat_forM_loop___at_Lean_IR_EmitC_emitFnDeclAux___spec__1___closed__1;
x_19 = lean_string_append(x_7, x_18);
x_20 = lean_box(0);
x_21 = l_Nat_foldM_loop___at_Lean_IR_EmitC_emitSimpleExternalCall___spec__1___lambda__1(x_2, x_13, x_20, x_6, x_19);
lean_dec(x_13);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_unbox(x_22);
lean_dec(x_22);
x_4 = x_11;
x_5 = x_24;
x_7 = x_23;
goto _start;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_26 = lean_box(0);
x_27 = l_Nat_foldM_loop___at_Lean_IR_EmitC_emitSimpleExternalCall___spec__1___lambda__1(x_2, x_13, x_26, x_6, x_7);
lean_dec(x_13);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_unbox(x_28);
lean_dec(x_28);
x_4 = x_11;
x_5 = x_30;
x_7 = x_29;
goto _start;
}
}
else
{
lean_dec(x_13);
x_4 = x_11;
goto _start;
}
}
else
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_4);
x_33 = lean_box(x_5);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_7);
return x_34;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitSimpleExternalCall(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; uint8_t x_12; 
x_6 = lean_string_append(x_5, x_1);
x_7 = l_Lean_IR_EmitC_emitFnDeclAux___lambda__3___closed__3;
x_8 = lean_string_append(x_6, x_7);
x_9 = lean_array_get_size(x_3);
x_10 = 1;
lean_inc(x_9);
x_11 = l_Nat_foldM_loop___at_Lean_IR_EmitC_emitSimpleExternalCall___spec__1(x_2, x_3, x_9, x_9, x_10, x_4, x_8);
lean_dec(x_9);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_ctor_get(x_11, 1);
x_14 = lean_ctor_get(x_11, 0);
lean_dec(x_14);
x_15 = l_Lean_IR_EmitC_emitInc___lambda__1___closed__1;
x_16 = lean_string_append(x_13, x_15);
x_17 = l_Lean_IR_EmitC_emitLn___rarg___closed__1;
x_18 = lean_string_append(x_16, x_17);
x_19 = lean_box(0);
lean_ctor_set(x_11, 1, x_18);
lean_ctor_set(x_11, 0, x_19);
return x_11;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_20 = lean_ctor_get(x_11, 1);
lean_inc(x_20);
lean_dec(x_11);
x_21 = l_Lean_IR_EmitC_emitInc___lambda__1___closed__1;
x_22 = lean_string_append(x_20, x_21);
x_23 = l_Lean_IR_EmitC_emitLn___rarg___closed__1;
x_24 = lean_string_append(x_22, x_23);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldM_loop___at_Lean_IR_EmitC_emitSimpleExternalCall___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Nat_foldM_loop___at_Lean_IR_EmitC_emitSimpleExternalCall___spec__1___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Nat_foldM_loop___at_Lean_IR_EmitC_emitSimpleExternalCall___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_5);
lean_dec(x_5);
x_9 = l_Nat_foldM_loop___at_Lean_IR_EmitC_emitSimpleExternalCall___spec__1(x_1, x_2, x_3, x_4, x_8, x_6, x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitSimpleExternalCall___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_EmitC_emitSimpleExternalCall(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitExternCall___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("failed to emit extern application '", 35);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitExternCall(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_List_forM___at_Lean_IR_EmitC_emitFnDecls___spec__5___closed__2;
x_8 = l_Lean_getExternEntryFor(x_3, x_7);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_4);
x_9 = 1;
x_10 = l_Lean_Name_toString(x_1, x_9);
x_11 = l_Lean_IR_EmitC_emitExternCall___closed__1;
x_12 = lean_string_append(x_11, x_10);
lean_dec(x_10);
x_13 = l_Lean_IR_EmitC_getDecl___closed__2;
x_14 = lean_string_append(x_12, x_13);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_6);
return x_15;
}
else
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_8, 0);
lean_inc(x_16);
lean_dec(x_8);
switch (lean_obj_tag(x_16)) {
case 0:
{
uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_16);
lean_dec(x_4);
x_17 = 1;
x_18 = l_Lean_Name_toString(x_1, x_17);
x_19 = l_Lean_IR_EmitC_emitExternCall___closed__1;
x_20 = lean_string_append(x_19, x_18);
lean_dec(x_18);
x_21 = l_Lean_IR_EmitC_getDecl___closed__2;
x_22 = lean_string_append(x_20, x_21);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_6);
return x_23;
}
case 1:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_1);
x_24 = lean_ctor_get(x_16, 1);
lean_inc(x_24);
lean_dec(x_16);
x_25 = l_Lean_IR_EmitC_toStringArgs(x_4);
x_26 = l_Lean_expandExternPattern(x_24, x_25);
lean_dec(x_25);
x_27 = lean_string_append(x_6, x_26);
lean_dec(x_26);
x_28 = l_Lean_IR_EmitC_emitFnDeclAux___lambda__1___closed__1;
x_29 = lean_string_append(x_27, x_28);
x_30 = l_Lean_IR_EmitC_emitLn___rarg___closed__1;
x_31 = lean_string_append(x_29, x_30);
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
default: 
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_1);
x_34 = lean_ctor_get(x_16, 1);
lean_inc(x_34);
lean_dec(x_16);
x_35 = l_Lean_IR_EmitC_emitSimpleExternalCall(x_34, x_2, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_34);
return x_35;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitExternCall___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_IR_EmitC_emitExternCall(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitFullApp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Lean_IR_EmitC_emitLhs(x_1, x_4, x_5);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
lean_inc(x_2);
x_8 = l_Lean_IR_EmitC_getDecl(x_2, x_4, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_IR_EmitC_emitCName(x_2, x_4, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = l_Lean_IR_EmitC_emitFnDeclAux___lambda__3___closed__2;
x_14 = lean_array_get_size(x_3);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_nat_dec_lt(x_15, x_14);
lean_dec(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_3);
x_17 = lean_box(0);
x_18 = lean_apply_3(x_13, x_17, x_4, x_12);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_19 = l_Lean_IR_EmitC_emitFnDeclAux___lambda__3___closed__3;
x_20 = lean_string_append(x_12, x_19);
lean_inc(x_4);
x_21 = l_Lean_IR_EmitC_emitArgs(x_3, x_4, x_20);
lean_dec(x_3);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = l_Lean_IR_EmitC_emitFnDeclAux___lambda__2___closed__1;
x_24 = lean_string_append(x_22, x_23);
x_25 = lean_box(0);
x_26 = lean_apply_3(x_13, x_25, x_4, x_24);
return x_26;
}
}
else
{
uint8_t x_27; 
lean_dec(x_4);
lean_dec(x_3);
x_27 = !lean_is_exclusive(x_11);
if (x_27 == 0)
{
return x_11;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_11, 0);
x_29 = lean_ctor_get(x_11, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_11);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_8, 1);
lean_inc(x_31);
lean_dec(x_8);
x_32 = lean_ctor_get(x_9, 1);
lean_inc(x_32);
x_33 = lean_ctor_get(x_9, 3);
lean_inc(x_33);
lean_dec(x_9);
x_34 = l_Lean_IR_EmitC_emitExternCall(x_2, x_32, x_33, x_3, x_4, x_31);
lean_dec(x_4);
lean_dec(x_33);
lean_dec(x_32);
return x_34;
}
}
else
{
uint8_t x_35; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_35 = !lean_is_exclusive(x_8);
if (x_35 == 0)
{
return x_8;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_8, 0);
x_37 = lean_ctor_get(x_8, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_8);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
static lean_object* _init_l_Nat_forM_loop___at_Lean_IR_EmitC_emitPartialApp___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("lean_closure_set(", 17);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Nat_forM_loop___at_Lean_IR_EmitC_emitPartialApp___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_eq(x_4, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_sub(x_4, x_9);
lean_dec(x_4);
x_11 = lean_nat_sub(x_3, x_10);
x_12 = lean_nat_sub(x_11, x_9);
lean_dec(x_11);
x_13 = l_Lean_IR_instInhabitedArg;
x_14 = lean_array_get(x_13, x_2, x_12);
x_15 = l_Nat_forM_loop___at_Lean_IR_EmitC_emitPartialApp___spec__1___closed__1;
x_16 = lean_string_append(x_6, x_15);
lean_inc(x_1);
x_17 = l_Nat_repr(x_1);
x_18 = l_Lean_IR_EmitC_argToCString___closed__1;
x_19 = lean_string_append(x_18, x_17);
lean_dec(x_17);
x_20 = lean_string_append(x_16, x_19);
lean_dec(x_19);
x_21 = l_Nat_forM_loop___at_Lean_IR_EmitC_emitFnDeclAux___spec__1___closed__1;
x_22 = lean_string_append(x_20, x_21);
x_23 = l_Nat_repr(x_12);
x_24 = lean_string_append(x_22, x_23);
lean_dec(x_23);
x_25 = lean_string_append(x_24, x_21);
x_26 = l_Lean_IR_EmitC_emitArg(x_14, x_5, x_25);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = l_Lean_IR_EmitC_emitInc___lambda__1___closed__1;
x_29 = lean_string_append(x_27, x_28);
x_30 = l_Lean_IR_EmitC_emitLn___rarg___closed__1;
x_31 = lean_string_append(x_29, x_30);
x_4 = x_10;
x_6 = x_31;
goto _start;
}
else
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_4);
lean_dec(x_1);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_6);
return x_34;
}
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitPartialApp___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("lean_alloc_closure((void*)(", 27);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitPartialApp___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("), ", 3);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitPartialApp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
lean_inc(x_2);
x_6 = l_Lean_IR_EmitC_getDecl(x_2, x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_IR_Decl_params(x_7);
lean_dec(x_7);
x_10 = lean_array_get_size(x_9);
lean_dec(x_9);
lean_inc(x_1);
x_11 = l_Lean_IR_EmitC_emitLhs(x_1, x_4, x_8);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = l_Lean_IR_EmitC_emitPartialApp___closed__1;
x_14 = lean_string_append(x_12, x_13);
x_15 = l_Lean_IR_EmitC_emitCName(x_2, x_4, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = l_Lean_IR_EmitC_emitPartialApp___closed__2;
x_18 = lean_string_append(x_16, x_17);
x_19 = l_Nat_repr(x_10);
x_20 = lean_string_append(x_18, x_19);
lean_dec(x_19);
x_21 = l_Nat_forM_loop___at_Lean_IR_EmitC_emitFnDeclAux___spec__1___closed__1;
x_22 = lean_string_append(x_20, x_21);
x_23 = lean_array_get_size(x_3);
lean_inc(x_23);
x_24 = l_Nat_repr(x_23);
x_25 = lean_string_append(x_22, x_24);
lean_dec(x_24);
x_26 = l_Lean_IR_EmitC_emitInc___lambda__1___closed__1;
x_27 = lean_string_append(x_25, x_26);
x_28 = l_Lean_IR_EmitC_emitLn___rarg___closed__1;
x_29 = lean_string_append(x_27, x_28);
lean_inc(x_23);
x_30 = l_Nat_forM_loop___at_Lean_IR_EmitC_emitPartialApp___spec__1(x_1, x_3, x_23, x_23, x_4, x_29);
lean_dec(x_4);
lean_dec(x_23);
lean_dec(x_3);
return x_30;
}
else
{
uint8_t x_31; 
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_15);
if (x_31 == 0)
{
return x_15;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_15, 0);
x_33 = lean_ctor_get(x_15, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_15);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
uint8_t x_35; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_6);
if (x_35 == 0)
{
return x_6;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_6, 0);
x_37 = lean_ctor_get(x_6, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_6);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_forM_loop___at_Lean_IR_EmitC_emitPartialApp___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Nat_forM_loop___at_Lean_IR_EmitC_emitPartialApp___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitApp___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("lean_apply_", 11);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitApp___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("{ lean_object* _aargs[] = {", 27);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitApp___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("};", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitApp___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("lean_apply_m(", 13);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitApp___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(", _aargs); }", 12);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitApp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_array_get_size(x_3);
x_7 = l_Lean_closureMaxArgs;
x_8 = lean_nat_dec_lt(x_7, x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_9 = l_Lean_IR_EmitC_emitLhs(x_1, x_4, x_5);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = l_Lean_IR_EmitC_emitApp___closed__1;
x_12 = lean_string_append(x_10, x_11);
x_13 = l_Nat_repr(x_6);
x_14 = lean_string_append(x_12, x_13);
lean_dec(x_13);
x_15 = l_Lean_IR_EmitC_emitFnDeclAux___lambda__3___closed__3;
x_16 = lean_string_append(x_14, x_15);
x_17 = l_Nat_repr(x_2);
x_18 = l_Lean_IR_EmitC_argToCString___closed__1;
x_19 = lean_string_append(x_18, x_17);
lean_dec(x_17);
x_20 = lean_string_append(x_16, x_19);
lean_dec(x_19);
x_21 = l_Nat_forM_loop___at_Lean_IR_EmitC_emitFnDeclAux___spec__1___closed__1;
x_22 = lean_string_append(x_20, x_21);
x_23 = l_Lean_IR_EmitC_emitArgs(x_3, x_4, x_22);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_25 = lean_ctor_get(x_23, 1);
x_26 = lean_ctor_get(x_23, 0);
lean_dec(x_26);
x_27 = l_Lean_IR_EmitC_emitInc___lambda__1___closed__1;
x_28 = lean_string_append(x_25, x_27);
x_29 = l_Lean_IR_EmitC_emitLn___rarg___closed__1;
x_30 = lean_string_append(x_28, x_29);
x_31 = lean_box(0);
lean_ctor_set(x_23, 1, x_30);
lean_ctor_set(x_23, 0, x_31);
return x_23;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_32 = lean_ctor_get(x_23, 1);
lean_inc(x_32);
lean_dec(x_23);
x_33 = l_Lean_IR_EmitC_emitInc___lambda__1___closed__1;
x_34 = lean_string_append(x_32, x_33);
x_35 = l_Lean_IR_EmitC_emitLn___rarg___closed__1;
x_36 = lean_string_append(x_34, x_35);
x_37 = lean_box(0);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_39 = l_Lean_IR_EmitC_emitApp___closed__2;
x_40 = lean_string_append(x_5, x_39);
lean_inc(x_4);
x_41 = l_Lean_IR_EmitC_emitArgs(x_3, x_4, x_40);
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
lean_dec(x_41);
x_43 = l_Lean_IR_EmitC_emitApp___closed__3;
x_44 = lean_string_append(x_42, x_43);
x_45 = l_Lean_IR_EmitC_emitLn___rarg___closed__1;
x_46 = lean_string_append(x_44, x_45);
x_47 = l_Lean_IR_EmitC_emitLhs(x_1, x_4, x_46);
lean_dec(x_4);
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_49 = lean_ctor_get(x_47, 1);
x_50 = lean_ctor_get(x_47, 0);
lean_dec(x_50);
x_51 = l_Lean_IR_EmitC_emitApp___closed__4;
x_52 = lean_string_append(x_49, x_51);
x_53 = l_Nat_repr(x_2);
x_54 = l_Lean_IR_EmitC_argToCString___closed__1;
x_55 = lean_string_append(x_54, x_53);
lean_dec(x_53);
x_56 = lean_string_append(x_52, x_55);
lean_dec(x_55);
x_57 = l_Nat_forM_loop___at_Lean_IR_EmitC_emitFnDeclAux___spec__1___closed__1;
x_58 = lean_string_append(x_56, x_57);
x_59 = l_Nat_repr(x_6);
x_60 = lean_string_append(x_58, x_59);
lean_dec(x_59);
x_61 = l_Lean_IR_EmitC_emitApp___closed__5;
x_62 = lean_string_append(x_60, x_61);
x_63 = lean_string_append(x_62, x_45);
x_64 = lean_box(0);
lean_ctor_set(x_47, 1, x_63);
lean_ctor_set(x_47, 0, x_64);
return x_47;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_65 = lean_ctor_get(x_47, 1);
lean_inc(x_65);
lean_dec(x_47);
x_66 = l_Lean_IR_EmitC_emitApp___closed__4;
x_67 = lean_string_append(x_65, x_66);
x_68 = l_Nat_repr(x_2);
x_69 = l_Lean_IR_EmitC_argToCString___closed__1;
x_70 = lean_string_append(x_69, x_68);
lean_dec(x_68);
x_71 = lean_string_append(x_67, x_70);
lean_dec(x_70);
x_72 = l_Nat_forM_loop___at_Lean_IR_EmitC_emitFnDeclAux___spec__1___closed__1;
x_73 = lean_string_append(x_71, x_72);
x_74 = l_Nat_repr(x_6);
x_75 = lean_string_append(x_73, x_74);
lean_dec(x_74);
x_76 = l_Lean_IR_EmitC_emitApp___closed__5;
x_77 = lean_string_append(x_75, x_76);
x_78 = lean_string_append(x_77, x_45);
x_79 = lean_box(0);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_78);
return x_80;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitApp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_EmitC_emitApp(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
return x_6;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitBoxFn___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("lean_box_float", 14);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitBoxFn___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("lean_box", 8);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitBoxFn___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("lean_box_uint32", 15);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitBoxFn___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("lean_box_uint64", 15);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitBoxFn___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("lean_box_usize", 14);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitBoxFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = l_Lean_IR_EmitC_emitBoxFn___closed__1;
x_5 = lean_string_append(x_3, x_4);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
case 3:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = l_Lean_IR_EmitC_emitBoxFn___closed__3;
x_9 = lean_string_append(x_3, x_8);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
case 4:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = l_Lean_IR_EmitC_emitBoxFn___closed__4;
x_13 = lean_string_append(x_3, x_12);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
case 5:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = l_Lean_IR_EmitC_emitBoxFn___closed__5;
x_17 = lean_string_append(x_3, x_16);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
default: 
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = l_Lean_IR_EmitC_emitBoxFn___closed__2;
x_21 = lean_string_append(x_3, x_20);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitBoxFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_EmitC_emitBoxFn(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitBox(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = l_Lean_IR_EmitC_emitLhs(x_1, x_4, x_5);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = l_Lean_IR_EmitC_emitBoxFn(x_3, x_4, x_7);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_10 = lean_ctor_get(x_8, 1);
x_11 = lean_ctor_get(x_8, 0);
lean_dec(x_11);
x_12 = l_Lean_IR_EmitC_emitFnDeclAux___lambda__3___closed__3;
x_13 = lean_string_append(x_10, x_12);
x_14 = l_Nat_repr(x_2);
x_15 = l_Lean_IR_EmitC_argToCString___closed__1;
x_16 = lean_string_append(x_15, x_14);
lean_dec(x_14);
x_17 = lean_string_append(x_13, x_16);
lean_dec(x_16);
x_18 = l_Lean_IR_EmitC_emitInc___lambda__1___closed__1;
x_19 = lean_string_append(x_17, x_18);
x_20 = l_Lean_IR_EmitC_emitLn___rarg___closed__1;
x_21 = lean_string_append(x_19, x_20);
x_22 = lean_box(0);
lean_ctor_set(x_8, 1, x_21);
lean_ctor_set(x_8, 0, x_22);
return x_8;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_23 = lean_ctor_get(x_8, 1);
lean_inc(x_23);
lean_dec(x_8);
x_24 = l_Lean_IR_EmitC_emitFnDeclAux___lambda__3___closed__3;
x_25 = lean_string_append(x_23, x_24);
x_26 = l_Nat_repr(x_2);
x_27 = l_Lean_IR_EmitC_argToCString___closed__1;
x_28 = lean_string_append(x_27, x_26);
lean_dec(x_26);
x_29 = lean_string_append(x_25, x_28);
lean_dec(x_28);
x_30 = l_Lean_IR_EmitC_emitInc___lambda__1___closed__1;
x_31 = lean_string_append(x_29, x_30);
x_32 = l_Lean_IR_EmitC_emitLn___rarg___closed__1;
x_33 = lean_string_append(x_31, x_32);
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
return x_35;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitBox___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_EmitC_emitBox(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitUnbox___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_5 = l_Lean_IR_EmitC_emitFnDeclAux___lambda__3___closed__3;
x_6 = lean_string_append(x_4, x_5);
x_7 = l_Nat_repr(x_1);
x_8 = l_Lean_IR_EmitC_argToCString___closed__1;
x_9 = lean_string_append(x_8, x_7);
lean_dec(x_7);
x_10 = lean_string_append(x_6, x_9);
lean_dec(x_9);
x_11 = l_Lean_IR_EmitC_emitInc___lambda__1___closed__1;
x_12 = lean_string_append(x_10, x_11);
x_13 = l_Lean_IR_EmitC_emitLn___rarg___closed__1;
x_14 = lean_string_append(x_12, x_13);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitUnbox___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("lean_unbox_float", 16);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitUnbox___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("lean_unbox", 10);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitUnbox___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("lean_unbox_uint32", 17);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitUnbox___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("lean_unbox_uint64", 17);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitUnbox___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("lean_unbox_usize", 16);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitUnbox(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_EmitC_emitLhs(x_1, x_4, x_5);
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = l_Lean_IR_EmitC_emitUnbox___closed__1;
x_9 = lean_string_append(x_7, x_8);
x_10 = lean_box(0);
x_11 = l_Lean_IR_EmitC_emitUnbox___lambda__1(x_3, x_10, x_4, x_9);
lean_dec(x_4);
return x_11;
}
case 3:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_6, 1);
lean_inc(x_12);
lean_dec(x_6);
x_13 = l_Lean_IR_EmitC_emitUnbox___closed__3;
x_14 = lean_string_append(x_12, x_13);
x_15 = lean_box(0);
x_16 = l_Lean_IR_EmitC_emitUnbox___lambda__1(x_3, x_15, x_4, x_14);
lean_dec(x_4);
return x_16;
}
case 4:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_6, 1);
lean_inc(x_17);
lean_dec(x_6);
x_18 = l_Lean_IR_EmitC_emitUnbox___closed__4;
x_19 = lean_string_append(x_17, x_18);
x_20 = lean_box(0);
x_21 = l_Lean_IR_EmitC_emitUnbox___lambda__1(x_3, x_20, x_4, x_19);
lean_dec(x_4);
return x_21;
}
case 5:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_6, 1);
lean_inc(x_22);
lean_dec(x_6);
x_23 = l_Lean_IR_EmitC_emitUnbox___closed__5;
x_24 = lean_string_append(x_22, x_23);
x_25 = lean_box(0);
x_26 = l_Lean_IR_EmitC_emitUnbox___lambda__1(x_3, x_25, x_4, x_24);
lean_dec(x_4);
return x_26;
}
default: 
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_2);
x_27 = lean_ctor_get(x_6, 1);
lean_inc(x_27);
lean_dec(x_6);
x_28 = l_Lean_IR_EmitC_emitUnbox___closed__2;
x_29 = lean_string_append(x_27, x_28);
x_30 = lean_box(0);
x_31 = l_Lean_IR_EmitC_emitUnbox___lambda__1(x_3, x_30, x_4, x_29);
lean_dec(x_4);
return x_31;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitUnbox___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_EmitC_emitUnbox___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitIsShared___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("!lean_is_exclusive(", 19);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitIsShared(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_IR_EmitC_emitLhs(x_1, x_3, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_7 = lean_ctor_get(x_5, 1);
x_8 = lean_ctor_get(x_5, 0);
lean_dec(x_8);
x_9 = l_Lean_IR_EmitC_emitIsShared___closed__1;
x_10 = lean_string_append(x_7, x_9);
x_11 = l_Nat_repr(x_2);
x_12 = l_Lean_IR_EmitC_argToCString___closed__1;
x_13 = lean_string_append(x_12, x_11);
lean_dec(x_11);
x_14 = lean_string_append(x_10, x_13);
lean_dec(x_13);
x_15 = l_Lean_IR_EmitC_emitInc___lambda__1___closed__1;
x_16 = lean_string_append(x_14, x_15);
x_17 = l_Lean_IR_EmitC_emitLn___rarg___closed__1;
x_18 = lean_string_append(x_16, x_17);
x_19 = lean_box(0);
lean_ctor_set(x_5, 1, x_18);
lean_ctor_set(x_5, 0, x_19);
return x_5;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_20 = lean_ctor_get(x_5, 1);
lean_inc(x_20);
lean_dec(x_5);
x_21 = l_Lean_IR_EmitC_emitIsShared___closed__1;
x_22 = lean_string_append(x_20, x_21);
x_23 = l_Nat_repr(x_2);
x_24 = l_Lean_IR_EmitC_argToCString___closed__1;
x_25 = lean_string_append(x_24, x_23);
lean_dec(x_23);
x_26 = lean_string_append(x_22, x_25);
lean_dec(x_25);
x_27 = l_Lean_IR_EmitC_emitInc___lambda__1___closed__1;
x_28 = lean_string_append(x_26, x_27);
x_29 = l_Lean_IR_EmitC_emitLn___rarg___closed__1;
x_30 = lean_string_append(x_28, x_29);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitIsShared___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_EmitC_emitIsShared(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitIsTaggedPtr___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("!lean_is_scalar(", 16);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitIsTaggedPtr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_IR_EmitC_emitLhs(x_1, x_3, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_7 = lean_ctor_get(x_5, 1);
x_8 = lean_ctor_get(x_5, 0);
lean_dec(x_8);
x_9 = l_Lean_IR_EmitC_emitIsTaggedPtr___closed__1;
x_10 = lean_string_append(x_7, x_9);
x_11 = l_Nat_repr(x_2);
x_12 = l_Lean_IR_EmitC_argToCString___closed__1;
x_13 = lean_string_append(x_12, x_11);
lean_dec(x_11);
x_14 = lean_string_append(x_10, x_13);
lean_dec(x_13);
x_15 = l_Lean_IR_EmitC_emitInc___lambda__1___closed__1;
x_16 = lean_string_append(x_14, x_15);
x_17 = l_Lean_IR_EmitC_emitLn___rarg___closed__1;
x_18 = lean_string_append(x_16, x_17);
x_19 = lean_box(0);
lean_ctor_set(x_5, 1, x_18);
lean_ctor_set(x_5, 0, x_19);
return x_5;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_20 = lean_ctor_get(x_5, 1);
lean_inc(x_20);
lean_dec(x_5);
x_21 = l_Lean_IR_EmitC_emitIsTaggedPtr___closed__1;
x_22 = lean_string_append(x_20, x_21);
x_23 = l_Nat_repr(x_2);
x_24 = l_Lean_IR_EmitC_argToCString___closed__1;
x_25 = lean_string_append(x_24, x_23);
lean_dec(x_23);
x_26 = lean_string_append(x_22, x_25);
lean_dec(x_25);
x_27 = l_Lean_IR_EmitC_emitInc___lambda__1___closed__1;
x_28 = lean_string_append(x_26, x_27);
x_29 = l_Lean_IR_EmitC_emitLn___rarg___closed__1;
x_30 = lean_string_append(x_28, x_29);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitIsTaggedPtr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_EmitC_emitIsTaggedPtr(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_toHexDigit(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Nat_digitChar(x_1);
x_3 = l_Array_foldlMUnsafe_fold___at_Lean_IR_EmitC_emitFileHeader___spec__1___closed__1;
x_4 = lean_string_push(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_toHexDigit___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_IR_EmitC_toHexDigit(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_EmitC_quoteString___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("\\x", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_quoteString___lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("\\\"", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_quoteString___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("\\\\", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_quoteString___lambda__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("\\t", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_quoteString___lambda__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("\\r", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_quoteString___lambda__1___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("\\n", 2);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_quoteString___lambda__1(lean_object* x_1, uint32_t x_2) {
_start:
{
uint32_t x_3; uint8_t x_4; 
x_3 = 10;
x_4 = lean_uint32_dec_eq(x_2, x_3);
if (x_4 == 0)
{
uint32_t x_5; uint8_t x_6; 
x_5 = 13;
x_6 = lean_uint32_dec_eq(x_2, x_5);
if (x_6 == 0)
{
uint32_t x_7; uint8_t x_8; 
x_7 = 9;
x_8 = lean_uint32_dec_eq(x_2, x_7);
if (x_8 == 0)
{
uint32_t x_9; uint8_t x_10; 
x_9 = 92;
x_10 = lean_uint32_dec_eq(x_2, x_9);
if (x_10 == 0)
{
uint32_t x_11; uint8_t x_12; 
x_11 = 34;
x_12 = lean_uint32_dec_eq(x_2, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_uint32_to_nat(x_2);
x_14 = lean_unsigned_to_nat(31u);
x_15 = lean_nat_dec_le(x_13, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_13);
x_16 = l_Array_foldlMUnsafe_fold___at_Lean_IR_EmitC_emitFileHeader___spec__1___closed__1;
x_17 = lean_string_push(x_16, x_2);
x_18 = lean_string_append(x_1, x_17);
lean_dec(x_17);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_19 = lean_unsigned_to_nat(16u);
x_20 = lean_nat_div(x_13, x_19);
x_21 = l_Lean_IR_EmitC_toHexDigit(x_20);
lean_dec(x_20);
x_22 = l_Lean_IR_EmitC_quoteString___lambda__1___closed__1;
x_23 = lean_string_append(x_22, x_21);
lean_dec(x_21);
x_24 = lean_nat_mod(x_13, x_19);
lean_dec(x_13);
x_25 = l_Lean_IR_EmitC_toHexDigit(x_24);
lean_dec(x_24);
x_26 = lean_string_append(x_23, x_25);
lean_dec(x_25);
x_27 = lean_string_append(x_1, x_26);
lean_dec(x_26);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = l_Lean_IR_EmitC_quoteString___lambda__1___closed__2;
x_29 = lean_string_append(x_1, x_28);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = l_Lean_IR_EmitC_quoteString___lambda__1___closed__3;
x_31 = lean_string_append(x_1, x_30);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = l_Lean_IR_EmitC_quoteString___lambda__1___closed__4;
x_33 = lean_string_append(x_1, x_32);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = l_Lean_IR_EmitC_quoteString___lambda__1___closed__5;
x_35 = lean_string_append(x_1, x_34);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = l_Lean_IR_EmitC_quoteString___lambda__1___closed__6;
x_37 = lean_string_append(x_1, x_36);
return x_37;
}
}
}
static lean_object* _init_l_Lean_IR_EmitC_quoteString___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_IR_EmitC_quoteString___lambda__1___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_quoteString___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("\"", 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_quoteString(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_string_utf8_byte_size(x_1);
x_3 = l_Lean_IR_EmitC_quoteString___closed__1;
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Lean_IR_EmitC_quoteString___closed__2;
x_6 = l_String_foldlAux_loop___rarg(x_3, x_1, x_2, x_4, x_5);
lean_dec(x_2);
x_7 = lean_string_append(x_6, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_quoteString___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_4 = l_Lean_IR_EmitC_quoteString___lambda__1(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_quoteString___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_IR_EmitC_quoteString(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitNumLit___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("lean_cstr_to_nat(\"", 18);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitNumLit___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("\")", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitNumLit___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("lean_unsigned_to_nat(", 21);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitNumLit___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("u)", 2);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitNumLit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Lean_IR_IRType_isObj(x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = l_Nat_repr(x_2);
x_7 = lean_string_append(x_4, x_6);
lean_dec(x_6);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
lean_object* x_10; uint8_t x_11; 
x_10 = l_UInt32_size;
x_11 = lean_nat_dec_lt(x_2, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = l_Lean_IR_EmitC_emitNumLit___closed__1;
x_13 = lean_string_append(x_4, x_12);
x_14 = l_Nat_repr(x_2);
x_15 = lean_string_append(x_13, x_14);
lean_dec(x_14);
x_16 = l_Lean_IR_EmitC_emitNumLit___closed__2;
x_17 = lean_string_append(x_15, x_16);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_20 = l_Lean_IR_EmitC_emitNumLit___closed__3;
x_21 = lean_string_append(x_4, x_20);
x_22 = l_Nat_repr(x_2);
x_23 = lean_string_append(x_21, x_22);
lean_dec(x_22);
x_24 = l_Lean_IR_EmitC_emitNumLit___closed__4;
x_25 = lean_string_append(x_23, x_24);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitNumLit___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_EmitC_emitNumLit(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitLit___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("lean_mk_string_from_bytes(", 26);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitLit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_EmitC_emitLhs(x_1, x_4, x_5);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
lean_dec(x_3);
x_9 = l_Lean_IR_EmitC_emitNumLit(x_2, x_8, x_4, x_7);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_9, 1);
x_12 = lean_ctor_get(x_9, 0);
lean_dec(x_12);
x_13 = l_Lean_IR_EmitC_emitFnDeclAux___lambda__1___closed__1;
x_14 = lean_string_append(x_11, x_13);
x_15 = l_Lean_IR_EmitC_emitLn___rarg___closed__1;
x_16 = lean_string_append(x_14, x_15);
x_17 = lean_box(0);
lean_ctor_set(x_9, 1, x_16);
lean_ctor_set(x_9, 0, x_17);
return x_9;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_18 = lean_ctor_get(x_9, 1);
lean_inc(x_18);
lean_dec(x_9);
x_19 = l_Lean_IR_EmitC_emitFnDeclAux___lambda__1___closed__1;
x_20 = lean_string_append(x_18, x_19);
x_21 = l_Lean_IR_EmitC_emitLn___rarg___closed__1;
x_22 = lean_string_append(x_20, x_21);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_6);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_26 = lean_ctor_get(x_6, 1);
x_27 = lean_ctor_get(x_6, 0);
lean_dec(x_27);
x_28 = lean_ctor_get(x_3, 0);
lean_inc(x_28);
lean_dec(x_3);
x_29 = l_Lean_IR_EmitC_emitLit___closed__1;
x_30 = lean_string_append(x_26, x_29);
x_31 = l_Lean_IR_EmitC_quoteString(x_28);
x_32 = lean_string_append(x_30, x_31);
lean_dec(x_31);
x_33 = l_Nat_forM_loop___at_Lean_IR_EmitC_emitFnDeclAux___spec__1___closed__1;
x_34 = lean_string_append(x_32, x_33);
x_35 = lean_string_utf8_byte_size(x_28);
lean_dec(x_28);
x_36 = l_Nat_repr(x_35);
x_37 = lean_string_append(x_34, x_36);
lean_dec(x_36);
x_38 = l_Lean_IR_EmitC_emitInc___lambda__1___closed__1;
x_39 = lean_string_append(x_37, x_38);
x_40 = l_Lean_IR_EmitC_emitLn___rarg___closed__1;
x_41 = lean_string_append(x_39, x_40);
x_42 = lean_box(0);
lean_ctor_set(x_6, 1, x_41);
lean_ctor_set(x_6, 0, x_42);
return x_6;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_43 = lean_ctor_get(x_6, 1);
lean_inc(x_43);
lean_dec(x_6);
x_44 = lean_ctor_get(x_3, 0);
lean_inc(x_44);
lean_dec(x_3);
x_45 = l_Lean_IR_EmitC_emitLit___closed__1;
x_46 = lean_string_append(x_43, x_45);
x_47 = l_Lean_IR_EmitC_quoteString(x_44);
x_48 = lean_string_append(x_46, x_47);
lean_dec(x_47);
x_49 = l_Nat_forM_loop___at_Lean_IR_EmitC_emitFnDeclAux___spec__1___closed__1;
x_50 = lean_string_append(x_48, x_49);
x_51 = lean_string_utf8_byte_size(x_44);
lean_dec(x_44);
x_52 = l_Nat_repr(x_51);
x_53 = lean_string_append(x_50, x_52);
lean_dec(x_52);
x_54 = l_Lean_IR_EmitC_emitInc___lambda__1___closed__1;
x_55 = lean_string_append(x_53, x_54);
x_56 = l_Lean_IR_EmitC_emitLn___rarg___closed__1;
x_57 = lean_string_append(x_55, x_56);
x_58 = lean_box(0);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_57);
return x_59;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitLit___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_EmitC_emitLit(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitVDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
switch (lean_obj_tag(x_3)) {
case 0:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_3, 1);
lean_inc(x_7);
lean_dec(x_3);
x_8 = l_Lean_IR_EmitC_emitCtor(x_1, x_6, x_7, x_4, x_5);
lean_dec(x_7);
return x_8;
}
case 1:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_2);
x_9 = lean_ctor_get(x_3, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
lean_dec(x_3);
x_11 = l_Lean_IR_EmitC_emitReset(x_1, x_9, x_10, x_4, x_5);
lean_dec(x_4);
return x_11;
}
case 2:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_2);
x_12 = lean_ctor_get(x_3, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_3, 1);
lean_inc(x_13);
x_14 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
x_15 = lean_ctor_get(x_3, 2);
lean_inc(x_15);
lean_dec(x_3);
x_16 = l_Lean_IR_EmitC_emitReuse(x_1, x_12, x_13, x_14, x_15, x_4, x_5);
return x_16;
}
case 3:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_2);
x_17 = lean_ctor_get(x_3, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_3, 1);
lean_inc(x_18);
lean_dec(x_3);
x_19 = l_Lean_IR_EmitC_emitProj(x_1, x_17, x_18, x_4, x_5);
lean_dec(x_4);
return x_19;
}
case 4:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_2);
x_20 = lean_ctor_get(x_3, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_3, 1);
lean_inc(x_21);
lean_dec(x_3);
x_22 = l_Lean_IR_EmitC_emitUProj(x_1, x_20, x_21, x_4, x_5);
lean_dec(x_4);
return x_22;
}
case 5:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_3, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_3, 1);
lean_inc(x_24);
x_25 = lean_ctor_get(x_3, 2);
lean_inc(x_25);
lean_dec(x_3);
x_26 = l_Lean_IR_EmitC_emitSProj(x_1, x_2, x_23, x_24, x_25, x_4, x_5);
return x_26;
}
case 6:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_2);
x_27 = lean_ctor_get(x_3, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_3, 1);
lean_inc(x_28);
lean_dec(x_3);
x_29 = l_Lean_IR_EmitC_emitFullApp(x_1, x_27, x_28, x_4, x_5);
return x_29;
}
case 7:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_2);
x_30 = lean_ctor_get(x_3, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_3, 1);
lean_inc(x_31);
lean_dec(x_3);
x_32 = l_Lean_IR_EmitC_emitPartialApp(x_1, x_30, x_31, x_4, x_5);
return x_32;
}
case 8:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_2);
x_33 = lean_ctor_get(x_3, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_3, 1);
lean_inc(x_34);
lean_dec(x_3);
x_35 = l_Lean_IR_EmitC_emitApp(x_1, x_33, x_34, x_4, x_5);
lean_dec(x_34);
return x_35;
}
case 9:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_2);
x_36 = lean_ctor_get(x_3, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_3, 1);
lean_inc(x_37);
lean_dec(x_3);
x_38 = l_Lean_IR_EmitC_emitBox(x_1, x_37, x_36, x_4, x_5);
lean_dec(x_4);
lean_dec(x_36);
return x_38;
}
case 10:
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_3, 0);
lean_inc(x_39);
lean_dec(x_3);
x_40 = l_Lean_IR_EmitC_emitUnbox(x_1, x_2, x_39, x_4, x_5);
return x_40;
}
case 11:
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_3, 0);
lean_inc(x_41);
lean_dec(x_3);
x_42 = l_Lean_IR_EmitC_emitLit(x_1, x_2, x_41, x_4, x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_42;
}
case 12:
{
lean_object* x_43; lean_object* x_44; 
lean_dec(x_2);
x_43 = lean_ctor_get(x_3, 0);
lean_inc(x_43);
lean_dec(x_3);
x_44 = l_Lean_IR_EmitC_emitIsShared(x_1, x_43, x_4, x_5);
lean_dec(x_4);
return x_44;
}
default: 
{
lean_object* x_45; lean_object* x_46; 
lean_dec(x_2);
x_45 = lean_ctor_get(x_3, 0);
lean_inc(x_45);
lean_dec(x_3);
x_46 = l_Lean_IR_EmitC_emitIsTaggedPtr(x_1, x_45, x_4, x_5);
lean_dec(x_4);
return x_46;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_isTailCall(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_4, 3);
x_10 = lean_name_eq(x_7, x_9);
if (x_10 == 0)
{
uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_11 = 0;
x_12 = lean_box(x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_5);
return x_13;
}
else
{
uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_nat_dec_eq(x_1, x_8);
x_15 = lean_box(x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_5);
return x_16;
}
}
else
{
uint8_t x_17; lean_object* x_18; lean_object* x_19; 
x_17 = 0;
x_18 = lean_box(x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_5);
return x_19;
}
}
else
{
uint8_t x_20; lean_object* x_21; lean_object* x_22; 
x_20 = 0;
x_21 = lean_box(x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_5);
return x_22;
}
}
else
{
uint8_t x_23; lean_object* x_24; lean_object* x_25; 
x_23 = 0;
x_24 = lean_box(x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_5);
return x_25;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_isTailCall___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_EmitC_isTailCall(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_EmitC_paramEqArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_nat_dec_eq(x_4, x_3);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = 0;
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_paramEqArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_IR_EmitC_paramEqArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Nat_anyAux___at_Lean_IR_EmitC_overwriteParam___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_4, x_7);
lean_dec(x_4);
x_9 = lean_nat_add(x_8, x_7);
x_10 = lean_nat_sub(x_3, x_9);
lean_dec(x_9);
x_11 = l_Lean_IR_instInhabitedArg;
x_12 = lean_array_get(x_11, x_1, x_10);
lean_dec(x_10);
x_13 = l_Lean_IR_EmitC_paramEqArg(x_2, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
x_4 = x_8;
goto _start;
}
else
{
uint8_t x_15; 
lean_dec(x_8);
x_15 = 1;
return x_15;
}
}
else
{
uint8_t x_16; 
lean_dec(x_4);
x_16 = 0;
return x_16;
}
}
}
LEAN_EXPORT uint8_t l_Nat_anyAux___at_Lean_IR_EmitC_overwriteParam___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_5, x_8);
lean_dec(x_5);
x_10 = lean_nat_add(x_9, x_8);
x_11 = lean_nat_sub(x_4, x_10);
lean_dec(x_10);
x_12 = l_Lean_IR_instInhabitedParam;
x_13 = lean_array_get(x_12, x_1, x_11);
x_14 = lean_nat_add(x_11, x_8);
lean_dec(x_11);
x_15 = lean_nat_sub(x_3, x_14);
lean_dec(x_14);
x_16 = l_Nat_anyAux___at_Lean_IR_EmitC_overwriteParam___spec__1(x_2, x_13, x_3, x_15);
lean_dec(x_13);
if (x_16 == 0)
{
x_5 = x_9;
goto _start;
}
else
{
uint8_t x_18; 
lean_dec(x_9);
x_18 = 1;
return x_18;
}
}
else
{
uint8_t x_19; 
lean_dec(x_5);
x_19 = 0;
return x_19;
}
}
}
LEAN_EXPORT uint8_t l_Lean_IR_EmitC_overwriteParam(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_array_get_size(x_1);
lean_inc(x_3);
x_4 = l_Nat_anyAux___at_Lean_IR_EmitC_overwriteParam___spec__2(x_1, x_2, x_3, x_3, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Nat_anyAux___at_Lean_IR_EmitC_overwriteParam___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Nat_anyAux___at_Lean_IR_EmitC_overwriteParam___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Nat_anyAux___at_Lean_IR_EmitC_overwriteParam___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Nat_anyAux___at_Lean_IR_EmitC_overwriteParam___spec__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_overwriteParam___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_IR_EmitC_overwriteParam(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Nat_forM_loop___at_Lean_IR_EmitC_emitTailCall___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_eq(x_4, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_sub(x_4, x_9);
lean_dec(x_4);
x_11 = lean_nat_sub(x_3, x_10);
x_12 = lean_nat_sub(x_11, x_9);
lean_dec(x_11);
x_13 = l_Lean_IR_instInhabitedParam;
x_14 = lean_array_get(x_13, x_2, x_12);
x_15 = l_Lean_IR_instInhabitedArg;
x_16 = lean_array_get(x_15, x_1, x_12);
lean_dec(x_12);
x_17 = l_Lean_IR_EmitC_paramEqArg(x_14, x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_18 = lean_ctor_get(x_14, 0);
lean_inc(x_18);
lean_dec(x_14);
x_19 = l_Nat_repr(x_18);
x_20 = l_Lean_IR_EmitC_argToCString___closed__1;
x_21 = lean_string_append(x_20, x_19);
lean_dec(x_19);
x_22 = lean_string_append(x_6, x_21);
lean_dec(x_21);
x_23 = l_Nat_forM_loop___at_Lean_IR_EmitC_emitJmp___spec__1___closed__1;
x_24 = lean_string_append(x_22, x_23);
x_25 = l_Lean_IR_EmitC_emitArg(x_16, x_5, x_24);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = l_Lean_IR_EmitC_emitFnDeclAux___lambda__1___closed__1;
x_28 = lean_string_append(x_26, x_27);
x_29 = l_Lean_IR_EmitC_emitLn___rarg___closed__1;
x_30 = lean_string_append(x_28, x_29);
x_4 = x_10;
x_6 = x_30;
goto _start;
}
else
{
lean_dec(x_16);
lean_dec(x_14);
x_4 = x_10;
goto _start;
}
}
else
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_4);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_6);
return x_34;
}
}
}
static lean_object* _init_l_Nat_forM_loop___at_Lean_IR_EmitC_emitTailCall___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" _tmp_", 6);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Nat_forM_loop___at_Lean_IR_EmitC_emitTailCall___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_eq(x_4, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_sub(x_4, x_9);
lean_dec(x_4);
x_11 = lean_nat_sub(x_3, x_10);
x_12 = lean_nat_sub(x_11, x_9);
lean_dec(x_11);
x_13 = l_Lean_IR_instInhabitedParam;
x_14 = lean_array_get(x_13, x_2, x_12);
x_15 = l_Lean_IR_instInhabitedArg;
x_16 = lean_array_get(x_15, x_1, x_12);
x_17 = l_Lean_IR_EmitC_paramEqArg(x_14, x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_18 = lean_ctor_get(x_14, 1);
lean_inc(x_18);
lean_dec(x_14);
x_19 = l_Lean_IR_EmitC_toCType(x_18);
lean_dec(x_18);
x_20 = lean_string_append(x_6, x_19);
lean_dec(x_19);
x_21 = l_Nat_forM_loop___at_Lean_IR_EmitC_emitTailCall___spec__2___closed__1;
x_22 = lean_string_append(x_20, x_21);
x_23 = l_Nat_repr(x_12);
x_24 = lean_string_append(x_22, x_23);
lean_dec(x_23);
x_25 = l_Nat_forM_loop___at_Lean_IR_EmitC_emitJmp___spec__1___closed__1;
x_26 = lean_string_append(x_24, x_25);
x_27 = l_Lean_IR_EmitC_emitArg(x_16, x_5, x_26);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = l_Lean_IR_EmitC_emitFnDeclAux___lambda__1___closed__1;
x_30 = lean_string_append(x_28, x_29);
x_31 = l_Lean_IR_EmitC_emitLn___rarg___closed__1;
x_32 = lean_string_append(x_30, x_31);
x_4 = x_10;
x_6 = x_32;
goto _start;
}
else
{
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_12);
x_4 = x_10;
goto _start;
}
}
else
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_4);
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_6);
return x_36;
}
}
}
static lean_object* _init_l_Nat_forM_loop___at_Lean_IR_EmitC_emitTailCall___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" = _tmp_", 8);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Nat_forM_loop___at_Lean_IR_EmitC_emitTailCall___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_eq(x_4, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_sub(x_4, x_9);
lean_dec(x_4);
x_11 = lean_nat_sub(x_3, x_10);
x_12 = lean_nat_sub(x_11, x_9);
lean_dec(x_11);
x_13 = l_Lean_IR_instInhabitedParam;
x_14 = lean_array_get(x_13, x_2, x_12);
x_15 = l_Lean_IR_instInhabitedArg;
x_16 = lean_array_get(x_15, x_1, x_12);
x_17 = l_Lean_IR_EmitC_paramEqArg(x_14, x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_18 = lean_ctor_get(x_14, 0);
lean_inc(x_18);
lean_dec(x_14);
x_19 = l_Nat_repr(x_18);
x_20 = l_Lean_IR_EmitC_argToCString___closed__1;
x_21 = lean_string_append(x_20, x_19);
lean_dec(x_19);
x_22 = lean_string_append(x_6, x_21);
lean_dec(x_21);
x_23 = l_Nat_forM_loop___at_Lean_IR_EmitC_emitTailCall___spec__3___closed__1;
x_24 = lean_string_append(x_22, x_23);
x_25 = l_Nat_repr(x_12);
x_26 = lean_string_append(x_24, x_25);
lean_dec(x_25);
x_27 = l_Lean_IR_EmitC_emitFnDeclAux___lambda__1___closed__1;
x_28 = lean_string_append(x_26, x_27);
x_29 = l_Lean_IR_EmitC_emitLn___rarg___closed__1;
x_30 = lean_string_append(x_28, x_29);
x_4 = x_10;
x_6 = x_30;
goto _start;
}
else
{
lean_dec(x_14);
lean_dec(x_12);
x_4 = x_10;
goto _start;
}
}
else
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_4);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_6);
return x_34;
}
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitTailCall___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("goto _start;", 12);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitTailCall___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = l_Lean_IR_EmitC_emitTailCall___lambda__1___closed__1;
x_5 = lean_string_append(x_3, x_4);
x_6 = l_Lean_IR_EmitC_emitLn___rarg___closed__1;
x_7 = lean_string_append(x_5, x_6);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitTailCall___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_IR_EmitC_emitTailCall___lambda__1___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitTailCall___lambda__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("{", 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitTailCall___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = l_Lean_IR_EmitC_emitTailCall___lambda__2___closed__1;
x_7 = l_Lean_IR_EmitC_overwriteParam(x_1, x_2);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_array_get_size(x_2);
lean_inc(x_8);
x_9 = l_Nat_forM_loop___at_Lean_IR_EmitC_emitTailCall___spec__1(x_2, x_1, x_8, x_8, x_4, x_5);
lean_dec(x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_apply_3(x_6, x_10, x_4, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_13 = l_Lean_IR_EmitC_emitTailCall___lambda__2___closed__2;
x_14 = lean_string_append(x_5, x_13);
x_15 = l_Lean_IR_EmitC_emitLn___rarg___closed__1;
x_16 = lean_string_append(x_14, x_15);
x_17 = lean_array_get_size(x_1);
lean_inc(x_17);
x_18 = l_Nat_forM_loop___at_Lean_IR_EmitC_emitTailCall___spec__2(x_2, x_1, x_17, x_17, x_4, x_16);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
lean_inc(x_17);
x_20 = l_Nat_forM_loop___at_Lean_IR_EmitC_emitTailCall___spec__3(x_2, x_1, x_17, x_17, x_4, x_19);
lean_dec(x_17);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__1;
x_23 = lean_string_append(x_21, x_22);
x_24 = lean_string_append(x_23, x_15);
x_25 = lean_box(0);
x_26 = lean_apply_3(x_6, x_25, x_4, x_24);
return x_26;
}
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitTailCall___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("bug at emitTailCall", 19);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitTailCall___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("invalid tail call", 17);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitTailCall(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 6)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_2, 4);
lean_inc(x_5);
x_6 = lean_array_get_size(x_5);
x_7 = lean_array_get_size(x_4);
x_8 = lean_nat_dec_eq(x_6, x_7);
lean_dec(x_7);
lean_dec(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_9 = l_Lean_IR_EmitC_emitTailCall___closed__2;
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_3);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_box(0);
x_12 = l_Lean_IR_EmitC_emitTailCall___lambda__2(x_5, x_4, x_11, x_2, x_3);
lean_dec(x_4);
lean_dec(x_5);
return x_12;
}
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_2);
lean_dec(x_1);
x_13 = l_Lean_IR_EmitC_emitTailCall___closed__1;
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_3);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Nat_forM_loop___at_Lean_IR_EmitC_emitTailCall___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Nat_forM_loop___at_Lean_IR_EmitC_emitTailCall___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Nat_forM_loop___at_Lean_IR_EmitC_emitTailCall___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Nat_forM_loop___at_Lean_IR_EmitC_emitTailCall___spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Nat_forM_loop___at_Lean_IR_EmitC_emitTailCall___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Nat_forM_loop___at_Lean_IR_EmitC_emitTailCall___spec__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitTailCall___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_EmitC_emitTailCall___lambda__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitTailCall___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_EmitC_emitTailCall___lambda__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitIf___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("if (", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitIf___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" == ", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitIf___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("else", 4);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitIf(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_8 = l_Lean_IR_EmitC_emitIf___closed__1;
x_9 = lean_string_append(x_7, x_8);
x_10 = l_Lean_IR_EmitC_emitTag(x_1, x_2, x_6, x_9);
lean_dec(x_2);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = l_Lean_IR_EmitC_emitIf___closed__2;
x_13 = lean_string_append(x_11, x_12);
x_14 = l_Nat_repr(x_3);
x_15 = lean_string_append(x_13, x_14);
lean_dec(x_14);
x_16 = l_Lean_IR_EmitC_emitFnDeclAux___lambda__2___closed__1;
x_17 = lean_string_append(x_15, x_16);
x_18 = l_Lean_IR_EmitC_emitLn___rarg___closed__1;
x_19 = lean_string_append(x_17, x_18);
lean_inc(x_6);
x_20 = l_Lean_IR_EmitC_emitFnBody(x_4, x_6, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = l_Lean_IR_EmitC_emitIf___closed__3;
x_23 = lean_string_append(x_21, x_22);
x_24 = lean_string_append(x_23, x_18);
x_25 = l_Lean_IR_EmitC_emitFnBody(x_5, x_6, x_24);
return x_25;
}
else
{
uint8_t x_26; 
lean_dec(x_6);
lean_dec(x_5);
x_26 = !lean_is_exclusive(x_20);
if (x_26 == 0)
{
return x_20;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_20, 0);
x_28 = lean_ctor_get(x_20, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_20);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitFnBody___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_3);
lean_inc(x_1);
x_5 = l_Lean_IR_EmitC_emitBlock(x_1, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_Lean_IR_EmitC_emitJPs(x_1, x_3, x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_ctor_get(x_7, 1);
x_10 = lean_ctor_get(x_7, 0);
lean_dec(x_10);
x_11 = l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__1;
x_12 = lean_string_append(x_9, x_11);
x_13 = l_Lean_IR_EmitC_emitLn___rarg___closed__1;
x_14 = lean_string_append(x_12, x_13);
x_15 = lean_box(0);
lean_ctor_set(x_7, 1, x_14);
lean_ctor_set(x_7, 0, x_15);
return x_7;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_ctor_get(x_7, 1);
lean_inc(x_16);
lean_dec(x_7);
x_17 = l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__1;
x_18 = lean_string_append(x_16, x_17);
x_19 = l_Lean_IR_EmitC_emitLn___rarg___closed__1;
x_20 = lean_string_append(x_18, x_19);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_7);
if (x_23 == 0)
{
return x_7;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_7, 0);
x_25 = lean_ctor_get(x_7, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_7);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
else
{
uint8_t x_27; 
lean_dec(x_3);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_5);
if (x_27 == 0)
{
return x_5;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_5, 0);
x_29 = lean_ctor_get(x_5, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_5);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitFnBody(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_4 = l_Lean_IR_EmitC_emitTailCall___lambda__2___closed__2;
x_5 = lean_string_append(x_3, x_4);
x_6 = l_Lean_IR_EmitC_emitLn___rarg___closed__1;
x_7 = lean_string_append(x_5, x_6);
x_8 = 0;
lean_inc(x_2);
lean_inc(x_1);
x_9 = l_Lean_IR_EmitC_declareVars(x_1, x_8, x_2, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_unbox(x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec(x_9);
x_13 = lean_box(0);
x_14 = l_Lean_IR_EmitC_emitFnBody___lambda__1(x_1, x_13, x_2, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_9, 1);
lean_inc(x_15);
lean_dec(x_9);
x_16 = l_Array_foldlMUnsafe_fold___at_Lean_IR_EmitC_emitFileHeader___spec__1___closed__1;
x_17 = lean_string_append(x_15, x_16);
x_18 = lean_string_append(x_17, x_6);
x_19 = lean_box(0);
x_20 = l_Lean_IR_EmitC_emitFnBody___lambda__1(x_1, x_19, x_2, x_18);
return x_20;
}
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitJPs___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(":", 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitJPs(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 3);
lean_inc(x_6);
lean_dec(x_1);
x_7 = l_Nat_repr(x_4);
x_8 = l_Lean_IR_EmitC_emitJmp___lambda__1___closed__2;
x_9 = lean_string_append(x_8, x_7);
lean_dec(x_7);
x_10 = lean_string_append(x_3, x_9);
lean_dec(x_9);
x_11 = l_Lean_IR_EmitC_emitJPs___closed__1;
x_12 = lean_string_append(x_10, x_11);
x_13 = l_Lean_IR_EmitC_emitLn___rarg___closed__1;
x_14 = lean_string_append(x_12, x_13);
lean_inc(x_2);
x_15 = l_Lean_IR_EmitC_emitFnBody(x_5, x_2, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_1 = x_6;
x_3 = x_16;
goto _start;
}
else
{
uint8_t x_18; 
lean_dec(x_6);
lean_dec(x_2);
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_15);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
else
{
uint8_t x_22; 
x_22 = l_Lean_IR_FnBody_isTerminal(x_1);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = l_Lean_IR_FnBody_body(x_1);
lean_dec(x_1);
x_1 = x_23;
goto _start;
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_2);
lean_dec(x_1);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_3);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitBlock___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_dec(x_2);
x_5 = l_Lean_IR_EmitC_emitBlock(x_1, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitBlock___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("return ", 7);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitBlock___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("lean_internal_panic_unreachable();", 34);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitBlock(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 3);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 3);
lean_inc(x_8);
x_9 = l_Lean_IR_isTailCallTo(x_8, x_1);
lean_dec(x_1);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_inc(x_2);
x_10 = l_Lean_IR_EmitC_emitVDecl(x_4, x_5, x_6, x_2, x_3);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_1 = x_7;
x_3 = x_11;
goto _start;
}
else
{
uint8_t x_13; 
lean_dec(x_7);
lean_dec(x_2);
x_13 = !lean_is_exclusive(x_10);
if (x_13 == 0)
{
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_10, 0);
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_10);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
else
{
lean_object* x_17; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_17 = l_Lean_IR_EmitC_emitTailCall(x_6, x_2, x_3);
return x_17;
}
}
case 1:
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_1, 3);
lean_inc(x_18);
lean_dec(x_1);
x_1 = x_18;
goto _start;
}
case 2:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
x_22 = lean_ctor_get(x_1, 2);
lean_inc(x_22);
x_23 = lean_ctor_get(x_1, 3);
lean_inc(x_23);
lean_dec(x_1);
x_24 = l_Lean_IR_EmitC_emitSet(x_20, x_21, x_22, x_2, x_3);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_1 = x_23;
x_3 = x_25;
goto _start;
}
case 3:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = lean_ctor_get(x_1, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_1, 1);
lean_inc(x_28);
x_29 = lean_ctor_get(x_1, 2);
lean_inc(x_29);
lean_dec(x_1);
x_30 = l_Lean_IR_EmitC_emitSetTag(x_27, x_28, x_2, x_3);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec(x_30);
x_1 = x_29;
x_3 = x_31;
goto _start;
}
case 4:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_33 = lean_ctor_get(x_1, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_1, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_1, 2);
lean_inc(x_35);
x_36 = lean_ctor_get(x_1, 3);
lean_inc(x_36);
lean_dec(x_1);
x_37 = l_Lean_IR_EmitC_emitUSet(x_33, x_34, x_35, x_2, x_3);
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
lean_dec(x_37);
x_1 = x_36;
x_3 = x_38;
goto _start;
}
case 5:
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_40 = lean_ctor_get(x_1, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_1, 1);
lean_inc(x_41);
x_42 = lean_ctor_get(x_1, 2);
lean_inc(x_42);
x_43 = lean_ctor_get(x_1, 3);
lean_inc(x_43);
x_44 = lean_ctor_get(x_1, 4);
lean_inc(x_44);
x_45 = lean_ctor_get(x_1, 5);
lean_inc(x_45);
lean_dec(x_1);
x_46 = l_Lean_IR_EmitC_emitSSet(x_40, x_41, x_42, x_43, x_44, x_2, x_3);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
lean_dec(x_46);
x_1 = x_45;
x_3 = x_47;
goto _start;
}
else
{
uint8_t x_49; 
lean_dec(x_45);
lean_dec(x_2);
x_49 = !lean_is_exclusive(x_46);
if (x_49 == 0)
{
return x_46;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_46, 0);
x_51 = lean_ctor_get(x_46, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_46);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
case 6:
{
uint8_t x_53; 
x_53 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 1);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; 
x_54 = lean_ctor_get(x_1, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_1, 1);
lean_inc(x_55);
x_56 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
x_57 = lean_ctor_get(x_1, 2);
lean_inc(x_57);
lean_dec(x_1);
lean_inc(x_2);
x_58 = l_Lean_IR_EmitC_emitInc(x_54, x_55, x_56, x_2, x_3);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; 
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec(x_58);
x_1 = x_57;
x_3 = x_59;
goto _start;
}
else
{
uint8_t x_61; 
lean_dec(x_57);
lean_dec(x_2);
x_61 = !lean_is_exclusive(x_58);
if (x_61 == 0)
{
return x_58;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_58, 0);
x_63 = lean_ctor_get(x_58, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_58);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
else
{
lean_object* x_65; 
x_65 = lean_ctor_get(x_1, 2);
lean_inc(x_65);
lean_dec(x_1);
x_1 = x_65;
goto _start;
}
}
case 7:
{
uint8_t x_67; 
x_67 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 1);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; uint8_t x_70; lean_object* x_71; lean_object* x_72; 
x_68 = lean_ctor_get(x_1, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_1, 1);
lean_inc(x_69);
x_70 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
x_71 = lean_ctor_get(x_1, 2);
lean_inc(x_71);
lean_dec(x_1);
lean_inc(x_2);
x_72 = l_Lean_IR_EmitC_emitDec(x_68, x_69, x_70, x_2, x_3);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; 
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
lean_dec(x_72);
x_1 = x_71;
x_3 = x_73;
goto _start;
}
else
{
uint8_t x_75; 
lean_dec(x_71);
lean_dec(x_2);
x_75 = !lean_is_exclusive(x_72);
if (x_75 == 0)
{
return x_72;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_72, 0);
x_77 = lean_ctor_get(x_72, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_72);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
}
else
{
lean_object* x_79; 
x_79 = lean_ctor_get(x_1, 2);
lean_inc(x_79);
lean_dec(x_1);
x_1 = x_79;
goto _start;
}
}
case 8:
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_81 = lean_ctor_get(x_1, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_1, 1);
lean_inc(x_82);
lean_dec(x_1);
x_83 = l_Lean_IR_EmitC_emitDel(x_81, x_2, x_3);
x_84 = lean_ctor_get(x_83, 1);
lean_inc(x_84);
lean_dec(x_83);
x_1 = x_82;
x_3 = x_84;
goto _start;
}
case 9:
{
lean_object* x_86; 
x_86 = lean_ctor_get(x_1, 1);
lean_inc(x_86);
lean_dec(x_1);
x_1 = x_86;
goto _start;
}
case 10:
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_88 = lean_ctor_get(x_1, 1);
lean_inc(x_88);
x_89 = lean_ctor_get(x_1, 2);
lean_inc(x_89);
x_90 = lean_ctor_get(x_1, 3);
lean_inc(x_90);
lean_dec(x_1);
x_91 = l_Lean_IR_EmitC_emitCase(x_88, x_89, x_90, x_2, x_3);
return x_91;
}
case 11:
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; 
x_92 = lean_ctor_get(x_1, 0);
lean_inc(x_92);
lean_dec(x_1);
x_93 = l_Lean_IR_EmitC_emitBlock___closed__1;
x_94 = lean_string_append(x_3, x_93);
x_95 = l_Lean_IR_EmitC_emitArg(x_92, x_2, x_94);
lean_dec(x_2);
x_96 = !lean_is_exclusive(x_95);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_97 = lean_ctor_get(x_95, 1);
x_98 = lean_ctor_get(x_95, 0);
lean_dec(x_98);
x_99 = l_Lean_IR_EmitC_emitFnDeclAux___lambda__1___closed__1;
x_100 = lean_string_append(x_97, x_99);
x_101 = l_Lean_IR_EmitC_emitLn___rarg___closed__1;
x_102 = lean_string_append(x_100, x_101);
x_103 = lean_box(0);
lean_ctor_set(x_95, 1, x_102);
lean_ctor_set(x_95, 0, x_103);
return x_95;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_104 = lean_ctor_get(x_95, 1);
lean_inc(x_104);
lean_dec(x_95);
x_105 = l_Lean_IR_EmitC_emitFnDeclAux___lambda__1___closed__1;
x_106 = lean_string_append(x_104, x_105);
x_107 = l_Lean_IR_EmitC_emitLn___rarg___closed__1;
x_108 = lean_string_append(x_106, x_107);
x_109 = lean_box(0);
x_110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_108);
return x_110;
}
}
case 12:
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_1, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_1, 1);
lean_inc(x_112);
lean_dec(x_1);
x_113 = l_Lean_IR_EmitC_emitJmp(x_111, x_112, x_2, x_3);
return x_113;
}
default: 
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
lean_dec(x_2);
x_114 = l_Lean_IR_EmitC_emitBlock___closed__2;
x_115 = lean_string_append(x_3, x_114);
x_116 = l_Lean_IR_EmitC_emitLn___rarg___closed__1;
x_117 = lean_string_append(x_115, x_116);
x_118 = lean_box(0);
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_117);
return x_119;
}
}
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lean_IR_EmitC_emitCase___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("case ", 5);
return x_1;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lean_IR_EmitC_emitCase___spec__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("default: ", 9);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_EmitC_emitCase___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_2, x_3);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_4);
x_8 = lean_array_uget(x_1, x_2);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Array_foldlMUnsafe_fold___at_Lean_IR_EmitC_emitCase___spec__1___closed__1;
x_12 = lean_string_append(x_6, x_11);
x_13 = lean_ctor_get(x_9, 1);
lean_inc(x_13);
lean_dec(x_9);
x_14 = l_Nat_repr(x_13);
x_15 = lean_string_append(x_12, x_14);
lean_dec(x_14);
x_16 = l_Lean_IR_EmitC_emitJPs___closed__1;
x_17 = lean_string_append(x_15, x_16);
x_18 = l_Lean_IR_EmitC_emitLn___rarg___closed__1;
x_19 = lean_string_append(x_17, x_18);
lean_inc(x_5);
x_20 = l_Lean_IR_EmitC_emitFnBody(x_10, x_5, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = 1;
x_24 = lean_usize_add(x_2, x_23);
x_2 = x_24;
x_4 = x_21;
x_6 = x_22;
goto _start;
}
else
{
uint8_t x_26; 
lean_dec(x_5);
x_26 = !lean_is_exclusive(x_20);
if (x_26 == 0)
{
return x_20;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_20, 0);
x_28 = lean_ctor_get(x_20, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_20);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_30 = lean_ctor_get(x_8, 0);
lean_inc(x_30);
lean_dec(x_8);
x_31 = l_Array_foldlMUnsafe_fold___at_Lean_IR_EmitC_emitCase___spec__1___closed__2;
x_32 = lean_string_append(x_6, x_31);
x_33 = l_Lean_IR_EmitC_emitLn___rarg___closed__1;
x_34 = lean_string_append(x_32, x_33);
lean_inc(x_5);
x_35 = l_Lean_IR_EmitC_emitFnBody(x_30, x_5, x_34);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; size_t x_38; size_t x_39; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = 1;
x_39 = lean_usize_add(x_2, x_38);
x_2 = x_39;
x_4 = x_36;
x_6 = x_37;
goto _start;
}
else
{
uint8_t x_41; 
lean_dec(x_5);
x_41 = !lean_is_exclusive(x_35);
if (x_41 == 0)
{
return x_35;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_35, 0);
x_43 = lean_ctor_get(x_35, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_35);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
}
else
{
lean_object* x_45; 
lean_dec(x_5);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_4);
lean_ctor_set(x_45, 1, x_6);
return x_45;
}
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitCase___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("switch (", 8);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitCase___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(") {", 3);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitCase(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_EmitC_isIf(x_3);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = l_Lean_IR_EmitC_emitCase___closed__1;
x_8 = lean_string_append(x_5, x_7);
x_9 = l_Lean_IR_EmitC_emitTag(x_1, x_2, x_4, x_8);
lean_dec(x_2);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_11 = lean_ctor_get(x_9, 1);
x_12 = lean_ctor_get(x_9, 0);
lean_dec(x_12);
x_13 = l_Lean_IR_EmitC_emitCase___closed__2;
x_14 = lean_string_append(x_11, x_13);
x_15 = l_Lean_IR_EmitC_emitLn___rarg___closed__1;
x_16 = lean_string_append(x_14, x_15);
x_17 = l_Lean_IR_ensureHasDefault(x_3);
x_18 = lean_array_get_size(x_17);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_nat_dec_lt(x_19, x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_4);
x_21 = l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__1;
x_22 = lean_string_append(x_16, x_21);
x_23 = lean_string_append(x_22, x_15);
x_24 = lean_box(0);
lean_ctor_set(x_9, 1, x_23);
lean_ctor_set(x_9, 0, x_24);
return x_9;
}
else
{
uint8_t x_25; 
x_25 = lean_nat_dec_le(x_18, x_18);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_4);
x_26 = l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__1;
x_27 = lean_string_append(x_16, x_26);
x_28 = lean_string_append(x_27, x_15);
x_29 = lean_box(0);
lean_ctor_set(x_9, 1, x_28);
lean_ctor_set(x_9, 0, x_29);
return x_9;
}
else
{
size_t x_30; size_t x_31; lean_object* x_32; lean_object* x_33; 
lean_free_object(x_9);
x_30 = 0;
x_31 = lean_usize_of_nat(x_18);
lean_dec(x_18);
x_32 = lean_box(0);
x_33 = l_Array_foldlMUnsafe_fold___at_Lean_IR_EmitC_emitCase___spec__1(x_17, x_30, x_31, x_32, x_4, x_16);
lean_dec(x_17);
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_33, 1);
x_36 = lean_ctor_get(x_33, 0);
lean_dec(x_36);
x_37 = l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__1;
x_38 = lean_string_append(x_35, x_37);
x_39 = lean_string_append(x_38, x_15);
lean_ctor_set(x_33, 1, x_39);
lean_ctor_set(x_33, 0, x_32);
return x_33;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_40 = lean_ctor_get(x_33, 1);
lean_inc(x_40);
lean_dec(x_33);
x_41 = l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__1;
x_42 = lean_string_append(x_40, x_41);
x_43 = lean_string_append(x_42, x_15);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_32);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
else
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_33);
if (x_45 == 0)
{
return x_33;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_33, 0);
x_47 = lean_ctor_get(x_33, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_33);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_49 = lean_ctor_get(x_9, 1);
lean_inc(x_49);
lean_dec(x_9);
x_50 = l_Lean_IR_EmitC_emitCase___closed__2;
x_51 = lean_string_append(x_49, x_50);
x_52 = l_Lean_IR_EmitC_emitLn___rarg___closed__1;
x_53 = lean_string_append(x_51, x_52);
x_54 = l_Lean_IR_ensureHasDefault(x_3);
x_55 = lean_array_get_size(x_54);
x_56 = lean_unsigned_to_nat(0u);
x_57 = lean_nat_dec_lt(x_56, x_55);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_4);
x_58 = l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__1;
x_59 = lean_string_append(x_53, x_58);
x_60 = lean_string_append(x_59, x_52);
x_61 = lean_box(0);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_60);
return x_62;
}
else
{
uint8_t x_63; 
x_63 = lean_nat_dec_le(x_55, x_55);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_4);
x_64 = l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__1;
x_65 = lean_string_append(x_53, x_64);
x_66 = lean_string_append(x_65, x_52);
x_67 = lean_box(0);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_66);
return x_68;
}
else
{
size_t x_69; size_t x_70; lean_object* x_71; lean_object* x_72; 
x_69 = 0;
x_70 = lean_usize_of_nat(x_55);
lean_dec(x_55);
x_71 = lean_box(0);
x_72 = l_Array_foldlMUnsafe_fold___at_Lean_IR_EmitC_emitCase___spec__1(x_54, x_69, x_70, x_71, x_4, x_53);
lean_dec(x_54);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_74 = x_72;
} else {
 lean_dec_ref(x_72);
 x_74 = lean_box(0);
}
x_75 = l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__1;
x_76 = lean_string_append(x_73, x_75);
x_77 = lean_string_append(x_76, x_52);
if (lean_is_scalar(x_74)) {
 x_78 = lean_alloc_ctor(0, 2, 0);
} else {
 x_78 = x_74;
}
lean_ctor_set(x_78, 0, x_71);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_79 = lean_ctor_get(x_72, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_72, 1);
lean_inc(x_80);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_81 = x_72;
} else {
 lean_dec_ref(x_72);
 x_81 = lean_box(0);
}
if (lean_is_scalar(x_81)) {
 x_82 = lean_alloc_ctor(1, 2, 0);
} else {
 x_82 = x_81;
}
lean_ctor_set(x_82, 0, x_79);
lean_ctor_set(x_82, 1, x_80);
return x_82;
}
}
}
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_dec(x_3);
x_83 = lean_ctor_get(x_6, 0);
lean_inc(x_83);
lean_dec(x_6);
x_84 = lean_ctor_get(x_83, 1);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 0);
lean_inc(x_85);
lean_dec(x_83);
x_86 = lean_ctor_get(x_84, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_84, 1);
lean_inc(x_87);
lean_dec(x_84);
x_88 = l_Lean_IR_EmitC_emitIf(x_1, x_2, x_85, x_86, x_87, x_4, x_5);
return x_88;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitFnBody___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_EmitC_emitFnBody___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_EmitC_emitCase___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l_Array_foldlMUnsafe_fold___at_Lean_IR_EmitC_emitCase___spec__1(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec(x_1);
return x_9;
}
}
static lean_object* _init_l_Nat_forM_loop___at_Lean_IR_EmitC_emitDeclAux___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("lean_object* ", 13);
return x_1;
}
}
static lean_object* _init_l_Nat_forM_loop___at_Lean_IR_EmitC_emitDeclAux___spec__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" = _args[", 9);
return x_1;
}
}
static lean_object* _init_l_Nat_forM_loop___at_Lean_IR_EmitC_emitDeclAux___spec__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("];", 2);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Nat_forM_loop___at_Lean_IR_EmitC_emitDeclAux___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_3, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_3, x_8);
lean_dec(x_3);
x_10 = lean_nat_sub(x_2, x_9);
x_11 = lean_nat_sub(x_10, x_8);
lean_dec(x_10);
x_12 = l_Lean_IR_instInhabitedParam;
x_13 = lean_array_get(x_12, x_1, x_11);
x_14 = l_Nat_forM_loop___at_Lean_IR_EmitC_emitDeclAux___spec__1___closed__1;
x_15 = lean_string_append(x_5, x_14);
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_16);
lean_dec(x_13);
x_17 = l_Nat_repr(x_16);
x_18 = l_Lean_IR_EmitC_argToCString___closed__1;
x_19 = lean_string_append(x_18, x_17);
lean_dec(x_17);
x_20 = lean_string_append(x_15, x_19);
lean_dec(x_19);
x_21 = l_Nat_forM_loop___at_Lean_IR_EmitC_emitDeclAux___spec__1___closed__2;
x_22 = lean_string_append(x_20, x_21);
x_23 = l_Nat_repr(x_11);
x_24 = lean_string_append(x_22, x_23);
lean_dec(x_23);
x_25 = l_Nat_forM_loop___at_Lean_IR_EmitC_emitDeclAux___spec__1___closed__3;
x_26 = lean_string_append(x_24, x_25);
x_27 = l_Lean_IR_EmitC_emitLn___rarg___closed__1;
x_28 = lean_string_append(x_26, x_27);
x_3 = x_9;
x_5 = x_28;
goto _start;
}
else
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_3);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_5);
return x_31;
}
}
}
LEAN_EXPORT lean_object* l_Nat_forM_loop___at_Lean_IR_EmitC_emitDeclAux___spec__2___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_6 = l_Lean_IR_instInhabitedParam;
x_7 = lean_array_get(x_6, x_1, x_2);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
x_9 = l_Lean_IR_EmitC_toCType(x_8);
lean_dec(x_8);
x_10 = lean_string_append(x_5, x_9);
lean_dec(x_9);
x_11 = l_Lean_IR_EmitC_emitFnDeclAux___lambda__3___closed__1;
x_12 = lean_string_append(x_10, x_11);
x_13 = lean_ctor_get(x_7, 0);
lean_inc(x_13);
lean_dec(x_7);
x_14 = l_Nat_repr(x_13);
x_15 = l_Lean_IR_EmitC_argToCString___closed__1;
x_16 = lean_string_append(x_15, x_14);
lean_dec(x_14);
x_17 = lean_string_append(x_12, x_16);
lean_dec(x_16);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Nat_forM_loop___at_Lean_IR_EmitC_emitDeclAux___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_3, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_3, x_8);
lean_dec(x_3);
x_10 = lean_nat_sub(x_2, x_9);
x_11 = lean_nat_sub(x_10, x_8);
lean_dec(x_10);
x_12 = lean_nat_dec_lt(x_6, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_box(0);
x_14 = l_Nat_forM_loop___at_Lean_IR_EmitC_emitDeclAux___spec__2___lambda__1(x_1, x_11, x_13, x_4, x_5);
lean_dec(x_11);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_3 = x_9;
x_5 = x_15;
goto _start;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = l_Nat_forM_loop___at_Lean_IR_EmitC_emitFnDeclAux___spec__1___closed__1;
x_18 = lean_string_append(x_5, x_17);
x_19 = lean_box(0);
x_20 = l_Nat_forM_loop___at_Lean_IR_EmitC_emitDeclAux___spec__2___lambda__1(x_1, x_11, x_19, x_4, x_18);
lean_dec(x_11);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_3 = x_9;
x_5 = x_21;
goto _start;
}
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_3);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_5);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Nat_forM_loop___at_Lean_IR_EmitC_emitDeclAux___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_3, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_3, x_8);
lean_dec(x_3);
x_10 = lean_nat_sub(x_2, x_9);
x_11 = lean_nat_sub(x_10, x_8);
lean_dec(x_10);
x_12 = lean_nat_dec_lt(x_6, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_box(0);
x_14 = l_Nat_forM_loop___at_Lean_IR_EmitC_emitDeclAux___spec__2___lambda__1(x_1, x_11, x_13, x_4, x_5);
lean_dec(x_11);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_3 = x_9;
x_5 = x_15;
goto _start;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = l_Nat_forM_loop___at_Lean_IR_EmitC_emitFnDeclAux___spec__1___closed__1;
x_18 = lean_string_append(x_5, x_17);
x_19 = lean_box(0);
x_20 = l_Nat_forM_loop___at_Lean_IR_EmitC_emitDeclAux___spec__2___lambda__1(x_1, x_11, x_19, x_4, x_18);
lean_dec(x_11);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_3 = x_9;
x_5 = x_21;
goto _start;
}
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_3);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_5);
return x_24;
}
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitDeclAux___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_start:", 7);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitDeclAux___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = l_Lean_IR_EmitC_emitDeclAux___lambda__1___closed__1;
x_8 = lean_string_append(x_6, x_7);
x_9 = l_Lean_IR_EmitC_emitLn___rarg___closed__1;
x_10 = lean_string_append(x_8, x_9);
x_11 = !lean_is_exclusive(x_5);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_5, 4);
lean_dec(x_12);
x_13 = lean_ctor_get(x_5, 3);
lean_dec(x_13);
lean_ctor_set(x_5, 4, x_2);
lean_ctor_set(x_5, 3, x_1);
x_14 = l_Lean_IR_EmitC_emitFnBody(x_3, x_5, x_10);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_14, 1);
x_17 = lean_ctor_get(x_14, 0);
lean_dec(x_17);
x_18 = l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__1;
x_19 = lean_string_append(x_16, x_18);
x_20 = lean_string_append(x_19, x_9);
x_21 = lean_box(0);
lean_ctor_set(x_14, 1, x_20);
lean_ctor_set(x_14, 0, x_21);
return x_14;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_ctor_get(x_14, 1);
lean_inc(x_22);
lean_dec(x_14);
x_23 = l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__1;
x_24 = lean_string_append(x_22, x_23);
x_25 = lean_string_append(x_24, x_9);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
else
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_14);
if (x_28 == 0)
{
return x_14;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_14, 0);
x_30 = lean_ctor_get(x_14, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_14);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_32 = lean_ctor_get(x_5, 0);
x_33 = lean_ctor_get(x_5, 1);
x_34 = lean_ctor_get(x_5, 2);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_5);
x_35 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_33);
lean_ctor_set(x_35, 2, x_34);
lean_ctor_set(x_35, 3, x_1);
lean_ctor_set(x_35, 4, x_2);
x_36 = l_Lean_IR_EmitC_emitFnBody(x_3, x_35, x_10);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_38 = x_36;
} else {
 lean_dec_ref(x_36);
 x_38 = lean_box(0);
}
x_39 = l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__1;
x_40 = lean_string_append(x_37, x_39);
x_41 = lean_string_append(x_40, x_9);
x_42 = lean_box(0);
if (lean_is_scalar(x_38)) {
 x_43 = lean_alloc_ctor(0, 2, 0);
} else {
 x_43 = x_38;
}
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_41);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_44 = lean_ctor_get(x_36, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_36, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_46 = x_36;
} else {
 lean_dec_ref(x_36);
 x_46 = lean_box(0);
}
if (lean_is_scalar(x_46)) {
 x_47 = lean_alloc_ctor(1, 2, 0);
} else {
 x_47 = x_46;
}
lean_ctor_set(x_47, 0, x_44);
lean_ctor_set(x_47, 1, x_45);
return x_47;
}
}
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitDeclAux___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" {", 2);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitDeclAux___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
lean_dec(x_5);
x_8 = l_Lean_IR_EmitC_emitDeclAux___lambda__2___closed__1;
x_9 = lean_string_append(x_7, x_8);
x_10 = l_Lean_IR_EmitC_emitLn___rarg___closed__1;
x_11 = lean_string_append(x_9, x_10);
x_12 = lean_array_get_size(x_2);
x_13 = l_Lean_closureMaxArgs;
x_14 = lean_nat_dec_lt(x_13, x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_12);
lean_dec(x_4);
x_15 = lean_box(0);
x_16 = l_Lean_IR_EmitC_emitDeclAux___lambda__1(x_1, x_2, x_3, x_15, x_6, x_11);
return x_16;
}
else
{
uint8_t x_17; 
x_17 = l_Lean_IR_ExplicitBoxing_isBoxedName(x_4);
lean_dec(x_4);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_12);
x_18 = lean_box(0);
x_19 = l_Lean_IR_EmitC_emitDeclAux___lambda__1(x_1, x_2, x_3, x_18, x_6, x_11);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_inc(x_12);
x_20 = l_Nat_forM_loop___at_Lean_IR_EmitC_emitDeclAux___spec__1(x_2, x_12, x_12, x_6, x_11);
lean_dec(x_12);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_IR_EmitC_emitDeclAux___lambda__1(x_1, x_2, x_3, x_21, x_6, x_22);
lean_dec(x_21);
return x_23;
}
}
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitDeclAux___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("()", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitDeclAux___lambda__3___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("lean_object** _args", 19);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitDeclAux___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
lean_dec(x_7);
x_10 = l_Lean_IR_EmitC_toCType(x_1);
lean_dec(x_1);
x_11 = lean_string_append(x_9, x_10);
lean_dec(x_10);
x_12 = l_Lean_IR_EmitC_emitFnDeclAux___lambda__3___closed__1;
x_13 = lean_string_append(x_11, x_12);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_14 = lean_alloc_closure((void*)(l_Lean_IR_EmitC_emitDeclAux___lambda__2), 7, 4);
lean_closure_set(x_14, 0, x_2);
lean_closure_set(x_14, 1, x_3);
lean_closure_set(x_14, 2, x_4);
lean_closure_set(x_14, 3, x_5);
x_15 = lean_array_get_size(x_3);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_nat_dec_lt(x_16, x_15);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_15);
lean_dec(x_14);
x_18 = l_Lean_IR_EmitC_toCInitName___closed__1;
x_19 = lean_string_append(x_18, x_6);
lean_dec(x_6);
x_20 = l_Lean_IR_EmitC_emitDeclAux___lambda__3___closed__1;
x_21 = lean_string_append(x_19, x_20);
x_22 = lean_string_append(x_13, x_21);
lean_dec(x_21);
x_23 = lean_box(0);
x_24 = l_Lean_IR_EmitC_emitDeclAux___lambda__2(x_2, x_3, x_4, x_5, x_23, x_8, x_22);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
lean_dec(x_4);
lean_dec(x_2);
x_25 = lean_string_append(x_13, x_6);
lean_dec(x_6);
x_26 = l_Lean_IR_EmitC_emitFnDeclAux___lambda__3___closed__3;
x_27 = lean_string_append(x_25, x_26);
x_28 = l_Lean_closureMaxArgs;
x_29 = lean_nat_dec_lt(x_28, x_15);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_5);
lean_inc(x_15);
x_30 = l_Nat_forM_loop___at_Lean_IR_EmitC_emitDeclAux___spec__2(x_3, x_15, x_15, x_8, x_27);
lean_dec(x_15);
lean_dec(x_3);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l_Lean_IR_EmitC_emitFnDeclAux___lambda__2(x_14, x_31, x_8, x_32);
lean_dec(x_31);
return x_33;
}
else
{
uint8_t x_34; 
x_34 = l_Lean_IR_ExplicitBoxing_isBoxedName(x_5);
lean_dec(x_5);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_inc(x_15);
x_35 = l_Nat_forM_loop___at_Lean_IR_EmitC_emitDeclAux___spec__3(x_3, x_15, x_15, x_8, x_27);
lean_dec(x_15);
lean_dec(x_3);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = l_Lean_IR_EmitC_emitFnDeclAux___lambda__2(x_14, x_36, x_8, x_37);
lean_dec(x_36);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_15);
lean_dec(x_3);
x_39 = l_Lean_IR_EmitC_emitDeclAux___lambda__3___closed__2;
x_40 = lean_string_append(x_27, x_39);
x_41 = lean_box(0);
x_42 = l_Lean_IR_EmitC_emitFnDeclAux___lambda__2(x_14, x_41, x_8, x_40);
return x_42;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitDeclAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_12; 
x_4 = l_Lean_IR_EmitC_getEnv(x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_7 = x_4;
} else {
 lean_dec_ref(x_4);
 x_7 = lean_box(0);
}
lean_inc(x_1);
x_8 = l_Lean_IR_mkVarJPMaps(x_1);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = l_Lean_IR_Decl_name(x_1);
lean_inc(x_10);
x_11 = l_Lean_hasInitAttr(x_5, x_10);
if (x_11 == 0)
{
uint8_t x_65; 
x_65 = 0;
x_12 = x_65;
goto block_64;
}
else
{
uint8_t x_66; 
x_66 = 1;
x_12 = x_66;
goto block_64;
}
block_64:
{
if (x_12 == 0)
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
lean_dec(x_7);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 2);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 3);
lean_inc(x_16);
lean_dec(x_1);
x_17 = !lean_is_exclusive(x_2);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_2, 2);
lean_dec(x_18);
lean_ctor_set(x_2, 2, x_9);
lean_inc(x_13);
x_19 = l_Lean_IR_EmitC_toCName(x_13, x_2, x_6);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_array_get_size(x_14);
x_23 = lean_unsigned_to_nat(0u);
x_24 = lean_nat_dec_eq(x_22, x_23);
lean_dec(x_22);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = l_Lean_IR_EmitC_emitFnDeclAux___closed__1;
x_26 = lean_string_append(x_21, x_25);
x_27 = lean_box(0);
x_28 = l_Lean_IR_EmitC_emitDeclAux___lambda__3(x_15, x_13, x_14, x_16, x_10, x_20, x_27, x_2, x_26);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = l_Lean_IR_EmitC_emitFnDeclAux___closed__3;
x_30 = lean_string_append(x_21, x_29);
x_31 = lean_box(0);
x_32 = l_Lean_IR_EmitC_emitDeclAux___lambda__3(x_15, x_13, x_14, x_16, x_10, x_20, x_31, x_2, x_30);
return x_32;
}
}
else
{
uint8_t x_33; 
lean_dec(x_2);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_10);
x_33 = !lean_is_exclusive(x_19);
if (x_33 == 0)
{
return x_19;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_19, 0);
x_35 = lean_ctor_get(x_19, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_19);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_37 = lean_ctor_get(x_2, 0);
x_38 = lean_ctor_get(x_2, 1);
x_39 = lean_ctor_get(x_2, 3);
x_40 = lean_ctor_get(x_2, 4);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_2);
x_41 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_41, 0, x_37);
lean_ctor_set(x_41, 1, x_38);
lean_ctor_set(x_41, 2, x_9);
lean_ctor_set(x_41, 3, x_39);
lean_ctor_set(x_41, 4, x_40);
lean_inc(x_13);
x_42 = l_Lean_IR_EmitC_toCName(x_13, x_41, x_6);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_array_get_size(x_14);
x_46 = lean_unsigned_to_nat(0u);
x_47 = lean_nat_dec_eq(x_45, x_46);
lean_dec(x_45);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_48 = l_Lean_IR_EmitC_emitFnDeclAux___closed__1;
x_49 = lean_string_append(x_44, x_48);
x_50 = lean_box(0);
x_51 = l_Lean_IR_EmitC_emitDeclAux___lambda__3(x_15, x_13, x_14, x_16, x_10, x_43, x_50, x_41, x_49);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_52 = l_Lean_IR_EmitC_emitFnDeclAux___closed__3;
x_53 = lean_string_append(x_44, x_52);
x_54 = lean_box(0);
x_55 = l_Lean_IR_EmitC_emitDeclAux___lambda__3(x_15, x_13, x_14, x_16, x_10, x_43, x_54, x_41, x_53);
return x_55;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_41);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_10);
x_56 = lean_ctor_get(x_42, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_42, 1);
lean_inc(x_57);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_58 = x_42;
} else {
 lean_dec_ref(x_42);
 x_58 = lean_box(0);
}
if (lean_is_scalar(x_58)) {
 x_59 = lean_alloc_ctor(1, 2, 0);
} else {
 x_59 = x_58;
}
lean_ctor_set(x_59, 0, x_56);
lean_ctor_set(x_59, 1, x_57);
return x_59;
}
}
}
else
{
lean_object* x_60; lean_object* x_61; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_2);
lean_dec(x_1);
x_60 = lean_box(0);
if (lean_is_scalar(x_7)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_7;
}
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_6);
return x_61;
}
}
else
{
lean_object* x_62; lean_object* x_63; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_2);
lean_dec(x_1);
x_62 = lean_box(0);
if (lean_is_scalar(x_7)) {
 x_63 = lean_alloc_ctor(0, 2, 0);
} else {
 x_63 = x_7;
}
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_6);
return x_63;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_forM_loop___at_Lean_IR_EmitC_emitDeclAux___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Nat_forM_loop___at_Lean_IR_EmitC_emitDeclAux___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Nat_forM_loop___at_Lean_IR_EmitC_emitDeclAux___spec__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Nat_forM_loop___at_Lean_IR_EmitC_emitDeclAux___spec__2___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Nat_forM_loop___at_Lean_IR_EmitC_emitDeclAux___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Nat_forM_loop___at_Lean_IR_EmitC_emitDeclAux___spec__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Nat_forM_loop___at_Lean_IR_EmitC_emitDeclAux___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Nat_forM_loop___at_Lean_IR_EmitC_emitDeclAux___spec__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitDeclAux___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_IR_EmitC_emitDeclAux___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
return x_7;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitDecl___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("\ncompiling:\n", 12);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_IR_Decl_normalizeIds(x_1);
lean_inc(x_4);
x_5 = l_Lean_IR_EmitC_emitDeclAux(x_4, x_2, x_3);
if (lean_obj_tag(x_5) == 0)
{
lean_dec(x_4);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = l_Array_foldlMUnsafe_fold___at_Lean_IR_EmitC_emitFileHeader___spec__1___closed__1;
x_9 = lean_string_append(x_8, x_7);
lean_dec(x_7);
x_10 = l_Lean_IR_EmitC_emitDecl___closed__1;
x_11 = lean_string_append(x_9, x_10);
x_12 = lean_ir_decl_to_string(x_4);
x_13 = lean_string_append(x_11, x_12);
lean_dec(x_12);
x_14 = lean_string_append(x_13, x_8);
lean_ctor_set(x_5, 0, x_14);
return x_5;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_15 = lean_ctor_get(x_5, 0);
x_16 = lean_ctor_get(x_5, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_5);
x_17 = l_Array_foldlMUnsafe_fold___at_Lean_IR_EmitC_emitFileHeader___spec__1___closed__1;
x_18 = lean_string_append(x_17, x_15);
lean_dec(x_15);
x_19 = l_Lean_IR_EmitC_emitDecl___closed__1;
x_20 = lean_string_append(x_18, x_19);
x_21 = lean_ir_decl_to_string(x_4);
x_22 = lean_string_append(x_20, x_21);
lean_dec(x_21);
x_23 = lean_string_append(x_22, x_17);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_16);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at_Lean_IR_EmitC_emitFns___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
lean_inc(x_2);
x_8 = l_Lean_IR_EmitC_emitDecl(x_6, x_2, x_3);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_1 = x_7;
x_3 = x_9;
goto _start;
}
else
{
uint8_t x_11; 
lean_dec(x_7);
lean_dec(x_2);
x_11 = !lean_is_exclusive(x_8);
if (x_11 == 0)
{
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_8, 0);
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_8);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitFns(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = l_Lean_IR_EmitC_getEnv(x_1, x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = l_Lean_IR_getDecls(x_4);
lean_dec(x_4);
x_7 = l_List_reverse___rarg(x_6);
x_8 = l_List_forM___at_Lean_IR_EmitC_emitFns___spec__1(x_7, x_1, x_5);
return x_8;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitMarkPersistent___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("lean_mark_persistent(", 21);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitMarkPersistent(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_IR_Decl_resultType(x_1);
x_6 = l_Lean_IR_IRType_isObj(x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_2);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_4);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = l_Lean_IR_EmitC_emitMarkPersistent___closed__1;
x_10 = lean_string_append(x_4, x_9);
x_11 = l_Lean_IR_EmitC_emitCName(x_2, x_3, x_10);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_ctor_get(x_11, 1);
x_14 = lean_ctor_get(x_11, 0);
lean_dec(x_14);
x_15 = l_Lean_IR_EmitC_emitInc___lambda__1___closed__1;
x_16 = lean_string_append(x_13, x_15);
x_17 = l_Lean_IR_EmitC_emitLn___rarg___closed__1;
x_18 = lean_string_append(x_16, x_17);
x_19 = lean_box(0);
lean_ctor_set(x_11, 1, x_18);
lean_ctor_set(x_11, 0, x_19);
return x_11;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_20 = lean_ctor_get(x_11, 1);
lean_inc(x_20);
lean_dec(x_11);
x_21 = l_Lean_IR_EmitC_emitInc___lambda__1___closed__1;
x_22 = lean_string_append(x_20, x_21);
x_23 = l_Lean_IR_EmitC_emitLn___rarg___closed__1;
x_24 = lean_string_append(x_22, x_23);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
else
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_11);
if (x_27 == 0)
{
return x_11;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_11, 0);
x_29 = lean_ctor_get(x_11, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_11);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitMarkPersistent___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_EmitC_emitMarkPersistent(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitDeclInit___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("if (lean_io_result_is_error(res)) return res;", 45);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitDeclInit___lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" = lean_io_result_get_value(res);", 33);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitDeclInit___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_builtinInitAttr;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitDeclInit___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__2;
x_9 = lean_string_append(x_7, x_8);
x_10 = l_Lean_IR_EmitC_emitCName(x_1, x_6, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__13;
x_13 = lean_string_append(x_11, x_12);
x_14 = l_Lean_IR_EmitC_emitLn___rarg___closed__1;
x_15 = lean_string_append(x_13, x_14);
x_16 = l_Lean_IR_EmitC_emitDeclInit___lambda__1___closed__1;
x_17 = lean_string_append(x_15, x_16);
x_18 = lean_string_append(x_17, x_14);
lean_inc(x_2);
x_19 = l_Lean_IR_EmitC_emitCName(x_2, x_6, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = l_Lean_IR_EmitC_emitDeclInit___lambda__1___closed__2;
x_22 = lean_string_append(x_20, x_21);
x_23 = lean_string_append(x_22, x_14);
lean_inc(x_2);
x_24 = l_Lean_IR_EmitC_emitMarkPersistent(x_3, x_2, x_6, x_23);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_26 = lean_ctor_get(x_24, 1);
x_27 = lean_ctor_get(x_24, 0);
lean_dec(x_27);
x_28 = l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__7;
x_29 = lean_string_append(x_26, x_28);
x_30 = lean_string_append(x_29, x_14);
x_31 = l_Lean_IR_EmitC_emitDeclInit___lambda__1___closed__3;
x_32 = l_Lean_getInitFnNameForCore_x3f(x_4, x_31, x_2);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; 
x_33 = lean_box(0);
lean_ctor_set(x_24, 1, x_30);
lean_ctor_set(x_24, 0, x_33);
return x_24;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_32);
x_34 = l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__1;
x_35 = lean_string_append(x_30, x_34);
x_36 = lean_box(0);
lean_ctor_set(x_24, 1, x_35);
lean_ctor_set(x_24, 0, x_36);
return x_24;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_37 = lean_ctor_get(x_24, 1);
lean_inc(x_37);
lean_dec(x_24);
x_38 = l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__7;
x_39 = lean_string_append(x_37, x_38);
x_40 = lean_string_append(x_39, x_14);
x_41 = l_Lean_IR_EmitC_emitDeclInit___lambda__1___closed__3;
x_42 = l_Lean_getInitFnNameForCore_x3f(x_4, x_41, x_2);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_box(0);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_40);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_42);
x_45 = l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__1;
x_46 = lean_string_append(x_40, x_45);
x_47 = lean_box(0);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
}
}
else
{
uint8_t x_49; 
lean_dec(x_4);
lean_dec(x_2);
x_49 = !lean_is_exclusive(x_24);
if (x_49 == 0)
{
return x_24;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_24, 0);
x_51 = lean_ctor_get(x_24, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_24);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
else
{
uint8_t x_53; 
lean_dec(x_4);
lean_dec(x_2);
x_53 = !lean_is_exclusive(x_19);
if (x_53 == 0)
{
return x_19;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_19, 0);
x_55 = lean_ctor_get(x_19, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_19);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
else
{
uint8_t x_57; 
lean_dec(x_4);
lean_dec(x_2);
x_57 = !lean_is_exclusive(x_10);
if (x_57 == 0)
{
return x_10;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_10, 0);
x_59 = lean_ctor_get(x_10, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_10);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitDeclInit___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("();", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitDeclInit___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("if (builtin) {", 14);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitDeclInit(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_IR_EmitC_getEnv(x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = l_Lean_IR_Decl_name(x_1);
lean_inc(x_8);
lean_inc(x_6);
x_9 = l_Lean_isIOUnitInitFn(x_6, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = l_Lean_IR_Decl_params(x_1);
x_11 = lean_array_get_size(x_10);
lean_dec(x_10);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_nat_dec_eq(x_11, x_12);
lean_dec(x_11);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_14 = lean_box(0);
lean_ctor_set(x_4, 0, x_14);
return x_4;
}
else
{
lean_object* x_15; 
lean_free_object(x_4);
lean_inc(x_8);
lean_inc(x_6);
x_15 = lean_get_init_fn_name_for(x_6, x_8);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
lean_dec(x_6);
lean_inc(x_8);
x_16 = l_Lean_IR_EmitC_emitCName(x_8, x_2, x_7);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = l_Nat_forM_loop___at_Lean_IR_EmitC_emitJmp___spec__1___closed__1;
x_19 = lean_string_append(x_17, x_18);
lean_inc(x_8);
x_20 = l_Lean_IR_EmitC_emitCInitName(x_8, x_2, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = l_Lean_IR_EmitC_emitDeclInit___closed__1;
x_23 = lean_string_append(x_21, x_22);
x_24 = l_Lean_IR_EmitC_emitLn___rarg___closed__1;
x_25 = lean_string_append(x_23, x_24);
x_26 = l_Lean_IR_EmitC_emitMarkPersistent(x_1, x_8, x_2, x_25);
lean_dec(x_2);
lean_dec(x_1);
return x_26;
}
else
{
uint8_t x_27; 
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_20);
if (x_27 == 0)
{
return x_20;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_20, 0);
x_29 = lean_ctor_get(x_20, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_20);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
else
{
uint8_t x_31; 
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_16);
if (x_31 == 0)
{
return x_16;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_16, 0);
x_33 = lean_ctor_get(x_16, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_16);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_15, 0);
lean_inc(x_35);
lean_dec(x_15);
x_36 = l_Lean_IR_EmitC_emitDeclInit___lambda__1___closed__3;
lean_inc(x_8);
lean_inc(x_6);
x_37 = l_Lean_getInitFnNameForCore_x3f(x_6, x_36, x_8);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_box(0);
x_39 = l_Lean_IR_EmitC_emitDeclInit___lambda__1(x_35, x_8, x_1, x_6, x_38, x_2, x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_37);
x_40 = l_Lean_IR_EmitC_emitDeclInit___closed__2;
x_41 = lean_string_append(x_7, x_40);
x_42 = lean_box(0);
x_43 = l_Lean_IR_EmitC_emitDeclInit___lambda__1(x_35, x_8, x_1, x_6, x_42, x_2, x_41);
lean_dec(x_2);
lean_dec(x_1);
return x_43;
}
}
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_free_object(x_4);
lean_dec(x_6);
lean_dec(x_1);
x_44 = l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__2;
x_45 = lean_string_append(x_7, x_44);
x_46 = l_Lean_IR_EmitC_emitCName(x_8, x_2, x_45);
lean_dec(x_2);
if (lean_obj_tag(x_46) == 0)
{
uint8_t x_47; 
x_47 = !lean_is_exclusive(x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_48 = lean_ctor_get(x_46, 1);
x_49 = lean_ctor_get(x_46, 0);
lean_dec(x_49);
x_50 = l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__13;
x_51 = lean_string_append(x_48, x_50);
x_52 = l_Lean_IR_EmitC_emitLn___rarg___closed__1;
x_53 = lean_string_append(x_51, x_52);
x_54 = l_Lean_IR_EmitC_emitDeclInit___lambda__1___closed__1;
x_55 = lean_string_append(x_53, x_54);
x_56 = lean_string_append(x_55, x_52);
x_57 = l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__7;
x_58 = lean_string_append(x_56, x_57);
x_59 = lean_string_append(x_58, x_52);
x_60 = lean_box(0);
lean_ctor_set(x_46, 1, x_59);
lean_ctor_set(x_46, 0, x_60);
return x_46;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_61 = lean_ctor_get(x_46, 1);
lean_inc(x_61);
lean_dec(x_46);
x_62 = l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__13;
x_63 = lean_string_append(x_61, x_62);
x_64 = l_Lean_IR_EmitC_emitLn___rarg___closed__1;
x_65 = lean_string_append(x_63, x_64);
x_66 = l_Lean_IR_EmitC_emitDeclInit___lambda__1___closed__1;
x_67 = lean_string_append(x_65, x_66);
x_68 = lean_string_append(x_67, x_64);
x_69 = l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__7;
x_70 = lean_string_append(x_68, x_69);
x_71 = lean_string_append(x_70, x_64);
x_72 = lean_box(0);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_71);
return x_73;
}
}
else
{
uint8_t x_74; 
x_74 = !lean_is_exclusive(x_46);
if (x_74 == 0)
{
return x_46;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_46, 0);
x_76 = lean_ctor_get(x_46, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_46);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_78 = lean_ctor_get(x_4, 0);
x_79 = lean_ctor_get(x_4, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_4);
x_80 = l_Lean_IR_Decl_name(x_1);
lean_inc(x_80);
lean_inc(x_78);
x_81 = l_Lean_isIOUnitInitFn(x_78, x_80);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_82 = l_Lean_IR_Decl_params(x_1);
x_83 = lean_array_get_size(x_82);
lean_dec(x_82);
x_84 = lean_unsigned_to_nat(0u);
x_85 = lean_nat_dec_eq(x_83, x_84);
lean_dec(x_83);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; 
lean_dec(x_80);
lean_dec(x_78);
lean_dec(x_2);
lean_dec(x_1);
x_86 = lean_box(0);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_79);
return x_87;
}
else
{
lean_object* x_88; 
lean_inc(x_80);
lean_inc(x_78);
x_88 = lean_get_init_fn_name_for(x_78, x_80);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; 
lean_dec(x_78);
lean_inc(x_80);
x_89 = l_Lean_IR_EmitC_emitCName(x_80, x_2, x_79);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_90 = lean_ctor_get(x_89, 1);
lean_inc(x_90);
lean_dec(x_89);
x_91 = l_Nat_forM_loop___at_Lean_IR_EmitC_emitJmp___spec__1___closed__1;
x_92 = lean_string_append(x_90, x_91);
lean_inc(x_80);
x_93 = l_Lean_IR_EmitC_emitCInitName(x_80, x_2, x_92);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_94 = lean_ctor_get(x_93, 1);
lean_inc(x_94);
lean_dec(x_93);
x_95 = l_Lean_IR_EmitC_emitDeclInit___closed__1;
x_96 = lean_string_append(x_94, x_95);
x_97 = l_Lean_IR_EmitC_emitLn___rarg___closed__1;
x_98 = lean_string_append(x_96, x_97);
x_99 = l_Lean_IR_EmitC_emitMarkPersistent(x_1, x_80, x_2, x_98);
lean_dec(x_2);
lean_dec(x_1);
return x_99;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec(x_80);
lean_dec(x_2);
lean_dec(x_1);
x_100 = lean_ctor_get(x_93, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_93, 1);
lean_inc(x_101);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 lean_ctor_release(x_93, 1);
 x_102 = x_93;
} else {
 lean_dec_ref(x_93);
 x_102 = lean_box(0);
}
if (lean_is_scalar(x_102)) {
 x_103 = lean_alloc_ctor(1, 2, 0);
} else {
 x_103 = x_102;
}
lean_ctor_set(x_103, 0, x_100);
lean_ctor_set(x_103, 1, x_101);
return x_103;
}
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
lean_dec(x_80);
lean_dec(x_2);
lean_dec(x_1);
x_104 = lean_ctor_get(x_89, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_89, 1);
lean_inc(x_105);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 x_106 = x_89;
} else {
 lean_dec_ref(x_89);
 x_106 = lean_box(0);
}
if (lean_is_scalar(x_106)) {
 x_107 = lean_alloc_ctor(1, 2, 0);
} else {
 x_107 = x_106;
}
lean_ctor_set(x_107, 0, x_104);
lean_ctor_set(x_107, 1, x_105);
return x_107;
}
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = lean_ctor_get(x_88, 0);
lean_inc(x_108);
lean_dec(x_88);
x_109 = l_Lean_IR_EmitC_emitDeclInit___lambda__1___closed__3;
lean_inc(x_80);
lean_inc(x_78);
x_110 = l_Lean_getInitFnNameForCore_x3f(x_78, x_109, x_80);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; lean_object* x_112; 
x_111 = lean_box(0);
x_112 = l_Lean_IR_EmitC_emitDeclInit___lambda__1(x_108, x_80, x_1, x_78, x_111, x_2, x_79);
lean_dec(x_2);
lean_dec(x_1);
return x_112;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
lean_dec(x_110);
x_113 = l_Lean_IR_EmitC_emitDeclInit___closed__2;
x_114 = lean_string_append(x_79, x_113);
x_115 = lean_box(0);
x_116 = l_Lean_IR_EmitC_emitDeclInit___lambda__1(x_108, x_80, x_1, x_78, x_115, x_2, x_114);
lean_dec(x_2);
lean_dec(x_1);
return x_116;
}
}
}
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
lean_dec(x_78);
lean_dec(x_1);
x_117 = l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__2;
x_118 = lean_string_append(x_79, x_117);
x_119 = l_Lean_IR_EmitC_emitCName(x_80, x_2, x_118);
lean_dec(x_2);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_120 = lean_ctor_get(x_119, 1);
lean_inc(x_120);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 x_121 = x_119;
} else {
 lean_dec_ref(x_119);
 x_121 = lean_box(0);
}
x_122 = l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__13;
x_123 = lean_string_append(x_120, x_122);
x_124 = l_Lean_IR_EmitC_emitLn___rarg___closed__1;
x_125 = lean_string_append(x_123, x_124);
x_126 = l_Lean_IR_EmitC_emitDeclInit___lambda__1___closed__1;
x_127 = lean_string_append(x_125, x_126);
x_128 = lean_string_append(x_127, x_124);
x_129 = l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__7;
x_130 = lean_string_append(x_128, x_129);
x_131 = lean_string_append(x_130, x_124);
x_132 = lean_box(0);
if (lean_is_scalar(x_121)) {
 x_133 = lean_alloc_ctor(0, 2, 0);
} else {
 x_133 = x_121;
}
lean_ctor_set(x_133, 0, x_132);
lean_ctor_set(x_133, 1, x_131);
return x_133;
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_134 = lean_ctor_get(x_119, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_119, 1);
lean_inc(x_135);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 x_136 = x_119;
} else {
 lean_dec_ref(x_119);
 x_136 = lean_box(0);
}
if (lean_is_scalar(x_136)) {
 x_137 = lean_alloc_ctor(1, 2, 0);
} else {
 x_137 = x_136;
}
lean_ctor_set(x_137, 0, x_134);
lean_ctor_set(x_137, 1, x_135);
return x_137;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitDeclInit___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_IR_EmitC_emitDeclInit___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_List_forM___at_Lean_IR_EmitC_emitInitFn___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
lean_inc(x_2);
x_8 = l_Lean_IR_EmitC_emitDeclInit(x_6, x_2, x_3);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_1 = x_7;
x_3 = x_9;
goto _start;
}
else
{
uint8_t x_11; 
lean_dec(x_7);
lean_dec(x_2);
x_11 = !lean_is_exclusive(x_8);
if (x_11 == 0)
{
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_8, 0);
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_8);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lean_IR_EmitC_emitInitFn___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("(builtin, lean_io_mk_world());", 30);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_EmitC_emitInitFn___spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_eq(x_3, x_4);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; size_t x_24; size_t x_25; 
lean_dec(x_5);
x_9 = lean_array_uget(x_2, x_3);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_mk_module_initialization_function_name(x_10);
x_12 = l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__2;
x_13 = lean_string_append(x_12, x_11);
lean_dec(x_11);
x_14 = l_Array_foldlMUnsafe_fold___at_Lean_IR_EmitC_emitInitFn___spec__2___closed__1;
x_15 = lean_string_append(x_13, x_14);
x_16 = l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__7;
lean_inc(x_1);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_1);
x_18 = l_Lean_IR_EmitC_emitDeclInit___lambda__1___closed__1;
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_15);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_List_forM___at_Lean_IR_EmitC_emitMainFn___spec__3(x_20, x_6, x_7);
lean_dec(x_20);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = 1;
x_25 = lean_usize_add(x_3, x_24);
x_3 = x_25;
x_5 = x_22;
x_7 = x_23;
goto _start;
}
else
{
lean_object* x_27; 
lean_dec(x_1);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_5);
lean_ctor_set(x_27, 1, x_7);
return x_27;
}
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lean_IR_EmitC_emitInitFn___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("(uint8_t builtin, lean_object*);", 32);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_EmitC_emitInitFn___spec__3(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_2, x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; 
lean_dec(x_4);
x_8 = lean_array_uget(x_1, x_2);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_mk_module_initialization_function_name(x_9);
x_11 = l_Nat_forM_loop___at_Lean_IR_EmitC_emitDeclAux___spec__1___closed__1;
x_12 = lean_string_append(x_11, x_10);
lean_dec(x_10);
x_13 = l_Array_foldlMUnsafe_fold___at_Lean_IR_EmitC_emitInitFn___spec__3___closed__1;
x_14 = lean_string_append(x_12, x_13);
x_15 = lean_string_append(x_6, x_14);
lean_dec(x_14);
x_16 = l_Lean_IR_EmitC_emitLn___rarg___closed__1;
x_17 = lean_string_append(x_15, x_16);
x_18 = 1;
x_19 = lean_usize_add(x_2, x_18);
x_20 = lean_box(0);
x_2 = x_19;
x_4 = x_20;
x_6 = x_17;
goto _start;
}
else
{
lean_object* x_22; 
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_4);
lean_ctor_set(x_22, 1, x_6);
return x_22;
}
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitInitFn___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("LEAN_EXPORT lean_object* ", 25);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitInitFn___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("(uint8_t builtin, lean_object* w) {", 35);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitInitFn___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_G_initialized = true;", 22);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitInitFn___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_IR_EmitC_emitInitFn___closed__3;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitInitFn___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));", 61);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitInitFn___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_EmitC_emitInitFn___closed__5;
x_2 = l_Lean_IR_EmitC_emitInitFn___closed__4;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitInitFn___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("lean_object * res;", 18);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitInitFn___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_EmitC_emitInitFn___closed__7;
x_2 = l_Lean_IR_EmitC_emitInitFn___closed__6;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitInitFn___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("static bool _G_initialized = false;", 35);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitInitFn___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("return lean_io_result_mk_ok(lean_box(0));", 41);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_EmitC_emitInitFn___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_EmitC_emitInitFn___closed__10;
x_2 = l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__15;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_emitInitFn(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_63; uint8_t x_64; 
x_3 = l_Lean_IR_EmitC_getEnv(x_1, x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = l_Lean_IR_EmitC_getModName(x_1, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_Environment_imports(x_4);
x_10 = lean_array_get_size(x_9);
x_63 = lean_unsigned_to_nat(0u);
x_64 = lean_nat_dec_lt(x_63, x_10);
if (x_64 == 0)
{
x_11 = x_8;
goto block_62;
}
else
{
uint8_t x_65; 
x_65 = lean_nat_dec_le(x_10, x_10);
if (x_65 == 0)
{
x_11 = x_8;
goto block_62;
}
else
{
size_t x_66; size_t x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_66 = 0;
x_67 = lean_usize_of_nat(x_10);
x_68 = lean_box(0);
x_69 = l_Array_foldlMUnsafe_fold___at_Lean_IR_EmitC_emitInitFn___spec__3(x_9, x_66, x_67, x_68, x_1, x_8);
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
lean_dec(x_69);
x_11 = x_70;
goto block_62;
}
}
block_62:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_12 = lean_mk_module_initialization_function_name(x_7);
x_13 = l_Lean_IR_EmitC_emitInitFn___closed__1;
x_14 = lean_string_append(x_13, x_12);
lean_dec(x_12);
x_15 = l_Lean_IR_EmitC_emitInitFn___closed__2;
x_16 = lean_string_append(x_14, x_15);
x_17 = lean_box(0);
x_18 = l_Lean_IR_EmitC_emitInitFn___closed__8;
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_IR_EmitC_emitInitFn___closed__9;
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
x_22 = l_List_forM___at_Lean_IR_EmitC_emitMainFn___spec__3(x_21, x_1, x_11);
lean_dec(x_21);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_unsigned_to_nat(0u);
x_25 = lean_nat_dec_lt(x_24, x_10);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_10);
lean_dec(x_9);
x_26 = l_Lean_IR_getDecls(x_4);
lean_dec(x_4);
x_27 = l_List_reverse___rarg(x_26);
lean_inc(x_1);
x_28 = l_List_forM___at_Lean_IR_EmitC_emitInitFn___spec__1(x_27, x_1, x_23);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = l_Lean_IR_EmitC_emitInitFn___closed__11;
x_31 = l_List_forM___at_Lean_IR_EmitC_emitMainFn___spec__3(x_30, x_1, x_29);
lean_dec(x_1);
return x_31;
}
else
{
uint8_t x_32; 
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_28);
if (x_32 == 0)
{
return x_28;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_28, 0);
x_34 = lean_ctor_get(x_28, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_28);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
uint8_t x_36; 
x_36 = lean_nat_dec_le(x_10, x_10);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_10);
lean_dec(x_9);
x_37 = l_Lean_IR_getDecls(x_4);
lean_dec(x_4);
x_38 = l_List_reverse___rarg(x_37);
lean_inc(x_1);
x_39 = l_List_forM___at_Lean_IR_EmitC_emitInitFn___spec__1(x_38, x_1, x_23);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec(x_39);
x_41 = l_Lean_IR_EmitC_emitInitFn___closed__11;
x_42 = l_List_forM___at_Lean_IR_EmitC_emitMainFn___spec__3(x_41, x_1, x_40);
lean_dec(x_1);
return x_42;
}
else
{
uint8_t x_43; 
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_39);
if (x_43 == 0)
{
return x_39;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_39, 0);
x_45 = lean_ctor_get(x_39, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_39);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
else
{
size_t x_47; size_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_47 = 0;
x_48 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_49 = lean_box(0);
x_50 = l_Array_foldlMUnsafe_fold___at_Lean_IR_EmitC_emitInitFn___spec__2(x_17, x_9, x_47, x_48, x_49, x_1, x_23);
lean_dec(x_9);
x_51 = lean_ctor_get(x_50, 1);
lean_inc(x_51);
lean_dec(x_50);
x_52 = l_Lean_IR_getDecls(x_4);
lean_dec(x_4);
x_53 = l_List_reverse___rarg(x_52);
lean_inc(x_1);
x_54 = l_List_forM___at_Lean_IR_EmitC_emitInitFn___spec__1(x_53, x_1, x_51);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
lean_dec(x_54);
x_56 = l_Lean_IR_EmitC_emitInitFn___closed__11;
x_57 = l_List_forM___at_Lean_IR_EmitC_emitMainFn___spec__3(x_56, x_1, x_55);
lean_dec(x_1);
return x_57;
}
else
{
uint8_t x_58; 
lean_dec(x_1);
x_58 = !lean_is_exclusive(x_54);
if (x_58 == 0)
{
return x_54;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_54, 0);
x_60 = lean_ctor_get(x_54, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_54);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_EmitC_emitInitFn___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = l_Array_foldlMUnsafe_fold___at_Lean_IR_EmitC_emitInitFn___spec__2(x_1, x_2, x_8, x_9, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_EmitC_emitInitFn___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l_Array_foldlMUnsafe_fold___at_Lean_IR_EmitC_emitInitFn___spec__3(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_EmitC_main(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Lean_IR_EmitC_emitFileHeader(x_1, x_2);
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec(x_3);
lean_inc(x_1);
x_5 = l_Lean_IR_EmitC_emitFnDecls(x_1, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
lean_inc(x_1);
x_7 = l_Lean_IR_EmitC_emitFns(x_1, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
lean_inc(x_1);
x_9 = l_Lean_IR_EmitC_emitInitFn(x_1, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
lean_inc(x_1);
x_11 = l_Lean_IR_EmitC_emitMainFnIfNeeded(x_1, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = l_Lean_IR_EmitC_emitFileFooter(x_1, x_12);
lean_dec(x_1);
return x_13;
}
else
{
uint8_t x_14; 
lean_dec(x_1);
x_14 = !lean_is_exclusive(x_11);
if (x_14 == 0)
{
return x_11;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_11, 0);
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_11);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
else
{
uint8_t x_18; 
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_9);
if (x_18 == 0)
{
return x_9;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_9, 0);
x_20 = lean_ctor_get(x_9, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_9);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
else
{
uint8_t x_22; 
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_7);
if (x_22 == 0)
{
return x_7;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_7, 0);
x_24 = lean_ctor_get(x_7, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_7);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
else
{
uint8_t x_26; 
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_5);
if (x_26 == 0)
{
return x_5;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_5, 0);
x_28 = lean_ctor_get(x_5, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_5);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
LEAN_EXPORT lean_object* lean_ir_emit_c(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = l_Lean_IR_EmitC_Context_jpMap___default___closed__1;
x_4 = lean_box(0);
x_5 = l_Lean_IR_EmitC_Context_mainParams___default___closed__1;
x_6 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_4);
lean_ctor_set(x_6, 4, x_5);
x_7 = l_Array_foldlMUnsafe_fold___at_Lean_IR_EmitC_emitFileHeader___spec__1___closed__1;
x_8 = l_Lean_IR_EmitC_main(x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_8, 0);
lean_inc(x_11);
lean_dec(x_8);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Runtime(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_NameMangling(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_ExportAttr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_InitAttr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_IR_CompilerM(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_IR_EmitUtil(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_IR_NormIds(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_IR_SimpCase(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_IR_Boxing(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_IR_EmitC(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Runtime(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_NameMangling(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_ExportAttr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_InitAttr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_CompilerM(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_EmitUtil(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_NormIds(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_SimpCase(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_Boxing(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_IR_EmitC_leanMainFn___closed__1 = _init_l_Lean_IR_EmitC_leanMainFn___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_leanMainFn___closed__1);
l_Lean_IR_EmitC_leanMainFn = _init_l_Lean_IR_EmitC_leanMainFn();
lean_mark_persistent(l_Lean_IR_EmitC_leanMainFn);
l_Lean_IR_EmitC_Context_jpMap___default___closed__1 = _init_l_Lean_IR_EmitC_Context_jpMap___default___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_Context_jpMap___default___closed__1);
l_Lean_IR_EmitC_Context_jpMap___default = _init_l_Lean_IR_EmitC_Context_jpMap___default();
lean_mark_persistent(l_Lean_IR_EmitC_Context_jpMap___default);
l_Lean_IR_EmitC_Context_mainFn___default = _init_l_Lean_IR_EmitC_Context_mainFn___default();
lean_mark_persistent(l_Lean_IR_EmitC_Context_mainFn___default);
l_Lean_IR_EmitC_Context_mainParams___default___closed__1 = _init_l_Lean_IR_EmitC_Context_mainParams___default___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_Context_mainParams___default___closed__1);
l_Lean_IR_EmitC_Context_mainParams___default = _init_l_Lean_IR_EmitC_Context_mainParams___default();
lean_mark_persistent(l_Lean_IR_EmitC_Context_mainParams___default);
l_Lean_IR_EmitC_getDecl___closed__1 = _init_l_Lean_IR_EmitC_getDecl___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_getDecl___closed__1);
l_Lean_IR_EmitC_getDecl___closed__2 = _init_l_Lean_IR_EmitC_getDecl___closed__2();
lean_mark_persistent(l_Lean_IR_EmitC_getDecl___closed__2);
l_Lean_IR_EmitC_emitLn___rarg___closed__1 = _init_l_Lean_IR_EmitC_emitLn___rarg___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_emitLn___rarg___closed__1);
l_Lean_IR_EmitC_argToCString___closed__1 = _init_l_Lean_IR_EmitC_argToCString___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_argToCString___closed__1);
l_Lean_IR_EmitC_argToCString___closed__2 = _init_l_Lean_IR_EmitC_argToCString___closed__2();
lean_mark_persistent(l_Lean_IR_EmitC_argToCString___closed__2);
l_Lean_IR_EmitC_toCType___closed__1 = _init_l_Lean_IR_EmitC_toCType___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_toCType___closed__1);
l_Lean_IR_EmitC_toCType___closed__2 = _init_l_Lean_IR_EmitC_toCType___closed__2();
lean_mark_persistent(l_Lean_IR_EmitC_toCType___closed__2);
l_Lean_IR_EmitC_toCType___closed__3 = _init_l_Lean_IR_EmitC_toCType___closed__3();
lean_mark_persistent(l_Lean_IR_EmitC_toCType___closed__3);
l_Lean_IR_EmitC_toCType___closed__4 = _init_l_Lean_IR_EmitC_toCType___closed__4();
lean_mark_persistent(l_Lean_IR_EmitC_toCType___closed__4);
l_Lean_IR_EmitC_toCType___closed__5 = _init_l_Lean_IR_EmitC_toCType___closed__5();
lean_mark_persistent(l_Lean_IR_EmitC_toCType___closed__5);
l_Lean_IR_EmitC_toCType___closed__6 = _init_l_Lean_IR_EmitC_toCType___closed__6();
lean_mark_persistent(l_Lean_IR_EmitC_toCType___closed__6);
l_Lean_IR_EmitC_toCType___closed__7 = _init_l_Lean_IR_EmitC_toCType___closed__7();
lean_mark_persistent(l_Lean_IR_EmitC_toCType___closed__7);
l_Lean_IR_EmitC_toCType___closed__8 = _init_l_Lean_IR_EmitC_toCType___closed__8();
lean_mark_persistent(l_Lean_IR_EmitC_toCType___closed__8);
l_Lean_IR_EmitC_toCType___closed__9 = _init_l_Lean_IR_EmitC_toCType___closed__9();
lean_mark_persistent(l_Lean_IR_EmitC_toCType___closed__9);
l_Lean_IR_EmitC_toCType___closed__10 = _init_l_Lean_IR_EmitC_toCType___closed__10();
lean_mark_persistent(l_Lean_IR_EmitC_toCType___closed__10);
l_Lean_IR_EmitC_toCType___closed__11 = _init_l_Lean_IR_EmitC_toCType___closed__11();
lean_mark_persistent(l_Lean_IR_EmitC_toCType___closed__11);
l_Lean_IR_EmitC_toCType___closed__12 = _init_l_Lean_IR_EmitC_toCType___closed__12();
lean_mark_persistent(l_Lean_IR_EmitC_toCType___closed__12);
l_Lean_IR_EmitC_throwInvalidExportName___rarg___closed__1 = _init_l_Lean_IR_EmitC_throwInvalidExportName___rarg___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_throwInvalidExportName___rarg___closed__1);
l_Lean_IR_EmitC_toCName___closed__1 = _init_l_Lean_IR_EmitC_toCName___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_toCName___closed__1);
l_Lean_IR_EmitC_toCName___closed__2 = _init_l_Lean_IR_EmitC_toCName___closed__2();
lean_mark_persistent(l_Lean_IR_EmitC_toCName___closed__2);
l_Lean_IR_EmitC_toCName___closed__3 = _init_l_Lean_IR_EmitC_toCName___closed__3();
lean_mark_persistent(l_Lean_IR_EmitC_toCName___closed__3);
l_Lean_IR_EmitC_toCName___closed__4 = _init_l_Lean_IR_EmitC_toCName___closed__4();
lean_mark_persistent(l_Lean_IR_EmitC_toCName___closed__4);
l_Lean_IR_EmitC_toCInitName___closed__1 = _init_l_Lean_IR_EmitC_toCInitName___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_toCInitName___closed__1);
l_Nat_forM_loop___at_Lean_IR_EmitC_emitFnDeclAux___spec__1___closed__1 = _init_l_Nat_forM_loop___at_Lean_IR_EmitC_emitFnDeclAux___spec__1___closed__1();
lean_mark_persistent(l_Nat_forM_loop___at_Lean_IR_EmitC_emitFnDeclAux___spec__1___closed__1);
l_Lean_IR_EmitC_emitFnDeclAux___lambda__1___closed__1 = _init_l_Lean_IR_EmitC_emitFnDeclAux___lambda__1___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_emitFnDeclAux___lambda__1___closed__1);
l_Lean_IR_EmitC_emitFnDeclAux___lambda__2___closed__1 = _init_l_Lean_IR_EmitC_emitFnDeclAux___lambda__2___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_emitFnDeclAux___lambda__2___closed__1);
l_Lean_IR_EmitC_emitFnDeclAux___lambda__3___closed__1 = _init_l_Lean_IR_EmitC_emitFnDeclAux___lambda__3___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_emitFnDeclAux___lambda__3___closed__1);
l_Lean_IR_EmitC_emitFnDeclAux___lambda__3___closed__2 = _init_l_Lean_IR_EmitC_emitFnDeclAux___lambda__3___closed__2();
lean_mark_persistent(l_Lean_IR_EmitC_emitFnDeclAux___lambda__3___closed__2);
l_Lean_IR_EmitC_emitFnDeclAux___lambda__3___closed__3 = _init_l_Lean_IR_EmitC_emitFnDeclAux___lambda__3___closed__3();
lean_mark_persistent(l_Lean_IR_EmitC_emitFnDeclAux___lambda__3___closed__3);
l_Lean_IR_EmitC_emitFnDeclAux___lambda__3___closed__4 = _init_l_Lean_IR_EmitC_emitFnDeclAux___lambda__3___closed__4();
lean_mark_persistent(l_Lean_IR_EmitC_emitFnDeclAux___lambda__3___closed__4);
l_Lean_IR_EmitC_emitFnDeclAux___closed__1 = _init_l_Lean_IR_EmitC_emitFnDeclAux___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_emitFnDeclAux___closed__1);
l_Lean_IR_EmitC_emitFnDeclAux___closed__2 = _init_l_Lean_IR_EmitC_emitFnDeclAux___closed__2();
lean_mark_persistent(l_Lean_IR_EmitC_emitFnDeclAux___closed__2);
l_Lean_IR_EmitC_emitFnDeclAux___closed__3 = _init_l_Lean_IR_EmitC_emitFnDeclAux___closed__3();
lean_mark_persistent(l_Lean_IR_EmitC_emitFnDeclAux___closed__3);
l_List_forM___at_Lean_IR_EmitC_emitFnDecls___spec__5___closed__1 = _init_l_List_forM___at_Lean_IR_EmitC_emitFnDecls___spec__5___closed__1();
lean_mark_persistent(l_List_forM___at_Lean_IR_EmitC_emitFnDecls___spec__5___closed__1);
l_List_forM___at_Lean_IR_EmitC_emitFnDecls___spec__5___closed__2 = _init_l_List_forM___at_Lean_IR_EmitC_emitFnDecls___spec__5___closed__2();
lean_mark_persistent(l_List_forM___at_Lean_IR_EmitC_emitFnDecls___spec__5___closed__2);
l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__1 = _init_l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__1);
l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__2 = _init_l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__2();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__2);
l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__3 = _init_l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__3();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__3);
l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__4 = _init_l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__4();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__4);
l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__5 = _init_l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__5();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__5);
l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__6 = _init_l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__6();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__6);
l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__7 = _init_l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__7();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__7);
l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__8 = _init_l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__8();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__8);
l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__9 = _init_l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__9();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__9);
l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__10 = _init_l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__10();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__10);
l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__11 = _init_l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__11();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__11);
l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__12 = _init_l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__12();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__12);
l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__13 = _init_l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__13();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__13);
l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__14 = _init_l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__14();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__14);
l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__15 = _init_l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__15();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__15);
l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__16 = _init_l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__16();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__16);
l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__17 = _init_l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__17();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__17);
l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__18 = _init_l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__18();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__18);
l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__19 = _init_l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__19();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__19);
l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__20 = _init_l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__20();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___lambda__1___closed__20);
l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__1 = _init_l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__1);
l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__2 = _init_l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__2();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__2);
l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__3 = _init_l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__3();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__3);
l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__4 = _init_l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__4();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__4);
l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__5 = _init_l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__5();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__5);
l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__6 = _init_l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__6();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__6);
l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__7 = _init_l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__7();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__7);
l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__8 = _init_l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__8();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__8);
l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__9 = _init_l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__9();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__9);
l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__10 = _init_l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__10();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__10);
l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__11 = _init_l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__11();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__11);
l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__12 = _init_l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__12();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__12);
l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__13 = _init_l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__13();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__13);
l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__14 = _init_l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__14();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__14);
l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__15 = _init_l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__15();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__15);
l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__16 = _init_l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__16();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__16);
l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__17 = _init_l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__17();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__17);
l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__18 = _init_l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__18();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__18);
l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__19 = _init_l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__19();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__19);
l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__20 = _init_l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__20();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__20);
l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__21 = _init_l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__21();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__21);
l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__22 = _init_l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__22();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__22);
l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__23 = _init_l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__23();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__23);
l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__24 = _init_l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__24();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__24);
l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__25 = _init_l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__25();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__25);
l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__26 = _init_l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__26();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__26);
l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__27 = _init_l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__27();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__27);
l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__28 = _init_l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__28();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__28);
l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__29 = _init_l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__29();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__29);
l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__30 = _init_l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__30();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__30);
l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__31 = _init_l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__31();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___lambda__2___closed__31);
l_Lean_IR_EmitC_emitMainFn___lambda__3___closed__1 = _init_l_Lean_IR_EmitC_emitMainFn___lambda__3___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___lambda__3___closed__1);
l_Lean_IR_EmitC_emitMainFn___lambda__3___closed__2 = _init_l_Lean_IR_EmitC_emitMainFn___lambda__3___closed__2();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___lambda__3___closed__2);
l_Lean_IR_EmitC_emitMainFn___lambda__3___closed__3 = _init_l_Lean_IR_EmitC_emitMainFn___lambda__3___closed__3();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___lambda__3___closed__3);
l_Lean_IR_EmitC_emitMainFn___lambda__4___closed__1 = _init_l_Lean_IR_EmitC_emitMainFn___lambda__4___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___lambda__4___closed__1);
l_Lean_IR_EmitC_emitMainFn___lambda__4___closed__2 = _init_l_Lean_IR_EmitC_emitMainFn___lambda__4___closed__2();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___lambda__4___closed__2);
l_Lean_IR_EmitC_emitMainFn___lambda__4___closed__3 = _init_l_Lean_IR_EmitC_emitMainFn___lambda__4___closed__3();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___lambda__4___closed__3);
l_Lean_IR_EmitC_emitMainFn___lambda__4___closed__4 = _init_l_Lean_IR_EmitC_emitMainFn___lambda__4___closed__4();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___lambda__4___closed__4);
l_Lean_IR_EmitC_emitMainFn___closed__1 = _init_l_Lean_IR_EmitC_emitMainFn___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___closed__1);
l_Lean_IR_EmitC_emitMainFn___closed__2 = _init_l_Lean_IR_EmitC_emitMainFn___closed__2();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___closed__2);
l_Array_foldlMUnsafe_fold___at_Lean_IR_EmitC_emitFileHeader___spec__1___closed__1 = _init_l_Array_foldlMUnsafe_fold___at_Lean_IR_EmitC_emitFileHeader___spec__1___closed__1();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lean_IR_EmitC_emitFileHeader___spec__1___closed__1);
l_Array_foldlMUnsafe_fold___at_Lean_IR_EmitC_emitFileHeader___spec__1___closed__2 = _init_l_Array_foldlMUnsafe_fold___at_Lean_IR_EmitC_emitFileHeader___spec__1___closed__2();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lean_IR_EmitC_emitFileHeader___spec__1___closed__2);
l_Lean_IR_EmitC_emitFileHeader___closed__1 = _init_l_Lean_IR_EmitC_emitFileHeader___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_emitFileHeader___closed__1);
l_Lean_IR_EmitC_emitFileHeader___closed__2 = _init_l_Lean_IR_EmitC_emitFileHeader___closed__2();
lean_mark_persistent(l_Lean_IR_EmitC_emitFileHeader___closed__2);
l_Lean_IR_EmitC_emitFileHeader___closed__3 = _init_l_Lean_IR_EmitC_emitFileHeader___closed__3();
lean_mark_persistent(l_Lean_IR_EmitC_emitFileHeader___closed__3);
l_Lean_IR_EmitC_emitFileHeader___closed__4 = _init_l_Lean_IR_EmitC_emitFileHeader___closed__4();
lean_mark_persistent(l_Lean_IR_EmitC_emitFileHeader___closed__4);
l_Lean_IR_EmitC_emitFileHeader___closed__5 = _init_l_Lean_IR_EmitC_emitFileHeader___closed__5();
lean_mark_persistent(l_Lean_IR_EmitC_emitFileHeader___closed__5);
l_Lean_IR_EmitC_emitFileHeader___closed__6 = _init_l_Lean_IR_EmitC_emitFileHeader___closed__6();
lean_mark_persistent(l_Lean_IR_EmitC_emitFileHeader___closed__6);
l_Lean_IR_EmitC_emitFileHeader___closed__7 = _init_l_Lean_IR_EmitC_emitFileHeader___closed__7();
lean_mark_persistent(l_Lean_IR_EmitC_emitFileHeader___closed__7);
l_Lean_IR_EmitC_emitFileHeader___closed__8 = _init_l_Lean_IR_EmitC_emitFileHeader___closed__8();
lean_mark_persistent(l_Lean_IR_EmitC_emitFileHeader___closed__8);
l_Lean_IR_EmitC_emitFileHeader___closed__9 = _init_l_Lean_IR_EmitC_emitFileHeader___closed__9();
lean_mark_persistent(l_Lean_IR_EmitC_emitFileHeader___closed__9);
l_Lean_IR_EmitC_emitFileHeader___closed__10 = _init_l_Lean_IR_EmitC_emitFileHeader___closed__10();
lean_mark_persistent(l_Lean_IR_EmitC_emitFileHeader___closed__10);
l_Lean_IR_EmitC_emitFileHeader___closed__11 = _init_l_Lean_IR_EmitC_emitFileHeader___closed__11();
lean_mark_persistent(l_Lean_IR_EmitC_emitFileHeader___closed__11);
l_Lean_IR_EmitC_emitFileHeader___closed__12 = _init_l_Lean_IR_EmitC_emitFileHeader___closed__12();
lean_mark_persistent(l_Lean_IR_EmitC_emitFileHeader___closed__12);
l_Lean_IR_EmitC_emitFileHeader___closed__13 = _init_l_Lean_IR_EmitC_emitFileHeader___closed__13();
lean_mark_persistent(l_Lean_IR_EmitC_emitFileHeader___closed__13);
l_Lean_IR_EmitC_emitFileHeader___closed__14 = _init_l_Lean_IR_EmitC_emitFileHeader___closed__14();
lean_mark_persistent(l_Lean_IR_EmitC_emitFileHeader___closed__14);
l_Lean_IR_EmitC_emitFileHeader___closed__15 = _init_l_Lean_IR_EmitC_emitFileHeader___closed__15();
lean_mark_persistent(l_Lean_IR_EmitC_emitFileHeader___closed__15);
l_Lean_IR_EmitC_emitFileHeader___closed__16 = _init_l_Lean_IR_EmitC_emitFileHeader___closed__16();
lean_mark_persistent(l_Lean_IR_EmitC_emitFileHeader___closed__16);
l_Lean_IR_EmitC_emitFileHeader___closed__17 = _init_l_Lean_IR_EmitC_emitFileHeader___closed__17();
lean_mark_persistent(l_Lean_IR_EmitC_emitFileHeader___closed__17);
l_Lean_IR_EmitC_emitFileHeader___closed__18 = _init_l_Lean_IR_EmitC_emitFileHeader___closed__18();
lean_mark_persistent(l_Lean_IR_EmitC_emitFileHeader___closed__18);
l_Lean_IR_EmitC_emitFileHeader___closed__19 = _init_l_Lean_IR_EmitC_emitFileHeader___closed__19();
lean_mark_persistent(l_Lean_IR_EmitC_emitFileHeader___closed__19);
l_Lean_IR_EmitC_emitFileHeader___closed__20 = _init_l_Lean_IR_EmitC_emitFileHeader___closed__20();
lean_mark_persistent(l_Lean_IR_EmitC_emitFileHeader___closed__20);
l_Lean_IR_EmitC_emitFileHeader___closed__21 = _init_l_Lean_IR_EmitC_emitFileHeader___closed__21();
lean_mark_persistent(l_Lean_IR_EmitC_emitFileHeader___closed__21);
l_Lean_IR_EmitC_emitFileHeader___closed__22 = _init_l_Lean_IR_EmitC_emitFileHeader___closed__22();
lean_mark_persistent(l_Lean_IR_EmitC_emitFileHeader___closed__22);
l_Lean_IR_EmitC_emitFileHeader___closed__23 = _init_l_Lean_IR_EmitC_emitFileHeader___closed__23();
lean_mark_persistent(l_Lean_IR_EmitC_emitFileHeader___closed__23);
l_Lean_IR_EmitC_emitFileHeader___closed__24 = _init_l_Lean_IR_EmitC_emitFileHeader___closed__24();
lean_mark_persistent(l_Lean_IR_EmitC_emitFileHeader___closed__24);
l_Lean_IR_EmitC_emitFileHeader___closed__25 = _init_l_Lean_IR_EmitC_emitFileHeader___closed__25();
lean_mark_persistent(l_Lean_IR_EmitC_emitFileHeader___closed__25);
l_Lean_IR_EmitC_emitFileFooter___closed__1 = _init_l_Lean_IR_EmitC_emitFileFooter___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_emitFileFooter___closed__1);
l_Lean_IR_EmitC_emitFileFooter___closed__2 = _init_l_Lean_IR_EmitC_emitFileFooter___closed__2();
lean_mark_persistent(l_Lean_IR_EmitC_emitFileFooter___closed__2);
l_Lean_IR_EmitC_throwUnknownVar___rarg___closed__1 = _init_l_Lean_IR_EmitC_throwUnknownVar___rarg___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_throwUnknownVar___rarg___closed__1);
l_Lean_IR_EmitC_getJPParams___closed__1 = _init_l_Lean_IR_EmitC_getJPParams___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_getJPParams___closed__1);
l_Lean_IR_EmitC_declareVar___closed__1 = _init_l_Lean_IR_EmitC_declareVar___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_declareVar___closed__1);
l_Lean_IR_EmitC_emitTag___closed__1 = _init_l_Lean_IR_EmitC_emitTag___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_emitTag___closed__1);
l_Lean_IR_EmitC_emitInc___lambda__1___closed__1 = _init_l_Lean_IR_EmitC_emitInc___lambda__1___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_emitInc___lambda__1___closed__1);
l_Lean_IR_EmitC_emitInc___closed__1 = _init_l_Lean_IR_EmitC_emitInc___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_emitInc___closed__1);
l_Lean_IR_EmitC_emitInc___closed__2 = _init_l_Lean_IR_EmitC_emitInc___closed__2();
lean_mark_persistent(l_Lean_IR_EmitC_emitInc___closed__2);
l_Lean_IR_EmitC_emitInc___closed__3 = _init_l_Lean_IR_EmitC_emitInc___closed__3();
lean_mark_persistent(l_Lean_IR_EmitC_emitInc___closed__3);
l_Lean_IR_EmitC_emitInc___closed__4 = _init_l_Lean_IR_EmitC_emitInc___closed__4();
lean_mark_persistent(l_Lean_IR_EmitC_emitInc___closed__4);
l_Lean_IR_EmitC_emitInc___closed__5 = _init_l_Lean_IR_EmitC_emitInc___closed__5();
lean_mark_persistent(l_Lean_IR_EmitC_emitInc___closed__5);
l_Lean_IR_EmitC_emitDec___closed__1 = _init_l_Lean_IR_EmitC_emitDec___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_emitDec___closed__1);
l_Lean_IR_EmitC_emitDec___closed__2 = _init_l_Lean_IR_EmitC_emitDec___closed__2();
lean_mark_persistent(l_Lean_IR_EmitC_emitDec___closed__2);
l_Lean_IR_EmitC_emitDel___closed__1 = _init_l_Lean_IR_EmitC_emitDel___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_emitDel___closed__1);
l_Lean_IR_EmitC_emitSetTag___closed__1 = _init_l_Lean_IR_EmitC_emitSetTag___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_emitSetTag___closed__1);
l_Lean_IR_EmitC_emitSet___closed__1 = _init_l_Lean_IR_EmitC_emitSet___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_emitSet___closed__1);
l_Lean_IR_EmitC_emitOffset___closed__1 = _init_l_Lean_IR_EmitC_emitOffset___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_emitOffset___closed__1);
l_Lean_IR_EmitC_emitOffset___closed__2 = _init_l_Lean_IR_EmitC_emitOffset___closed__2();
lean_mark_persistent(l_Lean_IR_EmitC_emitOffset___closed__2);
l_Lean_IR_EmitC_emitUSet___closed__1 = _init_l_Lean_IR_EmitC_emitUSet___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_emitUSet___closed__1);
l_Lean_IR_EmitC_emitSSet___closed__1 = _init_l_Lean_IR_EmitC_emitSSet___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_emitSSet___closed__1);
l_Lean_IR_EmitC_emitSSet___closed__2 = _init_l_Lean_IR_EmitC_emitSSet___closed__2();
lean_mark_persistent(l_Lean_IR_EmitC_emitSSet___closed__2);
l_Lean_IR_EmitC_emitSSet___closed__3 = _init_l_Lean_IR_EmitC_emitSSet___closed__3();
lean_mark_persistent(l_Lean_IR_EmitC_emitSSet___closed__3);
l_Lean_IR_EmitC_emitSSet___closed__4 = _init_l_Lean_IR_EmitC_emitSSet___closed__4();
lean_mark_persistent(l_Lean_IR_EmitC_emitSSet___closed__4);
l_Lean_IR_EmitC_emitSSet___closed__5 = _init_l_Lean_IR_EmitC_emitSSet___closed__5();
lean_mark_persistent(l_Lean_IR_EmitC_emitSSet___closed__5);
l_Lean_IR_EmitC_emitSSet___closed__6 = _init_l_Lean_IR_EmitC_emitSSet___closed__6();
lean_mark_persistent(l_Lean_IR_EmitC_emitSSet___closed__6);
l_Nat_forM_loop___at_Lean_IR_EmitC_emitJmp___spec__1___closed__1 = _init_l_Nat_forM_loop___at_Lean_IR_EmitC_emitJmp___spec__1___closed__1();
lean_mark_persistent(l_Nat_forM_loop___at_Lean_IR_EmitC_emitJmp___spec__1___closed__1);
l_Lean_IR_EmitC_emitJmp___lambda__1___closed__1 = _init_l_Lean_IR_EmitC_emitJmp___lambda__1___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_emitJmp___lambda__1___closed__1);
l_Lean_IR_EmitC_emitJmp___lambda__1___closed__2 = _init_l_Lean_IR_EmitC_emitJmp___lambda__1___closed__2();
lean_mark_persistent(l_Lean_IR_EmitC_emitJmp___lambda__1___closed__2);
l_Lean_IR_EmitC_emitJmp___closed__1 = _init_l_Lean_IR_EmitC_emitJmp___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_emitJmp___closed__1);
l_Lean_IR_EmitC_emitCtorScalarSize___closed__1 = _init_l_Lean_IR_EmitC_emitCtorScalarSize___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_emitCtorScalarSize___closed__1);
l_Lean_IR_EmitC_emitAllocCtor___closed__1 = _init_l_Lean_IR_EmitC_emitAllocCtor___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_emitAllocCtor___closed__1);
l_Lean_IR_EmitC_emitCtor___closed__1 = _init_l_Lean_IR_EmitC_emitCtor___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_emitCtor___closed__1);
l_Nat_forM_loop___at_Lean_IR_EmitC_emitReset___spec__1___closed__1 = _init_l_Nat_forM_loop___at_Lean_IR_EmitC_emitReset___spec__1___closed__1();
lean_mark_persistent(l_Nat_forM_loop___at_Lean_IR_EmitC_emitReset___spec__1___closed__1);
l_Lean_IR_EmitC_emitReset___closed__1 = _init_l_Lean_IR_EmitC_emitReset___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_emitReset___closed__1);
l_Lean_IR_EmitC_emitReset___closed__2 = _init_l_Lean_IR_EmitC_emitReset___closed__2();
lean_mark_persistent(l_Lean_IR_EmitC_emitReset___closed__2);
l_Lean_IR_EmitC_emitReset___closed__3 = _init_l_Lean_IR_EmitC_emitReset___closed__3();
lean_mark_persistent(l_Lean_IR_EmitC_emitReset___closed__3);
l_Lean_IR_EmitC_emitReset___closed__4 = _init_l_Lean_IR_EmitC_emitReset___closed__4();
lean_mark_persistent(l_Lean_IR_EmitC_emitReset___closed__4);
l_Lean_IR_EmitC_emitReuse___closed__1 = _init_l_Lean_IR_EmitC_emitReuse___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_emitReuse___closed__1);
l_Lean_IR_EmitC_emitReuse___closed__2 = _init_l_Lean_IR_EmitC_emitReuse___closed__2();
lean_mark_persistent(l_Lean_IR_EmitC_emitReuse___closed__2);
l_Lean_IR_EmitC_emitProj___closed__1 = _init_l_Lean_IR_EmitC_emitProj___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_emitProj___closed__1);
l_Lean_IR_EmitC_emitUProj___closed__1 = _init_l_Lean_IR_EmitC_emitUProj___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_emitUProj___closed__1);
l_Lean_IR_EmitC_emitSProj___closed__1 = _init_l_Lean_IR_EmitC_emitSProj___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_emitSProj___closed__1);
l_Lean_IR_EmitC_emitSProj___closed__2 = _init_l_Lean_IR_EmitC_emitSProj___closed__2();
lean_mark_persistent(l_Lean_IR_EmitC_emitSProj___closed__2);
l_Lean_IR_EmitC_emitSProj___closed__3 = _init_l_Lean_IR_EmitC_emitSProj___closed__3();
lean_mark_persistent(l_Lean_IR_EmitC_emitSProj___closed__3);
l_Lean_IR_EmitC_emitSProj___closed__4 = _init_l_Lean_IR_EmitC_emitSProj___closed__4();
lean_mark_persistent(l_Lean_IR_EmitC_emitSProj___closed__4);
l_Lean_IR_EmitC_emitSProj___closed__5 = _init_l_Lean_IR_EmitC_emitSProj___closed__5();
lean_mark_persistent(l_Lean_IR_EmitC_emitSProj___closed__5);
l_Lean_IR_EmitC_emitExternCall___closed__1 = _init_l_Lean_IR_EmitC_emitExternCall___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_emitExternCall___closed__1);
l_Nat_forM_loop___at_Lean_IR_EmitC_emitPartialApp___spec__1___closed__1 = _init_l_Nat_forM_loop___at_Lean_IR_EmitC_emitPartialApp___spec__1___closed__1();
lean_mark_persistent(l_Nat_forM_loop___at_Lean_IR_EmitC_emitPartialApp___spec__1___closed__1);
l_Lean_IR_EmitC_emitPartialApp___closed__1 = _init_l_Lean_IR_EmitC_emitPartialApp___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_emitPartialApp___closed__1);
l_Lean_IR_EmitC_emitPartialApp___closed__2 = _init_l_Lean_IR_EmitC_emitPartialApp___closed__2();
lean_mark_persistent(l_Lean_IR_EmitC_emitPartialApp___closed__2);
l_Lean_IR_EmitC_emitApp___closed__1 = _init_l_Lean_IR_EmitC_emitApp___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_emitApp___closed__1);
l_Lean_IR_EmitC_emitApp___closed__2 = _init_l_Lean_IR_EmitC_emitApp___closed__2();
lean_mark_persistent(l_Lean_IR_EmitC_emitApp___closed__2);
l_Lean_IR_EmitC_emitApp___closed__3 = _init_l_Lean_IR_EmitC_emitApp___closed__3();
lean_mark_persistent(l_Lean_IR_EmitC_emitApp___closed__3);
l_Lean_IR_EmitC_emitApp___closed__4 = _init_l_Lean_IR_EmitC_emitApp___closed__4();
lean_mark_persistent(l_Lean_IR_EmitC_emitApp___closed__4);
l_Lean_IR_EmitC_emitApp___closed__5 = _init_l_Lean_IR_EmitC_emitApp___closed__5();
lean_mark_persistent(l_Lean_IR_EmitC_emitApp___closed__5);
l_Lean_IR_EmitC_emitBoxFn___closed__1 = _init_l_Lean_IR_EmitC_emitBoxFn___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_emitBoxFn___closed__1);
l_Lean_IR_EmitC_emitBoxFn___closed__2 = _init_l_Lean_IR_EmitC_emitBoxFn___closed__2();
lean_mark_persistent(l_Lean_IR_EmitC_emitBoxFn___closed__2);
l_Lean_IR_EmitC_emitBoxFn___closed__3 = _init_l_Lean_IR_EmitC_emitBoxFn___closed__3();
lean_mark_persistent(l_Lean_IR_EmitC_emitBoxFn___closed__3);
l_Lean_IR_EmitC_emitBoxFn___closed__4 = _init_l_Lean_IR_EmitC_emitBoxFn___closed__4();
lean_mark_persistent(l_Lean_IR_EmitC_emitBoxFn___closed__4);
l_Lean_IR_EmitC_emitBoxFn___closed__5 = _init_l_Lean_IR_EmitC_emitBoxFn___closed__5();
lean_mark_persistent(l_Lean_IR_EmitC_emitBoxFn___closed__5);
l_Lean_IR_EmitC_emitUnbox___closed__1 = _init_l_Lean_IR_EmitC_emitUnbox___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_emitUnbox___closed__1);
l_Lean_IR_EmitC_emitUnbox___closed__2 = _init_l_Lean_IR_EmitC_emitUnbox___closed__2();
lean_mark_persistent(l_Lean_IR_EmitC_emitUnbox___closed__2);
l_Lean_IR_EmitC_emitUnbox___closed__3 = _init_l_Lean_IR_EmitC_emitUnbox___closed__3();
lean_mark_persistent(l_Lean_IR_EmitC_emitUnbox___closed__3);
l_Lean_IR_EmitC_emitUnbox___closed__4 = _init_l_Lean_IR_EmitC_emitUnbox___closed__4();
lean_mark_persistent(l_Lean_IR_EmitC_emitUnbox___closed__4);
l_Lean_IR_EmitC_emitUnbox___closed__5 = _init_l_Lean_IR_EmitC_emitUnbox___closed__5();
lean_mark_persistent(l_Lean_IR_EmitC_emitUnbox___closed__5);
l_Lean_IR_EmitC_emitIsShared___closed__1 = _init_l_Lean_IR_EmitC_emitIsShared___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_emitIsShared___closed__1);
l_Lean_IR_EmitC_emitIsTaggedPtr___closed__1 = _init_l_Lean_IR_EmitC_emitIsTaggedPtr___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_emitIsTaggedPtr___closed__1);
l_Lean_IR_EmitC_quoteString___lambda__1___closed__1 = _init_l_Lean_IR_EmitC_quoteString___lambda__1___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_quoteString___lambda__1___closed__1);
l_Lean_IR_EmitC_quoteString___lambda__1___closed__2 = _init_l_Lean_IR_EmitC_quoteString___lambda__1___closed__2();
lean_mark_persistent(l_Lean_IR_EmitC_quoteString___lambda__1___closed__2);
l_Lean_IR_EmitC_quoteString___lambda__1___closed__3 = _init_l_Lean_IR_EmitC_quoteString___lambda__1___closed__3();
lean_mark_persistent(l_Lean_IR_EmitC_quoteString___lambda__1___closed__3);
l_Lean_IR_EmitC_quoteString___lambda__1___closed__4 = _init_l_Lean_IR_EmitC_quoteString___lambda__1___closed__4();
lean_mark_persistent(l_Lean_IR_EmitC_quoteString___lambda__1___closed__4);
l_Lean_IR_EmitC_quoteString___lambda__1___closed__5 = _init_l_Lean_IR_EmitC_quoteString___lambda__1___closed__5();
lean_mark_persistent(l_Lean_IR_EmitC_quoteString___lambda__1___closed__5);
l_Lean_IR_EmitC_quoteString___lambda__1___closed__6 = _init_l_Lean_IR_EmitC_quoteString___lambda__1___closed__6();
lean_mark_persistent(l_Lean_IR_EmitC_quoteString___lambda__1___closed__6);
l_Lean_IR_EmitC_quoteString___closed__1 = _init_l_Lean_IR_EmitC_quoteString___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_quoteString___closed__1);
l_Lean_IR_EmitC_quoteString___closed__2 = _init_l_Lean_IR_EmitC_quoteString___closed__2();
lean_mark_persistent(l_Lean_IR_EmitC_quoteString___closed__2);
l_Lean_IR_EmitC_emitNumLit___closed__1 = _init_l_Lean_IR_EmitC_emitNumLit___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_emitNumLit___closed__1);
l_Lean_IR_EmitC_emitNumLit___closed__2 = _init_l_Lean_IR_EmitC_emitNumLit___closed__2();
lean_mark_persistent(l_Lean_IR_EmitC_emitNumLit___closed__2);
l_Lean_IR_EmitC_emitNumLit___closed__3 = _init_l_Lean_IR_EmitC_emitNumLit___closed__3();
lean_mark_persistent(l_Lean_IR_EmitC_emitNumLit___closed__3);
l_Lean_IR_EmitC_emitNumLit___closed__4 = _init_l_Lean_IR_EmitC_emitNumLit___closed__4();
lean_mark_persistent(l_Lean_IR_EmitC_emitNumLit___closed__4);
l_Lean_IR_EmitC_emitLit___closed__1 = _init_l_Lean_IR_EmitC_emitLit___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_emitLit___closed__1);
l_Nat_forM_loop___at_Lean_IR_EmitC_emitTailCall___spec__2___closed__1 = _init_l_Nat_forM_loop___at_Lean_IR_EmitC_emitTailCall___spec__2___closed__1();
lean_mark_persistent(l_Nat_forM_loop___at_Lean_IR_EmitC_emitTailCall___spec__2___closed__1);
l_Nat_forM_loop___at_Lean_IR_EmitC_emitTailCall___spec__3___closed__1 = _init_l_Nat_forM_loop___at_Lean_IR_EmitC_emitTailCall___spec__3___closed__1();
lean_mark_persistent(l_Nat_forM_loop___at_Lean_IR_EmitC_emitTailCall___spec__3___closed__1);
l_Lean_IR_EmitC_emitTailCall___lambda__1___closed__1 = _init_l_Lean_IR_EmitC_emitTailCall___lambda__1___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_emitTailCall___lambda__1___closed__1);
l_Lean_IR_EmitC_emitTailCall___lambda__2___closed__1 = _init_l_Lean_IR_EmitC_emitTailCall___lambda__2___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_emitTailCall___lambda__2___closed__1);
l_Lean_IR_EmitC_emitTailCall___lambda__2___closed__2 = _init_l_Lean_IR_EmitC_emitTailCall___lambda__2___closed__2();
lean_mark_persistent(l_Lean_IR_EmitC_emitTailCall___lambda__2___closed__2);
l_Lean_IR_EmitC_emitTailCall___closed__1 = _init_l_Lean_IR_EmitC_emitTailCall___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_emitTailCall___closed__1);
l_Lean_IR_EmitC_emitTailCall___closed__2 = _init_l_Lean_IR_EmitC_emitTailCall___closed__2();
lean_mark_persistent(l_Lean_IR_EmitC_emitTailCall___closed__2);
l_Lean_IR_EmitC_emitIf___closed__1 = _init_l_Lean_IR_EmitC_emitIf___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_emitIf___closed__1);
l_Lean_IR_EmitC_emitIf___closed__2 = _init_l_Lean_IR_EmitC_emitIf___closed__2();
lean_mark_persistent(l_Lean_IR_EmitC_emitIf___closed__2);
l_Lean_IR_EmitC_emitIf___closed__3 = _init_l_Lean_IR_EmitC_emitIf___closed__3();
lean_mark_persistent(l_Lean_IR_EmitC_emitIf___closed__3);
l_Lean_IR_EmitC_emitJPs___closed__1 = _init_l_Lean_IR_EmitC_emitJPs___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_emitJPs___closed__1);
l_Lean_IR_EmitC_emitBlock___closed__1 = _init_l_Lean_IR_EmitC_emitBlock___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_emitBlock___closed__1);
l_Lean_IR_EmitC_emitBlock___closed__2 = _init_l_Lean_IR_EmitC_emitBlock___closed__2();
lean_mark_persistent(l_Lean_IR_EmitC_emitBlock___closed__2);
l_Array_foldlMUnsafe_fold___at_Lean_IR_EmitC_emitCase___spec__1___closed__1 = _init_l_Array_foldlMUnsafe_fold___at_Lean_IR_EmitC_emitCase___spec__1___closed__1();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lean_IR_EmitC_emitCase___spec__1___closed__1);
l_Array_foldlMUnsafe_fold___at_Lean_IR_EmitC_emitCase___spec__1___closed__2 = _init_l_Array_foldlMUnsafe_fold___at_Lean_IR_EmitC_emitCase___spec__1___closed__2();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lean_IR_EmitC_emitCase___spec__1___closed__2);
l_Lean_IR_EmitC_emitCase___closed__1 = _init_l_Lean_IR_EmitC_emitCase___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_emitCase___closed__1);
l_Lean_IR_EmitC_emitCase___closed__2 = _init_l_Lean_IR_EmitC_emitCase___closed__2();
lean_mark_persistent(l_Lean_IR_EmitC_emitCase___closed__2);
l_Nat_forM_loop___at_Lean_IR_EmitC_emitDeclAux___spec__1___closed__1 = _init_l_Nat_forM_loop___at_Lean_IR_EmitC_emitDeclAux___spec__1___closed__1();
lean_mark_persistent(l_Nat_forM_loop___at_Lean_IR_EmitC_emitDeclAux___spec__1___closed__1);
l_Nat_forM_loop___at_Lean_IR_EmitC_emitDeclAux___spec__1___closed__2 = _init_l_Nat_forM_loop___at_Lean_IR_EmitC_emitDeclAux___spec__1___closed__2();
lean_mark_persistent(l_Nat_forM_loop___at_Lean_IR_EmitC_emitDeclAux___spec__1___closed__2);
l_Nat_forM_loop___at_Lean_IR_EmitC_emitDeclAux___spec__1___closed__3 = _init_l_Nat_forM_loop___at_Lean_IR_EmitC_emitDeclAux___spec__1___closed__3();
lean_mark_persistent(l_Nat_forM_loop___at_Lean_IR_EmitC_emitDeclAux___spec__1___closed__3);
l_Lean_IR_EmitC_emitDeclAux___lambda__1___closed__1 = _init_l_Lean_IR_EmitC_emitDeclAux___lambda__1___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_emitDeclAux___lambda__1___closed__1);
l_Lean_IR_EmitC_emitDeclAux___lambda__2___closed__1 = _init_l_Lean_IR_EmitC_emitDeclAux___lambda__2___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_emitDeclAux___lambda__2___closed__1);
l_Lean_IR_EmitC_emitDeclAux___lambda__3___closed__1 = _init_l_Lean_IR_EmitC_emitDeclAux___lambda__3___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_emitDeclAux___lambda__3___closed__1);
l_Lean_IR_EmitC_emitDeclAux___lambda__3___closed__2 = _init_l_Lean_IR_EmitC_emitDeclAux___lambda__3___closed__2();
lean_mark_persistent(l_Lean_IR_EmitC_emitDeclAux___lambda__3___closed__2);
l_Lean_IR_EmitC_emitDecl___closed__1 = _init_l_Lean_IR_EmitC_emitDecl___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_emitDecl___closed__1);
l_Lean_IR_EmitC_emitMarkPersistent___closed__1 = _init_l_Lean_IR_EmitC_emitMarkPersistent___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_emitMarkPersistent___closed__1);
l_Lean_IR_EmitC_emitDeclInit___lambda__1___closed__1 = _init_l_Lean_IR_EmitC_emitDeclInit___lambda__1___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_emitDeclInit___lambda__1___closed__1);
l_Lean_IR_EmitC_emitDeclInit___lambda__1___closed__2 = _init_l_Lean_IR_EmitC_emitDeclInit___lambda__1___closed__2();
lean_mark_persistent(l_Lean_IR_EmitC_emitDeclInit___lambda__1___closed__2);
l_Lean_IR_EmitC_emitDeclInit___lambda__1___closed__3 = _init_l_Lean_IR_EmitC_emitDeclInit___lambda__1___closed__3();
lean_mark_persistent(l_Lean_IR_EmitC_emitDeclInit___lambda__1___closed__3);
l_Lean_IR_EmitC_emitDeclInit___closed__1 = _init_l_Lean_IR_EmitC_emitDeclInit___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_emitDeclInit___closed__1);
l_Lean_IR_EmitC_emitDeclInit___closed__2 = _init_l_Lean_IR_EmitC_emitDeclInit___closed__2();
lean_mark_persistent(l_Lean_IR_EmitC_emitDeclInit___closed__2);
l_Array_foldlMUnsafe_fold___at_Lean_IR_EmitC_emitInitFn___spec__2___closed__1 = _init_l_Array_foldlMUnsafe_fold___at_Lean_IR_EmitC_emitInitFn___spec__2___closed__1();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lean_IR_EmitC_emitInitFn___spec__2___closed__1);
l_Array_foldlMUnsafe_fold___at_Lean_IR_EmitC_emitInitFn___spec__3___closed__1 = _init_l_Array_foldlMUnsafe_fold___at_Lean_IR_EmitC_emitInitFn___spec__3___closed__1();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lean_IR_EmitC_emitInitFn___spec__3___closed__1);
l_Lean_IR_EmitC_emitInitFn___closed__1 = _init_l_Lean_IR_EmitC_emitInitFn___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_emitInitFn___closed__1);
l_Lean_IR_EmitC_emitInitFn___closed__2 = _init_l_Lean_IR_EmitC_emitInitFn___closed__2();
lean_mark_persistent(l_Lean_IR_EmitC_emitInitFn___closed__2);
l_Lean_IR_EmitC_emitInitFn___closed__3 = _init_l_Lean_IR_EmitC_emitInitFn___closed__3();
lean_mark_persistent(l_Lean_IR_EmitC_emitInitFn___closed__3);
l_Lean_IR_EmitC_emitInitFn___closed__4 = _init_l_Lean_IR_EmitC_emitInitFn___closed__4();
lean_mark_persistent(l_Lean_IR_EmitC_emitInitFn___closed__4);
l_Lean_IR_EmitC_emitInitFn___closed__5 = _init_l_Lean_IR_EmitC_emitInitFn___closed__5();
lean_mark_persistent(l_Lean_IR_EmitC_emitInitFn___closed__5);
l_Lean_IR_EmitC_emitInitFn___closed__6 = _init_l_Lean_IR_EmitC_emitInitFn___closed__6();
lean_mark_persistent(l_Lean_IR_EmitC_emitInitFn___closed__6);
l_Lean_IR_EmitC_emitInitFn___closed__7 = _init_l_Lean_IR_EmitC_emitInitFn___closed__7();
lean_mark_persistent(l_Lean_IR_EmitC_emitInitFn___closed__7);
l_Lean_IR_EmitC_emitInitFn___closed__8 = _init_l_Lean_IR_EmitC_emitInitFn___closed__8();
lean_mark_persistent(l_Lean_IR_EmitC_emitInitFn___closed__8);
l_Lean_IR_EmitC_emitInitFn___closed__9 = _init_l_Lean_IR_EmitC_emitInitFn___closed__9();
lean_mark_persistent(l_Lean_IR_EmitC_emitInitFn___closed__9);
l_Lean_IR_EmitC_emitInitFn___closed__10 = _init_l_Lean_IR_EmitC_emitInitFn___closed__10();
lean_mark_persistent(l_Lean_IR_EmitC_emitInitFn___closed__10);
l_Lean_IR_EmitC_emitInitFn___closed__11 = _init_l_Lean_IR_EmitC_emitInitFn___closed__11();
lean_mark_persistent(l_Lean_IR_EmitC_emitInitFn___closed__11);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
