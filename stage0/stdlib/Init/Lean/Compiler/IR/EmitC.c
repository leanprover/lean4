// Lean compiler output
// Module: Init.Lean.Compiler.IR.EmitC
// Imports: Init.Control.Conditional Init.Lean.Runtime Init.Lean.Compiler.NameMangling Init.Lean.Compiler.ExportAttr Init.Lean.Compiler.InitAttr Init.Lean.Compiler.IR.CompilerM Init.Lean.Compiler.IR.EmitUtil Init.Lean.Compiler.IR.NormIds Init.Lean.Compiler.IR.SimpCase Init.Lean.Compiler.IR.Boxing
#include "runtime/lean.h"
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
lean_object* l_List_reverse___rarg(lean_object*);
lean_object* l_Lean_IR_EmitC_emitMarkPersistent___closed__1;
lean_object* l_Lean_IR_EmitC_emitCase___closed__1;
lean_object* l_Lean_IR_EmitC_argToCString___closed__1;
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* l_Lean_IR_EmitC_toStringArgs(lean_object*);
lean_object* l_Lean_IR_EmitC_emitSProj___closed__4;
lean_object* l_Lean_IR_EmitC_toCType___closed__7;
lean_object* l_Lean_IR_EmitC_emitFileHeader___closed__1;
lean_object* l_Lean_IR_EmitC_emitCInitName(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_toCName___closed__3;
lean_object* l_Lean_IR_EmitC_emitMainFn___closed__6;
lean_object* l_Lean_IR_EmitC_emitMainFn___closed__44;
extern uint8_t l_String_anyAux___main___at_String_all___spec__1___closed__1;
lean_object* l_Lean_IR_EmitC_emitMarkPersistent___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitUnbox___closed__4;
lean_object* l_Array_forMAux___main___at_Lean_IR_EmitC_declareParams___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Nat_anyAux___main___at_Lean_IR_EmitC_overwriteParam___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitFileHeader___closed__4;
lean_object* l_Lean_IR_EmitC_emitSetTag(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitProj(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitDel___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitMainFn___closed__1;
lean_object* l_Lean_IR_EmitC_emitFileHeader___closed__8;
lean_object* l_Lean_IR_EmitC_emitFileHeader___boxed(lean_object*, lean_object*);
lean_object* l_Nat_forMAux___main___at_Lean_IR_EmitC_emitArgs___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitDel___closed__1;
extern lean_object* l_Lean_IR_formatFnBodyHead___closed__29;
lean_object* l_Lean_IR_EmitC_emit(lean_object*);
lean_object* l_Lean_IR_EmitC_emitFileHeader___closed__17;
lean_object* l_Lean_IR_EmitC_emitIsShared(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_throwUnknownVar___rarg___closed__1;
lean_object* l_Lean_IR_EmitC_emitFnDecls___boxed(lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitInitFn___closed__10;
lean_object* l_Lean_IR_EmitC_emitBlock___main(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_declareVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_forMAux___main___at_Lean_IR_EmitC_emitTailCall___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitCase___closed__2;
lean_object* l_Lean_IR_EmitC_emitFileHeader___closed__11;
lean_object* l_Lean_IR_EmitC_emitFnDeclAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitAllocCtor___closed__1;
lean_object* l_Lean_IR_EmitC_emitCName___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitFnDeclAux(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitMainFn___closed__2;
lean_object* l_Nat_foldMAux___main___at_Lean_IR_EmitC_emitSimpleExternalCall___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitCtor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_foldr___main___at_Lean_IR_EmitC_hasMainFn___spec__1(uint8_t, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_IR_EmitC_emitAllocCtor___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_toCType___closed__3;
lean_object* l_Lean_IR_EmitC_emitInc___closed__3;
lean_object* l_Lean_IR_EmitC_emitMainFn___closed__11;
extern uint8_t l_String_Iterator_extract___closed__1;
lean_object* l_Lean_IR_EmitC_emitFileHeader___closed__9;
lean_object* l_Lean_IR_EmitC_getDecl___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_toHexDigit(lean_object*);
lean_object* l_Lean_Environment_imports(lean_object*);
lean_object* l_Lean_IR_EmitC_emitSProj___closed__2;
lean_object* l_Lean_IR_EmitC_throwUnknownVar___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_forMAux___main___at_Lean_IR_EmitC_emitDeclAux___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_forMAux___main___at_Lean_IR_EmitC_emitCtorSetArgs___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_collectUsedDecls(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitSSet___closed__6;
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitInc___closed__5;
extern lean_object* l_Prod_HasRepr___rarg___closed__1;
lean_object* l_Lean_IR_EmitC_emitSProj___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_anyAux___main___at_Lean_IR_EmitC_overwriteParam___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitDeclAux___closed__3;
lean_object* l_Lean_IR_EmitC_emitMainFn___closed__51;
lean_object* l_Lean_IR_EmitC_emitMainFn___closed__19;
lean_object* l_Lean_IR_EmitC_emitSProj___closed__1;
lean_object* l_Lean_IR_EmitC_emitMainFn___closed__41;
lean_object* l_Nat_forMAux___main___at_Lean_IR_EmitC_emitDeclAux___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitMainFn___closed__13;
extern lean_object* l_Array_empty___closed__1;
lean_object* l_Lean_IR_EmitC_emitSProj(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_getEnv___boxed(lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_toCType___closed__5;
lean_object* l___private_Init_Util_1__mkPanicMessage(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitUnbox___closed__2;
lean_object* l_Lean_IR_EmitC_emitVDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitMainFn___closed__47;
lean_object* l_Lean_expandExternPattern(lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitDel(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_closureMaxArgs;
uint8_t l_Lean_IR_IRType_isIrrelevant(lean_object*);
lean_object* l_Lean_IR_EmitC_emitMarkPersistent(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___main___at_Lean_IR_EmitC_toStringArgs___spec__1(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitApp___closed__3;
lean_object* lean_ir_emit_c(lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitMainFn___closed__35;
lean_object* l_Nat_forMAux___main___at_Lean_IR_EmitC_emitTailCall___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitApp___closed__5;
lean_object* l_Lean_IR_EmitC_emitLhs___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitReset___closed__4;
extern lean_object* l_Unit_HasRepr___closed__1;
lean_object* l_Lean_IR_EmitC_emitFileHeader___closed__19;
lean_object* l_Lean_IR_EmitC_emitFnDeclAux___closed__1;
lean_object* l_Nat_forMAux___main___at_Lean_IR_EmitC_emitTailCall___spec__3___closed__1;
lean_object* l_Lean_IR_EmitC_emitLn___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitDeclInit___closed__3;
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_IR_EmitC_emitReuse___closed__2;
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitFnDecl(lean_object*, uint8_t, lean_object*, lean_object*);
extern lean_object* l_String_splitAux___main___closed__1;
lean_object* l_Lean_IR_EmitC_toStringArgs___boxed(lean_object*);
lean_object* l_Lean_getExternNameFor(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_forMAux___main___at_Lean_IR_EmitC_emitArgs___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitMainFn___closed__39;
extern lean_object* l_String_quote___closed__1;
lean_object* l_Nat_anyAux___main___at_Lean_IR_EmitC_overwriteParam___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_quoteString___boxed(lean_object*);
lean_object* l_Lean_IR_EmitC_emitBlock___main___closed__2;
lean_object* l_Lean_IR_EmitC_emitSet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitMainFn___closed__46;
lean_object* l_List_forM___main___at_Lean_IR_EmitC_emitInitFn___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitCase___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_hasMainFn___boxed(lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitUnbox___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_Lean_IR_EmitC_emitCtorScalarSize(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_isTailCallTo(lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_throwUnknownVar___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitInitFn(lean_object*, lean_object*);
uint8_t l_Nat_anyAux___main___at_Lean_IR_EmitC_overwriteParam___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_declareVars(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitCtorSetArgs(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitMainFn___closed__25;
lean_object* l_Lean_IR_EmitC_emitUnbox___closed__1;
uint8_t l_Lean_IR_IRType_isObj(lean_object*);
lean_object* l_Nat_forMAux___main___at_Lean_IR_EmitC_emitDeclAux___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitFnDecls(lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitOffset___closed__2;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitApp___closed__4;
lean_object* l_Lean_IR_EmitC_emitMainFn___closed__8;
lean_object* l_Lean_IR_EmitC_emitJmp___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_toCType___closed__6;
lean_object* l_Lean_IR_Decl_resultType(lean_object*);
lean_object* l_Array_filterAux___main___at_Lean_IR_EmitC_emitFnDeclAux___spec__2(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Char_quoteCore___closed__1;
lean_object* l_Lean_IR_Decl_name(lean_object*);
lean_object* l_Lean_IR_EmitC_emitInc___closed__2;
lean_object* l_Lean_IR_EmitC_emitArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_toCInitName___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitLns___at_Lean_IR_EmitC_emitMainFn___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitFileHeader___closed__25;
lean_object* l_Lean_IR_EmitC_emitJmp___closed__1;
lean_object* l_Lean_IR_EmitC_toCInitName___closed__1;
lean_object* l_Lean_IR_EmitC_leanMainFn___closed__1;
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_main(lean_object*, lean_object*);
extern lean_object* l_Char_quoteCore___closed__2;
lean_object* l_Lean_IR_EmitC_emit___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_IR_Arg_Inhabited;
lean_object* l_HashMapImp_find___at_Lean_IR_EmitC_getJPParams___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitMainFn___closed__4;
lean_object* l_Lean_IR_EmitC_emitIf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitReset(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at_Lean_IR_EmitC_emitFileHeader___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitMainFn___closed__31;
lean_object* l_Lean_IR_AltCore_body(lean_object*);
lean_object* l_Lean_IR_EmitC_argToCString(lean_object*);
lean_object* l_Lean_IR_EmitC_emitFileHeader___closed__6;
lean_object* l_Lean_IR_EmitC_emitReset___closed__3;
uint8_t l_Lean_isExternC(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_isIf___boxed(lean_object*);
lean_object* l_RBNode_revFold___main___at_Lean_IR_EmitC_emitFnDecls___spec__4(lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitCtorScalarSize___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitMainFn___closed__43;
lean_object* l_Lean_IR_EmitC_emitCtorScalarSize___closed__1;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitApp___closed__2;
lean_object* l_Lean_IR_EmitC_toCInitName(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_overwriteParam___boxed(lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitJPs___main(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_forMAux___main___at_Lean_IR_EmitC_emitTailCall___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitTag___closed__1;
lean_object* l_Lean_IR_EmitC_emitTailCall(lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldl___main___at_Lean_IR_EmitC_emitFnDecls___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitUProj(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitTag___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitApp___closed__1;
lean_object* l_Lean_IR_EmitC_emitInitFn___closed__5;
lean_object* l_List_forM___main___at_Lean_IR_EmitC_emitFns___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_toCType___closed__2;
lean_object* l_Array_shrink___main___rarg(lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitExternCall___closed__1;
lean_object* l_Nat_forMAux___main___at_Lean_IR_EmitC_emitDeclAux___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_toHexDigit___boxed(lean_object*);
lean_object* l_Nat_forMAux___main___at_Lean_IR_EmitC_emitPartialApp___spec__1___closed__1;
lean_object* l_Lean_IR_EmitC_emitNumLit___closed__3;
lean_object* l_Lean_IR_EmitC_emitCtor___closed__1;
lean_object* l_Lean_IR_EmitC_emitExternCall___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_foldlAux___main___at_Lean_IR_EmitC_quoteString___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitLns___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitLhs(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitCtor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitSimpleExternalCall___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitBoxFn___closed__4;
lean_object* l_Lean_IR_EmitC_emitJmp(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_foldlAux___main___at_Lean_IR_EmitC_quoteString___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_forMAux___main___at_Lean_IR_EmitC_emitPartialApp___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitJmp___closed__2;
lean_object* l_Lean_IR_EmitC_emitMainFnIfNeeded(lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitFileHeader___closed__13;
lean_object* l_Lean_IR_EmitC_hasMainFn(lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitOffset___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_forMAux___main___at_Lean_IR_EmitC_emitFnDeclAux___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_FnBody_isTerminal(lean_object*);
lean_object* l_Lean_IR_EmitC_emitFileHeader___closed__23;
lean_object* l_Lean_IR_EmitC_emitIf___closed__2;
lean_object* l_Lean_IR_EmitC_emitArgs(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_forMAux___main___at_Lean_IR_EmitC_emitDeclAux___spec__1___closed__1;
extern lean_object* l_Lean_IR_formatDecl___closed__3;
lean_object* l_Lean_IR_EmitC_emitPartialApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitBox___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldl___main___at_Lean_IR_EmitC_emitFnDecls___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_toCName___closed__1;
lean_object* l_Nat_repr(lean_object*);
extern lean_object* l_Char_HasRepr___closed__1;
lean_object* l_Lean_IR_EmitC_toCType___closed__8;
extern lean_object* l_Lean_IR_paramInh;
lean_object* l_Lean_IR_EmitC_emitDeclInit___closed__2;
lean_object* l_Lean_IR_EmitC_emitDeclInit___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitSet___closed__1;
lean_object* l_Lean_IR_EmitC_emitBox(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_forM___main___at_Lean_IR_EmitC_emitMainFn___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitSet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitMainFn___closed__45;
lean_object* l_Lean_IR_EmitC_emitReset___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitOffset___closed__1;
lean_object* l_Lean_IR_EmitC_toCName___closed__2;
lean_object* l_Lean_IR_EmitC_emitFnBody___main(lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitDeclInit___closed__1;
lean_object* l_Lean_IR_EmitC_emitIf___closed__3;
lean_object* l_Lean_IR_EmitC_emitArgs___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitMainFn___closed__40;
lean_object* l_Lean_IR_EmitC_toCType___boxed(lean_object*);
lean_object* l_Lean_IR_EmitC_emitMainFn___closed__9;
lean_object* l_Lean_IR_EmitC_emitReset___closed__1;
lean_object* l_Lean_IR_EmitC_emitSProj___closed__3;
extern lean_object* l_List_reprAux___main___rarg___closed__1;
extern lean_object* l_Lean_IR_formatFnBody___main___closed__1;
lean_object* l_Lean_IR_EmitC_emitFileHeader___closed__21;
extern lean_object* l_IO_println___rarg___closed__1;
lean_object* l_Lean_IR_EmitC_toCName(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitInitFn___closed__7;
lean_object* l_Lean_IR_EmitC_emitFullApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitMainFn___closed__27;
lean_object* l_Lean_IR_EmitC_emitDeclInit(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitIf___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_forMAux___main___at_Lean_IR_EmitC_emitDeclAux___spec__1___closed__2;
extern lean_object* l_Lean_IR_getDecl___closed__1;
lean_object* l_Lean_IR_EmitC_emitIf___closed__1;
lean_object* l_Lean_IR_EmitC_toCName___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitMainFn___closed__36;
lean_object* l_Lean_IR_EmitC_emitFileHeader___closed__2;
lean_object* l_Lean_SimplePersistentEnvExtension_getEntries___rarg(lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_toCType___closed__1;
lean_object* l_List_forM___main___at_Lean_IR_EmitC_emitLns___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitInc(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitMainFn___closed__17;
lean_object* l_Lean_IR_EmitC_leanMainFn;
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitNumLit___closed__4;
lean_object* l_Array_forMAux___main___at_Lean_IR_EmitC_emitInitFn___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitDecl___closed__1;
lean_object* l_Lean_IR_EmitC_emitInitFn___boxed(lean_object*, lean_object*);
uint32_t l_Nat_digitChar(lean_object*);
size_t lean_usize_modn(size_t, lean_object*);
lean_object* l_Lean_IR_EmitC_throwInvalidExportName(lean_object*);
lean_object* l_Lean_IR_EmitC_emitFileHeader___closed__16;
lean_object* l_Array_forMAux___main___at_Lean_IR_EmitC_emitFileHeader___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_declareVar(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_toCType___closed__9;
uint8_t l_Array_isEmpty___rarg(lean_object*);
lean_object* l_Lean_IR_EmitC_emitIsShared___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitInitFn___closed__1;
extern lean_object* l_String_Iterator_HasRepr___closed__2;
lean_object* l_Lean_IR_EmitC_emitIsTaggedPtr___closed__1;
lean_object* l_Nat_forMAux___main___at_Lean_IR_EmitC_emitReset___spec__1___closed__1;
lean_object* l_Lean_IR_EmitC_declareVars___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitBoxFn___closed__2;
lean_object* l_Lean_IR_EmitC_toCType___closed__4;
lean_object* l_Lean_IR_EmitC_emitProj___closed__1;
lean_object* l_Lean_IR_EmitC_emitIsShared___closed__1;
lean_object* l_Lean_IR_EmitC_emitDeclAux___closed__2;
lean_object* l_List_forM___main___at_Lean_IR_EmitC_emitFnDecls___spec__5___closed__2;
lean_object* l_Lean_IR_EmitC_emitMainFn(lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitVDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_HashMapImp_find___at_Lean_IR_EmitC_getJPParams___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitMainFn___closed__32;
lean_object* l_Nat_forMAux___main___at_Lean_IR_EmitC_emitJmp___spec__1___closed__1;
lean_object* l_Lean_IR_EmitC_emitMainFn___closed__10;
lean_object* l_Nat_forMAux___main___at_Lean_IR_EmitC_emitReset___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_RBNode_insert___at_Lean_NameSet_insert___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitFileHeader___closed__14;
lean_object* l_Lean_IR_EmitC_emitMainFn___closed__20;
lean_object* l_Lean_IR_EmitC_emitFileHeader___closed__7;
lean_object* l_Lean_IR_EmitC_emitUProj___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitCInitName___boxed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_IR_EmitC_emitReuse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitFnBody(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_ensureHasDefault(lean_object*);
lean_object* l_Lean_IR_EmitC_emitMainFn___closed__14;
lean_object* l_Lean_IR_EmitC_emitUProj___closed__1;
lean_object* l_Lean_IR_EmitC_emitUnbox___closed__3;
lean_object* l_Lean_IR_EmitC_emitBoxFn___closed__3;
lean_object* l_Lean_IR_EmitC_emitNumLit(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitExternCall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitMainFn___closed__28;
extern lean_object* l_Lean_HasToString___closed__1;
lean_object* l_Lean_IR_EmitC_emitMainFn___closed__5;
lean_object* lean_ir_decl_to_string(lean_object*);
uint8_t l_Lean_hasInitAttr(lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitMainFn___closed__30;
extern lean_object* l_Lean_exportAttr;
lean_object* l_Lean_IR_EmitC_emitSimpleExternalCall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Char_quoteCore___closed__3;
lean_object* l_Lean_IR_EmitC_emitUSet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_forMAux___main___at_Lean_IR_EmitC_emitJmp___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitMainFn___closed__33;
lean_object* l_Lean_IR_EmitC_emitFnDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_declareParams(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitMainFn___closed__3;
lean_object* l_List_foldl___main___at_Lean_IR_EmitC_emitFnDecls___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitReset___closed__2;
lean_object* l_List_forM___main___at_Lean_IR_EmitC_emitInitFn___spec__3___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitAllocCtor(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_usesLeanNamespace(lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitLn___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Option_HasRepr___rarg___closed__3;
lean_object* l_Array_forMAux___main___at_Lean_IR_EmitC_emitInitFn___spec__1___closed__1;
lean_object* l_Array_forMAux___main___at_Lean_IR_EmitC_emitInitFn___spec__1___closed__2;
lean_object* l_Nat_foldMAux___main___at_Lean_IR_EmitC_emitSimpleExternalCall___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitLit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitMainFn___closed__42;
extern lean_object* l_PersistentArray_Stats_toString___closed__4;
lean_object* l_Lean_IR_EmitC_emitExternDeclAux(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_declareParams___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitFileHeader___closed__15;
lean_object* l_Lean_IR_EmitC_emitDec___closed__2;
lean_object* l_Lean_IR_EmitC_emitSetTag___closed__1;
lean_object* l_Lean_IR_EmitC_emitMainFn___closed__37;
lean_object* l_Nat_forMAux___main___at_Lean_IR_EmitC_emitTailCall___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitSetTag___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitMainFnIfNeeded___boxed(lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_toCType___closed__11;
lean_object* l_Lean_IR_EmitC_emitFileHeader___closed__3;
lean_object* l_Lean_IR_EmitC_emitReuse(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitLns(lean_object*);
lean_object* l_Lean_IR_EmitC_paramEqArg___boxed(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitFileHeader(lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at_Lean_IR_EmitC_emitInitFn___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitDeclAux(lean_object*, lean_object*, lean_object*);
lean_object* l_List_forM___main___at_Lean_IR_EmitC_emitMainFn___spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitNumLit___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitUSet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitInitFn___closed__3;
lean_object* l_Lean_IR_EmitC_emitBoxFn___closed__1;
lean_object* l_Lean_ParametricAttribute_getParam___at_Lean_isIOUnitInitFn___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitInc___closed__4;
lean_object* l_Lean_IR_EmitC_emitFileHeader___closed__5;
lean_object* l_Lean_IR_EmitC_emitUSet___closed__1;
lean_object* l_Lean_IR_EmitC_emitFnBody___main___closed__1;
lean_object* l_panic(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_forMAux___main___at_Lean_IR_EmitC_emitTailCall___spec__2___closed__1;
lean_object* l_Lean_IR_EmitC_emitNumLit___closed__2;
lean_object* l_Lean_IR_EmitC_isTailCall___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitBoxFn___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_forMAux___main___at_Lean_IR_EmitC_emitTailCall___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_IR_altInh;
lean_object* l_Lean_IR_EmitC_emitFileHeader___closed__22;
lean_object* l_Lean_IR_EmitC_emitFileFooter___closed__1;
lean_object* l_Nat_forMAux___main___at_Lean_IR_EmitC_emitTailCall___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitFileHeader___closed__18;
lean_object* l_Lean_IR_EmitC_emitMainFn___closed__12;
uint8_t l_Lean_IR_ExplicitBoxing_isBoxedName(lean_object*);
extern lean_object* l___private_Init_Util_1__mkPanicMessage___closed__2;
lean_object* l_Lean_IR_EmitC_emitIsTaggedPtr(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_IR_JoinPointId_HasToString___closed__1;
lean_object* l_Lean_IR_EmitC_emitInitFn___closed__6;
lean_object* l_Lean_IR_EmitC_emitProj___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_EmitC_overwriteParam(lean_object*, lean_object*);
uint8_t l_Lean_isIOUnitInitFn(lean_object*, lean_object*);
lean_object* l_Lean_getExternEntryFor(lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitNumLit___closed__1;
lean_object* l_Lean_IR_EmitC_emitMainFn___closed__26;
lean_object* l_Nat_forMAux___main___at_Lean_IR_EmitC_emitFnDeclAux___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitSSet___closed__5;
lean_object* l_Lean_IR_EmitC_emitApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitBlock___main___closed__1;
extern lean_object* l_uint32Sz;
lean_object* l_Array_forMAux___main___at_Lean_IR_EmitC_emitCase___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitTag(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_declareVars___main(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitMainFn___closed__7;
lean_object* l_Array_forMAux___main___at_Lean_IR_EmitC_emitCase___spec__1___closed__1;
lean_object* l_Lean_IR_EmitC_emitDecl(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_throwUnknownVar(lean_object*);
lean_object* l_Lean_IR_EmitC_isIf(lean_object*);
lean_object* l_Lean_IR_EmitC_emitTailCall___closed__2;
lean_object* l_Lean_IR_EmitC_emitBlock(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_RBNode_revFold___main___at_Lean_IR_EmitC_emitFnDecls___spec__4___boxed(lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitSSet___closed__3;
lean_object* l_Lean_IR_EmitC_emitBoxFn(lean_object*, lean_object*, lean_object*);
uint8_t l_Char_DecidableEq(uint32_t, uint32_t);
lean_object* l_Lean_IR_EmitC_isTailCall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_throwInvalidExportName___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitFileFooter___boxed(lean_object*, lean_object*);
lean_object* lean_get_init_fn_name_for(lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitTailCall___closed__3;
lean_object* l_Lean_IR_EmitC_throwInvalidExportName___rarg___closed__1;
lean_object* l_Lean_IR_EmitC_getModName___boxed(lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitInc___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitTailCall___closed__1;
lean_object* l_Lean_IR_EmitC_emitInc___closed__1;
extern lean_object* l_Lean_IR_VarId_HasToString___closed__1;
lean_object* l_Lean_IR_EmitC_emit___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitLit___closed__1;
lean_object* l_Lean_IR_EmitC_emitFileFooter___closed__2;
lean_object* l_Lean_IR_EmitC_emitMainFn___closed__22;
lean_object* l_Lean_IR_EmitC_emitDec(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Array_toList___rarg(lean_object*);
lean_object* l_Lean_IR_EmitC_emitDec___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_forMAux___main___at_Lean_IR_EmitC_emitDeclAux___spec__1___closed__3;
lean_object* l_Lean_IR_EmitC_emitLit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitTailCall___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitFileHeader___closed__12;
lean_object* l_Lean_IR_EmitC_getJPParams___closed__1;
lean_object* lean_ir_find_env_decl(lean_object*, lean_object*);
lean_object* lean_name_mangle(lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitMainFn___closed__29;
lean_object* l_Lean_IR_EmitC_emitDec___closed__1;
lean_object* l_Nat_forMAux___main___at_Lean_IR_EmitC_emitJmp___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_mkVarJPMaps(lean_object*);
lean_object* l_Lean_IR_EmitC_emitPartialApp___closed__2;
lean_object* l_Lean_IR_EmitC_emitFns(lean_object*, lean_object*);
lean_object* l_List_forM___main___at_Lean_IR_EmitC_emitFnDecls___spec__5___closed__1;
lean_object* l_List_forM___main___at_Lean_IR_EmitC_emitFnDecls___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at_Lean_IR_EmitC_emitInitFn___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Decl_normalizeIds(lean_object*);
lean_object* l_Lean_IR_EmitC_emitMainFn___closed__21;
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitCName(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitMainFn___closed__38;
lean_object* l_AssocList_find___main___at_Lean_IR_EmitC_getJPParams___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitFullApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitMainFn___boxed(lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitPartialApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_declareVar___closed__1;
lean_object* l_Lean_IR_EmitC_declareVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitSSet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitFileFooter(lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitMainFn___closed__23;
lean_object* l_Nat_forMAux___main___at_Lean_IR_EmitC_emitCtorSetArgs___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_toCType___closed__10;
lean_object* l_Lean_IR_EmitC_getJPParams___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Char_quoteCore___closed__5;
lean_object* l_Lean_IR_EmitC_emitUnbox(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitJPs(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_RBTree_toList___at_Lean_IR_EmitC_emitFnDecls___spec__3___boxed(lean_object*);
lean_object* l_Nat_forMAux___main___at_Lean_IR_EmitC_emitReset___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitOffset(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at_Lean_IR_EmitC_emitCase___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitExternDeclAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_System_FilePath_dirName___closed__1;
uint8_t l_Bool_DecidableEq(uint8_t, uint8_t);
lean_object* l_Lean_IR_EmitC_emitMainFn___closed__34;
lean_object* l_Lean_IR_EmitC_emitSSet___closed__4;
lean_object* l_Lean_Name_toStringWithSep___main(lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitInitFn___closed__2;
lean_object* l_Lean_IR_EmitC_emitMainFn___closed__48;
lean_object* l_Lean_IR_EmitC_emitLn(lean_object*);
extern lean_object* l_Lean_IR_declMapExt;
lean_object* l_Lean_IR_FnBody_body(lean_object*);
lean_object* l_Lean_IR_EmitC_emitReuse___closed__1;
lean_object* l_List_forM___main___at_Lean_IR_EmitC_emitLns___spec__1(lean_object*);
extern lean_object* l_HashMap_Inhabited___closed__1;
lean_object* l_Lean_IR_EmitC_emitMainFn___closed__18;
lean_object* l_Lean_IR_EmitC_emitMainFn___closed__15;
lean_object* l_List_forM___main___at_Lean_IR_EmitC_emitLns___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitLns___at_Lean_IR_EmitC_emitMainFn___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_List_forM___main___at_Lean_IR_EmitC_emitFnDecls___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_String_Inhabited;
lean_object* l_Lean_IR_EmitC_emitMainFn___closed__50;
lean_object* l_Lean_IR_EmitC_emitFileHeader___closed__24;
lean_object* l_Nat_forMAux___main___at_Lean_IR_EmitC_emitPartialApp___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitSSet___closed__1;
lean_object* l_Lean_IR_EmitC_emitInitFn___closed__8;
lean_object* l_Lean_IR_Decl_params(lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* l_Lean_IR_EmitC_throwInvalidExportName___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitInitFn___closed__4;
uint8_t l_Lean_IR_EmitC_paramEqArg(lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitCase(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitSSet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_RBTree_toList___at_Lean_IR_EmitC_emitFnDecls___spec__3(lean_object*);
lean_object* l_Lean_IR_EmitC_emitLns___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitFileHeader___closed__10;
lean_object* l_Lean_IR_EmitC_getModName(lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitSSet___closed__2;
lean_object* l_Lean_IR_EmitC_emitMainFn___closed__24;
lean_object* l_AssocList_find___main___at_Lean_IR_EmitC_getJPParams___spec__2___boxed(lean_object*, lean_object*);
extern lean_object* l_addParenHeuristic___closed__1;
lean_object* l_Lean_IR_EmitC_quoteString(lean_object*);
lean_object* l_Lean_IR_EmitC_emitMainFn___closed__49;
lean_object* l_Array_forMAux___main___at_Lean_IR_EmitC_emitInitFn___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_toCType(lean_object*);
lean_object* l_Lean_IR_EmitC_emitDeclAux___closed__1;
lean_object* l_Lean_IR_EmitC_emitInitFn___closed__9;
lean_object* l_Lean_IR_EmitC_emitFileHeader___closed__20;
lean_object* l_Lean_IR_EmitC_getEnv(lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at_Lean_IR_EmitC_declareParams___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_getJPParams(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitMainFn___closed__16;
lean_object* l_Lean_IR_EmitC_emitPartialApp___closed__1;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitIsTaggedPtr___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitCtorSetArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldr___main___at_Lean_IR_EmitC_hasMainFn___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_getDecl(lean_object*, lean_object*, lean_object*);
lean_object* _init_l_Lean_IR_EmitC_leanMainFn___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_lean_main");
return x_1;
}
}
lean_object* _init_l_Lean_IR_EmitC_leanMainFn() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_IR_EmitC_leanMainFn___closed__1;
return x_1;
}
}
lean_object* l_Lean_IR_EmitC_getEnv(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_IR_EmitC_getEnv___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_EmitC_getEnv(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_IR_EmitC_getModName(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_IR_EmitC_getModName___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_EmitC_getModName(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_IR_EmitC_getDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = l_System_FilePath_dirName___closed__1;
x_9 = l_Lean_Name_toStringWithSep___main(x_8, x_1);
x_10 = l_Lean_IR_getDecl___closed__1;
x_11 = lean_string_append(x_10, x_9);
lean_dec(x_9);
x_12 = l_Char_HasRepr___closed__1;
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
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_18 = l_System_FilePath_dirName___closed__1;
x_19 = l_Lean_Name_toStringWithSep___main(x_18, x_1);
x_20 = l_Lean_IR_getDecl___closed__1;
x_21 = lean_string_append(x_20, x_19);
lean_dec(x_19);
x_22 = l_Char_HasRepr___closed__1;
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
lean_object* l_Lean_IR_EmitC_getDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_EmitC_getDecl(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_IR_EmitC_emit___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* l_Lean_IR_EmitC_emit(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_IR_EmitC_emit___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Lean_IR_EmitC_emit___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_EmitC_emit___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Lean_IR_EmitC_emitLn___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_apply_1(x_1, x_2);
x_6 = lean_string_append(x_4, x_5);
lean_dec(x_5);
x_7 = l_IO_println___rarg___closed__1;
x_8 = lean_string_append(x_6, x_7);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
}
lean_object* l_Lean_IR_EmitC_emitLn(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_IR_EmitC_emitLn___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Lean_IR_EmitC_emitLn___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_EmitC_emitLn___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_List_forM___main___at_Lean_IR_EmitC_emitLns___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_11 = l_IO_println___rarg___closed__1;
x_12 = lean_string_append(x_10, x_11);
x_2 = x_8;
x_4 = x_12;
goto _start;
}
}
}
lean_object* l_List_forM___main___at_Lean_IR_EmitC_emitLns___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_forM___main___at_Lean_IR_EmitC_emitLns___spec__1___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Lean_IR_EmitC_emitLns___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_forM___main___at_Lean_IR_EmitC_emitLns___spec__1___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_IR_EmitC_emitLns(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_IR_EmitC_emitLns___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_List_forM___main___at_Lean_IR_EmitC_emitLns___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_forM___main___at_Lean_IR_EmitC_emitLns___spec__1___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Lean_IR_EmitC_emitLns___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_EmitC_emitLns___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* _init_l_Lean_IR_EmitC_argToCString___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("lean_box(0)");
return x_1;
}
}
lean_object* l_Lean_IR_EmitC_argToCString(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec(x_1);
x_3 = l_Nat_repr(x_2);
x_4 = l_Lean_IR_VarId_HasToString___closed__1;
x_5 = lean_string_append(x_4, x_3);
lean_dec(x_3);
return x_5;
}
else
{
lean_object* x_6; 
x_6 = l_Lean_IR_EmitC_argToCString___closed__1;
return x_6;
}
}
}
lean_object* l_Lean_IR_EmitC_emitArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_IR_EmitC_emitArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_EmitC_emitArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* _init_l_Lean_IR_EmitC_toCType___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("double");
return x_1;
}
}
lean_object* _init_l_Lean_IR_EmitC_toCType___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("uint8_t");
return x_1;
}
}
lean_object* _init_l_Lean_IR_EmitC_toCType___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("uint16_t");
return x_1;
}
}
lean_object* _init_l_Lean_IR_EmitC_toCType___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("uint32_t");
return x_1;
}
}
lean_object* _init_l_Lean_IR_EmitC_toCType___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("uint64_t");
return x_1;
}
}
lean_object* _init_l_Lean_IR_EmitC_toCType___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("size_t");
return x_1;
}
}
lean_object* _init_l_Lean_IR_EmitC_toCType___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("lean_object*");
return x_1;
}
}
lean_object* _init_l_Lean_IR_EmitC_toCType___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Init.Lean.Compiler.IR.EmitC");
return x_1;
}
}
lean_object* _init_l_Lean_IR_EmitC_toCType___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("not implemented yet");
return x_1;
}
}
lean_object* _init_l_Lean_IR_EmitC_toCType___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_IR_EmitC_toCType___closed__8;
x_2 = lean_unsigned_to_nat(69u);
x_3 = lean_unsigned_to_nat(23u);
x_4 = l_Lean_IR_EmitC_toCType___closed__9;
x_5 = l___private_Init_Util_1__mkPanicMessage(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* _init_l_Lean_IR_EmitC_toCType___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_IR_EmitC_toCType___closed__8;
x_2 = lean_unsigned_to_nat(70u);
x_3 = lean_unsigned_to_nat(23u);
x_4 = l_Lean_IR_EmitC_toCType___closed__9;
x_5 = l___private_Init_Util_1__mkPanicMessage(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_IR_EmitC_toCType(lean_object* x_1) {
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l_String_Inhabited;
x_9 = l_Lean_IR_EmitC_toCType___closed__10;
x_10 = lean_panic_fn(x_9);
return x_10;
}
case 10:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = l_String_Inhabited;
x_12 = l_Lean_IR_EmitC_toCType___closed__11;
x_13 = lean_panic_fn(x_12);
return x_13;
}
default: 
{
lean_object* x_14; 
x_14 = l_Lean_IR_EmitC_toCType___closed__7;
return x_14;
}
}
}
}
lean_object* l_Lean_IR_EmitC_toCType___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_IR_EmitC_toCType(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_IR_EmitC_throwInvalidExportName___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid export name '");
return x_1;
}
}
lean_object* l_Lean_IR_EmitC_throwInvalidExportName___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = l_System_FilePath_dirName___closed__1;
x_5 = l_Lean_Name_toStringWithSep___main(x_4, x_1);
x_6 = l_Lean_IR_EmitC_throwInvalidExportName___rarg___closed__1;
x_7 = lean_string_append(x_6, x_5);
lean_dec(x_5);
x_8 = l_Char_HasRepr___closed__1;
x_9 = lean_string_append(x_7, x_8);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_3);
return x_10;
}
}
lean_object* l_Lean_IR_EmitC_throwInvalidExportName(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_IR_EmitC_throwInvalidExportName___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Lean_IR_EmitC_throwInvalidExportName___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_EmitC_throwInvalidExportName___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* _init_l_Lean_IR_EmitC_toCName___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("main");
return x_1;
}
}
lean_object* _init_l_Lean_IR_EmitC_toCName___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_IR_EmitC_toCName___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_IR_EmitC_toCName___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("l_");
return x_1;
}
}
lean_object* l_Lean_IR_EmitC_toCName(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_IR_EmitC_getEnv(x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = l_Lean_exportAttr;
lean_inc(x_1);
x_9 = l_Lean_ParametricAttribute_getParam___at_Lean_isIOUnitInitFn___spec__1(x_8, x_6, x_1);
lean_dec(x_6);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; uint8_t x_11; uint8_t x_12; uint8_t x_13; 
x_10 = l_Lean_IR_EmitC_toCName___closed__2;
x_11 = lean_name_eq(x_1, x_10);
x_12 = 1;
x_13 = l_Bool_DecidableEq(x_11, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Lean_IR_EmitC_toCName___closed__3;
x_15 = lean_name_mangle(x_1, x_14);
lean_ctor_set(x_4, 0, x_15);
return x_4;
}
else
{
lean_object* x_16; 
lean_dec(x_1);
x_16 = l_Lean_IR_EmitC_leanMainFn;
lean_ctor_set(x_4, 0, x_16);
return x_4;
}
}
else
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_9, 0);
lean_inc(x_17);
lean_dec(x_9);
if (lean_obj_tag(x_17) == 1)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
lean_dec(x_1);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_ctor_set(x_4, 0, x_19);
return x_4;
}
else
{
lean_object* x_20; 
lean_dec(x_18);
lean_dec(x_17);
lean_free_object(x_4);
x_20 = l_Lean_IR_EmitC_throwInvalidExportName___rarg(x_1, x_2, x_7);
return x_20;
}
}
else
{
lean_object* x_21; 
lean_dec(x_17);
lean_free_object(x_4);
x_21 = l_Lean_IR_EmitC_throwInvalidExportName___rarg(x_1, x_2, x_7);
return x_21;
}
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_4, 0);
x_23 = lean_ctor_get(x_4, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_4);
x_24 = l_Lean_exportAttr;
lean_inc(x_1);
x_25 = l_Lean_ParametricAttribute_getParam___at_Lean_isIOUnitInitFn___spec__1(x_24, x_22, x_1);
lean_dec(x_22);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; uint8_t x_27; uint8_t x_28; uint8_t x_29; 
x_26 = l_Lean_IR_EmitC_toCName___closed__2;
x_27 = lean_name_eq(x_1, x_26);
x_28 = 1;
x_29 = l_Bool_DecidableEq(x_27, x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = l_Lean_IR_EmitC_toCName___closed__3;
x_31 = lean_name_mangle(x_1, x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_23);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_1);
x_33 = l_Lean_IR_EmitC_leanMainFn;
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_23);
return x_34;
}
}
else
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_25, 0);
lean_inc(x_35);
lean_dec(x_25);
if (lean_obj_tag(x_35) == 1)
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_1);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_23);
return x_38;
}
else
{
lean_object* x_39; 
lean_dec(x_36);
lean_dec(x_35);
x_39 = l_Lean_IR_EmitC_throwInvalidExportName___rarg(x_1, x_2, x_23);
return x_39;
}
}
else
{
lean_object* x_40; 
lean_dec(x_35);
x_40 = l_Lean_IR_EmitC_throwInvalidExportName___rarg(x_1, x_2, x_23);
return x_40;
}
}
}
}
}
lean_object* l_Lean_IR_EmitC_toCName___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_EmitC_toCName(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_IR_EmitC_emitCName(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_IR_EmitC_emitCName___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_EmitC_emitCName(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* _init_l_Lean_IR_EmitC_toCInitName___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_init_");
return x_1;
}
}
lean_object* l_Lean_IR_EmitC_toCInitName(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_IR_EmitC_getEnv(x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = l_Lean_exportAttr;
lean_inc(x_1);
x_9 = l_Lean_ParametricAttribute_getParam___at_Lean_isIOUnitInitFn___spec__1(x_8, x_6, x_1);
lean_dec(x_6);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_Lean_IR_EmitC_toCName___closed__3;
x_11 = lean_name_mangle(x_1, x_10);
x_12 = l_Lean_IR_EmitC_toCInitName___closed__1;
x_13 = lean_string_append(x_12, x_11);
lean_dec(x_11);
lean_ctor_set(x_4, 0, x_13);
return x_4;
}
else
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_9, 0);
lean_inc(x_14);
lean_dec(x_9);
if (lean_obj_tag(x_14) == 1)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_1);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_IR_EmitC_toCInitName___closed__1;
x_18 = lean_string_append(x_17, x_16);
lean_dec(x_16);
lean_ctor_set(x_4, 0, x_18);
return x_4;
}
else
{
lean_object* x_19; 
lean_dec(x_15);
lean_dec(x_14);
lean_free_object(x_4);
x_19 = l_Lean_IR_EmitC_throwInvalidExportName___rarg(x_1, x_2, x_7);
return x_19;
}
}
else
{
lean_object* x_20; 
lean_dec(x_14);
lean_free_object(x_4);
x_20 = l_Lean_IR_EmitC_throwInvalidExportName___rarg(x_1, x_2, x_7);
return x_20;
}
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_4, 0);
x_22 = lean_ctor_get(x_4, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_4);
x_23 = l_Lean_exportAttr;
lean_inc(x_1);
x_24 = l_Lean_ParametricAttribute_getParam___at_Lean_isIOUnitInitFn___spec__1(x_23, x_21, x_1);
lean_dec(x_21);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = l_Lean_IR_EmitC_toCName___closed__3;
x_26 = lean_name_mangle(x_1, x_25);
x_27 = l_Lean_IR_EmitC_toCInitName___closed__1;
x_28 = lean_string_append(x_27, x_26);
lean_dec(x_26);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_22);
return x_29;
}
else
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_24, 0);
lean_inc(x_30);
lean_dec(x_24);
if (lean_obj_tag(x_30) == 1)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_1);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l_Lean_IR_EmitC_toCInitName___closed__1;
x_34 = lean_string_append(x_33, x_32);
lean_dec(x_32);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_22);
return x_35;
}
else
{
lean_object* x_36; 
lean_dec(x_31);
lean_dec(x_30);
x_36 = l_Lean_IR_EmitC_throwInvalidExportName___rarg(x_1, x_2, x_22);
return x_36;
}
}
else
{
lean_object* x_37; 
lean_dec(x_30);
x_37 = l_Lean_IR_EmitC_throwInvalidExportName___rarg(x_1, x_2, x_22);
return x_37;
}
}
}
}
}
lean_object* l_Lean_IR_EmitC_toCInitName___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_EmitC_toCInitName(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_IR_EmitC_emitCInitName(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_IR_EmitC_emitCInitName___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_EmitC_emitCInitName(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Nat_forMAux___main___at_Lean_IR_EmitC_emitFnDeclAux___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = l_Lean_IR_paramInh;
x_14 = lean_array_get(x_13, x_1, x_11);
lean_dec(x_11);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = l_Lean_IR_EmitC_toCType(x_15);
lean_dec(x_15);
x_17 = lean_string_append(x_5, x_16);
lean_dec(x_16);
x_3 = x_9;
x_5 = x_17;
goto _start;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_19 = l_List_reprAux___main___rarg___closed__1;
x_20 = lean_string_append(x_5, x_19);
x_21 = l_Lean_IR_paramInh;
x_22 = lean_array_get(x_21, x_1, x_11);
lean_dec(x_11);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = l_Lean_IR_EmitC_toCType(x_23);
lean_dec(x_23);
x_25 = lean_string_append(x_20, x_24);
lean_dec(x_24);
x_3 = x_9;
x_5 = x_25;
goto _start;
}
}
else
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_3);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_5);
return x_28;
}
}
}
lean_object* l_Array_filterAux___main___at_Lean_IR_EmitC_emitFnDeclAux___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_2);
x_6 = l_Array_shrink___main___rarg(x_1, x_3);
lean_dec(x_3);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_array_fget(x_1, x_2);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_Lean_IR_IRType_isIrrelevant(x_8);
lean_dec(x_8);
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = l_String_Iterator_extract___closed__1;
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_2, x_11);
lean_dec(x_2);
x_2 = x_12;
goto _start;
}
else
{
uint8_t x_14; 
x_14 = lean_nat_dec_lt(x_3, x_2);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_2, x_15);
lean_dec(x_2);
x_17 = lean_nat_add(x_3, x_15);
lean_dec(x_3);
x_2 = x_16;
x_3 = x_17;
goto _start;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_array_fswap(x_1, x_2, x_3);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_2, x_20);
lean_dec(x_2);
x_22 = lean_nat_add(x_3, x_20);
lean_dec(x_3);
x_1 = x_19;
x_2 = x_21;
x_3 = x_22;
goto _start;
}
}
}
else
{
uint8_t x_24; 
x_24 = l_String_anyAux___main___at_String_all___spec__1___closed__1;
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_add(x_2, x_25);
lean_dec(x_2);
x_2 = x_26;
goto _start;
}
else
{
uint8_t x_28; 
x_28 = lean_nat_dec_lt(x_3, x_2);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_add(x_2, x_29);
lean_dec(x_2);
x_31 = lean_nat_add(x_3, x_29);
lean_dec(x_3);
x_2 = x_30;
x_3 = x_31;
goto _start;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_array_fswap(x_1, x_2, x_3);
x_34 = lean_unsigned_to_nat(1u);
x_35 = lean_nat_add(x_2, x_34);
lean_dec(x_2);
x_36 = lean_nat_add(x_3, x_34);
lean_dec(x_3);
x_1 = x_33;
x_2 = x_35;
x_3 = x_36;
goto _start;
}
}
}
}
}
}
lean_object* _init_l_Lean_IR_EmitC_emitFnDeclAux___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("lean_object**");
return x_1;
}
}
lean_object* l_Lean_IR_EmitC_emitFnDeclAux(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_6 = l_Lean_IR_Decl_params(x_1);
x_7 = l_Lean_IR_EmitC_getEnv(x_4, x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_10 = x_7;
} else {
 lean_dec_ref(x_7);
 x_10 = lean_box(0);
}
x_11 = l_Array_isEmpty___rarg(x_6);
if (x_11 == 0)
{
uint8_t x_75; 
x_75 = l_String_anyAux___main___at_String_all___spec__1___closed__1;
if (x_75 == 0)
{
x_12 = x_9;
goto block_74;
}
else
{
lean_object* x_76; lean_object* x_77; 
x_76 = l_Lean_IR_formatDecl___closed__3;
x_77 = lean_string_append(x_9, x_76);
x_12 = x_77;
goto block_74;
}
}
else
{
uint8_t x_78; uint8_t x_79; 
x_78 = 1;
x_79 = l_Bool_DecidableEq(x_3, x_78);
if (x_79 == 0)
{
x_12 = x_9;
goto block_74;
}
else
{
lean_object* x_80; lean_object* x_81; 
x_80 = l_Lean_IR_formatDecl___closed__3;
x_81 = lean_string_append(x_9, x_80);
x_12 = x_81;
goto block_74;
}
}
block_74:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_20; 
x_13 = l_Lean_IR_Decl_resultType(x_1);
x_14 = l_Lean_IR_EmitC_toCType(x_13);
lean_dec(x_13);
x_15 = l_String_Iterator_HasRepr___closed__2;
x_16 = lean_string_append(x_14, x_15);
x_17 = lean_string_append(x_16, x_2);
x_18 = lean_string_append(x_12, x_17);
lean_dec(x_17);
x_19 = 1;
x_20 = l_Bool_DecidableEq(x_11, x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_64; uint8_t x_65; 
x_21 = l_Prod_HasRepr___rarg___closed__1;
x_22 = lean_string_append(x_18, x_21);
x_23 = l_Lean_IR_Decl_name(x_1);
lean_inc(x_23);
x_64 = l_Lean_isExternC(x_8, x_23);
lean_dec(x_8);
x_65 = l_Bool_DecidableEq(x_64, x_19);
if (x_65 == 0)
{
x_24 = x_6;
goto block_63;
}
else
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_unsigned_to_nat(0u);
x_67 = l_Array_filterAux___main___at_Lean_IR_EmitC_emitFnDeclAux___spec__2(x_6, x_66, x_66);
x_24 = x_67;
goto block_63;
}
block_63:
{
lean_object* x_25; uint8_t x_26; lean_object* x_59; uint8_t x_60; 
x_25 = lean_array_get_size(x_24);
x_59 = l_Lean_closureMaxArgs;
x_60 = lean_nat_dec_lt(x_59, x_25);
if (x_60 == 0)
{
uint8_t x_61; 
lean_dec(x_23);
x_61 = 0;
x_26 = x_61;
goto block_58;
}
else
{
uint8_t x_62; 
x_62 = l_Lean_IR_ExplicitBoxing_isBoxedName(x_23);
lean_dec(x_23);
x_26 = x_62;
goto block_58;
}
block_58:
{
uint8_t x_27; 
x_27 = l_Bool_DecidableEq(x_26, x_19);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; 
lean_dec(x_10);
lean_inc(x_25);
x_28 = l_Nat_forMAux___main___at_Lean_IR_EmitC_emitFnDeclAux___spec__1(x_24, x_25, x_25, x_4, x_22);
lean_dec(x_25);
lean_dec(x_24);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_30 = lean_ctor_get(x_28, 1);
x_31 = lean_ctor_get(x_28, 0);
lean_dec(x_31);
x_32 = l_Option_HasRepr___rarg___closed__3;
x_33 = lean_string_append(x_30, x_32);
x_34 = l_Lean_IR_formatFnBody___main___closed__1;
x_35 = lean_string_append(x_33, x_34);
x_36 = l_IO_println___rarg___closed__1;
x_37 = lean_string_append(x_35, x_36);
x_38 = lean_box(0);
lean_ctor_set(x_28, 1, x_37);
lean_ctor_set(x_28, 0, x_38);
return x_28;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_39 = lean_ctor_get(x_28, 1);
lean_inc(x_39);
lean_dec(x_28);
x_40 = l_Option_HasRepr___rarg___closed__3;
x_41 = lean_string_append(x_39, x_40);
x_42 = l_Lean_IR_formatFnBody___main___closed__1;
x_43 = lean_string_append(x_41, x_42);
x_44 = l_IO_println___rarg___closed__1;
x_45 = lean_string_append(x_43, x_44);
x_46 = lean_box(0);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
return x_47;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_25);
lean_dec(x_24);
x_48 = l_Lean_IR_EmitC_emitFnDeclAux___closed__1;
x_49 = lean_string_append(x_22, x_48);
x_50 = l_Option_HasRepr___rarg___closed__3;
x_51 = lean_string_append(x_49, x_50);
x_52 = l_Lean_IR_formatFnBody___main___closed__1;
x_53 = lean_string_append(x_51, x_52);
x_54 = l_IO_println___rarg___closed__1;
x_55 = lean_string_append(x_53, x_54);
x_56 = lean_box(0);
if (lean_is_scalar(x_10)) {
 x_57 = lean_alloc_ctor(0, 2, 0);
} else {
 x_57 = x_10;
}
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_55);
return x_57;
}
}
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_8);
lean_dec(x_6);
x_68 = l_Lean_IR_formatFnBody___main___closed__1;
x_69 = lean_string_append(x_18, x_68);
x_70 = l_IO_println___rarg___closed__1;
x_71 = lean_string_append(x_69, x_70);
x_72 = lean_box(0);
if (lean_is_scalar(x_10)) {
 x_73 = lean_alloc_ctor(0, 2, 0);
} else {
 x_73 = x_10;
}
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_71);
return x_73;
}
}
}
}
lean_object* l_Nat_forMAux___main___at_Lean_IR_EmitC_emitFnDeclAux___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Nat_forMAux___main___at_Lean_IR_EmitC_emitFnDeclAux___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_IR_EmitC_emitFnDeclAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_3);
lean_dec(x_3);
x_7 = l_Lean_IR_EmitC_emitFnDeclAux(x_1, x_2, x_6, x_4, x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_IR_EmitC_emitFnDecl(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
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
lean_dec(x_7);
return x_9;
}
else
{
uint8_t x_10; 
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
lean_object* l_Lean_IR_EmitC_emitFnDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Lean_IR_EmitC_emitFnDecl(x_1, x_5, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_IR_EmitC_emitExternDeclAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = l_Lean_IR_EmitC_getEnv(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l_Lean_IR_Decl_name(x_1);
x_9 = l_Lean_isExternC(x_6, x_8);
lean_dec(x_6);
if (x_9 == 0)
{
uint8_t x_10; lean_object* x_11; 
x_10 = 1;
x_11 = l_Lean_IR_EmitC_emitFnDeclAux(x_1, x_2, x_10, x_3, x_7);
return x_11;
}
else
{
uint8_t x_12; lean_object* x_13; 
x_12 = 0;
x_13 = l_Lean_IR_EmitC_emitFnDeclAux(x_1, x_2, x_12, x_3, x_7);
return x_13;
}
}
}
lean_object* l_Lean_IR_EmitC_emitExternDeclAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_EmitC_emitExternDeclAux(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_List_foldl___main___at_Lean_IR_EmitC_emitFnDecls___spec__1(lean_object* x_1, lean_object* x_2) {
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
x_7 = l_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_1, x_5, x_6);
x_1 = x_7;
x_2 = x_4;
goto _start;
}
}
}
lean_object* l_List_foldl___main___at_Lean_IR_EmitC_emitFnDecls___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_8 = l_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_2, x_6, x_7);
lean_inc(x_1);
x_9 = l_Lean_IR_collectUsedDecls(x_1, x_4, x_8);
x_2 = x_9;
x_3 = x_5;
goto _start;
}
}
}
lean_object* l_RBNode_revFold___main___at_Lean_IR_EmitC_emitFnDecls___spec__4(lean_object* x_1, lean_object* x_2) {
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
x_6 = l_RBNode_revFold___main___at_Lean_IR_EmitC_emitFnDecls___spec__4(x_1, x_5);
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
lean_object* l_RBTree_toList___at_Lean_IR_EmitC_emitFnDecls___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = l_RBNode_revFold___main___at_Lean_IR_EmitC_emitFnDecls___spec__4(x_2, x_1);
return x_3;
}
}
lean_object* _init_l_List_forM___main___at_Lean_IR_EmitC_emitFnDecls___spec__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("c");
return x_1;
}
}
lean_object* _init_l_List_forM___main___at_Lean_IR_EmitC_emitFnDecls___spec__5___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_List_forM___main___at_Lean_IR_EmitC_emitFnDecls___spec__5___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_List_forM___main___at_Lean_IR_EmitC_emitFnDecls___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_6; lean_object* x_7; 
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
x_14 = l_List_forM___main___at_Lean_IR_EmitC_emitFnDecls___spec__5___closed__2;
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
x_18 = l_Lean_IR_EmitC_emitFnDecl(x_11, x_17, x_4, x_12);
lean_dec(x_11);
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
x_26 = l_Lean_IR_EmitC_emitFnDecl(x_11, x_25, x_4, x_12);
lean_dec(x_11);
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
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_8);
x_33 = lean_ctor_get(x_15, 0);
lean_inc(x_33);
lean_dec(x_15);
x_34 = l_Lean_IR_EmitC_emitExternDeclAux(x_11, x_33, x_4, x_12);
lean_dec(x_33);
lean_dec(x_11);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
x_3 = x_9;
x_5 = x_35;
goto _start;
}
}
else
{
uint8_t x_37; 
lean_dec(x_9);
lean_dec(x_8);
x_37 = !lean_is_exclusive(x_10);
if (x_37 == 0)
{
return x_10;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_10, 0);
x_39 = lean_ctor_get(x_10, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_10);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
}
lean_object* l_Lean_IR_EmitC_emitFnDecls(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_3 = l_Lean_IR_EmitC_getEnv(x_1, x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = l_Lean_IR_declMapExt;
x_7 = l_Lean_SimplePersistentEnvExtension_getEntries___rarg(x_6, x_4);
x_8 = lean_box(0);
x_9 = l_List_foldl___main___at_Lean_IR_EmitC_emitFnDecls___spec__1(x_8, x_7);
lean_inc(x_4);
x_10 = l_List_foldl___main___at_Lean_IR_EmitC_emitFnDecls___spec__2(x_4, x_8, x_7);
x_11 = l_RBTree_toList___at_Lean_IR_EmitC_emitFnDecls___spec__3(x_10);
lean_dec(x_10);
x_12 = l_List_forM___main___at_Lean_IR_EmitC_emitFnDecls___spec__5(x_4, x_9, x_11, x_1, x_5);
lean_dec(x_9);
lean_dec(x_4);
return x_12;
}
}
lean_object* l_List_foldl___main___at_Lean_IR_EmitC_emitFnDecls___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_foldl___main___at_Lean_IR_EmitC_emitFnDecls___spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_RBNode_revFold___main___at_Lean_IR_EmitC_emitFnDecls___spec__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_RBNode_revFold___main___at_Lean_IR_EmitC_emitFnDecls___spec__4(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_RBTree_toList___at_Lean_IR_EmitC_emitFnDecls___spec__3___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_RBTree_toList___at_Lean_IR_EmitC_emitFnDecls___spec__3(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_List_forM___main___at_Lean_IR_EmitC_emitFnDecls___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_List_forM___main___at_Lean_IR_EmitC_emitFnDecls___spec__5(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_IR_EmitC_emitFnDecls___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_EmitC_emitFnDecls(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_List_forM___main___at_Lean_IR_EmitC_emitMainFn___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_string_append(x_3, x_6);
x_9 = l_IO_println___rarg___closed__1;
x_10 = lean_string_append(x_8, x_9);
x_1 = x_7;
x_3 = x_10;
goto _start;
}
}
}
lean_object* l_Lean_IR_EmitC_emitLns___at_Lean_IR_EmitC_emitMainFn___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_forM___main___at_Lean_IR_EmitC_emitMainFn___spec__2(x_1, x_2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid main function, incorrect arity when generating code");
return x_1;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("res = initialize_");
return x_1;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("(lean_io_mk_world());");
return x_1;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_PersistentArray_Stats_toString___closed__4;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("  return 1;");
return x_1;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_EmitC_emitMainFn___closed__5;
x_2 = l_Lean_IR_EmitC_emitMainFn___closed__4;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("  lean_dec_ref(res);");
return x_1;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_EmitC_emitMainFn___closed__7;
x_2 = l_Lean_IR_EmitC_emitMainFn___closed__6;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("  lean_io_result_show_error(res);");
return x_1;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_EmitC_emitMainFn___closed__9;
x_2 = l_Lean_IR_EmitC_emitMainFn___closed__8;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("} else {");
return x_1;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_EmitC_emitMainFn___closed__11;
x_2 = l_Lean_IR_EmitC_emitMainFn___closed__10;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("  return ret;");
return x_1;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_EmitC_emitMainFn___closed__13;
x_2 = l_Lean_IR_EmitC_emitMainFn___closed__12;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_EmitC_emitMainFn___closed__7;
x_2 = l_Lean_IR_EmitC_emitMainFn___closed__14;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("  int ret = lean_unbox(lean_io_result_get_value(res));");
return x_1;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_EmitC_emitMainFn___closed__16;
x_2 = l_Lean_IR_EmitC_emitMainFn___closed__15;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__18() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("if (lean_io_result_is_ok(res)) {");
return x_1;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_EmitC_emitMainFn___closed__18;
x_2 = l_Lean_IR_EmitC_emitMainFn___closed__17;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__20() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("lean_init_task_manager();");
return x_1;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_IR_EmitC_emitMainFn___closed__20;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__22() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("lean_dec_ref(res);");
return x_1;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_EmitC_emitMainFn___closed__22;
x_2 = l_Lean_IR_EmitC_emitMainFn___closed__21;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_EmitC_emitMainFn___closed__18;
x_2 = l_Lean_IR_EmitC_emitMainFn___closed__23;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__25() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("lean_io_mark_end_initialization();");
return x_1;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_EmitC_emitMainFn___closed__25;
x_2 = l_Lean_IR_EmitC_emitMainFn___closed__24;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__27() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("res = ");
return x_1;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__28() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_EmitC_emitMainFn___closed__27;
x_2 = l_Lean_IR_EmitC_leanMainFn;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__29() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_EmitC_emitMainFn___closed__28;
x_2 = l_Lean_IR_EmitC_emitMainFn___closed__3;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__30() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" in = n;");
return x_1;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__31() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_EmitC_emitMainFn___closed__30;
x_2 = l_Lean_IR_EmitC_emitMainFn___closed__4;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__32() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" n = lean_alloc_ctor(1,2,0); lean_ctor_set(n, 0, lean_mk_string(argv[i])); lean_ctor_set(n, 1, in);");
return x_1;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__33() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_EmitC_emitMainFn___closed__32;
x_2 = l_Lean_IR_EmitC_emitMainFn___closed__31;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__34() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" i--;");
return x_1;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__35() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_EmitC_emitMainFn___closed__34;
x_2 = l_Lean_IR_EmitC_emitMainFn___closed__33;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__36() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" lean_object* n;");
return x_1;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__37() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_EmitC_emitMainFn___closed__36;
x_2 = l_Lean_IR_EmitC_emitMainFn___closed__35;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__38() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("while (i > 1) {");
return x_1;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__39() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_EmitC_emitMainFn___closed__38;
x_2 = l_Lean_IR_EmitC_emitMainFn___closed__37;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__40() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("int i = argc;");
return x_1;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__41() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_EmitC_emitMainFn___closed__40;
x_2 = l_Lean_IR_EmitC_emitMainFn___closed__39;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__42() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("in = lean_box(0);");
return x_1;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__43() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_EmitC_emitMainFn___closed__42;
x_2 = l_Lean_IR_EmitC_emitMainFn___closed__41;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__44() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("(in, lean_io_mk_world());");
return x_1;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__45() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_EmitC_emitMainFn___closed__28;
x_2 = l_Lean_IR_EmitC_emitMainFn___closed__44;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__46() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("void lean_initialize_runtime_module();");
return x_1;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__47() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("int main(int argc, char ** argv) {\nlean_object* in; lean_object* res;");
return x_1;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__48() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("lean_initialize_runtime_module();");
return x_1;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__49() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("void lean_initialize();");
return x_1;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__50() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("lean_initialize();");
return x_1;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__51() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("function declaration expected");
return x_1;
}
}
lean_object* l_Lean_IR_EmitC_emitMainFn(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_IR_EmitC_toCName___closed__2;
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
x_10 = lean_array_get_size(x_9);
lean_dec(x_9);
x_11 = lean_unsigned_to_nat(2u);
x_12 = lean_nat_dec_eq(x_10, x_11);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; uint8_t x_15; uint8_t x_16; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_dec_eq(x_10, x_13);
lean_dec(x_10);
x_15 = 1;
x_16 = l_Bool_DecidableEq(x_14, x_15);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_5);
x_17 = l_Lean_IR_EmitC_emitMainFn___closed__1;
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_17);
return x_4;
}
else
{
lean_object* x_18; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; uint8_t x_68; 
lean_free_object(x_4);
x_63 = l_Lean_IR_EmitC_getEnv(x_1, x_7);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_66 = l_Lean_IR_usesLeanNamespace(x_64, x_5);
x_67 = lean_unbox(x_66);
lean_dec(x_66);
x_68 = l_Bool_DecidableEq(x_67, x_15);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_69 = l_Lean_IR_EmitC_emitMainFn___closed__46;
x_70 = lean_string_append(x_65, x_69);
x_71 = l_IO_println___rarg___closed__1;
x_72 = lean_string_append(x_70, x_71);
x_73 = l_Lean_IR_EmitC_emitMainFn___closed__47;
x_74 = lean_string_append(x_72, x_73);
x_75 = lean_string_append(x_74, x_71);
x_76 = l_Lean_IR_EmitC_emitMainFn___closed__48;
x_77 = lean_string_append(x_75, x_76);
x_78 = lean_string_append(x_77, x_71);
x_18 = x_78;
goto block_62;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_79 = l_Lean_IR_EmitC_emitMainFn___closed__49;
x_80 = lean_string_append(x_65, x_79);
x_81 = l_IO_println___rarg___closed__1;
x_82 = lean_string_append(x_80, x_81);
x_83 = l_Lean_IR_EmitC_emitMainFn___closed__47;
x_84 = lean_string_append(x_82, x_83);
x_85 = lean_string_append(x_84, x_81);
x_86 = l_Lean_IR_EmitC_emitMainFn___closed__50;
x_87 = lean_string_append(x_85, x_86);
x_88 = lean_string_append(x_87, x_81);
x_18 = x_88;
goto block_62;
}
block_62:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_19 = l_Lean_IR_EmitC_getModName(x_1, x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_String_splitAux___main___closed__1;
x_23 = lean_name_mangle(x_20, x_22);
x_24 = l_Lean_IR_EmitC_emitMainFn___closed__2;
x_25 = lean_string_append(x_24, x_23);
lean_dec(x_23);
x_26 = l_Lean_IR_EmitC_emitMainFn___closed__3;
x_27 = lean_string_append(x_25, x_26);
x_28 = lean_string_append(x_21, x_27);
lean_dec(x_27);
x_29 = l_IO_println___rarg___closed__1;
x_30 = lean_string_append(x_28, x_29);
x_49 = l_Lean_IR_EmitC_emitMainFn___closed__26;
x_50 = l_List_forM___main___at_Lean_IR_EmitC_emitMainFn___spec__2(x_49, x_1, x_30);
x_51 = lean_ctor_get(x_50, 1);
lean_inc(x_51);
lean_dec(x_50);
x_52 = l_Bool_DecidableEq(x_12, x_15);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = l_Lean_IR_EmitC_emitMainFn___closed__29;
x_54 = lean_string_append(x_51, x_53);
x_55 = lean_string_append(x_54, x_29);
x_31 = x_55;
goto block_48;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_56 = l_Lean_IR_EmitC_emitMainFn___closed__43;
x_57 = l_List_forM___main___at_Lean_IR_EmitC_emitMainFn___spec__2(x_56, x_1, x_51);
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
lean_dec(x_57);
x_59 = l_Lean_IR_EmitC_emitMainFn___closed__45;
x_60 = lean_string_append(x_58, x_59);
x_61 = lean_string_append(x_60, x_29);
x_31 = x_61;
goto block_48;
}
block_48:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_32 = l_PersistentArray_Stats_toString___closed__4;
x_33 = lean_string_append(x_31, x_32);
x_34 = lean_string_append(x_33, x_29);
x_35 = l_Lean_IR_EmitC_emitMainFn___closed__19;
x_36 = l_List_forM___main___at_Lean_IR_EmitC_emitMainFn___spec__2(x_35, x_1, x_34);
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_38 = lean_ctor_get(x_36, 1);
x_39 = lean_ctor_get(x_36, 0);
lean_dec(x_39);
x_40 = lean_string_append(x_38, x_32);
x_41 = lean_string_append(x_40, x_29);
x_42 = lean_box(0);
lean_ctor_set(x_36, 1, x_41);
lean_ctor_set(x_36, 0, x_42);
return x_36;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_43 = lean_ctor_get(x_36, 1);
lean_inc(x_43);
lean_dec(x_36);
x_44 = lean_string_append(x_43, x_32);
x_45 = lean_string_append(x_44, x_29);
x_46 = lean_box(0);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
return x_47;
}
}
}
}
}
else
{
uint8_t x_89; 
lean_dec(x_10);
x_89 = l_String_Iterator_extract___closed__1;
if (x_89 == 0)
{
lean_object* x_90; 
lean_dec(x_5);
x_90 = l_Lean_IR_EmitC_emitMainFn___closed__1;
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_90);
return x_4;
}
else
{
lean_object* x_91; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; uint8_t x_141; uint8_t x_142; uint8_t x_143; 
lean_free_object(x_4);
x_137 = l_Lean_IR_EmitC_getEnv(x_1, x_7);
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_137, 1);
lean_inc(x_139);
lean_dec(x_137);
x_140 = l_Lean_IR_usesLeanNamespace(x_138, x_5);
x_141 = lean_unbox(x_140);
lean_dec(x_140);
x_142 = 1;
x_143 = l_Bool_DecidableEq(x_141, x_142);
if (x_143 == 0)
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_144 = l_Lean_IR_EmitC_emitMainFn___closed__46;
x_145 = lean_string_append(x_139, x_144);
x_146 = l_IO_println___rarg___closed__1;
x_147 = lean_string_append(x_145, x_146);
x_148 = l_Lean_IR_EmitC_emitMainFn___closed__47;
x_149 = lean_string_append(x_147, x_148);
x_150 = lean_string_append(x_149, x_146);
x_151 = l_Lean_IR_EmitC_emitMainFn___closed__48;
x_152 = lean_string_append(x_150, x_151);
x_153 = lean_string_append(x_152, x_146);
x_91 = x_153;
goto block_136;
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_154 = l_Lean_IR_EmitC_emitMainFn___closed__49;
x_155 = lean_string_append(x_139, x_154);
x_156 = l_IO_println___rarg___closed__1;
x_157 = lean_string_append(x_155, x_156);
x_158 = l_Lean_IR_EmitC_emitMainFn___closed__47;
x_159 = lean_string_append(x_157, x_158);
x_160 = lean_string_append(x_159, x_156);
x_161 = l_Lean_IR_EmitC_emitMainFn___closed__50;
x_162 = lean_string_append(x_160, x_161);
x_163 = lean_string_append(x_162, x_156);
x_91 = x_163;
goto block_136;
}
block_136:
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_122; lean_object* x_123; lean_object* x_124; uint8_t x_125; uint8_t x_126; 
x_92 = l_Lean_IR_EmitC_getModName(x_1, x_91);
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
lean_dec(x_92);
x_95 = l_String_splitAux___main___closed__1;
x_96 = lean_name_mangle(x_93, x_95);
x_97 = l_Lean_IR_EmitC_emitMainFn___closed__2;
x_98 = lean_string_append(x_97, x_96);
lean_dec(x_96);
x_99 = l_Lean_IR_EmitC_emitMainFn___closed__3;
x_100 = lean_string_append(x_98, x_99);
x_101 = lean_string_append(x_94, x_100);
lean_dec(x_100);
x_102 = l_IO_println___rarg___closed__1;
x_103 = lean_string_append(x_101, x_102);
x_122 = l_Lean_IR_EmitC_emitMainFn___closed__26;
x_123 = l_List_forM___main___at_Lean_IR_EmitC_emitMainFn___spec__2(x_122, x_1, x_103);
x_124 = lean_ctor_get(x_123, 1);
lean_inc(x_124);
lean_dec(x_123);
x_125 = 1;
x_126 = l_Bool_DecidableEq(x_12, x_125);
if (x_126 == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_127 = l_Lean_IR_EmitC_emitMainFn___closed__29;
x_128 = lean_string_append(x_124, x_127);
x_129 = lean_string_append(x_128, x_102);
x_104 = x_129;
goto block_121;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_130 = l_Lean_IR_EmitC_emitMainFn___closed__43;
x_131 = l_List_forM___main___at_Lean_IR_EmitC_emitMainFn___spec__2(x_130, x_1, x_124);
x_132 = lean_ctor_get(x_131, 1);
lean_inc(x_132);
lean_dec(x_131);
x_133 = l_Lean_IR_EmitC_emitMainFn___closed__45;
x_134 = lean_string_append(x_132, x_133);
x_135 = lean_string_append(x_134, x_102);
x_104 = x_135;
goto block_121;
}
block_121:
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; 
x_105 = l_PersistentArray_Stats_toString___closed__4;
x_106 = lean_string_append(x_104, x_105);
x_107 = lean_string_append(x_106, x_102);
x_108 = l_Lean_IR_EmitC_emitMainFn___closed__19;
x_109 = l_List_forM___main___at_Lean_IR_EmitC_emitMainFn___spec__2(x_108, x_1, x_107);
x_110 = !lean_is_exclusive(x_109);
if (x_110 == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_111 = lean_ctor_get(x_109, 1);
x_112 = lean_ctor_get(x_109, 0);
lean_dec(x_112);
x_113 = lean_string_append(x_111, x_105);
x_114 = lean_string_append(x_113, x_102);
x_115 = lean_box(0);
lean_ctor_set(x_109, 1, x_114);
lean_ctor_set(x_109, 0, x_115);
return x_109;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_116 = lean_ctor_get(x_109, 1);
lean_inc(x_116);
lean_dec(x_109);
x_117 = lean_string_append(x_116, x_105);
x_118 = lean_string_append(x_117, x_102);
x_119 = lean_box(0);
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_118);
return x_120;
}
}
}
}
}
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; uint8_t x_168; 
x_164 = lean_ctor_get(x_4, 1);
lean_inc(x_164);
lean_dec(x_4);
x_165 = lean_ctor_get(x_5, 1);
lean_inc(x_165);
x_166 = lean_array_get_size(x_165);
lean_dec(x_165);
x_167 = lean_unsigned_to_nat(2u);
x_168 = lean_nat_dec_eq(x_166, x_167);
if (x_168 == 0)
{
lean_object* x_169; uint8_t x_170; uint8_t x_171; uint8_t x_172; 
x_169 = lean_unsigned_to_nat(1u);
x_170 = lean_nat_dec_eq(x_166, x_169);
lean_dec(x_166);
x_171 = 1;
x_172 = l_Bool_DecidableEq(x_170, x_171);
if (x_172 == 0)
{
lean_object* x_173; lean_object* x_174; 
lean_dec(x_5);
x_173 = l_Lean_IR_EmitC_emitMainFn___closed__1;
x_174 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_174, 0, x_173);
lean_ctor_set(x_174, 1, x_164);
return x_174;
}
else
{
lean_object* x_175; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; uint8_t x_219; uint8_t x_220; 
x_215 = l_Lean_IR_EmitC_getEnv(x_1, x_164);
x_216 = lean_ctor_get(x_215, 0);
lean_inc(x_216);
x_217 = lean_ctor_get(x_215, 1);
lean_inc(x_217);
lean_dec(x_215);
x_218 = l_Lean_IR_usesLeanNamespace(x_216, x_5);
x_219 = lean_unbox(x_218);
lean_dec(x_218);
x_220 = l_Bool_DecidableEq(x_219, x_171);
if (x_220 == 0)
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; 
x_221 = l_Lean_IR_EmitC_emitMainFn___closed__46;
x_222 = lean_string_append(x_217, x_221);
x_223 = l_IO_println___rarg___closed__1;
x_224 = lean_string_append(x_222, x_223);
x_225 = l_Lean_IR_EmitC_emitMainFn___closed__47;
x_226 = lean_string_append(x_224, x_225);
x_227 = lean_string_append(x_226, x_223);
x_228 = l_Lean_IR_EmitC_emitMainFn___closed__48;
x_229 = lean_string_append(x_227, x_228);
x_230 = lean_string_append(x_229, x_223);
x_175 = x_230;
goto block_214;
}
else
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; 
x_231 = l_Lean_IR_EmitC_emitMainFn___closed__49;
x_232 = lean_string_append(x_217, x_231);
x_233 = l_IO_println___rarg___closed__1;
x_234 = lean_string_append(x_232, x_233);
x_235 = l_Lean_IR_EmitC_emitMainFn___closed__47;
x_236 = lean_string_append(x_234, x_235);
x_237 = lean_string_append(x_236, x_233);
x_238 = l_Lean_IR_EmitC_emitMainFn___closed__50;
x_239 = lean_string_append(x_237, x_238);
x_240 = lean_string_append(x_239, x_233);
x_175 = x_240;
goto block_214;
}
block_214:
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_201; lean_object* x_202; lean_object* x_203; uint8_t x_204; 
x_176 = l_Lean_IR_EmitC_getModName(x_1, x_175);
x_177 = lean_ctor_get(x_176, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_176, 1);
lean_inc(x_178);
lean_dec(x_176);
x_179 = l_String_splitAux___main___closed__1;
x_180 = lean_name_mangle(x_177, x_179);
x_181 = l_Lean_IR_EmitC_emitMainFn___closed__2;
x_182 = lean_string_append(x_181, x_180);
lean_dec(x_180);
x_183 = l_Lean_IR_EmitC_emitMainFn___closed__3;
x_184 = lean_string_append(x_182, x_183);
x_185 = lean_string_append(x_178, x_184);
lean_dec(x_184);
x_186 = l_IO_println___rarg___closed__1;
x_187 = lean_string_append(x_185, x_186);
x_201 = l_Lean_IR_EmitC_emitMainFn___closed__26;
x_202 = l_List_forM___main___at_Lean_IR_EmitC_emitMainFn___spec__2(x_201, x_1, x_187);
x_203 = lean_ctor_get(x_202, 1);
lean_inc(x_203);
lean_dec(x_202);
x_204 = l_Bool_DecidableEq(x_168, x_171);
if (x_204 == 0)
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_205 = l_Lean_IR_EmitC_emitMainFn___closed__29;
x_206 = lean_string_append(x_203, x_205);
x_207 = lean_string_append(x_206, x_186);
x_188 = x_207;
goto block_200;
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_208 = l_Lean_IR_EmitC_emitMainFn___closed__43;
x_209 = l_List_forM___main___at_Lean_IR_EmitC_emitMainFn___spec__2(x_208, x_1, x_203);
x_210 = lean_ctor_get(x_209, 1);
lean_inc(x_210);
lean_dec(x_209);
x_211 = l_Lean_IR_EmitC_emitMainFn___closed__45;
x_212 = lean_string_append(x_210, x_211);
x_213 = lean_string_append(x_212, x_186);
x_188 = x_213;
goto block_200;
}
block_200:
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_189 = l_PersistentArray_Stats_toString___closed__4;
x_190 = lean_string_append(x_188, x_189);
x_191 = lean_string_append(x_190, x_186);
x_192 = l_Lean_IR_EmitC_emitMainFn___closed__19;
x_193 = l_List_forM___main___at_Lean_IR_EmitC_emitMainFn___spec__2(x_192, x_1, x_191);
x_194 = lean_ctor_get(x_193, 1);
lean_inc(x_194);
if (lean_is_exclusive(x_193)) {
 lean_ctor_release(x_193, 0);
 lean_ctor_release(x_193, 1);
 x_195 = x_193;
} else {
 lean_dec_ref(x_193);
 x_195 = lean_box(0);
}
x_196 = lean_string_append(x_194, x_189);
x_197 = lean_string_append(x_196, x_186);
x_198 = lean_box(0);
if (lean_is_scalar(x_195)) {
 x_199 = lean_alloc_ctor(0, 2, 0);
} else {
 x_199 = x_195;
}
lean_ctor_set(x_199, 0, x_198);
lean_ctor_set(x_199, 1, x_197);
return x_199;
}
}
}
}
else
{
uint8_t x_241; 
lean_dec(x_166);
x_241 = l_String_Iterator_extract___closed__1;
if (x_241 == 0)
{
lean_object* x_242; lean_object* x_243; 
lean_dec(x_5);
x_242 = l_Lean_IR_EmitC_emitMainFn___closed__1;
x_243 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_243, 0, x_242);
lean_ctor_set(x_243, 1, x_164);
return x_243;
}
else
{
lean_object* x_244; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; uint8_t x_289; uint8_t x_290; uint8_t x_291; 
x_285 = l_Lean_IR_EmitC_getEnv(x_1, x_164);
x_286 = lean_ctor_get(x_285, 0);
lean_inc(x_286);
x_287 = lean_ctor_get(x_285, 1);
lean_inc(x_287);
lean_dec(x_285);
x_288 = l_Lean_IR_usesLeanNamespace(x_286, x_5);
x_289 = lean_unbox(x_288);
lean_dec(x_288);
x_290 = 1;
x_291 = l_Bool_DecidableEq(x_289, x_290);
if (x_291 == 0)
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; 
x_292 = l_Lean_IR_EmitC_emitMainFn___closed__46;
x_293 = lean_string_append(x_287, x_292);
x_294 = l_IO_println___rarg___closed__1;
x_295 = lean_string_append(x_293, x_294);
x_296 = l_Lean_IR_EmitC_emitMainFn___closed__47;
x_297 = lean_string_append(x_295, x_296);
x_298 = lean_string_append(x_297, x_294);
x_299 = l_Lean_IR_EmitC_emitMainFn___closed__48;
x_300 = lean_string_append(x_298, x_299);
x_301 = lean_string_append(x_300, x_294);
x_244 = x_301;
goto block_284;
}
else
{
lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; 
x_302 = l_Lean_IR_EmitC_emitMainFn___closed__49;
x_303 = lean_string_append(x_287, x_302);
x_304 = l_IO_println___rarg___closed__1;
x_305 = lean_string_append(x_303, x_304);
x_306 = l_Lean_IR_EmitC_emitMainFn___closed__47;
x_307 = lean_string_append(x_305, x_306);
x_308 = lean_string_append(x_307, x_304);
x_309 = l_Lean_IR_EmitC_emitMainFn___closed__50;
x_310 = lean_string_append(x_308, x_309);
x_311 = lean_string_append(x_310, x_304);
x_244 = x_311;
goto block_284;
}
block_284:
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_270; lean_object* x_271; lean_object* x_272; uint8_t x_273; uint8_t x_274; 
x_245 = l_Lean_IR_EmitC_getModName(x_1, x_244);
x_246 = lean_ctor_get(x_245, 0);
lean_inc(x_246);
x_247 = lean_ctor_get(x_245, 1);
lean_inc(x_247);
lean_dec(x_245);
x_248 = l_String_splitAux___main___closed__1;
x_249 = lean_name_mangle(x_246, x_248);
x_250 = l_Lean_IR_EmitC_emitMainFn___closed__2;
x_251 = lean_string_append(x_250, x_249);
lean_dec(x_249);
x_252 = l_Lean_IR_EmitC_emitMainFn___closed__3;
x_253 = lean_string_append(x_251, x_252);
x_254 = lean_string_append(x_247, x_253);
lean_dec(x_253);
x_255 = l_IO_println___rarg___closed__1;
x_256 = lean_string_append(x_254, x_255);
x_270 = l_Lean_IR_EmitC_emitMainFn___closed__26;
x_271 = l_List_forM___main___at_Lean_IR_EmitC_emitMainFn___spec__2(x_270, x_1, x_256);
x_272 = lean_ctor_get(x_271, 1);
lean_inc(x_272);
lean_dec(x_271);
x_273 = 1;
x_274 = l_Bool_DecidableEq(x_168, x_273);
if (x_274 == 0)
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; 
x_275 = l_Lean_IR_EmitC_emitMainFn___closed__29;
x_276 = lean_string_append(x_272, x_275);
x_277 = lean_string_append(x_276, x_255);
x_257 = x_277;
goto block_269;
}
else
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; 
x_278 = l_Lean_IR_EmitC_emitMainFn___closed__43;
x_279 = l_List_forM___main___at_Lean_IR_EmitC_emitMainFn___spec__2(x_278, x_1, x_272);
x_280 = lean_ctor_get(x_279, 1);
lean_inc(x_280);
lean_dec(x_279);
x_281 = l_Lean_IR_EmitC_emitMainFn___closed__45;
x_282 = lean_string_append(x_280, x_281);
x_283 = lean_string_append(x_282, x_255);
x_257 = x_283;
goto block_269;
}
block_269:
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; 
x_258 = l_PersistentArray_Stats_toString___closed__4;
x_259 = lean_string_append(x_257, x_258);
x_260 = lean_string_append(x_259, x_255);
x_261 = l_Lean_IR_EmitC_emitMainFn___closed__19;
x_262 = l_List_forM___main___at_Lean_IR_EmitC_emitMainFn___spec__2(x_261, x_1, x_260);
x_263 = lean_ctor_get(x_262, 1);
lean_inc(x_263);
if (lean_is_exclusive(x_262)) {
 lean_ctor_release(x_262, 0);
 lean_ctor_release(x_262, 1);
 x_264 = x_262;
} else {
 lean_dec_ref(x_262);
 x_264 = lean_box(0);
}
x_265 = lean_string_append(x_263, x_258);
x_266 = lean_string_append(x_265, x_255);
x_267 = lean_box(0);
if (lean_is_scalar(x_264)) {
 x_268 = lean_alloc_ctor(0, 2, 0);
} else {
 x_268 = x_264;
}
lean_ctor_set(x_268, 0, x_267);
lean_ctor_set(x_268, 1, x_266);
return x_268;
}
}
}
}
}
}
else
{
uint8_t x_312; 
lean_dec(x_5);
x_312 = !lean_is_exclusive(x_4);
if (x_312 == 0)
{
lean_object* x_313; lean_object* x_314; 
x_313 = lean_ctor_get(x_4, 0);
lean_dec(x_313);
x_314 = l_Lean_IR_EmitC_emitMainFn___closed__51;
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_314);
return x_4;
}
else
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; 
x_315 = lean_ctor_get(x_4, 1);
lean_inc(x_315);
lean_dec(x_4);
x_316 = l_Lean_IR_EmitC_emitMainFn___closed__51;
x_317 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_317, 0, x_316);
lean_ctor_set(x_317, 1, x_315);
return x_317;
}
}
}
else
{
uint8_t x_318; 
x_318 = !lean_is_exclusive(x_4);
if (x_318 == 0)
{
return x_4;
}
else
{
lean_object* x_319; lean_object* x_320; lean_object* x_321; 
x_319 = lean_ctor_get(x_4, 0);
x_320 = lean_ctor_get(x_4, 1);
lean_inc(x_320);
lean_inc(x_319);
lean_dec(x_4);
x_321 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_321, 0, x_319);
lean_ctor_set(x_321, 1, x_320);
return x_321;
}
}
}
}
lean_object* l_List_forM___main___at_Lean_IR_EmitC_emitMainFn___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_forM___main___at_Lean_IR_EmitC_emitMainFn___spec__2(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_IR_EmitC_emitLns___at_Lean_IR_EmitC_emitMainFn___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_EmitC_emitLns___at_Lean_IR_EmitC_emitMainFn___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_IR_EmitC_emitMainFn___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_EmitC_emitMainFn(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
uint8_t l_List_foldr___main___at_Lean_IR_EmitC_hasMainFn___spec__1(uint8_t x_1, lean_object* x_2) {
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
x_5 = l_List_foldr___main___at_Lean_IR_EmitC_hasMainFn___spec__1(x_1, x_4);
x_6 = l_Lean_IR_Decl_name(x_3);
x_7 = l_Lean_IR_EmitC_toCName___closed__2;
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
lean_object* l_Lean_IR_EmitC_hasMainFn(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lean_IR_EmitC_getEnv(x_1, x_2);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = l_Lean_IR_declMapExt;
x_7 = l_Lean_SimplePersistentEnvExtension_getEntries___rarg(x_6, x_5);
lean_dec(x_5);
x_8 = 0;
x_9 = l_List_foldr___main___at_Lean_IR_EmitC_hasMainFn___spec__1(x_8, x_7);
lean_dec(x_7);
x_10 = lean_box(x_9);
lean_ctor_set(x_3, 0, x_10);
return x_3;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_3);
x_13 = l_Lean_IR_declMapExt;
x_14 = l_Lean_SimplePersistentEnvExtension_getEntries___rarg(x_13, x_11);
lean_dec(x_11);
x_15 = 0;
x_16 = l_List_foldr___main___at_Lean_IR_EmitC_hasMainFn___spec__1(x_15, x_14);
lean_dec(x_14);
x_17 = lean_box(x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_12);
return x_18;
}
}
}
lean_object* l_List_foldr___main___at_Lean_IR_EmitC_hasMainFn___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_List_foldr___main___at_Lean_IR_EmitC_hasMainFn___spec__1(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
lean_object* l_Lean_IR_EmitC_hasMainFn___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_EmitC_hasMainFn(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_IR_EmitC_emitMainFnIfNeeded(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_IR_EmitC_emitMainFnIfNeeded___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_EmitC_emitMainFnIfNeeded(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Array_forMAux___main___at_Lean_IR_EmitC_emitFileHeader___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_1);
x_6 = lean_nat_dec_lt(x_2, x_5);
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
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; 
x_9 = lean_array_fget(x_1, x_2);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_2, x_10);
lean_dec(x_2);
x_12 = lean_ctor_get(x_9, 0);
lean_inc(x_12);
x_13 = l_System_FilePath_dirName___closed__1;
x_14 = l_Lean_Name_toStringWithSep___main(x_13, x_12);
x_15 = lean_ctor_get_uint8(x_9, sizeof(void*)*1);
lean_dec(x_9);
x_16 = 1;
x_17 = l_Bool_DecidableEq(x_15, x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = l_String_splitAux___main___closed__1;
x_19 = lean_string_append(x_14, x_18);
x_20 = l_String_Iterator_HasRepr___closed__2;
x_21 = lean_string_append(x_20, x_19);
lean_dec(x_19);
x_22 = lean_string_append(x_4, x_21);
lean_dec(x_21);
x_2 = x_11;
x_4 = x_22;
goto _start;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = l_Lean_HasToString___closed__1;
x_25 = lean_string_append(x_14, x_24);
x_26 = l_String_Iterator_HasRepr___closed__2;
x_27 = lean_string_append(x_26, x_25);
lean_dec(x_25);
x_28 = lean_string_append(x_4, x_27);
lean_dec(x_27);
x_2 = x_11;
x_4 = x_28;
goto _start;
}
}
}
}
lean_object* _init_l_Lean_IR_EmitC_emitFileHeader___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("// Lean compiler output");
return x_1;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitFileHeader___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("// Module: ");
return x_1;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitFileHeader___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("// Imports:");
return x_1;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitFileHeader___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("#include \"runtime/lean.h\"");
return x_1;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitFileHeader___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("#endif");
return x_1;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitFileHeader___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_IR_EmitC_emitFileHeader___closed__5;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitFileHeader___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("extern \"C\" {");
return x_1;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitFileHeader___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_EmitC_emitFileHeader___closed__7;
x_2 = l_Lean_IR_EmitC_emitFileHeader___closed__6;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitFileHeader___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("#ifdef __cplusplus");
return x_1;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitFileHeader___closed__10() {
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
lean_object* _init_l_Lean_IR_EmitC_emitFileHeader___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_EmitC_emitFileHeader___closed__5;
x_2 = l_Lean_IR_EmitC_emitFileHeader___closed__10;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitFileHeader___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("#pragma GCC diagnostic ignored \"-Wunused-but-set-variable\"");
return x_1;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitFileHeader___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_EmitC_emitFileHeader___closed__12;
x_2 = l_Lean_IR_EmitC_emitFileHeader___closed__11;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitFileHeader___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("#pragma GCC diagnostic ignored \"-Wunused-label\"");
return x_1;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitFileHeader___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_EmitC_emitFileHeader___closed__14;
x_2 = l_Lean_IR_EmitC_emitFileHeader___closed__13;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitFileHeader___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("#pragma GCC diagnostic ignored \"-Wunused-parameter\"");
return x_1;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitFileHeader___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_EmitC_emitFileHeader___closed__16;
x_2 = l_Lean_IR_EmitC_emitFileHeader___closed__15;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitFileHeader___closed__18() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("#elif defined(__GNUC__) && !defined(__CLANG__)");
return x_1;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitFileHeader___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_EmitC_emitFileHeader___closed__18;
x_2 = l_Lean_IR_EmitC_emitFileHeader___closed__17;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitFileHeader___closed__20() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("#pragma clang diagnostic ignored \"-Wunused-label\"");
return x_1;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitFileHeader___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_EmitC_emitFileHeader___closed__20;
x_2 = l_Lean_IR_EmitC_emitFileHeader___closed__19;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitFileHeader___closed__22() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("#pragma clang diagnostic ignored \"-Wunused-parameter\"");
return x_1;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitFileHeader___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_EmitC_emitFileHeader___closed__22;
x_2 = l_Lean_IR_EmitC_emitFileHeader___closed__21;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitFileHeader___closed__24() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("#if defined(__clang__)");
return x_1;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitFileHeader___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_EmitC_emitFileHeader___closed__24;
x_2 = l_Lean_IR_EmitC_emitFileHeader___closed__23;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_IR_EmitC_emitFileHeader(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
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
x_9 = l_Lean_IR_EmitC_emitFileHeader___closed__1;
x_10 = lean_string_append(x_8, x_9);
x_11 = l_IO_println___rarg___closed__1;
x_12 = lean_string_append(x_10, x_11);
x_13 = l_System_FilePath_dirName___closed__1;
x_14 = l_Lean_Name_toStringWithSep___main(x_13, x_7);
x_15 = l_Lean_IR_EmitC_emitFileHeader___closed__2;
x_16 = lean_string_append(x_15, x_14);
lean_dec(x_14);
x_17 = lean_string_append(x_12, x_16);
lean_dec(x_16);
x_18 = lean_string_append(x_17, x_11);
x_19 = l_Lean_IR_EmitC_emitFileHeader___closed__3;
x_20 = lean_string_append(x_18, x_19);
x_21 = l_Lean_Environment_imports(x_4);
lean_dec(x_4);
x_22 = lean_unsigned_to_nat(0u);
x_23 = l_Array_forMAux___main___at_Lean_IR_EmitC_emitFileHeader___spec__1(x_21, x_22, x_1, x_20);
lean_dec(x_21);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = l_String_splitAux___main___closed__1;
x_26 = lean_string_append(x_24, x_25);
x_27 = lean_string_append(x_26, x_11);
x_28 = l_Lean_IR_EmitC_emitFileHeader___closed__4;
x_29 = lean_string_append(x_27, x_28);
x_30 = lean_string_append(x_29, x_11);
x_31 = l_Lean_IR_EmitC_emitFileHeader___closed__25;
x_32 = l_List_forM___main___at_Lean_IR_EmitC_emitMainFn___spec__2(x_31, x_1, x_30);
return x_32;
}
}
lean_object* l_Array_forMAux___main___at_Lean_IR_EmitC_emitFileHeader___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_forMAux___main___at_Lean_IR_EmitC_emitFileHeader___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_IR_EmitC_emitFileHeader___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_EmitC_emitFileHeader(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitFileFooter___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_PersistentArray_Stats_toString___closed__4;
x_2 = l_Lean_IR_EmitC_emitFileHeader___closed__6;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitFileFooter___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_EmitC_emitFileHeader___closed__9;
x_2 = l_Lean_IR_EmitC_emitFileFooter___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_IR_EmitC_emitFileFooter(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_IR_EmitC_emitFileFooter___closed__2;
x_4 = l_List_forM___main___at_Lean_IR_EmitC_emitMainFn___spec__2(x_3, x_1, x_2);
return x_4;
}
}
lean_object* l_Lean_IR_EmitC_emitFileFooter___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_EmitC_emitFileFooter(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* _init_l_Lean_IR_EmitC_throwUnknownVar___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unknown variable '");
return x_1;
}
}
lean_object* l_Lean_IR_EmitC_throwUnknownVar___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = l_Nat_repr(x_1);
x_5 = l_Lean_IR_VarId_HasToString___closed__1;
x_6 = lean_string_append(x_5, x_4);
lean_dec(x_4);
x_7 = l_Lean_IR_EmitC_throwUnknownVar___rarg___closed__1;
x_8 = lean_string_append(x_7, x_6);
lean_dec(x_6);
x_9 = l_Char_HasRepr___closed__1;
x_10 = lean_string_append(x_8, x_9);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_3);
return x_11;
}
}
lean_object* l_Lean_IR_EmitC_throwUnknownVar(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_IR_EmitC_throwUnknownVar___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Lean_IR_EmitC_throwUnknownVar___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_EmitC_throwUnknownVar___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_AssocList_find___main___at_Lean_IR_EmitC_getJPParams___spec__2(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_HashMapImp_find___at_Lean_IR_EmitC_getJPParams___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; size_t x_5; size_t x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = lean_usize_of_nat(x_2);
x_6 = lean_usize_modn(x_5, x_4);
lean_dec(x_4);
x_7 = lean_array_uget(x_3, x_6);
x_8 = l_AssocList_find___main___at_Lean_IR_EmitC_getJPParams___spec__2(x_2, x_7);
lean_dec(x_7);
return x_8;
}
}
lean_object* _init_l_Lean_IR_EmitC_getJPParams___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unknown join point");
return x_1;
}
}
lean_object* l_Lean_IR_EmitC_getJPParams(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 2);
x_5 = l_HashMapImp_find___at_Lean_IR_EmitC_getJPParams___spec__1(x_4, x_1);
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
lean_object* l_AssocList_find___main___at_Lean_IR_EmitC_getJPParams___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_AssocList_find___main___at_Lean_IR_EmitC_getJPParams___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_HashMapImp_find___at_Lean_IR_EmitC_getJPParams___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_HashMapImp_find___at_Lean_IR_EmitC_getJPParams___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_IR_EmitC_getJPParams___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_EmitC_getJPParams(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* _init_l_Lean_IR_EmitC_declareVar___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("; ");
return x_1;
}
}
lean_object* l_Lean_IR_EmitC_declareVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_5 = l_Lean_IR_EmitC_toCType(x_2);
x_6 = lean_string_append(x_4, x_5);
lean_dec(x_5);
x_7 = l_String_Iterator_HasRepr___closed__2;
x_8 = lean_string_append(x_6, x_7);
x_9 = l_Nat_repr(x_1);
x_10 = l_Lean_IR_VarId_HasToString___closed__1;
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
lean_object* l_Lean_IR_EmitC_declareVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_EmitC_declareVar(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Array_forMAux___main___at_Lean_IR_EmitC_declareParams___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_1);
x_6 = lean_nat_dec_lt(x_2, x_5);
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
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_array_fget(x_1, x_2);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_2, x_10);
lean_dec(x_2);
x_12 = lean_ctor_get(x_9, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_9, 1);
lean_inc(x_13);
lean_dec(x_9);
x_14 = l_Lean_IR_EmitC_declareVar(x_12, x_13, x_3, x_4);
lean_dec(x_13);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_2 = x_11;
x_4 = x_15;
goto _start;
}
}
}
lean_object* l_Lean_IR_EmitC_declareParams(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Array_forMAux___main___at_Lean_IR_EmitC_declareParams___spec__1(x_1, x_4, x_2, x_3);
return x_5;
}
}
lean_object* l_Array_forMAux___main___at_Lean_IR_EmitC_declareParams___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_forMAux___main___at_Lean_IR_EmitC_declareParams___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_IR_EmitC_declareParams___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_EmitC_declareParams(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_IR_EmitC_declareVars___main(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; 
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 3);
lean_inc(x_16);
x_17 = lean_ctor_get(x_3, 3);
x_18 = l_Lean_IR_isTailCallTo(x_17, x_1);
lean_dec(x_1);
x_19 = 1;
x_20 = l_Bool_DecidableEq(x_18, x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = l_Lean_IR_EmitC_declareVar(x_14, x_15, x_3, x_4);
lean_dec(x_15);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_1 = x_16;
x_2 = x_19;
x_4 = x_22;
goto _start;
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
x_24 = lean_box(x_2);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_4);
return x_25;
}
}
case 1:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_1, 1);
lean_inc(x_26);
x_27 = lean_ctor_get(x_1, 3);
lean_inc(x_27);
lean_dec(x_1);
x_28 = lean_unsigned_to_nat(0u);
x_29 = l_Array_forMAux___main___at_Lean_IR_EmitC_declareParams___spec__1(x_26, x_28, x_3, x_4);
if (x_2 == 0)
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_31 = lean_array_get_size(x_26);
lean_dec(x_26);
x_32 = lean_nat_dec_lt(x_28, x_31);
lean_dec(x_31);
x_1 = x_27;
x_2 = x_32;
x_4 = x_30;
goto _start;
}
else
{
lean_object* x_34; uint8_t x_35; 
lean_dec(x_26);
x_34 = lean_ctor_get(x_29, 1);
lean_inc(x_34);
lean_dec(x_29);
x_35 = 1;
x_1 = x_27;
x_2 = x_35;
x_4 = x_34;
goto _start;
}
}
default: 
{
lean_object* x_37; 
x_37 = lean_box(0);
x_5 = x_37;
goto block_13;
}
}
block_13:
{
uint8_t x_6; uint8_t x_7; uint8_t x_8; 
lean_dec(x_5);
x_6 = l_Lean_IR_FnBody_isTerminal(x_1);
x_7 = 1;
x_8 = l_Bool_DecidableEq(x_6, x_7);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = l_Lean_IR_FnBody_body(x_1);
lean_dec(x_1);
x_1 = x_9;
goto _start;
}
else
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_1);
x_11 = lean_box(x_2);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_4);
return x_12;
}
}
}
}
lean_object* l_Lean_IR_EmitC_declareVars___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Lean_IR_EmitC_declareVars___main(x_1, x_5, x_3, x_4);
lean_dec(x_3);
return x_6;
}
}
lean_object* l_Lean_IR_EmitC_declareVars(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_EmitC_declareVars___main(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_IR_EmitC_declareVars___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Lean_IR_EmitC_declareVars(x_1, x_5, x_3, x_4);
lean_dec(x_3);
return x_6;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitTag___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("lean_obj_tag(");
return x_1;
}
}
lean_object* l_Lean_IR_EmitC_emitTag(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; uint8_t x_7; 
x_5 = l_Lean_IR_IRType_isObj(x_2);
x_6 = 1;
x_7 = l_Bool_DecidableEq(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = l_Nat_repr(x_1);
x_9 = l_Lean_IR_VarId_HasToString___closed__1;
x_10 = lean_string_append(x_9, x_8);
lean_dec(x_8);
x_11 = lean_string_append(x_4, x_10);
lean_dec(x_10);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_14 = l_Lean_IR_EmitC_emitTag___closed__1;
x_15 = lean_string_append(x_4, x_14);
x_16 = l_Nat_repr(x_1);
x_17 = l_Lean_IR_VarId_HasToString___closed__1;
x_18 = lean_string_append(x_17, x_16);
lean_dec(x_16);
x_19 = lean_string_append(x_15, x_18);
lean_dec(x_18);
x_20 = l_Option_HasRepr___rarg___closed__3;
x_21 = lean_string_append(x_19, x_20);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
}
lean_object* l_Lean_IR_EmitC_emitTag___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_EmitC_emitTag(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_IR_EmitC_isIf(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(2u);
x_4 = lean_nat_dec_eq(x_2, x_3);
lean_dec(x_2);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = l_String_Iterator_extract___closed__1;
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Lean_IR_altInh;
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
else
{
lean_object* x_19; 
x_19 = lean_box(0);
return x_19;
}
}
else
{
uint8_t x_20; 
x_20 = l_String_anyAux___main___at_String_all___spec__1___closed__1;
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = l_Lean_IR_altInh;
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_array_get(x_21, x_1, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_array_get(x_21, x_1, x_27);
x_29 = l_Lean_IR_AltCore_body(x_28);
lean_dec(x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_25);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_26);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
return x_32;
}
else
{
lean_object* x_33; 
lean_dec(x_23);
x_33 = lean_box(0);
return x_33;
}
}
else
{
lean_object* x_34; 
x_34 = lean_box(0);
return x_34;
}
}
}
}
lean_object* l_Lean_IR_EmitC_isIf___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_IR_EmitC_isIf(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitIf___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("if (");
return x_1;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitIf___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" == ");
return x_1;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitIf___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("else");
return x_1;
}
}
lean_object* l_Lean_IR_EmitC_emitIf(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_9 = l_Lean_IR_EmitC_emitIf___closed__1;
x_10 = lean_string_append(x_8, x_9);
x_11 = l_Lean_IR_EmitC_emitTag(x_2, x_3, x_7, x_10);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = l_Lean_IR_EmitC_emitIf___closed__2;
x_14 = lean_string_append(x_12, x_13);
x_15 = l_Nat_repr(x_4);
x_16 = lean_string_append(x_14, x_15);
lean_dec(x_15);
x_17 = l_Option_HasRepr___rarg___closed__3;
x_18 = lean_string_append(x_16, x_17);
x_19 = l_IO_println___rarg___closed__1;
x_20 = lean_string_append(x_18, x_19);
lean_inc(x_1);
lean_inc(x_7);
x_21 = lean_apply_3(x_1, x_5, x_7, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = l_Lean_IR_EmitC_emitIf___closed__3;
x_24 = lean_string_append(x_22, x_23);
x_25 = lean_string_append(x_24, x_19);
x_26 = lean_apply_3(x_1, x_6, x_7, x_25);
return x_26;
}
else
{
uint8_t x_27; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_21);
if (x_27 == 0)
{
return x_21;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_21, 0);
x_29 = lean_ctor_get(x_21, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_21);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
lean_object* l_Lean_IR_EmitC_emitIf___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_IR_EmitC_emitIf(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_9;
}
}
lean_object* _init_l_Array_forMAux___main___at_Lean_IR_EmitC_emitCase___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("default: ");
return x_1;
}
}
lean_object* l_Array_forMAux___main___at_Lean_IR_EmitC_emitCase___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_2);
x_7 = lean_nat_dec_lt(x_3, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_5);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_array_fget(x_2, x_3);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_3, x_11);
lean_dec(x_3);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_10, 1);
lean_inc(x_14);
lean_dec(x_10);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_IR_formatFnBodyHead___closed__29;
x_17 = lean_string_append(x_5, x_16);
x_18 = l_Nat_repr(x_15);
x_19 = lean_string_append(x_17, x_18);
lean_dec(x_18);
x_20 = l___private_Init_Util_1__mkPanicMessage___closed__2;
x_21 = lean_string_append(x_19, x_20);
x_22 = l_IO_println___rarg___closed__1;
x_23 = lean_string_append(x_21, x_22);
lean_inc(x_1);
lean_inc(x_4);
x_24 = lean_apply_3(x_1, x_14, x_4, x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_3 = x_12;
x_5 = x_25;
goto _start;
}
else
{
uint8_t x_27; 
lean_dec(x_12);
lean_dec(x_4);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_24);
if (x_27 == 0)
{
return x_24;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_24, 0);
x_29 = lean_ctor_get(x_24, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_24);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_31 = lean_ctor_get(x_10, 0);
lean_inc(x_31);
lean_dec(x_10);
x_32 = l_Array_forMAux___main___at_Lean_IR_EmitC_emitCase___spec__1___closed__1;
x_33 = lean_string_append(x_5, x_32);
x_34 = l_IO_println___rarg___closed__1;
x_35 = lean_string_append(x_33, x_34);
lean_inc(x_1);
lean_inc(x_4);
x_36 = lean_apply_3(x_1, x_31, x_4, x_35);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
x_3 = x_12;
x_5 = x_37;
goto _start;
}
else
{
uint8_t x_39; 
lean_dec(x_12);
lean_dec(x_4);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_36);
if (x_39 == 0)
{
return x_36;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_36, 0);
x_41 = lean_ctor_get(x_36, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_36);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
}
}
}
lean_object* _init_l_Lean_IR_EmitC_emitCase___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("switch (");
return x_1;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitCase___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(") {");
return x_1;
}
}
lean_object* l_Lean_IR_EmitC_emitCase(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_IR_EmitC_isIf(x_4);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_8 = l_Lean_IR_EmitC_emitCase___closed__1;
x_9 = lean_string_append(x_6, x_8);
x_10 = l_Lean_IR_EmitC_emitTag(x_2, x_3, x_5, x_9);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = l_Lean_IR_EmitC_emitCase___closed__2;
x_13 = lean_string_append(x_11, x_12);
x_14 = l_IO_println___rarg___closed__1;
x_15 = lean_string_append(x_13, x_14);
x_16 = l_Lean_IR_ensureHasDefault(x_4);
x_17 = lean_unsigned_to_nat(0u);
x_18 = l_Array_forMAux___main___at_Lean_IR_EmitC_emitCase___spec__1(x_1, x_16, x_17, x_5, x_15);
lean_dec(x_16);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_18, 1);
x_21 = lean_ctor_get(x_18, 0);
lean_dec(x_21);
x_22 = l_PersistentArray_Stats_toString___closed__4;
x_23 = lean_string_append(x_20, x_22);
x_24 = lean_string_append(x_23, x_14);
x_25 = lean_box(0);
lean_ctor_set(x_18, 1, x_24);
lean_ctor_set(x_18, 0, x_25);
return x_18;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_26 = lean_ctor_get(x_18, 1);
lean_inc(x_26);
lean_dec(x_18);
x_27 = l_PersistentArray_Stats_toString___closed__4;
x_28 = lean_string_append(x_26, x_27);
x_29 = lean_string_append(x_28, x_14);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
else
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_18);
if (x_32 == 0)
{
return x_18;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_18, 0);
x_34 = lean_ctor_get(x_18, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_18);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_4);
x_36 = lean_ctor_get(x_7, 0);
lean_inc(x_36);
lean_dec(x_7);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 0);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_ctor_get(x_37, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
lean_dec(x_37);
x_41 = l_Lean_IR_EmitC_emitIf(x_1, x_2, x_3, x_38, x_39, x_40, x_5, x_6);
return x_41;
}
}
}
lean_object* l_Array_forMAux___main___at_Lean_IR_EmitC_emitCase___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_forMAux___main___at_Lean_IR_EmitC_emitCase___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Lean_IR_EmitC_emitCase___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_IR_EmitC_emitCase(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
return x_7;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitInc___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(");");
return x_1;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitInc___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("lean_inc_ref_n");
return x_1;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitInc___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("lean_inc_ref");
return x_1;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitInc___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("lean_inc_n");
return x_1;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitInc___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("lean_inc");
return x_1;
}
}
lean_object* l_Lean_IR_EmitC_emitInc(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_6 = 1;
x_7 = l_Bool_DecidableEq(x_3, x_6);
x_8 = l_Nat_repr(x_1);
x_9 = l_Lean_IR_VarId_HasToString___closed__1;
x_10 = lean_string_append(x_9, x_8);
lean_dec(x_8);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_dec_eq(x_2, x_11);
if (x_7 == 0)
{
uint8_t x_53; 
x_53 = l_Bool_DecidableEq(x_12, x_6);
if (x_53 == 0)
{
lean_object* x_54; 
x_54 = l_Lean_IR_EmitC_emitInc___closed__2;
x_13 = x_54;
goto block_52;
}
else
{
lean_object* x_55; 
x_55 = l_Lean_IR_EmitC_emitInc___closed__3;
x_13 = x_55;
goto block_52;
}
}
else
{
uint8_t x_56; 
x_56 = l_Bool_DecidableEq(x_12, x_6);
if (x_56 == 0)
{
lean_object* x_57; 
x_57 = l_Lean_IR_EmitC_emitInc___closed__4;
x_13 = x_57;
goto block_52;
}
else
{
lean_object* x_58; 
x_58 = l_Lean_IR_EmitC_emitInc___closed__5;
x_13 = x_58;
goto block_52;
}
}
block_52:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_string_append(x_5, x_13);
lean_dec(x_13);
x_15 = l_Prod_HasRepr___rarg___closed__1;
x_16 = lean_string_append(x_14, x_15);
x_17 = lean_string_append(x_16, x_10);
lean_dec(x_10);
if (x_12 == 0)
{
uint8_t x_18; 
x_18 = l_String_Iterator_extract___closed__1;
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_2);
x_19 = l_Lean_IR_EmitC_emitInc___closed__1;
x_20 = lean_string_append(x_17, x_19);
x_21 = l_IO_println___rarg___closed__1;
x_22 = lean_string_append(x_20, x_21);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_25 = l_List_reprAux___main___rarg___closed__1;
x_26 = lean_string_append(x_17, x_25);
x_27 = l_Nat_repr(x_2);
x_28 = lean_string_append(x_26, x_27);
lean_dec(x_27);
x_29 = l_Lean_IR_EmitC_emitInc___closed__1;
x_30 = lean_string_append(x_28, x_29);
x_31 = l_IO_println___rarg___closed__1;
x_32 = lean_string_append(x_30, x_31);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
}
else
{
uint8_t x_35; 
x_35 = l_String_anyAux___main___at_String_all___spec__1___closed__1;
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_2);
x_36 = l_Lean_IR_EmitC_emitInc___closed__1;
x_37 = lean_string_append(x_17, x_36);
x_38 = l_IO_println___rarg___closed__1;
x_39 = lean_string_append(x_37, x_38);
x_40 = lean_box(0);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_42 = l_List_reprAux___main___rarg___closed__1;
x_43 = lean_string_append(x_17, x_42);
x_44 = l_Nat_repr(x_2);
x_45 = lean_string_append(x_43, x_44);
lean_dec(x_44);
x_46 = l_Lean_IR_EmitC_emitInc___closed__1;
x_47 = lean_string_append(x_45, x_46);
x_48 = l_IO_println___rarg___closed__1;
x_49 = lean_string_append(x_47, x_48);
x_50 = lean_box(0);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_49);
return x_51;
}
}
}
}
}
lean_object* l_Lean_IR_EmitC_emitInc___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_3);
lean_dec(x_3);
x_7 = l_Lean_IR_EmitC_emitInc(x_1, x_2, x_6, x_4, x_5);
lean_dec(x_4);
return x_7;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitDec___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("lean_dec_ref");
return x_1;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitDec___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("lean_dec");
return x_1;
}
}
lean_object* l_Lean_IR_EmitC_emitDec(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_6 = 1;
x_7 = l_Bool_DecidableEq(x_3, x_6);
x_8 = l_Nat_repr(x_1);
x_9 = l_Lean_IR_VarId_HasToString___closed__1;
x_10 = lean_string_append(x_9, x_8);
lean_dec(x_8);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_dec_eq(x_2, x_11);
if (x_7 == 0)
{
lean_object* x_53; 
x_53 = l_Lean_IR_EmitC_emitDec___closed__1;
x_13 = x_53;
goto block_52;
}
else
{
lean_object* x_54; 
x_54 = l_Lean_IR_EmitC_emitDec___closed__2;
x_13 = x_54;
goto block_52;
}
block_52:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_string_append(x_5, x_13);
lean_dec(x_13);
x_15 = l_Prod_HasRepr___rarg___closed__1;
x_16 = lean_string_append(x_14, x_15);
x_17 = lean_string_append(x_16, x_10);
lean_dec(x_10);
if (x_12 == 0)
{
uint8_t x_18; 
x_18 = l_String_Iterator_extract___closed__1;
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_2);
x_19 = l_Lean_IR_EmitC_emitInc___closed__1;
x_20 = lean_string_append(x_17, x_19);
x_21 = l_IO_println___rarg___closed__1;
x_22 = lean_string_append(x_20, x_21);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_25 = l_List_reprAux___main___rarg___closed__1;
x_26 = lean_string_append(x_17, x_25);
x_27 = l_Nat_repr(x_2);
x_28 = lean_string_append(x_26, x_27);
lean_dec(x_27);
x_29 = l_Lean_IR_EmitC_emitInc___closed__1;
x_30 = lean_string_append(x_28, x_29);
x_31 = l_IO_println___rarg___closed__1;
x_32 = lean_string_append(x_30, x_31);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
}
else
{
uint8_t x_35; 
x_35 = l_String_anyAux___main___at_String_all___spec__1___closed__1;
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_2);
x_36 = l_Lean_IR_EmitC_emitInc___closed__1;
x_37 = lean_string_append(x_17, x_36);
x_38 = l_IO_println___rarg___closed__1;
x_39 = lean_string_append(x_37, x_38);
x_40 = lean_box(0);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_42 = l_List_reprAux___main___rarg___closed__1;
x_43 = lean_string_append(x_17, x_42);
x_44 = l_Nat_repr(x_2);
x_45 = lean_string_append(x_43, x_44);
lean_dec(x_44);
x_46 = l_Lean_IR_EmitC_emitInc___closed__1;
x_47 = lean_string_append(x_45, x_46);
x_48 = l_IO_println___rarg___closed__1;
x_49 = lean_string_append(x_47, x_48);
x_50 = lean_box(0);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_49);
return x_51;
}
}
}
}
}
lean_object* l_Lean_IR_EmitC_emitDec___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_3);
lean_dec(x_3);
x_7 = l_Lean_IR_EmitC_emitDec(x_1, x_2, x_6, x_4, x_5);
lean_dec(x_4);
return x_7;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitDel___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("lean_free_object(");
return x_1;
}
}
lean_object* l_Lean_IR_EmitC_emitDel(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_4 = l_Lean_IR_EmitC_emitDel___closed__1;
x_5 = lean_string_append(x_3, x_4);
x_6 = l_Nat_repr(x_1);
x_7 = l_Lean_IR_VarId_HasToString___closed__1;
x_8 = lean_string_append(x_7, x_6);
lean_dec(x_6);
x_9 = lean_string_append(x_5, x_8);
lean_dec(x_8);
x_10 = l_Lean_IR_EmitC_emitInc___closed__1;
x_11 = lean_string_append(x_9, x_10);
x_12 = l_IO_println___rarg___closed__1;
x_13 = lean_string_append(x_11, x_12);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
lean_object* l_Lean_IR_EmitC_emitDel___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_EmitC_emitDel(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitSetTag___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("lean_ctor_set_tag(");
return x_1;
}
}
lean_object* l_Lean_IR_EmitC_emitSetTag(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_5 = l_Lean_IR_EmitC_emitSetTag___closed__1;
x_6 = lean_string_append(x_4, x_5);
x_7 = l_Nat_repr(x_1);
x_8 = l_Lean_IR_VarId_HasToString___closed__1;
x_9 = lean_string_append(x_8, x_7);
lean_dec(x_7);
x_10 = lean_string_append(x_6, x_9);
lean_dec(x_9);
x_11 = l_List_reprAux___main___rarg___closed__1;
x_12 = lean_string_append(x_10, x_11);
x_13 = l_Nat_repr(x_2);
x_14 = lean_string_append(x_12, x_13);
lean_dec(x_13);
x_15 = l_Lean_IR_EmitC_emitInc___closed__1;
x_16 = lean_string_append(x_14, x_15);
x_17 = l_IO_println___rarg___closed__1;
x_18 = lean_string_append(x_16, x_17);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
lean_object* l_Lean_IR_EmitC_emitSetTag___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_EmitC_emitSetTag(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitSet___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("lean_ctor_set(");
return x_1;
}
}
lean_object* l_Lean_IR_EmitC_emitSet(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_6 = l_Lean_IR_EmitC_emitSet___closed__1;
x_7 = lean_string_append(x_5, x_6);
x_8 = l_Nat_repr(x_1);
x_9 = l_Lean_IR_VarId_HasToString___closed__1;
x_10 = lean_string_append(x_9, x_8);
lean_dec(x_8);
x_11 = lean_string_append(x_7, x_10);
lean_dec(x_10);
x_12 = l_List_reprAux___main___rarg___closed__1;
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
x_21 = l_Lean_IR_EmitC_emitInc___closed__1;
x_22 = lean_string_append(x_19, x_21);
x_23 = l_IO_println___rarg___closed__1;
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
x_27 = l_Lean_IR_EmitC_emitInc___closed__1;
x_28 = lean_string_append(x_26, x_27);
x_29 = l_IO_println___rarg___closed__1;
x_30 = lean_string_append(x_28, x_29);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
}
lean_object* l_Lean_IR_EmitC_emitSet___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_EmitC_emitSet(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitOffset___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("sizeof(void*)*");
return x_1;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitOffset___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" + ");
return x_1;
}
}
lean_object* l_Lean_IR_EmitC_emitOffset(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* l_Lean_IR_EmitC_emitOffset___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_EmitC_emitOffset(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitUSet___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("lean_ctor_set_usize(");
return x_1;
}
}
lean_object* l_Lean_IR_EmitC_emitUSet(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_6 = l_Lean_IR_EmitC_emitUSet___closed__1;
x_7 = lean_string_append(x_5, x_6);
x_8 = l_Nat_repr(x_1);
x_9 = l_Lean_IR_VarId_HasToString___closed__1;
x_10 = lean_string_append(x_9, x_8);
lean_dec(x_8);
x_11 = lean_string_append(x_7, x_10);
lean_dec(x_10);
x_12 = l_List_reprAux___main___rarg___closed__1;
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
x_20 = l_Lean_IR_EmitC_emitInc___closed__1;
x_21 = lean_string_append(x_19, x_20);
x_22 = l_IO_println___rarg___closed__1;
x_23 = lean_string_append(x_21, x_22);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
lean_object* l_Lean_IR_EmitC_emitUSet___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_EmitC_emitUSet(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitSSet___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("floats are not supported yet");
return x_1;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitSSet___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("lean_ctor_set_uint8");
return x_1;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitSSet___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("lean_ctor_set_uint16");
return x_1;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitSSet___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("lean_ctor_set_uint32");
return x_1;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitSSet___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("lean_ctor_set_uint64");
return x_1;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitSSet___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid instruction");
return x_1;
}
}
lean_object* l_Lean_IR_EmitC_emitSSet(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
switch (lean_obj_tag(x_5)) {
case 0:
{
lean_object* x_42; lean_object* x_43; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_42 = l_Lean_IR_EmitC_emitSSet___closed__1;
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_7);
return x_43;
}
case 1:
{
lean_object* x_44; lean_object* x_45; 
x_44 = l_Lean_IR_EmitC_emitSSet___closed__2;
x_45 = lean_string_append(x_7, x_44);
x_8 = x_45;
goto block_41;
}
case 2:
{
lean_object* x_46; lean_object* x_47; 
x_46 = l_Lean_IR_EmitC_emitSSet___closed__3;
x_47 = lean_string_append(x_7, x_46);
x_8 = x_47;
goto block_41;
}
case 3:
{
lean_object* x_48; lean_object* x_49; 
x_48 = l_Lean_IR_EmitC_emitSSet___closed__4;
x_49 = lean_string_append(x_7, x_48);
x_8 = x_49;
goto block_41;
}
case 4:
{
lean_object* x_50; lean_object* x_51; 
x_50 = l_Lean_IR_EmitC_emitSSet___closed__5;
x_51 = lean_string_append(x_7, x_50);
x_8 = x_51;
goto block_41;
}
default: 
{
lean_object* x_52; lean_object* x_53; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_52 = l_Lean_IR_EmitC_emitSSet___closed__6;
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_7);
return x_53;
}
}
block_41:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_9 = l_Prod_HasRepr___rarg___closed__1;
x_10 = lean_string_append(x_8, x_9);
x_11 = l_Nat_repr(x_1);
x_12 = l_Lean_IR_VarId_HasToString___closed__1;
x_13 = lean_string_append(x_12, x_11);
lean_dec(x_11);
x_14 = lean_string_append(x_10, x_13);
lean_dec(x_13);
x_15 = l_List_reprAux___main___rarg___closed__1;
x_16 = lean_string_append(x_14, x_15);
x_17 = l_Lean_IR_EmitC_emitOffset(x_2, x_3, x_6, x_16);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_19 = lean_ctor_get(x_17, 1);
x_20 = lean_ctor_get(x_17, 0);
lean_dec(x_20);
x_21 = lean_string_append(x_19, x_15);
x_22 = l_Nat_repr(x_4);
x_23 = lean_string_append(x_12, x_22);
lean_dec(x_22);
x_24 = lean_string_append(x_21, x_23);
lean_dec(x_23);
x_25 = l_Lean_IR_EmitC_emitInc___closed__1;
x_26 = lean_string_append(x_24, x_25);
x_27 = l_IO_println___rarg___closed__1;
x_28 = lean_string_append(x_26, x_27);
x_29 = lean_box(0);
lean_ctor_set(x_17, 1, x_28);
lean_ctor_set(x_17, 0, x_29);
return x_17;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_30 = lean_ctor_get(x_17, 1);
lean_inc(x_30);
lean_dec(x_17);
x_31 = lean_string_append(x_30, x_15);
x_32 = l_Nat_repr(x_4);
x_33 = lean_string_append(x_12, x_32);
lean_dec(x_32);
x_34 = lean_string_append(x_31, x_33);
lean_dec(x_33);
x_35 = l_Lean_IR_EmitC_emitInc___closed__1;
x_36 = lean_string_append(x_34, x_35);
x_37 = l_IO_println___rarg___closed__1;
x_38 = lean_string_append(x_36, x_37);
x_39 = lean_box(0);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
return x_40;
}
}
}
}
lean_object* l_Lean_IR_EmitC_emitSSet___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_IR_EmitC_emitSSet(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_8;
}
}
lean_object* _init_l_Nat_forMAux___main___at_Lean_IR_EmitC_emitJmp___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" = ");
return x_1;
}
}
lean_object* l_Nat_forMAux___main___at_Lean_IR_EmitC_emitJmp___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_13 = l_Lean_IR_paramInh;
x_14 = lean_array_get(x_13, x_2, x_12);
x_15 = l_Lean_IR_Arg_Inhabited;
x_16 = lean_array_get(x_15, x_1, x_12);
lean_dec(x_12);
x_17 = lean_ctor_get(x_14, 0);
lean_inc(x_17);
lean_dec(x_14);
x_18 = l_Nat_repr(x_17);
x_19 = l_Lean_IR_VarId_HasToString___closed__1;
x_20 = lean_string_append(x_19, x_18);
lean_dec(x_18);
x_21 = lean_string_append(x_6, x_20);
lean_dec(x_20);
x_22 = l_Nat_forMAux___main___at_Lean_IR_EmitC_emitJmp___spec__1___closed__1;
x_23 = lean_string_append(x_21, x_22);
x_24 = l_Lean_IR_EmitC_emitArg(x_16, x_5, x_23);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_26 = l_Lean_IR_formatFnBody___main___closed__1;
x_27 = lean_string_append(x_25, x_26);
x_28 = l_IO_println___rarg___closed__1;
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
lean_object* _init_l_Lean_IR_EmitC_emitJmp___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid goto");
return x_1;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitJmp___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("goto ");
return x_1;
}
}
lean_object* l_Lean_IR_EmitC_emitJmp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_EmitC_getJPParams(x_1, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_12; uint8_t x_13; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
x_9 = lean_array_get_size(x_2);
x_10 = lean_array_get_size(x_7);
x_11 = lean_nat_dec_eq(x_9, x_10);
lean_dec(x_10);
x_12 = 1;
x_13 = l_Bool_DecidableEq(x_11, x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_1);
x_14 = l_Lean_IR_EmitC_emitJmp___closed__1;
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 0, x_14);
return x_5;
}
else
{
lean_object* x_15; uint8_t x_16; 
lean_free_object(x_5);
lean_inc(x_9);
x_15 = l_Nat_forMAux___main___at_Lean_IR_EmitC_emitJmp___spec__1(x_2, x_7, x_9, x_9, x_3, x_8);
lean_dec(x_9);
lean_dec(x_7);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_17 = lean_ctor_get(x_15, 1);
x_18 = lean_ctor_get(x_15, 0);
lean_dec(x_18);
x_19 = l_Lean_IR_EmitC_emitJmp___closed__2;
x_20 = lean_string_append(x_17, x_19);
x_21 = l_Nat_repr(x_1);
x_22 = l_Lean_IR_JoinPointId_HasToString___closed__1;
x_23 = lean_string_append(x_22, x_21);
lean_dec(x_21);
x_24 = lean_string_append(x_20, x_23);
lean_dec(x_23);
x_25 = l_Lean_IR_formatFnBody___main___closed__1;
x_26 = lean_string_append(x_24, x_25);
x_27 = l_IO_println___rarg___closed__1;
x_28 = lean_string_append(x_26, x_27);
x_29 = lean_box(0);
lean_ctor_set(x_15, 1, x_28);
lean_ctor_set(x_15, 0, x_29);
return x_15;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_30 = lean_ctor_get(x_15, 1);
lean_inc(x_30);
lean_dec(x_15);
x_31 = l_Lean_IR_EmitC_emitJmp___closed__2;
x_32 = lean_string_append(x_30, x_31);
x_33 = l_Nat_repr(x_1);
x_34 = l_Lean_IR_JoinPointId_HasToString___closed__1;
x_35 = lean_string_append(x_34, x_33);
lean_dec(x_33);
x_36 = lean_string_append(x_32, x_35);
lean_dec(x_35);
x_37 = l_Lean_IR_formatFnBody___main___closed__1;
x_38 = lean_string_append(x_36, x_37);
x_39 = l_IO_println___rarg___closed__1;
x_40 = lean_string_append(x_38, x_39);
x_41 = lean_box(0);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
return x_42;
}
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; uint8_t x_48; uint8_t x_49; 
x_43 = lean_ctor_get(x_5, 0);
x_44 = lean_ctor_get(x_5, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_5);
x_45 = lean_array_get_size(x_2);
x_46 = lean_array_get_size(x_43);
x_47 = lean_nat_dec_eq(x_45, x_46);
lean_dec(x_46);
x_48 = 1;
x_49 = l_Bool_DecidableEq(x_47, x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
lean_dec(x_45);
lean_dec(x_43);
lean_dec(x_1);
x_50 = l_Lean_IR_EmitC_emitJmp___closed__1;
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_44);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_inc(x_45);
x_52 = l_Nat_forMAux___main___at_Lean_IR_EmitC_emitJmp___spec__1(x_2, x_43, x_45, x_45, x_3, x_44);
lean_dec(x_45);
lean_dec(x_43);
x_53 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_54 = x_52;
} else {
 lean_dec_ref(x_52);
 x_54 = lean_box(0);
}
x_55 = l_Lean_IR_EmitC_emitJmp___closed__2;
x_56 = lean_string_append(x_53, x_55);
x_57 = l_Nat_repr(x_1);
x_58 = l_Lean_IR_JoinPointId_HasToString___closed__1;
x_59 = lean_string_append(x_58, x_57);
lean_dec(x_57);
x_60 = lean_string_append(x_56, x_59);
lean_dec(x_59);
x_61 = l_Lean_IR_formatFnBody___main___closed__1;
x_62 = lean_string_append(x_60, x_61);
x_63 = l_IO_println___rarg___closed__1;
x_64 = lean_string_append(x_62, x_63);
x_65 = lean_box(0);
if (lean_is_scalar(x_54)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_54;
}
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_64);
return x_66;
}
}
}
else
{
uint8_t x_67; 
lean_dec(x_1);
x_67 = !lean_is_exclusive(x_5);
if (x_67 == 0)
{
return x_5;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_5, 0);
x_69 = lean_ctor_get(x_5, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_5);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
}
lean_object* l_Nat_forMAux___main___at_Lean_IR_EmitC_emitJmp___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Nat_forMAux___main___at_Lean_IR_EmitC_emitJmp___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_IR_EmitC_emitJmp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_EmitC_emitJmp(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_IR_EmitC_emitLhs(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = l_Nat_repr(x_1);
x_5 = l_Lean_IR_VarId_HasToString___closed__1;
x_6 = lean_string_append(x_5, x_4);
lean_dec(x_4);
x_7 = lean_string_append(x_3, x_6);
lean_dec(x_6);
x_8 = l_Nat_forMAux___main___at_Lean_IR_EmitC_emitJmp___spec__1___closed__1;
x_9 = lean_string_append(x_7, x_8);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
lean_object* l_Lean_IR_EmitC_emitLhs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_EmitC_emitLhs(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Nat_forMAux___main___at_Lean_IR_EmitC_emitArgs___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = l_Lean_IR_Arg_Inhabited;
x_14 = lean_array_get(x_13, x_1, x_11);
lean_dec(x_11);
x_15 = l_Lean_IR_EmitC_emitArg(x_14, x_4, x_5);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_3 = x_9;
x_5 = x_16;
goto _start;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_18 = l_List_reprAux___main___rarg___closed__1;
x_19 = lean_string_append(x_5, x_18);
x_20 = l_Lean_IR_Arg_Inhabited;
x_21 = lean_array_get(x_20, x_1, x_11);
lean_dec(x_11);
x_22 = l_Lean_IR_EmitC_emitArg(x_21, x_4, x_19);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_3 = x_9;
x_5 = x_23;
goto _start;
}
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_3);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_5);
return x_26;
}
}
}
lean_object* l_Lean_IR_EmitC_emitArgs(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_array_get_size(x_1);
lean_inc(x_4);
x_5 = l_Nat_forMAux___main___at_Lean_IR_EmitC_emitArgs___spec__1(x_1, x_4, x_4, x_2, x_3);
lean_dec(x_4);
return x_5;
}
}
lean_object* l_Nat_forMAux___main___at_Lean_IR_EmitC_emitArgs___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Nat_forMAux___main___at_Lean_IR_EmitC_emitArgs___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_IR_EmitC_emitArgs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_EmitC_emitArgs(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitCtorScalarSize___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("sizeof(size_t)*");
return x_1;
}
}
lean_object* l_Lean_IR_EmitC_emitCtorScalarSize(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; uint8_t x_7; uint8_t x_8; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_1, x_5);
x_7 = 1;
x_8 = l_Bool_DecidableEq(x_6, x_7);
if (x_8 == 0)
{
uint8_t x_9; uint8_t x_10; 
x_9 = lean_nat_dec_eq(x_2, x_5);
x_10 = l_Bool_DecidableEq(x_9, x_7);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_11 = l_Lean_IR_EmitC_emitCtorScalarSize___closed__1;
x_12 = lean_string_append(x_4, x_11);
x_13 = l_Nat_repr(x_1);
x_14 = lean_string_append(x_12, x_13);
lean_dec(x_13);
x_15 = l_Lean_IR_EmitC_emitOffset___closed__2;
x_16 = lean_string_append(x_14, x_15);
x_17 = l_Nat_repr(x_2);
x_18 = lean_string_append(x_16, x_17);
lean_dec(x_17);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_2);
x_21 = l_Lean_IR_EmitC_emitCtorScalarSize___closed__1;
x_22 = lean_string_append(x_4, x_21);
x_23 = l_Nat_repr(x_1);
x_24 = lean_string_append(x_22, x_23);
lean_dec(x_23);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_1);
x_27 = l_Nat_repr(x_2);
x_28 = lean_string_append(x_4, x_27);
lean_dec(x_27);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
}
lean_object* l_Lean_IR_EmitC_emitCtorScalarSize___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_EmitC_emitCtorScalarSize(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitAllocCtor___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("lean_alloc_ctor(");
return x_1;
}
}
lean_object* l_Lean_IR_EmitC_emitAllocCtor(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_List_reprAux___main___rarg___closed__1;
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
x_21 = l_Lean_IR_EmitC_emitInc___closed__1;
x_22 = lean_string_append(x_19, x_21);
x_23 = l_IO_println___rarg___closed__1;
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
x_27 = l_Lean_IR_EmitC_emitInc___closed__1;
x_28 = lean_string_append(x_26, x_27);
x_29 = l_IO_println___rarg___closed__1;
x_30 = lean_string_append(x_28, x_29);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
}
lean_object* l_Lean_IR_EmitC_emitAllocCtor___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_EmitC_emitAllocCtor(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Nat_forMAux___main___at_Lean_IR_EmitC_emitCtorSetArgs___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_16 = l_Lean_IR_VarId_HasToString___closed__1;
x_17 = lean_string_append(x_16, x_15);
lean_dec(x_15);
x_18 = lean_string_append(x_14, x_17);
lean_dec(x_17);
x_19 = l_List_reprAux___main___rarg___closed__1;
x_20 = lean_string_append(x_18, x_19);
lean_inc(x_12);
x_21 = l_Nat_repr(x_12);
x_22 = lean_string_append(x_20, x_21);
lean_dec(x_21);
x_23 = lean_string_append(x_22, x_19);
x_24 = l_Lean_IR_Arg_Inhabited;
x_25 = lean_array_get(x_24, x_2, x_12);
lean_dec(x_12);
x_26 = l_Lean_IR_EmitC_emitArg(x_25, x_5, x_23);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = l_Lean_IR_EmitC_emitInc___closed__1;
x_29 = lean_string_append(x_27, x_28);
x_30 = l_IO_println___rarg___closed__1;
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
lean_object* l_Lean_IR_EmitC_emitCtorSetArgs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_array_get_size(x_2);
lean_inc(x_5);
x_6 = l_Nat_forMAux___main___at_Lean_IR_EmitC_emitCtorSetArgs___spec__1(x_1, x_2, x_5, x_5, x_3, x_4);
lean_dec(x_5);
return x_6;
}
}
lean_object* l_Nat_forMAux___main___at_Lean_IR_EmitC_emitCtorSetArgs___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Nat_forMAux___main___at_Lean_IR_EmitC_emitCtorSetArgs___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_IR_EmitC_emitCtorSetArgs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_EmitC_emitCtorSetArgs(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitCtor___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("lean_box(");
return x_1;
}
}
lean_object* l_Lean_IR_EmitC_emitCtor(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
uint8_t x_13; 
x_13 = l_String_anyAux___main___at_String_all___spec__1___closed__1;
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_free_object(x_6);
x_14 = l_Lean_IR_EmitC_emitAllocCtor(x_2, x_4, x_8);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = l_Lean_IR_EmitC_emitCtorSetArgs(x_1, x_3, x_4, x_15);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_1);
x_17 = l_Lean_IR_EmitC_emitCtor___closed__1;
x_18 = lean_string_append(x_8, x_17);
x_19 = lean_ctor_get(x_2, 1);
lean_inc(x_19);
lean_dec(x_2);
x_20 = l_Nat_repr(x_19);
x_21 = lean_string_append(x_18, x_20);
lean_dec(x_20);
x_22 = l_Lean_IR_EmitC_emitInc___closed__1;
x_23 = lean_string_append(x_21, x_22);
x_24 = l_IO_println___rarg___closed__1;
x_25 = lean_string_append(x_23, x_24);
x_26 = lean_box(0);
lean_ctor_set(x_6, 1, x_25);
lean_ctor_set(x_6, 0, x_26);
return x_6;
}
}
else
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_2, 3);
lean_inc(x_27);
x_28 = lean_nat_dec_eq(x_27, x_11);
lean_dec(x_27);
if (x_28 == 0)
{
uint8_t x_29; 
x_29 = l_String_anyAux___main___at_String_all___spec__1___closed__1;
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_free_object(x_6);
x_30 = l_Lean_IR_EmitC_emitAllocCtor(x_2, x_4, x_8);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec(x_30);
x_32 = l_Lean_IR_EmitC_emitCtorSetArgs(x_1, x_3, x_4, x_31);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_1);
x_33 = l_Lean_IR_EmitC_emitCtor___closed__1;
x_34 = lean_string_append(x_8, x_33);
x_35 = lean_ctor_get(x_2, 1);
lean_inc(x_35);
lean_dec(x_2);
x_36 = l_Nat_repr(x_35);
x_37 = lean_string_append(x_34, x_36);
lean_dec(x_36);
x_38 = l_Lean_IR_EmitC_emitInc___closed__1;
x_39 = lean_string_append(x_37, x_38);
x_40 = l_IO_println___rarg___closed__1;
x_41 = lean_string_append(x_39, x_40);
x_42 = lean_box(0);
lean_ctor_set(x_6, 1, x_41);
lean_ctor_set(x_6, 0, x_42);
return x_6;
}
}
else
{
lean_object* x_43; uint8_t x_44; uint8_t x_45; uint8_t x_46; 
x_43 = lean_ctor_get(x_2, 4);
lean_inc(x_43);
x_44 = lean_nat_dec_eq(x_43, x_11);
lean_dec(x_43);
x_45 = 1;
x_46 = l_Bool_DecidableEq(x_44, x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_free_object(x_6);
x_47 = l_Lean_IR_EmitC_emitAllocCtor(x_2, x_4, x_8);
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
lean_dec(x_47);
x_49 = l_Lean_IR_EmitC_emitCtorSetArgs(x_1, x_3, x_4, x_48);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_1);
x_50 = l_Lean_IR_EmitC_emitCtor___closed__1;
x_51 = lean_string_append(x_8, x_50);
x_52 = lean_ctor_get(x_2, 1);
lean_inc(x_52);
lean_dec(x_2);
x_53 = l_Nat_repr(x_52);
x_54 = lean_string_append(x_51, x_53);
lean_dec(x_53);
x_55 = l_Lean_IR_EmitC_emitInc___closed__1;
x_56 = lean_string_append(x_54, x_55);
x_57 = l_IO_println___rarg___closed__1;
x_58 = lean_string_append(x_56, x_57);
x_59 = lean_box(0);
lean_ctor_set(x_6, 1, x_58);
lean_ctor_set(x_6, 0, x_59);
return x_6;
}
}
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_60 = lean_ctor_get(x_6, 1);
lean_inc(x_60);
lean_dec(x_6);
x_61 = lean_ctor_get(x_2, 2);
lean_inc(x_61);
x_62 = lean_unsigned_to_nat(0u);
x_63 = lean_nat_dec_eq(x_61, x_62);
lean_dec(x_61);
if (x_63 == 0)
{
uint8_t x_64; 
x_64 = l_String_anyAux___main___at_String_all___spec__1___closed__1;
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = l_Lean_IR_EmitC_emitAllocCtor(x_2, x_4, x_60);
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
lean_dec(x_65);
x_67 = l_Lean_IR_EmitC_emitCtorSetArgs(x_1, x_3, x_4, x_66);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_1);
x_68 = l_Lean_IR_EmitC_emitCtor___closed__1;
x_69 = lean_string_append(x_60, x_68);
x_70 = lean_ctor_get(x_2, 1);
lean_inc(x_70);
lean_dec(x_2);
x_71 = l_Nat_repr(x_70);
x_72 = lean_string_append(x_69, x_71);
lean_dec(x_71);
x_73 = l_Lean_IR_EmitC_emitInc___closed__1;
x_74 = lean_string_append(x_72, x_73);
x_75 = l_IO_println___rarg___closed__1;
x_76 = lean_string_append(x_74, x_75);
x_77 = lean_box(0);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_76);
return x_78;
}
}
else
{
lean_object* x_79; uint8_t x_80; 
x_79 = lean_ctor_get(x_2, 3);
lean_inc(x_79);
x_80 = lean_nat_dec_eq(x_79, x_62);
lean_dec(x_79);
if (x_80 == 0)
{
uint8_t x_81; 
x_81 = l_String_anyAux___main___at_String_all___spec__1___closed__1;
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = l_Lean_IR_EmitC_emitAllocCtor(x_2, x_4, x_60);
x_83 = lean_ctor_get(x_82, 1);
lean_inc(x_83);
lean_dec(x_82);
x_84 = l_Lean_IR_EmitC_emitCtorSetArgs(x_1, x_3, x_4, x_83);
return x_84;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_1);
x_85 = l_Lean_IR_EmitC_emitCtor___closed__1;
x_86 = lean_string_append(x_60, x_85);
x_87 = lean_ctor_get(x_2, 1);
lean_inc(x_87);
lean_dec(x_2);
x_88 = l_Nat_repr(x_87);
x_89 = lean_string_append(x_86, x_88);
lean_dec(x_88);
x_90 = l_Lean_IR_EmitC_emitInc___closed__1;
x_91 = lean_string_append(x_89, x_90);
x_92 = l_IO_println___rarg___closed__1;
x_93 = lean_string_append(x_91, x_92);
x_94 = lean_box(0);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_93);
return x_95;
}
}
else
{
lean_object* x_96; uint8_t x_97; uint8_t x_98; uint8_t x_99; 
x_96 = lean_ctor_get(x_2, 4);
lean_inc(x_96);
x_97 = lean_nat_dec_eq(x_96, x_62);
lean_dec(x_96);
x_98 = 1;
x_99 = l_Bool_DecidableEq(x_97, x_98);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = l_Lean_IR_EmitC_emitAllocCtor(x_2, x_4, x_60);
x_101 = lean_ctor_get(x_100, 1);
lean_inc(x_101);
lean_dec(x_100);
x_102 = l_Lean_IR_EmitC_emitCtorSetArgs(x_1, x_3, x_4, x_101);
return x_102;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
lean_dec(x_1);
x_103 = l_Lean_IR_EmitC_emitCtor___closed__1;
x_104 = lean_string_append(x_60, x_103);
x_105 = lean_ctor_get(x_2, 1);
lean_inc(x_105);
lean_dec(x_2);
x_106 = l_Nat_repr(x_105);
x_107 = lean_string_append(x_104, x_106);
lean_dec(x_106);
x_108 = l_Lean_IR_EmitC_emitInc___closed__1;
x_109 = lean_string_append(x_107, x_108);
x_110 = l_IO_println___rarg___closed__1;
x_111 = lean_string_append(x_109, x_110);
x_112 = lean_box(0);
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_111);
return x_113;
}
}
}
}
}
}
lean_object* l_Lean_IR_EmitC_emitCtor___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_EmitC_emitCtor(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
lean_object* _init_l_Nat_forMAux___main___at_Lean_IR_EmitC_emitReset___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" lean_ctor_release(");
return x_1;
}
}
lean_object* l_Nat_forMAux___main___at_Lean_IR_EmitC_emitReset___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
x_12 = l_Nat_forMAux___main___at_Lean_IR_EmitC_emitReset___spec__1___closed__1;
x_13 = lean_string_append(x_5, x_12);
x_14 = lean_string_append(x_13, x_1);
x_15 = l_List_reprAux___main___rarg___closed__1;
x_16 = lean_string_append(x_14, x_15);
x_17 = l_Nat_repr(x_11);
x_18 = lean_string_append(x_16, x_17);
lean_dec(x_17);
x_19 = l_Lean_IR_EmitC_emitInc___closed__1;
x_20 = lean_string_append(x_18, x_19);
x_21 = l_IO_println___rarg___closed__1;
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
lean_object* _init_l_Lean_IR_EmitC_emitReset___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("if (lean_is_exclusive(");
return x_1;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitReset___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(")) {");
return x_1;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitReset___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" lean_dec_ref(");
return x_1;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitReset___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("lean_box(0);");
return x_1;
}
}
lean_object* l_Lean_IR_EmitC_emitReset(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_6 = l_Lean_IR_EmitC_emitReset___closed__1;
x_7 = lean_string_append(x_5, x_6);
x_8 = l_Nat_repr(x_3);
x_9 = l_Lean_IR_VarId_HasToString___closed__1;
x_10 = lean_string_append(x_9, x_8);
lean_dec(x_8);
x_11 = lean_string_append(x_7, x_10);
x_12 = l_Lean_IR_EmitC_emitReset___closed__2;
x_13 = lean_string_append(x_11, x_12);
x_14 = l_IO_println___rarg___closed__1;
x_15 = lean_string_append(x_13, x_14);
lean_inc(x_2);
x_16 = l_Nat_forMAux___main___at_Lean_IR_EmitC_emitReset___spec__1(x_10, x_2, x_2, x_4, x_15);
lean_dec(x_2);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = l_String_Iterator_HasRepr___closed__2;
x_19 = lean_string_append(x_17, x_18);
lean_inc(x_1);
x_20 = l_Lean_IR_EmitC_emitLhs(x_1, x_4, x_19);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_string_append(x_21, x_10);
x_23 = l_Lean_IR_formatFnBody___main___closed__1;
x_24 = lean_string_append(x_22, x_23);
x_25 = lean_string_append(x_24, x_14);
x_26 = l_Lean_IR_EmitC_emitMainFn___closed__11;
x_27 = lean_string_append(x_25, x_26);
x_28 = lean_string_append(x_27, x_14);
x_29 = l_Lean_IR_EmitC_emitReset___closed__3;
x_30 = lean_string_append(x_28, x_29);
x_31 = lean_string_append(x_30, x_10);
lean_dec(x_10);
x_32 = l_Lean_IR_EmitC_emitInc___closed__1;
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
x_43 = l_PersistentArray_Stats_toString___closed__4;
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
x_51 = l_PersistentArray_Stats_toString___closed__4;
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
lean_object* l_Nat_forMAux___main___at_Lean_IR_EmitC_emitReset___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Nat_forMAux___main___at_Lean_IR_EmitC_emitReset___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_IR_EmitC_emitReset___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_EmitC_emitReset(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitReuse___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("if (lean_is_scalar(");
return x_1;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitReuse___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" lean_ctor_set_tag(");
return x_1;
}
}
lean_object* l_Lean_IR_EmitC_emitReuse(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; uint8_t x_35; 
x_8 = l_Lean_IR_EmitC_emitReuse___closed__1;
x_9 = lean_string_append(x_7, x_8);
x_10 = l_Nat_repr(x_2);
x_11 = l_Lean_IR_VarId_HasToString___closed__1;
x_12 = lean_string_append(x_11, x_10);
lean_dec(x_10);
x_13 = lean_string_append(x_9, x_12);
x_14 = l_Lean_IR_EmitC_emitReset___closed__2;
x_15 = lean_string_append(x_13, x_14);
x_16 = l_IO_println___rarg___closed__1;
x_17 = lean_string_append(x_15, x_16);
x_18 = l_String_Iterator_HasRepr___closed__2;
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
x_24 = l_Lean_IR_EmitC_emitMainFn___closed__11;
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
x_31 = l_Lean_IR_formatFnBody___main___closed__1;
x_32 = lean_string_append(x_30, x_31);
x_33 = lean_string_append(x_32, x_16);
x_34 = 1;
x_35 = l_Bool_DecidableEq(x_4, x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_3);
x_36 = l_PersistentArray_Stats_toString___closed__4;
x_37 = lean_string_append(x_33, x_36);
x_38 = lean_string_append(x_37, x_16);
x_39 = l_Lean_IR_EmitC_emitCtorSetArgs(x_1, x_5, x_6, x_38);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_40 = l_Lean_IR_EmitC_emitReuse___closed__2;
x_41 = lean_string_append(x_33, x_40);
lean_inc(x_1);
x_42 = l_Nat_repr(x_1);
x_43 = lean_string_append(x_11, x_42);
lean_dec(x_42);
x_44 = lean_string_append(x_41, x_43);
lean_dec(x_43);
x_45 = l_List_reprAux___main___rarg___closed__1;
x_46 = lean_string_append(x_44, x_45);
x_47 = lean_ctor_get(x_3, 1);
lean_inc(x_47);
lean_dec(x_3);
x_48 = l_Nat_repr(x_47);
x_49 = lean_string_append(x_46, x_48);
lean_dec(x_48);
x_50 = l_Lean_IR_EmitC_emitInc___closed__1;
x_51 = lean_string_append(x_49, x_50);
x_52 = lean_string_append(x_51, x_16);
x_53 = l_PersistentArray_Stats_toString___closed__4;
x_54 = lean_string_append(x_52, x_53);
x_55 = lean_string_append(x_54, x_16);
x_56 = l_Lean_IR_EmitC_emitCtorSetArgs(x_1, x_5, x_6, x_55);
return x_56;
}
}
}
lean_object* l_Lean_IR_EmitC_emitReuse___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_4);
lean_dec(x_4);
x_9 = l_Lean_IR_EmitC_emitReuse(x_1, x_2, x_3, x_8, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_9;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitProj___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("lean_ctor_get(");
return x_1;
}
}
lean_object* l_Lean_IR_EmitC_emitProj(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
x_13 = l_Lean_IR_VarId_HasToString___closed__1;
x_14 = lean_string_append(x_13, x_12);
lean_dec(x_12);
x_15 = lean_string_append(x_11, x_14);
lean_dec(x_14);
x_16 = l_List_reprAux___main___rarg___closed__1;
x_17 = lean_string_append(x_15, x_16);
x_18 = l_Nat_repr(x_2);
x_19 = lean_string_append(x_17, x_18);
lean_dec(x_18);
x_20 = l_Lean_IR_EmitC_emitInc___closed__1;
x_21 = lean_string_append(x_19, x_20);
x_22 = l_IO_println___rarg___closed__1;
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
x_29 = l_Lean_IR_VarId_HasToString___closed__1;
x_30 = lean_string_append(x_29, x_28);
lean_dec(x_28);
x_31 = lean_string_append(x_27, x_30);
lean_dec(x_30);
x_32 = l_List_reprAux___main___rarg___closed__1;
x_33 = lean_string_append(x_31, x_32);
x_34 = l_Nat_repr(x_2);
x_35 = lean_string_append(x_33, x_34);
lean_dec(x_34);
x_36 = l_Lean_IR_EmitC_emitInc___closed__1;
x_37 = lean_string_append(x_35, x_36);
x_38 = l_IO_println___rarg___closed__1;
x_39 = lean_string_append(x_37, x_38);
x_40 = lean_box(0);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
return x_41;
}
}
}
lean_object* l_Lean_IR_EmitC_emitProj___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_EmitC_emitProj(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitUProj___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("lean_ctor_get_usize(");
return x_1;
}
}
lean_object* l_Lean_IR_EmitC_emitUProj(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
x_13 = l_Lean_IR_VarId_HasToString___closed__1;
x_14 = lean_string_append(x_13, x_12);
lean_dec(x_12);
x_15 = lean_string_append(x_11, x_14);
lean_dec(x_14);
x_16 = l_List_reprAux___main___rarg___closed__1;
x_17 = lean_string_append(x_15, x_16);
x_18 = l_Nat_repr(x_2);
x_19 = lean_string_append(x_17, x_18);
lean_dec(x_18);
x_20 = l_Lean_IR_EmitC_emitInc___closed__1;
x_21 = lean_string_append(x_19, x_20);
x_22 = l_IO_println___rarg___closed__1;
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
x_29 = l_Lean_IR_VarId_HasToString___closed__1;
x_30 = lean_string_append(x_29, x_28);
lean_dec(x_28);
x_31 = lean_string_append(x_27, x_30);
lean_dec(x_30);
x_32 = l_List_reprAux___main___rarg___closed__1;
x_33 = lean_string_append(x_31, x_32);
x_34 = l_Nat_repr(x_2);
x_35 = lean_string_append(x_33, x_34);
lean_dec(x_34);
x_36 = l_Lean_IR_EmitC_emitInc___closed__1;
x_37 = lean_string_append(x_35, x_36);
x_38 = l_IO_println___rarg___closed__1;
x_39 = lean_string_append(x_37, x_38);
x_40 = lean_box(0);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
return x_41;
}
}
}
lean_object* l_Lean_IR_EmitC_emitUProj___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_EmitC_emitUProj(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitSProj___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("lean_ctor_get_uint8");
return x_1;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitSProj___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("lean_ctor_get_uint16");
return x_1;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitSProj___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("lean_ctor_get_uint32");
return x_1;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitSProj___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("lean_ctor_get_uint64");
return x_1;
}
}
lean_object* l_Lean_IR_EmitC_emitSProj(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_34; 
x_34 = l_Lean_IR_EmitC_emitLhs(x_1, x_6, x_7);
switch (lean_obj_tag(x_2)) {
case 0:
{
uint8_t x_35; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_34, 0);
lean_dec(x_36);
x_37 = l_Lean_IR_EmitC_emitSSet___closed__1;
lean_ctor_set_tag(x_34, 1);
lean_ctor_set(x_34, 0, x_37);
return x_34;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_34, 1);
lean_inc(x_38);
lean_dec(x_34);
x_39 = l_Lean_IR_EmitC_emitSSet___closed__1;
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
return x_40;
}
}
case 1:
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_34, 1);
lean_inc(x_41);
lean_dec(x_34);
x_42 = l_Lean_IR_EmitC_emitSProj___closed__1;
x_43 = lean_string_append(x_41, x_42);
x_8 = x_43;
goto block_33;
}
case 2:
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_34, 1);
lean_inc(x_44);
lean_dec(x_34);
x_45 = l_Lean_IR_EmitC_emitSProj___closed__2;
x_46 = lean_string_append(x_44, x_45);
x_8 = x_46;
goto block_33;
}
case 3:
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_34, 1);
lean_inc(x_47);
lean_dec(x_34);
x_48 = l_Lean_IR_EmitC_emitSProj___closed__3;
x_49 = lean_string_append(x_47, x_48);
x_8 = x_49;
goto block_33;
}
case 4:
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_34, 1);
lean_inc(x_50);
lean_dec(x_34);
x_51 = l_Lean_IR_EmitC_emitSProj___closed__4;
x_52 = lean_string_append(x_50, x_51);
x_8 = x_52;
goto block_33;
}
default: 
{
uint8_t x_53; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_53 = !lean_is_exclusive(x_34);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_34, 0);
lean_dec(x_54);
x_55 = l_Lean_IR_EmitC_emitSSet___closed__6;
lean_ctor_set_tag(x_34, 1);
lean_ctor_set(x_34, 0, x_55);
return x_34;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_34, 1);
lean_inc(x_56);
lean_dec(x_34);
x_57 = l_Lean_IR_EmitC_emitSSet___closed__6;
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_56);
return x_58;
}
}
}
block_33:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_9 = l_Prod_HasRepr___rarg___closed__1;
x_10 = lean_string_append(x_8, x_9);
x_11 = l_Nat_repr(x_5);
x_12 = l_Lean_IR_VarId_HasToString___closed__1;
x_13 = lean_string_append(x_12, x_11);
lean_dec(x_11);
x_14 = lean_string_append(x_10, x_13);
lean_dec(x_13);
x_15 = l_List_reprAux___main___rarg___closed__1;
x_16 = lean_string_append(x_14, x_15);
x_17 = l_Lean_IR_EmitC_emitOffset(x_3, x_4, x_6, x_16);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_19 = lean_ctor_get(x_17, 1);
x_20 = lean_ctor_get(x_17, 0);
lean_dec(x_20);
x_21 = l_Lean_IR_EmitC_emitInc___closed__1;
x_22 = lean_string_append(x_19, x_21);
x_23 = l_IO_println___rarg___closed__1;
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
x_27 = l_Lean_IR_EmitC_emitInc___closed__1;
x_28 = lean_string_append(x_26, x_27);
x_29 = l_IO_println___rarg___closed__1;
x_30 = lean_string_append(x_28, x_29);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
}
}
lean_object* l_Lean_IR_EmitC_emitSProj___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_IR_EmitC_emitSProj(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_List_map___main___at_Lean_IR_EmitC_toStringArgs___spec__1(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = l_Lean_IR_EmitC_argToCString(x_4);
x_7 = l_List_map___main___at_Lean_IR_EmitC_toStringArgs___spec__1(x_5);
lean_ctor_set(x_1, 1, x_7);
lean_ctor_set(x_1, 0, x_6);
return x_1;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_1);
x_10 = l_Lean_IR_EmitC_argToCString(x_8);
x_11 = l_List_map___main___at_Lean_IR_EmitC_toStringArgs___spec__1(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
}
lean_object* l_Lean_IR_EmitC_toStringArgs(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Array_toList___rarg(x_1);
x_3 = l_List_map___main___at_Lean_IR_EmitC_toStringArgs___spec__1(x_2);
return x_3;
}
}
lean_object* l_Lean_IR_EmitC_toStringArgs___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_IR_EmitC_toStringArgs(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Nat_foldMAux___main___at_Lean_IR_EmitC_emitSimpleExternalCall___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_4, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_sub(x_4, x_10);
lean_dec(x_4);
x_12 = lean_nat_sub(x_3, x_11);
x_13 = lean_nat_sub(x_12, x_10);
lean_dec(x_12);
x_14 = l_Lean_IR_paramInh;
x_15 = lean_array_get(x_14, x_1, x_13);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = l_Lean_IR_IRType_isIrrelevant(x_16);
lean_dec(x_16);
x_18 = 1;
x_19 = l_Bool_DecidableEq(x_17, x_18);
if (x_19 == 0)
{
uint8_t x_20; 
x_20 = l_Bool_DecidableEq(x_5, x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_21 = l_List_reprAux___main___rarg___closed__1;
x_22 = lean_string_append(x_7, x_21);
x_23 = l_Lean_IR_Arg_Inhabited;
x_24 = lean_array_get(x_23, x_2, x_13);
lean_dec(x_13);
x_25 = l_Lean_IR_EmitC_emitArg(x_24, x_6, x_22);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = 0;
x_4 = x_11;
x_5 = x_27;
x_7 = x_26;
goto _start;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_29 = l_Lean_IR_Arg_Inhabited;
x_30 = lean_array_get(x_29, x_2, x_13);
lean_dec(x_13);
x_31 = l_Lean_IR_EmitC_emitArg(x_30, x_6, x_7);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_33 = 0;
x_4 = x_11;
x_5 = x_33;
x_7 = x_32;
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
lean_object* x_36; lean_object* x_37; 
lean_dec(x_4);
x_36 = lean_box(x_5);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_7);
return x_37;
}
}
}
lean_object* l_Lean_IR_EmitC_emitSimpleExternalCall(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; uint8_t x_12; 
x_6 = lean_string_append(x_5, x_1);
x_7 = l_Prod_HasRepr___rarg___closed__1;
x_8 = lean_string_append(x_6, x_7);
x_9 = lean_array_get_size(x_3);
x_10 = 1;
lean_inc(x_9);
x_11 = l_Nat_foldMAux___main___at_Lean_IR_EmitC_emitSimpleExternalCall___spec__1(x_2, x_3, x_9, x_9, x_10, x_4, x_8);
lean_dec(x_9);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_ctor_get(x_11, 1);
x_14 = lean_ctor_get(x_11, 0);
lean_dec(x_14);
x_15 = l_Lean_IR_EmitC_emitInc___closed__1;
x_16 = lean_string_append(x_13, x_15);
x_17 = l_IO_println___rarg___closed__1;
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
x_21 = l_Lean_IR_EmitC_emitInc___closed__1;
x_22 = lean_string_append(x_20, x_21);
x_23 = l_IO_println___rarg___closed__1;
x_24 = lean_string_append(x_22, x_23);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
}
lean_object* l_Nat_foldMAux___main___at_Lean_IR_EmitC_emitSimpleExternalCall___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_5);
lean_dec(x_5);
x_9 = l_Nat_foldMAux___main___at_Lean_IR_EmitC_emitSimpleExternalCall___spec__1(x_1, x_2, x_3, x_4, x_8, x_6, x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
lean_object* l_Lean_IR_EmitC_emitSimpleExternalCall___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* _init_l_Lean_IR_EmitC_emitExternCall___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("failed to emit extern application '");
return x_1;
}
}
lean_object* l_Lean_IR_EmitC_emitExternCall(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_16; lean_object* x_17; 
x_16 = l_List_forM___main___at_Lean_IR_EmitC_emitFnDecls___spec__5___closed__2;
x_17 = l_Lean_getExternEntryFor(x_3, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
x_18 = lean_box(0);
x_7 = x_18;
goto block_15;
}
else
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
switch (lean_obj_tag(x_19)) {
case 0:
{
lean_object* x_20; 
lean_dec(x_19);
x_20 = lean_box(0);
x_7 = x_20;
goto block_15;
}
case 1:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_1);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_IR_EmitC_toStringArgs(x_4);
x_23 = l_Lean_expandExternPattern(x_21, x_22);
lean_dec(x_22);
x_24 = lean_string_append(x_6, x_23);
lean_dec(x_23);
x_25 = l_Lean_IR_formatFnBody___main___closed__1;
x_26 = lean_string_append(x_24, x_25);
x_27 = l_IO_println___rarg___closed__1;
x_28 = lean_string_append(x_26, x_27);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
default: 
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_1);
x_31 = lean_ctor_get(x_19, 1);
lean_inc(x_31);
lean_dec(x_19);
x_32 = l_Lean_IR_EmitC_emitSimpleExternalCall(x_31, x_2, x_4, x_5, x_6);
lean_dec(x_31);
return x_32;
}
}
}
block_15:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_7);
x_8 = l_System_FilePath_dirName___closed__1;
x_9 = l_Lean_Name_toStringWithSep___main(x_8, x_1);
x_10 = l_Lean_IR_EmitC_emitExternCall___closed__1;
x_11 = lean_string_append(x_10, x_9);
lean_dec(x_9);
x_12 = l_Char_HasRepr___closed__1;
x_13 = lean_string_append(x_11, x_12);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_6);
return x_14;
}
}
}
lean_object* l_Lean_IR_EmitC_emitExternCall___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_IR_EmitC_emitExternCall(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_IR_EmitC_emitFullApp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_13 = lean_ctor_get(x_11, 1);
x_14 = lean_ctor_get(x_11, 0);
lean_dec(x_14);
x_15 = lean_array_get_size(x_3);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_nat_dec_lt(x_16, x_15);
lean_dec(x_15);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = l_Lean_IR_formatFnBody___main___closed__1;
x_19 = lean_string_append(x_13, x_18);
x_20 = l_IO_println___rarg___closed__1;
x_21 = lean_string_append(x_19, x_20);
x_22 = lean_box(0);
lean_ctor_set(x_11, 1, x_21);
lean_ctor_set(x_11, 0, x_22);
return x_11;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
lean_free_object(x_11);
x_23 = l_Prod_HasRepr___rarg___closed__1;
x_24 = lean_string_append(x_13, x_23);
x_25 = l_Lean_IR_EmitC_emitArgs(x_3, x_4, x_24);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_27 = lean_ctor_get(x_25, 1);
x_28 = lean_ctor_get(x_25, 0);
lean_dec(x_28);
x_29 = l_Option_HasRepr___rarg___closed__3;
x_30 = lean_string_append(x_27, x_29);
x_31 = l_Lean_IR_formatFnBody___main___closed__1;
x_32 = lean_string_append(x_30, x_31);
x_33 = l_IO_println___rarg___closed__1;
x_34 = lean_string_append(x_32, x_33);
x_35 = lean_box(0);
lean_ctor_set(x_25, 1, x_34);
lean_ctor_set(x_25, 0, x_35);
return x_25;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_36 = lean_ctor_get(x_25, 1);
lean_inc(x_36);
lean_dec(x_25);
x_37 = l_Option_HasRepr___rarg___closed__3;
x_38 = lean_string_append(x_36, x_37);
x_39 = l_Lean_IR_formatFnBody___main___closed__1;
x_40 = lean_string_append(x_38, x_39);
x_41 = l_IO_println___rarg___closed__1;
x_42 = lean_string_append(x_40, x_41);
x_43 = lean_box(0);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_42);
return x_44;
}
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_45 = lean_ctor_get(x_11, 1);
lean_inc(x_45);
lean_dec(x_11);
x_46 = lean_array_get_size(x_3);
x_47 = lean_unsigned_to_nat(0u);
x_48 = lean_nat_dec_lt(x_47, x_46);
lean_dec(x_46);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_49 = l_Lean_IR_formatFnBody___main___closed__1;
x_50 = lean_string_append(x_45, x_49);
x_51 = l_IO_println___rarg___closed__1;
x_52 = lean_string_append(x_50, x_51);
x_53 = lean_box(0);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_52);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_55 = l_Prod_HasRepr___rarg___closed__1;
x_56 = lean_string_append(x_45, x_55);
x_57 = l_Lean_IR_EmitC_emitArgs(x_3, x_4, x_56);
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_59 = x_57;
} else {
 lean_dec_ref(x_57);
 x_59 = lean_box(0);
}
x_60 = l_Option_HasRepr___rarg___closed__3;
x_61 = lean_string_append(x_58, x_60);
x_62 = l_Lean_IR_formatFnBody___main___closed__1;
x_63 = lean_string_append(x_61, x_62);
x_64 = l_IO_println___rarg___closed__1;
x_65 = lean_string_append(x_63, x_64);
x_66 = lean_box(0);
if (lean_is_scalar(x_59)) {
 x_67 = lean_alloc_ctor(0, 2, 0);
} else {
 x_67 = x_59;
}
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_65);
return x_67;
}
}
}
else
{
uint8_t x_68; 
x_68 = !lean_is_exclusive(x_11);
if (x_68 == 0)
{
return x_11;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_11, 0);
x_70 = lean_ctor_get(x_11, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_11);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_72 = lean_ctor_get(x_8, 1);
lean_inc(x_72);
lean_dec(x_8);
x_73 = lean_ctor_get(x_9, 1);
lean_inc(x_73);
x_74 = lean_ctor_get(x_9, 3);
lean_inc(x_74);
lean_dec(x_9);
x_75 = l_Lean_IR_EmitC_emitExternCall(x_2, x_73, x_74, x_3, x_4, x_72);
lean_dec(x_74);
lean_dec(x_73);
return x_75;
}
}
else
{
uint8_t x_76; 
lean_dec(x_2);
x_76 = !lean_is_exclusive(x_8);
if (x_76 == 0)
{
return x_8;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_8, 0);
x_78 = lean_ctor_get(x_8, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_8);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
}
lean_object* l_Lean_IR_EmitC_emitFullApp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_EmitC_emitFullApp(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
lean_object* _init_l_Nat_forMAux___main___at_Lean_IR_EmitC_emitPartialApp___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("lean_closure_set(");
return x_1;
}
}
lean_object* l_Nat_forMAux___main___at_Lean_IR_EmitC_emitPartialApp___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_13 = l_Lean_IR_Arg_Inhabited;
x_14 = lean_array_get(x_13, x_2, x_12);
x_15 = l_Nat_forMAux___main___at_Lean_IR_EmitC_emitPartialApp___spec__1___closed__1;
x_16 = lean_string_append(x_6, x_15);
lean_inc(x_1);
x_17 = l_Nat_repr(x_1);
x_18 = l_Lean_IR_VarId_HasToString___closed__1;
x_19 = lean_string_append(x_18, x_17);
lean_dec(x_17);
x_20 = lean_string_append(x_16, x_19);
lean_dec(x_19);
x_21 = l_List_reprAux___main___rarg___closed__1;
x_22 = lean_string_append(x_20, x_21);
x_23 = l_Nat_repr(x_12);
x_24 = lean_string_append(x_22, x_23);
lean_dec(x_23);
x_25 = lean_string_append(x_24, x_21);
x_26 = l_Lean_IR_EmitC_emitArg(x_14, x_5, x_25);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = l_Lean_IR_EmitC_emitInc___closed__1;
x_29 = lean_string_append(x_27, x_28);
x_30 = l_IO_println___rarg___closed__1;
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
lean_object* _init_l_Lean_IR_EmitC_emitPartialApp___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("lean_alloc_closure((void*)(");
return x_1;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitPartialApp___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("), ");
return x_1;
}
}
lean_object* l_Lean_IR_EmitC_emitPartialApp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
x_21 = l_List_reprAux___main___rarg___closed__1;
x_22 = lean_string_append(x_20, x_21);
x_23 = lean_array_get_size(x_3);
lean_inc(x_23);
x_24 = l_Nat_repr(x_23);
x_25 = lean_string_append(x_22, x_24);
lean_dec(x_24);
x_26 = l_Lean_IR_EmitC_emitInc___closed__1;
x_27 = lean_string_append(x_25, x_26);
x_28 = l_IO_println___rarg___closed__1;
x_29 = lean_string_append(x_27, x_28);
lean_inc(x_23);
x_30 = l_Nat_forMAux___main___at_Lean_IR_EmitC_emitPartialApp___spec__1(x_1, x_3, x_23, x_23, x_4, x_29);
lean_dec(x_23);
return x_30;
}
else
{
uint8_t x_31; 
lean_dec(x_10);
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
lean_object* l_Nat_forMAux___main___at_Lean_IR_EmitC_emitPartialApp___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Nat_forMAux___main___at_Lean_IR_EmitC_emitPartialApp___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_IR_EmitC_emitPartialApp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_EmitC_emitPartialApp(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitApp___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("lean_apply_");
return x_1;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitApp___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("{ lean_object* _aargs[] = {");
return x_1;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitApp___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("};");
return x_1;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitApp___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("lean_apply_m(");
return x_1;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitApp___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(", _aargs); }");
return x_1;
}
}
lean_object* l_Lean_IR_EmitC_emitApp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
x_15 = l_Prod_HasRepr___rarg___closed__1;
x_16 = lean_string_append(x_14, x_15);
x_17 = l_Nat_repr(x_2);
x_18 = l_Lean_IR_VarId_HasToString___closed__1;
x_19 = lean_string_append(x_18, x_17);
lean_dec(x_17);
x_20 = lean_string_append(x_16, x_19);
lean_dec(x_19);
x_21 = l_List_reprAux___main___rarg___closed__1;
x_22 = lean_string_append(x_20, x_21);
x_23 = l_Lean_IR_EmitC_emitArgs(x_3, x_4, x_22);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_25 = lean_ctor_get(x_23, 1);
x_26 = lean_ctor_get(x_23, 0);
lean_dec(x_26);
x_27 = l_Lean_IR_EmitC_emitInc___closed__1;
x_28 = lean_string_append(x_25, x_27);
x_29 = l_IO_println___rarg___closed__1;
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
x_33 = l_Lean_IR_EmitC_emitInc___closed__1;
x_34 = lean_string_append(x_32, x_33);
x_35 = l_IO_println___rarg___closed__1;
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
x_41 = l_Lean_IR_EmitC_emitArgs(x_3, x_4, x_40);
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
lean_dec(x_41);
x_43 = l_Lean_IR_EmitC_emitApp___closed__3;
x_44 = lean_string_append(x_42, x_43);
x_45 = l_IO_println___rarg___closed__1;
x_46 = lean_string_append(x_44, x_45);
x_47 = l_Lean_IR_EmitC_emitLhs(x_1, x_4, x_46);
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
x_54 = l_Lean_IR_VarId_HasToString___closed__1;
x_55 = lean_string_append(x_54, x_53);
lean_dec(x_53);
x_56 = lean_string_append(x_52, x_55);
lean_dec(x_55);
x_57 = l_List_reprAux___main___rarg___closed__1;
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
x_69 = l_Lean_IR_VarId_HasToString___closed__1;
x_70 = lean_string_append(x_69, x_68);
lean_dec(x_68);
x_71 = lean_string_append(x_67, x_70);
lean_dec(x_70);
x_72 = l_List_reprAux___main___rarg___closed__1;
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
lean_object* l_Lean_IR_EmitC_emitApp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_EmitC_emitApp(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitBoxFn___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("lean_box");
return x_1;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitBoxFn___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("lean_box_uint32");
return x_1;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitBoxFn___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("lean_box_uint64");
return x_1;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitBoxFn___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("lean_box_usize");
return x_1;
}
}
lean_object* l_Lean_IR_EmitC_emitBoxFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_IR_EmitC_emitSSet___closed__1;
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
case 3:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = l_Lean_IR_EmitC_emitBoxFn___closed__2;
x_7 = lean_string_append(x_3, x_6);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
case 4:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_Lean_IR_EmitC_emitBoxFn___closed__3;
x_11 = lean_string_append(x_3, x_10);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
case 5:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = l_Lean_IR_EmitC_emitBoxFn___closed__4;
x_15 = lean_string_append(x_3, x_14);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
default: 
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = l_Lean_IR_EmitC_emitBoxFn___closed__1;
x_19 = lean_string_append(x_3, x_18);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
}
}
lean_object* l_Lean_IR_EmitC_emitBoxFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_EmitC_emitBoxFn(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_IR_EmitC_emitBox(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Lean_IR_EmitC_emitLhs(x_1, x_4, x_5);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = l_Lean_IR_EmitC_emitBoxFn(x_3, x_4, x_7);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_10 = lean_ctor_get(x_8, 1);
x_11 = lean_ctor_get(x_8, 0);
lean_dec(x_11);
x_12 = l_Prod_HasRepr___rarg___closed__1;
x_13 = lean_string_append(x_10, x_12);
x_14 = l_Nat_repr(x_2);
x_15 = l_Lean_IR_VarId_HasToString___closed__1;
x_16 = lean_string_append(x_15, x_14);
lean_dec(x_14);
x_17 = lean_string_append(x_13, x_16);
lean_dec(x_16);
x_18 = l_Lean_IR_EmitC_emitInc___closed__1;
x_19 = lean_string_append(x_17, x_18);
x_20 = l_IO_println___rarg___closed__1;
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
x_24 = l_Prod_HasRepr___rarg___closed__1;
x_25 = lean_string_append(x_23, x_24);
x_26 = l_Nat_repr(x_2);
x_27 = l_Lean_IR_VarId_HasToString___closed__1;
x_28 = lean_string_append(x_27, x_26);
lean_dec(x_26);
x_29 = lean_string_append(x_25, x_28);
lean_dec(x_28);
x_30 = l_Lean_IR_EmitC_emitInc___closed__1;
x_31 = lean_string_append(x_29, x_30);
x_32 = l_IO_println___rarg___closed__1;
x_33 = lean_string_append(x_31, x_32);
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
return x_35;
}
}
else
{
uint8_t x_36; 
lean_dec(x_2);
x_36 = !lean_is_exclusive(x_8);
if (x_36 == 0)
{
return x_8;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_8, 0);
x_38 = lean_ctor_get(x_8, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_8);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
lean_object* l_Lean_IR_EmitC_emitBox___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_EmitC_emitBox(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitUnbox___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("lean_unbox");
return x_1;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitUnbox___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("lean_unbox_uint32");
return x_1;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitUnbox___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("lean_unbox_uint64");
return x_1;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitUnbox___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("lean_unbox_usize");
return x_1;
}
}
lean_object* l_Lean_IR_EmitC_emitUnbox(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_20; 
x_20 = l_Lean_IR_EmitC_emitLhs(x_1, x_4, x_5);
switch (lean_obj_tag(x_2)) {
case 0:
{
uint8_t x_21; 
lean_dec(x_3);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_20, 0);
lean_dec(x_22);
x_23 = l_Lean_IR_EmitC_emitSSet___closed__1;
lean_ctor_set_tag(x_20, 1);
lean_ctor_set(x_20, 0, x_23);
return x_20;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_20, 1);
lean_inc(x_24);
lean_dec(x_20);
x_25 = l_Lean_IR_EmitC_emitSSet___closed__1;
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
case 3:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_20, 1);
lean_inc(x_27);
lean_dec(x_20);
x_28 = l_Lean_IR_EmitC_emitUnbox___closed__2;
x_29 = lean_string_append(x_27, x_28);
x_6 = x_29;
goto block_19;
}
case 4:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_20, 1);
lean_inc(x_30);
lean_dec(x_20);
x_31 = l_Lean_IR_EmitC_emitUnbox___closed__3;
x_32 = lean_string_append(x_30, x_31);
x_6 = x_32;
goto block_19;
}
case 5:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_20, 1);
lean_inc(x_33);
lean_dec(x_20);
x_34 = l_Lean_IR_EmitC_emitUnbox___closed__4;
x_35 = lean_string_append(x_33, x_34);
x_6 = x_35;
goto block_19;
}
default: 
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_20, 1);
lean_inc(x_36);
lean_dec(x_20);
x_37 = l_Lean_IR_EmitC_emitUnbox___closed__1;
x_38 = lean_string_append(x_36, x_37);
x_6 = x_38;
goto block_19;
}
}
block_19:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_7 = l_Prod_HasRepr___rarg___closed__1;
x_8 = lean_string_append(x_6, x_7);
x_9 = l_Nat_repr(x_3);
x_10 = l_Lean_IR_VarId_HasToString___closed__1;
x_11 = lean_string_append(x_10, x_9);
lean_dec(x_9);
x_12 = lean_string_append(x_8, x_11);
lean_dec(x_11);
x_13 = l_Lean_IR_EmitC_emitInc___closed__1;
x_14 = lean_string_append(x_12, x_13);
x_15 = l_IO_println___rarg___closed__1;
x_16 = lean_string_append(x_14, x_15);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
}
lean_object* l_Lean_IR_EmitC_emitUnbox___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_EmitC_emitUnbox(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_6;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitIsShared___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("!lean_is_exclusive(");
return x_1;
}
}
lean_object* l_Lean_IR_EmitC_emitIsShared(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_12 = l_Lean_IR_VarId_HasToString___closed__1;
x_13 = lean_string_append(x_12, x_11);
lean_dec(x_11);
x_14 = lean_string_append(x_10, x_13);
lean_dec(x_13);
x_15 = l_Lean_IR_EmitC_emitInc___closed__1;
x_16 = lean_string_append(x_14, x_15);
x_17 = l_IO_println___rarg___closed__1;
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
x_24 = l_Lean_IR_VarId_HasToString___closed__1;
x_25 = lean_string_append(x_24, x_23);
lean_dec(x_23);
x_26 = lean_string_append(x_22, x_25);
lean_dec(x_25);
x_27 = l_Lean_IR_EmitC_emitInc___closed__1;
x_28 = lean_string_append(x_26, x_27);
x_29 = l_IO_println___rarg___closed__1;
x_30 = lean_string_append(x_28, x_29);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
}
lean_object* l_Lean_IR_EmitC_emitIsShared___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_EmitC_emitIsShared(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitIsTaggedPtr___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("!lean_is_scalar(");
return x_1;
}
}
lean_object* l_Lean_IR_EmitC_emitIsTaggedPtr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_12 = l_Lean_IR_VarId_HasToString___closed__1;
x_13 = lean_string_append(x_12, x_11);
lean_dec(x_11);
x_14 = lean_string_append(x_10, x_13);
lean_dec(x_13);
x_15 = l_Lean_IR_EmitC_emitInc___closed__1;
x_16 = lean_string_append(x_14, x_15);
x_17 = l_IO_println___rarg___closed__1;
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
x_24 = l_Lean_IR_VarId_HasToString___closed__1;
x_25 = lean_string_append(x_24, x_23);
lean_dec(x_23);
x_26 = lean_string_append(x_22, x_25);
lean_dec(x_25);
x_27 = l_Lean_IR_EmitC_emitInc___closed__1;
x_28 = lean_string_append(x_26, x_27);
x_29 = l_IO_println___rarg___closed__1;
x_30 = lean_string_append(x_28, x_29);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
}
lean_object* l_Lean_IR_EmitC_emitIsTaggedPtr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_EmitC_emitIsTaggedPtr(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Lean_IR_EmitC_toHexDigit(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Nat_digitChar(x_1);
x_3 = l_String_splitAux___main___closed__1;
x_4 = lean_string_push(x_3, x_2);
return x_4;
}
}
lean_object* l_Lean_IR_EmitC_toHexDigit___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_IR_EmitC_toHexDigit(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_String_foldlAux___main___at_Lean_IR_EmitC_quoteString___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; uint8_t x_7; 
x_5 = lean_nat_dec_eq(x_3, x_2);
x_6 = 1;
x_7 = l_Bool_DecidableEq(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; uint32_t x_9; uint32_t x_10; uint8_t x_11; uint8_t x_12; 
x_8 = lean_string_utf8_next(x_1, x_3);
x_9 = lean_string_utf8_get(x_1, x_3);
lean_dec(x_3);
x_10 = 10;
x_11 = l_Char_DecidableEq(x_9, x_10);
x_12 = l_Bool_DecidableEq(x_11, x_6);
if (x_12 == 0)
{
uint32_t x_13; uint8_t x_14; uint8_t x_15; 
x_13 = 92;
x_14 = l_Char_DecidableEq(x_9, x_13);
x_15 = l_Bool_DecidableEq(x_14, x_6);
if (x_15 == 0)
{
uint32_t x_16; uint8_t x_17; uint8_t x_18; 
x_16 = 34;
x_17 = l_Char_DecidableEq(x_9, x_16);
x_18 = l_Bool_DecidableEq(x_17, x_6);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_uint32_to_nat(x_9);
x_20 = lean_unsigned_to_nat(31u);
x_21 = lean_nat_dec_le(x_19, x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_19);
x_22 = l_String_splitAux___main___closed__1;
x_23 = lean_string_push(x_22, x_9);
x_24 = lean_string_append(x_4, x_23);
lean_dec(x_23);
x_3 = x_8;
x_4 = x_24;
goto _start;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_26 = lean_unsigned_to_nat(16u);
x_27 = lean_nat_div(x_19, x_26);
x_28 = l_Lean_IR_EmitC_toHexDigit(x_27);
lean_dec(x_27);
x_29 = l_Char_quoteCore___closed__1;
x_30 = lean_string_append(x_29, x_28);
lean_dec(x_28);
x_31 = lean_nat_mod(x_19, x_26);
lean_dec(x_19);
x_32 = l_Lean_IR_EmitC_toHexDigit(x_31);
lean_dec(x_31);
x_33 = lean_string_append(x_30, x_32);
lean_dec(x_32);
x_34 = lean_string_append(x_4, x_33);
lean_dec(x_33);
x_3 = x_8;
x_4 = x_34;
goto _start;
}
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = l_Char_quoteCore___closed__2;
x_37 = lean_string_append(x_4, x_36);
x_3 = x_8;
x_4 = x_37;
goto _start;
}
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = l_Char_quoteCore___closed__3;
x_40 = lean_string_append(x_4, x_39);
x_3 = x_8;
x_4 = x_40;
goto _start;
}
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = l_Char_quoteCore___closed__5;
x_43 = lean_string_append(x_4, x_42);
x_3 = x_8;
x_4 = x_43;
goto _start;
}
}
else
{
lean_dec(x_3);
return x_4;
}
}
}
lean_object* l_Lean_IR_EmitC_quoteString(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_string_utf8_byte_size(x_1);
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_String_quote___closed__1;
x_5 = l_String_foldlAux___main___at_Lean_IR_EmitC_quoteString___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_2);
x_6 = lean_string_append(x_5, x_4);
return x_6;
}
}
lean_object* l_String_foldlAux___main___at_Lean_IR_EmitC_quoteString___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_String_foldlAux___main___at_Lean_IR_EmitC_quoteString___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_IR_EmitC_quoteString___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_IR_EmitC_quoteString(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitNumLit___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("lean_cstr_to_nat(\"");
return x_1;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitNumLit___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("\")");
return x_1;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitNumLit___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("lean_unsigned_to_nat(");
return x_1;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitNumLit___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("u)");
return x_1;
}
}
lean_object* l_Lean_IR_EmitC_emitNumLit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; uint8_t x_7; 
x_5 = l_Lean_IR_IRType_isObj(x_1);
x_6 = 1;
x_7 = l_Bool_DecidableEq(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = l_Nat_repr(x_2);
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
lean_object* x_12; uint8_t x_13; 
x_12 = l_uint32Sz;
x_13 = lean_nat_dec_lt(x_2, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_14 = l_Lean_IR_EmitC_emitNumLit___closed__1;
x_15 = lean_string_append(x_4, x_14);
x_16 = l_Nat_repr(x_2);
x_17 = lean_string_append(x_15, x_16);
lean_dec(x_16);
x_18 = l_Lean_IR_EmitC_emitNumLit___closed__2;
x_19 = lean_string_append(x_17, x_18);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_22 = l_Lean_IR_EmitC_emitNumLit___closed__3;
x_23 = lean_string_append(x_4, x_22);
x_24 = l_Nat_repr(x_2);
x_25 = lean_string_append(x_23, x_24);
lean_dec(x_24);
x_26 = l_Lean_IR_EmitC_emitNumLit___closed__4;
x_27 = lean_string_append(x_25, x_26);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
}
}
lean_object* l_Lean_IR_EmitC_emitNumLit___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_EmitC_emitNumLit(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitLit___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("lean_mk_string(");
return x_1;
}
}
lean_object* l_Lean_IR_EmitC_emitLit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
x_13 = l_Lean_IR_formatFnBody___main___closed__1;
x_14 = lean_string_append(x_11, x_13);
x_15 = l_IO_println___rarg___closed__1;
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
x_19 = l_Lean_IR_formatFnBody___main___closed__1;
x_20 = lean_string_append(x_18, x_19);
x_21 = l_IO_println___rarg___closed__1;
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
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_26 = lean_ctor_get(x_6, 1);
x_27 = lean_ctor_get(x_6, 0);
lean_dec(x_27);
x_28 = lean_ctor_get(x_3, 0);
lean_inc(x_28);
lean_dec(x_3);
x_29 = l_Lean_IR_EmitC_emitLit___closed__1;
x_30 = lean_string_append(x_26, x_29);
x_31 = l_Lean_IR_EmitC_quoteString(x_28);
lean_dec(x_28);
x_32 = lean_string_append(x_30, x_31);
lean_dec(x_31);
x_33 = l_Lean_IR_EmitC_emitInc___closed__1;
x_34 = lean_string_append(x_32, x_33);
x_35 = l_IO_println___rarg___closed__1;
x_36 = lean_string_append(x_34, x_35);
x_37 = lean_box(0);
lean_ctor_set(x_6, 1, x_36);
lean_ctor_set(x_6, 0, x_37);
return x_6;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_38 = lean_ctor_get(x_6, 1);
lean_inc(x_38);
lean_dec(x_6);
x_39 = lean_ctor_get(x_3, 0);
lean_inc(x_39);
lean_dec(x_3);
x_40 = l_Lean_IR_EmitC_emitLit___closed__1;
x_41 = lean_string_append(x_38, x_40);
x_42 = l_Lean_IR_EmitC_quoteString(x_39);
lean_dec(x_39);
x_43 = lean_string_append(x_41, x_42);
lean_dec(x_42);
x_44 = l_Lean_IR_EmitC_emitInc___closed__1;
x_45 = lean_string_append(x_43, x_44);
x_46 = l_IO_println___rarg___closed__1;
x_47 = lean_string_append(x_45, x_46);
x_48 = lean_box(0);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_47);
return x_49;
}
}
}
}
lean_object* l_Lean_IR_EmitC_emitLit___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_EmitC_emitLit(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Lean_IR_EmitC_emitVDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
switch (lean_obj_tag(x_3)) {
case 0:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
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
x_9 = lean_ctor_get(x_3, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
lean_dec(x_3);
x_11 = l_Lean_IR_EmitC_emitReset(x_1, x_9, x_10, x_4, x_5);
return x_11;
}
case 2:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_3, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_3, 1);
lean_inc(x_13);
x_14 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
x_15 = lean_ctor_get(x_3, 2);
lean_inc(x_15);
lean_dec(x_3);
x_16 = l_Lean_IR_EmitC_emitReuse(x_1, x_12, x_13, x_14, x_15, x_4, x_5);
lean_dec(x_15);
return x_16;
}
case 3:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_3, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_3, 1);
lean_inc(x_18);
lean_dec(x_3);
x_19 = l_Lean_IR_EmitC_emitProj(x_1, x_17, x_18, x_4, x_5);
return x_19;
}
case 4:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_3, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_3, 1);
lean_inc(x_21);
lean_dec(x_3);
x_22 = l_Lean_IR_EmitC_emitUProj(x_1, x_20, x_21, x_4, x_5);
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
x_27 = lean_ctor_get(x_3, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_3, 1);
lean_inc(x_28);
lean_dec(x_3);
x_29 = l_Lean_IR_EmitC_emitFullApp(x_1, x_27, x_28, x_4, x_5);
lean_dec(x_28);
return x_29;
}
case 7:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_3, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_3, 1);
lean_inc(x_31);
lean_dec(x_3);
x_32 = l_Lean_IR_EmitC_emitPartialApp(x_1, x_30, x_31, x_4, x_5);
lean_dec(x_31);
return x_32;
}
case 8:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
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
x_36 = lean_ctor_get(x_3, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_3, 1);
lean_inc(x_37);
lean_dec(x_3);
x_38 = l_Lean_IR_EmitC_emitBox(x_1, x_37, x_36, x_4, x_5);
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
return x_42;
}
case 12:
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_3, 0);
lean_inc(x_43);
lean_dec(x_3);
x_44 = l_Lean_IR_EmitC_emitIsShared(x_1, x_43, x_4, x_5);
return x_44;
}
default: 
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_3, 0);
lean_inc(x_45);
lean_dec(x_3);
x_46 = l_Lean_IR_EmitC_emitIsTaggedPtr(x_1, x_45, x_4, x_5);
return x_46;
}
}
}
}
lean_object* l_Lean_IR_EmitC_emitVDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_EmitC_emitVDecl(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Lean_IR_EmitC_isTailCall(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* l_Lean_IR_EmitC_isTailCall___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
uint8_t l_Lean_IR_EmitC_paramEqArg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_IR_EmitC_paramEqArg___boxed(lean_object* x_1, lean_object* x_2) {
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
uint8_t l_Nat_anyAux___main___at_Lean_IR_EmitC_overwriteParam___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_4, x_7);
x_9 = lean_nat_sub(x_3, x_4);
lean_dec(x_4);
x_10 = l_Lean_IR_Arg_Inhabited;
x_11 = lean_array_get(x_10, x_1, x_9);
lean_dec(x_9);
x_12 = l_Lean_IR_EmitC_paramEqArg(x_2, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
x_4 = x_8;
goto _start;
}
else
{
uint8_t x_14; 
lean_dec(x_8);
x_14 = 1;
return x_14;
}
}
else
{
uint8_t x_15; 
lean_dec(x_4);
x_15 = 0;
return x_15;
}
}
}
uint8_t l_Nat_anyAux___main___at_Lean_IR_EmitC_overwriteParam___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_5, x_8);
x_10 = lean_nat_sub(x_4, x_5);
lean_dec(x_5);
x_11 = l_Lean_IR_paramInh;
x_12 = lean_array_get(x_11, x_1, x_10);
x_13 = lean_nat_add(x_10, x_8);
lean_dec(x_10);
x_14 = lean_nat_sub(x_3, x_13);
lean_dec(x_13);
x_15 = l_Nat_anyAux___main___at_Lean_IR_EmitC_overwriteParam___spec__1(x_2, x_12, x_3, x_14);
lean_dec(x_12);
if (x_15 == 0)
{
x_5 = x_9;
goto _start;
}
else
{
uint8_t x_17; 
lean_dec(x_9);
x_17 = 1;
return x_17;
}
}
else
{
uint8_t x_18; 
lean_dec(x_5);
x_18 = 0;
return x_18;
}
}
}
uint8_t l_Lean_IR_EmitC_overwriteParam(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_array_get_size(x_1);
lean_inc(x_3);
x_4 = l_Nat_anyAux___main___at_Lean_IR_EmitC_overwriteParam___spec__2(x_1, x_2, x_3, x_3, x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_Nat_anyAux___main___at_Lean_IR_EmitC_overwriteParam___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Nat_anyAux___main___at_Lean_IR_EmitC_overwriteParam___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_Nat_anyAux___main___at_Lean_IR_EmitC_overwriteParam___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Nat_anyAux___main___at_Lean_IR_EmitC_overwriteParam___spec__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l_Lean_IR_EmitC_overwriteParam___boxed(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Nat_forMAux___main___at_Lean_IR_EmitC_emitTailCall___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_eq(x_4, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_sub(x_4, x_9);
lean_dec(x_4);
x_11 = lean_nat_sub(x_3, x_10);
x_12 = lean_nat_sub(x_11, x_9);
lean_dec(x_11);
x_13 = l_Lean_IR_paramInh;
x_14 = lean_array_get(x_13, x_2, x_12);
x_15 = l_Lean_IR_Arg_Inhabited;
x_16 = lean_array_get(x_15, x_1, x_12);
lean_dec(x_12);
x_17 = l_Lean_IR_EmitC_paramEqArg(x_14, x_16);
x_18 = 1;
x_19 = l_Bool_DecidableEq(x_17, x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_20 = lean_ctor_get(x_14, 0);
lean_inc(x_20);
lean_dec(x_14);
x_21 = l_Nat_repr(x_20);
x_22 = l_Lean_IR_VarId_HasToString___closed__1;
x_23 = lean_string_append(x_22, x_21);
lean_dec(x_21);
x_24 = lean_string_append(x_6, x_23);
lean_dec(x_23);
x_25 = l_Nat_forMAux___main___at_Lean_IR_EmitC_emitJmp___spec__1___closed__1;
x_26 = lean_string_append(x_24, x_25);
x_27 = l_Lean_IR_EmitC_emitArg(x_16, x_5, x_26);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = l_Lean_IR_formatFnBody___main___closed__1;
x_30 = lean_string_append(x_28, x_29);
x_31 = l_IO_println___rarg___closed__1;
x_32 = lean_string_append(x_30, x_31);
x_4 = x_10;
x_6 = x_32;
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
lean_object* _init_l_Nat_forMAux___main___at_Lean_IR_EmitC_emitTailCall___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" _tmp_");
return x_1;
}
}
lean_object* l_Nat_forMAux___main___at_Lean_IR_EmitC_emitTailCall___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_eq(x_4, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_sub(x_4, x_9);
lean_dec(x_4);
x_11 = lean_nat_sub(x_3, x_10);
x_12 = lean_nat_sub(x_11, x_9);
lean_dec(x_11);
x_13 = l_Lean_IR_paramInh;
x_14 = lean_array_get(x_13, x_2, x_12);
x_15 = l_Lean_IR_Arg_Inhabited;
x_16 = lean_array_get(x_15, x_1, x_12);
x_17 = l_Lean_IR_EmitC_paramEqArg(x_14, x_16);
x_18 = 1;
x_19 = l_Bool_DecidableEq(x_17, x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_20 = lean_ctor_get(x_14, 1);
lean_inc(x_20);
lean_dec(x_14);
x_21 = l_Lean_IR_EmitC_toCType(x_20);
lean_dec(x_20);
x_22 = lean_string_append(x_6, x_21);
lean_dec(x_21);
x_23 = l_Nat_forMAux___main___at_Lean_IR_EmitC_emitTailCall___spec__2___closed__1;
x_24 = lean_string_append(x_22, x_23);
x_25 = l_Nat_repr(x_12);
x_26 = lean_string_append(x_24, x_25);
lean_dec(x_25);
x_27 = l_Nat_forMAux___main___at_Lean_IR_EmitC_emitJmp___spec__1___closed__1;
x_28 = lean_string_append(x_26, x_27);
x_29 = l_Lean_IR_EmitC_emitArg(x_16, x_5, x_28);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_31 = l_Lean_IR_formatFnBody___main___closed__1;
x_32 = lean_string_append(x_30, x_31);
x_33 = l_IO_println___rarg___closed__1;
x_34 = lean_string_append(x_32, x_33);
x_4 = x_10;
x_6 = x_34;
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
lean_object* x_37; lean_object* x_38; 
lean_dec(x_4);
x_37 = lean_box(0);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_6);
return x_38;
}
}
}
lean_object* _init_l_Nat_forMAux___main___at_Lean_IR_EmitC_emitTailCall___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" = _tmp_");
return x_1;
}
}
lean_object* l_Nat_forMAux___main___at_Lean_IR_EmitC_emitTailCall___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_eq(x_4, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_sub(x_4, x_9);
lean_dec(x_4);
x_11 = lean_nat_sub(x_3, x_10);
x_12 = lean_nat_sub(x_11, x_9);
lean_dec(x_11);
x_13 = l_Lean_IR_paramInh;
x_14 = lean_array_get(x_13, x_2, x_12);
x_15 = l_Lean_IR_Arg_Inhabited;
x_16 = lean_array_get(x_15, x_1, x_12);
x_17 = l_Lean_IR_EmitC_paramEqArg(x_14, x_16);
lean_dec(x_16);
x_18 = 1;
x_19 = l_Bool_DecidableEq(x_17, x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_20 = lean_ctor_get(x_14, 0);
lean_inc(x_20);
lean_dec(x_14);
x_21 = l_Nat_repr(x_20);
x_22 = l_Lean_IR_VarId_HasToString___closed__1;
x_23 = lean_string_append(x_22, x_21);
lean_dec(x_21);
x_24 = lean_string_append(x_6, x_23);
lean_dec(x_23);
x_25 = l_Nat_forMAux___main___at_Lean_IR_EmitC_emitTailCall___spec__3___closed__1;
x_26 = lean_string_append(x_24, x_25);
x_27 = l_Nat_repr(x_12);
x_28 = lean_string_append(x_26, x_27);
lean_dec(x_27);
x_29 = l_Lean_IR_formatFnBody___main___closed__1;
x_30 = lean_string_append(x_28, x_29);
x_31 = l_IO_println___rarg___closed__1;
x_32 = lean_string_append(x_30, x_31);
x_4 = x_10;
x_6 = x_32;
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
lean_object* _init_l_Lean_IR_EmitC_emitTailCall___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("bug at emitTailCall");
return x_1;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitTailCall___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid tail call");
return x_1;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitTailCall___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("goto _start;");
return x_1;
}
}
lean_object* l_Lean_IR_EmitC_emitTailCall(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 6)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; uint8_t x_10; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_2, 4);
x_6 = lean_array_get_size(x_5);
x_7 = lean_array_get_size(x_4);
x_8 = lean_nat_dec_eq(x_6, x_7);
x_9 = 1;
x_10 = l_Bool_DecidableEq(x_8, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_7);
lean_dec(x_6);
x_11 = l_Lean_IR_EmitC_emitTailCall___closed__2;
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_3);
return x_12;
}
else
{
uint8_t x_13; uint8_t x_14; 
x_13 = l_Lean_IR_EmitC_overwriteParam(x_5, x_4);
x_14 = l_Bool_DecidableEq(x_13, x_9);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
lean_dec(x_6);
lean_inc(x_7);
x_15 = l_Nat_forMAux___main___at_Lean_IR_EmitC_emitTailCall___spec__1(x_4, x_5, x_7, x_7, x_2, x_3);
lean_dec(x_7);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_17 = lean_ctor_get(x_15, 1);
x_18 = lean_ctor_get(x_15, 0);
lean_dec(x_18);
x_19 = l_Lean_IR_EmitC_emitTailCall___closed__3;
x_20 = lean_string_append(x_17, x_19);
x_21 = l_IO_println___rarg___closed__1;
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
x_25 = l_Lean_IR_EmitC_emitTailCall___closed__3;
x_26 = lean_string_append(x_24, x_25);
x_27 = l_IO_println___rarg___closed__1;
x_28 = lean_string_append(x_26, x_27);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
lean_dec(x_7);
x_31 = l_addParenHeuristic___closed__1;
x_32 = lean_string_append(x_3, x_31);
x_33 = l_IO_println___rarg___closed__1;
x_34 = lean_string_append(x_32, x_33);
lean_inc(x_6);
x_35 = l_Nat_forMAux___main___at_Lean_IR_EmitC_emitTailCall___spec__2(x_4, x_5, x_6, x_6, x_2, x_34);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
lean_inc(x_6);
x_37 = l_Nat_forMAux___main___at_Lean_IR_EmitC_emitTailCall___spec__3(x_4, x_5, x_6, x_6, x_2, x_36);
lean_dec(x_6);
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_39 = lean_ctor_get(x_37, 1);
x_40 = lean_ctor_get(x_37, 0);
lean_dec(x_40);
x_41 = l_PersistentArray_Stats_toString___closed__4;
x_42 = lean_string_append(x_39, x_41);
x_43 = lean_string_append(x_42, x_33);
x_44 = l_Lean_IR_EmitC_emitTailCall___closed__3;
x_45 = lean_string_append(x_43, x_44);
x_46 = lean_string_append(x_45, x_33);
x_47 = lean_box(0);
lean_ctor_set(x_37, 1, x_46);
lean_ctor_set(x_37, 0, x_47);
return x_37;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_48 = lean_ctor_get(x_37, 1);
lean_inc(x_48);
lean_dec(x_37);
x_49 = l_PersistentArray_Stats_toString___closed__4;
x_50 = lean_string_append(x_48, x_49);
x_51 = lean_string_append(x_50, x_33);
x_52 = l_Lean_IR_EmitC_emitTailCall___closed__3;
x_53 = lean_string_append(x_51, x_52);
x_54 = lean_string_append(x_53, x_33);
x_55 = lean_box(0);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_54);
return x_56;
}
}
}
}
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = l_Lean_IR_EmitC_emitTailCall___closed__1;
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_3);
return x_58;
}
}
}
lean_object* l_Nat_forMAux___main___at_Lean_IR_EmitC_emitTailCall___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Nat_forMAux___main___at_Lean_IR_EmitC_emitTailCall___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Nat_forMAux___main___at_Lean_IR_EmitC_emitTailCall___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Nat_forMAux___main___at_Lean_IR_EmitC_emitTailCall___spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Nat_forMAux___main___at_Lean_IR_EmitC_emitTailCall___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Nat_forMAux___main___at_Lean_IR_EmitC_emitTailCall___spec__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_IR_EmitC_emitTailCall___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_EmitC_emitTailCall(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitBlock___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("return ");
return x_1;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitBlock___main___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("lean_panic_unreachable();");
return x_1;
}
}
lean_object* l_Lean_IR_EmitC_emitBlock___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_11; uint8_t x_12; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 2);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 3);
lean_inc(x_8);
x_9 = lean_ctor_get(x_3, 3);
lean_inc(x_9);
x_10 = l_Lean_IR_isTailCallTo(x_9, x_2);
lean_dec(x_2);
lean_dec(x_9);
x_11 = 1;
x_12 = l_Bool_DecidableEq(x_10, x_11);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = l_Lean_IR_EmitC_emitVDecl(x_5, x_6, x_7, x_3, x_4);
lean_dec(x_6);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_2 = x_8;
x_4 = x_14;
goto _start;
}
else
{
uint8_t x_16; 
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_1);
x_16 = !lean_is_exclusive(x_13);
if (x_16 == 0)
{
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_13, 0);
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_13);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
else
{
lean_object* x_20; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_20 = l_Lean_IR_EmitC_emitTailCall(x_7, x_3, x_4);
lean_dec(x_3);
lean_dec(x_7);
return x_20;
}
}
case 1:
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_2, 3);
lean_inc(x_21);
lean_dec(x_2);
x_2 = x_21;
goto _start;
}
case 2:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_23 = lean_ctor_get(x_2, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_2, 1);
lean_inc(x_24);
x_25 = lean_ctor_get(x_2, 2);
lean_inc(x_25);
x_26 = lean_ctor_get(x_2, 3);
lean_inc(x_26);
lean_dec(x_2);
x_27 = l_Lean_IR_EmitC_emitSet(x_23, x_24, x_25, x_3, x_4);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_2 = x_26;
x_4 = x_28;
goto _start;
}
case 3:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_30 = lean_ctor_get(x_2, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_2, 1);
lean_inc(x_31);
x_32 = lean_ctor_get(x_2, 2);
lean_inc(x_32);
lean_dec(x_2);
x_33 = l_Lean_IR_EmitC_emitSetTag(x_30, x_31, x_3, x_4);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
x_2 = x_32;
x_4 = x_34;
goto _start;
}
case 4:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_36 = lean_ctor_get(x_2, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_2, 1);
lean_inc(x_37);
x_38 = lean_ctor_get(x_2, 2);
lean_inc(x_38);
x_39 = lean_ctor_get(x_2, 3);
lean_inc(x_39);
lean_dec(x_2);
x_40 = l_Lean_IR_EmitC_emitUSet(x_36, x_37, x_38, x_3, x_4);
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec(x_40);
x_2 = x_39;
x_4 = x_41;
goto _start;
}
case 5:
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_43 = lean_ctor_get(x_2, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_2, 1);
lean_inc(x_44);
x_45 = lean_ctor_get(x_2, 2);
lean_inc(x_45);
x_46 = lean_ctor_get(x_2, 3);
lean_inc(x_46);
x_47 = lean_ctor_get(x_2, 4);
lean_inc(x_47);
x_48 = lean_ctor_get(x_2, 5);
lean_inc(x_48);
lean_dec(x_2);
x_49 = l_Lean_IR_EmitC_emitSSet(x_43, x_44, x_45, x_46, x_47, x_3, x_4);
lean_dec(x_47);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_49, 1);
lean_inc(x_50);
lean_dec(x_49);
x_2 = x_48;
x_4 = x_50;
goto _start;
}
else
{
uint8_t x_52; 
lean_dec(x_48);
lean_dec(x_3);
lean_dec(x_1);
x_52 = !lean_is_exclusive(x_49);
if (x_52 == 0)
{
return x_49;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_49, 0);
x_54 = lean_ctor_get(x_49, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_49);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
case 6:
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; uint8_t x_59; lean_object* x_60; uint8_t x_61; uint8_t x_62; 
x_56 = lean_ctor_get(x_2, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_2, 1);
lean_inc(x_57);
x_58 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_59 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 1);
x_60 = lean_ctor_get(x_2, 2);
lean_inc(x_60);
lean_dec(x_2);
x_61 = 1;
x_62 = l_Bool_DecidableEq(x_59, x_61);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; 
x_63 = l_Lean_IR_EmitC_emitInc(x_56, x_57, x_58, x_3, x_4);
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
lean_dec(x_63);
x_2 = x_60;
x_4 = x_64;
goto _start;
}
else
{
lean_dec(x_57);
lean_dec(x_56);
x_2 = x_60;
goto _start;
}
}
case 7:
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; uint8_t x_70; lean_object* x_71; uint8_t x_72; uint8_t x_73; 
x_67 = lean_ctor_get(x_2, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_2, 1);
lean_inc(x_68);
x_69 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_70 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 1);
x_71 = lean_ctor_get(x_2, 2);
lean_inc(x_71);
lean_dec(x_2);
x_72 = 1;
x_73 = l_Bool_DecidableEq(x_70, x_72);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; 
x_74 = l_Lean_IR_EmitC_emitDec(x_67, x_68, x_69, x_3, x_4);
x_75 = lean_ctor_get(x_74, 1);
lean_inc(x_75);
lean_dec(x_74);
x_2 = x_71;
x_4 = x_75;
goto _start;
}
else
{
lean_dec(x_68);
lean_dec(x_67);
x_2 = x_71;
goto _start;
}
}
case 8:
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_78 = lean_ctor_get(x_2, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_2, 1);
lean_inc(x_79);
lean_dec(x_2);
x_80 = l_Lean_IR_EmitC_emitDel(x_78, x_3, x_4);
x_81 = lean_ctor_get(x_80, 1);
lean_inc(x_81);
lean_dec(x_80);
x_2 = x_79;
x_4 = x_81;
goto _start;
}
case 9:
{
lean_object* x_83; 
x_83 = lean_ctor_get(x_2, 1);
lean_inc(x_83);
lean_dec(x_2);
x_2 = x_83;
goto _start;
}
case 10:
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_85 = lean_ctor_get(x_2, 1);
lean_inc(x_85);
x_86 = lean_ctor_get(x_2, 2);
lean_inc(x_86);
x_87 = lean_ctor_get(x_2, 3);
lean_inc(x_87);
lean_dec(x_2);
x_88 = l_Lean_IR_EmitC_emitCase(x_1, x_85, x_86, x_87, x_3, x_4);
lean_dec(x_86);
return x_88;
}
case 11:
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; 
lean_dec(x_1);
x_89 = lean_ctor_get(x_2, 0);
lean_inc(x_89);
lean_dec(x_2);
x_90 = l_Lean_IR_EmitC_emitBlock___main___closed__1;
x_91 = lean_string_append(x_4, x_90);
x_92 = l_Lean_IR_EmitC_emitArg(x_89, x_3, x_91);
lean_dec(x_3);
x_93 = !lean_is_exclusive(x_92);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_94 = lean_ctor_get(x_92, 1);
x_95 = lean_ctor_get(x_92, 0);
lean_dec(x_95);
x_96 = l_Lean_IR_formatFnBody___main___closed__1;
x_97 = lean_string_append(x_94, x_96);
x_98 = l_IO_println___rarg___closed__1;
x_99 = lean_string_append(x_97, x_98);
x_100 = lean_box(0);
lean_ctor_set(x_92, 1, x_99);
lean_ctor_set(x_92, 0, x_100);
return x_92;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_101 = lean_ctor_get(x_92, 1);
lean_inc(x_101);
lean_dec(x_92);
x_102 = l_Lean_IR_formatFnBody___main___closed__1;
x_103 = lean_string_append(x_101, x_102);
x_104 = l_IO_println___rarg___closed__1;
x_105 = lean_string_append(x_103, x_104);
x_106 = lean_box(0);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_105);
return x_107;
}
}
case 12:
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
lean_dec(x_1);
x_108 = lean_ctor_get(x_2, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_2, 1);
lean_inc(x_109);
lean_dec(x_2);
x_110 = l_Lean_IR_EmitC_emitJmp(x_108, x_109, x_3, x_4);
lean_dec(x_3);
lean_dec(x_109);
return x_110;
}
default: 
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
lean_dec(x_3);
lean_dec(x_1);
x_111 = l_Lean_IR_EmitC_emitBlock___main___closed__2;
x_112 = lean_string_append(x_4, x_111);
x_113 = l_IO_println___rarg___closed__1;
x_114 = lean_string_append(x_112, x_113);
x_115 = lean_box(0);
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_114);
return x_116;
}
}
}
}
lean_object* l_Lean_IR_EmitC_emitBlock(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_EmitC_emitBlock___main(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_IR_EmitC_emitJPs___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_2, 2);
lean_inc(x_15);
x_16 = lean_ctor_get(x_2, 3);
lean_inc(x_16);
lean_dec(x_2);
x_17 = l_Nat_repr(x_14);
x_18 = l_Lean_IR_JoinPointId_HasToString___closed__1;
x_19 = lean_string_append(x_18, x_17);
lean_dec(x_17);
x_20 = lean_string_append(x_4, x_19);
lean_dec(x_19);
x_21 = l___private_Init_Util_1__mkPanicMessage___closed__2;
x_22 = lean_string_append(x_20, x_21);
x_23 = l_IO_println___rarg___closed__1;
x_24 = lean_string_append(x_22, x_23);
lean_inc(x_1);
lean_inc(x_3);
x_25 = lean_apply_3(x_1, x_15, x_3, x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_2 = x_16;
x_4 = x_26;
goto _start;
}
else
{
uint8_t x_28; 
lean_dec(x_16);
lean_dec(x_3);
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_25);
if (x_28 == 0)
{
return x_25;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_25, 0);
x_30 = lean_ctor_get(x_25, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_25);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
else
{
lean_object* x_32; 
x_32 = lean_box(0);
x_5 = x_32;
goto block_13;
}
block_13:
{
uint8_t x_6; uint8_t x_7; uint8_t x_8; 
lean_dec(x_5);
x_6 = l_Lean_IR_FnBody_isTerminal(x_2);
x_7 = 1;
x_8 = l_Bool_DecidableEq(x_6, x_7);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = l_Lean_IR_FnBody_body(x_2);
lean_dec(x_2);
x_2 = x_9;
goto _start;
}
else
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_4);
return x_12;
}
}
}
}
lean_object* l_Lean_IR_EmitC_emitJPs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_EmitC_emitJPs___main(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitFnBody___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_IR_EmitC_emitFnBody___main), 3, 0);
return x_1;
}
}
lean_object* l_Lean_IR_EmitC_emitFnBody___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; 
x_4 = l_addParenHeuristic___closed__1;
x_5 = lean_string_append(x_3, x_4);
x_6 = l_IO_println___rarg___closed__1;
x_7 = lean_string_append(x_5, x_6);
x_8 = 0;
lean_inc(x_1);
x_9 = l_Lean_IR_EmitC_declareVars___main(x_1, x_8, x_2, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = 1;
x_13 = lean_unbox(x_10);
lean_dec(x_10);
x_14 = l_Bool_DecidableEq(x_13, x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = l_Lean_IR_EmitC_emitFnBody___main___closed__1;
lean_inc(x_2);
lean_inc(x_1);
x_16 = l_Lean_IR_EmitC_emitBlock___main(x_15, x_1, x_2, x_11);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = l_Lean_IR_EmitC_emitJPs___main(x_15, x_1, x_2, x_17);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_18, 1);
x_21 = lean_ctor_get(x_18, 0);
lean_dec(x_21);
x_22 = l_PersistentArray_Stats_toString___closed__4;
x_23 = lean_string_append(x_20, x_22);
x_24 = lean_string_append(x_23, x_6);
x_25 = lean_box(0);
lean_ctor_set(x_18, 1, x_24);
lean_ctor_set(x_18, 0, x_25);
return x_18;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_26 = lean_ctor_get(x_18, 1);
lean_inc(x_26);
lean_dec(x_18);
x_27 = l_PersistentArray_Stats_toString___closed__4;
x_28 = lean_string_append(x_26, x_27);
x_29 = lean_string_append(x_28, x_6);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
else
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_18);
if (x_32 == 0)
{
return x_18;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_18, 0);
x_34 = lean_ctor_get(x_18, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_18);
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
lean_dec(x_2);
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_16);
if (x_36 == 0)
{
return x_16;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_16, 0);
x_38 = lean_ctor_get(x_16, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_16);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_40 = l_String_splitAux___main___closed__1;
x_41 = lean_string_append(x_11, x_40);
x_42 = lean_string_append(x_41, x_6);
x_43 = l_Lean_IR_EmitC_emitFnBody___main___closed__1;
lean_inc(x_2);
lean_inc(x_1);
x_44 = l_Lean_IR_EmitC_emitBlock___main(x_43, x_1, x_2, x_42);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
x_46 = l_Lean_IR_EmitC_emitJPs___main(x_43, x_1, x_2, x_45);
if (lean_obj_tag(x_46) == 0)
{
uint8_t x_47; 
x_47 = !lean_is_exclusive(x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_48 = lean_ctor_get(x_46, 1);
x_49 = lean_ctor_get(x_46, 0);
lean_dec(x_49);
x_50 = l_PersistentArray_Stats_toString___closed__4;
x_51 = lean_string_append(x_48, x_50);
x_52 = lean_string_append(x_51, x_6);
x_53 = lean_box(0);
lean_ctor_set(x_46, 1, x_52);
lean_ctor_set(x_46, 0, x_53);
return x_46;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_54 = lean_ctor_get(x_46, 1);
lean_inc(x_54);
lean_dec(x_46);
x_55 = l_PersistentArray_Stats_toString___closed__4;
x_56 = lean_string_append(x_54, x_55);
x_57 = lean_string_append(x_56, x_6);
x_58 = lean_box(0);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_57);
return x_59;
}
}
else
{
uint8_t x_60; 
x_60 = !lean_is_exclusive(x_46);
if (x_60 == 0)
{
return x_46;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_46, 0);
x_62 = lean_ctor_get(x_46, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_46);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
else
{
uint8_t x_64; 
lean_dec(x_2);
lean_dec(x_1);
x_64 = !lean_is_exclusive(x_44);
if (x_64 == 0)
{
return x_44;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_44, 0);
x_66 = lean_ctor_get(x_44, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_44);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
}
}
lean_object* l_Lean_IR_EmitC_emitFnBody(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_EmitC_emitFnBody___main(x_1, x_2, x_3);
return x_4;
}
}
lean_object* _init_l_Nat_forMAux___main___at_Lean_IR_EmitC_emitDeclAux___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("lean_object* ");
return x_1;
}
}
lean_object* _init_l_Nat_forMAux___main___at_Lean_IR_EmitC_emitDeclAux___spec__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" = _args[");
return x_1;
}
}
lean_object* _init_l_Nat_forMAux___main___at_Lean_IR_EmitC_emitDeclAux___spec__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("];");
return x_1;
}
}
lean_object* l_Nat_forMAux___main___at_Lean_IR_EmitC_emitDeclAux___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
x_12 = l_Lean_IR_paramInh;
x_13 = lean_array_get(x_12, x_1, x_11);
x_14 = l_Nat_forMAux___main___at_Lean_IR_EmitC_emitDeclAux___spec__1___closed__1;
x_15 = lean_string_append(x_5, x_14);
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_16);
lean_dec(x_13);
x_17 = l_Nat_repr(x_16);
x_18 = l_Lean_IR_VarId_HasToString___closed__1;
x_19 = lean_string_append(x_18, x_17);
lean_dec(x_17);
x_20 = lean_string_append(x_15, x_19);
lean_dec(x_19);
x_21 = l_Nat_forMAux___main___at_Lean_IR_EmitC_emitDeclAux___spec__1___closed__2;
x_22 = lean_string_append(x_20, x_21);
x_23 = l_Nat_repr(x_11);
x_24 = lean_string_append(x_22, x_23);
lean_dec(x_23);
x_25 = l_Nat_forMAux___main___at_Lean_IR_EmitC_emitDeclAux___spec__1___closed__3;
x_26 = lean_string_append(x_24, x_25);
x_27 = l_IO_println___rarg___closed__1;
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
lean_object* l_Nat_forMAux___main___at_Lean_IR_EmitC_emitDeclAux___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_13 = l_Lean_IR_paramInh;
x_14 = lean_array_get(x_13, x_1, x_11);
lean_dec(x_11);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
x_16 = l_Lean_IR_EmitC_toCType(x_15);
lean_dec(x_15);
x_17 = lean_string_append(x_5, x_16);
lean_dec(x_16);
x_18 = l_String_Iterator_HasRepr___closed__2;
x_19 = lean_string_append(x_17, x_18);
x_20 = lean_ctor_get(x_14, 0);
lean_inc(x_20);
lean_dec(x_14);
x_21 = l_Nat_repr(x_20);
x_22 = l_Lean_IR_VarId_HasToString___closed__1;
x_23 = lean_string_append(x_22, x_21);
lean_dec(x_21);
x_24 = lean_string_append(x_19, x_23);
lean_dec(x_23);
x_3 = x_9;
x_5 = x_24;
goto _start;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_26 = l_List_reprAux___main___rarg___closed__1;
x_27 = lean_string_append(x_5, x_26);
x_28 = l_Lean_IR_paramInh;
x_29 = lean_array_get(x_28, x_1, x_11);
lean_dec(x_11);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
x_31 = l_Lean_IR_EmitC_toCType(x_30);
lean_dec(x_30);
x_32 = lean_string_append(x_27, x_31);
lean_dec(x_31);
x_33 = l_String_Iterator_HasRepr___closed__2;
x_34 = lean_string_append(x_32, x_33);
x_35 = lean_ctor_get(x_29, 0);
lean_inc(x_35);
lean_dec(x_29);
x_36 = l_Nat_repr(x_35);
x_37 = l_Lean_IR_VarId_HasToString___closed__1;
x_38 = lean_string_append(x_37, x_36);
lean_dec(x_36);
x_39 = lean_string_append(x_34, x_38);
lean_dec(x_38);
x_3 = x_9;
x_5 = x_39;
goto _start;
}
}
else
{
lean_object* x_41; lean_object* x_42; 
lean_dec(x_3);
x_41 = lean_box(0);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_5);
return x_42;
}
}
}
lean_object* _init_l_Lean_IR_EmitC_emitDeclAux___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" {");
return x_1;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitDeclAux___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_start:");
return x_1;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitDeclAux___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("lean_object** _args");
return x_1;
}
}
lean_object* l_Lean_IR_EmitC_emitDeclAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_IR_EmitC_getEnv(x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_12; uint8_t x_13; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_1);
x_8 = l_Lean_IR_mkVarJPMaps(x_1);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = l_Lean_IR_Decl_name(x_1);
lean_inc(x_10);
x_11 = l_Lean_hasInitAttr(x_6, x_10);
x_12 = 1;
x_13 = l_Bool_DecidableEq(x_11, x_12);
if (x_13 == 0)
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
lean_free_object(x_4);
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 2);
lean_inc(x_16);
x_17 = lean_ctor_get(x_1, 3);
lean_inc(x_17);
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_2);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_2, 0);
x_20 = lean_ctor_get(x_2, 1);
x_21 = lean_ctor_get(x_2, 2);
lean_dec(x_21);
lean_inc(x_9);
lean_inc(x_20);
lean_inc(x_19);
lean_ctor_set(x_2, 2, x_9);
lean_inc(x_14);
x_22 = l_Lean_IR_EmitC_toCName(x_14, x_2, x_7);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_89; uint8_t x_90; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_IR_EmitC_toCType(x_16);
lean_dec(x_16);
x_26 = lean_string_append(x_24, x_25);
lean_dec(x_25);
x_27 = l_String_Iterator_HasRepr___closed__2;
x_28 = lean_string_append(x_26, x_27);
x_29 = lean_array_get_size(x_15);
x_89 = lean_unsigned_to_nat(0u);
x_90 = lean_nat_dec_lt(x_89, x_29);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_91 = l_Lean_IR_EmitC_toCInitName___closed__1;
x_92 = lean_string_append(x_91, x_23);
lean_dec(x_23);
x_93 = l_Unit_HasRepr___closed__1;
x_94 = lean_string_append(x_92, x_93);
x_95 = lean_string_append(x_28, x_94);
lean_dec(x_94);
x_30 = x_95;
goto block_88;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; lean_object* x_110; uint8_t x_111; 
x_96 = lean_string_append(x_28, x_23);
lean_dec(x_23);
x_97 = l_Prod_HasRepr___rarg___closed__1;
x_98 = lean_string_append(x_96, x_97);
x_110 = l_Lean_closureMaxArgs;
x_111 = lean_nat_dec_lt(x_110, x_29);
if (x_111 == 0)
{
uint8_t x_112; 
x_112 = 0;
x_99 = x_112;
goto block_109;
}
else
{
uint8_t x_113; 
x_113 = l_Lean_IR_ExplicitBoxing_isBoxedName(x_10);
x_99 = x_113;
goto block_109;
}
block_109:
{
uint8_t x_100; 
x_100 = l_Bool_DecidableEq(x_99, x_12);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
lean_inc(x_29);
x_101 = l_Nat_forMAux___main___at_Lean_IR_EmitC_emitDeclAux___spec__2(x_15, x_29, x_29, x_2, x_98);
x_102 = lean_ctor_get(x_101, 1);
lean_inc(x_102);
lean_dec(x_101);
x_103 = l_Option_HasRepr___rarg___closed__3;
x_104 = lean_string_append(x_102, x_103);
x_30 = x_104;
goto block_88;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_105 = l_Lean_IR_EmitC_emitDeclAux___closed__3;
x_106 = lean_string_append(x_98, x_105);
x_107 = l_Option_HasRepr___rarg___closed__3;
x_108 = lean_string_append(x_106, x_107);
x_30 = x_108;
goto block_88;
}
}
}
block_88:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_84; uint8_t x_85; 
x_31 = l_Lean_IR_EmitC_emitDeclAux___closed__1;
x_32 = lean_string_append(x_30, x_31);
x_33 = l_IO_println___rarg___closed__1;
x_34 = lean_string_append(x_32, x_33);
x_84 = l_Lean_closureMaxArgs;
x_85 = lean_nat_dec_lt(x_84, x_29);
if (x_85 == 0)
{
uint8_t x_86; 
lean_dec(x_10);
x_86 = 0;
x_35 = x_86;
goto block_83;
}
else
{
uint8_t x_87; 
x_87 = l_Lean_IR_ExplicitBoxing_isBoxedName(x_10);
lean_dec(x_10);
x_35 = x_87;
goto block_83;
}
block_83:
{
uint8_t x_36; 
x_36 = l_Bool_DecidableEq(x_35, x_12);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_29);
lean_dec(x_2);
x_37 = l_Lean_IR_EmitC_emitDeclAux___closed__2;
x_38 = lean_string_append(x_34, x_37);
x_39 = lean_string_append(x_38, x_33);
x_40 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_40, 0, x_19);
lean_ctor_set(x_40, 1, x_20);
lean_ctor_set(x_40, 2, x_9);
lean_ctor_set(x_40, 3, x_14);
lean_ctor_set(x_40, 4, x_15);
x_41 = l_Lean_IR_EmitC_emitFnBody___main(x_17, x_40, x_39);
if (lean_obj_tag(x_41) == 0)
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_43 = lean_ctor_get(x_41, 1);
x_44 = lean_ctor_get(x_41, 0);
lean_dec(x_44);
x_45 = l_PersistentArray_Stats_toString___closed__4;
x_46 = lean_string_append(x_43, x_45);
x_47 = lean_string_append(x_46, x_33);
x_48 = lean_box(0);
lean_ctor_set(x_41, 1, x_47);
lean_ctor_set(x_41, 0, x_48);
return x_41;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_49 = lean_ctor_get(x_41, 1);
lean_inc(x_49);
lean_dec(x_41);
x_50 = l_PersistentArray_Stats_toString___closed__4;
x_51 = lean_string_append(x_49, x_50);
x_52 = lean_string_append(x_51, x_33);
x_53 = lean_box(0);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_52);
return x_54;
}
}
else
{
uint8_t x_55; 
x_55 = !lean_is_exclusive(x_41);
if (x_55 == 0)
{
return x_41;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_41, 0);
x_57 = lean_ctor_get(x_41, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_41);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_inc(x_29);
x_59 = l_Nat_forMAux___main___at_Lean_IR_EmitC_emitDeclAux___spec__1(x_15, x_29, x_29, x_2, x_34);
lean_dec(x_2);
lean_dec(x_29);
x_60 = lean_ctor_get(x_59, 1);
lean_inc(x_60);
lean_dec(x_59);
x_61 = l_Lean_IR_EmitC_emitDeclAux___closed__2;
x_62 = lean_string_append(x_60, x_61);
x_63 = lean_string_append(x_62, x_33);
x_64 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_64, 0, x_19);
lean_ctor_set(x_64, 1, x_20);
lean_ctor_set(x_64, 2, x_9);
lean_ctor_set(x_64, 3, x_14);
lean_ctor_set(x_64, 4, x_15);
x_65 = l_Lean_IR_EmitC_emitFnBody___main(x_17, x_64, x_63);
if (lean_obj_tag(x_65) == 0)
{
uint8_t x_66; 
x_66 = !lean_is_exclusive(x_65);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_67 = lean_ctor_get(x_65, 1);
x_68 = lean_ctor_get(x_65, 0);
lean_dec(x_68);
x_69 = l_PersistentArray_Stats_toString___closed__4;
x_70 = lean_string_append(x_67, x_69);
x_71 = lean_string_append(x_70, x_33);
x_72 = lean_box(0);
lean_ctor_set(x_65, 1, x_71);
lean_ctor_set(x_65, 0, x_72);
return x_65;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_73 = lean_ctor_get(x_65, 1);
lean_inc(x_73);
lean_dec(x_65);
x_74 = l_PersistentArray_Stats_toString___closed__4;
x_75 = lean_string_append(x_73, x_74);
x_76 = lean_string_append(x_75, x_33);
x_77 = lean_box(0);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_76);
return x_78;
}
}
else
{
uint8_t x_79; 
x_79 = !lean_is_exclusive(x_65);
if (x_79 == 0)
{
return x_65;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_65, 0);
x_81 = lean_ctor_get(x_65, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_65);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
}
}
}
}
else
{
uint8_t x_114; 
lean_dec(x_2);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
x_114 = !lean_is_exclusive(x_22);
if (x_114 == 0)
{
return x_22;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_22, 0);
x_116 = lean_ctor_get(x_22, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_22);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
return x_117;
}
}
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_118 = lean_ctor_get(x_2, 0);
x_119 = lean_ctor_get(x_2, 1);
x_120 = lean_ctor_get(x_2, 3);
x_121 = lean_ctor_get(x_2, 4);
lean_inc(x_121);
lean_inc(x_120);
lean_inc(x_119);
lean_inc(x_118);
lean_dec(x_2);
lean_inc(x_9);
lean_inc(x_119);
lean_inc(x_118);
x_122 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_122, 0, x_118);
lean_ctor_set(x_122, 1, x_119);
lean_ctor_set(x_122, 2, x_9);
lean_ctor_set(x_122, 3, x_120);
lean_ctor_set(x_122, 4, x_121);
lean_inc(x_14);
x_123 = l_Lean_IR_EmitC_toCName(x_14, x_122, x_7);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_178; uint8_t x_179; 
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_123, 1);
lean_inc(x_125);
lean_dec(x_123);
x_126 = l_Lean_IR_EmitC_toCType(x_16);
lean_dec(x_16);
x_127 = lean_string_append(x_125, x_126);
lean_dec(x_126);
x_128 = l_String_Iterator_HasRepr___closed__2;
x_129 = lean_string_append(x_127, x_128);
x_130 = lean_array_get_size(x_15);
x_178 = lean_unsigned_to_nat(0u);
x_179 = lean_nat_dec_lt(x_178, x_130);
if (x_179 == 0)
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_180 = l_Lean_IR_EmitC_toCInitName___closed__1;
x_181 = lean_string_append(x_180, x_124);
lean_dec(x_124);
x_182 = l_Unit_HasRepr___closed__1;
x_183 = lean_string_append(x_181, x_182);
x_184 = lean_string_append(x_129, x_183);
lean_dec(x_183);
x_131 = x_184;
goto block_177;
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; uint8_t x_188; lean_object* x_199; uint8_t x_200; 
x_185 = lean_string_append(x_129, x_124);
lean_dec(x_124);
x_186 = l_Prod_HasRepr___rarg___closed__1;
x_187 = lean_string_append(x_185, x_186);
x_199 = l_Lean_closureMaxArgs;
x_200 = lean_nat_dec_lt(x_199, x_130);
if (x_200 == 0)
{
uint8_t x_201; 
x_201 = 0;
x_188 = x_201;
goto block_198;
}
else
{
uint8_t x_202; 
x_202 = l_Lean_IR_ExplicitBoxing_isBoxedName(x_10);
x_188 = x_202;
goto block_198;
}
block_198:
{
uint8_t x_189; 
x_189 = l_Bool_DecidableEq(x_188, x_12);
if (x_189 == 0)
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
lean_inc(x_130);
x_190 = l_Nat_forMAux___main___at_Lean_IR_EmitC_emitDeclAux___spec__2(x_15, x_130, x_130, x_122, x_187);
x_191 = lean_ctor_get(x_190, 1);
lean_inc(x_191);
lean_dec(x_190);
x_192 = l_Option_HasRepr___rarg___closed__3;
x_193 = lean_string_append(x_191, x_192);
x_131 = x_193;
goto block_177;
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_194 = l_Lean_IR_EmitC_emitDeclAux___closed__3;
x_195 = lean_string_append(x_187, x_194);
x_196 = l_Option_HasRepr___rarg___closed__3;
x_197 = lean_string_append(x_195, x_196);
x_131 = x_197;
goto block_177;
}
}
}
block_177:
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; uint8_t x_136; lean_object* x_173; uint8_t x_174; 
x_132 = l_Lean_IR_EmitC_emitDeclAux___closed__1;
x_133 = lean_string_append(x_131, x_132);
x_134 = l_IO_println___rarg___closed__1;
x_135 = lean_string_append(x_133, x_134);
x_173 = l_Lean_closureMaxArgs;
x_174 = lean_nat_dec_lt(x_173, x_130);
if (x_174 == 0)
{
uint8_t x_175; 
lean_dec(x_10);
x_175 = 0;
x_136 = x_175;
goto block_172;
}
else
{
uint8_t x_176; 
x_176 = l_Lean_IR_ExplicitBoxing_isBoxedName(x_10);
lean_dec(x_10);
x_136 = x_176;
goto block_172;
}
block_172:
{
uint8_t x_137; 
x_137 = l_Bool_DecidableEq(x_136, x_12);
if (x_137 == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
lean_dec(x_130);
lean_dec(x_122);
x_138 = l_Lean_IR_EmitC_emitDeclAux___closed__2;
x_139 = lean_string_append(x_135, x_138);
x_140 = lean_string_append(x_139, x_134);
x_141 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_141, 0, x_118);
lean_ctor_set(x_141, 1, x_119);
lean_ctor_set(x_141, 2, x_9);
lean_ctor_set(x_141, 3, x_14);
lean_ctor_set(x_141, 4, x_15);
x_142 = l_Lean_IR_EmitC_emitFnBody___main(x_17, x_141, x_140);
if (lean_obj_tag(x_142) == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_143 = lean_ctor_get(x_142, 1);
lean_inc(x_143);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 lean_ctor_release(x_142, 1);
 x_144 = x_142;
} else {
 lean_dec_ref(x_142);
 x_144 = lean_box(0);
}
x_145 = l_PersistentArray_Stats_toString___closed__4;
x_146 = lean_string_append(x_143, x_145);
x_147 = lean_string_append(x_146, x_134);
x_148 = lean_box(0);
if (lean_is_scalar(x_144)) {
 x_149 = lean_alloc_ctor(0, 2, 0);
} else {
 x_149 = x_144;
}
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set(x_149, 1, x_147);
return x_149;
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_150 = lean_ctor_get(x_142, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_142, 1);
lean_inc(x_151);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 lean_ctor_release(x_142, 1);
 x_152 = x_142;
} else {
 lean_dec_ref(x_142);
 x_152 = lean_box(0);
}
if (lean_is_scalar(x_152)) {
 x_153 = lean_alloc_ctor(1, 2, 0);
} else {
 x_153 = x_152;
}
lean_ctor_set(x_153, 0, x_150);
lean_ctor_set(x_153, 1, x_151);
return x_153;
}
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
lean_inc(x_130);
x_154 = l_Nat_forMAux___main___at_Lean_IR_EmitC_emitDeclAux___spec__1(x_15, x_130, x_130, x_122, x_135);
lean_dec(x_122);
lean_dec(x_130);
x_155 = lean_ctor_get(x_154, 1);
lean_inc(x_155);
lean_dec(x_154);
x_156 = l_Lean_IR_EmitC_emitDeclAux___closed__2;
x_157 = lean_string_append(x_155, x_156);
x_158 = lean_string_append(x_157, x_134);
x_159 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_159, 0, x_118);
lean_ctor_set(x_159, 1, x_119);
lean_ctor_set(x_159, 2, x_9);
lean_ctor_set(x_159, 3, x_14);
lean_ctor_set(x_159, 4, x_15);
x_160 = l_Lean_IR_EmitC_emitFnBody___main(x_17, x_159, x_158);
if (lean_obj_tag(x_160) == 0)
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_161 = lean_ctor_get(x_160, 1);
lean_inc(x_161);
if (lean_is_exclusive(x_160)) {
 lean_ctor_release(x_160, 0);
 lean_ctor_release(x_160, 1);
 x_162 = x_160;
} else {
 lean_dec_ref(x_160);
 x_162 = lean_box(0);
}
x_163 = l_PersistentArray_Stats_toString___closed__4;
x_164 = lean_string_append(x_161, x_163);
x_165 = lean_string_append(x_164, x_134);
x_166 = lean_box(0);
if (lean_is_scalar(x_162)) {
 x_167 = lean_alloc_ctor(0, 2, 0);
} else {
 x_167 = x_162;
}
lean_ctor_set(x_167, 0, x_166);
lean_ctor_set(x_167, 1, x_165);
return x_167;
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_168 = lean_ctor_get(x_160, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_160, 1);
lean_inc(x_169);
if (lean_is_exclusive(x_160)) {
 lean_ctor_release(x_160, 0);
 lean_ctor_release(x_160, 1);
 x_170 = x_160;
} else {
 lean_dec_ref(x_160);
 x_170 = lean_box(0);
}
if (lean_is_scalar(x_170)) {
 x_171 = lean_alloc_ctor(1, 2, 0);
} else {
 x_171 = x_170;
}
lean_ctor_set(x_171, 0, x_168);
lean_ctor_set(x_171, 1, x_169);
return x_171;
}
}
}
}
}
else
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; 
lean_dec(x_122);
lean_dec(x_119);
lean_dec(x_118);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
x_203 = lean_ctor_get(x_123, 0);
lean_inc(x_203);
x_204 = lean_ctor_get(x_123, 1);
lean_inc(x_204);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 lean_ctor_release(x_123, 1);
 x_205 = x_123;
} else {
 lean_dec_ref(x_123);
 x_205 = lean_box(0);
}
if (lean_is_scalar(x_205)) {
 x_206 = lean_alloc_ctor(1, 2, 0);
} else {
 x_206 = x_205;
}
lean_ctor_set(x_206, 0, x_203);
lean_ctor_set(x_206, 1, x_204);
return x_206;
}
}
}
else
{
lean_object* x_207; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_2);
lean_dec(x_1);
x_207 = lean_box(0);
lean_ctor_set(x_4, 0, x_207);
return x_4;
}
}
else
{
lean_object* x_208; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_2);
lean_dec(x_1);
x_208 = lean_box(0);
lean_ctor_set(x_4, 0, x_208);
return x_4;
}
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; uint8_t x_214; uint8_t x_215; uint8_t x_216; 
x_209 = lean_ctor_get(x_4, 0);
x_210 = lean_ctor_get(x_4, 1);
lean_inc(x_210);
lean_inc(x_209);
lean_dec(x_4);
lean_inc(x_1);
x_211 = l_Lean_IR_mkVarJPMaps(x_1);
x_212 = lean_ctor_get(x_211, 1);
lean_inc(x_212);
lean_dec(x_211);
x_213 = l_Lean_IR_Decl_name(x_1);
lean_inc(x_213);
x_214 = l_Lean_hasInitAttr(x_209, x_213);
x_215 = 1;
x_216 = l_Bool_DecidableEq(x_214, x_215);
if (x_216 == 0)
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; 
x_217 = lean_ctor_get(x_1, 0);
lean_inc(x_217);
x_218 = lean_ctor_get(x_1, 1);
lean_inc(x_218);
x_219 = lean_ctor_get(x_1, 2);
lean_inc(x_219);
x_220 = lean_ctor_get(x_1, 3);
lean_inc(x_220);
lean_dec(x_1);
x_221 = lean_ctor_get(x_2, 0);
lean_inc(x_221);
x_222 = lean_ctor_get(x_2, 1);
lean_inc(x_222);
x_223 = lean_ctor_get(x_2, 3);
lean_inc(x_223);
x_224 = lean_ctor_get(x_2, 4);
lean_inc(x_224);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 lean_ctor_release(x_2, 3);
 lean_ctor_release(x_2, 4);
 x_225 = x_2;
} else {
 lean_dec_ref(x_2);
 x_225 = lean_box(0);
}
lean_inc(x_212);
lean_inc(x_222);
lean_inc(x_221);
if (lean_is_scalar(x_225)) {
 x_226 = lean_alloc_ctor(0, 5, 0);
} else {
 x_226 = x_225;
}
lean_ctor_set(x_226, 0, x_221);
lean_ctor_set(x_226, 1, x_222);
lean_ctor_set(x_226, 2, x_212);
lean_ctor_set(x_226, 3, x_223);
lean_ctor_set(x_226, 4, x_224);
lean_inc(x_217);
x_227 = l_Lean_IR_EmitC_toCName(x_217, x_226, x_210);
if (lean_obj_tag(x_227) == 0)
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_282; uint8_t x_283; 
x_228 = lean_ctor_get(x_227, 0);
lean_inc(x_228);
x_229 = lean_ctor_get(x_227, 1);
lean_inc(x_229);
lean_dec(x_227);
x_230 = l_Lean_IR_EmitC_toCType(x_219);
lean_dec(x_219);
x_231 = lean_string_append(x_229, x_230);
lean_dec(x_230);
x_232 = l_String_Iterator_HasRepr___closed__2;
x_233 = lean_string_append(x_231, x_232);
x_234 = lean_array_get_size(x_218);
x_282 = lean_unsigned_to_nat(0u);
x_283 = lean_nat_dec_lt(x_282, x_234);
if (x_283 == 0)
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; 
x_284 = l_Lean_IR_EmitC_toCInitName___closed__1;
x_285 = lean_string_append(x_284, x_228);
lean_dec(x_228);
x_286 = l_Unit_HasRepr___closed__1;
x_287 = lean_string_append(x_285, x_286);
x_288 = lean_string_append(x_233, x_287);
lean_dec(x_287);
x_235 = x_288;
goto block_281;
}
else
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; uint8_t x_292; lean_object* x_303; uint8_t x_304; 
x_289 = lean_string_append(x_233, x_228);
lean_dec(x_228);
x_290 = l_Prod_HasRepr___rarg___closed__1;
x_291 = lean_string_append(x_289, x_290);
x_303 = l_Lean_closureMaxArgs;
x_304 = lean_nat_dec_lt(x_303, x_234);
if (x_304 == 0)
{
uint8_t x_305; 
x_305 = 0;
x_292 = x_305;
goto block_302;
}
else
{
uint8_t x_306; 
x_306 = l_Lean_IR_ExplicitBoxing_isBoxedName(x_213);
x_292 = x_306;
goto block_302;
}
block_302:
{
uint8_t x_293; 
x_293 = l_Bool_DecidableEq(x_292, x_215);
if (x_293 == 0)
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; 
lean_inc(x_234);
x_294 = l_Nat_forMAux___main___at_Lean_IR_EmitC_emitDeclAux___spec__2(x_218, x_234, x_234, x_226, x_291);
x_295 = lean_ctor_get(x_294, 1);
lean_inc(x_295);
lean_dec(x_294);
x_296 = l_Option_HasRepr___rarg___closed__3;
x_297 = lean_string_append(x_295, x_296);
x_235 = x_297;
goto block_281;
}
else
{
lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; 
x_298 = l_Lean_IR_EmitC_emitDeclAux___closed__3;
x_299 = lean_string_append(x_291, x_298);
x_300 = l_Option_HasRepr___rarg___closed__3;
x_301 = lean_string_append(x_299, x_300);
x_235 = x_301;
goto block_281;
}
}
}
block_281:
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; uint8_t x_240; lean_object* x_277; uint8_t x_278; 
x_236 = l_Lean_IR_EmitC_emitDeclAux___closed__1;
x_237 = lean_string_append(x_235, x_236);
x_238 = l_IO_println___rarg___closed__1;
x_239 = lean_string_append(x_237, x_238);
x_277 = l_Lean_closureMaxArgs;
x_278 = lean_nat_dec_lt(x_277, x_234);
if (x_278 == 0)
{
uint8_t x_279; 
lean_dec(x_213);
x_279 = 0;
x_240 = x_279;
goto block_276;
}
else
{
uint8_t x_280; 
x_280 = l_Lean_IR_ExplicitBoxing_isBoxedName(x_213);
lean_dec(x_213);
x_240 = x_280;
goto block_276;
}
block_276:
{
uint8_t x_241; 
x_241 = l_Bool_DecidableEq(x_240, x_215);
if (x_241 == 0)
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; 
lean_dec(x_234);
lean_dec(x_226);
x_242 = l_Lean_IR_EmitC_emitDeclAux___closed__2;
x_243 = lean_string_append(x_239, x_242);
x_244 = lean_string_append(x_243, x_238);
x_245 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_245, 0, x_221);
lean_ctor_set(x_245, 1, x_222);
lean_ctor_set(x_245, 2, x_212);
lean_ctor_set(x_245, 3, x_217);
lean_ctor_set(x_245, 4, x_218);
x_246 = l_Lean_IR_EmitC_emitFnBody___main(x_220, x_245, x_244);
if (lean_obj_tag(x_246) == 0)
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; 
x_247 = lean_ctor_get(x_246, 1);
lean_inc(x_247);
if (lean_is_exclusive(x_246)) {
 lean_ctor_release(x_246, 0);
 lean_ctor_release(x_246, 1);
 x_248 = x_246;
} else {
 lean_dec_ref(x_246);
 x_248 = lean_box(0);
}
x_249 = l_PersistentArray_Stats_toString___closed__4;
x_250 = lean_string_append(x_247, x_249);
x_251 = lean_string_append(x_250, x_238);
x_252 = lean_box(0);
if (lean_is_scalar(x_248)) {
 x_253 = lean_alloc_ctor(0, 2, 0);
} else {
 x_253 = x_248;
}
lean_ctor_set(x_253, 0, x_252);
lean_ctor_set(x_253, 1, x_251);
return x_253;
}
else
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; 
x_254 = lean_ctor_get(x_246, 0);
lean_inc(x_254);
x_255 = lean_ctor_get(x_246, 1);
lean_inc(x_255);
if (lean_is_exclusive(x_246)) {
 lean_ctor_release(x_246, 0);
 lean_ctor_release(x_246, 1);
 x_256 = x_246;
} else {
 lean_dec_ref(x_246);
 x_256 = lean_box(0);
}
if (lean_is_scalar(x_256)) {
 x_257 = lean_alloc_ctor(1, 2, 0);
} else {
 x_257 = x_256;
}
lean_ctor_set(x_257, 0, x_254);
lean_ctor_set(x_257, 1, x_255);
return x_257;
}
}
else
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; 
lean_inc(x_234);
x_258 = l_Nat_forMAux___main___at_Lean_IR_EmitC_emitDeclAux___spec__1(x_218, x_234, x_234, x_226, x_239);
lean_dec(x_226);
lean_dec(x_234);
x_259 = lean_ctor_get(x_258, 1);
lean_inc(x_259);
lean_dec(x_258);
x_260 = l_Lean_IR_EmitC_emitDeclAux___closed__2;
x_261 = lean_string_append(x_259, x_260);
x_262 = lean_string_append(x_261, x_238);
x_263 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_263, 0, x_221);
lean_ctor_set(x_263, 1, x_222);
lean_ctor_set(x_263, 2, x_212);
lean_ctor_set(x_263, 3, x_217);
lean_ctor_set(x_263, 4, x_218);
x_264 = l_Lean_IR_EmitC_emitFnBody___main(x_220, x_263, x_262);
if (lean_obj_tag(x_264) == 0)
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; 
x_265 = lean_ctor_get(x_264, 1);
lean_inc(x_265);
if (lean_is_exclusive(x_264)) {
 lean_ctor_release(x_264, 0);
 lean_ctor_release(x_264, 1);
 x_266 = x_264;
} else {
 lean_dec_ref(x_264);
 x_266 = lean_box(0);
}
x_267 = l_PersistentArray_Stats_toString___closed__4;
x_268 = lean_string_append(x_265, x_267);
x_269 = lean_string_append(x_268, x_238);
x_270 = lean_box(0);
if (lean_is_scalar(x_266)) {
 x_271 = lean_alloc_ctor(0, 2, 0);
} else {
 x_271 = x_266;
}
lean_ctor_set(x_271, 0, x_270);
lean_ctor_set(x_271, 1, x_269);
return x_271;
}
else
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; 
x_272 = lean_ctor_get(x_264, 0);
lean_inc(x_272);
x_273 = lean_ctor_get(x_264, 1);
lean_inc(x_273);
if (lean_is_exclusive(x_264)) {
 lean_ctor_release(x_264, 0);
 lean_ctor_release(x_264, 1);
 x_274 = x_264;
} else {
 lean_dec_ref(x_264);
 x_274 = lean_box(0);
}
if (lean_is_scalar(x_274)) {
 x_275 = lean_alloc_ctor(1, 2, 0);
} else {
 x_275 = x_274;
}
lean_ctor_set(x_275, 0, x_272);
lean_ctor_set(x_275, 1, x_273);
return x_275;
}
}
}
}
}
else
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; 
lean_dec(x_226);
lean_dec(x_222);
lean_dec(x_221);
lean_dec(x_220);
lean_dec(x_219);
lean_dec(x_218);
lean_dec(x_217);
lean_dec(x_213);
lean_dec(x_212);
x_307 = lean_ctor_get(x_227, 0);
lean_inc(x_307);
x_308 = lean_ctor_get(x_227, 1);
lean_inc(x_308);
if (lean_is_exclusive(x_227)) {
 lean_ctor_release(x_227, 0);
 lean_ctor_release(x_227, 1);
 x_309 = x_227;
} else {
 lean_dec_ref(x_227);
 x_309 = lean_box(0);
}
if (lean_is_scalar(x_309)) {
 x_310 = lean_alloc_ctor(1, 2, 0);
} else {
 x_310 = x_309;
}
lean_ctor_set(x_310, 0, x_307);
lean_ctor_set(x_310, 1, x_308);
return x_310;
}
}
else
{
lean_object* x_311; lean_object* x_312; 
lean_dec(x_213);
lean_dec(x_212);
lean_dec(x_2);
lean_dec(x_1);
x_311 = lean_box(0);
x_312 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_312, 0, x_311);
lean_ctor_set(x_312, 1, x_210);
return x_312;
}
}
else
{
lean_object* x_313; lean_object* x_314; 
lean_dec(x_213);
lean_dec(x_212);
lean_dec(x_2);
lean_dec(x_1);
x_313 = lean_box(0);
x_314 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_314, 0, x_313);
lean_ctor_set(x_314, 1, x_210);
return x_314;
}
}
}
}
lean_object* l_Nat_forMAux___main___at_Lean_IR_EmitC_emitDeclAux___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Nat_forMAux___main___at_Lean_IR_EmitC_emitDeclAux___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Nat_forMAux___main___at_Lean_IR_EmitC_emitDeclAux___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Nat_forMAux___main___at_Lean_IR_EmitC_emitDeclAux___spec__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitDecl___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("\ncompiling:\n");
return x_1;
}
}
lean_object* l_Lean_IR_EmitC_emitDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = l_Lean_IR_EmitC_emitDecl___closed__1;
x_9 = lean_string_append(x_7, x_8);
x_10 = lean_ir_decl_to_string(x_4);
x_11 = lean_string_append(x_9, x_10);
lean_dec(x_10);
lean_ctor_set(x_5, 0, x_11);
return x_5;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_5, 0);
x_13 = lean_ctor_get(x_5, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_5);
x_14 = l_Lean_IR_EmitC_emitDecl___closed__1;
x_15 = lean_string_append(x_12, x_14);
x_16 = lean_ir_decl_to_string(x_4);
x_17 = lean_string_append(x_15, x_16);
lean_dec(x_16);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_13);
return x_18;
}
}
}
}
lean_object* l_List_forM___main___at_Lean_IR_EmitC_emitFns___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_IR_EmitC_emitFns(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = l_Lean_IR_EmitC_getEnv(x_1, x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = l_Lean_IR_declMapExt;
x_7 = l_Lean_SimplePersistentEnvExtension_getEntries___rarg(x_6, x_4);
lean_dec(x_4);
x_8 = l_List_reverse___rarg(x_7);
x_9 = l_List_forM___main___at_Lean_IR_EmitC_emitFns___spec__1(x_8, x_1, x_5);
return x_9;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitMarkPersistent___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("lean_mark_persistent(");
return x_1;
}
}
lean_object* l_Lean_IR_EmitC_emitMarkPersistent(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; uint8_t x_7; uint8_t x_8; 
x_5 = l_Lean_IR_Decl_resultType(x_1);
x_6 = l_Lean_IR_IRType_isObj(x_5);
lean_dec(x_5);
x_7 = 1;
x_8 = l_Bool_DecidableEq(x_6, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_2);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_4);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = l_Lean_IR_EmitC_emitMarkPersistent___closed__1;
x_12 = lean_string_append(x_4, x_11);
x_13 = l_Lean_IR_EmitC_emitCName(x_2, x_3, x_12);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_ctor_get(x_13, 1);
x_16 = lean_ctor_get(x_13, 0);
lean_dec(x_16);
x_17 = l_Lean_IR_EmitC_emitInc___closed__1;
x_18 = lean_string_append(x_15, x_17);
x_19 = l_IO_println___rarg___closed__1;
x_20 = lean_string_append(x_18, x_19);
x_21 = lean_box(0);
lean_ctor_set(x_13, 1, x_20);
lean_ctor_set(x_13, 0, x_21);
return x_13;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_22 = lean_ctor_get(x_13, 1);
lean_inc(x_22);
lean_dec(x_13);
x_23 = l_Lean_IR_EmitC_emitInc___closed__1;
x_24 = lean_string_append(x_22, x_23);
x_25 = l_IO_println___rarg___closed__1;
x_26 = lean_string_append(x_24, x_25);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
else
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_13);
if (x_29 == 0)
{
return x_13;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_13, 0);
x_31 = lean_ctor_get(x_13, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_13);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
}
lean_object* l_Lean_IR_EmitC_emitMarkPersistent___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_EmitC_emitMarkPersistent(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitDeclInit___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("();");
return x_1;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitDeclInit___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("if (lean_io_result_is_error(res)) return res;");
return x_1;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitDeclInit___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" = lean_io_result_get_value(res);");
return x_1;
}
}
lean_object* l_Lean_IR_EmitC_emitDeclInit(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_IR_EmitC_getEnv(x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_10; uint8_t x_11; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = l_Lean_IR_Decl_name(x_1);
lean_inc(x_8);
x_9 = l_Lean_isIOUnitInitFn(x_6, x_8);
x_10 = 1;
x_11 = l_Bool_DecidableEq(x_9, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_16; 
x_12 = l_Lean_IR_Decl_params(x_1);
x_13 = lean_array_get_size(x_12);
lean_dec(x_12);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_eq(x_13, x_14);
lean_dec(x_13);
x_16 = l_Bool_DecidableEq(x_15, x_10);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_8);
lean_dec(x_6);
x_17 = lean_box(0);
lean_ctor_set(x_4, 0, x_17);
return x_4;
}
else
{
lean_object* x_18; 
lean_free_object(x_4);
lean_inc(x_8);
x_18 = lean_get_init_fn_name_for(x_6, x_8);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
lean_inc(x_8);
x_19 = l_Lean_IR_EmitC_emitCName(x_8, x_2, x_7);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = l_Nat_forMAux___main___at_Lean_IR_EmitC_emitJmp___spec__1___closed__1;
x_22 = lean_string_append(x_20, x_21);
lean_inc(x_8);
x_23 = l_Lean_IR_EmitC_emitCInitName(x_8, x_2, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = l_Lean_IR_EmitC_emitDeclInit___closed__1;
x_26 = lean_string_append(x_24, x_25);
x_27 = l_IO_println___rarg___closed__1;
x_28 = lean_string_append(x_26, x_27);
x_29 = l_Lean_IR_EmitC_emitMarkPersistent(x_1, x_8, x_2, x_28);
return x_29;
}
else
{
uint8_t x_30; 
lean_dec(x_8);
x_30 = !lean_is_exclusive(x_23);
if (x_30 == 0)
{
return x_23;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_23, 0);
x_32 = lean_ctor_get(x_23, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_23);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
else
{
uint8_t x_34; 
lean_dec(x_8);
x_34 = !lean_is_exclusive(x_19);
if (x_34 == 0)
{
return x_19;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_19, 0);
x_36 = lean_ctor_get(x_19, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_19);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_18, 0);
lean_inc(x_38);
lean_dec(x_18);
x_39 = l_Lean_IR_EmitC_emitMainFn___closed__27;
x_40 = lean_string_append(x_7, x_39);
x_41 = l_Lean_IR_EmitC_emitCName(x_38, x_2, x_40);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
lean_dec(x_41);
x_43 = l_Lean_IR_EmitC_emitMainFn___closed__3;
x_44 = lean_string_append(x_42, x_43);
x_45 = l_IO_println___rarg___closed__1;
x_46 = lean_string_append(x_44, x_45);
x_47 = l_Lean_IR_EmitC_emitDeclInit___closed__2;
x_48 = lean_string_append(x_46, x_47);
x_49 = lean_string_append(x_48, x_45);
lean_inc(x_8);
x_50 = l_Lean_IR_EmitC_emitCName(x_8, x_2, x_49);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_51 = lean_ctor_get(x_50, 1);
lean_inc(x_51);
lean_dec(x_50);
x_52 = l_Lean_IR_EmitC_emitDeclInit___closed__3;
x_53 = lean_string_append(x_51, x_52);
x_54 = lean_string_append(x_53, x_45);
x_55 = l_Lean_IR_EmitC_emitMarkPersistent(x_1, x_8, x_2, x_54);
if (lean_obj_tag(x_55) == 0)
{
uint8_t x_56; 
x_56 = !lean_is_exclusive(x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_57 = lean_ctor_get(x_55, 1);
x_58 = lean_ctor_get(x_55, 0);
lean_dec(x_58);
x_59 = l_Lean_IR_EmitC_emitMainFn___closed__22;
x_60 = lean_string_append(x_57, x_59);
x_61 = lean_string_append(x_60, x_45);
x_62 = lean_box(0);
lean_ctor_set(x_55, 1, x_61);
lean_ctor_set(x_55, 0, x_62);
return x_55;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_63 = lean_ctor_get(x_55, 1);
lean_inc(x_63);
lean_dec(x_55);
x_64 = l_Lean_IR_EmitC_emitMainFn___closed__22;
x_65 = lean_string_append(x_63, x_64);
x_66 = lean_string_append(x_65, x_45);
x_67 = lean_box(0);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_66);
return x_68;
}
}
else
{
uint8_t x_69; 
x_69 = !lean_is_exclusive(x_55);
if (x_69 == 0)
{
return x_55;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_55, 0);
x_71 = lean_ctor_get(x_55, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_55);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
else
{
uint8_t x_73; 
lean_dec(x_8);
x_73 = !lean_is_exclusive(x_50);
if (x_73 == 0)
{
return x_50;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_50, 0);
x_75 = lean_ctor_get(x_50, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_50);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
else
{
uint8_t x_77; 
lean_dec(x_8);
x_77 = !lean_is_exclusive(x_41);
if (x_77 == 0)
{
return x_41;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_41, 0);
x_79 = lean_ctor_get(x_41, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_41);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_free_object(x_4);
lean_dec(x_6);
x_81 = l_Lean_IR_EmitC_emitMainFn___closed__27;
x_82 = lean_string_append(x_7, x_81);
x_83 = l_Lean_IR_EmitC_emitCName(x_8, x_2, x_82);
if (lean_obj_tag(x_83) == 0)
{
uint8_t x_84; 
x_84 = !lean_is_exclusive(x_83);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_85 = lean_ctor_get(x_83, 1);
x_86 = lean_ctor_get(x_83, 0);
lean_dec(x_86);
x_87 = l_Lean_IR_EmitC_emitMainFn___closed__3;
x_88 = lean_string_append(x_85, x_87);
x_89 = l_IO_println___rarg___closed__1;
x_90 = lean_string_append(x_88, x_89);
x_91 = l_Lean_IR_EmitC_emitDeclInit___closed__2;
x_92 = lean_string_append(x_90, x_91);
x_93 = lean_string_append(x_92, x_89);
x_94 = l_Lean_IR_EmitC_emitMainFn___closed__22;
x_95 = lean_string_append(x_93, x_94);
x_96 = lean_string_append(x_95, x_89);
x_97 = lean_box(0);
lean_ctor_set(x_83, 1, x_96);
lean_ctor_set(x_83, 0, x_97);
return x_83;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_98 = lean_ctor_get(x_83, 1);
lean_inc(x_98);
lean_dec(x_83);
x_99 = l_Lean_IR_EmitC_emitMainFn___closed__3;
x_100 = lean_string_append(x_98, x_99);
x_101 = l_IO_println___rarg___closed__1;
x_102 = lean_string_append(x_100, x_101);
x_103 = l_Lean_IR_EmitC_emitDeclInit___closed__2;
x_104 = lean_string_append(x_102, x_103);
x_105 = lean_string_append(x_104, x_101);
x_106 = l_Lean_IR_EmitC_emitMainFn___closed__22;
x_107 = lean_string_append(x_105, x_106);
x_108 = lean_string_append(x_107, x_101);
x_109 = lean_box(0);
x_110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_108);
return x_110;
}
}
else
{
uint8_t x_111; 
x_111 = !lean_is_exclusive(x_83);
if (x_111 == 0)
{
return x_83;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_83, 0);
x_113 = lean_ctor_get(x_83, 1);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_83);
x_114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set(x_114, 1, x_113);
return x_114;
}
}
}
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; uint8_t x_118; uint8_t x_119; uint8_t x_120; 
x_115 = lean_ctor_get(x_4, 0);
x_116 = lean_ctor_get(x_4, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_4);
x_117 = l_Lean_IR_Decl_name(x_1);
lean_inc(x_117);
x_118 = l_Lean_isIOUnitInitFn(x_115, x_117);
x_119 = 1;
x_120 = l_Bool_DecidableEq(x_118, x_119);
if (x_120 == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; uint8_t x_124; uint8_t x_125; 
x_121 = l_Lean_IR_Decl_params(x_1);
x_122 = lean_array_get_size(x_121);
lean_dec(x_121);
x_123 = lean_unsigned_to_nat(0u);
x_124 = lean_nat_dec_eq(x_122, x_123);
lean_dec(x_122);
x_125 = l_Bool_DecidableEq(x_124, x_119);
if (x_125 == 0)
{
lean_object* x_126; lean_object* x_127; 
lean_dec(x_117);
lean_dec(x_115);
x_126 = lean_box(0);
x_127 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_127, 1, x_116);
return x_127;
}
else
{
lean_object* x_128; 
lean_inc(x_117);
x_128 = lean_get_init_fn_name_for(x_115, x_117);
if (lean_obj_tag(x_128) == 0)
{
lean_object* x_129; 
lean_inc(x_117);
x_129 = l_Lean_IR_EmitC_emitCName(x_117, x_2, x_116);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_130 = lean_ctor_get(x_129, 1);
lean_inc(x_130);
lean_dec(x_129);
x_131 = l_Nat_forMAux___main___at_Lean_IR_EmitC_emitJmp___spec__1___closed__1;
x_132 = lean_string_append(x_130, x_131);
lean_inc(x_117);
x_133 = l_Lean_IR_EmitC_emitCInitName(x_117, x_2, x_132);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_134 = lean_ctor_get(x_133, 1);
lean_inc(x_134);
lean_dec(x_133);
x_135 = l_Lean_IR_EmitC_emitDeclInit___closed__1;
x_136 = lean_string_append(x_134, x_135);
x_137 = l_IO_println___rarg___closed__1;
x_138 = lean_string_append(x_136, x_137);
x_139 = l_Lean_IR_EmitC_emitMarkPersistent(x_1, x_117, x_2, x_138);
return x_139;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
lean_dec(x_117);
x_140 = lean_ctor_get(x_133, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_133, 1);
lean_inc(x_141);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 lean_ctor_release(x_133, 1);
 x_142 = x_133;
} else {
 lean_dec_ref(x_133);
 x_142 = lean_box(0);
}
if (lean_is_scalar(x_142)) {
 x_143 = lean_alloc_ctor(1, 2, 0);
} else {
 x_143 = x_142;
}
lean_ctor_set(x_143, 0, x_140);
lean_ctor_set(x_143, 1, x_141);
return x_143;
}
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
lean_dec(x_117);
x_144 = lean_ctor_get(x_129, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_129, 1);
lean_inc(x_145);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 lean_ctor_release(x_129, 1);
 x_146 = x_129;
} else {
 lean_dec_ref(x_129);
 x_146 = lean_box(0);
}
if (lean_is_scalar(x_146)) {
 x_147 = lean_alloc_ctor(1, 2, 0);
} else {
 x_147 = x_146;
}
lean_ctor_set(x_147, 0, x_144);
lean_ctor_set(x_147, 1, x_145);
return x_147;
}
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_148 = lean_ctor_get(x_128, 0);
lean_inc(x_148);
lean_dec(x_128);
x_149 = l_Lean_IR_EmitC_emitMainFn___closed__27;
x_150 = lean_string_append(x_116, x_149);
x_151 = l_Lean_IR_EmitC_emitCName(x_148, x_2, x_150);
if (lean_obj_tag(x_151) == 0)
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_152 = lean_ctor_get(x_151, 1);
lean_inc(x_152);
lean_dec(x_151);
x_153 = l_Lean_IR_EmitC_emitMainFn___closed__3;
x_154 = lean_string_append(x_152, x_153);
x_155 = l_IO_println___rarg___closed__1;
x_156 = lean_string_append(x_154, x_155);
x_157 = l_Lean_IR_EmitC_emitDeclInit___closed__2;
x_158 = lean_string_append(x_156, x_157);
x_159 = lean_string_append(x_158, x_155);
lean_inc(x_117);
x_160 = l_Lean_IR_EmitC_emitCName(x_117, x_2, x_159);
if (lean_obj_tag(x_160) == 0)
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_161 = lean_ctor_get(x_160, 1);
lean_inc(x_161);
lean_dec(x_160);
x_162 = l_Lean_IR_EmitC_emitDeclInit___closed__3;
x_163 = lean_string_append(x_161, x_162);
x_164 = lean_string_append(x_163, x_155);
x_165 = l_Lean_IR_EmitC_emitMarkPersistent(x_1, x_117, x_2, x_164);
if (lean_obj_tag(x_165) == 0)
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_166 = lean_ctor_get(x_165, 1);
lean_inc(x_166);
if (lean_is_exclusive(x_165)) {
 lean_ctor_release(x_165, 0);
 lean_ctor_release(x_165, 1);
 x_167 = x_165;
} else {
 lean_dec_ref(x_165);
 x_167 = lean_box(0);
}
x_168 = l_Lean_IR_EmitC_emitMainFn___closed__22;
x_169 = lean_string_append(x_166, x_168);
x_170 = lean_string_append(x_169, x_155);
x_171 = lean_box(0);
if (lean_is_scalar(x_167)) {
 x_172 = lean_alloc_ctor(0, 2, 0);
} else {
 x_172 = x_167;
}
lean_ctor_set(x_172, 0, x_171);
lean_ctor_set(x_172, 1, x_170);
return x_172;
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_173 = lean_ctor_get(x_165, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_165, 1);
lean_inc(x_174);
if (lean_is_exclusive(x_165)) {
 lean_ctor_release(x_165, 0);
 lean_ctor_release(x_165, 1);
 x_175 = x_165;
} else {
 lean_dec_ref(x_165);
 x_175 = lean_box(0);
}
if (lean_is_scalar(x_175)) {
 x_176 = lean_alloc_ctor(1, 2, 0);
} else {
 x_176 = x_175;
}
lean_ctor_set(x_176, 0, x_173);
lean_ctor_set(x_176, 1, x_174);
return x_176;
}
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
lean_dec(x_117);
x_177 = lean_ctor_get(x_160, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_160, 1);
lean_inc(x_178);
if (lean_is_exclusive(x_160)) {
 lean_ctor_release(x_160, 0);
 lean_ctor_release(x_160, 1);
 x_179 = x_160;
} else {
 lean_dec_ref(x_160);
 x_179 = lean_box(0);
}
if (lean_is_scalar(x_179)) {
 x_180 = lean_alloc_ctor(1, 2, 0);
} else {
 x_180 = x_179;
}
lean_ctor_set(x_180, 0, x_177);
lean_ctor_set(x_180, 1, x_178);
return x_180;
}
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
lean_dec(x_117);
x_181 = lean_ctor_get(x_151, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_151, 1);
lean_inc(x_182);
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 lean_ctor_release(x_151, 1);
 x_183 = x_151;
} else {
 lean_dec_ref(x_151);
 x_183 = lean_box(0);
}
if (lean_is_scalar(x_183)) {
 x_184 = lean_alloc_ctor(1, 2, 0);
} else {
 x_184 = x_183;
}
lean_ctor_set(x_184, 0, x_181);
lean_ctor_set(x_184, 1, x_182);
return x_184;
}
}
}
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; 
lean_dec(x_115);
x_185 = l_Lean_IR_EmitC_emitMainFn___closed__27;
x_186 = lean_string_append(x_116, x_185);
x_187 = l_Lean_IR_EmitC_emitCName(x_117, x_2, x_186);
if (lean_obj_tag(x_187) == 0)
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_188 = lean_ctor_get(x_187, 1);
lean_inc(x_188);
if (lean_is_exclusive(x_187)) {
 lean_ctor_release(x_187, 0);
 lean_ctor_release(x_187, 1);
 x_189 = x_187;
} else {
 lean_dec_ref(x_187);
 x_189 = lean_box(0);
}
x_190 = l_Lean_IR_EmitC_emitMainFn___closed__3;
x_191 = lean_string_append(x_188, x_190);
x_192 = l_IO_println___rarg___closed__1;
x_193 = lean_string_append(x_191, x_192);
x_194 = l_Lean_IR_EmitC_emitDeclInit___closed__2;
x_195 = lean_string_append(x_193, x_194);
x_196 = lean_string_append(x_195, x_192);
x_197 = l_Lean_IR_EmitC_emitMainFn___closed__22;
x_198 = lean_string_append(x_196, x_197);
x_199 = lean_string_append(x_198, x_192);
x_200 = lean_box(0);
if (lean_is_scalar(x_189)) {
 x_201 = lean_alloc_ctor(0, 2, 0);
} else {
 x_201 = x_189;
}
lean_ctor_set(x_201, 0, x_200);
lean_ctor_set(x_201, 1, x_199);
return x_201;
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; 
x_202 = lean_ctor_get(x_187, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_187, 1);
lean_inc(x_203);
if (lean_is_exclusive(x_187)) {
 lean_ctor_release(x_187, 0);
 lean_ctor_release(x_187, 1);
 x_204 = x_187;
} else {
 lean_dec_ref(x_187);
 x_204 = lean_box(0);
}
if (lean_is_scalar(x_204)) {
 x_205 = lean_alloc_ctor(1, 2, 0);
} else {
 x_205 = x_204;
}
lean_ctor_set(x_205, 0, x_202);
lean_ctor_set(x_205, 1, x_203);
return x_205;
}
}
}
}
}
lean_object* l_Lean_IR_EmitC_emitDeclInit___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_EmitC_emitDeclInit(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* _init_l_Array_forMAux___main___at_Lean_IR_EmitC_emitInitFn___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("lean_object* initialize_");
return x_1;
}
}
lean_object* _init_l_Array_forMAux___main___at_Lean_IR_EmitC_emitInitFn___spec__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("(lean_object*);");
return x_1;
}
}
lean_object* l_Array_forMAux___main___at_Lean_IR_EmitC_emitInitFn___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_1);
x_6 = lean_nat_dec_lt(x_2, x_5);
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
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_9 = lean_array_fget(x_1, x_2);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_2, x_10);
lean_dec(x_2);
x_12 = lean_ctor_get(x_9, 0);
lean_inc(x_12);
lean_dec(x_9);
x_13 = l_String_splitAux___main___closed__1;
x_14 = lean_name_mangle(x_12, x_13);
x_15 = l_Array_forMAux___main___at_Lean_IR_EmitC_emitInitFn___spec__1___closed__1;
x_16 = lean_string_append(x_15, x_14);
lean_dec(x_14);
x_17 = l_Array_forMAux___main___at_Lean_IR_EmitC_emitInitFn___spec__1___closed__2;
x_18 = lean_string_append(x_16, x_17);
x_19 = lean_string_append(x_4, x_18);
lean_dec(x_18);
x_20 = l_IO_println___rarg___closed__1;
x_21 = lean_string_append(x_19, x_20);
x_2 = x_11;
x_4 = x_21;
goto _start;
}
}
}
lean_object* l_Array_forMAux___main___at_Lean_IR_EmitC_emitInitFn___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_2);
x_7 = lean_nat_dec_lt(x_3, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
lean_dec(x_1);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_5);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_10 = lean_array_fget(x_2, x_3);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_3, x_11);
lean_dec(x_3);
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec(x_10);
x_14 = l_String_splitAux___main___closed__1;
x_15 = lean_name_mangle(x_13, x_14);
x_16 = l_Lean_IR_EmitC_emitMainFn___closed__2;
x_17 = lean_string_append(x_16, x_15);
lean_dec(x_15);
x_18 = l_Lean_IR_EmitC_emitMainFn___closed__3;
x_19 = lean_string_append(x_17, x_18);
x_20 = l_Lean_IR_EmitC_emitMainFn___closed__22;
lean_inc(x_1);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_1);
x_22 = l_Lean_IR_EmitC_emitDeclInit___closed__2;
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_19);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_List_forM___main___at_Lean_IR_EmitC_emitMainFn___spec__2(x_24, x_4, x_5);
lean_dec(x_24);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_3 = x_12;
x_5 = x_26;
goto _start;
}
}
}
lean_object* l_List_forM___main___at_Lean_IR_EmitC_emitInitFn___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
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
lean_object* _init_l_Lean_IR_EmitC_emitInitFn___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("(lean_object* w) {");
return x_1;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitInitFn___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_G_initialized = true;");
return x_1;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitInitFn___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_IR_EmitC_emitInitFn___closed__2;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitInitFn___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("if (_G_initialized) return lean_mk_io_result(lean_box(0));");
return x_1;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitInitFn___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_EmitC_emitInitFn___closed__4;
x_2 = l_Lean_IR_EmitC_emitInitFn___closed__3;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitInitFn___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("lean_object * res;");
return x_1;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitInitFn___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_EmitC_emitInitFn___closed__6;
x_2 = l_Lean_IR_EmitC_emitInitFn___closed__5;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitInitFn___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("static bool _G_initialized = false;");
return x_1;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitInitFn___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("return lean_mk_io_result(lean_box(0));");
return x_1;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitInitFn___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_EmitC_emitInitFn___closed__9;
x_2 = l_Lean_IR_EmitC_emitMainFn___closed__4;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_IR_EmitC_emitInitFn(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
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
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_Array_forMAux___main___at_Lean_IR_EmitC_emitInitFn___spec__1(x_9, x_10, x_1, x_8);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = l_String_splitAux___main___closed__1;
x_14 = lean_name_mangle(x_7, x_13);
x_15 = l_Array_forMAux___main___at_Lean_IR_EmitC_emitInitFn___spec__1___closed__1;
x_16 = lean_string_append(x_15, x_14);
lean_dec(x_14);
x_17 = l_Lean_IR_EmitC_emitInitFn___closed__1;
x_18 = lean_string_append(x_16, x_17);
x_19 = lean_box(0);
x_20 = l_Lean_IR_EmitC_emitInitFn___closed__7;
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_Lean_IR_EmitC_emitInitFn___closed__8;
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
x_24 = l_List_forM___main___at_Lean_IR_EmitC_emitMainFn___spec__2(x_23, x_1, x_12);
lean_dec(x_23);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_26 = l_Array_forMAux___main___at_Lean_IR_EmitC_emitInitFn___spec__2(x_19, x_9, x_10, x_1, x_25);
lean_dec(x_9);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = l_Lean_IR_declMapExt;
x_29 = l_Lean_SimplePersistentEnvExtension_getEntries___rarg(x_28, x_4);
lean_dec(x_4);
x_30 = l_List_reverse___rarg(x_29);
x_31 = l_List_forM___main___at_Lean_IR_EmitC_emitInitFn___spec__3(x_30, x_1, x_27);
lean_dec(x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_33 = l_Lean_IR_EmitC_emitInitFn___closed__10;
x_34 = l_List_forM___main___at_Lean_IR_EmitC_emitMainFn___spec__2(x_33, x_1, x_32);
return x_34;
}
else
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_31);
if (x_35 == 0)
{
return x_31;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_31, 0);
x_37 = lean_ctor_get(x_31, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_31);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
lean_object* l_Array_forMAux___main___at_Lean_IR_EmitC_emitInitFn___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_forMAux___main___at_Lean_IR_EmitC_emitInitFn___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_forMAux___main___at_Lean_IR_EmitC_emitInitFn___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_forMAux___main___at_Lean_IR_EmitC_emitInitFn___spec__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_List_forM___main___at_Lean_IR_EmitC_emitInitFn___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_forM___main___at_Lean_IR_EmitC_emitInitFn___spec__3(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_IR_EmitC_emitInitFn___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_EmitC_emitInitFn(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_IR_EmitC_main(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Lean_IR_EmitC_emitFileHeader(x_1, x_2);
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec(x_3);
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
x_9 = l_Lean_IR_EmitC_emitInitFn(x_1, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
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
lean_object* lean_ir_emit_c(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = l_HashMap_Inhabited___closed__1;
x_4 = lean_box(0);
x_5 = l_Array_empty___closed__1;
x_6 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_4);
lean_ctor_set(x_6, 4, x_5);
x_7 = l_String_splitAux___main___closed__1;
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
lean_object* initialize_Init_Control_Conditional(lean_object*);
lean_object* initialize_Init_Lean_Runtime(lean_object*);
lean_object* initialize_Init_Lean_Compiler_NameMangling(lean_object*);
lean_object* initialize_Init_Lean_Compiler_ExportAttr(lean_object*);
lean_object* initialize_Init_Lean_Compiler_InitAttr(lean_object*);
lean_object* initialize_Init_Lean_Compiler_IR_CompilerM(lean_object*);
lean_object* initialize_Init_Lean_Compiler_IR_EmitUtil(lean_object*);
lean_object* initialize_Init_Lean_Compiler_IR_NormIds(lean_object*);
lean_object* initialize_Init_Lean_Compiler_IR_SimpCase(lean_object*);
lean_object* initialize_Init_Lean_Compiler_IR_Boxing(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Compiler_IR_EmitC(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Control_Conditional(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Runtime(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Compiler_NameMangling(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Compiler_ExportAttr(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Compiler_InitAttr(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Compiler_IR_CompilerM(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Compiler_IR_EmitUtil(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Compiler_IR_NormIds(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Compiler_IR_SimpCase(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Compiler_IR_Boxing(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_IR_EmitC_leanMainFn___closed__1 = _init_l_Lean_IR_EmitC_leanMainFn___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_leanMainFn___closed__1);
l_Lean_IR_EmitC_leanMainFn = _init_l_Lean_IR_EmitC_leanMainFn();
lean_mark_persistent(l_Lean_IR_EmitC_leanMainFn);
l_Lean_IR_EmitC_argToCString___closed__1 = _init_l_Lean_IR_EmitC_argToCString___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_argToCString___closed__1);
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
l_Lean_IR_EmitC_throwInvalidExportName___rarg___closed__1 = _init_l_Lean_IR_EmitC_throwInvalidExportName___rarg___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_throwInvalidExportName___rarg___closed__1);
l_Lean_IR_EmitC_toCName___closed__1 = _init_l_Lean_IR_EmitC_toCName___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_toCName___closed__1);
l_Lean_IR_EmitC_toCName___closed__2 = _init_l_Lean_IR_EmitC_toCName___closed__2();
lean_mark_persistent(l_Lean_IR_EmitC_toCName___closed__2);
l_Lean_IR_EmitC_toCName___closed__3 = _init_l_Lean_IR_EmitC_toCName___closed__3();
lean_mark_persistent(l_Lean_IR_EmitC_toCName___closed__3);
l_Lean_IR_EmitC_toCInitName___closed__1 = _init_l_Lean_IR_EmitC_toCInitName___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_toCInitName___closed__1);
l_Lean_IR_EmitC_emitFnDeclAux___closed__1 = _init_l_Lean_IR_EmitC_emitFnDeclAux___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_emitFnDeclAux___closed__1);
l_List_forM___main___at_Lean_IR_EmitC_emitFnDecls___spec__5___closed__1 = _init_l_List_forM___main___at_Lean_IR_EmitC_emitFnDecls___spec__5___closed__1();
lean_mark_persistent(l_List_forM___main___at_Lean_IR_EmitC_emitFnDecls___spec__5___closed__1);
l_List_forM___main___at_Lean_IR_EmitC_emitFnDecls___spec__5___closed__2 = _init_l_List_forM___main___at_Lean_IR_EmitC_emitFnDecls___spec__5___closed__2();
lean_mark_persistent(l_List_forM___main___at_Lean_IR_EmitC_emitFnDecls___spec__5___closed__2);
l_Lean_IR_EmitC_emitMainFn___closed__1 = _init_l_Lean_IR_EmitC_emitMainFn___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___closed__1);
l_Lean_IR_EmitC_emitMainFn___closed__2 = _init_l_Lean_IR_EmitC_emitMainFn___closed__2();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___closed__2);
l_Lean_IR_EmitC_emitMainFn___closed__3 = _init_l_Lean_IR_EmitC_emitMainFn___closed__3();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___closed__3);
l_Lean_IR_EmitC_emitMainFn___closed__4 = _init_l_Lean_IR_EmitC_emitMainFn___closed__4();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___closed__4);
l_Lean_IR_EmitC_emitMainFn___closed__5 = _init_l_Lean_IR_EmitC_emitMainFn___closed__5();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___closed__5);
l_Lean_IR_EmitC_emitMainFn___closed__6 = _init_l_Lean_IR_EmitC_emitMainFn___closed__6();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___closed__6);
l_Lean_IR_EmitC_emitMainFn___closed__7 = _init_l_Lean_IR_EmitC_emitMainFn___closed__7();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___closed__7);
l_Lean_IR_EmitC_emitMainFn___closed__8 = _init_l_Lean_IR_EmitC_emitMainFn___closed__8();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___closed__8);
l_Lean_IR_EmitC_emitMainFn___closed__9 = _init_l_Lean_IR_EmitC_emitMainFn___closed__9();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___closed__9);
l_Lean_IR_EmitC_emitMainFn___closed__10 = _init_l_Lean_IR_EmitC_emitMainFn___closed__10();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___closed__10);
l_Lean_IR_EmitC_emitMainFn___closed__11 = _init_l_Lean_IR_EmitC_emitMainFn___closed__11();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___closed__11);
l_Lean_IR_EmitC_emitMainFn___closed__12 = _init_l_Lean_IR_EmitC_emitMainFn___closed__12();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___closed__12);
l_Lean_IR_EmitC_emitMainFn___closed__13 = _init_l_Lean_IR_EmitC_emitMainFn___closed__13();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___closed__13);
l_Lean_IR_EmitC_emitMainFn___closed__14 = _init_l_Lean_IR_EmitC_emitMainFn___closed__14();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___closed__14);
l_Lean_IR_EmitC_emitMainFn___closed__15 = _init_l_Lean_IR_EmitC_emitMainFn___closed__15();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___closed__15);
l_Lean_IR_EmitC_emitMainFn___closed__16 = _init_l_Lean_IR_EmitC_emitMainFn___closed__16();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___closed__16);
l_Lean_IR_EmitC_emitMainFn___closed__17 = _init_l_Lean_IR_EmitC_emitMainFn___closed__17();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___closed__17);
l_Lean_IR_EmitC_emitMainFn___closed__18 = _init_l_Lean_IR_EmitC_emitMainFn___closed__18();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___closed__18);
l_Lean_IR_EmitC_emitMainFn___closed__19 = _init_l_Lean_IR_EmitC_emitMainFn___closed__19();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___closed__19);
l_Lean_IR_EmitC_emitMainFn___closed__20 = _init_l_Lean_IR_EmitC_emitMainFn___closed__20();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___closed__20);
l_Lean_IR_EmitC_emitMainFn___closed__21 = _init_l_Lean_IR_EmitC_emitMainFn___closed__21();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___closed__21);
l_Lean_IR_EmitC_emitMainFn___closed__22 = _init_l_Lean_IR_EmitC_emitMainFn___closed__22();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___closed__22);
l_Lean_IR_EmitC_emitMainFn___closed__23 = _init_l_Lean_IR_EmitC_emitMainFn___closed__23();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___closed__23);
l_Lean_IR_EmitC_emitMainFn___closed__24 = _init_l_Lean_IR_EmitC_emitMainFn___closed__24();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___closed__24);
l_Lean_IR_EmitC_emitMainFn___closed__25 = _init_l_Lean_IR_EmitC_emitMainFn___closed__25();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___closed__25);
l_Lean_IR_EmitC_emitMainFn___closed__26 = _init_l_Lean_IR_EmitC_emitMainFn___closed__26();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___closed__26);
l_Lean_IR_EmitC_emitMainFn___closed__27 = _init_l_Lean_IR_EmitC_emitMainFn___closed__27();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___closed__27);
l_Lean_IR_EmitC_emitMainFn___closed__28 = _init_l_Lean_IR_EmitC_emitMainFn___closed__28();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___closed__28);
l_Lean_IR_EmitC_emitMainFn___closed__29 = _init_l_Lean_IR_EmitC_emitMainFn___closed__29();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___closed__29);
l_Lean_IR_EmitC_emitMainFn___closed__30 = _init_l_Lean_IR_EmitC_emitMainFn___closed__30();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___closed__30);
l_Lean_IR_EmitC_emitMainFn___closed__31 = _init_l_Lean_IR_EmitC_emitMainFn___closed__31();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___closed__31);
l_Lean_IR_EmitC_emitMainFn___closed__32 = _init_l_Lean_IR_EmitC_emitMainFn___closed__32();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___closed__32);
l_Lean_IR_EmitC_emitMainFn___closed__33 = _init_l_Lean_IR_EmitC_emitMainFn___closed__33();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___closed__33);
l_Lean_IR_EmitC_emitMainFn___closed__34 = _init_l_Lean_IR_EmitC_emitMainFn___closed__34();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___closed__34);
l_Lean_IR_EmitC_emitMainFn___closed__35 = _init_l_Lean_IR_EmitC_emitMainFn___closed__35();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___closed__35);
l_Lean_IR_EmitC_emitMainFn___closed__36 = _init_l_Lean_IR_EmitC_emitMainFn___closed__36();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___closed__36);
l_Lean_IR_EmitC_emitMainFn___closed__37 = _init_l_Lean_IR_EmitC_emitMainFn___closed__37();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___closed__37);
l_Lean_IR_EmitC_emitMainFn___closed__38 = _init_l_Lean_IR_EmitC_emitMainFn___closed__38();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___closed__38);
l_Lean_IR_EmitC_emitMainFn___closed__39 = _init_l_Lean_IR_EmitC_emitMainFn___closed__39();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___closed__39);
l_Lean_IR_EmitC_emitMainFn___closed__40 = _init_l_Lean_IR_EmitC_emitMainFn___closed__40();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___closed__40);
l_Lean_IR_EmitC_emitMainFn___closed__41 = _init_l_Lean_IR_EmitC_emitMainFn___closed__41();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___closed__41);
l_Lean_IR_EmitC_emitMainFn___closed__42 = _init_l_Lean_IR_EmitC_emitMainFn___closed__42();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___closed__42);
l_Lean_IR_EmitC_emitMainFn___closed__43 = _init_l_Lean_IR_EmitC_emitMainFn___closed__43();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___closed__43);
l_Lean_IR_EmitC_emitMainFn___closed__44 = _init_l_Lean_IR_EmitC_emitMainFn___closed__44();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___closed__44);
l_Lean_IR_EmitC_emitMainFn___closed__45 = _init_l_Lean_IR_EmitC_emitMainFn___closed__45();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___closed__45);
l_Lean_IR_EmitC_emitMainFn___closed__46 = _init_l_Lean_IR_EmitC_emitMainFn___closed__46();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___closed__46);
l_Lean_IR_EmitC_emitMainFn___closed__47 = _init_l_Lean_IR_EmitC_emitMainFn___closed__47();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___closed__47);
l_Lean_IR_EmitC_emitMainFn___closed__48 = _init_l_Lean_IR_EmitC_emitMainFn___closed__48();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___closed__48);
l_Lean_IR_EmitC_emitMainFn___closed__49 = _init_l_Lean_IR_EmitC_emitMainFn___closed__49();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___closed__49);
l_Lean_IR_EmitC_emitMainFn___closed__50 = _init_l_Lean_IR_EmitC_emitMainFn___closed__50();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___closed__50);
l_Lean_IR_EmitC_emitMainFn___closed__51 = _init_l_Lean_IR_EmitC_emitMainFn___closed__51();
lean_mark_persistent(l_Lean_IR_EmitC_emitMainFn___closed__51);
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
l_Lean_IR_EmitC_emitIf___closed__1 = _init_l_Lean_IR_EmitC_emitIf___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_emitIf___closed__1);
l_Lean_IR_EmitC_emitIf___closed__2 = _init_l_Lean_IR_EmitC_emitIf___closed__2();
lean_mark_persistent(l_Lean_IR_EmitC_emitIf___closed__2);
l_Lean_IR_EmitC_emitIf___closed__3 = _init_l_Lean_IR_EmitC_emitIf___closed__3();
lean_mark_persistent(l_Lean_IR_EmitC_emitIf___closed__3);
l_Array_forMAux___main___at_Lean_IR_EmitC_emitCase___spec__1___closed__1 = _init_l_Array_forMAux___main___at_Lean_IR_EmitC_emitCase___spec__1___closed__1();
lean_mark_persistent(l_Array_forMAux___main___at_Lean_IR_EmitC_emitCase___spec__1___closed__1);
l_Lean_IR_EmitC_emitCase___closed__1 = _init_l_Lean_IR_EmitC_emitCase___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_emitCase___closed__1);
l_Lean_IR_EmitC_emitCase___closed__2 = _init_l_Lean_IR_EmitC_emitCase___closed__2();
lean_mark_persistent(l_Lean_IR_EmitC_emitCase___closed__2);
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
l_Nat_forMAux___main___at_Lean_IR_EmitC_emitJmp___spec__1___closed__1 = _init_l_Nat_forMAux___main___at_Lean_IR_EmitC_emitJmp___spec__1___closed__1();
lean_mark_persistent(l_Nat_forMAux___main___at_Lean_IR_EmitC_emitJmp___spec__1___closed__1);
l_Lean_IR_EmitC_emitJmp___closed__1 = _init_l_Lean_IR_EmitC_emitJmp___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_emitJmp___closed__1);
l_Lean_IR_EmitC_emitJmp___closed__2 = _init_l_Lean_IR_EmitC_emitJmp___closed__2();
lean_mark_persistent(l_Lean_IR_EmitC_emitJmp___closed__2);
l_Lean_IR_EmitC_emitCtorScalarSize___closed__1 = _init_l_Lean_IR_EmitC_emitCtorScalarSize___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_emitCtorScalarSize___closed__1);
l_Lean_IR_EmitC_emitAllocCtor___closed__1 = _init_l_Lean_IR_EmitC_emitAllocCtor___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_emitAllocCtor___closed__1);
l_Lean_IR_EmitC_emitCtor___closed__1 = _init_l_Lean_IR_EmitC_emitCtor___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_emitCtor___closed__1);
l_Nat_forMAux___main___at_Lean_IR_EmitC_emitReset___spec__1___closed__1 = _init_l_Nat_forMAux___main___at_Lean_IR_EmitC_emitReset___spec__1___closed__1();
lean_mark_persistent(l_Nat_forMAux___main___at_Lean_IR_EmitC_emitReset___spec__1___closed__1);
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
l_Lean_IR_EmitC_emitExternCall___closed__1 = _init_l_Lean_IR_EmitC_emitExternCall___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_emitExternCall___closed__1);
l_Nat_forMAux___main___at_Lean_IR_EmitC_emitPartialApp___spec__1___closed__1 = _init_l_Nat_forMAux___main___at_Lean_IR_EmitC_emitPartialApp___spec__1___closed__1();
lean_mark_persistent(l_Nat_forMAux___main___at_Lean_IR_EmitC_emitPartialApp___spec__1___closed__1);
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
l_Lean_IR_EmitC_emitUnbox___closed__1 = _init_l_Lean_IR_EmitC_emitUnbox___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_emitUnbox___closed__1);
l_Lean_IR_EmitC_emitUnbox___closed__2 = _init_l_Lean_IR_EmitC_emitUnbox___closed__2();
lean_mark_persistent(l_Lean_IR_EmitC_emitUnbox___closed__2);
l_Lean_IR_EmitC_emitUnbox___closed__3 = _init_l_Lean_IR_EmitC_emitUnbox___closed__3();
lean_mark_persistent(l_Lean_IR_EmitC_emitUnbox___closed__3);
l_Lean_IR_EmitC_emitUnbox___closed__4 = _init_l_Lean_IR_EmitC_emitUnbox___closed__4();
lean_mark_persistent(l_Lean_IR_EmitC_emitUnbox___closed__4);
l_Lean_IR_EmitC_emitIsShared___closed__1 = _init_l_Lean_IR_EmitC_emitIsShared___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_emitIsShared___closed__1);
l_Lean_IR_EmitC_emitIsTaggedPtr___closed__1 = _init_l_Lean_IR_EmitC_emitIsTaggedPtr___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_emitIsTaggedPtr___closed__1);
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
l_Nat_forMAux___main___at_Lean_IR_EmitC_emitTailCall___spec__2___closed__1 = _init_l_Nat_forMAux___main___at_Lean_IR_EmitC_emitTailCall___spec__2___closed__1();
lean_mark_persistent(l_Nat_forMAux___main___at_Lean_IR_EmitC_emitTailCall___spec__2___closed__1);
l_Nat_forMAux___main___at_Lean_IR_EmitC_emitTailCall___spec__3___closed__1 = _init_l_Nat_forMAux___main___at_Lean_IR_EmitC_emitTailCall___spec__3___closed__1();
lean_mark_persistent(l_Nat_forMAux___main___at_Lean_IR_EmitC_emitTailCall___spec__3___closed__1);
l_Lean_IR_EmitC_emitTailCall___closed__1 = _init_l_Lean_IR_EmitC_emitTailCall___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_emitTailCall___closed__1);
l_Lean_IR_EmitC_emitTailCall___closed__2 = _init_l_Lean_IR_EmitC_emitTailCall___closed__2();
lean_mark_persistent(l_Lean_IR_EmitC_emitTailCall___closed__2);
l_Lean_IR_EmitC_emitTailCall___closed__3 = _init_l_Lean_IR_EmitC_emitTailCall___closed__3();
lean_mark_persistent(l_Lean_IR_EmitC_emitTailCall___closed__3);
l_Lean_IR_EmitC_emitBlock___main___closed__1 = _init_l_Lean_IR_EmitC_emitBlock___main___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_emitBlock___main___closed__1);
l_Lean_IR_EmitC_emitBlock___main___closed__2 = _init_l_Lean_IR_EmitC_emitBlock___main___closed__2();
lean_mark_persistent(l_Lean_IR_EmitC_emitBlock___main___closed__2);
l_Lean_IR_EmitC_emitFnBody___main___closed__1 = _init_l_Lean_IR_EmitC_emitFnBody___main___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_emitFnBody___main___closed__1);
l_Nat_forMAux___main___at_Lean_IR_EmitC_emitDeclAux___spec__1___closed__1 = _init_l_Nat_forMAux___main___at_Lean_IR_EmitC_emitDeclAux___spec__1___closed__1();
lean_mark_persistent(l_Nat_forMAux___main___at_Lean_IR_EmitC_emitDeclAux___spec__1___closed__1);
l_Nat_forMAux___main___at_Lean_IR_EmitC_emitDeclAux___spec__1___closed__2 = _init_l_Nat_forMAux___main___at_Lean_IR_EmitC_emitDeclAux___spec__1___closed__2();
lean_mark_persistent(l_Nat_forMAux___main___at_Lean_IR_EmitC_emitDeclAux___spec__1___closed__2);
l_Nat_forMAux___main___at_Lean_IR_EmitC_emitDeclAux___spec__1___closed__3 = _init_l_Nat_forMAux___main___at_Lean_IR_EmitC_emitDeclAux___spec__1___closed__3();
lean_mark_persistent(l_Nat_forMAux___main___at_Lean_IR_EmitC_emitDeclAux___spec__1___closed__3);
l_Lean_IR_EmitC_emitDeclAux___closed__1 = _init_l_Lean_IR_EmitC_emitDeclAux___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_emitDeclAux___closed__1);
l_Lean_IR_EmitC_emitDeclAux___closed__2 = _init_l_Lean_IR_EmitC_emitDeclAux___closed__2();
lean_mark_persistent(l_Lean_IR_EmitC_emitDeclAux___closed__2);
l_Lean_IR_EmitC_emitDeclAux___closed__3 = _init_l_Lean_IR_EmitC_emitDeclAux___closed__3();
lean_mark_persistent(l_Lean_IR_EmitC_emitDeclAux___closed__3);
l_Lean_IR_EmitC_emitDecl___closed__1 = _init_l_Lean_IR_EmitC_emitDecl___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_emitDecl___closed__1);
l_Lean_IR_EmitC_emitMarkPersistent___closed__1 = _init_l_Lean_IR_EmitC_emitMarkPersistent___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_emitMarkPersistent___closed__1);
l_Lean_IR_EmitC_emitDeclInit___closed__1 = _init_l_Lean_IR_EmitC_emitDeclInit___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_emitDeclInit___closed__1);
l_Lean_IR_EmitC_emitDeclInit___closed__2 = _init_l_Lean_IR_EmitC_emitDeclInit___closed__2();
lean_mark_persistent(l_Lean_IR_EmitC_emitDeclInit___closed__2);
l_Lean_IR_EmitC_emitDeclInit___closed__3 = _init_l_Lean_IR_EmitC_emitDeclInit___closed__3();
lean_mark_persistent(l_Lean_IR_EmitC_emitDeclInit___closed__3);
l_Array_forMAux___main___at_Lean_IR_EmitC_emitInitFn___spec__1___closed__1 = _init_l_Array_forMAux___main___at_Lean_IR_EmitC_emitInitFn___spec__1___closed__1();
lean_mark_persistent(l_Array_forMAux___main___at_Lean_IR_EmitC_emitInitFn___spec__1___closed__1);
l_Array_forMAux___main___at_Lean_IR_EmitC_emitInitFn___spec__1___closed__2 = _init_l_Array_forMAux___main___at_Lean_IR_EmitC_emitInitFn___spec__1___closed__2();
lean_mark_persistent(l_Array_forMAux___main___at_Lean_IR_EmitC_emitInitFn___spec__1___closed__2);
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
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
