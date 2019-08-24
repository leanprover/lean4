// Lean compiler output
// Module: init.lean.compiler.ir.emitc
// Imports: init.control.conditional init.lean.runtime init.lean.compiler.namemangling init.lean.compiler.exportattr init.lean.compiler.initattr init.lean.compiler.ir.compilerm init.lean.compiler.ir.emitutil init.lean.compiler.ir.normids init.lean.compiler.ir.simpcase init.lean.compiler.ir.boxing
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
lean_object* l_Lean_IR_EmitC_emitSSet___closed__4;
lean_object* l_Lean_IR_EmitC_toCName___closed__1;
extern lean_object* l_Lean_IR_getDecl___closed__1;
lean_object* l_Lean_IR_EmitC_emitMainFn___closed__49;
uint8_t l_List_foldr___main___at_Lean_IR_EmitC_hasMainFn___spec__1(uint8_t, lean_object*);
lean_object* l_Lean_IR_EmitC_emitInitFn___closed__3;
lean_object* l_Lean_Name_mangle(lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_isIf___boxed(lean_object*);
lean_object* l_Lean_IR_EmitC_emitMainFn___closed__27;
lean_object* l_Lean_IR_EmitC_toCInitName___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitFnBody(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_toCName___closed__3;
lean_object* l_List_mfor___main___at_Lean_IR_EmitC_emitLns___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitCtor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emit___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitSProj___closed__4;
lean_object* l_Lean_IR_EmitC_emitSProj___closed__1;
lean_object* l_Lean_IR_EmitC_emitIsTaggedPtr___closed__1;
lean_object* l_Lean_getExternNameFor(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitReset___closed__3;
lean_object* l_Lean_IR_EmitC_toCType___closed__5;
lean_object* l_Lean_IR_EmitC_emitDeclAux___closed__1;
lean_object* l_Nat_mforAux___main___at_Lean_IR_EmitC_emitReset___spec__1___closed__1;
lean_object* l_Lean_IR_EmitC_throwUnknownVar___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitMainFn___closed__18;
lean_object* l_Lean_IR_EmitC_emitTag___closed__1;
lean_object* l_Lean_IR_EmitC_emitMainFn___closed__16;
lean_object* l_Nat_mforAux___main___at_Lean_IR_EmitC_emitTailCall___spec__3___closed__1;
lean_object* l_Lean_IR_EmitC_emitFileHeader___closed__13;
lean_object* l_Lean_IR_EmitC_emitAllocCtor(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitSSet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitDec(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
extern lean_object* l_Lean_IR_formatDecl___closed__3;
extern lean_object* l_Array_empty___closed__1;
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t l_Nat_anyAux___main___at_Lean_IR_EmitC_overwriteParam___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitFileHeader___closed__19;
lean_object* l_Lean_IR_EmitC_emitMainFn___closed__19;
lean_object* l_Lean_IR_EmitC_emitInitFn___closed__9;
lean_object* l_Lean_IR_EmitC_emitSetTag(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitDel___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitInc___closed__4;
lean_object* l_Lean_IR_EmitC_emitMainFn___closed__26;
lean_object* l_Lean_IR_EmitC_emitMainFn___closed__23;
lean_object* l_Lean_IR_EmitC_emitDecl___closed__1;
lean_object* l_Lean_IR_EmitC_emitFileFooter___boxed(lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitDeclAux___closed__2;
lean_object* l_Lean_IR_EmitC_emitCase___closed__1;
lean_object* l_Lean_IR_EmitC_emitJmp___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitCtorScalarSize___closed__1;
extern lean_object* l_Lean_IR_JoinPointId_HasToString___closed__1;
lean_object* l_Lean_IR_EmitC_emitReset___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mforAux___main___at_Lean_IR_EmitC_emitInitFn___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitMainFn___closed__5;
lean_object* l_Lean_IR_EmitC_emitCtor___closed__1;
lean_object* l_Lean_IR_EmitC_emitPartialApp___closed__1;
lean_object* l_Lean_IR_EmitC_leanMainFn;
lean_object* l_List_foldr___main___at_Lean_IR_EmitC_hasMainFn___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitInc___closed__3;
lean_object* l_Lean_IR_EmitC_emitDecl(lean_object*, lean_object*, lean_object*);
lean_object* l_List_mfor___main___at_Lean_IR_EmitC_emitFnDecls___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitFileHeader___closed__23;
extern lean_object* l_Char_quoteCore___closed__3;
lean_object* l_Nat_mforAux___main___at_Lean_IR_EmitC_emitTailCall___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_declareVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_declareParams___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_List_mfor___main___at_Lean_IR_EmitC_emitMainFn___spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitMainFn___closed__14;
lean_object* l_Nat_mforAux___main___at_Lean_IR_EmitC_emitDeclAux___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mforAux___main___at_Lean_IR_EmitC_emitInitFn___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitFileHeader___closed__17;
lean_object* l_Lean_IR_EmitC_emitSet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emit(lean_object*);
lean_object* l_Lean_IR_EmitC_declareParams(lean_object*, lean_object*, lean_object*);
lean_object* lean_get_init_fn_name_for(lean_object*, lean_object*);
lean_object* l_Lean_IR_Decl_normalizeIds(lean_object*);
lean_object* l_Lean_IR_EmitC_emitUnbox___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitMainFn___closed__38;
lean_object* l_Lean_IR_EmitC_emitMainFn___closed__1;
lean_object* l_Lean_IR_EmitC_emitNumLit___closed__3;
lean_object* l_Lean_IR_EmitC_emitSSet___closed__5;
lean_object* l_Lean_IR_EmitC_emitMainFnIfNeeded___boxed(lean_object*, lean_object*);
lean_object* l_Array_mforAux___main___at_Lean_IR_EmitC_emitFileHeader___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitOffset(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitFileHeader___closed__10;
lean_object* l_Lean_IR_EmitC_toCName___closed__2;
lean_object* l_Nat_mforAux___main___at_Lean_IR_EmitC_emitCtorSetArgs___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitFileHeader___closed__6;
lean_object* l_Lean_IR_EmitC_emitApp___closed__2;
lean_object* l_Lean_IR_EmitC_emitMainFn___closed__46;
lean_object* l_Lean_IR_EmitC_emitTailCall___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitPartialApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitInc___closed__5;
lean_object* l_Lean_IR_FnBody_body(lean_object*);
lean_object* l_Lean_IR_EmitC_emitMainFn___closed__33;
lean_object* l_Lean_IR_EmitC_emitApp___closed__1;
uint8_t l_Lean_isIOUnitInitFn(lean_object*, lean_object*);
lean_object* l_List_reverse___rarg(lean_object*);
lean_object* l_Lean_mkExternCall(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitMainFn___closed__30;
lean_object* l_Lean_IR_EmitC_emitSProj(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_declareVar(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_IR_ensureHasDefault(lean_object*);
lean_object* l_Lean_IR_EmitC_emitUProj___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitMainFn___closed__20;
lean_object* l_Lean_IR_EmitC_emitFileHeader___closed__2;
lean_object* l_Lean_IR_EmitC_quoteString___boxed(lean_object*);
lean_object* l_Lean_IR_EmitC_emitLns___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitMainFn___closed__35;
lean_object* lean_ir_decl_to_string(lean_object*);
lean_object* l_Array_mforAux___main___at_Lean_IR_EmitC_emitInitFn___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_mforAux___main___at_Lean_IR_EmitC_emitDeclAux___spec__1___closed__1;
lean_object* l_Lean_IR_EmitC_emitProj___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_getJPParams___closed__1;
lean_object* l_Lean_IR_EmitC_emitInc___closed__1;
lean_object* l_Array_uget(lean_object*, lean_object*, size_t, lean_object*);
lean_object* l_Lean_Name_toStringWithSep___main(lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitIsShared___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitMainFn___closed__24;
lean_object* l_Lean_IR_EmitC_emitMainFn___closed__11;
lean_object* l_Lean_IR_EmitC_isObj___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_isObj(lean_object*, lean_object*, lean_object*);
lean_object* l_List_mfor___main___at_Lean_IR_EmitC_emitInitFn___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitUSet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_isTailCall___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitFileFooter___closed__1;
lean_object* l_Lean_IR_EmitC_emitUSet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_toCType___closed__7;
lean_object* l_Lean_IR_EmitC_emitMainFn___closed__6;
lean_object* l_Lean_IR_EmitC_emitBoxFn___closed__4;
lean_object* l_Lean_IR_EmitC_emitFnDeclAux(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_toCType___closed__2;
uint8_t l_Lean_IR_ExplicitBoxing_isBoxedName(lean_object*);
lean_object* l_Lean_IR_EmitC_emitFileFooter___closed__2;
lean_object* l_Lean_IR_EmitC_emitDeclAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_leanMainFn___closed__1;
lean_object* l_Array_mforAux___main___at_Lean_IR_EmitC_emitCase___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitLit___closed__1;
extern lean_object* l_uint32Sz;
lean_object* l_Lean_IR_EmitC_emitFnDeclAux___closed__1;
lean_object* l_Nat_mforAux___main___at_Lean_IR_EmitC_emitFnDeclAux___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitUnbox___closed__1;
lean_object* l_Lean_IR_EmitC_emitLn___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_HashMapImp_find___at_Lean_IR_EmitC_isObj___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitSetTag___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitJmp(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_getEnv(lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitOffset___closed__1;
uint8_t l_Lean_IR_Decl_resultType(lean_object*);
lean_object* l_Lean_IR_EmitC_emitSSet___closed__2;
lean_object* l_Lean_IR_EmitC_emitApp___closed__4;
lean_object* l_Array_mforAux___main___at_Lean_IR_EmitC_declareParams___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Char_quoteCore___closed__1;
lean_object* l_Lean_IR_EmitC_emitMainFn___closed__2;
lean_object* l_Lean_IR_EmitC_throwInvalidExportName___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_mforAux___main___at_Lean_IR_EmitC_emitArgs___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitSProj___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* l_Lean_IR_EmitC_emitReset___closed__1;
lean_object* l_Lean_IR_EmitC_emitOffset___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitInitFn___closed__8;
lean_object* l_Lean_IR_EmitC_emitFnDecl(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_declareVars___main(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitFnDecls(lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitIsTaggedPtr(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_RBTree_toList___at_Lean_IR_EmitC_emitFnDecls___spec__3(lean_object*);
extern lean_object* l_Lean_IR_formatFnBody___main___closed__31;
lean_object* l_Lean_SimplePersistentEnvExtension_getEntries___rarg(lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_toCType___closed__4;
lean_object* l_Lean_IR_EmitC_emitReuse(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitInitFn___closed__4;
lean_object* l_Lean_IR_EmitC_emitFnDeclAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toList___rarg(lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitCtor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_quoteString(lean_object*);
lean_object* l_Nat_repr(lean_object*);
lean_object* l_Lean_IR_EmitC_emitMainFn___boxed(lean_object*, lean_object*);
extern lean_object* l_String_quote___closed__1;
lean_object* l_Lean_IR_EmitC_emitPartialApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_hasInitAttr(lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitJPs___main(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitLit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_mforAux___main___at_Lean_IR_EmitC_emitDeclAux___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_RBNode_insert___at_Lean_NameSet_insert___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitMainFn___closed__43;
lean_object* l_Lean_IR_EmitC_emitOffset___closed__2;
lean_object* l_Nat_mforAux___main___at_Lean_IR_EmitC_emitDeclAux___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_mkVarJPMaps(lean_object*);
lean_object* l_Lean_IR_EmitC_emitNumLit___closed__1;
lean_object* l_Nat_mforAux___main___at_Lean_IR_EmitC_emitTailCall___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_toStringArgs___boxed(lean_object*);
lean_object* l_Lean_IR_EmitC_emitInitFn(lean_object*, lean_object*);
lean_object* l_Nat_mforAux___main___at_Lean_IR_EmitC_emitDeclAux___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_AltCore_body(lean_object*);
lean_object* l_Lean_IR_EmitC_emitMainFn(lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitDel(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitMainFn___closed__47;
lean_object* l_Lean_IR_EmitC_getModName___boxed(lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_isIf(lean_object*);
lean_object* l_Lean_IR_EmitC_emitUnbox(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitTailCall(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_mforAux___main___at_Lean_IR_EmitC_emitJmp___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitIsTaggedPtr___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitVDecl(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitInitFn___closed__7;
lean_object* l_Lean_IR_EmitC_emitSSet(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitDeclInit___closed__2;
lean_object* l_Lean_IR_EmitC_emitMainFn___closed__31;
extern lean_object* l_Char_quoteCore___closed__2;
lean_object* l_Lean_IR_EmitC_emitMainFn___closed__12;
lean_object* l_Lean_IR_EmitC_emitMainFn___closed__15;
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitIf___closed__2;
lean_object* l_Lean_IR_EmitC_emitReset(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitProj___closed__1;
lean_object* l_Lean_IR_EmitC_toCType___closed__3;
lean_object* l_Lean_IR_EmitC_emitCase(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitReuse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_toHexDigit___boxed(lean_object*);
extern lean_object* l_List_reprAux___main___rarg___closed__1;
lean_object* l_Lean_IR_EmitC_emitUProj___closed__1;
lean_object* l_Lean_IR_EmitC_throwUnknownVar___rarg___closed__1;
lean_object* l_Lean_IR_EmitC_emitIsShared(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_isTailCallTo(lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_toCType(uint8_t);
lean_object* l_Lean_IR_EmitC_emitReset___closed__4;
lean_object* l_List_foldl___main___at_Lean_IR_EmitC_emitFnDecls___spec__1(lean_object*, lean_object*);
extern lean_object* l_PersistentHashMap_Stats_toString___closed__5;
lean_object* l_Lean_IR_EmitC_emitApp___closed__3;
lean_object* l_HashMapImp_find___at_Lean_IR_EmitC_isObj___spec__1___boxed(lean_object*, lean_object*);
extern lean_object* l_Option_HasRepr___rarg___closed__3;
extern lean_object* l_Lean_IR_formatFnBody___main___closed__3;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_declareVar___closed__1;
lean_object* l_Lean_IR_EmitC_emitFileHeader___closed__21;
lean_object* l_Lean_IR_EmitC_emitMainFn___closed__36;
uint8_t l_Lean_isExternC(lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitLns___at_Lean_IR_EmitC_emitMainFn___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_main(lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitMainFnIfNeeded(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitFileHeader___closed__3;
lean_object* l_Lean_IR_EmitC_emitSSet___closed__3;
lean_object* l_AssocList_find___main___at_Lean_IR_EmitC_isObj___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitFileHeader___closed__11;
lean_object* l_AssocList_find___main___at_Lean_IR_EmitC_isObj___spec__2(lean_object*, lean_object*);
extern lean_object* l_Char_HasRepr___closed__1;
lean_object* l_Lean_IR_EmitC_emitMainFn___closed__34;
lean_object* l_List_mfor___main___at_Lean_IR_EmitC_emitFnDecls___spec__5___closed__1;
lean_object* l_Lean_IR_EmitC_emitMainFn___closed__4;
lean_object* l_Lean_IR_EmitC_emitNumLit___closed__4;
lean_object* l_Lean_IR_EmitC_emitArg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldl___main___at_Lean_IR_EmitC_emitFnDecls___spec__1___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_IR_declMapExt;
lean_object* l_Nat_mforAux___main___at_Lean_IR_EmitC_emitTailCall___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_fget(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitCtorScalarSize___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Array_mforAux___main___at_Lean_IR_EmitC_declareParams___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitMainFn___closed__29;
lean_object* l_Nat_mforAux___main___at_Lean_IR_EmitC_emitArgs___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitMainFn___closed__39;
lean_object* l_Array_mforAux___main___at_Lean_IR_EmitC_emitInitFn___spec__1___closed__2;
lean_object* l_Array_mforAux___main___at_Lean_IR_EmitC_emitCase___spec__1___closed__1;
extern lean_object* l_Char_quoteCore___closed__5;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_throwUnknownVar(lean_object*);
lean_object* l_Lean_IR_EmitC_emitMainFn___closed__13;
lean_object* l_Lean_IR_EmitC_emitSet___closed__1;
lean_object* l_Nat_mforAux___main___at_Lean_IR_EmitC_emitReset___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitLit(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_anyAux___main___at_Lean_IR_EmitC_overwriteParam___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
extern lean_object* l_Prod_HasRepr___rarg___closed__1;
lean_object* l_Lean_IR_EmitC_emitVDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_IR_paramInh;
uint8_t l_Array_isEmpty___rarg(lean_object*);
lean_object* l_Lean_IR_EmitC_emitArgs___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_String_foldlAux___main___at_Lean_IR_EmitC_quoteString___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitMainFn___closed__32;
lean_object* l_Lean_IR_EmitC_emitDec___closed__1;
lean_object* l_Lean_IR_EmitC_emitMainFn___closed__10;
lean_object* l_Lean_IR_EmitC_emitMainFn___closed__50;
lean_object* l_Lean_IR_EmitC_emitBox(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitFileHeader___closed__4;
lean_object* l_RBNode_revFold___main___at_Lean_IR_EmitC_emitFnDecls___spec__4___boxed(lean_object*, lean_object*);
lean_object* l_Nat_mforAux___main___at_Lean_IR_EmitC_emitFnDeclAux___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_getModName(lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitBoxFn___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_toHexDigit(lean_object*);
lean_object* l_Lean_IR_EmitC_emitSProj___closed__3;
lean_object* l_Lean_IR_EmitC_emitLn(lean_object*);
extern lean_object* l_Lean_Format_flatten___main___closed__1;
lean_object* l_Lean_IR_EmitC_emitDeclInit___closed__4;
extern lean_object* l_Lean_IR_altInh;
lean_object* l_Lean_IR_EmitC_emitUnbox___closed__4;
lean_object* l_AssocList_find___main___at_Lean_IR_EmitC_getJPParams___spec__2___boxed(lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitAllocCtor___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_EmitC_overwriteParam(lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_argToCString(lean_object*);
lean_object* l_Lean_IR_EmitC_emitSSet___closed__1;
lean_object* l_Lean_IR_EmitC_emitMainFn___closed__41;
lean_object* l_Lean_IR_EmitC_emitIf___closed__3;
lean_object* l_Lean_IR_EmitC_hasMainFn___boxed(lean_object*, lean_object*);
uint8_t l_Lean_IR_EmitC_paramEqArg(lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitNumLit___closed__2;
lean_object* l_Lean_IR_EmitC_emitSProj___closed__2;
lean_object* l_Nat_mforAux___main___at_Lean_IR_EmitC_emitCtorSetArgs___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitFns(lean_object*, lean_object*);
lean_object* l_List_mfor___main___at_Lean_IR_EmitC_emitInitFn___spec__3___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_collectUsedDecls(lean_object*, lean_object*, lean_object*);
uint8_t l_UInt32_decEq(uint32_t, uint32_t);
lean_object* l_Lean_IR_EmitC_emitNumLit___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Decl_params(lean_object*);
lean_object* l_Lean_IR_EmitC_emitFileHeader___closed__15;
lean_object* l_Lean_IR_EmitC_toCInitName___closed__1;
lean_object* l_Lean_IR_EmitC_toCName___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mforAux___main___at_Lean_IR_EmitC_emitFileHeader___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitBlock(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitJPs(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitFileHeader___closed__18;
lean_object* l_Lean_ParametricAttribute_getParam___at_Lean_isIOUnitInitFn___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitMainFn___closed__25;
lean_object* l_Lean_IR_EmitC_emitFileHeader___closed__22;
lean_object* l_Lean_IR_EmitC_emitFileHeader___boxed(lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitFileHeader___closed__14;
lean_object* l_Lean_IR_EmitC_emitAllocCtor___closed__1;
lean_object* l_Lean_IR_EmitC_emitInc___closed__2;
lean_object* l_Nat_mforAux___main___at_Lean_IR_EmitC_emitTailCall___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitBlock___main___closed__2;
lean_object* l_Lean_IR_EmitC_emitApp___closed__5;
uint8_t l_Lean_IR_FnBody_isTerminal(lean_object*);
lean_object* l_Lean_IR_EmitC_emitFileHeader___closed__12;
lean_object* l_Lean_IR_EmitC_getEnv___boxed(lean_object*, lean_object*);
lean_object* l_Nat_mforAux___main___at_Lean_IR_EmitC_emitReset___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitMainFn___closed__3;
lean_object* l_Lean_IR_EmitC_emitUProj(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitReuse___closed__1;
lean_object* l_Lean_IR_EmitC_emitCInitName(lean_object*, lean_object*, lean_object*);
lean_object* l_HashMapImp_find___at_Lean_IR_EmitC_getJPParams___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitDeclAux___closed__3;
lean_object* l_Lean_IR_EmitC_emitFileHeader___closed__1;
lean_object* l_Lean_IR_EmitC_emitArgs(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitBlock___main___closed__1;
lean_object* l_Lean_IR_EmitC_emitBoxFn(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitFileFooter(lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitReset___closed__2;
lean_object* l_List_mfor___main___at_Lean_IR_EmitC_emitLns___spec__1(lean_object*);
extern lean_object* l_System_FilePath_dirName___closed__1;
lean_object* l_Lean_IR_EmitC_toCInitName(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_closureMaxArgs;
lean_object* l_List_mfor___main___at_Lean_IR_EmitC_emitLns___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Decl_name(lean_object*);
lean_object* l_Array_mforAux___main___at_Lean_IR_EmitC_emitInitFn___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitLhs(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_usesLeanNamespace(lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitBox___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitSetTag___closed__1;
lean_object* l_Lean_IR_EmitC_emitCtorScalarSize(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitDeclInit___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_exportAttr;
lean_object* l_Lean_IR_EmitC_emitMainFn___closed__40;
lean_object* l_Lean_IR_EmitC_emitBoxFn___closed__2;
lean_object* l_Lean_IR_findEnvDecl(lean_object*, lean_object*);
lean_object* l_HashMapImp_find___at_Lean_IR_EmitC_getJPParams___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Nat_mforAux___main___at_Lean_IR_EmitC_emitPartialApp___spec__1___closed__1;
size_t lean_usize_modn(size_t, lean_object*);
lean_object* l_Lean_IR_EmitC_throwUnknownVar___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitCName___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitSSet___closed__6;
lean_object* l_Lean_IR_EmitC_emitMainFn___closed__28;
lean_object* l_Lean_IR_EmitC_emitInitFn___closed__5;
lean_object* l_Lean_IR_EmitC_emitMainFn___closed__45;
lean_object* l_List_mfor___main___at_Lean_IR_EmitC_emitFnDecls___spec__5___closed__2;
extern lean_object* l_HashMap_Inhabited___closed__1;
lean_object* l_Nat_mforAux___main___at_Lean_IR_EmitC_emitTailCall___spec__2___closed__1;
lean_object* l_Lean_IR_EmitC_emitUnbox___closed__3;
lean_object* l_Lean_IR_EmitC_emitInitFn___closed__2;
lean_object* l_Lean_IR_EmitC_getDecl(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitFnDecls___boxed(lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitTailCall___closed__1;
extern lean_object* l_Lean_IR_VarId_HasToString___closed__1;
lean_object* l_Lean_IR_EmitC_emitTag(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_size(lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitSet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitFileHeader___closed__16;
lean_object* l_Lean_IR_EmitC_emitUnbox___closed__2;
lean_object* l_Lean_IR_EmitC_emitFileHeader___closed__25;
lean_object* l_List_foldl___main___at_Lean_IR_EmitC_emitFnDecls___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitInitFn___closed__1;
lean_object* l_Lean_IR_EmitC_throwInvalidExportName(lean_object*);
lean_object* l_Lean_IR_EmitC_emitMainFn___closed__8;
lean_object* l_Array_get(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mforAux___main___at_Lean_IR_EmitC_emitCase___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitReuse___closed__2;
lean_object* l_Lean_IR_EmitC_toCType___boxed(lean_object*);
lean_object* l_Nat_mforAux___main___at_Lean_IR_EmitC_emitDeclAux___spec__1___closed__3;
lean_object* l_Lean_IR_EmitC_emitCName(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_throwInvalidExportName___rarg___closed__1;
lean_object* l_Lean_IR_EmitC_emitDec___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emit___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitInc___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitMainFn___closed__7;
lean_object* l_Nat_mforAux___main___at_Lean_IR_EmitC_emitPartialApp___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_mforAux___main___at_Lean_IR_EmitC_emitPartialApp___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitFullApp___closed__1;
lean_object* l_Lean_IR_EmitC_emitIf___closed__1;
lean_object* l_Lean_Environment_imports(lean_object*);
lean_object* l_Lean_IR_EmitC_getJPParams(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_isTailCall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitExternDeclAux(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitFnBody___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitMainFn___closed__17;
lean_object* l_Lean_IR_EmitC_emitFileHeader___closed__8;
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
lean_object* l_Nat_mforAux___main___at_Lean_IR_EmitC_emitJmp___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitMainFn___closed__22;
lean_object* l_String_foldlAux___main___at_Lean_IR_EmitC_quoteString___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitIsShared___closed__1;
lean_object* l_RBNode_revFold___main___at_Lean_IR_EmitC_emitFnDecls___spec__4(lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitFnDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitBoxFn___closed__3;
lean_object* l_Lean_IR_EmitC_emitFullApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitDeclInit___closed__1;
lean_object* l_Lean_IR_EmitC_emitInitFn___boxed(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitInc(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitLn___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_getDecl___boxed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_IR_EmitC_emitFileHeader___closed__20;
lean_object* l_Lean_IR_EmitC_emitMainFn___closed__44;
lean_object* l_List_mfor___main___at_Lean_IR_EmitC_emitFns___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitLns(lean_object*);
lean_object* l_Lean_IR_EmitC_emitInitFn___closed__6;
lean_object* l_Lean_IR_EmitC_emitFileHeader(lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitFnBody___main___closed__1;
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitMainFn___closed__21;
lean_object* l_Lean_IR_EmitC_emitDeclInit(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitMainFn___closed__37;
lean_object* l_Nat_mforAux___main___at_Lean_IR_EmitC_emitJmp___spec__1___closed__1;
lean_object* l_Lean_IR_EmitC_getJPParams___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitIf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* l_Lean_IR_EmitC_argToCString___closed__1;
lean_object* l_Lean_IR_EmitC_emitJmp___closed__1;
lean_object* l_Lean_IR_EmitC_toCType___closed__6;
lean_object* l_Lean_IR_EmitC_emitFileHeader___closed__24;
lean_object* l_Lean_IR_EmitC_hasMainFn(lean_object*, lean_object*);
uint32_t l_Nat_digitChar(lean_object*);
uint8_t l_Nat_anyAux___main___at_Lean_IR_EmitC_overwriteParam___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_declareVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitFullApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mfor___main___at_Lean_IR_EmitC_emitMainFn___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitLns___at_Lean_IR_EmitC_emitMainFn___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitMainFn___closed__42;
lean_object* l_Lean_IR_EmitC_emitLhs___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_anyAux___main___at_Lean_IR_EmitC_overwriteParam___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mfor___main___at_Lean_IR_EmitC_emitFnDecls___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitFileHeader___closed__9;
lean_object* l_Lean_IR_EmitC_paramEqArg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_declareVars(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitDec___closed__2;
lean_object* l_Lean_IR_EmitC_emitCtorSetArgs(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitTailCall___closed__2;
lean_object* l_Array_mforAux___main___at_Lean_IR_EmitC_emitInitFn___spec__1___closed__1;
lean_object* l_Nat_mforAux___main___at_Lean_IR_EmitC_emitTailCall___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitPartialApp___closed__2;
lean_object* l_Lean_IR_EmitC_emitLns___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_RBTree_toList___at_Lean_IR_EmitC_emitFnDecls___spec__3___boxed(lean_object*);
lean_object* l_Lean_IR_EmitC_emitMainFn___closed__9;
lean_object* l_Lean_IR_EmitC_declareVars___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_IO_println___rarg___closed__1;
lean_object* l_List_map___main___at_Lean_IR_EmitC_toStringArgs___spec__1(lean_object*);
lean_object* l_Lean_IR_EmitC_emitBoxFn___closed__1;
lean_object* l_Lean_IR_EmitC_emitTailCall___closed__4;
lean_object* l_Lean_IR_EmitC_toCName(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitBlock___main(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitFileHeader___closed__7;
lean_object* l_Lean_IR_EmitC_overwriteParam___boxed(lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitTag___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_mforAux___main___at_Lean_IR_EmitC_emitTailCall___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_throwInvalidExportName___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitJmp___closed__2;
lean_object* l_Lean_IR_EmitC_emitProj(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_IRType_isObj(uint8_t);
lean_object* l_Lean_IR_EmitC_emitTailCall___closed__3;
lean_object* l_Lean_IR_emitC___closed__1;
lean_object* l_Lean_IR_EmitC_emitCtorSetArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_emitMainFn___closed__48;
lean_object* l_Lean_IR_EmitC_emitUSet___closed__1;
extern lean_object* l_Lean_IR_Arg_Inhabited;
lean_object* l_Lean_IR_EmitC_emitExternDeclAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_EmitC_toCType___closed__1;
lean_object* l_Lean_IR_EmitC_emitFileHeader___closed__5;
lean_object* l_Lean_IR_EmitC_emitCase___closed__2;
lean_object* l_Array_mforAux___main___at_Lean_IR_EmitC_emitCase___spec__1___closed__2;
lean_object* l_Lean_IR_EmitC_emitCInitName___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Unit_HasRepr___closed__1;
lean_object* l_Lean_IR_EmitC_toStringArgs(lean_object*);
lean_object* l_AssocList_find___main___at_Lean_IR_EmitC_getJPParams___spec__2(lean_object*, lean_object*);
lean_object* l_Nat_mforAux___main___at_Lean_IR_EmitC_emitDeclAux___spec__1___closed__2;
lean_object* l_Lean_IR_EmitC_emitNumLit(uint8_t, lean_object*, lean_object*, lean_object*);
extern lean_object* l_String_splitAux___main___closed__1;
lean_object* l_Lean_IR_EmitC_emitDel___closed__1;
lean_object* l_Lean_IR_EmitC_emitDeclInit___closed__3;
lean_object* lean_ir_emit_c(lean_object*, lean_object*);
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
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
lean_dec(x_4);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_ctor_set(x_2, 0, x_5);
return x_2;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
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
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
lean_dec(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_ctor_set(x_2, 0, x_5);
return x_2;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
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
lean_object* x_4; 
x_4 = l_Lean_IR_EmitC_getEnv(x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = l_Lean_IR_findEnvDecl(x_6, x_1);
lean_dec(x_6);
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
x_17 = l_Lean_IR_findEnvDecl(x_15, x_1);
lean_dec(x_15);
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
else
{
uint8_t x_27; 
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_4);
if (x_27 == 0)
{
return x_4;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_4, 0);
x_29 = lean_ctor_get(x_4, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_4);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
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
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_4, 1);
x_7 = lean_ctor_get(x_4, 0);
lean_dec(x_7);
x_8 = lean_apply_1(x_1, x_2);
x_9 = lean_string_append(x_6, x_8);
lean_dec(x_8);
x_10 = lean_box(0);
lean_ctor_set(x_4, 1, x_9);
lean_ctor_set(x_4, 0, x_10);
return x_4;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_4, 1);
lean_inc(x_11);
lean_dec(x_4);
x_12 = lean_apply_1(x_1, x_2);
x_13 = lean_string_append(x_11, x_12);
lean_dec(x_12);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
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
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_ctor_get(x_4, 1);
x_7 = lean_ctor_get(x_4, 0);
lean_dec(x_7);
x_8 = lean_apply_1(x_1, x_2);
x_9 = lean_string_append(x_6, x_8);
lean_dec(x_8);
x_10 = l_IO_println___rarg___closed__1;
x_11 = lean_string_append(x_9, x_10);
x_12 = lean_box(0);
lean_ctor_set(x_4, 1, x_11);
lean_ctor_set(x_4, 0, x_12);
return x_4;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_ctor_get(x_4, 1);
lean_inc(x_13);
lean_dec(x_4);
x_14 = lean_apply_1(x_1, x_2);
x_15 = lean_string_append(x_13, x_14);
lean_dec(x_14);
x_16 = l_IO_println___rarg___closed__1;
x_17 = lean_string_append(x_15, x_16);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
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
lean_object* l_List_mfor___main___at_Lean_IR_EmitC_emitLns___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_5; 
lean_dec(x_1);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 0);
lean_dec(x_6);
x_7 = lean_box(0);
lean_ctor_set(x_4, 0, x_7);
return x_4;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_4, 1);
lean_inc(x_8);
lean_dec(x_4);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
lean_dec(x_2);
x_13 = !lean_is_exclusive(x_4);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_14 = lean_ctor_get(x_4, 1);
x_15 = lean_ctor_get(x_4, 0);
lean_dec(x_15);
lean_inc(x_1);
x_16 = lean_apply_1(x_1, x_11);
x_17 = lean_string_append(x_14, x_16);
lean_dec(x_16);
x_18 = l_IO_println___rarg___closed__1;
x_19 = lean_string_append(x_17, x_18);
x_20 = lean_box(0);
lean_ctor_set(x_4, 1, x_19);
lean_ctor_set(x_4, 0, x_20);
x_2 = x_12;
goto _start;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_22 = lean_ctor_get(x_4, 1);
lean_inc(x_22);
lean_dec(x_4);
lean_inc(x_1);
x_23 = lean_apply_1(x_1, x_11);
x_24 = lean_string_append(x_22, x_23);
lean_dec(x_23);
x_25 = l_IO_println___rarg___closed__1;
x_26 = lean_string_append(x_24, x_25);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
x_2 = x_12;
x_4 = x_28;
goto _start;
}
}
}
}
lean_object* l_List_mfor___main___at_Lean_IR_EmitC_emitLns___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_mfor___main___at_Lean_IR_EmitC_emitLns___spec__1___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Lean_IR_EmitC_emitLns___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_mfor___main___at_Lean_IR_EmitC_emitLns___spec__1___rarg(x_1, x_2, x_3, x_4);
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
lean_object* l_List_mfor___main___at_Lean_IR_EmitC_emitLns___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_mfor___main___at_Lean_IR_EmitC_emitLns___spec__1___rarg(x_1, x_2, x_3, x_4);
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
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_ctor_get(x_3, 0);
lean_dec(x_6);
x_7 = l_Lean_IR_EmitC_argToCString(x_1);
x_8 = lean_string_append(x_5, x_7);
lean_dec(x_7);
x_9 = lean_box(0);
lean_ctor_set(x_3, 1, x_8);
lean_ctor_set(x_3, 0, x_9);
return x_3;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
lean_dec(x_3);
x_11 = l_Lean_IR_EmitC_argToCString(x_1);
x_12 = lean_string_append(x_10, x_11);
lean_dec(x_11);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
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
lean_object* l_Lean_IR_EmitC_toCType(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(x_1);
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_3; 
x_3 = l_Lean_IR_EmitC_toCType___closed__1;
return x_3;
}
case 1:
{
lean_object* x_4; 
x_4 = l_Lean_IR_EmitC_toCType___closed__2;
return x_4;
}
case 2:
{
lean_object* x_5; 
x_5 = l_Lean_IR_EmitC_toCType___closed__3;
return x_5;
}
case 3:
{
lean_object* x_6; 
x_6 = l_Lean_IR_EmitC_toCType___closed__4;
return x_6;
}
case 4:
{
lean_object* x_7; 
x_7 = l_Lean_IR_EmitC_toCType___closed__5;
return x_7;
}
case 5:
{
lean_object* x_8; 
x_8 = l_Lean_IR_EmitC_toCType___closed__6;
return x_8;
}
default: 
{
lean_object* x_9; 
lean_dec(x_2);
x_9 = l_Lean_IR_EmitC_toCType___closed__7;
return x_9;
}
}
}
}
lean_object* l_Lean_IR_EmitC_toCType___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_IR_EmitC_toCType(x_2);
return x_3;
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
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_3, 0);
lean_dec(x_5);
x_6 = l_System_FilePath_dirName___closed__1;
x_7 = l_Lean_Name_toStringWithSep___main(x_6, x_1);
x_8 = l_Lean_IR_EmitC_throwInvalidExportName___rarg___closed__1;
x_9 = lean_string_append(x_8, x_7);
lean_dec(x_7);
x_10 = l_Char_HasRepr___closed__1;
x_11 = lean_string_append(x_9, x_10);
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 0, x_11);
return x_3;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
lean_dec(x_3);
x_13 = l_System_FilePath_dirName___closed__1;
x_14 = l_Lean_Name_toStringWithSep___main(x_13, x_1);
x_15 = l_Lean_IR_EmitC_throwInvalidExportName___rarg___closed__1;
x_16 = lean_string_append(x_15, x_14);
lean_dec(x_14);
x_17 = l_Char_HasRepr___closed__1;
x_18 = lean_string_append(x_16, x_17);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_12);
return x_19;
}
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
lean_object* x_4; 
x_4 = l_Lean_IR_EmitC_getEnv(x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_box(0);
lean_inc(x_7);
lean_ctor_set(x_4, 0, x_8);
x_9 = l_Lean_exportAttr;
lean_inc(x_1);
x_10 = l_Lean_ParametricAttribute_getParam___at_Lean_isIOUnitInitFn___spec__1(x_9, x_6, x_1);
lean_dec(x_6);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; uint8_t x_12; 
lean_dec(x_4);
x_11 = l_Lean_IR_EmitC_toCName___closed__2;
x_12 = lean_name_dec_eq(x_1, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = l_Lean_IR_EmitC_toCName___closed__3;
x_14 = l_Lean_Name_mangle(x_1, x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_7);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_1);
x_16 = l_Lean_IR_EmitC_leanMainFn;
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_7);
return x_17;
}
}
else
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_10, 0);
lean_inc(x_18);
lean_dec(x_10);
if (lean_obj_tag(x_18) == 1)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_box(0);
x_22 = lean_name_dec_eq(x_19, x_21);
lean_dec(x_19);
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec(x_20);
lean_dec(x_7);
x_23 = l_Lean_IR_EmitC_throwInvalidExportName___rarg(x_1, x_2, x_4);
return x_23;
}
else
{
lean_object* x_24; 
lean_dec(x_4);
lean_dec(x_1);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_20);
lean_ctor_set(x_24, 1, x_7);
return x_24;
}
}
else
{
lean_object* x_25; 
lean_dec(x_18);
lean_dec(x_7);
x_25 = l_Lean_IR_EmitC_throwInvalidExportName___rarg(x_1, x_2, x_4);
return x_25;
}
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_26 = lean_ctor_get(x_4, 0);
x_27 = lean_ctor_get(x_4, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_4);
x_28 = lean_box(0);
lean_inc(x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
x_30 = l_Lean_exportAttr;
lean_inc(x_1);
x_31 = l_Lean_ParametricAttribute_getParam___at_Lean_isIOUnitInitFn___spec__1(x_30, x_26, x_1);
lean_dec(x_26);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; uint8_t x_33; 
lean_dec(x_29);
x_32 = l_Lean_IR_EmitC_toCName___closed__2;
x_33 = lean_name_dec_eq(x_1, x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = l_Lean_IR_EmitC_toCName___closed__3;
x_35 = l_Lean_Name_mangle(x_1, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_27);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_1);
x_37 = l_Lean_IR_EmitC_leanMainFn;
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_27);
return x_38;
}
}
else
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_31, 0);
lean_inc(x_39);
lean_dec(x_31);
if (lean_obj_tag(x_39) == 1)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = lean_box(0);
x_43 = lean_name_dec_eq(x_40, x_42);
lean_dec(x_40);
if (x_43 == 0)
{
lean_object* x_44; 
lean_dec(x_41);
lean_dec(x_27);
x_44 = l_Lean_IR_EmitC_throwInvalidExportName___rarg(x_1, x_2, x_29);
return x_44;
}
else
{
lean_object* x_45; 
lean_dec(x_29);
lean_dec(x_1);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_41);
lean_ctor_set(x_45, 1, x_27);
return x_45;
}
}
else
{
lean_object* x_46; 
lean_dec(x_39);
lean_dec(x_27);
x_46 = l_Lean_IR_EmitC_throwInvalidExportName___rarg(x_1, x_2, x_29);
return x_46;
}
}
}
}
else
{
uint8_t x_47; 
lean_dec(x_1);
x_47 = !lean_is_exclusive(x_4);
if (x_47 == 0)
{
return x_4;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_4, 0);
x_49 = lean_ctor_get(x_4, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_4);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
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
lean_object* x_4; 
x_4 = l_Lean_IR_EmitC_getEnv(x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_box(0);
lean_inc(x_7);
lean_ctor_set(x_4, 0, x_8);
x_9 = l_Lean_exportAttr;
lean_inc(x_1);
x_10 = l_Lean_ParametricAttribute_getParam___at_Lean_isIOUnitInitFn___spec__1(x_9, x_6, x_1);
lean_dec(x_6);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_4);
x_11 = l_Lean_IR_EmitC_toCName___closed__3;
x_12 = l_Lean_Name_mangle(x_1, x_11);
x_13 = l_Lean_IR_EmitC_toCInitName___closed__1;
x_14 = lean_string_append(x_13, x_12);
lean_dec(x_12);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_7);
return x_15;
}
else
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_10, 0);
lean_inc(x_16);
lean_dec(x_10);
if (lean_obj_tag(x_16) == 1)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_box(0);
x_20 = lean_name_dec_eq(x_17, x_19);
lean_dec(x_17);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_18);
lean_dec(x_7);
x_21 = l_Lean_IR_EmitC_throwInvalidExportName___rarg(x_1, x_2, x_4);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_4);
lean_dec(x_1);
x_22 = l_Lean_IR_EmitC_toCInitName___closed__1;
x_23 = lean_string_append(x_22, x_18);
lean_dec(x_18);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_7);
return x_24;
}
}
else
{
lean_object* x_25; 
lean_dec(x_16);
lean_dec(x_7);
x_25 = l_Lean_IR_EmitC_throwInvalidExportName___rarg(x_1, x_2, x_4);
return x_25;
}
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_26 = lean_ctor_get(x_4, 0);
x_27 = lean_ctor_get(x_4, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_4);
x_28 = lean_box(0);
lean_inc(x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
x_30 = l_Lean_exportAttr;
lean_inc(x_1);
x_31 = l_Lean_ParametricAttribute_getParam___at_Lean_isIOUnitInitFn___spec__1(x_30, x_26, x_1);
lean_dec(x_26);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_29);
x_32 = l_Lean_IR_EmitC_toCName___closed__3;
x_33 = l_Lean_Name_mangle(x_1, x_32);
x_34 = l_Lean_IR_EmitC_toCInitName___closed__1;
x_35 = lean_string_append(x_34, x_33);
lean_dec(x_33);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_27);
return x_36;
}
else
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_31, 0);
lean_inc(x_37);
lean_dec(x_31);
if (lean_obj_tag(x_37) == 1)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_box(0);
x_41 = lean_name_dec_eq(x_38, x_40);
lean_dec(x_38);
if (x_41 == 0)
{
lean_object* x_42; 
lean_dec(x_39);
lean_dec(x_27);
x_42 = l_Lean_IR_EmitC_throwInvalidExportName___rarg(x_1, x_2, x_29);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_29);
lean_dec(x_1);
x_43 = l_Lean_IR_EmitC_toCInitName___closed__1;
x_44 = lean_string_append(x_43, x_39);
lean_dec(x_39);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_27);
return x_45;
}
}
else
{
lean_object* x_46; 
lean_dec(x_37);
lean_dec(x_27);
x_46 = l_Lean_IR_EmitC_throwInvalidExportName___rarg(x_1, x_2, x_29);
return x_46;
}
}
}
}
else
{
uint8_t x_47; 
lean_dec(x_1);
x_47 = !lean_is_exclusive(x_4);
if (x_47 == 0)
{
return x_4;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_4, 0);
x_49 = lean_ctor_get(x_4, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_4);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
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
lean_object* l_Nat_mforAux___main___at_Lean_IR_EmitC_emitFnDeclAux___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_5);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_14 = lean_ctor_get(x_5, 1);
x_15 = lean_ctor_get(x_5, 0);
lean_dec(x_15);
x_16 = l_Lean_IR_paramInh;
x_17 = lean_array_get(x_16, x_1, x_11);
lean_dec(x_11);
x_18 = lean_ctor_get_uint8(x_17, sizeof(void*)*1 + 1);
lean_dec(x_17);
x_19 = l_Lean_IR_EmitC_toCType(x_18);
x_20 = lean_string_append(x_14, x_19);
lean_dec(x_19);
x_21 = lean_box(0);
lean_ctor_set(x_5, 1, x_20);
lean_ctor_set(x_5, 0, x_21);
x_3 = x_9;
goto _start;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_23 = lean_ctor_get(x_5, 1);
lean_inc(x_23);
lean_dec(x_5);
x_24 = l_Lean_IR_paramInh;
x_25 = lean_array_get(x_24, x_1, x_11);
lean_dec(x_11);
x_26 = lean_ctor_get_uint8(x_25, sizeof(void*)*1 + 1);
lean_dec(x_25);
x_27 = l_Lean_IR_EmitC_toCType(x_26);
x_28 = lean_string_append(x_23, x_27);
lean_dec(x_27);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
x_3 = x_9;
x_5 = x_30;
goto _start;
}
}
else
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_5);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_33 = lean_ctor_get(x_5, 1);
x_34 = lean_ctor_get(x_5, 0);
lean_dec(x_34);
x_35 = l_List_reprAux___main___rarg___closed__1;
x_36 = lean_string_append(x_33, x_35);
x_37 = l_Lean_IR_paramInh;
x_38 = lean_array_get(x_37, x_1, x_11);
lean_dec(x_11);
x_39 = lean_ctor_get_uint8(x_38, sizeof(void*)*1 + 1);
lean_dec(x_38);
x_40 = l_Lean_IR_EmitC_toCType(x_39);
x_41 = lean_string_append(x_36, x_40);
lean_dec(x_40);
x_42 = lean_box(0);
lean_ctor_set(x_5, 1, x_41);
lean_ctor_set(x_5, 0, x_42);
x_3 = x_9;
goto _start;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_44 = lean_ctor_get(x_5, 1);
lean_inc(x_44);
lean_dec(x_5);
x_45 = l_List_reprAux___main___rarg___closed__1;
x_46 = lean_string_append(x_44, x_45);
x_47 = l_Lean_IR_paramInh;
x_48 = lean_array_get(x_47, x_1, x_11);
lean_dec(x_11);
x_49 = lean_ctor_get_uint8(x_48, sizeof(void*)*1 + 1);
lean_dec(x_48);
x_50 = l_Lean_IR_EmitC_toCType(x_49);
x_51 = lean_string_append(x_46, x_50);
lean_dec(x_50);
x_52 = lean_box(0);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_51);
x_3 = x_9;
x_5 = x_53;
goto _start;
}
}
}
else
{
uint8_t x_55; 
lean_dec(x_3);
x_55 = !lean_is_exclusive(x_5);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_5, 0);
lean_dec(x_56);
x_57 = lean_box(0);
lean_ctor_set(x_5, 0, x_57);
return x_5;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_5, 1);
lean_inc(x_58);
lean_dec(x_5);
x_59 = lean_box(0);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_58);
return x_60;
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
lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_6 = l_Lean_IR_Decl_params(x_1);
x_7 = l_Array_isEmpty___rarg(x_6);
if (x_7 == 0)
{
lean_object* x_64; 
x_64 = lean_ctor_get(x_5, 1);
lean_inc(x_64);
lean_dec(x_5);
x_8 = x_64;
goto block_63;
}
else
{
if (x_3 == 0)
{
lean_object* x_65; 
x_65 = lean_ctor_get(x_5, 1);
lean_inc(x_65);
lean_dec(x_5);
x_8 = x_65;
goto block_63;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_5, 1);
lean_inc(x_66);
lean_dec(x_5);
x_67 = l_Lean_IR_formatDecl___closed__3;
x_68 = lean_string_append(x_66, x_67);
x_8 = x_68;
goto block_63;
}
}
block_63:
{
uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = l_Lean_IR_Decl_resultType(x_1);
x_10 = l_Lean_IR_EmitC_toCType(x_9);
x_11 = l_Lean_Format_flatten___main___closed__1;
x_12 = lean_string_append(x_10, x_11);
x_13 = lean_string_append(x_12, x_2);
x_14 = lean_string_append(x_8, x_13);
lean_dec(x_13);
if (x_7 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_44; uint8_t x_45; 
x_15 = l_Prod_HasRepr___rarg___closed__1;
x_16 = lean_string_append(x_14, x_15);
x_17 = lean_box(0);
lean_inc(x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = lean_array_get_size(x_6);
x_44 = l_Lean_closureMaxArgs;
x_45 = lean_nat_dec_lt(x_44, x_19);
if (x_45 == 0)
{
lean_dec(x_16);
x_20 = x_17;
goto block_43;
}
else
{
lean_object* x_46; uint8_t x_47; 
x_46 = l_Lean_IR_Decl_name(x_1);
x_47 = l_Lean_IR_ExplicitBoxing_isBoxedName(x_46);
lean_dec(x_46);
if (x_47 == 0)
{
lean_dec(x_16);
x_20 = x_17;
goto block_43;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_6);
x_48 = l_Lean_IR_EmitC_emitFnDeclAux___closed__1;
x_49 = lean_string_append(x_16, x_48);
x_50 = l_Option_HasRepr___rarg___closed__3;
x_51 = lean_string_append(x_49, x_50);
x_52 = l_Lean_IR_formatFnBody___main___closed__3;
x_53 = lean_string_append(x_51, x_52);
x_54 = l_IO_println___rarg___closed__1;
x_55 = lean_string_append(x_53, x_54);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_17);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
block_43:
{
lean_object* x_21; 
lean_dec(x_20);
lean_inc(x_19);
x_21 = l_Nat_mforAux___main___at_Lean_IR_EmitC_emitFnDeclAux___spec__1(x_6, x_19, x_19, x_4, x_18);
lean_dec(x_19);
lean_dec(x_6);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_23 = lean_ctor_get(x_21, 1);
x_24 = lean_ctor_get(x_21, 0);
lean_dec(x_24);
x_25 = l_Option_HasRepr___rarg___closed__3;
x_26 = lean_string_append(x_23, x_25);
x_27 = l_Lean_IR_formatFnBody___main___closed__3;
x_28 = lean_string_append(x_26, x_27);
x_29 = l_IO_println___rarg___closed__1;
x_30 = lean_string_append(x_28, x_29);
lean_ctor_set(x_21, 1, x_30);
lean_ctor_set(x_21, 0, x_17);
return x_21;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_31 = lean_ctor_get(x_21, 1);
lean_inc(x_31);
lean_dec(x_21);
x_32 = l_Option_HasRepr___rarg___closed__3;
x_33 = lean_string_append(x_31, x_32);
x_34 = l_Lean_IR_formatFnBody___main___closed__3;
x_35 = lean_string_append(x_33, x_34);
x_36 = l_IO_println___rarg___closed__1;
x_37 = lean_string_append(x_35, x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_17);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
else
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_21);
if (x_39 == 0)
{
return x_21;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_21, 0);
x_41 = lean_ctor_get(x_21, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_21);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_6);
x_57 = l_Lean_IR_formatFnBody___main___closed__3;
x_58 = lean_string_append(x_14, x_57);
x_59 = l_IO_println___rarg___closed__1;
x_60 = lean_string_append(x_58, x_59);
x_61 = lean_box(0);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_60);
return x_62;
}
}
}
}
lean_object* l_Nat_mforAux___main___at_Lean_IR_EmitC_emitFnDeclAux___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Nat_mforAux___main___at_Lean_IR_EmitC_emitFnDeclAux___spec__1(x_1, x_2, x_3, x_4, x_5);
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
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_box(0);
lean_ctor_set(x_6, 0, x_9);
x_10 = l_Lean_IR_EmitC_emitFnDeclAux(x_1, x_8, x_2, x_3, x_6);
lean_dec(x_8);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_6, 0);
x_12 = lean_ctor_get(x_6, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_6);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
x_15 = l_Lean_IR_EmitC_emitFnDeclAux(x_1, x_11, x_2, x_3, x_14);
lean_dec(x_11);
return x_15;
}
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_6);
if (x_16 == 0)
{
return x_6;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_6, 0);
x_18 = lean_ctor_get(x_6, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_6);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
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
lean_object* x_5; 
x_5 = l_Lean_IR_EmitC_getEnv(x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_box(0);
lean_ctor_set(x_5, 0, x_8);
x_9 = l_Lean_IR_Decl_name(x_1);
x_10 = l_Lean_isExternC(x_7, x_9);
lean_dec(x_7);
if (x_10 == 0)
{
uint8_t x_11; lean_object* x_12; 
x_11 = 1;
x_12 = l_Lean_IR_EmitC_emitFnDeclAux(x_1, x_2, x_11, x_3, x_5);
return x_12;
}
else
{
uint8_t x_13; lean_object* x_14; 
x_13 = 0;
x_14 = l_Lean_IR_EmitC_emitFnDeclAux(x_1, x_2, x_13, x_3, x_5);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_15 = lean_ctor_get(x_5, 0);
x_16 = lean_ctor_get(x_5, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_5);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = l_Lean_IR_Decl_name(x_1);
x_20 = l_Lean_isExternC(x_15, x_19);
lean_dec(x_15);
if (x_20 == 0)
{
uint8_t x_21; lean_object* x_22; 
x_21 = 1;
x_22 = l_Lean_IR_EmitC_emitFnDeclAux(x_1, x_2, x_21, x_3, x_18);
return x_22;
}
else
{
uint8_t x_23; lean_object* x_24; 
x_23 = 0;
x_24 = l_Lean_IR_EmitC_emitFnDeclAux(x_1, x_2, x_23, x_3, x_18);
return x_24;
}
}
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_5);
if (x_25 == 0)
{
return x_5;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_5, 0);
x_27 = lean_ctor_get(x_5, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_5);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
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
lean_object* _init_l_List_mfor___main___at_Lean_IR_EmitC_emitFnDecls___spec__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("c");
return x_1;
}
}
lean_object* _init_l_List_mfor___main___at_Lean_IR_EmitC_emitFnDecls___spec__5___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_List_mfor___main___at_Lean_IR_EmitC_emitFnDecls___spec__5___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_List_mfor___main___at_Lean_IR_EmitC_emitFnDecls___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_5, 0);
lean_dec(x_7);
x_8 = lean_box(0);
lean_ctor_set(x_5, 0, x_8);
return x_5;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_5, 1);
lean_inc(x_9);
lean_dec(x_5);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_3, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_3, 1);
lean_inc(x_13);
lean_dec(x_3);
lean_inc(x_12);
x_14 = l_Lean_IR_EmitC_getDecl(x_12, x_4, x_5);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_box(0);
lean_ctor_set(x_14, 0, x_17);
x_18 = l_Lean_IR_Decl_name(x_16);
x_19 = l_List_mfor___main___at_Lean_IR_EmitC_emitFnDecls___spec__5___closed__2;
x_20 = l_Lean_getExternNameFor(x_1, x_19, x_18);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = l_Lean_NameSet_contains(x_2, x_12);
lean_dec(x_12);
if (x_21 == 0)
{
uint8_t x_22; lean_object* x_23; 
x_22 = 1;
x_23 = l_Lean_IR_EmitC_emitFnDecl(x_16, x_22, x_4, x_14);
lean_dec(x_16);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_23, 0);
lean_dec(x_25);
lean_ctor_set(x_23, 0, x_17);
x_3 = x_13;
x_5 = x_23;
goto _start;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_23, 1);
lean_inc(x_27);
lean_dec(x_23);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_17);
lean_ctor_set(x_28, 1, x_27);
x_3 = x_13;
x_5 = x_28;
goto _start;
}
}
else
{
uint8_t x_30; 
lean_dec(x_13);
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
uint8_t x_34; lean_object* x_35; 
x_34 = 0;
x_35 = l_Lean_IR_EmitC_emitFnDecl(x_16, x_34, x_4, x_14);
lean_dec(x_16);
if (lean_obj_tag(x_35) == 0)
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_35, 0);
lean_dec(x_37);
lean_ctor_set(x_35, 0, x_17);
x_3 = x_13;
x_5 = x_35;
goto _start;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_35, 1);
lean_inc(x_39);
lean_dec(x_35);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_17);
lean_ctor_set(x_40, 1, x_39);
x_3 = x_13;
x_5 = x_40;
goto _start;
}
}
else
{
uint8_t x_42; 
lean_dec(x_13);
x_42 = !lean_is_exclusive(x_35);
if (x_42 == 0)
{
return x_35;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_35, 0);
x_44 = lean_ctor_get(x_35, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_35);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
else
{
lean_object* x_46; lean_object* x_47; 
lean_dec(x_12);
x_46 = lean_ctor_get(x_20, 0);
lean_inc(x_46);
lean_dec(x_20);
x_47 = l_Lean_IR_EmitC_emitExternDeclAux(x_16, x_46, x_4, x_14);
lean_dec(x_46);
lean_dec(x_16);
if (lean_obj_tag(x_47) == 0)
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_47, 0);
lean_dec(x_49);
lean_ctor_set(x_47, 0, x_17);
x_3 = x_13;
x_5 = x_47;
goto _start;
}
else
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_47, 1);
lean_inc(x_51);
lean_dec(x_47);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_17);
lean_ctor_set(x_52, 1, x_51);
x_3 = x_13;
x_5 = x_52;
goto _start;
}
}
else
{
uint8_t x_54; 
lean_dec(x_13);
x_54 = !lean_is_exclusive(x_47);
if (x_54 == 0)
{
return x_47;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_47, 0);
x_56 = lean_ctor_get(x_47, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_47);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_58 = lean_ctor_get(x_14, 0);
x_59 = lean_ctor_get(x_14, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_14);
x_60 = lean_box(0);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_59);
x_62 = l_Lean_IR_Decl_name(x_58);
x_63 = l_List_mfor___main___at_Lean_IR_EmitC_emitFnDecls___spec__5___closed__2;
x_64 = l_Lean_getExternNameFor(x_1, x_63, x_62);
if (lean_obj_tag(x_64) == 0)
{
uint8_t x_65; 
x_65 = l_Lean_NameSet_contains(x_2, x_12);
lean_dec(x_12);
if (x_65 == 0)
{
uint8_t x_66; lean_object* x_67; 
x_66 = 1;
x_67 = l_Lean_IR_EmitC_emitFnDecl(x_58, x_66, x_4, x_61);
lean_dec(x_58);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_67, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_69 = x_67;
} else {
 lean_dec_ref(x_67);
 x_69 = lean_box(0);
}
if (lean_is_scalar(x_69)) {
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_69;
}
lean_ctor_set(x_70, 0, x_60);
lean_ctor_set(x_70, 1, x_68);
x_3 = x_13;
x_5 = x_70;
goto _start;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_13);
x_72 = lean_ctor_get(x_67, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_67, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_74 = x_67;
} else {
 lean_dec_ref(x_67);
 x_74 = lean_box(0);
}
if (lean_is_scalar(x_74)) {
 x_75 = lean_alloc_ctor(1, 2, 0);
} else {
 x_75 = x_74;
}
lean_ctor_set(x_75, 0, x_72);
lean_ctor_set(x_75, 1, x_73);
return x_75;
}
}
else
{
uint8_t x_76; lean_object* x_77; 
x_76 = 0;
x_77 = l_Lean_IR_EmitC_emitFnDecl(x_58, x_76, x_4, x_61);
lean_dec(x_58);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_77, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 x_79 = x_77;
} else {
 lean_dec_ref(x_77);
 x_79 = lean_box(0);
}
if (lean_is_scalar(x_79)) {
 x_80 = lean_alloc_ctor(0, 2, 0);
} else {
 x_80 = x_79;
}
lean_ctor_set(x_80, 0, x_60);
lean_ctor_set(x_80, 1, x_78);
x_3 = x_13;
x_5 = x_80;
goto _start;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_13);
x_82 = lean_ctor_get(x_77, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_77, 1);
lean_inc(x_83);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 x_84 = x_77;
} else {
 lean_dec_ref(x_77);
 x_84 = lean_box(0);
}
if (lean_is_scalar(x_84)) {
 x_85 = lean_alloc_ctor(1, 2, 0);
} else {
 x_85 = x_84;
}
lean_ctor_set(x_85, 0, x_82);
lean_ctor_set(x_85, 1, x_83);
return x_85;
}
}
}
else
{
lean_object* x_86; lean_object* x_87; 
lean_dec(x_12);
x_86 = lean_ctor_get(x_64, 0);
lean_inc(x_86);
lean_dec(x_64);
x_87 = l_Lean_IR_EmitC_emitExternDeclAux(x_58, x_86, x_4, x_61);
lean_dec(x_86);
lean_dec(x_58);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_87, 1);
lean_inc(x_88);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 x_89 = x_87;
} else {
 lean_dec_ref(x_87);
 x_89 = lean_box(0);
}
if (lean_is_scalar(x_89)) {
 x_90 = lean_alloc_ctor(0, 2, 0);
} else {
 x_90 = x_89;
}
lean_ctor_set(x_90, 0, x_60);
lean_ctor_set(x_90, 1, x_88);
x_3 = x_13;
x_5 = x_90;
goto _start;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_13);
x_92 = lean_ctor_get(x_87, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_87, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 x_94 = x_87;
} else {
 lean_dec_ref(x_87);
 x_94 = lean_box(0);
}
if (lean_is_scalar(x_94)) {
 x_95 = lean_alloc_ctor(1, 2, 0);
} else {
 x_95 = x_94;
}
lean_ctor_set(x_95, 0, x_92);
lean_ctor_set(x_95, 1, x_93);
return x_95;
}
}
}
}
else
{
uint8_t x_96; 
lean_dec(x_13);
lean_dec(x_12);
x_96 = !lean_is_exclusive(x_14);
if (x_96 == 0)
{
return x_14;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_14, 0);
x_98 = lean_ctor_get(x_14, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_14);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
}
}
}
}
lean_object* l_Lean_IR_EmitC_emitFnDecls(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_EmitC_getEnv(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_box(0);
lean_ctor_set(x_3, 0, x_6);
x_7 = l_Lean_IR_declMapExt;
x_8 = l_Lean_SimplePersistentEnvExtension_getEntries___rarg(x_7, x_5);
x_9 = lean_box(0);
x_10 = l_List_foldl___main___at_Lean_IR_EmitC_emitFnDecls___spec__1(x_9, x_8);
lean_inc(x_5);
x_11 = l_List_foldl___main___at_Lean_IR_EmitC_emitFnDecls___spec__2(x_5, x_9, x_8);
x_12 = l_RBTree_toList___at_Lean_IR_EmitC_emitFnDecls___spec__3(x_11);
lean_dec(x_11);
x_13 = l_List_mfor___main___at_Lean_IR_EmitC_emitFnDecls___spec__5(x_5, x_10, x_12, x_1, x_3);
lean_dec(x_10);
lean_dec(x_5);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_14 = lean_ctor_get(x_3, 0);
x_15 = lean_ctor_get(x_3, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_3);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
x_18 = l_Lean_IR_declMapExt;
x_19 = l_Lean_SimplePersistentEnvExtension_getEntries___rarg(x_18, x_14);
x_20 = lean_box(0);
x_21 = l_List_foldl___main___at_Lean_IR_EmitC_emitFnDecls___spec__1(x_20, x_19);
lean_inc(x_14);
x_22 = l_List_foldl___main___at_Lean_IR_EmitC_emitFnDecls___spec__2(x_14, x_20, x_19);
x_23 = l_RBTree_toList___at_Lean_IR_EmitC_emitFnDecls___spec__3(x_22);
lean_dec(x_22);
x_24 = l_List_mfor___main___at_Lean_IR_EmitC_emitFnDecls___spec__5(x_14, x_21, x_23, x_1, x_17);
lean_dec(x_21);
lean_dec(x_14);
return x_24;
}
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_3);
if (x_25 == 0)
{
return x_3;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_3, 0);
x_27 = lean_ctor_get(x_3, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_3);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
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
lean_object* l_List_mfor___main___at_Lean_IR_EmitC_emitFnDecls___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_List_mfor___main___at_Lean_IR_EmitC_emitFnDecls___spec__5(x_1, x_2, x_3, x_4, x_5);
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
lean_object* l_List_mfor___main___at_Lean_IR_EmitC_emitMainFn___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
lean_dec(x_5);
x_6 = lean_box(0);
lean_ctor_set(x_3, 0, x_6);
return x_3;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_3, 1);
lean_inc(x_7);
lean_dec(x_3);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_ctor_get(x_1, 1);
x_13 = lean_ctor_get(x_3, 1);
x_14 = lean_ctor_get(x_3, 0);
lean_dec(x_14);
x_15 = lean_string_append(x_13, x_11);
x_16 = l_IO_println___rarg___closed__1;
x_17 = lean_string_append(x_15, x_16);
x_18 = lean_box(0);
lean_ctor_set(x_3, 1, x_17);
lean_ctor_set(x_3, 0, x_18);
x_1 = x_12;
goto _start;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_20 = lean_ctor_get(x_1, 0);
x_21 = lean_ctor_get(x_1, 1);
x_22 = lean_ctor_get(x_3, 1);
lean_inc(x_22);
lean_dec(x_3);
x_23 = lean_string_append(x_22, x_20);
x_24 = l_IO_println___rarg___closed__1;
x_25 = lean_string_append(x_23, x_24);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
x_1 = x_21;
x_3 = x_27;
goto _start;
}
}
}
}
lean_object* l_Lean_IR_EmitC_emitLns___at_Lean_IR_EmitC_emitMainFn___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_mfor___main___at_Lean_IR_EmitC_emitMainFn___spec__2(x_1, x_2, x_3);
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
x_1 = lean_mk_string("w = lean_io_mk_world();");
return x_1;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("w = initialize_");
return x_1;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("(w);");
return x_1;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("lean_init_task_manager();");
return x_1;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_IR_EmitC_emitMainFn___closed__5;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("if (lean_io_result_is_ok(w)) {");
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
x_1 = lean_mk_string("lean_io_mark_end_initialization();");
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
x_1 = lean_mk_string("w = ");
return x_1;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_EmitC_emitMainFn___closed__11;
x_2 = l_Lean_IR_EmitC_leanMainFn;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_EmitC_emitMainFn___closed__12;
x_2 = l_Lean_IR_EmitC_emitMainFn___closed__4;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_PersistentHashMap_Stats_toString___closed__5;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("  return 1;");
return x_1;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_EmitC_emitMainFn___closed__15;
x_2 = l_Lean_IR_EmitC_emitMainFn___closed__14;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("  lean_dec_ref(w);");
return x_1;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_EmitC_emitMainFn___closed__17;
x_2 = l_Lean_IR_EmitC_emitMainFn___closed__16;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("  lean_io_result_show_error(w);");
return x_1;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_EmitC_emitMainFn___closed__19;
x_2 = l_Lean_IR_EmitC_emitMainFn___closed__18;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__21() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("} else {");
return x_1;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_EmitC_emitMainFn___closed__21;
x_2 = l_Lean_IR_EmitC_emitMainFn___closed__20;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__23() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("  return ret;");
return x_1;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_EmitC_emitMainFn___closed__23;
x_2 = l_Lean_IR_EmitC_emitMainFn___closed__22;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_EmitC_emitMainFn___closed__17;
x_2 = l_Lean_IR_EmitC_emitMainFn___closed__24;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__26() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("  int ret = lean_unbox(lean_io_result_get_value(w));");
return x_1;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_EmitC_emitMainFn___closed__26;
x_2 = l_Lean_IR_EmitC_emitMainFn___closed__25;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__28() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_EmitC_emitMainFn___closed__7;
x_2 = l_Lean_IR_EmitC_emitMainFn___closed__27;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__29() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("void lean_initialize_runtime_module();");
return x_1;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__30() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("int main(int argc, char ** argv) {\nlean_object* w; lean_object* in;");
return x_1;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__31() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("lean_initialize_runtime_module();");
return x_1;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__32() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("void lean_initialize();");
return x_1;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__33() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("lean_initialize();");
return x_1;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__34() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" in = n;");
return x_1;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__35() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_EmitC_emitMainFn___closed__34;
x_2 = l_Lean_IR_EmitC_emitMainFn___closed__14;
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
x_1 = lean_mk_string(" n = lean_alloc_ctor(1,2,0); lean_ctor_set(n, 0, lean_mk_string(argv[i])); lean_ctor_set(n, 1, in);");
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
x_1 = lean_mk_string(" i--;");
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
x_1 = lean_mk_string(" lean_object* n;");
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
x_1 = lean_mk_string("while (i > 1) {");
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
x_1 = lean_mk_string("int i = argc;");
return x_1;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__45() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_EmitC_emitMainFn___closed__44;
x_2 = l_Lean_IR_EmitC_emitMainFn___closed__43;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__46() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("in = lean_box(0);");
return x_1;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__47() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_EmitC_emitMainFn___closed__46;
x_2 = l_Lean_IR_EmitC_emitMainFn___closed__45;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__48() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("(in, w);");
return x_1;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__49() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_EmitC_emitMainFn___closed__12;
x_2 = l_Lean_IR_EmitC_emitMainFn___closed__48;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitMainFn___closed__50() {
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
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_ctor_get(x_4, 0);
lean_dec(x_7);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
x_9 = lean_array_get_size(x_8);
lean_dec(x_8);
x_10 = lean_unsigned_to_nat(2u);
x_11 = lean_nat_dec_eq(x_9, x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_dec_eq(x_9, x_12);
lean_dec(x_9);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_5);
x_14 = l_Lean_IR_EmitC_emitMainFn___closed__1;
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_14);
return x_4;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_125; 
x_15 = lean_box(0);
lean_ctor_set(x_4, 0, x_15);
x_125 = l_Lean_IR_EmitC_getEnv(x_1, x_4);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; uint8_t x_129; 
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_125, 1);
lean_inc(x_127);
lean_dec(x_125);
x_128 = l_Lean_IR_usesLeanNamespace(x_126, x_5);
lean_dec(x_126);
x_129 = lean_unbox(x_128);
lean_dec(x_128);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_130 = l_Lean_IR_EmitC_emitMainFn___closed__29;
x_131 = lean_string_append(x_127, x_130);
x_132 = l_IO_println___rarg___closed__1;
x_133 = lean_string_append(x_131, x_132);
x_134 = l_Lean_IR_EmitC_emitMainFn___closed__30;
x_135 = lean_string_append(x_133, x_134);
x_136 = lean_string_append(x_135, x_132);
x_137 = l_Lean_IR_EmitC_emitMainFn___closed__31;
x_138 = lean_string_append(x_136, x_137);
x_139 = lean_string_append(x_138, x_132);
x_16 = x_139;
goto block_124;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_140 = l_Lean_IR_EmitC_emitMainFn___closed__32;
x_141 = lean_string_append(x_127, x_140);
x_142 = l_IO_println___rarg___closed__1;
x_143 = lean_string_append(x_141, x_142);
x_144 = l_Lean_IR_EmitC_emitMainFn___closed__30;
x_145 = lean_string_append(x_143, x_144);
x_146 = lean_string_append(x_145, x_142);
x_147 = l_Lean_IR_EmitC_emitMainFn___closed__33;
x_148 = lean_string_append(x_146, x_147);
x_149 = lean_string_append(x_148, x_142);
x_16 = x_149;
goto block_124;
}
}
else
{
uint8_t x_150; 
lean_dec(x_5);
x_150 = !lean_is_exclusive(x_125);
if (x_150 == 0)
{
return x_125;
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_151 = lean_ctor_get(x_125, 0);
x_152 = lean_ctor_get(x_125, 1);
lean_inc(x_152);
lean_inc(x_151);
lean_dec(x_125);
x_153 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_153, 0, x_151);
lean_ctor_set(x_153, 1, x_152);
return x_153;
}
}
block_124:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_17 = l_Lean_IR_EmitC_emitMainFn___closed__2;
x_18 = lean_string_append(x_16, x_17);
x_19 = l_IO_println___rarg___closed__1;
x_20 = lean_string_append(x_18, x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_15);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_Lean_IR_EmitC_getModName(x_1, x_21);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_ctor_get(x_22, 1);
x_26 = l_String_splitAux___main___closed__1;
x_27 = l_Lean_Name_mangle(x_24, x_26);
x_28 = l_Lean_IR_EmitC_emitMainFn___closed__3;
x_29 = lean_string_append(x_28, x_27);
lean_dec(x_27);
x_30 = l_Lean_IR_EmitC_emitMainFn___closed__4;
x_31 = lean_string_append(x_29, x_30);
x_32 = lean_string_append(x_25, x_31);
lean_dec(x_31);
x_33 = lean_string_append(x_32, x_19);
lean_ctor_set(x_22, 1, x_33);
lean_ctor_set(x_22, 0, x_15);
x_34 = l_Lean_IR_EmitC_emitMainFn___closed__10;
x_35 = l_List_mfor___main___at_Lean_IR_EmitC_emitMainFn___spec__2(x_34, x_1, x_22);
if (lean_obj_tag(x_35) == 0)
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_37 = lean_ctor_get(x_35, 1);
x_38 = lean_ctor_get(x_35, 0);
lean_dec(x_38);
x_39 = l_Lean_IR_EmitC_emitMainFn___closed__13;
x_40 = lean_string_append(x_37, x_39);
x_41 = lean_string_append(x_40, x_19);
x_42 = l_PersistentHashMap_Stats_toString___closed__5;
x_43 = lean_string_append(x_41, x_42);
x_44 = lean_string_append(x_43, x_19);
lean_ctor_set(x_35, 1, x_44);
lean_ctor_set(x_35, 0, x_15);
x_45 = l_Lean_IR_EmitC_emitMainFn___closed__28;
x_46 = l_List_mfor___main___at_Lean_IR_EmitC_emitMainFn___spec__2(x_45, x_1, x_35);
if (lean_obj_tag(x_46) == 0)
{
uint8_t x_47; 
x_47 = !lean_is_exclusive(x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_48 = lean_ctor_get(x_46, 1);
x_49 = lean_ctor_get(x_46, 0);
lean_dec(x_49);
x_50 = lean_string_append(x_48, x_42);
x_51 = lean_string_append(x_50, x_19);
lean_ctor_set(x_46, 1, x_51);
lean_ctor_set(x_46, 0, x_15);
return x_46;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_52 = lean_ctor_get(x_46, 1);
lean_inc(x_52);
lean_dec(x_46);
x_53 = lean_string_append(x_52, x_42);
x_54 = lean_string_append(x_53, x_19);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_15);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
else
{
uint8_t x_56; 
x_56 = !lean_is_exclusive(x_46);
if (x_56 == 0)
{
return x_46;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_46, 0);
x_58 = lean_ctor_get(x_46, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_46);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_60 = lean_ctor_get(x_35, 1);
lean_inc(x_60);
lean_dec(x_35);
x_61 = l_Lean_IR_EmitC_emitMainFn___closed__13;
x_62 = lean_string_append(x_60, x_61);
x_63 = lean_string_append(x_62, x_19);
x_64 = l_PersistentHashMap_Stats_toString___closed__5;
x_65 = lean_string_append(x_63, x_64);
x_66 = lean_string_append(x_65, x_19);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_15);
lean_ctor_set(x_67, 1, x_66);
x_68 = l_Lean_IR_EmitC_emitMainFn___closed__28;
x_69 = l_List_mfor___main___at_Lean_IR_EmitC_emitMainFn___spec__2(x_68, x_1, x_67);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_71 = x_69;
} else {
 lean_dec_ref(x_69);
 x_71 = lean_box(0);
}
x_72 = lean_string_append(x_70, x_64);
x_73 = lean_string_append(x_72, x_19);
if (lean_is_scalar(x_71)) {
 x_74 = lean_alloc_ctor(0, 2, 0);
} else {
 x_74 = x_71;
}
lean_ctor_set(x_74, 0, x_15);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_75 = lean_ctor_get(x_69, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_69, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_77 = x_69;
} else {
 lean_dec_ref(x_69);
 x_77 = lean_box(0);
}
if (lean_is_scalar(x_77)) {
 x_78 = lean_alloc_ctor(1, 2, 0);
} else {
 x_78 = x_77;
}
lean_ctor_set(x_78, 0, x_75);
lean_ctor_set(x_78, 1, x_76);
return x_78;
}
}
}
else
{
uint8_t x_79; 
x_79 = !lean_is_exclusive(x_35);
if (x_79 == 0)
{
return x_35;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_35, 0);
x_81 = lean_ctor_get(x_35, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_35);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_83 = lean_ctor_get(x_22, 0);
x_84 = lean_ctor_get(x_22, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_22);
x_85 = l_String_splitAux___main___closed__1;
x_86 = l_Lean_Name_mangle(x_83, x_85);
x_87 = l_Lean_IR_EmitC_emitMainFn___closed__3;
x_88 = lean_string_append(x_87, x_86);
lean_dec(x_86);
x_89 = l_Lean_IR_EmitC_emitMainFn___closed__4;
x_90 = lean_string_append(x_88, x_89);
x_91 = lean_string_append(x_84, x_90);
lean_dec(x_90);
x_92 = lean_string_append(x_91, x_19);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_15);
lean_ctor_set(x_93, 1, x_92);
x_94 = l_Lean_IR_EmitC_emitMainFn___closed__10;
x_95 = l_List_mfor___main___at_Lean_IR_EmitC_emitMainFn___spec__2(x_94, x_1, x_93);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_96 = lean_ctor_get(x_95, 1);
lean_inc(x_96);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 x_97 = x_95;
} else {
 lean_dec_ref(x_95);
 x_97 = lean_box(0);
}
x_98 = l_Lean_IR_EmitC_emitMainFn___closed__13;
x_99 = lean_string_append(x_96, x_98);
x_100 = lean_string_append(x_99, x_19);
x_101 = l_PersistentHashMap_Stats_toString___closed__5;
x_102 = lean_string_append(x_100, x_101);
x_103 = lean_string_append(x_102, x_19);
if (lean_is_scalar(x_97)) {
 x_104 = lean_alloc_ctor(0, 2, 0);
} else {
 x_104 = x_97;
}
lean_ctor_set(x_104, 0, x_15);
lean_ctor_set(x_104, 1, x_103);
x_105 = l_Lean_IR_EmitC_emitMainFn___closed__28;
x_106 = l_List_mfor___main___at_Lean_IR_EmitC_emitMainFn___spec__2(x_105, x_1, x_104);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_107 = lean_ctor_get(x_106, 1);
lean_inc(x_107);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 lean_ctor_release(x_106, 1);
 x_108 = x_106;
} else {
 lean_dec_ref(x_106);
 x_108 = lean_box(0);
}
x_109 = lean_string_append(x_107, x_101);
x_110 = lean_string_append(x_109, x_19);
if (lean_is_scalar(x_108)) {
 x_111 = lean_alloc_ctor(0, 2, 0);
} else {
 x_111 = x_108;
}
lean_ctor_set(x_111, 0, x_15);
lean_ctor_set(x_111, 1, x_110);
return x_111;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_112 = lean_ctor_get(x_106, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_106, 1);
lean_inc(x_113);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 lean_ctor_release(x_106, 1);
 x_114 = x_106;
} else {
 lean_dec_ref(x_106);
 x_114 = lean_box(0);
}
if (lean_is_scalar(x_114)) {
 x_115 = lean_alloc_ctor(1, 2, 0);
} else {
 x_115 = x_114;
}
lean_ctor_set(x_115, 0, x_112);
lean_ctor_set(x_115, 1, x_113);
return x_115;
}
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_116 = lean_ctor_get(x_95, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_95, 1);
lean_inc(x_117);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 x_118 = x_95;
} else {
 lean_dec_ref(x_95);
 x_118 = lean_box(0);
}
if (lean_is_scalar(x_118)) {
 x_119 = lean_alloc_ctor(1, 2, 0);
} else {
 x_119 = x_118;
}
lean_ctor_set(x_119, 0, x_116);
lean_ctor_set(x_119, 1, x_117);
return x_119;
}
}
}
else
{
uint8_t x_120; 
x_120 = !lean_is_exclusive(x_22);
if (x_120 == 0)
{
return x_22;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_22, 0);
x_122 = lean_ctor_get(x_22, 1);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_22);
x_123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_122);
return x_123;
}
}
}
}
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_284; 
lean_dec(x_9);
x_154 = lean_box(0);
lean_ctor_set(x_4, 0, x_154);
x_284 = l_Lean_IR_EmitC_getEnv(x_1, x_4);
if (lean_obj_tag(x_284) == 0)
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; uint8_t x_288; 
x_285 = lean_ctor_get(x_284, 0);
lean_inc(x_285);
x_286 = lean_ctor_get(x_284, 1);
lean_inc(x_286);
lean_dec(x_284);
x_287 = l_Lean_IR_usesLeanNamespace(x_285, x_5);
lean_dec(x_285);
x_288 = lean_unbox(x_287);
lean_dec(x_287);
if (x_288 == 0)
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; 
x_289 = l_Lean_IR_EmitC_emitMainFn___closed__29;
x_290 = lean_string_append(x_286, x_289);
x_291 = l_IO_println___rarg___closed__1;
x_292 = lean_string_append(x_290, x_291);
x_293 = l_Lean_IR_EmitC_emitMainFn___closed__30;
x_294 = lean_string_append(x_292, x_293);
x_295 = lean_string_append(x_294, x_291);
x_296 = l_Lean_IR_EmitC_emitMainFn___closed__31;
x_297 = lean_string_append(x_295, x_296);
x_298 = lean_string_append(x_297, x_291);
x_155 = x_298;
goto block_283;
}
else
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; 
x_299 = l_Lean_IR_EmitC_emitMainFn___closed__32;
x_300 = lean_string_append(x_286, x_299);
x_301 = l_IO_println___rarg___closed__1;
x_302 = lean_string_append(x_300, x_301);
x_303 = l_Lean_IR_EmitC_emitMainFn___closed__30;
x_304 = lean_string_append(x_302, x_303);
x_305 = lean_string_append(x_304, x_301);
x_306 = l_Lean_IR_EmitC_emitMainFn___closed__33;
x_307 = lean_string_append(x_305, x_306);
x_308 = lean_string_append(x_307, x_301);
x_155 = x_308;
goto block_283;
}
}
else
{
uint8_t x_309; 
lean_dec(x_5);
x_309 = !lean_is_exclusive(x_284);
if (x_309 == 0)
{
return x_284;
}
else
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; 
x_310 = lean_ctor_get(x_284, 0);
x_311 = lean_ctor_get(x_284, 1);
lean_inc(x_311);
lean_inc(x_310);
lean_dec(x_284);
x_312 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_312, 0, x_310);
lean_ctor_set(x_312, 1, x_311);
return x_312;
}
}
block_283:
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_156 = l_Lean_IR_EmitC_emitMainFn___closed__2;
x_157 = lean_string_append(x_155, x_156);
x_158 = l_IO_println___rarg___closed__1;
x_159 = lean_string_append(x_157, x_158);
x_160 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_160, 0, x_154);
lean_ctor_set(x_160, 1, x_159);
x_161 = l_Lean_IR_EmitC_getModName(x_1, x_160);
if (lean_obj_tag(x_161) == 0)
{
uint8_t x_162; 
x_162 = !lean_is_exclusive(x_161);
if (x_162 == 0)
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_194; lean_object* x_195; 
x_163 = lean_ctor_get(x_161, 0);
x_164 = lean_ctor_get(x_161, 1);
x_165 = l_String_splitAux___main___closed__1;
x_166 = l_Lean_Name_mangle(x_163, x_165);
x_167 = l_Lean_IR_EmitC_emitMainFn___closed__3;
x_168 = lean_string_append(x_167, x_166);
lean_dec(x_166);
x_169 = l_Lean_IR_EmitC_emitMainFn___closed__4;
x_170 = lean_string_append(x_168, x_169);
x_171 = lean_string_append(x_164, x_170);
lean_dec(x_170);
x_172 = lean_string_append(x_171, x_158);
lean_ctor_set(x_161, 1, x_172);
lean_ctor_set(x_161, 0, x_154);
x_194 = l_Lean_IR_EmitC_emitMainFn___closed__10;
x_195 = l_List_mfor___main___at_Lean_IR_EmitC_emitMainFn___spec__2(x_194, x_1, x_161);
if (lean_obj_tag(x_195) == 0)
{
if (x_11 == 0)
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_196 = lean_ctor_get(x_195, 1);
lean_inc(x_196);
lean_dec(x_195);
x_197 = l_Lean_IR_EmitC_emitMainFn___closed__13;
x_198 = lean_string_append(x_196, x_197);
x_199 = lean_string_append(x_198, x_158);
x_173 = x_199;
goto block_193;
}
else
{
uint8_t x_200; 
x_200 = !lean_is_exclusive(x_195);
if (x_200 == 0)
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_201 = lean_ctor_get(x_195, 0);
lean_dec(x_201);
lean_ctor_set(x_195, 0, x_154);
x_202 = l_Lean_IR_EmitC_emitMainFn___closed__47;
x_203 = l_List_mfor___main___at_Lean_IR_EmitC_emitMainFn___spec__2(x_202, x_1, x_195);
if (lean_obj_tag(x_203) == 0)
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_204 = lean_ctor_get(x_203, 1);
lean_inc(x_204);
lean_dec(x_203);
x_205 = l_Lean_IR_EmitC_emitMainFn___closed__49;
x_206 = lean_string_append(x_204, x_205);
x_207 = lean_string_append(x_206, x_158);
x_173 = x_207;
goto block_193;
}
else
{
uint8_t x_208; 
x_208 = !lean_is_exclusive(x_203);
if (x_208 == 0)
{
return x_203;
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; 
x_209 = lean_ctor_get(x_203, 0);
x_210 = lean_ctor_get(x_203, 1);
lean_inc(x_210);
lean_inc(x_209);
lean_dec(x_203);
x_211 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_211, 0, x_209);
lean_ctor_set(x_211, 1, x_210);
return x_211;
}
}
}
else
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_212 = lean_ctor_get(x_195, 1);
lean_inc(x_212);
lean_dec(x_195);
x_213 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_213, 0, x_154);
lean_ctor_set(x_213, 1, x_212);
x_214 = l_Lean_IR_EmitC_emitMainFn___closed__47;
x_215 = l_List_mfor___main___at_Lean_IR_EmitC_emitMainFn___spec__2(x_214, x_1, x_213);
if (lean_obj_tag(x_215) == 0)
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; 
x_216 = lean_ctor_get(x_215, 1);
lean_inc(x_216);
lean_dec(x_215);
x_217 = l_Lean_IR_EmitC_emitMainFn___closed__49;
x_218 = lean_string_append(x_216, x_217);
x_219 = lean_string_append(x_218, x_158);
x_173 = x_219;
goto block_193;
}
else
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; 
x_220 = lean_ctor_get(x_215, 0);
lean_inc(x_220);
x_221 = lean_ctor_get(x_215, 1);
lean_inc(x_221);
if (lean_is_exclusive(x_215)) {
 lean_ctor_release(x_215, 0);
 lean_ctor_release(x_215, 1);
 x_222 = x_215;
} else {
 lean_dec_ref(x_215);
 x_222 = lean_box(0);
}
if (lean_is_scalar(x_222)) {
 x_223 = lean_alloc_ctor(1, 2, 0);
} else {
 x_223 = x_222;
}
lean_ctor_set(x_223, 0, x_220);
lean_ctor_set(x_223, 1, x_221);
return x_223;
}
}
}
}
else
{
uint8_t x_224; 
x_224 = !lean_is_exclusive(x_195);
if (x_224 == 0)
{
return x_195;
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; 
x_225 = lean_ctor_get(x_195, 0);
x_226 = lean_ctor_get(x_195, 1);
lean_inc(x_226);
lean_inc(x_225);
lean_dec(x_195);
x_227 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_227, 0, x_225);
lean_ctor_set(x_227, 1, x_226);
return x_227;
}
}
block_193:
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_174 = l_PersistentHashMap_Stats_toString___closed__5;
x_175 = lean_string_append(x_173, x_174);
x_176 = lean_string_append(x_175, x_158);
x_177 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_177, 0, x_154);
lean_ctor_set(x_177, 1, x_176);
x_178 = l_Lean_IR_EmitC_emitMainFn___closed__28;
x_179 = l_List_mfor___main___at_Lean_IR_EmitC_emitMainFn___spec__2(x_178, x_1, x_177);
if (lean_obj_tag(x_179) == 0)
{
uint8_t x_180; 
x_180 = !lean_is_exclusive(x_179);
if (x_180 == 0)
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_181 = lean_ctor_get(x_179, 1);
x_182 = lean_ctor_get(x_179, 0);
lean_dec(x_182);
x_183 = lean_string_append(x_181, x_174);
x_184 = lean_string_append(x_183, x_158);
lean_ctor_set(x_179, 1, x_184);
lean_ctor_set(x_179, 0, x_154);
return x_179;
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_185 = lean_ctor_get(x_179, 1);
lean_inc(x_185);
lean_dec(x_179);
x_186 = lean_string_append(x_185, x_174);
x_187 = lean_string_append(x_186, x_158);
x_188 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_188, 0, x_154);
lean_ctor_set(x_188, 1, x_187);
return x_188;
}
}
else
{
uint8_t x_189; 
x_189 = !lean_is_exclusive(x_179);
if (x_189 == 0)
{
return x_179;
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_190 = lean_ctor_get(x_179, 0);
x_191 = lean_ctor_get(x_179, 1);
lean_inc(x_191);
lean_inc(x_190);
lean_dec(x_179);
x_192 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_192, 0, x_190);
lean_ctor_set(x_192, 1, x_191);
return x_192;
}
}
}
}
else
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_256; lean_object* x_257; 
x_228 = lean_ctor_get(x_161, 0);
x_229 = lean_ctor_get(x_161, 1);
lean_inc(x_229);
lean_inc(x_228);
lean_dec(x_161);
x_230 = l_String_splitAux___main___closed__1;
x_231 = l_Lean_Name_mangle(x_228, x_230);
x_232 = l_Lean_IR_EmitC_emitMainFn___closed__3;
x_233 = lean_string_append(x_232, x_231);
lean_dec(x_231);
x_234 = l_Lean_IR_EmitC_emitMainFn___closed__4;
x_235 = lean_string_append(x_233, x_234);
x_236 = lean_string_append(x_229, x_235);
lean_dec(x_235);
x_237 = lean_string_append(x_236, x_158);
x_238 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_238, 0, x_154);
lean_ctor_set(x_238, 1, x_237);
x_256 = l_Lean_IR_EmitC_emitMainFn___closed__10;
x_257 = l_List_mfor___main___at_Lean_IR_EmitC_emitMainFn___spec__2(x_256, x_1, x_238);
if (lean_obj_tag(x_257) == 0)
{
if (x_11 == 0)
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; 
x_258 = lean_ctor_get(x_257, 1);
lean_inc(x_258);
lean_dec(x_257);
x_259 = l_Lean_IR_EmitC_emitMainFn___closed__13;
x_260 = lean_string_append(x_258, x_259);
x_261 = lean_string_append(x_260, x_158);
x_239 = x_261;
goto block_255;
}
else
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; 
x_262 = lean_ctor_get(x_257, 1);
lean_inc(x_262);
if (lean_is_exclusive(x_257)) {
 lean_ctor_release(x_257, 0);
 lean_ctor_release(x_257, 1);
 x_263 = x_257;
} else {
 lean_dec_ref(x_257);
 x_263 = lean_box(0);
}
if (lean_is_scalar(x_263)) {
 x_264 = lean_alloc_ctor(0, 2, 0);
} else {
 x_264 = x_263;
}
lean_ctor_set(x_264, 0, x_154);
lean_ctor_set(x_264, 1, x_262);
x_265 = l_Lean_IR_EmitC_emitMainFn___closed__47;
x_266 = l_List_mfor___main___at_Lean_IR_EmitC_emitMainFn___spec__2(x_265, x_1, x_264);
if (lean_obj_tag(x_266) == 0)
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; 
x_267 = lean_ctor_get(x_266, 1);
lean_inc(x_267);
lean_dec(x_266);
x_268 = l_Lean_IR_EmitC_emitMainFn___closed__49;
x_269 = lean_string_append(x_267, x_268);
x_270 = lean_string_append(x_269, x_158);
x_239 = x_270;
goto block_255;
}
else
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; 
x_271 = lean_ctor_get(x_266, 0);
lean_inc(x_271);
x_272 = lean_ctor_get(x_266, 1);
lean_inc(x_272);
if (lean_is_exclusive(x_266)) {
 lean_ctor_release(x_266, 0);
 lean_ctor_release(x_266, 1);
 x_273 = x_266;
} else {
 lean_dec_ref(x_266);
 x_273 = lean_box(0);
}
if (lean_is_scalar(x_273)) {
 x_274 = lean_alloc_ctor(1, 2, 0);
} else {
 x_274 = x_273;
}
lean_ctor_set(x_274, 0, x_271);
lean_ctor_set(x_274, 1, x_272);
return x_274;
}
}
}
else
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; 
x_275 = lean_ctor_get(x_257, 0);
lean_inc(x_275);
x_276 = lean_ctor_get(x_257, 1);
lean_inc(x_276);
if (lean_is_exclusive(x_257)) {
 lean_ctor_release(x_257, 0);
 lean_ctor_release(x_257, 1);
 x_277 = x_257;
} else {
 lean_dec_ref(x_257);
 x_277 = lean_box(0);
}
if (lean_is_scalar(x_277)) {
 x_278 = lean_alloc_ctor(1, 2, 0);
} else {
 x_278 = x_277;
}
lean_ctor_set(x_278, 0, x_275);
lean_ctor_set(x_278, 1, x_276);
return x_278;
}
block_255:
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; 
x_240 = l_PersistentHashMap_Stats_toString___closed__5;
x_241 = lean_string_append(x_239, x_240);
x_242 = lean_string_append(x_241, x_158);
x_243 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_243, 0, x_154);
lean_ctor_set(x_243, 1, x_242);
x_244 = l_Lean_IR_EmitC_emitMainFn___closed__28;
x_245 = l_List_mfor___main___at_Lean_IR_EmitC_emitMainFn___spec__2(x_244, x_1, x_243);
if (lean_obj_tag(x_245) == 0)
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; 
x_246 = lean_ctor_get(x_245, 1);
lean_inc(x_246);
if (lean_is_exclusive(x_245)) {
 lean_ctor_release(x_245, 0);
 lean_ctor_release(x_245, 1);
 x_247 = x_245;
} else {
 lean_dec_ref(x_245);
 x_247 = lean_box(0);
}
x_248 = lean_string_append(x_246, x_240);
x_249 = lean_string_append(x_248, x_158);
if (lean_is_scalar(x_247)) {
 x_250 = lean_alloc_ctor(0, 2, 0);
} else {
 x_250 = x_247;
}
lean_ctor_set(x_250, 0, x_154);
lean_ctor_set(x_250, 1, x_249);
return x_250;
}
else
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; 
x_251 = lean_ctor_get(x_245, 0);
lean_inc(x_251);
x_252 = lean_ctor_get(x_245, 1);
lean_inc(x_252);
if (lean_is_exclusive(x_245)) {
 lean_ctor_release(x_245, 0);
 lean_ctor_release(x_245, 1);
 x_253 = x_245;
} else {
 lean_dec_ref(x_245);
 x_253 = lean_box(0);
}
if (lean_is_scalar(x_253)) {
 x_254 = lean_alloc_ctor(1, 2, 0);
} else {
 x_254 = x_253;
}
lean_ctor_set(x_254, 0, x_251);
lean_ctor_set(x_254, 1, x_252);
return x_254;
}
}
}
}
else
{
uint8_t x_279; 
x_279 = !lean_is_exclusive(x_161);
if (x_279 == 0)
{
return x_161;
}
else
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; 
x_280 = lean_ctor_get(x_161, 0);
x_281 = lean_ctor_get(x_161, 1);
lean_inc(x_281);
lean_inc(x_280);
lean_dec(x_161);
x_282 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_282, 0, x_280);
lean_ctor_set(x_282, 1, x_281);
return x_282;
}
}
}
}
}
else
{
lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; uint8_t x_317; 
x_313 = lean_ctor_get(x_4, 1);
lean_inc(x_313);
lean_dec(x_4);
x_314 = lean_ctor_get(x_5, 1);
lean_inc(x_314);
x_315 = lean_array_get_size(x_314);
lean_dec(x_314);
x_316 = lean_unsigned_to_nat(2u);
x_317 = lean_nat_dec_eq(x_315, x_316);
if (x_317 == 0)
{
lean_object* x_318; uint8_t x_319; 
x_318 = lean_unsigned_to_nat(1u);
x_319 = lean_nat_dec_eq(x_315, x_318);
lean_dec(x_315);
if (x_319 == 0)
{
lean_object* x_320; lean_object* x_321; 
lean_dec(x_5);
x_320 = l_Lean_IR_EmitC_emitMainFn___closed__1;
x_321 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_321, 0, x_320);
lean_ctor_set(x_321, 1, x_313);
return x_321;
}
else
{
lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_374; 
x_322 = lean_box(0);
x_323 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_323, 0, x_322);
lean_ctor_set(x_323, 1, x_313);
x_374 = l_Lean_IR_EmitC_getEnv(x_1, x_323);
if (lean_obj_tag(x_374) == 0)
{
lean_object* x_375; lean_object* x_376; lean_object* x_377; uint8_t x_378; 
x_375 = lean_ctor_get(x_374, 0);
lean_inc(x_375);
x_376 = lean_ctor_get(x_374, 1);
lean_inc(x_376);
lean_dec(x_374);
x_377 = l_Lean_IR_usesLeanNamespace(x_375, x_5);
lean_dec(x_375);
x_378 = lean_unbox(x_377);
lean_dec(x_377);
if (x_378 == 0)
{
lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; 
x_379 = l_Lean_IR_EmitC_emitMainFn___closed__29;
x_380 = lean_string_append(x_376, x_379);
x_381 = l_IO_println___rarg___closed__1;
x_382 = lean_string_append(x_380, x_381);
x_383 = l_Lean_IR_EmitC_emitMainFn___closed__30;
x_384 = lean_string_append(x_382, x_383);
x_385 = lean_string_append(x_384, x_381);
x_386 = l_Lean_IR_EmitC_emitMainFn___closed__31;
x_387 = lean_string_append(x_385, x_386);
x_388 = lean_string_append(x_387, x_381);
x_324 = x_388;
goto block_373;
}
else
{
lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; 
x_389 = l_Lean_IR_EmitC_emitMainFn___closed__32;
x_390 = lean_string_append(x_376, x_389);
x_391 = l_IO_println___rarg___closed__1;
x_392 = lean_string_append(x_390, x_391);
x_393 = l_Lean_IR_EmitC_emitMainFn___closed__30;
x_394 = lean_string_append(x_392, x_393);
x_395 = lean_string_append(x_394, x_391);
x_396 = l_Lean_IR_EmitC_emitMainFn___closed__33;
x_397 = lean_string_append(x_395, x_396);
x_398 = lean_string_append(x_397, x_391);
x_324 = x_398;
goto block_373;
}
}
else
{
lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; 
lean_dec(x_5);
x_399 = lean_ctor_get(x_374, 0);
lean_inc(x_399);
x_400 = lean_ctor_get(x_374, 1);
lean_inc(x_400);
if (lean_is_exclusive(x_374)) {
 lean_ctor_release(x_374, 0);
 lean_ctor_release(x_374, 1);
 x_401 = x_374;
} else {
 lean_dec_ref(x_374);
 x_401 = lean_box(0);
}
if (lean_is_scalar(x_401)) {
 x_402 = lean_alloc_ctor(1, 2, 0);
} else {
 x_402 = x_401;
}
lean_ctor_set(x_402, 0, x_399);
lean_ctor_set(x_402, 1, x_400);
return x_402;
}
block_373:
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; 
x_325 = l_Lean_IR_EmitC_emitMainFn___closed__2;
x_326 = lean_string_append(x_324, x_325);
x_327 = l_IO_println___rarg___closed__1;
x_328 = lean_string_append(x_326, x_327);
x_329 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_329, 0, x_322);
lean_ctor_set(x_329, 1, x_328);
x_330 = l_Lean_IR_EmitC_getModName(x_1, x_329);
if (lean_obj_tag(x_330) == 0)
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; 
x_331 = lean_ctor_get(x_330, 0);
lean_inc(x_331);
x_332 = lean_ctor_get(x_330, 1);
lean_inc(x_332);
if (lean_is_exclusive(x_330)) {
 lean_ctor_release(x_330, 0);
 lean_ctor_release(x_330, 1);
 x_333 = x_330;
} else {
 lean_dec_ref(x_330);
 x_333 = lean_box(0);
}
x_334 = l_String_splitAux___main___closed__1;
x_335 = l_Lean_Name_mangle(x_331, x_334);
x_336 = l_Lean_IR_EmitC_emitMainFn___closed__3;
x_337 = lean_string_append(x_336, x_335);
lean_dec(x_335);
x_338 = l_Lean_IR_EmitC_emitMainFn___closed__4;
x_339 = lean_string_append(x_337, x_338);
x_340 = lean_string_append(x_332, x_339);
lean_dec(x_339);
x_341 = lean_string_append(x_340, x_327);
if (lean_is_scalar(x_333)) {
 x_342 = lean_alloc_ctor(0, 2, 0);
} else {
 x_342 = x_333;
}
lean_ctor_set(x_342, 0, x_322);
lean_ctor_set(x_342, 1, x_341);
x_343 = l_Lean_IR_EmitC_emitMainFn___closed__10;
x_344 = l_List_mfor___main___at_Lean_IR_EmitC_emitMainFn___spec__2(x_343, x_1, x_342);
if (lean_obj_tag(x_344) == 0)
{
lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; 
x_345 = lean_ctor_get(x_344, 1);
lean_inc(x_345);
if (lean_is_exclusive(x_344)) {
 lean_ctor_release(x_344, 0);
 lean_ctor_release(x_344, 1);
 x_346 = x_344;
} else {
 lean_dec_ref(x_344);
 x_346 = lean_box(0);
}
x_347 = l_Lean_IR_EmitC_emitMainFn___closed__13;
x_348 = lean_string_append(x_345, x_347);
x_349 = lean_string_append(x_348, x_327);
x_350 = l_PersistentHashMap_Stats_toString___closed__5;
x_351 = lean_string_append(x_349, x_350);
x_352 = lean_string_append(x_351, x_327);
if (lean_is_scalar(x_346)) {
 x_353 = lean_alloc_ctor(0, 2, 0);
} else {
 x_353 = x_346;
}
lean_ctor_set(x_353, 0, x_322);
lean_ctor_set(x_353, 1, x_352);
x_354 = l_Lean_IR_EmitC_emitMainFn___closed__28;
x_355 = l_List_mfor___main___at_Lean_IR_EmitC_emitMainFn___spec__2(x_354, x_1, x_353);
if (lean_obj_tag(x_355) == 0)
{
lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; 
x_356 = lean_ctor_get(x_355, 1);
lean_inc(x_356);
if (lean_is_exclusive(x_355)) {
 lean_ctor_release(x_355, 0);
 lean_ctor_release(x_355, 1);
 x_357 = x_355;
} else {
 lean_dec_ref(x_355);
 x_357 = lean_box(0);
}
x_358 = lean_string_append(x_356, x_350);
x_359 = lean_string_append(x_358, x_327);
if (lean_is_scalar(x_357)) {
 x_360 = lean_alloc_ctor(0, 2, 0);
} else {
 x_360 = x_357;
}
lean_ctor_set(x_360, 0, x_322);
lean_ctor_set(x_360, 1, x_359);
return x_360;
}
else
{
lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; 
x_361 = lean_ctor_get(x_355, 0);
lean_inc(x_361);
x_362 = lean_ctor_get(x_355, 1);
lean_inc(x_362);
if (lean_is_exclusive(x_355)) {
 lean_ctor_release(x_355, 0);
 lean_ctor_release(x_355, 1);
 x_363 = x_355;
} else {
 lean_dec_ref(x_355);
 x_363 = lean_box(0);
}
if (lean_is_scalar(x_363)) {
 x_364 = lean_alloc_ctor(1, 2, 0);
} else {
 x_364 = x_363;
}
lean_ctor_set(x_364, 0, x_361);
lean_ctor_set(x_364, 1, x_362);
return x_364;
}
}
else
{
lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; 
x_365 = lean_ctor_get(x_344, 0);
lean_inc(x_365);
x_366 = lean_ctor_get(x_344, 1);
lean_inc(x_366);
if (lean_is_exclusive(x_344)) {
 lean_ctor_release(x_344, 0);
 lean_ctor_release(x_344, 1);
 x_367 = x_344;
} else {
 lean_dec_ref(x_344);
 x_367 = lean_box(0);
}
if (lean_is_scalar(x_367)) {
 x_368 = lean_alloc_ctor(1, 2, 0);
} else {
 x_368 = x_367;
}
lean_ctor_set(x_368, 0, x_365);
lean_ctor_set(x_368, 1, x_366);
return x_368;
}
}
else
{
lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; 
x_369 = lean_ctor_get(x_330, 0);
lean_inc(x_369);
x_370 = lean_ctor_get(x_330, 1);
lean_inc(x_370);
if (lean_is_exclusive(x_330)) {
 lean_ctor_release(x_330, 0);
 lean_ctor_release(x_330, 1);
 x_371 = x_330;
} else {
 lean_dec_ref(x_330);
 x_371 = lean_box(0);
}
if (lean_is_scalar(x_371)) {
 x_372 = lean_alloc_ctor(1, 2, 0);
} else {
 x_372 = x_371;
}
lean_ctor_set(x_372, 0, x_369);
lean_ctor_set(x_372, 1, x_370);
return x_372;
}
}
}
}
else
{
lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_469; 
lean_dec(x_315);
x_403 = lean_box(0);
x_404 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_404, 0, x_403);
lean_ctor_set(x_404, 1, x_313);
x_469 = l_Lean_IR_EmitC_getEnv(x_1, x_404);
if (lean_obj_tag(x_469) == 0)
{
lean_object* x_470; lean_object* x_471; lean_object* x_472; uint8_t x_473; 
x_470 = lean_ctor_get(x_469, 0);
lean_inc(x_470);
x_471 = lean_ctor_get(x_469, 1);
lean_inc(x_471);
lean_dec(x_469);
x_472 = l_Lean_IR_usesLeanNamespace(x_470, x_5);
lean_dec(x_470);
x_473 = lean_unbox(x_472);
lean_dec(x_472);
if (x_473 == 0)
{
lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; 
x_474 = l_Lean_IR_EmitC_emitMainFn___closed__29;
x_475 = lean_string_append(x_471, x_474);
x_476 = l_IO_println___rarg___closed__1;
x_477 = lean_string_append(x_475, x_476);
x_478 = l_Lean_IR_EmitC_emitMainFn___closed__30;
x_479 = lean_string_append(x_477, x_478);
x_480 = lean_string_append(x_479, x_476);
x_481 = l_Lean_IR_EmitC_emitMainFn___closed__31;
x_482 = lean_string_append(x_480, x_481);
x_483 = lean_string_append(x_482, x_476);
x_405 = x_483;
goto block_468;
}
else
{
lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; 
x_484 = l_Lean_IR_EmitC_emitMainFn___closed__32;
x_485 = lean_string_append(x_471, x_484);
x_486 = l_IO_println___rarg___closed__1;
x_487 = lean_string_append(x_485, x_486);
x_488 = l_Lean_IR_EmitC_emitMainFn___closed__30;
x_489 = lean_string_append(x_487, x_488);
x_490 = lean_string_append(x_489, x_486);
x_491 = l_Lean_IR_EmitC_emitMainFn___closed__33;
x_492 = lean_string_append(x_490, x_491);
x_493 = lean_string_append(x_492, x_486);
x_405 = x_493;
goto block_468;
}
}
else
{
lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; 
lean_dec(x_5);
x_494 = lean_ctor_get(x_469, 0);
lean_inc(x_494);
x_495 = lean_ctor_get(x_469, 1);
lean_inc(x_495);
if (lean_is_exclusive(x_469)) {
 lean_ctor_release(x_469, 0);
 lean_ctor_release(x_469, 1);
 x_496 = x_469;
} else {
 lean_dec_ref(x_469);
 x_496 = lean_box(0);
}
if (lean_is_scalar(x_496)) {
 x_497 = lean_alloc_ctor(1, 2, 0);
} else {
 x_497 = x_496;
}
lean_ctor_set(x_497, 0, x_494);
lean_ctor_set(x_497, 1, x_495);
return x_497;
}
block_468:
{
lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; 
x_406 = l_Lean_IR_EmitC_emitMainFn___closed__2;
x_407 = lean_string_append(x_405, x_406);
x_408 = l_IO_println___rarg___closed__1;
x_409 = lean_string_append(x_407, x_408);
x_410 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_410, 0, x_403);
lean_ctor_set(x_410, 1, x_409);
x_411 = l_Lean_IR_EmitC_getModName(x_1, x_410);
if (lean_obj_tag(x_411) == 0)
{
lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_441; lean_object* x_442; 
x_412 = lean_ctor_get(x_411, 0);
lean_inc(x_412);
x_413 = lean_ctor_get(x_411, 1);
lean_inc(x_413);
if (lean_is_exclusive(x_411)) {
 lean_ctor_release(x_411, 0);
 lean_ctor_release(x_411, 1);
 x_414 = x_411;
} else {
 lean_dec_ref(x_411);
 x_414 = lean_box(0);
}
x_415 = l_String_splitAux___main___closed__1;
x_416 = l_Lean_Name_mangle(x_412, x_415);
x_417 = l_Lean_IR_EmitC_emitMainFn___closed__3;
x_418 = lean_string_append(x_417, x_416);
lean_dec(x_416);
x_419 = l_Lean_IR_EmitC_emitMainFn___closed__4;
x_420 = lean_string_append(x_418, x_419);
x_421 = lean_string_append(x_413, x_420);
lean_dec(x_420);
x_422 = lean_string_append(x_421, x_408);
if (lean_is_scalar(x_414)) {
 x_423 = lean_alloc_ctor(0, 2, 0);
} else {
 x_423 = x_414;
}
lean_ctor_set(x_423, 0, x_403);
lean_ctor_set(x_423, 1, x_422);
x_441 = l_Lean_IR_EmitC_emitMainFn___closed__10;
x_442 = l_List_mfor___main___at_Lean_IR_EmitC_emitMainFn___spec__2(x_441, x_1, x_423);
if (lean_obj_tag(x_442) == 0)
{
if (x_317 == 0)
{
lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; 
x_443 = lean_ctor_get(x_442, 1);
lean_inc(x_443);
lean_dec(x_442);
x_444 = l_Lean_IR_EmitC_emitMainFn___closed__13;
x_445 = lean_string_append(x_443, x_444);
x_446 = lean_string_append(x_445, x_408);
x_424 = x_446;
goto block_440;
}
else
{
lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; 
x_447 = lean_ctor_get(x_442, 1);
lean_inc(x_447);
if (lean_is_exclusive(x_442)) {
 lean_ctor_release(x_442, 0);
 lean_ctor_release(x_442, 1);
 x_448 = x_442;
} else {
 lean_dec_ref(x_442);
 x_448 = lean_box(0);
}
if (lean_is_scalar(x_448)) {
 x_449 = lean_alloc_ctor(0, 2, 0);
} else {
 x_449 = x_448;
}
lean_ctor_set(x_449, 0, x_403);
lean_ctor_set(x_449, 1, x_447);
x_450 = l_Lean_IR_EmitC_emitMainFn___closed__47;
x_451 = l_List_mfor___main___at_Lean_IR_EmitC_emitMainFn___spec__2(x_450, x_1, x_449);
if (lean_obj_tag(x_451) == 0)
{
lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; 
x_452 = lean_ctor_get(x_451, 1);
lean_inc(x_452);
lean_dec(x_451);
x_453 = l_Lean_IR_EmitC_emitMainFn___closed__49;
x_454 = lean_string_append(x_452, x_453);
x_455 = lean_string_append(x_454, x_408);
x_424 = x_455;
goto block_440;
}
else
{
lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; 
x_456 = lean_ctor_get(x_451, 0);
lean_inc(x_456);
x_457 = lean_ctor_get(x_451, 1);
lean_inc(x_457);
if (lean_is_exclusive(x_451)) {
 lean_ctor_release(x_451, 0);
 lean_ctor_release(x_451, 1);
 x_458 = x_451;
} else {
 lean_dec_ref(x_451);
 x_458 = lean_box(0);
}
if (lean_is_scalar(x_458)) {
 x_459 = lean_alloc_ctor(1, 2, 0);
} else {
 x_459 = x_458;
}
lean_ctor_set(x_459, 0, x_456);
lean_ctor_set(x_459, 1, x_457);
return x_459;
}
}
}
else
{
lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; 
x_460 = lean_ctor_get(x_442, 0);
lean_inc(x_460);
x_461 = lean_ctor_get(x_442, 1);
lean_inc(x_461);
if (lean_is_exclusive(x_442)) {
 lean_ctor_release(x_442, 0);
 lean_ctor_release(x_442, 1);
 x_462 = x_442;
} else {
 lean_dec_ref(x_442);
 x_462 = lean_box(0);
}
if (lean_is_scalar(x_462)) {
 x_463 = lean_alloc_ctor(1, 2, 0);
} else {
 x_463 = x_462;
}
lean_ctor_set(x_463, 0, x_460);
lean_ctor_set(x_463, 1, x_461);
return x_463;
}
block_440:
{
lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; 
x_425 = l_PersistentHashMap_Stats_toString___closed__5;
x_426 = lean_string_append(x_424, x_425);
x_427 = lean_string_append(x_426, x_408);
x_428 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_428, 0, x_403);
lean_ctor_set(x_428, 1, x_427);
x_429 = l_Lean_IR_EmitC_emitMainFn___closed__28;
x_430 = l_List_mfor___main___at_Lean_IR_EmitC_emitMainFn___spec__2(x_429, x_1, x_428);
if (lean_obj_tag(x_430) == 0)
{
lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; 
x_431 = lean_ctor_get(x_430, 1);
lean_inc(x_431);
if (lean_is_exclusive(x_430)) {
 lean_ctor_release(x_430, 0);
 lean_ctor_release(x_430, 1);
 x_432 = x_430;
} else {
 lean_dec_ref(x_430);
 x_432 = lean_box(0);
}
x_433 = lean_string_append(x_431, x_425);
x_434 = lean_string_append(x_433, x_408);
if (lean_is_scalar(x_432)) {
 x_435 = lean_alloc_ctor(0, 2, 0);
} else {
 x_435 = x_432;
}
lean_ctor_set(x_435, 0, x_403);
lean_ctor_set(x_435, 1, x_434);
return x_435;
}
else
{
lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; 
x_436 = lean_ctor_get(x_430, 0);
lean_inc(x_436);
x_437 = lean_ctor_get(x_430, 1);
lean_inc(x_437);
if (lean_is_exclusive(x_430)) {
 lean_ctor_release(x_430, 0);
 lean_ctor_release(x_430, 1);
 x_438 = x_430;
} else {
 lean_dec_ref(x_430);
 x_438 = lean_box(0);
}
if (lean_is_scalar(x_438)) {
 x_439 = lean_alloc_ctor(1, 2, 0);
} else {
 x_439 = x_438;
}
lean_ctor_set(x_439, 0, x_436);
lean_ctor_set(x_439, 1, x_437);
return x_439;
}
}
}
else
{
lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; 
x_464 = lean_ctor_get(x_411, 0);
lean_inc(x_464);
x_465 = lean_ctor_get(x_411, 1);
lean_inc(x_465);
if (lean_is_exclusive(x_411)) {
 lean_ctor_release(x_411, 0);
 lean_ctor_release(x_411, 1);
 x_466 = x_411;
} else {
 lean_dec_ref(x_411);
 x_466 = lean_box(0);
}
if (lean_is_scalar(x_466)) {
 x_467 = lean_alloc_ctor(1, 2, 0);
} else {
 x_467 = x_466;
}
lean_ctor_set(x_467, 0, x_464);
lean_ctor_set(x_467, 1, x_465);
return x_467;
}
}
}
}
}
else
{
uint8_t x_498; 
lean_dec(x_5);
x_498 = !lean_is_exclusive(x_4);
if (x_498 == 0)
{
lean_object* x_499; lean_object* x_500; 
x_499 = lean_ctor_get(x_4, 0);
lean_dec(x_499);
x_500 = l_Lean_IR_EmitC_emitMainFn___closed__50;
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_500);
return x_4;
}
else
{
lean_object* x_501; lean_object* x_502; lean_object* x_503; 
x_501 = lean_ctor_get(x_4, 1);
lean_inc(x_501);
lean_dec(x_4);
x_502 = l_Lean_IR_EmitC_emitMainFn___closed__50;
x_503 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_503, 0, x_502);
lean_ctor_set(x_503, 1, x_501);
return x_503;
}
}
}
else
{
uint8_t x_504; 
x_504 = !lean_is_exclusive(x_4);
if (x_504 == 0)
{
return x_4;
}
else
{
lean_object* x_505; lean_object* x_506; lean_object* x_507; 
x_505 = lean_ctor_get(x_4, 0);
x_506 = lean_ctor_get(x_4, 1);
lean_inc(x_506);
lean_inc(x_505);
lean_dec(x_4);
x_507 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_507, 0, x_505);
lean_ctor_set(x_507, 1, x_506);
return x_507;
}
}
}
}
lean_object* l_List_mfor___main___at_Lean_IR_EmitC_emitMainFn___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_mfor___main___at_Lean_IR_EmitC_emitMainFn___spec__2(x_1, x_2, x_3);
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
x_8 = lean_name_dec_eq(x_6, x_7);
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
lean_object* x_3; 
x_3 = l_Lean_IR_EmitC_getEnv(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
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
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_3);
if (x_19 == 0)
{
return x_3;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_3, 0);
x_21 = lean_ctor_get(x_3, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_3);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
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
lean_object* x_3; 
x_3 = l_Lean_IR_EmitC_hasMainFn(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; uint8_t x_5; 
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
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_3);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_3, 0);
lean_dec(x_13);
x_14 = lean_box(0);
lean_ctor_set(x_3, 0, x_14);
x_15 = l_Lean_IR_EmitC_emitMainFn(x_1, x_3);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_3, 1);
lean_inc(x_16);
lean_dec(x_3);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = l_Lean_IR_EmitC_emitMainFn(x_1, x_18);
return x_19;
}
}
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_3);
if (x_20 == 0)
{
return x_3;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_3, 0);
x_22 = lean_ctor_get(x_3, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_3);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
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
lean_object* l_Array_mforAux___main___at_Lean_IR_EmitC_emitFileHeader___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_1);
x_6 = lean_nat_dec_lt(x_2, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
uint8_t x_7; 
lean_dec(x_2);
x_7 = !lean_is_exclusive(x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_4, 0);
lean_dec(x_8);
x_9 = lean_box(0);
lean_ctor_set(x_4, 0, x_9);
return x_4;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
lean_dec(x_4);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_4);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_14 = lean_ctor_get(x_4, 1);
x_15 = lean_ctor_get(x_4, 0);
lean_dec(x_15);
x_16 = lean_array_fget(x_1, x_2);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_2, x_17);
lean_dec(x_2);
x_19 = l_System_FilePath_dirName___closed__1;
x_20 = l_Lean_Name_toStringWithSep___main(x_19, x_16);
x_21 = l_Lean_Format_flatten___main___closed__1;
x_22 = lean_string_append(x_21, x_20);
lean_dec(x_20);
x_23 = lean_string_append(x_14, x_22);
lean_dec(x_22);
x_24 = lean_box(0);
lean_ctor_set(x_4, 1, x_23);
lean_ctor_set(x_4, 0, x_24);
x_2 = x_18;
goto _start;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_26 = lean_ctor_get(x_4, 1);
lean_inc(x_26);
lean_dec(x_4);
x_27 = lean_array_fget(x_1, x_2);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_add(x_2, x_28);
lean_dec(x_2);
x_30 = l_System_FilePath_dirName___closed__1;
x_31 = l_Lean_Name_toStringWithSep___main(x_30, x_27);
x_32 = l_Lean_Format_flatten___main___closed__1;
x_33 = lean_string_append(x_32, x_31);
lean_dec(x_31);
x_34 = lean_string_append(x_26, x_33);
lean_dec(x_33);
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
x_2 = x_29;
x_4 = x_36;
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
lean_object* x_3; 
x_3 = l_Lean_IR_EmitC_getEnv(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_box(0);
lean_ctor_set(x_3, 0, x_6);
x_7 = l_Lean_IR_EmitC_getModName(x_1, x_3);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_11 = l_Lean_IR_EmitC_emitFileHeader___closed__1;
x_12 = lean_string_append(x_10, x_11);
x_13 = l_IO_println___rarg___closed__1;
x_14 = lean_string_append(x_12, x_13);
x_15 = l_System_FilePath_dirName___closed__1;
x_16 = l_Lean_Name_toStringWithSep___main(x_15, x_9);
x_17 = l_Lean_IR_EmitC_emitFileHeader___closed__2;
x_18 = lean_string_append(x_17, x_16);
lean_dec(x_16);
x_19 = lean_string_append(x_14, x_18);
lean_dec(x_18);
x_20 = lean_string_append(x_19, x_13);
x_21 = l_Lean_IR_EmitC_emitFileHeader___closed__3;
x_22 = lean_string_append(x_20, x_21);
lean_ctor_set(x_7, 1, x_22);
lean_ctor_set(x_7, 0, x_6);
x_23 = l_Lean_Environment_imports(x_5);
lean_dec(x_5);
x_24 = lean_unsigned_to_nat(0u);
x_25 = l_Array_mforAux___main___at_Lean_IR_EmitC_emitFileHeader___spec__1(x_23, x_24, x_1, x_7);
lean_dec(x_23);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_27 = lean_ctor_get(x_25, 1);
x_28 = lean_ctor_get(x_25, 0);
lean_dec(x_28);
x_29 = l_String_splitAux___main___closed__1;
x_30 = lean_string_append(x_27, x_29);
x_31 = lean_string_append(x_30, x_13);
x_32 = l_Lean_IR_EmitC_emitFileHeader___closed__4;
x_33 = lean_string_append(x_31, x_32);
x_34 = lean_string_append(x_33, x_13);
lean_ctor_set(x_25, 1, x_34);
lean_ctor_set(x_25, 0, x_6);
x_35 = l_Lean_IR_EmitC_emitFileHeader___closed__25;
x_36 = l_List_mfor___main___at_Lean_IR_EmitC_emitMainFn___spec__2(x_35, x_1, x_25);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_37 = lean_ctor_get(x_25, 1);
lean_inc(x_37);
lean_dec(x_25);
x_38 = l_String_splitAux___main___closed__1;
x_39 = lean_string_append(x_37, x_38);
x_40 = lean_string_append(x_39, x_13);
x_41 = l_Lean_IR_EmitC_emitFileHeader___closed__4;
x_42 = lean_string_append(x_40, x_41);
x_43 = lean_string_append(x_42, x_13);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_6);
lean_ctor_set(x_44, 1, x_43);
x_45 = l_Lean_IR_EmitC_emitFileHeader___closed__25;
x_46 = l_List_mfor___main___at_Lean_IR_EmitC_emitMainFn___spec__2(x_45, x_1, x_44);
return x_46;
}
}
else
{
uint8_t x_47; 
x_47 = !lean_is_exclusive(x_25);
if (x_47 == 0)
{
return x_25;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_25, 0);
x_49 = lean_ctor_get(x_25, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_25);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_51 = lean_ctor_get(x_7, 0);
x_52 = lean_ctor_get(x_7, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_7);
x_53 = l_Lean_IR_EmitC_emitFileHeader___closed__1;
x_54 = lean_string_append(x_52, x_53);
x_55 = l_IO_println___rarg___closed__1;
x_56 = lean_string_append(x_54, x_55);
x_57 = l_System_FilePath_dirName___closed__1;
x_58 = l_Lean_Name_toStringWithSep___main(x_57, x_51);
x_59 = l_Lean_IR_EmitC_emitFileHeader___closed__2;
x_60 = lean_string_append(x_59, x_58);
lean_dec(x_58);
x_61 = lean_string_append(x_56, x_60);
lean_dec(x_60);
x_62 = lean_string_append(x_61, x_55);
x_63 = l_Lean_IR_EmitC_emitFileHeader___closed__3;
x_64 = lean_string_append(x_62, x_63);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_6);
lean_ctor_set(x_65, 1, x_64);
x_66 = l_Lean_Environment_imports(x_5);
lean_dec(x_5);
x_67 = lean_unsigned_to_nat(0u);
x_68 = l_Array_mforAux___main___at_Lean_IR_EmitC_emitFileHeader___spec__1(x_66, x_67, x_1, x_65);
lean_dec(x_66);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_69 = lean_ctor_get(x_68, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_70 = x_68;
} else {
 lean_dec_ref(x_68);
 x_70 = lean_box(0);
}
x_71 = l_String_splitAux___main___closed__1;
x_72 = lean_string_append(x_69, x_71);
x_73 = lean_string_append(x_72, x_55);
x_74 = l_Lean_IR_EmitC_emitFileHeader___closed__4;
x_75 = lean_string_append(x_73, x_74);
x_76 = lean_string_append(x_75, x_55);
if (lean_is_scalar(x_70)) {
 x_77 = lean_alloc_ctor(0, 2, 0);
} else {
 x_77 = x_70;
}
lean_ctor_set(x_77, 0, x_6);
lean_ctor_set(x_77, 1, x_76);
x_78 = l_Lean_IR_EmitC_emitFileHeader___closed__25;
x_79 = l_List_mfor___main___at_Lean_IR_EmitC_emitMainFn___spec__2(x_78, x_1, x_77);
return x_79;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_80 = lean_ctor_get(x_68, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_68, 1);
lean_inc(x_81);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_82 = x_68;
} else {
 lean_dec_ref(x_68);
 x_82 = lean_box(0);
}
if (lean_is_scalar(x_82)) {
 x_83 = lean_alloc_ctor(1, 2, 0);
} else {
 x_83 = x_82;
}
lean_ctor_set(x_83, 0, x_80);
lean_ctor_set(x_83, 1, x_81);
return x_83;
}
}
}
else
{
uint8_t x_84; 
lean_dec(x_5);
x_84 = !lean_is_exclusive(x_7);
if (x_84 == 0)
{
return x_7;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_7, 0);
x_86 = lean_ctor_get(x_7, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_7);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_88 = lean_ctor_get(x_3, 0);
x_89 = lean_ctor_get(x_3, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_3);
x_90 = lean_box(0);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_89);
x_92 = l_Lean_IR_EmitC_getModName(x_1, x_91);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 x_95 = x_92;
} else {
 lean_dec_ref(x_92);
 x_95 = lean_box(0);
}
x_96 = l_Lean_IR_EmitC_emitFileHeader___closed__1;
x_97 = lean_string_append(x_94, x_96);
x_98 = l_IO_println___rarg___closed__1;
x_99 = lean_string_append(x_97, x_98);
x_100 = l_System_FilePath_dirName___closed__1;
x_101 = l_Lean_Name_toStringWithSep___main(x_100, x_93);
x_102 = l_Lean_IR_EmitC_emitFileHeader___closed__2;
x_103 = lean_string_append(x_102, x_101);
lean_dec(x_101);
x_104 = lean_string_append(x_99, x_103);
lean_dec(x_103);
x_105 = lean_string_append(x_104, x_98);
x_106 = l_Lean_IR_EmitC_emitFileHeader___closed__3;
x_107 = lean_string_append(x_105, x_106);
if (lean_is_scalar(x_95)) {
 x_108 = lean_alloc_ctor(0, 2, 0);
} else {
 x_108 = x_95;
}
lean_ctor_set(x_108, 0, x_90);
lean_ctor_set(x_108, 1, x_107);
x_109 = l_Lean_Environment_imports(x_88);
lean_dec(x_88);
x_110 = lean_unsigned_to_nat(0u);
x_111 = l_Array_mforAux___main___at_Lean_IR_EmitC_emitFileHeader___spec__1(x_109, x_110, x_1, x_108);
lean_dec(x_109);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_112 = lean_ctor_get(x_111, 1);
lean_inc(x_112);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 x_113 = x_111;
} else {
 lean_dec_ref(x_111);
 x_113 = lean_box(0);
}
x_114 = l_String_splitAux___main___closed__1;
x_115 = lean_string_append(x_112, x_114);
x_116 = lean_string_append(x_115, x_98);
x_117 = l_Lean_IR_EmitC_emitFileHeader___closed__4;
x_118 = lean_string_append(x_116, x_117);
x_119 = lean_string_append(x_118, x_98);
if (lean_is_scalar(x_113)) {
 x_120 = lean_alloc_ctor(0, 2, 0);
} else {
 x_120 = x_113;
}
lean_ctor_set(x_120, 0, x_90);
lean_ctor_set(x_120, 1, x_119);
x_121 = l_Lean_IR_EmitC_emitFileHeader___closed__25;
x_122 = l_List_mfor___main___at_Lean_IR_EmitC_emitMainFn___spec__2(x_121, x_1, x_120);
return x_122;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_123 = lean_ctor_get(x_111, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_111, 1);
lean_inc(x_124);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 x_125 = x_111;
} else {
 lean_dec_ref(x_111);
 x_125 = lean_box(0);
}
if (lean_is_scalar(x_125)) {
 x_126 = lean_alloc_ctor(1, 2, 0);
} else {
 x_126 = x_125;
}
lean_ctor_set(x_126, 0, x_123);
lean_ctor_set(x_126, 1, x_124);
return x_126;
}
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
lean_dec(x_88);
x_127 = lean_ctor_get(x_92, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_92, 1);
lean_inc(x_128);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 x_129 = x_92;
} else {
 lean_dec_ref(x_92);
 x_129 = lean_box(0);
}
if (lean_is_scalar(x_129)) {
 x_130 = lean_alloc_ctor(1, 2, 0);
} else {
 x_130 = x_129;
}
lean_ctor_set(x_130, 0, x_127);
lean_ctor_set(x_130, 1, x_128);
return x_130;
}
}
}
else
{
uint8_t x_131; 
x_131 = !lean_is_exclusive(x_3);
if (x_131 == 0)
{
return x_3;
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_132 = lean_ctor_get(x_3, 0);
x_133 = lean_ctor_get(x_3, 1);
lean_inc(x_133);
lean_inc(x_132);
lean_dec(x_3);
x_134 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_134, 0, x_132);
lean_ctor_set(x_134, 1, x_133);
return x_134;
}
}
}
}
lean_object* l_Array_mforAux___main___at_Lean_IR_EmitC_emitFileHeader___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_mforAux___main___at_Lean_IR_EmitC_emitFileHeader___spec__1(x_1, x_2, x_3, x_4);
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
x_1 = l_PersistentHashMap_Stats_toString___closed__5;
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
x_4 = l_List_mfor___main___at_Lean_IR_EmitC_emitMainFn___spec__2(x_3, x_1, x_2);
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
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_ctor_get(x_3, 0);
lean_dec(x_5);
x_6 = l_Nat_repr(x_1);
x_7 = l_Lean_IR_VarId_HasToString___closed__1;
x_8 = lean_string_append(x_7, x_6);
lean_dec(x_6);
x_9 = l_Lean_IR_EmitC_throwUnknownVar___rarg___closed__1;
x_10 = lean_string_append(x_9, x_8);
lean_dec(x_8);
x_11 = l_Char_HasRepr___closed__1;
x_12 = lean_string_append(x_10, x_11);
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 0, x_12);
return x_3;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_13 = lean_ctor_get(x_3, 1);
lean_inc(x_13);
lean_dec(x_3);
x_14 = l_Nat_repr(x_1);
x_15 = l_Lean_IR_VarId_HasToString___closed__1;
x_16 = lean_string_append(x_15, x_14);
lean_dec(x_14);
x_17 = l_Lean_IR_EmitC_throwUnknownVar___rarg___closed__1;
x_18 = lean_string_append(x_17, x_16);
lean_dec(x_16);
x_19 = l_Char_HasRepr___closed__1;
x_20 = lean_string_append(x_18, x_19);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_13);
return x_21;
}
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
lean_object* l_AssocList_find___main___at_Lean_IR_EmitC_isObj___spec__2(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_HashMapImp_find___at_Lean_IR_EmitC_isObj___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; size_t x_5; size_t x_6; lean_object* x_7; size_t x_8; lean_object* x_9; lean_object* x_10; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = lean_usize_of_nat(x_2);
x_6 = lean_usize_modn(x_5, x_4);
lean_dec(x_4);
x_7 = lean_box_usize(x_6);
x_8 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_9 = lean_array_uget(x_3, x_8);
x_10 = l_AssocList_find___main___at_Lean_IR_EmitC_isObj___spec__2(x_2, x_9);
lean_dec(x_9);
return x_10;
}
}
lean_object* l_Lean_IR_EmitC_isObj(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_ctor_get(x_3, 0);
lean_dec(x_6);
x_7 = lean_box(0);
lean_inc(x_5);
lean_ctor_set(x_3, 0, x_7);
x_8 = lean_ctor_get(x_2, 2);
x_9 = l_HashMapImp_find___at_Lean_IR_EmitC_isObj___spec__1(x_8, x_1);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
lean_dec(x_5);
x_10 = l_Lean_IR_EmitC_throwUnknownVar___rarg(x_1, x_2, x_3);
return x_10;
}
else
{
lean_object* x_11; uint8_t x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_3);
lean_dec(x_1);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_unbox(x_11);
lean_dec(x_11);
x_13 = l_Lean_IR_IRType_isObj(x_12);
x_14 = lean_box(x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_5);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_3, 1);
lean_inc(x_16);
lean_dec(x_3);
x_17 = lean_box(0);
lean_inc(x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = lean_ctor_get(x_2, 2);
x_20 = l_HashMapImp_find___at_Lean_IR_EmitC_isObj___spec__1(x_19, x_1);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
lean_dec(x_16);
x_21 = l_Lean_IR_EmitC_throwUnknownVar___rarg(x_1, x_2, x_18);
return x_21;
}
else
{
lean_object* x_22; uint8_t x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_18);
lean_dec(x_1);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_unbox(x_22);
lean_dec(x_22);
x_24 = l_Lean_IR_IRType_isObj(x_23);
x_25 = lean_box(x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_16);
return x_26;
}
}
}
}
lean_object* l_AssocList_find___main___at_Lean_IR_EmitC_isObj___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_AssocList_find___main___at_Lean_IR_EmitC_isObj___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_HashMapImp_find___at_Lean_IR_EmitC_isObj___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_HashMapImp_find___at_Lean_IR_EmitC_isObj___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_IR_EmitC_isObj___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_EmitC_isObj(x_1, x_2, x_3);
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
lean_object* x_3; lean_object* x_4; size_t x_5; size_t x_6; lean_object* x_7; size_t x_8; lean_object* x_9; lean_object* x_10; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = lean_usize_of_nat(x_2);
x_6 = lean_usize_modn(x_5, x_4);
lean_dec(x_4);
x_7 = lean_box_usize(x_6);
x_8 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_9 = lean_array_uget(x_3, x_8);
x_10 = l_AssocList_find___main___at_Lean_IR_EmitC_getJPParams___spec__2(x_2, x_9);
lean_dec(x_9);
return x_10;
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
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
lean_dec(x_5);
x_6 = lean_ctor_get(x_2, 3);
x_7 = l_HashMapImp_find___at_Lean_IR_EmitC_getJPParams___spec__1(x_6, x_1);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
x_8 = l_Lean_IR_EmitC_getJPParams___closed__1;
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 0, x_8);
return x_3;
}
else
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
lean_ctor_set(x_3, 0, x_9);
return x_3;
}
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
lean_dec(x_3);
x_11 = lean_ctor_get(x_2, 3);
x_12 = l_HashMapImp_find___at_Lean_IR_EmitC_getJPParams___spec__1(x_11, x_1);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = l_Lean_IR_EmitC_getJPParams___closed__1;
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_10);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_10);
return x_16;
}
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
lean_object* l_Lean_IR_EmitC_declareVar(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_6 = lean_ctor_get(x_4, 1);
x_7 = lean_ctor_get(x_4, 0);
lean_dec(x_7);
x_8 = l_Lean_IR_EmitC_toCType(x_2);
x_9 = lean_string_append(x_6, x_8);
lean_dec(x_8);
x_10 = l_Lean_Format_flatten___main___closed__1;
x_11 = lean_string_append(x_9, x_10);
x_12 = l_Nat_repr(x_1);
x_13 = l_Lean_IR_VarId_HasToString___closed__1;
x_14 = lean_string_append(x_13, x_12);
lean_dec(x_12);
x_15 = lean_string_append(x_11, x_14);
lean_dec(x_14);
x_16 = l_Lean_IR_EmitC_declareVar___closed__1;
x_17 = lean_string_append(x_15, x_16);
x_18 = lean_box(0);
lean_ctor_set(x_4, 1, x_17);
lean_ctor_set(x_4, 0, x_18);
return x_4;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_19 = lean_ctor_get(x_4, 1);
lean_inc(x_19);
lean_dec(x_4);
x_20 = l_Lean_IR_EmitC_toCType(x_2);
x_21 = lean_string_append(x_19, x_20);
lean_dec(x_20);
x_22 = l_Lean_Format_flatten___main___closed__1;
x_23 = lean_string_append(x_21, x_22);
x_24 = l_Nat_repr(x_1);
x_25 = l_Lean_IR_VarId_HasToString___closed__1;
x_26 = lean_string_append(x_25, x_24);
lean_dec(x_24);
x_27 = lean_string_append(x_23, x_26);
lean_dec(x_26);
x_28 = l_Lean_IR_EmitC_declareVar___closed__1;
x_29 = lean_string_append(x_27, x_28);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
}
lean_object* l_Lean_IR_EmitC_declareVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Lean_IR_EmitC_declareVar(x_1, x_5, x_3, x_4);
lean_dec(x_3);
return x_6;
}
}
lean_object* l_Array_mforAux___main___at_Lean_IR_EmitC_declareParams___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_1);
x_6 = lean_nat_dec_lt(x_2, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
uint8_t x_7; 
lean_dec(x_2);
x_7 = !lean_is_exclusive(x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_4, 0);
lean_dec(x_8);
x_9 = lean_box(0);
lean_ctor_set(x_4, 0, x_9);
return x_4;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
lean_dec(x_4);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; 
x_13 = lean_array_fget(x_1, x_2);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_2, x_14);
lean_dec(x_2);
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_16);
x_17 = lean_ctor_get_uint8(x_13, sizeof(void*)*1 + 1);
lean_dec(x_13);
x_18 = l_Lean_IR_EmitC_declareVar(x_16, x_17, x_3, x_4);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_18, 0);
lean_dec(x_20);
x_21 = lean_box(0);
lean_ctor_set(x_18, 0, x_21);
x_2 = x_15;
x_4 = x_18;
goto _start;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_18, 1);
lean_inc(x_23);
lean_dec(x_18);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
x_2 = x_15;
x_4 = x_25;
goto _start;
}
}
else
{
uint8_t x_27; 
lean_dec(x_15);
x_27 = !lean_is_exclusive(x_18);
if (x_27 == 0)
{
return x_18;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_18, 0);
x_29 = lean_ctor_get(x_18, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_18);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
}
lean_object* l_Lean_IR_EmitC_declareParams(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Array_mforAux___main___at_Lean_IR_EmitC_declareParams___spec__1(x_1, x_4, x_2, x_3);
return x_5;
}
}
lean_object* l_Array_mforAux___main___at_Lean_IR_EmitC_declareParams___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_mforAux___main___at_Lean_IR_EmitC_declareParams___spec__1(x_1, x_2, x_3, x_4);
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
lean_object* x_16; uint8_t x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
x_17 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
x_18 = lean_ctor_get(x_1, 2);
lean_inc(x_18);
x_19 = !lean_is_exclusive(x_4);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_20 = lean_ctor_get(x_4, 1);
x_21 = lean_ctor_get(x_4, 0);
lean_dec(x_21);
x_22 = lean_box(0);
lean_inc(x_20);
lean_ctor_set(x_4, 0, x_22);
x_23 = lean_ctor_get(x_3, 4);
x_24 = l_Lean_IR_isTailCallTo(x_23, x_1);
lean_dec(x_1);
if (x_24 == 0)
{
lean_object* x_25; 
lean_dec(x_20);
x_25 = l_Lean_IR_EmitC_declareVar(x_16, x_17, x_3, x_4);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_25, 0);
lean_dec(x_27);
lean_ctor_set(x_25, 0, x_22);
x_28 = 1;
x_1 = x_18;
x_2 = x_28;
x_4 = x_25;
goto _start;
}
else
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_30 = lean_ctor_get(x_25, 1);
lean_inc(x_30);
lean_dec(x_25);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_22);
lean_ctor_set(x_31, 1, x_30);
x_32 = 1;
x_1 = x_18;
x_2 = x_32;
x_4 = x_31;
goto _start;
}
}
else
{
uint8_t x_34; 
lean_dec(x_18);
x_34 = !lean_is_exclusive(x_25);
if (x_34 == 0)
{
return x_25;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_25, 0);
x_36 = lean_ctor_get(x_25, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_25);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_4);
lean_dec(x_18);
lean_dec(x_16);
x_38 = lean_box(x_2);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_20);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_40 = lean_ctor_get(x_4, 1);
lean_inc(x_40);
lean_dec(x_4);
x_41 = lean_box(0);
lean_inc(x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
x_43 = lean_ctor_get(x_3, 4);
x_44 = l_Lean_IR_isTailCallTo(x_43, x_1);
lean_dec(x_1);
if (x_44 == 0)
{
lean_object* x_45; 
lean_dec(x_40);
x_45 = l_Lean_IR_EmitC_declareVar(x_16, x_17, x_3, x_42);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_47 = x_45;
} else {
 lean_dec_ref(x_45);
 x_47 = lean_box(0);
}
if (lean_is_scalar(x_47)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_47;
}
lean_ctor_set(x_48, 0, x_41);
lean_ctor_set(x_48, 1, x_46);
x_49 = 1;
x_1 = x_18;
x_2 = x_49;
x_4 = x_48;
goto _start;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_18);
x_51 = lean_ctor_get(x_45, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_45, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_53 = x_45;
} else {
 lean_dec_ref(x_45);
 x_53 = lean_box(0);
}
if (lean_is_scalar(x_53)) {
 x_54 = lean_alloc_ctor(1, 2, 0);
} else {
 x_54 = x_53;
}
lean_ctor_set(x_54, 0, x_51);
lean_ctor_set(x_54, 1, x_52);
return x_54;
}
}
else
{
lean_object* x_55; lean_object* x_56; 
lean_dec(x_42);
lean_dec(x_18);
lean_dec(x_16);
x_55 = lean_box(x_2);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_40);
return x_56;
}
}
}
case 1:
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_57 = lean_ctor_get(x_1, 1);
lean_inc(x_57);
x_58 = lean_ctor_get(x_1, 3);
lean_inc(x_58);
lean_dec(x_1);
x_59 = lean_unsigned_to_nat(0u);
x_60 = l_Array_mforAux___main___at_Lean_IR_EmitC_declareParams___spec__1(x_57, x_59, x_3, x_4);
if (x_2 == 0)
{
if (lean_obj_tag(x_60) == 0)
{
uint8_t x_61; 
x_61 = !lean_is_exclusive(x_60);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; uint8_t x_64; lean_object* x_65; 
x_62 = lean_ctor_get(x_60, 0);
lean_dec(x_62);
x_63 = lean_array_get_size(x_57);
lean_dec(x_57);
x_64 = lean_nat_dec_lt(x_59, x_63);
lean_dec(x_63);
x_65 = lean_box(0);
lean_ctor_set(x_60, 0, x_65);
x_1 = x_58;
x_2 = x_64;
x_4 = x_60;
goto _start;
}
else
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; lean_object* x_70; lean_object* x_71; 
x_67 = lean_ctor_get(x_60, 1);
lean_inc(x_67);
lean_dec(x_60);
x_68 = lean_array_get_size(x_57);
lean_dec(x_57);
x_69 = lean_nat_dec_lt(x_59, x_68);
lean_dec(x_68);
x_70 = lean_box(0);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_67);
x_1 = x_58;
x_2 = x_69;
x_4 = x_71;
goto _start;
}
}
else
{
uint8_t x_73; 
lean_dec(x_58);
lean_dec(x_57);
x_73 = !lean_is_exclusive(x_60);
if (x_73 == 0)
{
return x_60;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_60, 0);
x_75 = lean_ctor_get(x_60, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_60);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
else
{
lean_dec(x_57);
if (lean_obj_tag(x_60) == 0)
{
uint8_t x_77; 
x_77 = !lean_is_exclusive(x_60);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_78 = lean_ctor_get(x_60, 0);
lean_dec(x_78);
x_79 = lean_box(0);
lean_ctor_set(x_60, 0, x_79);
x_80 = 1;
x_1 = x_58;
x_2 = x_80;
x_4 = x_60;
goto _start;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_82 = lean_ctor_get(x_60, 1);
lean_inc(x_82);
lean_dec(x_60);
x_83 = lean_box(0);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_82);
x_85 = 1;
x_1 = x_58;
x_2 = x_85;
x_4 = x_84;
goto _start;
}
}
else
{
uint8_t x_87; 
lean_dec(x_58);
x_87 = !lean_is_exclusive(x_60);
if (x_87 == 0)
{
return x_60;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_60, 0);
x_89 = lean_ctor_get(x_60, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_60);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
}
}
default: 
{
lean_object* x_91; 
x_91 = lean_box(0);
x_5 = x_91;
goto block_15;
}
}
block_15:
{
uint8_t x_6; 
lean_dec(x_5);
x_6 = l_Lean_IR_FnBody_isTerminal(x_1);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = l_Lean_IR_FnBody_body(x_1);
lean_dec(x_1);
x_1 = x_7;
goto _start;
}
else
{
uint8_t x_9; 
lean_dec(x_1);
x_9 = !lean_is_exclusive(x_4);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_4, 0);
lean_dec(x_10);
x_11 = lean_box(x_2);
lean_ctor_set(x_4, 0, x_11);
return x_4;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_4, 1);
lean_inc(x_12);
lean_dec(x_4);
x_13 = lean_box(x_2);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
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
lean_object* l_Lean_IR_EmitC_emitTag(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_1);
x_4 = l_Lean_IR_EmitC_isObj(x_1, x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_unbox(x_5);
lean_dec(x_5);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_ctor_get(x_4, 1);
x_9 = lean_ctor_get(x_4, 0);
lean_dec(x_9);
x_10 = l_Nat_repr(x_1);
x_11 = l_Lean_IR_VarId_HasToString___closed__1;
x_12 = lean_string_append(x_11, x_10);
lean_dec(x_10);
x_13 = lean_string_append(x_8, x_12);
lean_dec(x_12);
x_14 = lean_box(0);
lean_ctor_set(x_4, 1, x_13);
lean_ctor_set(x_4, 0, x_14);
return x_4;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_ctor_get(x_4, 1);
lean_inc(x_15);
lean_dec(x_4);
x_16 = l_Nat_repr(x_1);
x_17 = l_Lean_IR_VarId_HasToString___closed__1;
x_18 = lean_string_append(x_17, x_16);
lean_dec(x_16);
x_19 = lean_string_append(x_15, x_18);
lean_dec(x_18);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_4);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_23 = lean_ctor_get(x_4, 1);
x_24 = lean_ctor_get(x_4, 0);
lean_dec(x_24);
x_25 = l_Lean_IR_EmitC_emitTag___closed__1;
x_26 = lean_string_append(x_23, x_25);
x_27 = l_Nat_repr(x_1);
x_28 = l_Lean_IR_VarId_HasToString___closed__1;
x_29 = lean_string_append(x_28, x_27);
lean_dec(x_27);
x_30 = lean_string_append(x_26, x_29);
lean_dec(x_29);
x_31 = l_Option_HasRepr___rarg___closed__3;
x_32 = lean_string_append(x_30, x_31);
x_33 = lean_box(0);
lean_ctor_set(x_4, 1, x_32);
lean_ctor_set(x_4, 0, x_33);
return x_4;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_34 = lean_ctor_get(x_4, 1);
lean_inc(x_34);
lean_dec(x_4);
x_35 = l_Lean_IR_EmitC_emitTag___closed__1;
x_36 = lean_string_append(x_34, x_35);
x_37 = l_Nat_repr(x_1);
x_38 = l_Lean_IR_VarId_HasToString___closed__1;
x_39 = lean_string_append(x_38, x_37);
lean_dec(x_37);
x_40 = lean_string_append(x_36, x_39);
lean_dec(x_39);
x_41 = l_Option_HasRepr___rarg___closed__3;
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
uint8_t x_45; 
lean_dec(x_1);
x_45 = !lean_is_exclusive(x_4);
if (x_45 == 0)
{
return x_4;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_4, 0);
x_47 = lean_ctor_get(x_4, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_4);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
}
lean_object* l_Lean_IR_EmitC_emitTag___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_EmitC_emitTag(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
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
lean_object* x_5; 
x_5 = lean_box(0);
return x_5;
}
else
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
lean_object* l_Lean_IR_EmitC_emitIf(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_7, 1);
x_10 = lean_ctor_get(x_7, 0);
lean_dec(x_10);
x_11 = l_Lean_IR_EmitC_emitIf___closed__1;
x_12 = lean_string_append(x_9, x_11);
x_13 = lean_box(0);
lean_ctor_set(x_7, 1, x_12);
lean_ctor_set(x_7, 0, x_13);
x_14 = l_Lean_IR_EmitC_emitTag(x_2, x_6, x_7);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_16 = lean_ctor_get(x_14, 1);
x_17 = lean_ctor_get(x_14, 0);
lean_dec(x_17);
x_18 = l_Lean_IR_EmitC_emitIf___closed__2;
x_19 = lean_string_append(x_16, x_18);
x_20 = l_Nat_repr(x_3);
x_21 = lean_string_append(x_19, x_20);
lean_dec(x_20);
x_22 = l_Option_HasRepr___rarg___closed__3;
x_23 = lean_string_append(x_21, x_22);
x_24 = l_IO_println___rarg___closed__1;
x_25 = lean_string_append(x_23, x_24);
lean_ctor_set(x_14, 1, x_25);
lean_ctor_set(x_14, 0, x_13);
lean_inc(x_1);
lean_inc(x_6);
x_26 = lean_apply_3(x_1, x_4, x_6, x_14);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_28 = lean_ctor_get(x_26, 1);
x_29 = lean_ctor_get(x_26, 0);
lean_dec(x_29);
x_30 = l_Lean_IR_EmitC_emitIf___closed__3;
x_31 = lean_string_append(x_28, x_30);
x_32 = lean_string_append(x_31, x_24);
lean_ctor_set(x_26, 1, x_32);
lean_ctor_set(x_26, 0, x_13);
x_33 = lean_apply_3(x_1, x_5, x_6, x_26);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_34 = lean_ctor_get(x_26, 1);
lean_inc(x_34);
lean_dec(x_26);
x_35 = l_Lean_IR_EmitC_emitIf___closed__3;
x_36 = lean_string_append(x_34, x_35);
x_37 = lean_string_append(x_36, x_24);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_13);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_apply_3(x_1, x_5, x_6, x_38);
return x_39;
}
}
else
{
uint8_t x_40; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_26);
if (x_40 == 0)
{
return x_26;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_26, 0);
x_42 = lean_ctor_get(x_26, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_26);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_44 = lean_ctor_get(x_14, 1);
lean_inc(x_44);
lean_dec(x_14);
x_45 = l_Lean_IR_EmitC_emitIf___closed__2;
x_46 = lean_string_append(x_44, x_45);
x_47 = l_Nat_repr(x_3);
x_48 = lean_string_append(x_46, x_47);
lean_dec(x_47);
x_49 = l_Option_HasRepr___rarg___closed__3;
x_50 = lean_string_append(x_48, x_49);
x_51 = l_IO_println___rarg___closed__1;
x_52 = lean_string_append(x_50, x_51);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_13);
lean_ctor_set(x_53, 1, x_52);
lean_inc(x_1);
lean_inc(x_6);
x_54 = lean_apply_3(x_1, x_4, x_6, x_53);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_56 = x_54;
} else {
 lean_dec_ref(x_54);
 x_56 = lean_box(0);
}
x_57 = l_Lean_IR_EmitC_emitIf___closed__3;
x_58 = lean_string_append(x_55, x_57);
x_59 = lean_string_append(x_58, x_51);
if (lean_is_scalar(x_56)) {
 x_60 = lean_alloc_ctor(0, 2, 0);
} else {
 x_60 = x_56;
}
lean_ctor_set(x_60, 0, x_13);
lean_ctor_set(x_60, 1, x_59);
x_61 = lean_apply_3(x_1, x_5, x_6, x_60);
return x_61;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_62 = lean_ctor_get(x_54, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_54, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_64 = x_54;
} else {
 lean_dec_ref(x_54);
 x_64 = lean_box(0);
}
if (lean_is_scalar(x_64)) {
 x_65 = lean_alloc_ctor(1, 2, 0);
} else {
 x_65 = x_64;
}
lean_ctor_set(x_65, 0, x_62);
lean_ctor_set(x_65, 1, x_63);
return x_65;
}
}
}
else
{
uint8_t x_66; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_66 = !lean_is_exclusive(x_14);
if (x_66 == 0)
{
return x_14;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_14, 0);
x_68 = lean_ctor_get(x_14, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_14);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_70 = lean_ctor_get(x_7, 1);
lean_inc(x_70);
lean_dec(x_7);
x_71 = l_Lean_IR_EmitC_emitIf___closed__1;
x_72 = lean_string_append(x_70, x_71);
x_73 = lean_box(0);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_72);
x_75 = l_Lean_IR_EmitC_emitTag(x_2, x_6, x_74);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_76 = lean_ctor_get(x_75, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 x_77 = x_75;
} else {
 lean_dec_ref(x_75);
 x_77 = lean_box(0);
}
x_78 = l_Lean_IR_EmitC_emitIf___closed__2;
x_79 = lean_string_append(x_76, x_78);
x_80 = l_Nat_repr(x_3);
x_81 = lean_string_append(x_79, x_80);
lean_dec(x_80);
x_82 = l_Option_HasRepr___rarg___closed__3;
x_83 = lean_string_append(x_81, x_82);
x_84 = l_IO_println___rarg___closed__1;
x_85 = lean_string_append(x_83, x_84);
if (lean_is_scalar(x_77)) {
 x_86 = lean_alloc_ctor(0, 2, 0);
} else {
 x_86 = x_77;
}
lean_ctor_set(x_86, 0, x_73);
lean_ctor_set(x_86, 1, x_85);
lean_inc(x_1);
lean_inc(x_6);
x_87 = lean_apply_3(x_1, x_4, x_6, x_86);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_88 = lean_ctor_get(x_87, 1);
lean_inc(x_88);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 x_89 = x_87;
} else {
 lean_dec_ref(x_87);
 x_89 = lean_box(0);
}
x_90 = l_Lean_IR_EmitC_emitIf___closed__3;
x_91 = lean_string_append(x_88, x_90);
x_92 = lean_string_append(x_91, x_84);
if (lean_is_scalar(x_89)) {
 x_93 = lean_alloc_ctor(0, 2, 0);
} else {
 x_93 = x_89;
}
lean_ctor_set(x_93, 0, x_73);
lean_ctor_set(x_93, 1, x_92);
x_94 = lean_apply_3(x_1, x_5, x_6, x_93);
return x_94;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_95 = lean_ctor_get(x_87, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_87, 1);
lean_inc(x_96);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 x_97 = x_87;
} else {
 lean_dec_ref(x_87);
 x_97 = lean_box(0);
}
if (lean_is_scalar(x_97)) {
 x_98 = lean_alloc_ctor(1, 2, 0);
} else {
 x_98 = x_97;
}
lean_ctor_set(x_98, 0, x_95);
lean_ctor_set(x_98, 1, x_96);
return x_98;
}
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_99 = lean_ctor_get(x_75, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_75, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 x_101 = x_75;
} else {
 lean_dec_ref(x_75);
 x_101 = lean_box(0);
}
if (lean_is_scalar(x_101)) {
 x_102 = lean_alloc_ctor(1, 2, 0);
} else {
 x_102 = x_101;
}
lean_ctor_set(x_102, 0, x_99);
lean_ctor_set(x_102, 1, x_100);
return x_102;
}
}
}
}
lean_object* _init_l_Array_mforAux___main___at_Lean_IR_EmitC_emitCase___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(":");
return x_1;
}
}
lean_object* _init_l_Array_mforAux___main___at_Lean_IR_EmitC_emitCase___spec__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("default: ");
return x_1;
}
}
lean_object* l_Array_mforAux___main___at_Lean_IR_EmitC_emitCase___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_2);
x_7 = lean_nat_dec_lt(x_3, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_5, 0);
lean_dec(x_9);
x_10 = lean_box(0);
lean_ctor_set(x_5, 0, x_10);
return x_5;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
lean_dec(x_5);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_array_fget(x_2, x_3);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_3, x_15);
lean_dec(x_3);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_14, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_14, 1);
lean_inc(x_18);
lean_dec(x_14);
x_19 = !lean_is_exclusive(x_5);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_20 = lean_ctor_get(x_5, 1);
x_21 = lean_ctor_get(x_5, 0);
lean_dec(x_21);
x_22 = lean_ctor_get(x_17, 1);
lean_inc(x_22);
lean_dec(x_17);
x_23 = l_Lean_IR_formatFnBody___main___closed__31;
x_24 = lean_string_append(x_20, x_23);
x_25 = l_Nat_repr(x_22);
x_26 = lean_string_append(x_24, x_25);
lean_dec(x_25);
x_27 = l_Array_mforAux___main___at_Lean_IR_EmitC_emitCase___spec__1___closed__1;
x_28 = lean_string_append(x_26, x_27);
x_29 = l_IO_println___rarg___closed__1;
x_30 = lean_string_append(x_28, x_29);
x_31 = lean_box(0);
lean_ctor_set(x_5, 1, x_30);
lean_ctor_set(x_5, 0, x_31);
lean_inc(x_1);
lean_inc(x_4);
x_32 = lean_apply_3(x_1, x_18, x_4, x_5);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_32, 0);
lean_dec(x_34);
lean_ctor_set(x_32, 0, x_31);
x_3 = x_16;
x_5 = x_32;
goto _start;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_32, 1);
lean_inc(x_36);
lean_dec(x_32);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_31);
lean_ctor_set(x_37, 1, x_36);
x_3 = x_16;
x_5 = x_37;
goto _start;
}
}
else
{
uint8_t x_39; 
lean_dec(x_16);
lean_dec(x_4);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_32);
if (x_39 == 0)
{
return x_32;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_32, 0);
x_41 = lean_ctor_get(x_32, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_32);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_43 = lean_ctor_get(x_5, 1);
lean_inc(x_43);
lean_dec(x_5);
x_44 = lean_ctor_get(x_17, 1);
lean_inc(x_44);
lean_dec(x_17);
x_45 = l_Lean_IR_formatFnBody___main___closed__31;
x_46 = lean_string_append(x_43, x_45);
x_47 = l_Nat_repr(x_44);
x_48 = lean_string_append(x_46, x_47);
lean_dec(x_47);
x_49 = l_Array_mforAux___main___at_Lean_IR_EmitC_emitCase___spec__1___closed__1;
x_50 = lean_string_append(x_48, x_49);
x_51 = l_IO_println___rarg___closed__1;
x_52 = lean_string_append(x_50, x_51);
x_53 = lean_box(0);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_52);
lean_inc(x_1);
lean_inc(x_4);
x_55 = lean_apply_3(x_1, x_18, x_4, x_54);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_57 = x_55;
} else {
 lean_dec_ref(x_55);
 x_57 = lean_box(0);
}
if (lean_is_scalar(x_57)) {
 x_58 = lean_alloc_ctor(0, 2, 0);
} else {
 x_58 = x_57;
}
lean_ctor_set(x_58, 0, x_53);
lean_ctor_set(x_58, 1, x_56);
x_3 = x_16;
x_5 = x_58;
goto _start;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_16);
lean_dec(x_4);
lean_dec(x_1);
x_60 = lean_ctor_get(x_55, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_55, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_62 = x_55;
} else {
 lean_dec_ref(x_55);
 x_62 = lean_box(0);
}
if (lean_is_scalar(x_62)) {
 x_63 = lean_alloc_ctor(1, 2, 0);
} else {
 x_63 = x_62;
}
lean_ctor_set(x_63, 0, x_60);
lean_ctor_set(x_63, 1, x_61);
return x_63;
}
}
}
else
{
lean_object* x_64; uint8_t x_65; 
x_64 = lean_ctor_get(x_14, 0);
lean_inc(x_64);
lean_dec(x_14);
x_65 = !lean_is_exclusive(x_5);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_66 = lean_ctor_get(x_5, 1);
x_67 = lean_ctor_get(x_5, 0);
lean_dec(x_67);
x_68 = l_Array_mforAux___main___at_Lean_IR_EmitC_emitCase___spec__1___closed__2;
x_69 = lean_string_append(x_66, x_68);
x_70 = l_IO_println___rarg___closed__1;
x_71 = lean_string_append(x_69, x_70);
x_72 = lean_box(0);
lean_ctor_set(x_5, 1, x_71);
lean_ctor_set(x_5, 0, x_72);
lean_inc(x_1);
lean_inc(x_4);
x_73 = lean_apply_3(x_1, x_64, x_4, x_5);
if (lean_obj_tag(x_73) == 0)
{
uint8_t x_74; 
x_74 = !lean_is_exclusive(x_73);
if (x_74 == 0)
{
lean_object* x_75; 
x_75 = lean_ctor_get(x_73, 0);
lean_dec(x_75);
lean_ctor_set(x_73, 0, x_72);
x_3 = x_16;
x_5 = x_73;
goto _start;
}
else
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_73, 1);
lean_inc(x_77);
lean_dec(x_73);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_72);
lean_ctor_set(x_78, 1, x_77);
x_3 = x_16;
x_5 = x_78;
goto _start;
}
}
else
{
uint8_t x_80; 
lean_dec(x_16);
lean_dec(x_4);
lean_dec(x_1);
x_80 = !lean_is_exclusive(x_73);
if (x_80 == 0)
{
return x_73;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_73, 0);
x_82 = lean_ctor_get(x_73, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_73);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_84 = lean_ctor_get(x_5, 1);
lean_inc(x_84);
lean_dec(x_5);
x_85 = l_Array_mforAux___main___at_Lean_IR_EmitC_emitCase___spec__1___closed__2;
x_86 = lean_string_append(x_84, x_85);
x_87 = l_IO_println___rarg___closed__1;
x_88 = lean_string_append(x_86, x_87);
x_89 = lean_box(0);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_88);
lean_inc(x_1);
lean_inc(x_4);
x_91 = lean_apply_3(x_1, x_64, x_4, x_90);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_91, 1);
lean_inc(x_92);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 x_93 = x_91;
} else {
 lean_dec_ref(x_91);
 x_93 = lean_box(0);
}
if (lean_is_scalar(x_93)) {
 x_94 = lean_alloc_ctor(0, 2, 0);
} else {
 x_94 = x_93;
}
lean_ctor_set(x_94, 0, x_89);
lean_ctor_set(x_94, 1, x_92);
x_3 = x_16;
x_5 = x_94;
goto _start;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
lean_dec(x_16);
lean_dec(x_4);
lean_dec(x_1);
x_96 = lean_ctor_get(x_91, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_91, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 x_98 = x_91;
} else {
 lean_dec_ref(x_91);
 x_98 = lean_box(0);
}
if (lean_is_scalar(x_98)) {
 x_99 = lean_alloc_ctor(1, 2, 0);
} else {
 x_99 = x_98;
}
lean_ctor_set(x_99, 0, x_96);
lean_ctor_set(x_99, 1, x_97);
return x_99;
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
lean_object* l_Lean_IR_EmitC_emitCase(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_EmitC_isIf(x_3);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_5, 1);
x_9 = lean_ctor_get(x_5, 0);
lean_dec(x_9);
x_10 = l_Lean_IR_EmitC_emitCase___closed__1;
x_11 = lean_string_append(x_8, x_10);
x_12 = lean_box(0);
lean_ctor_set(x_5, 1, x_11);
lean_ctor_set(x_5, 0, x_12);
x_13 = l_Lean_IR_EmitC_emitTag(x_2, x_4, x_5);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_15 = lean_ctor_get(x_13, 1);
x_16 = lean_ctor_get(x_13, 0);
lean_dec(x_16);
x_17 = l_Lean_IR_EmitC_emitCase___closed__2;
x_18 = lean_string_append(x_15, x_17);
x_19 = l_IO_println___rarg___closed__1;
x_20 = lean_string_append(x_18, x_19);
lean_ctor_set(x_13, 1, x_20);
lean_ctor_set(x_13, 0, x_12);
x_21 = l_Lean_IR_ensureHasDefault(x_3);
x_22 = lean_unsigned_to_nat(0u);
x_23 = l_Array_mforAux___main___at_Lean_IR_EmitC_emitCase___spec__1(x_1, x_21, x_22, x_4, x_13);
lean_dec(x_21);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_23, 1);
x_26 = lean_ctor_get(x_23, 0);
lean_dec(x_26);
x_27 = l_PersistentHashMap_Stats_toString___closed__5;
x_28 = lean_string_append(x_25, x_27);
x_29 = lean_string_append(x_28, x_19);
lean_ctor_set(x_23, 1, x_29);
lean_ctor_set(x_23, 0, x_12);
return x_23;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_30 = lean_ctor_get(x_23, 1);
lean_inc(x_30);
lean_dec(x_23);
x_31 = l_PersistentHashMap_Stats_toString___closed__5;
x_32 = lean_string_append(x_30, x_31);
x_33 = lean_string_append(x_32, x_19);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_12);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
else
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_23);
if (x_35 == 0)
{
return x_23;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_23, 0);
x_37 = lean_ctor_get(x_23, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_23);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_39 = lean_ctor_get(x_13, 1);
lean_inc(x_39);
lean_dec(x_13);
x_40 = l_Lean_IR_EmitC_emitCase___closed__2;
x_41 = lean_string_append(x_39, x_40);
x_42 = l_IO_println___rarg___closed__1;
x_43 = lean_string_append(x_41, x_42);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_12);
lean_ctor_set(x_44, 1, x_43);
x_45 = l_Lean_IR_ensureHasDefault(x_3);
x_46 = lean_unsigned_to_nat(0u);
x_47 = l_Array_mforAux___main___at_Lean_IR_EmitC_emitCase___spec__1(x_1, x_45, x_46, x_4, x_44);
lean_dec(x_45);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_49 = x_47;
} else {
 lean_dec_ref(x_47);
 x_49 = lean_box(0);
}
x_50 = l_PersistentHashMap_Stats_toString___closed__5;
x_51 = lean_string_append(x_48, x_50);
x_52 = lean_string_append(x_51, x_42);
if (lean_is_scalar(x_49)) {
 x_53 = lean_alloc_ctor(0, 2, 0);
} else {
 x_53 = x_49;
}
lean_ctor_set(x_53, 0, x_12);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_54 = lean_ctor_get(x_47, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_47, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_56 = x_47;
} else {
 lean_dec_ref(x_47);
 x_56 = lean_box(0);
}
if (lean_is_scalar(x_56)) {
 x_57 = lean_alloc_ctor(1, 2, 0);
} else {
 x_57 = x_56;
}
lean_ctor_set(x_57, 0, x_54);
lean_ctor_set(x_57, 1, x_55);
return x_57;
}
}
}
else
{
uint8_t x_58; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_58 = !lean_is_exclusive(x_13);
if (x_58 == 0)
{
return x_13;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_13, 0);
x_60 = lean_ctor_get(x_13, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_13);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_62 = lean_ctor_get(x_5, 1);
lean_inc(x_62);
lean_dec(x_5);
x_63 = l_Lean_IR_EmitC_emitCase___closed__1;
x_64 = lean_string_append(x_62, x_63);
x_65 = lean_box(0);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_64);
x_67 = l_Lean_IR_EmitC_emitTag(x_2, x_4, x_66);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_68 = lean_ctor_get(x_67, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_69 = x_67;
} else {
 lean_dec_ref(x_67);
 x_69 = lean_box(0);
}
x_70 = l_Lean_IR_EmitC_emitCase___closed__2;
x_71 = lean_string_append(x_68, x_70);
x_72 = l_IO_println___rarg___closed__1;
x_73 = lean_string_append(x_71, x_72);
if (lean_is_scalar(x_69)) {
 x_74 = lean_alloc_ctor(0, 2, 0);
} else {
 x_74 = x_69;
}
lean_ctor_set(x_74, 0, x_65);
lean_ctor_set(x_74, 1, x_73);
x_75 = l_Lean_IR_ensureHasDefault(x_3);
x_76 = lean_unsigned_to_nat(0u);
x_77 = l_Array_mforAux___main___at_Lean_IR_EmitC_emitCase___spec__1(x_1, x_75, x_76, x_4, x_74);
lean_dec(x_75);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_78 = lean_ctor_get(x_77, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 x_79 = x_77;
} else {
 lean_dec_ref(x_77);
 x_79 = lean_box(0);
}
x_80 = l_PersistentHashMap_Stats_toString___closed__5;
x_81 = lean_string_append(x_78, x_80);
x_82 = lean_string_append(x_81, x_72);
if (lean_is_scalar(x_79)) {
 x_83 = lean_alloc_ctor(0, 2, 0);
} else {
 x_83 = x_79;
}
lean_ctor_set(x_83, 0, x_65);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_84 = lean_ctor_get(x_77, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_77, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 x_86 = x_77;
} else {
 lean_dec_ref(x_77);
 x_86 = lean_box(0);
}
if (lean_is_scalar(x_86)) {
 x_87 = lean_alloc_ctor(1, 2, 0);
} else {
 x_87 = x_86;
}
lean_ctor_set(x_87, 0, x_84);
lean_ctor_set(x_87, 1, x_85);
return x_87;
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_88 = lean_ctor_get(x_67, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_67, 1);
lean_inc(x_89);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_90 = x_67;
} else {
 lean_dec_ref(x_67);
 x_90 = lean_box(0);
}
if (lean_is_scalar(x_90)) {
 x_91 = lean_alloc_ctor(1, 2, 0);
} else {
 x_91 = x_90;
}
lean_ctor_set(x_91, 0, x_88);
lean_ctor_set(x_91, 1, x_89);
return x_91;
}
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_3);
x_92 = lean_ctor_get(x_6, 0);
lean_inc(x_92);
lean_dec(x_6);
x_93 = lean_ctor_get(x_92, 1);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 0);
lean_inc(x_94);
lean_dec(x_92);
x_95 = lean_ctor_get(x_93, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_93, 1);
lean_inc(x_96);
lean_dec(x_93);
x_97 = l_Lean_IR_EmitC_emitIf(x_1, x_2, x_94, x_95, x_96, x_4, x_5);
return x_97;
}
}
}
lean_object* l_Array_mforAux___main___at_Lean_IR_EmitC_emitCase___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_mforAux___main___at_Lean_IR_EmitC_emitCase___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
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
lean_object* x_6; lean_object* x_7; 
if (x_3 == 0)
{
lean_object* x_61; uint8_t x_62; 
x_61 = lean_unsigned_to_nat(1u);
x_62 = lean_nat_dec_eq(x_2, x_61);
if (x_62 == 0)
{
lean_object* x_63; 
x_63 = l_Lean_IR_EmitC_emitInc___closed__2;
x_6 = x_63;
x_7 = x_5;
goto block_60;
}
else
{
lean_object* x_64; 
x_64 = l_Lean_IR_EmitC_emitInc___closed__3;
x_6 = x_64;
x_7 = x_5;
goto block_60;
}
}
else
{
lean_object* x_65; uint8_t x_66; 
x_65 = lean_unsigned_to_nat(1u);
x_66 = lean_nat_dec_eq(x_2, x_65);
if (x_66 == 0)
{
lean_object* x_67; 
x_67 = l_Lean_IR_EmitC_emitInc___closed__4;
x_6 = x_67;
x_7 = x_5;
goto block_60;
}
else
{
lean_object* x_68; 
x_68 = l_Lean_IR_EmitC_emitInc___closed__5;
x_6 = x_68;
x_7 = x_5;
goto block_60;
}
}
block_60:
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_9 = lean_ctor_get(x_7, 1);
x_10 = lean_ctor_get(x_7, 0);
lean_dec(x_10);
x_11 = lean_string_append(x_9, x_6);
lean_dec(x_6);
x_12 = l_Prod_HasRepr___rarg___closed__1;
x_13 = lean_string_append(x_11, x_12);
x_14 = l_Nat_repr(x_1);
x_15 = l_Lean_IR_VarId_HasToString___closed__1;
x_16 = lean_string_append(x_15, x_14);
lean_dec(x_14);
x_17 = lean_string_append(x_13, x_16);
lean_dec(x_16);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_dec_eq(x_2, x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_20 = l_List_reprAux___main___rarg___closed__1;
x_21 = lean_string_append(x_17, x_20);
x_22 = l_Nat_repr(x_2);
x_23 = lean_string_append(x_21, x_22);
lean_dec(x_22);
x_24 = l_Lean_IR_EmitC_emitInc___closed__1;
x_25 = lean_string_append(x_23, x_24);
x_26 = l_IO_println___rarg___closed__1;
x_27 = lean_string_append(x_25, x_26);
x_28 = lean_box(0);
lean_ctor_set(x_7, 1, x_27);
lean_ctor_set(x_7, 0, x_28);
return x_7;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_2);
x_29 = l_Lean_IR_EmitC_emitInc___closed__1;
x_30 = lean_string_append(x_17, x_29);
x_31 = l_IO_println___rarg___closed__1;
x_32 = lean_string_append(x_30, x_31);
x_33 = lean_box(0);
lean_ctor_set(x_7, 1, x_32);
lean_ctor_set(x_7, 0, x_33);
return x_7;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_34 = lean_ctor_get(x_7, 1);
lean_inc(x_34);
lean_dec(x_7);
x_35 = lean_string_append(x_34, x_6);
lean_dec(x_6);
x_36 = l_Prod_HasRepr___rarg___closed__1;
x_37 = lean_string_append(x_35, x_36);
x_38 = l_Nat_repr(x_1);
x_39 = l_Lean_IR_VarId_HasToString___closed__1;
x_40 = lean_string_append(x_39, x_38);
lean_dec(x_38);
x_41 = lean_string_append(x_37, x_40);
lean_dec(x_40);
x_42 = lean_unsigned_to_nat(1u);
x_43 = lean_nat_dec_eq(x_2, x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_44 = l_List_reprAux___main___rarg___closed__1;
x_45 = lean_string_append(x_41, x_44);
x_46 = l_Nat_repr(x_2);
x_47 = lean_string_append(x_45, x_46);
lean_dec(x_46);
x_48 = l_Lean_IR_EmitC_emitInc___closed__1;
x_49 = lean_string_append(x_47, x_48);
x_50 = l_IO_println___rarg___closed__1;
x_51 = lean_string_append(x_49, x_50);
x_52 = lean_box(0);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_51);
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_2);
x_54 = l_Lean_IR_EmitC_emitInc___closed__1;
x_55 = lean_string_append(x_41, x_54);
x_56 = l_IO_println___rarg___closed__1;
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
if (x_3 == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_7 = lean_ctor_get(x_5, 1);
x_8 = lean_ctor_get(x_5, 0);
lean_dec(x_8);
x_9 = l_Lean_IR_EmitC_emitDec___closed__1;
x_10 = lean_string_append(x_7, x_9);
x_11 = l_Prod_HasRepr___rarg___closed__1;
x_12 = lean_string_append(x_10, x_11);
x_13 = l_Nat_repr(x_1);
x_14 = l_Lean_IR_VarId_HasToString___closed__1;
x_15 = lean_string_append(x_14, x_13);
lean_dec(x_13);
x_16 = lean_string_append(x_12, x_15);
lean_dec(x_15);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_dec_eq(x_2, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_19 = l_List_reprAux___main___rarg___closed__1;
x_20 = lean_string_append(x_16, x_19);
x_21 = l_Nat_repr(x_2);
x_22 = lean_string_append(x_20, x_21);
lean_dec(x_21);
x_23 = l_Lean_IR_EmitC_emitInc___closed__1;
x_24 = lean_string_append(x_22, x_23);
x_25 = l_IO_println___rarg___closed__1;
x_26 = lean_string_append(x_24, x_25);
x_27 = lean_box(0);
lean_ctor_set(x_5, 1, x_26);
lean_ctor_set(x_5, 0, x_27);
return x_5;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_2);
x_28 = l_Lean_IR_EmitC_emitInc___closed__1;
x_29 = lean_string_append(x_16, x_28);
x_30 = l_IO_println___rarg___closed__1;
x_31 = lean_string_append(x_29, x_30);
x_32 = lean_box(0);
lean_ctor_set(x_5, 1, x_31);
lean_ctor_set(x_5, 0, x_32);
return x_5;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_33 = lean_ctor_get(x_5, 1);
lean_inc(x_33);
lean_dec(x_5);
x_34 = l_Lean_IR_EmitC_emitDec___closed__1;
x_35 = lean_string_append(x_33, x_34);
x_36 = l_Prod_HasRepr___rarg___closed__1;
x_37 = lean_string_append(x_35, x_36);
x_38 = l_Nat_repr(x_1);
x_39 = l_Lean_IR_VarId_HasToString___closed__1;
x_40 = lean_string_append(x_39, x_38);
lean_dec(x_38);
x_41 = lean_string_append(x_37, x_40);
lean_dec(x_40);
x_42 = lean_unsigned_to_nat(1u);
x_43 = lean_nat_dec_eq(x_2, x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_44 = l_List_reprAux___main___rarg___closed__1;
x_45 = lean_string_append(x_41, x_44);
x_46 = l_Nat_repr(x_2);
x_47 = lean_string_append(x_45, x_46);
lean_dec(x_46);
x_48 = l_Lean_IR_EmitC_emitInc___closed__1;
x_49 = lean_string_append(x_47, x_48);
x_50 = l_IO_println___rarg___closed__1;
x_51 = lean_string_append(x_49, x_50);
x_52 = lean_box(0);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_51);
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_2);
x_54 = l_Lean_IR_EmitC_emitInc___closed__1;
x_55 = lean_string_append(x_41, x_54);
x_56 = l_IO_println___rarg___closed__1;
x_57 = lean_string_append(x_55, x_56);
x_58 = lean_box(0);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_57);
return x_59;
}
}
}
else
{
uint8_t x_60; 
x_60 = !lean_is_exclusive(x_5);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_61 = lean_ctor_get(x_5, 1);
x_62 = lean_ctor_get(x_5, 0);
lean_dec(x_62);
x_63 = l_Lean_IR_EmitC_emitDec___closed__2;
x_64 = lean_string_append(x_61, x_63);
x_65 = l_Prod_HasRepr___rarg___closed__1;
x_66 = lean_string_append(x_64, x_65);
x_67 = l_Nat_repr(x_1);
x_68 = l_Lean_IR_VarId_HasToString___closed__1;
x_69 = lean_string_append(x_68, x_67);
lean_dec(x_67);
x_70 = lean_string_append(x_66, x_69);
lean_dec(x_69);
x_71 = lean_unsigned_to_nat(1u);
x_72 = lean_nat_dec_eq(x_2, x_71);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_73 = l_List_reprAux___main___rarg___closed__1;
x_74 = lean_string_append(x_70, x_73);
x_75 = l_Nat_repr(x_2);
x_76 = lean_string_append(x_74, x_75);
lean_dec(x_75);
x_77 = l_Lean_IR_EmitC_emitInc___closed__1;
x_78 = lean_string_append(x_76, x_77);
x_79 = l_IO_println___rarg___closed__1;
x_80 = lean_string_append(x_78, x_79);
x_81 = lean_box(0);
lean_ctor_set(x_5, 1, x_80);
lean_ctor_set(x_5, 0, x_81);
return x_5;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_2);
x_82 = l_Lean_IR_EmitC_emitInc___closed__1;
x_83 = lean_string_append(x_70, x_82);
x_84 = l_IO_println___rarg___closed__1;
x_85 = lean_string_append(x_83, x_84);
x_86 = lean_box(0);
lean_ctor_set(x_5, 1, x_85);
lean_ctor_set(x_5, 0, x_86);
return x_5;
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; 
x_87 = lean_ctor_get(x_5, 1);
lean_inc(x_87);
lean_dec(x_5);
x_88 = l_Lean_IR_EmitC_emitDec___closed__2;
x_89 = lean_string_append(x_87, x_88);
x_90 = l_Prod_HasRepr___rarg___closed__1;
x_91 = lean_string_append(x_89, x_90);
x_92 = l_Nat_repr(x_1);
x_93 = l_Lean_IR_VarId_HasToString___closed__1;
x_94 = lean_string_append(x_93, x_92);
lean_dec(x_92);
x_95 = lean_string_append(x_91, x_94);
lean_dec(x_94);
x_96 = lean_unsigned_to_nat(1u);
x_97 = lean_nat_dec_eq(x_2, x_96);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_98 = l_List_reprAux___main___rarg___closed__1;
x_99 = lean_string_append(x_95, x_98);
x_100 = l_Nat_repr(x_2);
x_101 = lean_string_append(x_99, x_100);
lean_dec(x_100);
x_102 = l_Lean_IR_EmitC_emitInc___closed__1;
x_103 = lean_string_append(x_101, x_102);
x_104 = l_IO_println___rarg___closed__1;
x_105 = lean_string_append(x_103, x_104);
x_106 = lean_box(0);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_105);
return x_107;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
lean_dec(x_2);
x_108 = l_Lean_IR_EmitC_emitInc___closed__1;
x_109 = lean_string_append(x_95, x_108);
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
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_ctor_get(x_3, 0);
lean_dec(x_6);
x_7 = l_Lean_IR_EmitC_emitDel___closed__1;
x_8 = lean_string_append(x_5, x_7);
x_9 = l_Nat_repr(x_1);
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
lean_ctor_set(x_3, 1, x_16);
lean_ctor_set(x_3, 0, x_17);
return x_3;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_18 = lean_ctor_get(x_3, 1);
lean_inc(x_18);
lean_dec(x_3);
x_19 = l_Lean_IR_EmitC_emitDel___closed__1;
x_20 = lean_string_append(x_18, x_19);
x_21 = l_Nat_repr(x_1);
x_22 = l_Lean_IR_VarId_HasToString___closed__1;
x_23 = lean_string_append(x_22, x_21);
lean_dec(x_21);
x_24 = lean_string_append(x_20, x_23);
lean_dec(x_23);
x_25 = l_Lean_IR_EmitC_emitInc___closed__1;
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
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_6 = lean_ctor_get(x_4, 1);
x_7 = lean_ctor_get(x_4, 0);
lean_dec(x_7);
x_8 = l_Lean_IR_EmitC_emitSetTag___closed__1;
x_9 = lean_string_append(x_6, x_8);
x_10 = l_Nat_repr(x_1);
x_11 = l_Lean_IR_VarId_HasToString___closed__1;
x_12 = lean_string_append(x_11, x_10);
lean_dec(x_10);
x_13 = lean_string_append(x_9, x_12);
lean_dec(x_12);
x_14 = l_List_reprAux___main___rarg___closed__1;
x_15 = lean_string_append(x_13, x_14);
x_16 = l_Nat_repr(x_2);
x_17 = lean_string_append(x_15, x_16);
lean_dec(x_16);
x_18 = l_Lean_IR_EmitC_emitInc___closed__1;
x_19 = lean_string_append(x_17, x_18);
x_20 = l_IO_println___rarg___closed__1;
x_21 = lean_string_append(x_19, x_20);
x_22 = lean_box(0);
lean_ctor_set(x_4, 1, x_21);
lean_ctor_set(x_4, 0, x_22);
return x_4;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_23 = lean_ctor_get(x_4, 1);
lean_inc(x_23);
lean_dec(x_4);
x_24 = l_Lean_IR_EmitC_emitSetTag___closed__1;
x_25 = lean_string_append(x_23, x_24);
x_26 = l_Nat_repr(x_1);
x_27 = l_Lean_IR_VarId_HasToString___closed__1;
x_28 = lean_string_append(x_27, x_26);
lean_dec(x_26);
x_29 = lean_string_append(x_25, x_28);
lean_dec(x_28);
x_30 = l_List_reprAux___main___rarg___closed__1;
x_31 = lean_string_append(x_29, x_30);
x_32 = l_Nat_repr(x_2);
x_33 = lean_string_append(x_31, x_32);
lean_dec(x_32);
x_34 = l_Lean_IR_EmitC_emitInc___closed__1;
x_35 = lean_string_append(x_33, x_34);
x_36 = l_IO_println___rarg___closed__1;
x_37 = lean_string_append(x_35, x_36);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
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
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_7 = lean_ctor_get(x_5, 1);
x_8 = lean_ctor_get(x_5, 0);
lean_dec(x_8);
x_9 = l_Lean_IR_EmitC_emitSet___closed__1;
x_10 = lean_string_append(x_7, x_9);
x_11 = l_Nat_repr(x_1);
x_12 = l_Lean_IR_VarId_HasToString___closed__1;
x_13 = lean_string_append(x_12, x_11);
lean_dec(x_11);
x_14 = lean_string_append(x_10, x_13);
lean_dec(x_13);
x_15 = l_List_reprAux___main___rarg___closed__1;
x_16 = lean_string_append(x_14, x_15);
x_17 = l_Nat_repr(x_2);
x_18 = lean_string_append(x_16, x_17);
lean_dec(x_17);
x_19 = lean_string_append(x_18, x_15);
x_20 = lean_box(0);
lean_ctor_set(x_5, 1, x_19);
lean_ctor_set(x_5, 0, x_20);
x_21 = l_Lean_IR_EmitC_emitArg(x_3, x_4, x_5);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_23 = lean_ctor_get(x_21, 1);
x_24 = lean_ctor_get(x_21, 0);
lean_dec(x_24);
x_25 = l_Lean_IR_EmitC_emitInc___closed__1;
x_26 = lean_string_append(x_23, x_25);
x_27 = l_IO_println___rarg___closed__1;
x_28 = lean_string_append(x_26, x_27);
lean_ctor_set(x_21, 1, x_28);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_29 = lean_ctor_get(x_21, 1);
lean_inc(x_29);
lean_dec(x_21);
x_30 = l_Lean_IR_EmitC_emitInc___closed__1;
x_31 = lean_string_append(x_29, x_30);
x_32 = l_IO_println___rarg___closed__1;
x_33 = lean_string_append(x_31, x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_20);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
else
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_21);
if (x_35 == 0)
{
return x_21;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_21, 0);
x_37 = lean_ctor_get(x_21, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_21);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_39 = lean_ctor_get(x_5, 1);
lean_inc(x_39);
lean_dec(x_5);
x_40 = l_Lean_IR_EmitC_emitSet___closed__1;
x_41 = lean_string_append(x_39, x_40);
x_42 = l_Nat_repr(x_1);
x_43 = l_Lean_IR_VarId_HasToString___closed__1;
x_44 = lean_string_append(x_43, x_42);
lean_dec(x_42);
x_45 = lean_string_append(x_41, x_44);
lean_dec(x_44);
x_46 = l_List_reprAux___main___rarg___closed__1;
x_47 = lean_string_append(x_45, x_46);
x_48 = l_Nat_repr(x_2);
x_49 = lean_string_append(x_47, x_48);
lean_dec(x_48);
x_50 = lean_string_append(x_49, x_46);
x_51 = lean_box(0);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_50);
x_53 = l_Lean_IR_EmitC_emitArg(x_3, x_4, x_52);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_55 = x_53;
} else {
 lean_dec_ref(x_53);
 x_55 = lean_box(0);
}
x_56 = l_Lean_IR_EmitC_emitInc___closed__1;
x_57 = lean_string_append(x_54, x_56);
x_58 = l_IO_println___rarg___closed__1;
x_59 = lean_string_append(x_57, x_58);
if (lean_is_scalar(x_55)) {
 x_60 = lean_alloc_ctor(0, 2, 0);
} else {
 x_60 = x_55;
}
lean_ctor_set(x_60, 0, x_51);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_61 = lean_ctor_get(x_53, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_53, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_63 = x_53;
} else {
 lean_dec_ref(x_53);
 x_63 = lean_box(0);
}
if (lean_is_scalar(x_63)) {
 x_64 = lean_alloc_ctor(1, 2, 0);
} else {
 x_64 = x_63;
}
lean_ctor_set(x_64, 0, x_61);
lean_ctor_set(x_64, 1, x_62);
return x_64;
}
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
uint8_t x_7; 
lean_dec(x_1);
x_7 = !lean_is_exclusive(x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_4, 1);
x_9 = lean_ctor_get(x_4, 0);
lean_dec(x_9);
x_10 = l_Nat_repr(x_2);
x_11 = lean_string_append(x_8, x_10);
lean_dec(x_10);
x_12 = lean_box(0);
lean_ctor_set(x_4, 1, x_11);
lean_ctor_set(x_4, 0, x_12);
return x_4;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_4, 1);
lean_inc(x_13);
lean_dec(x_4);
x_14 = l_Nat_repr(x_2);
x_15 = lean_string_append(x_13, x_14);
lean_dec(x_14);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_4);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_19 = lean_ctor_get(x_4, 1);
x_20 = lean_ctor_get(x_4, 0);
lean_dec(x_20);
x_21 = l_Lean_IR_EmitC_emitOffset___closed__1;
x_22 = lean_string_append(x_19, x_21);
x_23 = l_Nat_repr(x_1);
x_24 = lean_string_append(x_22, x_23);
lean_dec(x_23);
x_25 = lean_nat_dec_lt(x_5, x_2);
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec(x_2);
x_26 = lean_box(0);
lean_ctor_set(x_4, 1, x_24);
lean_ctor_set(x_4, 0, x_26);
return x_4;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = l_Lean_IR_EmitC_emitOffset___closed__2;
x_28 = lean_string_append(x_24, x_27);
x_29 = l_Nat_repr(x_2);
x_30 = lean_string_append(x_28, x_29);
lean_dec(x_29);
x_31 = lean_box(0);
lean_ctor_set(x_4, 1, x_30);
lean_ctor_set(x_4, 0, x_31);
return x_4;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_32 = lean_ctor_get(x_4, 1);
lean_inc(x_32);
lean_dec(x_4);
x_33 = l_Lean_IR_EmitC_emitOffset___closed__1;
x_34 = lean_string_append(x_32, x_33);
x_35 = l_Nat_repr(x_1);
x_36 = lean_string_append(x_34, x_35);
lean_dec(x_35);
x_37 = lean_nat_dec_lt(x_5, x_2);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_2);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_36);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_40 = l_Lean_IR_EmitC_emitOffset___closed__2;
x_41 = lean_string_append(x_36, x_40);
x_42 = l_Nat_repr(x_2);
x_43 = lean_string_append(x_41, x_42);
lean_dec(x_42);
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
return x_45;
}
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
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_7 = lean_ctor_get(x_5, 1);
x_8 = lean_ctor_get(x_5, 0);
lean_dec(x_8);
x_9 = l_Lean_IR_EmitC_emitUSet___closed__1;
x_10 = lean_string_append(x_7, x_9);
x_11 = l_Nat_repr(x_1);
x_12 = l_Lean_IR_VarId_HasToString___closed__1;
x_13 = lean_string_append(x_12, x_11);
lean_dec(x_11);
x_14 = lean_string_append(x_10, x_13);
lean_dec(x_13);
x_15 = l_List_reprAux___main___rarg___closed__1;
x_16 = lean_string_append(x_14, x_15);
x_17 = l_Nat_repr(x_2);
x_18 = lean_string_append(x_16, x_17);
lean_dec(x_17);
x_19 = lean_string_append(x_18, x_15);
x_20 = l_Nat_repr(x_3);
x_21 = lean_string_append(x_12, x_20);
lean_dec(x_20);
x_22 = lean_string_append(x_19, x_21);
lean_dec(x_21);
x_23 = l_Lean_IR_EmitC_emitInc___closed__1;
x_24 = lean_string_append(x_22, x_23);
x_25 = l_IO_println___rarg___closed__1;
x_26 = lean_string_append(x_24, x_25);
x_27 = lean_box(0);
lean_ctor_set(x_5, 1, x_26);
lean_ctor_set(x_5, 0, x_27);
return x_5;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_28 = lean_ctor_get(x_5, 1);
lean_inc(x_28);
lean_dec(x_5);
x_29 = l_Lean_IR_EmitC_emitUSet___closed__1;
x_30 = lean_string_append(x_28, x_29);
x_31 = l_Nat_repr(x_1);
x_32 = l_Lean_IR_VarId_HasToString___closed__1;
x_33 = lean_string_append(x_32, x_31);
lean_dec(x_31);
x_34 = lean_string_append(x_30, x_33);
lean_dec(x_33);
x_35 = l_List_reprAux___main___rarg___closed__1;
x_36 = lean_string_append(x_34, x_35);
x_37 = l_Nat_repr(x_2);
x_38 = lean_string_append(x_36, x_37);
lean_dec(x_37);
x_39 = lean_string_append(x_38, x_35);
x_40 = l_Nat_repr(x_3);
x_41 = lean_string_append(x_32, x_40);
lean_dec(x_40);
x_42 = lean_string_append(x_39, x_41);
lean_dec(x_41);
x_43 = l_Lean_IR_EmitC_emitInc___closed__1;
x_44 = lean_string_append(x_42, x_43);
x_45 = l_IO_println___rarg___closed__1;
x_46 = lean_string_append(x_44, x_45);
x_47 = lean_box(0);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
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
x_1 = lean_mk_string("invalid instruction");
return x_1;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitSSet___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("floats are not supported yet");
return x_1;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitSSet___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("lean_ctor_set_uint8");
return x_1;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitSSet___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("lean_ctor_set_uint16");
return x_1;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitSSet___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("lean_ctor_set_uint32");
return x_1;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitSSet___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("lean_ctor_set_uint64");
return x_1;
}
}
lean_object* l_Lean_IR_EmitC_emitSSet(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_46; lean_object* x_54; 
x_54 = lean_box(x_5);
switch (lean_obj_tag(x_54)) {
case 0:
{
uint8_t x_55; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_55 = !lean_is_exclusive(x_7);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_7, 0);
lean_dec(x_56);
x_57 = l_Lean_IR_EmitC_emitSSet___closed__2;
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 0, x_57);
return x_7;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_7, 1);
lean_inc(x_58);
lean_dec(x_7);
x_59 = l_Lean_IR_EmitC_emitSSet___closed__2;
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_58);
return x_60;
}
}
case 1:
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_7, 1);
lean_inc(x_61);
lean_dec(x_7);
x_62 = l_Lean_IR_EmitC_emitSSet___closed__3;
x_63 = lean_string_append(x_61, x_62);
x_8 = x_63;
goto block_45;
}
case 2:
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_7, 1);
lean_inc(x_64);
lean_dec(x_7);
x_65 = l_Lean_IR_EmitC_emitSSet___closed__4;
x_66 = lean_string_append(x_64, x_65);
x_8 = x_66;
goto block_45;
}
case 3:
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_7, 1);
lean_inc(x_67);
lean_dec(x_7);
x_68 = l_Lean_IR_EmitC_emitSSet___closed__5;
x_69 = lean_string_append(x_67, x_68);
x_8 = x_69;
goto block_45;
}
case 4:
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_7, 1);
lean_inc(x_70);
lean_dec(x_7);
x_71 = l_Lean_IR_EmitC_emitSSet___closed__6;
x_72 = lean_string_append(x_70, x_71);
x_8 = x_72;
goto block_45;
}
default: 
{
lean_object* x_73; 
lean_dec(x_54);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_73 = lean_box(0);
x_46 = x_73;
goto block_53;
}
}
block_45:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
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
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = l_Lean_IR_EmitC_emitOffset(x_2, x_3, x_6, x_18);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_21 = lean_ctor_get(x_19, 1);
x_22 = lean_ctor_get(x_19, 0);
lean_dec(x_22);
x_23 = lean_string_append(x_21, x_15);
x_24 = l_Nat_repr(x_4);
x_25 = lean_string_append(x_12, x_24);
lean_dec(x_24);
x_26 = lean_string_append(x_23, x_25);
lean_dec(x_25);
x_27 = l_Lean_IR_EmitC_emitInc___closed__1;
x_28 = lean_string_append(x_26, x_27);
x_29 = l_IO_println___rarg___closed__1;
x_30 = lean_string_append(x_28, x_29);
lean_ctor_set(x_19, 1, x_30);
lean_ctor_set(x_19, 0, x_17);
return x_19;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_31 = lean_ctor_get(x_19, 1);
lean_inc(x_31);
lean_dec(x_19);
x_32 = lean_string_append(x_31, x_15);
x_33 = l_Nat_repr(x_4);
x_34 = lean_string_append(x_12, x_33);
lean_dec(x_33);
x_35 = lean_string_append(x_32, x_34);
lean_dec(x_34);
x_36 = l_Lean_IR_EmitC_emitInc___closed__1;
x_37 = lean_string_append(x_35, x_36);
x_38 = l_IO_println___rarg___closed__1;
x_39 = lean_string_append(x_37, x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_17);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
else
{
uint8_t x_41; 
lean_dec(x_4);
x_41 = !lean_is_exclusive(x_19);
if (x_41 == 0)
{
return x_19;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_19, 0);
x_43 = lean_ctor_get(x_19, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_19);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
block_53:
{
uint8_t x_47; 
lean_dec(x_46);
x_47 = !lean_is_exclusive(x_7);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_7, 0);
lean_dec(x_48);
x_49 = l_Lean_IR_EmitC_emitSSet___closed__1;
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 0, x_49);
return x_7;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_7, 1);
lean_inc(x_50);
lean_dec(x_7);
x_51 = l_Lean_IR_EmitC_emitSSet___closed__1;
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_50);
return x_52;
}
}
}
}
lean_object* l_Lean_IR_EmitC_emitSSet___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_5);
lean_dec(x_5);
x_9 = l_Lean_IR_EmitC_emitSSet(x_1, x_2, x_3, x_4, x_8, x_6, x_7);
lean_dec(x_6);
return x_9;
}
}
lean_object* _init_l_Nat_mforAux___main___at_Lean_IR_EmitC_emitJmp___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" = ");
return x_1;
}
}
lean_object* l_Nat_mforAux___main___at_Lean_IR_EmitC_emitJmp___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_eq(x_4, x_7);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_6);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_10 = lean_ctor_get(x_6, 1);
x_11 = lean_ctor_get(x_6, 0);
lean_dec(x_11);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_sub(x_4, x_12);
lean_dec(x_4);
x_14 = lean_nat_sub(x_3, x_13);
x_15 = lean_nat_sub(x_14, x_12);
lean_dec(x_14);
x_16 = l_Lean_IR_paramInh;
x_17 = lean_array_get(x_16, x_2, x_15);
x_18 = l_Lean_IR_Arg_Inhabited;
x_19 = lean_array_get(x_18, x_1, x_15);
lean_dec(x_15);
x_20 = lean_ctor_get(x_17, 0);
lean_inc(x_20);
lean_dec(x_17);
x_21 = l_Nat_repr(x_20);
x_22 = l_Lean_IR_VarId_HasToString___closed__1;
x_23 = lean_string_append(x_22, x_21);
lean_dec(x_21);
x_24 = lean_string_append(x_10, x_23);
lean_dec(x_23);
x_25 = l_Nat_mforAux___main___at_Lean_IR_EmitC_emitJmp___spec__1___closed__1;
x_26 = lean_string_append(x_24, x_25);
x_27 = lean_box(0);
lean_ctor_set(x_6, 1, x_26);
lean_ctor_set(x_6, 0, x_27);
x_28 = l_Lean_IR_EmitC_emitArg(x_19, x_5, x_6);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_30 = lean_ctor_get(x_28, 1);
x_31 = lean_ctor_get(x_28, 0);
lean_dec(x_31);
x_32 = l_Lean_IR_formatFnBody___main___closed__3;
x_33 = lean_string_append(x_30, x_32);
x_34 = l_IO_println___rarg___closed__1;
x_35 = lean_string_append(x_33, x_34);
lean_ctor_set(x_28, 1, x_35);
lean_ctor_set(x_28, 0, x_27);
x_4 = x_13;
x_6 = x_28;
goto _start;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_37 = lean_ctor_get(x_28, 1);
lean_inc(x_37);
lean_dec(x_28);
x_38 = l_Lean_IR_formatFnBody___main___closed__3;
x_39 = lean_string_append(x_37, x_38);
x_40 = l_IO_println___rarg___closed__1;
x_41 = lean_string_append(x_39, x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_27);
lean_ctor_set(x_42, 1, x_41);
x_4 = x_13;
x_6 = x_42;
goto _start;
}
}
else
{
uint8_t x_44; 
lean_dec(x_13);
x_44 = !lean_is_exclusive(x_28);
if (x_44 == 0)
{
return x_28;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_28, 0);
x_46 = lean_ctor_get(x_28, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_28);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_48 = lean_ctor_get(x_6, 1);
lean_inc(x_48);
lean_dec(x_6);
x_49 = lean_unsigned_to_nat(1u);
x_50 = lean_nat_sub(x_4, x_49);
lean_dec(x_4);
x_51 = lean_nat_sub(x_3, x_50);
x_52 = lean_nat_sub(x_51, x_49);
lean_dec(x_51);
x_53 = l_Lean_IR_paramInh;
x_54 = lean_array_get(x_53, x_2, x_52);
x_55 = l_Lean_IR_Arg_Inhabited;
x_56 = lean_array_get(x_55, x_1, x_52);
lean_dec(x_52);
x_57 = lean_ctor_get(x_54, 0);
lean_inc(x_57);
lean_dec(x_54);
x_58 = l_Nat_repr(x_57);
x_59 = l_Lean_IR_VarId_HasToString___closed__1;
x_60 = lean_string_append(x_59, x_58);
lean_dec(x_58);
x_61 = lean_string_append(x_48, x_60);
lean_dec(x_60);
x_62 = l_Nat_mforAux___main___at_Lean_IR_EmitC_emitJmp___spec__1___closed__1;
x_63 = lean_string_append(x_61, x_62);
x_64 = lean_box(0);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_63);
x_66 = l_Lean_IR_EmitC_emitArg(x_56, x_5, x_65);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_67 = lean_ctor_get(x_66, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 x_68 = x_66;
} else {
 lean_dec_ref(x_66);
 x_68 = lean_box(0);
}
x_69 = l_Lean_IR_formatFnBody___main___closed__3;
x_70 = lean_string_append(x_67, x_69);
x_71 = l_IO_println___rarg___closed__1;
x_72 = lean_string_append(x_70, x_71);
if (lean_is_scalar(x_68)) {
 x_73 = lean_alloc_ctor(0, 2, 0);
} else {
 x_73 = x_68;
}
lean_ctor_set(x_73, 0, x_64);
lean_ctor_set(x_73, 1, x_72);
x_4 = x_50;
x_6 = x_73;
goto _start;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_50);
x_75 = lean_ctor_get(x_66, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_66, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 x_77 = x_66;
} else {
 lean_dec_ref(x_66);
 x_77 = lean_box(0);
}
if (lean_is_scalar(x_77)) {
 x_78 = lean_alloc_ctor(1, 2, 0);
} else {
 x_78 = x_77;
}
lean_ctor_set(x_78, 0, x_75);
lean_ctor_set(x_78, 1, x_76);
return x_78;
}
}
}
else
{
uint8_t x_79; 
lean_dec(x_4);
x_79 = !lean_is_exclusive(x_6);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; 
x_80 = lean_ctor_get(x_6, 0);
lean_dec(x_80);
x_81 = lean_box(0);
lean_ctor_set(x_6, 0, x_81);
return x_6;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_6, 1);
lean_inc(x_82);
lean_dec(x_6);
x_83 = lean_box(0);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_82);
return x_84;
}
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
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_array_get_size(x_2);
x_9 = lean_array_get_size(x_7);
x_10 = lean_nat_dec_eq(x_8, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_11 = l_Lean_IR_EmitC_emitJmp___closed__1;
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 0, x_11);
return x_5;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_box(0);
lean_ctor_set(x_5, 0, x_12);
lean_inc(x_8);
x_13 = l_Nat_mforAux___main___at_Lean_IR_EmitC_emitJmp___spec__1(x_2, x_7, x_8, x_8, x_3, x_5);
lean_dec(x_8);
lean_dec(x_7);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_15 = lean_ctor_get(x_13, 1);
x_16 = lean_ctor_get(x_13, 0);
lean_dec(x_16);
x_17 = l_Lean_IR_EmitC_emitJmp___closed__2;
x_18 = lean_string_append(x_15, x_17);
x_19 = l_Nat_repr(x_1);
x_20 = l_Lean_IR_JoinPointId_HasToString___closed__1;
x_21 = lean_string_append(x_20, x_19);
lean_dec(x_19);
x_22 = lean_string_append(x_18, x_21);
lean_dec(x_21);
x_23 = l_Lean_IR_formatFnBody___main___closed__3;
x_24 = lean_string_append(x_22, x_23);
x_25 = l_IO_println___rarg___closed__1;
x_26 = lean_string_append(x_24, x_25);
lean_ctor_set(x_13, 1, x_26);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_27 = lean_ctor_get(x_13, 1);
lean_inc(x_27);
lean_dec(x_13);
x_28 = l_Lean_IR_EmitC_emitJmp___closed__2;
x_29 = lean_string_append(x_27, x_28);
x_30 = l_Nat_repr(x_1);
x_31 = l_Lean_IR_JoinPointId_HasToString___closed__1;
x_32 = lean_string_append(x_31, x_30);
lean_dec(x_30);
x_33 = lean_string_append(x_29, x_32);
lean_dec(x_32);
x_34 = l_Lean_IR_formatFnBody___main___closed__3;
x_35 = lean_string_append(x_33, x_34);
x_36 = l_IO_println___rarg___closed__1;
x_37 = lean_string_append(x_35, x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_12);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
else
{
uint8_t x_39; 
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_13);
if (x_39 == 0)
{
return x_13;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_13, 0);
x_41 = lean_ctor_get(x_13, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_13);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_43 = lean_ctor_get(x_5, 0);
x_44 = lean_ctor_get(x_5, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_5);
x_45 = lean_array_get_size(x_2);
x_46 = lean_array_get_size(x_43);
x_47 = lean_nat_dec_eq(x_45, x_46);
lean_dec(x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_45);
lean_dec(x_43);
lean_dec(x_1);
x_48 = l_Lean_IR_EmitC_emitJmp___closed__1;
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_44);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_box(0);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_44);
lean_inc(x_45);
x_52 = l_Nat_mforAux___main___at_Lean_IR_EmitC_emitJmp___spec__1(x_2, x_43, x_45, x_45, x_3, x_51);
lean_dec(x_45);
lean_dec(x_43);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
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
x_61 = l_Lean_IR_formatFnBody___main___closed__3;
x_62 = lean_string_append(x_60, x_61);
x_63 = l_IO_println___rarg___closed__1;
x_64 = lean_string_append(x_62, x_63);
if (lean_is_scalar(x_54)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_54;
}
lean_ctor_set(x_65, 0, x_50);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_1);
x_66 = lean_ctor_get(x_52, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_52, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_68 = x_52;
} else {
 lean_dec_ref(x_52);
 x_68 = lean_box(0);
}
if (lean_is_scalar(x_68)) {
 x_69 = lean_alloc_ctor(1, 2, 0);
} else {
 x_69 = x_68;
}
lean_ctor_set(x_69, 0, x_66);
lean_ctor_set(x_69, 1, x_67);
return x_69;
}
}
}
}
else
{
uint8_t x_70; 
lean_dec(x_1);
x_70 = !lean_is_exclusive(x_5);
if (x_70 == 0)
{
return x_5;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_5, 0);
x_72 = lean_ctor_get(x_5, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_5);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
}
lean_object* l_Nat_mforAux___main___at_Lean_IR_EmitC_emitJmp___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Nat_mforAux___main___at_Lean_IR_EmitC_emitJmp___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
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
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_ctor_get(x_3, 0);
lean_dec(x_6);
x_7 = l_Nat_repr(x_1);
x_8 = l_Lean_IR_VarId_HasToString___closed__1;
x_9 = lean_string_append(x_8, x_7);
lean_dec(x_7);
x_10 = lean_string_append(x_5, x_9);
lean_dec(x_9);
x_11 = l_Nat_mforAux___main___at_Lean_IR_EmitC_emitJmp___spec__1___closed__1;
x_12 = lean_string_append(x_10, x_11);
x_13 = lean_box(0);
lean_ctor_set(x_3, 1, x_12);
lean_ctor_set(x_3, 0, x_13);
return x_3;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_14 = lean_ctor_get(x_3, 1);
lean_inc(x_14);
lean_dec(x_3);
x_15 = l_Nat_repr(x_1);
x_16 = l_Lean_IR_VarId_HasToString___closed__1;
x_17 = lean_string_append(x_16, x_15);
lean_dec(x_15);
x_18 = lean_string_append(x_14, x_17);
lean_dec(x_17);
x_19 = l_Nat_mforAux___main___at_Lean_IR_EmitC_emitJmp___spec__1___closed__1;
x_20 = lean_string_append(x_18, x_19);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
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
lean_object* l_Nat_mforAux___main___at_Lean_IR_EmitC_emitArgs___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_5);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_5, 0);
lean_dec(x_14);
x_15 = lean_box(0);
lean_ctor_set(x_5, 0, x_15);
x_16 = l_Lean_IR_Arg_Inhabited;
x_17 = lean_array_get(x_16, x_1, x_11);
lean_dec(x_11);
x_18 = l_Lean_IR_EmitC_emitArg(x_17, x_4, x_5);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_18, 0);
lean_dec(x_20);
lean_ctor_set(x_18, 0, x_15);
x_3 = x_9;
x_5 = x_18;
goto _start;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_18, 1);
lean_inc(x_22);
lean_dec(x_18);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_15);
lean_ctor_set(x_23, 1, x_22);
x_3 = x_9;
x_5 = x_23;
goto _start;
}
}
else
{
uint8_t x_25; 
lean_dec(x_9);
x_25 = !lean_is_exclusive(x_18);
if (x_25 == 0)
{
return x_18;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_18, 0);
x_27 = lean_ctor_get(x_18, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_18);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_29 = lean_ctor_get(x_5, 1);
lean_inc(x_29);
lean_dec(x_5);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
x_32 = l_Lean_IR_Arg_Inhabited;
x_33 = lean_array_get(x_32, x_1, x_11);
lean_dec(x_11);
x_34 = l_Lean_IR_EmitC_emitArg(x_33, x_4, x_31);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_36 = x_34;
} else {
 lean_dec_ref(x_34);
 x_36 = lean_box(0);
}
if (lean_is_scalar(x_36)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_36;
}
lean_ctor_set(x_37, 0, x_30);
lean_ctor_set(x_37, 1, x_35);
x_3 = x_9;
x_5 = x_37;
goto _start;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_9);
x_39 = lean_ctor_get(x_34, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_34, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_41 = x_34;
} else {
 lean_dec_ref(x_34);
 x_41 = lean_box(0);
}
if (lean_is_scalar(x_41)) {
 x_42 = lean_alloc_ctor(1, 2, 0);
} else {
 x_42 = x_41;
}
lean_ctor_set(x_42, 0, x_39);
lean_ctor_set(x_42, 1, x_40);
return x_42;
}
}
}
else
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_5);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_44 = lean_ctor_get(x_5, 1);
x_45 = lean_ctor_get(x_5, 0);
lean_dec(x_45);
x_46 = l_List_reprAux___main___rarg___closed__1;
x_47 = lean_string_append(x_44, x_46);
x_48 = lean_box(0);
lean_ctor_set(x_5, 1, x_47);
lean_ctor_set(x_5, 0, x_48);
x_49 = l_Lean_IR_Arg_Inhabited;
x_50 = lean_array_get(x_49, x_1, x_11);
lean_dec(x_11);
x_51 = l_Lean_IR_EmitC_emitArg(x_50, x_4, x_5);
if (lean_obj_tag(x_51) == 0)
{
uint8_t x_52; 
x_52 = !lean_is_exclusive(x_51);
if (x_52 == 0)
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_51, 0);
lean_dec(x_53);
lean_ctor_set(x_51, 0, x_48);
x_3 = x_9;
x_5 = x_51;
goto _start;
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_51, 1);
lean_inc(x_55);
lean_dec(x_51);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_48);
lean_ctor_set(x_56, 1, x_55);
x_3 = x_9;
x_5 = x_56;
goto _start;
}
}
else
{
uint8_t x_58; 
lean_dec(x_9);
x_58 = !lean_is_exclusive(x_51);
if (x_58 == 0)
{
return x_51;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_51, 0);
x_60 = lean_ctor_get(x_51, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_51);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_62 = lean_ctor_get(x_5, 1);
lean_inc(x_62);
lean_dec(x_5);
x_63 = l_List_reprAux___main___rarg___closed__1;
x_64 = lean_string_append(x_62, x_63);
x_65 = lean_box(0);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_64);
x_67 = l_Lean_IR_Arg_Inhabited;
x_68 = lean_array_get(x_67, x_1, x_11);
lean_dec(x_11);
x_69 = l_Lean_IR_EmitC_emitArg(x_68, x_4, x_66);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_71 = x_69;
} else {
 lean_dec_ref(x_69);
 x_71 = lean_box(0);
}
if (lean_is_scalar(x_71)) {
 x_72 = lean_alloc_ctor(0, 2, 0);
} else {
 x_72 = x_71;
}
lean_ctor_set(x_72, 0, x_65);
lean_ctor_set(x_72, 1, x_70);
x_3 = x_9;
x_5 = x_72;
goto _start;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_9);
x_74 = lean_ctor_get(x_69, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_69, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_76 = x_69;
} else {
 lean_dec_ref(x_69);
 x_76 = lean_box(0);
}
if (lean_is_scalar(x_76)) {
 x_77 = lean_alloc_ctor(1, 2, 0);
} else {
 x_77 = x_76;
}
lean_ctor_set(x_77, 0, x_74);
lean_ctor_set(x_77, 1, x_75);
return x_77;
}
}
}
}
else
{
uint8_t x_78; 
lean_dec(x_3);
x_78 = !lean_is_exclusive(x_5);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_ctor_get(x_5, 0);
lean_dec(x_79);
x_80 = lean_box(0);
lean_ctor_set(x_5, 0, x_80);
return x_5;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_5, 1);
lean_inc(x_81);
lean_dec(x_5);
x_82 = lean_box(0);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_81);
return x_83;
}
}
}
}
lean_object* l_Lean_IR_EmitC_emitArgs(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_array_get_size(x_1);
lean_inc(x_4);
x_5 = l_Nat_mforAux___main___at_Lean_IR_EmitC_emitArgs___spec__1(x_1, x_4, x_4, x_2, x_3);
lean_dec(x_4);
return x_5;
}
}
lean_object* l_Nat_mforAux___main___at_Lean_IR_EmitC_emitArgs___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Nat_mforAux___main___at_Lean_IR_EmitC_emitArgs___spec__1(x_1, x_2, x_3, x_4, x_5);
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
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_1, x_5);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = lean_nat_dec_eq(x_2, x_5);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_4);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_9 = lean_ctor_get(x_4, 1);
x_10 = lean_ctor_get(x_4, 0);
lean_dec(x_10);
x_11 = l_Lean_IR_EmitC_emitCtorScalarSize___closed__1;
x_12 = lean_string_append(x_9, x_11);
x_13 = l_Nat_repr(x_1);
x_14 = lean_string_append(x_12, x_13);
lean_dec(x_13);
x_15 = l_Lean_IR_EmitC_emitOffset___closed__2;
x_16 = lean_string_append(x_14, x_15);
x_17 = l_Nat_repr(x_2);
x_18 = lean_string_append(x_16, x_17);
lean_dec(x_17);
x_19 = lean_box(0);
lean_ctor_set(x_4, 1, x_18);
lean_ctor_set(x_4, 0, x_19);
return x_4;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_20 = lean_ctor_get(x_4, 1);
lean_inc(x_20);
lean_dec(x_4);
x_21 = l_Lean_IR_EmitC_emitCtorScalarSize___closed__1;
x_22 = lean_string_append(x_20, x_21);
x_23 = l_Nat_repr(x_1);
x_24 = lean_string_append(x_22, x_23);
lean_dec(x_23);
x_25 = l_Lean_IR_EmitC_emitOffset___closed__2;
x_26 = lean_string_append(x_24, x_25);
x_27 = l_Nat_repr(x_2);
x_28 = lean_string_append(x_26, x_27);
lean_dec(x_27);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
else
{
uint8_t x_31; 
lean_dec(x_2);
x_31 = !lean_is_exclusive(x_4);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_32 = lean_ctor_get(x_4, 1);
x_33 = lean_ctor_get(x_4, 0);
lean_dec(x_33);
x_34 = l_Lean_IR_EmitC_emitCtorScalarSize___closed__1;
x_35 = lean_string_append(x_32, x_34);
x_36 = l_Nat_repr(x_1);
x_37 = lean_string_append(x_35, x_36);
lean_dec(x_36);
x_38 = lean_box(0);
lean_ctor_set(x_4, 1, x_37);
lean_ctor_set(x_4, 0, x_38);
return x_4;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_39 = lean_ctor_get(x_4, 1);
lean_inc(x_39);
lean_dec(x_4);
x_40 = l_Lean_IR_EmitC_emitCtorScalarSize___closed__1;
x_41 = lean_string_append(x_39, x_40);
x_42 = l_Nat_repr(x_1);
x_43 = lean_string_append(x_41, x_42);
lean_dec(x_42);
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
return x_45;
}
}
}
else
{
uint8_t x_46; 
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_4);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_47 = lean_ctor_get(x_4, 1);
x_48 = lean_ctor_get(x_4, 0);
lean_dec(x_48);
x_49 = l_Nat_repr(x_2);
x_50 = lean_string_append(x_47, x_49);
lean_dec(x_49);
x_51 = lean_box(0);
lean_ctor_set(x_4, 1, x_50);
lean_ctor_set(x_4, 0, x_51);
return x_4;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_52 = lean_ctor_get(x_4, 1);
lean_inc(x_52);
lean_dec(x_4);
x_53 = l_Nat_repr(x_2);
x_54 = lean_string_append(x_52, x_53);
lean_dec(x_53);
x_55 = lean_box(0);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_54);
return x_56;
}
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
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_ctor_get(x_3, 0);
lean_dec(x_6);
x_7 = l_Lean_IR_EmitC_emitAllocCtor___closed__1;
x_8 = lean_string_append(x_5, x_7);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
x_10 = l_Nat_repr(x_9);
x_11 = lean_string_append(x_8, x_10);
lean_dec(x_10);
x_12 = l_List_reprAux___main___rarg___closed__1;
x_13 = lean_string_append(x_11, x_12);
x_14 = lean_ctor_get(x_1, 2);
lean_inc(x_14);
x_15 = l_Nat_repr(x_14);
x_16 = lean_string_append(x_13, x_15);
lean_dec(x_15);
x_17 = lean_string_append(x_16, x_12);
x_18 = lean_box(0);
lean_ctor_set(x_3, 1, x_17);
lean_ctor_set(x_3, 0, x_18);
x_19 = lean_ctor_get(x_1, 3);
lean_inc(x_19);
x_20 = lean_ctor_get(x_1, 4);
lean_inc(x_20);
lean_dec(x_1);
x_21 = l_Lean_IR_EmitC_emitCtorScalarSize(x_19, x_20, x_2, x_3);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_23 = lean_ctor_get(x_21, 1);
x_24 = lean_ctor_get(x_21, 0);
lean_dec(x_24);
x_25 = l_Lean_IR_EmitC_emitInc___closed__1;
x_26 = lean_string_append(x_23, x_25);
x_27 = l_IO_println___rarg___closed__1;
x_28 = lean_string_append(x_26, x_27);
lean_ctor_set(x_21, 1, x_28);
lean_ctor_set(x_21, 0, x_18);
return x_21;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_29 = lean_ctor_get(x_21, 1);
lean_inc(x_29);
lean_dec(x_21);
x_30 = l_Lean_IR_EmitC_emitInc___closed__1;
x_31 = lean_string_append(x_29, x_30);
x_32 = l_IO_println___rarg___closed__1;
x_33 = lean_string_append(x_31, x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_18);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
else
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_21);
if (x_35 == 0)
{
return x_21;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_21, 0);
x_37 = lean_ctor_get(x_21, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_21);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_39 = lean_ctor_get(x_3, 1);
lean_inc(x_39);
lean_dec(x_3);
x_40 = l_Lean_IR_EmitC_emitAllocCtor___closed__1;
x_41 = lean_string_append(x_39, x_40);
x_42 = lean_ctor_get(x_1, 1);
lean_inc(x_42);
x_43 = l_Nat_repr(x_42);
x_44 = lean_string_append(x_41, x_43);
lean_dec(x_43);
x_45 = l_List_reprAux___main___rarg___closed__1;
x_46 = lean_string_append(x_44, x_45);
x_47 = lean_ctor_get(x_1, 2);
lean_inc(x_47);
x_48 = l_Nat_repr(x_47);
x_49 = lean_string_append(x_46, x_48);
lean_dec(x_48);
x_50 = lean_string_append(x_49, x_45);
x_51 = lean_box(0);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_50);
x_53 = lean_ctor_get(x_1, 3);
lean_inc(x_53);
x_54 = lean_ctor_get(x_1, 4);
lean_inc(x_54);
lean_dec(x_1);
x_55 = l_Lean_IR_EmitC_emitCtorScalarSize(x_53, x_54, x_2, x_52);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_57 = x_55;
} else {
 lean_dec_ref(x_55);
 x_57 = lean_box(0);
}
x_58 = l_Lean_IR_EmitC_emitInc___closed__1;
x_59 = lean_string_append(x_56, x_58);
x_60 = l_IO_println___rarg___closed__1;
x_61 = lean_string_append(x_59, x_60);
if (lean_is_scalar(x_57)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_57;
}
lean_ctor_set(x_62, 0, x_51);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_63 = lean_ctor_get(x_55, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_55, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_65 = x_55;
} else {
 lean_dec_ref(x_55);
 x_65 = lean_box(0);
}
if (lean_is_scalar(x_65)) {
 x_66 = lean_alloc_ctor(1, 2, 0);
} else {
 x_66 = x_65;
}
lean_ctor_set(x_66, 0, x_63);
lean_ctor_set(x_66, 1, x_64);
return x_66;
}
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
lean_object* l_Nat_mforAux___main___at_Lean_IR_EmitC_emitCtorSetArgs___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_eq(x_4, x_7);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_6);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_10 = lean_ctor_get(x_6, 1);
x_11 = lean_ctor_get(x_6, 0);
lean_dec(x_11);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_sub(x_4, x_12);
lean_dec(x_4);
x_14 = lean_nat_sub(x_3, x_13);
x_15 = lean_nat_sub(x_14, x_12);
lean_dec(x_14);
x_16 = l_Lean_IR_EmitC_emitSet___closed__1;
x_17 = lean_string_append(x_10, x_16);
lean_inc(x_1);
x_18 = l_Nat_repr(x_1);
x_19 = l_Lean_IR_VarId_HasToString___closed__1;
x_20 = lean_string_append(x_19, x_18);
lean_dec(x_18);
x_21 = lean_string_append(x_17, x_20);
lean_dec(x_20);
x_22 = l_List_reprAux___main___rarg___closed__1;
x_23 = lean_string_append(x_21, x_22);
lean_inc(x_15);
x_24 = l_Nat_repr(x_15);
x_25 = lean_string_append(x_23, x_24);
lean_dec(x_24);
x_26 = lean_string_append(x_25, x_22);
x_27 = lean_box(0);
lean_ctor_set(x_6, 1, x_26);
lean_ctor_set(x_6, 0, x_27);
x_28 = l_Lean_IR_Arg_Inhabited;
x_29 = lean_array_get(x_28, x_2, x_15);
lean_dec(x_15);
x_30 = l_Lean_IR_EmitC_emitArg(x_29, x_5, x_6);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_32 = lean_ctor_get(x_30, 1);
x_33 = lean_ctor_get(x_30, 0);
lean_dec(x_33);
x_34 = l_Lean_IR_EmitC_emitInc___closed__1;
x_35 = lean_string_append(x_32, x_34);
x_36 = l_IO_println___rarg___closed__1;
x_37 = lean_string_append(x_35, x_36);
lean_ctor_set(x_30, 1, x_37);
lean_ctor_set(x_30, 0, x_27);
x_4 = x_13;
x_6 = x_30;
goto _start;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_39 = lean_ctor_get(x_30, 1);
lean_inc(x_39);
lean_dec(x_30);
x_40 = l_Lean_IR_EmitC_emitInc___closed__1;
x_41 = lean_string_append(x_39, x_40);
x_42 = l_IO_println___rarg___closed__1;
x_43 = lean_string_append(x_41, x_42);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_27);
lean_ctor_set(x_44, 1, x_43);
x_4 = x_13;
x_6 = x_44;
goto _start;
}
}
else
{
uint8_t x_46; 
lean_dec(x_13);
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_30);
if (x_46 == 0)
{
return x_30;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_30, 0);
x_48 = lean_ctor_get(x_30, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_30);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_50 = lean_ctor_get(x_6, 1);
lean_inc(x_50);
lean_dec(x_6);
x_51 = lean_unsigned_to_nat(1u);
x_52 = lean_nat_sub(x_4, x_51);
lean_dec(x_4);
x_53 = lean_nat_sub(x_3, x_52);
x_54 = lean_nat_sub(x_53, x_51);
lean_dec(x_53);
x_55 = l_Lean_IR_EmitC_emitSet___closed__1;
x_56 = lean_string_append(x_50, x_55);
lean_inc(x_1);
x_57 = l_Nat_repr(x_1);
x_58 = l_Lean_IR_VarId_HasToString___closed__1;
x_59 = lean_string_append(x_58, x_57);
lean_dec(x_57);
x_60 = lean_string_append(x_56, x_59);
lean_dec(x_59);
x_61 = l_List_reprAux___main___rarg___closed__1;
x_62 = lean_string_append(x_60, x_61);
lean_inc(x_54);
x_63 = l_Nat_repr(x_54);
x_64 = lean_string_append(x_62, x_63);
lean_dec(x_63);
x_65 = lean_string_append(x_64, x_61);
x_66 = lean_box(0);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_65);
x_68 = l_Lean_IR_Arg_Inhabited;
x_69 = lean_array_get(x_68, x_2, x_54);
lean_dec(x_54);
x_70 = l_Lean_IR_EmitC_emitArg(x_69, x_5, x_67);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_71 = lean_ctor_get(x_70, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_72 = x_70;
} else {
 lean_dec_ref(x_70);
 x_72 = lean_box(0);
}
x_73 = l_Lean_IR_EmitC_emitInc___closed__1;
x_74 = lean_string_append(x_71, x_73);
x_75 = l_IO_println___rarg___closed__1;
x_76 = lean_string_append(x_74, x_75);
if (lean_is_scalar(x_72)) {
 x_77 = lean_alloc_ctor(0, 2, 0);
} else {
 x_77 = x_72;
}
lean_ctor_set(x_77, 0, x_66);
lean_ctor_set(x_77, 1, x_76);
x_4 = x_52;
x_6 = x_77;
goto _start;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_52);
lean_dec(x_1);
x_79 = lean_ctor_get(x_70, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_70, 1);
lean_inc(x_80);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_81 = x_70;
} else {
 lean_dec_ref(x_70);
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
else
{
uint8_t x_83; 
lean_dec(x_4);
lean_dec(x_1);
x_83 = !lean_is_exclusive(x_6);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_6, 0);
lean_dec(x_84);
x_85 = lean_box(0);
lean_ctor_set(x_6, 0, x_85);
return x_6;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_6, 1);
lean_inc(x_86);
lean_dec(x_6);
x_87 = lean_box(0);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_86);
return x_88;
}
}
}
}
lean_object* l_Lean_IR_EmitC_emitCtorSetArgs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_array_get_size(x_2);
lean_inc(x_5);
x_6 = l_Nat_mforAux___main___at_Lean_IR_EmitC_emitCtorSetArgs___spec__1(x_1, x_2, x_5, x_5, x_3, x_4);
lean_dec(x_5);
return x_6;
}
}
lean_object* l_Nat_mforAux___main___at_Lean_IR_EmitC_emitCtorSetArgs___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Nat_mforAux___main___at_Lean_IR_EmitC_emitCtorSetArgs___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
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
lean_object* x_6; 
lean_inc(x_1);
x_6 = l_Lean_IR_EmitC_emitLhs(x_1, x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_8 = lean_ctor_get(x_6, 1);
x_9 = lean_ctor_get(x_6, 0);
lean_dec(x_9);
x_10 = lean_box(0);
lean_inc(x_8);
lean_ctor_set(x_6, 0, x_10);
x_11 = lean_ctor_get(x_2, 2);
lean_inc(x_11);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_nat_dec_eq(x_11, x_12);
lean_dec(x_11);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_8);
x_14 = l_Lean_IR_EmitC_emitAllocCtor(x_2, x_4, x_6);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 0);
lean_dec(x_16);
lean_ctor_set(x_14, 0, x_10);
x_17 = l_Lean_IR_EmitC_emitCtorSetArgs(x_1, x_3, x_4, x_14);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_14, 1);
lean_inc(x_18);
lean_dec(x_14);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_10);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_IR_EmitC_emitCtorSetArgs(x_1, x_3, x_4, x_19);
return x_20;
}
}
else
{
uint8_t x_21; 
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_14);
if (x_21 == 0)
{
return x_14;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_14, 0);
x_23 = lean_ctor_get(x_14, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_14);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
else
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_2, 3);
lean_inc(x_25);
x_26 = lean_nat_dec_eq(x_25, x_12);
lean_dec(x_25);
if (x_26 == 0)
{
lean_object* x_27; 
lean_dec(x_8);
x_27 = l_Lean_IR_EmitC_emitAllocCtor(x_2, x_4, x_6);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_27, 0);
lean_dec(x_29);
lean_ctor_set(x_27, 0, x_10);
x_30 = l_Lean_IR_EmitC_emitCtorSetArgs(x_1, x_3, x_4, x_27);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_27, 1);
lean_inc(x_31);
lean_dec(x_27);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_10);
lean_ctor_set(x_32, 1, x_31);
x_33 = l_Lean_IR_EmitC_emitCtorSetArgs(x_1, x_3, x_4, x_32);
return x_33;
}
}
else
{
uint8_t x_34; 
lean_dec(x_1);
x_34 = !lean_is_exclusive(x_27);
if (x_34 == 0)
{
return x_27;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_27, 0);
x_36 = lean_ctor_get(x_27, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_27);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_ctor_get(x_2, 4);
lean_inc(x_38);
x_39 = lean_nat_dec_eq(x_38, x_12);
lean_dec(x_38);
if (x_39 == 0)
{
lean_object* x_40; 
lean_dec(x_8);
x_40 = l_Lean_IR_EmitC_emitAllocCtor(x_2, x_4, x_6);
if (lean_obj_tag(x_40) == 0)
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_40, 0);
lean_dec(x_42);
lean_ctor_set(x_40, 0, x_10);
x_43 = l_Lean_IR_EmitC_emitCtorSetArgs(x_1, x_3, x_4, x_40);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_40, 1);
lean_inc(x_44);
lean_dec(x_40);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_10);
lean_ctor_set(x_45, 1, x_44);
x_46 = l_Lean_IR_EmitC_emitCtorSetArgs(x_1, x_3, x_4, x_45);
return x_46;
}
}
else
{
uint8_t x_47; 
lean_dec(x_1);
x_47 = !lean_is_exclusive(x_40);
if (x_47 == 0)
{
return x_40;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_40, 0);
x_49 = lean_ctor_get(x_40, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_40);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_6);
lean_dec(x_1);
x_51 = l_Lean_IR_EmitC_emitCtor___closed__1;
x_52 = lean_string_append(x_8, x_51);
x_53 = lean_ctor_get(x_2, 1);
lean_inc(x_53);
lean_dec(x_2);
x_54 = l_Nat_repr(x_53);
x_55 = lean_string_append(x_52, x_54);
lean_dec(x_54);
x_56 = l_Lean_IR_EmitC_emitInc___closed__1;
x_57 = lean_string_append(x_55, x_56);
x_58 = l_IO_println___rarg___closed__1;
x_59 = lean_string_append(x_57, x_58);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_10);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_61 = lean_ctor_get(x_6, 1);
lean_inc(x_61);
lean_dec(x_6);
x_62 = lean_box(0);
lean_inc(x_61);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_61);
x_64 = lean_ctor_get(x_2, 2);
lean_inc(x_64);
x_65 = lean_unsigned_to_nat(0u);
x_66 = lean_nat_dec_eq(x_64, x_65);
lean_dec(x_64);
if (x_66 == 0)
{
lean_object* x_67; 
lean_dec(x_61);
x_67 = l_Lean_IR_EmitC_emitAllocCtor(x_2, x_4, x_63);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_68 = lean_ctor_get(x_67, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_69 = x_67;
} else {
 lean_dec_ref(x_67);
 x_69 = lean_box(0);
}
if (lean_is_scalar(x_69)) {
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_69;
}
lean_ctor_set(x_70, 0, x_62);
lean_ctor_set(x_70, 1, x_68);
x_71 = l_Lean_IR_EmitC_emitCtorSetArgs(x_1, x_3, x_4, x_70);
return x_71;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_1);
x_72 = lean_ctor_get(x_67, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_67, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_74 = x_67;
} else {
 lean_dec_ref(x_67);
 x_74 = lean_box(0);
}
if (lean_is_scalar(x_74)) {
 x_75 = lean_alloc_ctor(1, 2, 0);
} else {
 x_75 = x_74;
}
lean_ctor_set(x_75, 0, x_72);
lean_ctor_set(x_75, 1, x_73);
return x_75;
}
}
else
{
lean_object* x_76; uint8_t x_77; 
x_76 = lean_ctor_get(x_2, 3);
lean_inc(x_76);
x_77 = lean_nat_dec_eq(x_76, x_65);
lean_dec(x_76);
if (x_77 == 0)
{
lean_object* x_78; 
lean_dec(x_61);
x_78 = l_Lean_IR_EmitC_emitAllocCtor(x_2, x_4, x_63);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_79 = lean_ctor_get(x_78, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 x_80 = x_78;
} else {
 lean_dec_ref(x_78);
 x_80 = lean_box(0);
}
if (lean_is_scalar(x_80)) {
 x_81 = lean_alloc_ctor(0, 2, 0);
} else {
 x_81 = x_80;
}
lean_ctor_set(x_81, 0, x_62);
lean_ctor_set(x_81, 1, x_79);
x_82 = l_Lean_IR_EmitC_emitCtorSetArgs(x_1, x_3, x_4, x_81);
return x_82;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_1);
x_83 = lean_ctor_get(x_78, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_78, 1);
lean_inc(x_84);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 x_85 = x_78;
} else {
 lean_dec_ref(x_78);
 x_85 = lean_box(0);
}
if (lean_is_scalar(x_85)) {
 x_86 = lean_alloc_ctor(1, 2, 0);
} else {
 x_86 = x_85;
}
lean_ctor_set(x_86, 0, x_83);
lean_ctor_set(x_86, 1, x_84);
return x_86;
}
}
else
{
lean_object* x_87; uint8_t x_88; 
x_87 = lean_ctor_get(x_2, 4);
lean_inc(x_87);
x_88 = lean_nat_dec_eq(x_87, x_65);
lean_dec(x_87);
if (x_88 == 0)
{
lean_object* x_89; 
lean_dec(x_61);
x_89 = l_Lean_IR_EmitC_emitAllocCtor(x_2, x_4, x_63);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_90 = lean_ctor_get(x_89, 1);
lean_inc(x_90);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 x_91 = x_89;
} else {
 lean_dec_ref(x_89);
 x_91 = lean_box(0);
}
if (lean_is_scalar(x_91)) {
 x_92 = lean_alloc_ctor(0, 2, 0);
} else {
 x_92 = x_91;
}
lean_ctor_set(x_92, 0, x_62);
lean_ctor_set(x_92, 1, x_90);
x_93 = l_Lean_IR_EmitC_emitCtorSetArgs(x_1, x_3, x_4, x_92);
return x_93;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_1);
x_94 = lean_ctor_get(x_89, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_89, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 x_96 = x_89;
} else {
 lean_dec_ref(x_89);
 x_96 = lean_box(0);
}
if (lean_is_scalar(x_96)) {
 x_97 = lean_alloc_ctor(1, 2, 0);
} else {
 x_97 = x_96;
}
lean_ctor_set(x_97, 0, x_94);
lean_ctor_set(x_97, 1, x_95);
return x_97;
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
lean_dec(x_63);
lean_dec(x_1);
x_98 = l_Lean_IR_EmitC_emitCtor___closed__1;
x_99 = lean_string_append(x_61, x_98);
x_100 = lean_ctor_get(x_2, 1);
lean_inc(x_100);
lean_dec(x_2);
x_101 = l_Nat_repr(x_100);
x_102 = lean_string_append(x_99, x_101);
lean_dec(x_101);
x_103 = l_Lean_IR_EmitC_emitInc___closed__1;
x_104 = lean_string_append(x_102, x_103);
x_105 = l_IO_println___rarg___closed__1;
x_106 = lean_string_append(x_104, x_105);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_62);
lean_ctor_set(x_107, 1, x_106);
return x_107;
}
}
}
}
}
else
{
uint8_t x_108; 
lean_dec(x_2);
lean_dec(x_1);
x_108 = !lean_is_exclusive(x_6);
if (x_108 == 0)
{
return x_6;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_6, 0);
x_110 = lean_ctor_get(x_6, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_6);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
return x_111;
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
lean_object* _init_l_Nat_mforAux___main___at_Lean_IR_EmitC_emitReset___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" lean_ctor_release(");
return x_1;
}
}
lean_object* l_Nat_mforAux___main___at_Lean_IR_EmitC_emitReset___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_3, x_6);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_9 = lean_ctor_get(x_5, 1);
x_10 = lean_ctor_get(x_5, 0);
lean_dec(x_10);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_sub(x_3, x_11);
lean_dec(x_3);
x_13 = lean_nat_sub(x_2, x_12);
x_14 = lean_nat_sub(x_13, x_11);
lean_dec(x_13);
x_15 = l_Nat_mforAux___main___at_Lean_IR_EmitC_emitReset___spec__1___closed__1;
x_16 = lean_string_append(x_9, x_15);
x_17 = lean_string_append(x_16, x_1);
x_18 = l_List_reprAux___main___rarg___closed__1;
x_19 = lean_string_append(x_17, x_18);
x_20 = l_Nat_repr(x_14);
x_21 = lean_string_append(x_19, x_20);
lean_dec(x_20);
x_22 = l_Lean_IR_EmitC_emitInc___closed__1;
x_23 = lean_string_append(x_21, x_22);
x_24 = l_IO_println___rarg___closed__1;
x_25 = lean_string_append(x_23, x_24);
x_26 = lean_box(0);
lean_ctor_set(x_5, 1, x_25);
lean_ctor_set(x_5, 0, x_26);
x_3 = x_12;
goto _start;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_28 = lean_ctor_get(x_5, 1);
lean_inc(x_28);
lean_dec(x_5);
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_sub(x_3, x_29);
lean_dec(x_3);
x_31 = lean_nat_sub(x_2, x_30);
x_32 = lean_nat_sub(x_31, x_29);
lean_dec(x_31);
x_33 = l_Nat_mforAux___main___at_Lean_IR_EmitC_emitReset___spec__1___closed__1;
x_34 = lean_string_append(x_28, x_33);
x_35 = lean_string_append(x_34, x_1);
x_36 = l_List_reprAux___main___rarg___closed__1;
x_37 = lean_string_append(x_35, x_36);
x_38 = l_Nat_repr(x_32);
x_39 = lean_string_append(x_37, x_38);
lean_dec(x_38);
x_40 = l_Lean_IR_EmitC_emitInc___closed__1;
x_41 = lean_string_append(x_39, x_40);
x_42 = l_IO_println___rarg___closed__1;
x_43 = lean_string_append(x_41, x_42);
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
x_3 = x_30;
x_5 = x_45;
goto _start;
}
}
else
{
uint8_t x_47; 
lean_dec(x_3);
x_47 = !lean_is_exclusive(x_5);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_5, 0);
lean_dec(x_48);
x_49 = lean_box(0);
lean_ctor_set(x_5, 0, x_49);
return x_5;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_5, 1);
lean_inc(x_50);
lean_dec(x_5);
x_51 = lean_box(0);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_50);
return x_52;
}
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
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_7 = lean_ctor_get(x_5, 1);
x_8 = lean_ctor_get(x_5, 0);
lean_dec(x_8);
x_9 = l_Lean_IR_EmitC_emitReset___closed__1;
x_10 = lean_string_append(x_7, x_9);
x_11 = l_Nat_repr(x_3);
x_12 = l_Lean_IR_VarId_HasToString___closed__1;
x_13 = lean_string_append(x_12, x_11);
lean_dec(x_11);
x_14 = lean_string_append(x_10, x_13);
x_15 = l_Lean_IR_EmitC_emitReset___closed__2;
x_16 = lean_string_append(x_14, x_15);
x_17 = l_IO_println___rarg___closed__1;
x_18 = lean_string_append(x_16, x_17);
x_19 = lean_box(0);
lean_ctor_set(x_5, 1, x_18);
lean_ctor_set(x_5, 0, x_19);
lean_inc(x_2);
x_20 = l_Nat_mforAux___main___at_Lean_IR_EmitC_emitReset___spec__1(x_13, x_2, x_2, x_4, x_5);
lean_dec(x_2);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_20, 1);
x_23 = lean_ctor_get(x_20, 0);
lean_dec(x_23);
x_24 = l_Lean_Format_flatten___main___closed__1;
x_25 = lean_string_append(x_22, x_24);
lean_ctor_set(x_20, 1, x_25);
lean_ctor_set(x_20, 0, x_19);
lean_inc(x_1);
x_26 = l_Lean_IR_EmitC_emitLhs(x_1, x_4, x_20);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_28 = lean_ctor_get(x_26, 1);
x_29 = lean_ctor_get(x_26, 0);
lean_dec(x_29);
x_30 = lean_string_append(x_28, x_13);
x_31 = l_Lean_IR_formatFnBody___main___closed__3;
x_32 = lean_string_append(x_30, x_31);
x_33 = lean_string_append(x_32, x_17);
x_34 = l_Lean_IR_EmitC_emitMainFn___closed__21;
x_35 = lean_string_append(x_33, x_34);
x_36 = lean_string_append(x_35, x_17);
x_37 = l_Lean_IR_EmitC_emitReset___closed__3;
x_38 = lean_string_append(x_36, x_37);
x_39 = lean_string_append(x_38, x_13);
lean_dec(x_13);
x_40 = l_Lean_IR_EmitC_emitInc___closed__1;
x_41 = lean_string_append(x_39, x_40);
x_42 = lean_string_append(x_41, x_17);
x_43 = lean_string_append(x_42, x_24);
lean_ctor_set(x_26, 1, x_43);
lean_ctor_set(x_26, 0, x_19);
x_44 = l_Lean_IR_EmitC_emitLhs(x_1, x_4, x_26);
if (lean_obj_tag(x_44) == 0)
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_46 = lean_ctor_get(x_44, 1);
x_47 = lean_ctor_get(x_44, 0);
lean_dec(x_47);
x_48 = l_Lean_IR_EmitC_emitReset___closed__4;
x_49 = lean_string_append(x_46, x_48);
x_50 = lean_string_append(x_49, x_17);
x_51 = l_PersistentHashMap_Stats_toString___closed__5;
x_52 = lean_string_append(x_50, x_51);
x_53 = lean_string_append(x_52, x_17);
lean_ctor_set(x_44, 1, x_53);
lean_ctor_set(x_44, 0, x_19);
return x_44;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_54 = lean_ctor_get(x_44, 1);
lean_inc(x_54);
lean_dec(x_44);
x_55 = l_Lean_IR_EmitC_emitReset___closed__4;
x_56 = lean_string_append(x_54, x_55);
x_57 = lean_string_append(x_56, x_17);
x_58 = l_PersistentHashMap_Stats_toString___closed__5;
x_59 = lean_string_append(x_57, x_58);
x_60 = lean_string_append(x_59, x_17);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_19);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
else
{
uint8_t x_62; 
x_62 = !lean_is_exclusive(x_44);
if (x_62 == 0)
{
return x_44;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_44, 0);
x_64 = lean_ctor_get(x_44, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_44);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_66 = lean_ctor_get(x_26, 1);
lean_inc(x_66);
lean_dec(x_26);
x_67 = lean_string_append(x_66, x_13);
x_68 = l_Lean_IR_formatFnBody___main___closed__3;
x_69 = lean_string_append(x_67, x_68);
x_70 = lean_string_append(x_69, x_17);
x_71 = l_Lean_IR_EmitC_emitMainFn___closed__21;
x_72 = lean_string_append(x_70, x_71);
x_73 = lean_string_append(x_72, x_17);
x_74 = l_Lean_IR_EmitC_emitReset___closed__3;
x_75 = lean_string_append(x_73, x_74);
x_76 = lean_string_append(x_75, x_13);
lean_dec(x_13);
x_77 = l_Lean_IR_EmitC_emitInc___closed__1;
x_78 = lean_string_append(x_76, x_77);
x_79 = lean_string_append(x_78, x_17);
x_80 = lean_string_append(x_79, x_24);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_19);
lean_ctor_set(x_81, 1, x_80);
x_82 = l_Lean_IR_EmitC_emitLhs(x_1, x_4, x_81);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_83 = lean_ctor_get(x_82, 1);
lean_inc(x_83);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_84 = x_82;
} else {
 lean_dec_ref(x_82);
 x_84 = lean_box(0);
}
x_85 = l_Lean_IR_EmitC_emitReset___closed__4;
x_86 = lean_string_append(x_83, x_85);
x_87 = lean_string_append(x_86, x_17);
x_88 = l_PersistentHashMap_Stats_toString___closed__5;
x_89 = lean_string_append(x_87, x_88);
x_90 = lean_string_append(x_89, x_17);
if (lean_is_scalar(x_84)) {
 x_91 = lean_alloc_ctor(0, 2, 0);
} else {
 x_91 = x_84;
}
lean_ctor_set(x_91, 0, x_19);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_92 = lean_ctor_get(x_82, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_82, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_94 = x_82;
} else {
 lean_dec_ref(x_82);
 x_94 = lean_box(0);
}
if (lean_is_scalar(x_94)) {
 x_95 = lean_alloc_ctor(1, 2, 0);
} else {
 x_95 = x_94;
}
lean_ctor_set(x_95, 0, x_92);
lean_ctor_set(x_95, 1, x_93);
return x_95;
}
}
}
else
{
uint8_t x_96; 
lean_dec(x_13);
lean_dec(x_1);
x_96 = !lean_is_exclusive(x_26);
if (x_96 == 0)
{
return x_26;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_26, 0);
x_98 = lean_ctor_get(x_26, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_26);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_100 = lean_ctor_get(x_20, 1);
lean_inc(x_100);
lean_dec(x_20);
x_101 = l_Lean_Format_flatten___main___closed__1;
x_102 = lean_string_append(x_100, x_101);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_19);
lean_ctor_set(x_103, 1, x_102);
lean_inc(x_1);
x_104 = l_Lean_IR_EmitC_emitLhs(x_1, x_4, x_103);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_105 = lean_ctor_get(x_104, 1);
lean_inc(x_105);
if (lean_is_exclusive(x_104)) {
 lean_ctor_release(x_104, 0);
 lean_ctor_release(x_104, 1);
 x_106 = x_104;
} else {
 lean_dec_ref(x_104);
 x_106 = lean_box(0);
}
x_107 = lean_string_append(x_105, x_13);
x_108 = l_Lean_IR_formatFnBody___main___closed__3;
x_109 = lean_string_append(x_107, x_108);
x_110 = lean_string_append(x_109, x_17);
x_111 = l_Lean_IR_EmitC_emitMainFn___closed__21;
x_112 = lean_string_append(x_110, x_111);
x_113 = lean_string_append(x_112, x_17);
x_114 = l_Lean_IR_EmitC_emitReset___closed__3;
x_115 = lean_string_append(x_113, x_114);
x_116 = lean_string_append(x_115, x_13);
lean_dec(x_13);
x_117 = l_Lean_IR_EmitC_emitInc___closed__1;
x_118 = lean_string_append(x_116, x_117);
x_119 = lean_string_append(x_118, x_17);
x_120 = lean_string_append(x_119, x_101);
if (lean_is_scalar(x_106)) {
 x_121 = lean_alloc_ctor(0, 2, 0);
} else {
 x_121 = x_106;
}
lean_ctor_set(x_121, 0, x_19);
lean_ctor_set(x_121, 1, x_120);
x_122 = l_Lean_IR_EmitC_emitLhs(x_1, x_4, x_121);
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_123 = lean_ctor_get(x_122, 1);
lean_inc(x_123);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 lean_ctor_release(x_122, 1);
 x_124 = x_122;
} else {
 lean_dec_ref(x_122);
 x_124 = lean_box(0);
}
x_125 = l_Lean_IR_EmitC_emitReset___closed__4;
x_126 = lean_string_append(x_123, x_125);
x_127 = lean_string_append(x_126, x_17);
x_128 = l_PersistentHashMap_Stats_toString___closed__5;
x_129 = lean_string_append(x_127, x_128);
x_130 = lean_string_append(x_129, x_17);
if (lean_is_scalar(x_124)) {
 x_131 = lean_alloc_ctor(0, 2, 0);
} else {
 x_131 = x_124;
}
lean_ctor_set(x_131, 0, x_19);
lean_ctor_set(x_131, 1, x_130);
return x_131;
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_132 = lean_ctor_get(x_122, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_122, 1);
lean_inc(x_133);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 lean_ctor_release(x_122, 1);
 x_134 = x_122;
} else {
 lean_dec_ref(x_122);
 x_134 = lean_box(0);
}
if (lean_is_scalar(x_134)) {
 x_135 = lean_alloc_ctor(1, 2, 0);
} else {
 x_135 = x_134;
}
lean_ctor_set(x_135, 0, x_132);
lean_ctor_set(x_135, 1, x_133);
return x_135;
}
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
lean_dec(x_13);
lean_dec(x_1);
x_136 = lean_ctor_get(x_104, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_104, 1);
lean_inc(x_137);
if (lean_is_exclusive(x_104)) {
 lean_ctor_release(x_104, 0);
 lean_ctor_release(x_104, 1);
 x_138 = x_104;
} else {
 lean_dec_ref(x_104);
 x_138 = lean_box(0);
}
if (lean_is_scalar(x_138)) {
 x_139 = lean_alloc_ctor(1, 2, 0);
} else {
 x_139 = x_138;
}
lean_ctor_set(x_139, 0, x_136);
lean_ctor_set(x_139, 1, x_137);
return x_139;
}
}
}
else
{
uint8_t x_140; 
lean_dec(x_13);
lean_dec(x_1);
x_140 = !lean_is_exclusive(x_20);
if (x_140 == 0)
{
return x_20;
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_141 = lean_ctor_get(x_20, 0);
x_142 = lean_ctor_get(x_20, 1);
lean_inc(x_142);
lean_inc(x_141);
lean_dec(x_20);
x_143 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_143, 0, x_141);
lean_ctor_set(x_143, 1, x_142);
return x_143;
}
}
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_144 = lean_ctor_get(x_5, 1);
lean_inc(x_144);
lean_dec(x_5);
x_145 = l_Lean_IR_EmitC_emitReset___closed__1;
x_146 = lean_string_append(x_144, x_145);
x_147 = l_Nat_repr(x_3);
x_148 = l_Lean_IR_VarId_HasToString___closed__1;
x_149 = lean_string_append(x_148, x_147);
lean_dec(x_147);
x_150 = lean_string_append(x_146, x_149);
x_151 = l_Lean_IR_EmitC_emitReset___closed__2;
x_152 = lean_string_append(x_150, x_151);
x_153 = l_IO_println___rarg___closed__1;
x_154 = lean_string_append(x_152, x_153);
x_155 = lean_box(0);
x_156 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_156, 0, x_155);
lean_ctor_set(x_156, 1, x_154);
lean_inc(x_2);
x_157 = l_Nat_mforAux___main___at_Lean_IR_EmitC_emitReset___spec__1(x_149, x_2, x_2, x_4, x_156);
lean_dec(x_2);
if (lean_obj_tag(x_157) == 0)
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_158 = lean_ctor_get(x_157, 1);
lean_inc(x_158);
if (lean_is_exclusive(x_157)) {
 lean_ctor_release(x_157, 0);
 lean_ctor_release(x_157, 1);
 x_159 = x_157;
} else {
 lean_dec_ref(x_157);
 x_159 = lean_box(0);
}
x_160 = l_Lean_Format_flatten___main___closed__1;
x_161 = lean_string_append(x_158, x_160);
if (lean_is_scalar(x_159)) {
 x_162 = lean_alloc_ctor(0, 2, 0);
} else {
 x_162 = x_159;
}
lean_ctor_set(x_162, 0, x_155);
lean_ctor_set(x_162, 1, x_161);
lean_inc(x_1);
x_163 = l_Lean_IR_EmitC_emitLhs(x_1, x_4, x_162);
if (lean_obj_tag(x_163) == 0)
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_164 = lean_ctor_get(x_163, 1);
lean_inc(x_164);
if (lean_is_exclusive(x_163)) {
 lean_ctor_release(x_163, 0);
 lean_ctor_release(x_163, 1);
 x_165 = x_163;
} else {
 lean_dec_ref(x_163);
 x_165 = lean_box(0);
}
x_166 = lean_string_append(x_164, x_149);
x_167 = l_Lean_IR_formatFnBody___main___closed__3;
x_168 = lean_string_append(x_166, x_167);
x_169 = lean_string_append(x_168, x_153);
x_170 = l_Lean_IR_EmitC_emitMainFn___closed__21;
x_171 = lean_string_append(x_169, x_170);
x_172 = lean_string_append(x_171, x_153);
x_173 = l_Lean_IR_EmitC_emitReset___closed__3;
x_174 = lean_string_append(x_172, x_173);
x_175 = lean_string_append(x_174, x_149);
lean_dec(x_149);
x_176 = l_Lean_IR_EmitC_emitInc___closed__1;
x_177 = lean_string_append(x_175, x_176);
x_178 = lean_string_append(x_177, x_153);
x_179 = lean_string_append(x_178, x_160);
if (lean_is_scalar(x_165)) {
 x_180 = lean_alloc_ctor(0, 2, 0);
} else {
 x_180 = x_165;
}
lean_ctor_set(x_180, 0, x_155);
lean_ctor_set(x_180, 1, x_179);
x_181 = l_Lean_IR_EmitC_emitLhs(x_1, x_4, x_180);
if (lean_obj_tag(x_181) == 0)
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_182 = lean_ctor_get(x_181, 1);
lean_inc(x_182);
if (lean_is_exclusive(x_181)) {
 lean_ctor_release(x_181, 0);
 lean_ctor_release(x_181, 1);
 x_183 = x_181;
} else {
 lean_dec_ref(x_181);
 x_183 = lean_box(0);
}
x_184 = l_Lean_IR_EmitC_emitReset___closed__4;
x_185 = lean_string_append(x_182, x_184);
x_186 = lean_string_append(x_185, x_153);
x_187 = l_PersistentHashMap_Stats_toString___closed__5;
x_188 = lean_string_append(x_186, x_187);
x_189 = lean_string_append(x_188, x_153);
if (lean_is_scalar(x_183)) {
 x_190 = lean_alloc_ctor(0, 2, 0);
} else {
 x_190 = x_183;
}
lean_ctor_set(x_190, 0, x_155);
lean_ctor_set(x_190, 1, x_189);
return x_190;
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_191 = lean_ctor_get(x_181, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_181, 1);
lean_inc(x_192);
if (lean_is_exclusive(x_181)) {
 lean_ctor_release(x_181, 0);
 lean_ctor_release(x_181, 1);
 x_193 = x_181;
} else {
 lean_dec_ref(x_181);
 x_193 = lean_box(0);
}
if (lean_is_scalar(x_193)) {
 x_194 = lean_alloc_ctor(1, 2, 0);
} else {
 x_194 = x_193;
}
lean_ctor_set(x_194, 0, x_191);
lean_ctor_set(x_194, 1, x_192);
return x_194;
}
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; 
lean_dec(x_149);
lean_dec(x_1);
x_195 = lean_ctor_get(x_163, 0);
lean_inc(x_195);
x_196 = lean_ctor_get(x_163, 1);
lean_inc(x_196);
if (lean_is_exclusive(x_163)) {
 lean_ctor_release(x_163, 0);
 lean_ctor_release(x_163, 1);
 x_197 = x_163;
} else {
 lean_dec_ref(x_163);
 x_197 = lean_box(0);
}
if (lean_is_scalar(x_197)) {
 x_198 = lean_alloc_ctor(1, 2, 0);
} else {
 x_198 = x_197;
}
lean_ctor_set(x_198, 0, x_195);
lean_ctor_set(x_198, 1, x_196);
return x_198;
}
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; 
lean_dec(x_149);
lean_dec(x_1);
x_199 = lean_ctor_get(x_157, 0);
lean_inc(x_199);
x_200 = lean_ctor_get(x_157, 1);
lean_inc(x_200);
if (lean_is_exclusive(x_157)) {
 lean_ctor_release(x_157, 0);
 lean_ctor_release(x_157, 1);
 x_201 = x_157;
} else {
 lean_dec_ref(x_157);
 x_201 = lean_box(0);
}
if (lean_is_scalar(x_201)) {
 x_202 = lean_alloc_ctor(1, 2, 0);
} else {
 x_202 = x_201;
}
lean_ctor_set(x_202, 0, x_199);
lean_ctor_set(x_202, 1, x_200);
return x_202;
}
}
}
}
lean_object* l_Nat_mforAux___main___at_Lean_IR_EmitC_emitReset___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Nat_mforAux___main___at_Lean_IR_EmitC_emitReset___spec__1(x_1, x_2, x_3, x_4, x_5);
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
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_9 = lean_ctor_get(x_7, 1);
x_10 = lean_ctor_get(x_7, 0);
lean_dec(x_10);
x_11 = l_Lean_IR_EmitC_emitReuse___closed__1;
x_12 = lean_string_append(x_9, x_11);
x_13 = l_Nat_repr(x_2);
x_14 = l_Lean_IR_VarId_HasToString___closed__1;
x_15 = lean_string_append(x_14, x_13);
lean_dec(x_13);
x_16 = lean_string_append(x_12, x_15);
x_17 = l_Lean_IR_EmitC_emitReset___closed__2;
x_18 = lean_string_append(x_16, x_17);
x_19 = l_IO_println___rarg___closed__1;
x_20 = lean_string_append(x_18, x_19);
x_21 = l_Lean_Format_flatten___main___closed__1;
x_22 = lean_string_append(x_20, x_21);
x_23 = lean_box(0);
lean_ctor_set(x_7, 1, x_22);
lean_ctor_set(x_7, 0, x_23);
lean_inc(x_1);
x_24 = l_Lean_IR_EmitC_emitLhs(x_1, x_6, x_7);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_24, 0);
lean_dec(x_26);
lean_ctor_set(x_24, 0, x_23);
lean_inc(x_3);
x_27 = l_Lean_IR_EmitC_emitAllocCtor(x_3, x_6, x_24);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_29 = lean_ctor_get(x_27, 1);
x_30 = lean_ctor_get(x_27, 0);
lean_dec(x_30);
x_31 = l_Lean_IR_EmitC_emitMainFn___closed__21;
x_32 = lean_string_append(x_29, x_31);
x_33 = lean_string_append(x_32, x_19);
x_34 = lean_string_append(x_33, x_21);
lean_ctor_set(x_27, 1, x_34);
lean_ctor_set(x_27, 0, x_23);
lean_inc(x_1);
x_35 = l_Lean_IR_EmitC_emitLhs(x_1, x_6, x_27);
if (lean_obj_tag(x_35) == 0)
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_37 = lean_ctor_get(x_35, 1);
x_38 = lean_ctor_get(x_35, 0);
lean_dec(x_38);
x_39 = lean_string_append(x_37, x_15);
lean_dec(x_15);
x_40 = l_Lean_IR_formatFnBody___main___closed__3;
x_41 = lean_string_append(x_39, x_40);
x_42 = lean_string_append(x_41, x_19);
if (x_4 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_3);
x_43 = l_PersistentHashMap_Stats_toString___closed__5;
x_44 = lean_string_append(x_42, x_43);
x_45 = lean_string_append(x_44, x_19);
lean_ctor_set(x_35, 1, x_45);
lean_ctor_set(x_35, 0, x_23);
x_46 = l_Lean_IR_EmitC_emitCtorSetArgs(x_1, x_5, x_6, x_35);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_47 = l_Lean_IR_EmitC_emitReuse___closed__2;
x_48 = lean_string_append(x_42, x_47);
lean_inc(x_1);
x_49 = l_Nat_repr(x_1);
x_50 = lean_string_append(x_14, x_49);
lean_dec(x_49);
x_51 = lean_string_append(x_48, x_50);
lean_dec(x_50);
x_52 = l_List_reprAux___main___rarg___closed__1;
x_53 = lean_string_append(x_51, x_52);
x_54 = lean_ctor_get(x_3, 1);
lean_inc(x_54);
lean_dec(x_3);
x_55 = l_Nat_repr(x_54);
x_56 = lean_string_append(x_53, x_55);
lean_dec(x_55);
x_57 = l_Lean_IR_EmitC_emitInc___closed__1;
x_58 = lean_string_append(x_56, x_57);
x_59 = lean_string_append(x_58, x_19);
x_60 = l_PersistentHashMap_Stats_toString___closed__5;
x_61 = lean_string_append(x_59, x_60);
x_62 = lean_string_append(x_61, x_19);
lean_ctor_set(x_35, 1, x_62);
lean_ctor_set(x_35, 0, x_23);
x_63 = l_Lean_IR_EmitC_emitCtorSetArgs(x_1, x_5, x_6, x_35);
return x_63;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_64 = lean_ctor_get(x_35, 1);
lean_inc(x_64);
lean_dec(x_35);
x_65 = lean_string_append(x_64, x_15);
lean_dec(x_15);
x_66 = l_Lean_IR_formatFnBody___main___closed__3;
x_67 = lean_string_append(x_65, x_66);
x_68 = lean_string_append(x_67, x_19);
if (x_4 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_3);
x_69 = l_PersistentHashMap_Stats_toString___closed__5;
x_70 = lean_string_append(x_68, x_69);
x_71 = lean_string_append(x_70, x_19);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_23);
lean_ctor_set(x_72, 1, x_71);
x_73 = l_Lean_IR_EmitC_emitCtorSetArgs(x_1, x_5, x_6, x_72);
return x_73;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_74 = l_Lean_IR_EmitC_emitReuse___closed__2;
x_75 = lean_string_append(x_68, x_74);
lean_inc(x_1);
x_76 = l_Nat_repr(x_1);
x_77 = lean_string_append(x_14, x_76);
lean_dec(x_76);
x_78 = lean_string_append(x_75, x_77);
lean_dec(x_77);
x_79 = l_List_reprAux___main___rarg___closed__1;
x_80 = lean_string_append(x_78, x_79);
x_81 = lean_ctor_get(x_3, 1);
lean_inc(x_81);
lean_dec(x_3);
x_82 = l_Nat_repr(x_81);
x_83 = lean_string_append(x_80, x_82);
lean_dec(x_82);
x_84 = l_Lean_IR_EmitC_emitInc___closed__1;
x_85 = lean_string_append(x_83, x_84);
x_86 = lean_string_append(x_85, x_19);
x_87 = l_PersistentHashMap_Stats_toString___closed__5;
x_88 = lean_string_append(x_86, x_87);
x_89 = lean_string_append(x_88, x_19);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_23);
lean_ctor_set(x_90, 1, x_89);
x_91 = l_Lean_IR_EmitC_emitCtorSetArgs(x_1, x_5, x_6, x_90);
return x_91;
}
}
}
else
{
uint8_t x_92; 
lean_dec(x_15);
lean_dec(x_3);
lean_dec(x_1);
x_92 = !lean_is_exclusive(x_35);
if (x_92 == 0)
{
return x_35;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_35, 0);
x_94 = lean_ctor_get(x_35, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_35);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_96 = lean_ctor_get(x_27, 1);
lean_inc(x_96);
lean_dec(x_27);
x_97 = l_Lean_IR_EmitC_emitMainFn___closed__21;
x_98 = lean_string_append(x_96, x_97);
x_99 = lean_string_append(x_98, x_19);
x_100 = lean_string_append(x_99, x_21);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_23);
lean_ctor_set(x_101, 1, x_100);
lean_inc(x_1);
x_102 = l_Lean_IR_EmitC_emitLhs(x_1, x_6, x_101);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_103 = lean_ctor_get(x_102, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 lean_ctor_release(x_102, 1);
 x_104 = x_102;
} else {
 lean_dec_ref(x_102);
 x_104 = lean_box(0);
}
x_105 = lean_string_append(x_103, x_15);
lean_dec(x_15);
x_106 = l_Lean_IR_formatFnBody___main___closed__3;
x_107 = lean_string_append(x_105, x_106);
x_108 = lean_string_append(x_107, x_19);
if (x_4 == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
lean_dec(x_3);
x_109 = l_PersistentHashMap_Stats_toString___closed__5;
x_110 = lean_string_append(x_108, x_109);
x_111 = lean_string_append(x_110, x_19);
if (lean_is_scalar(x_104)) {
 x_112 = lean_alloc_ctor(0, 2, 0);
} else {
 x_112 = x_104;
}
lean_ctor_set(x_112, 0, x_23);
lean_ctor_set(x_112, 1, x_111);
x_113 = l_Lean_IR_EmitC_emitCtorSetArgs(x_1, x_5, x_6, x_112);
return x_113;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_114 = l_Lean_IR_EmitC_emitReuse___closed__2;
x_115 = lean_string_append(x_108, x_114);
lean_inc(x_1);
x_116 = l_Nat_repr(x_1);
x_117 = lean_string_append(x_14, x_116);
lean_dec(x_116);
x_118 = lean_string_append(x_115, x_117);
lean_dec(x_117);
x_119 = l_List_reprAux___main___rarg___closed__1;
x_120 = lean_string_append(x_118, x_119);
x_121 = lean_ctor_get(x_3, 1);
lean_inc(x_121);
lean_dec(x_3);
x_122 = l_Nat_repr(x_121);
x_123 = lean_string_append(x_120, x_122);
lean_dec(x_122);
x_124 = l_Lean_IR_EmitC_emitInc___closed__1;
x_125 = lean_string_append(x_123, x_124);
x_126 = lean_string_append(x_125, x_19);
x_127 = l_PersistentHashMap_Stats_toString___closed__5;
x_128 = lean_string_append(x_126, x_127);
x_129 = lean_string_append(x_128, x_19);
if (lean_is_scalar(x_104)) {
 x_130 = lean_alloc_ctor(0, 2, 0);
} else {
 x_130 = x_104;
}
lean_ctor_set(x_130, 0, x_23);
lean_ctor_set(x_130, 1, x_129);
x_131 = l_Lean_IR_EmitC_emitCtorSetArgs(x_1, x_5, x_6, x_130);
return x_131;
}
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
lean_dec(x_15);
lean_dec(x_3);
lean_dec(x_1);
x_132 = lean_ctor_get(x_102, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_102, 1);
lean_inc(x_133);
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 lean_ctor_release(x_102, 1);
 x_134 = x_102;
} else {
 lean_dec_ref(x_102);
 x_134 = lean_box(0);
}
if (lean_is_scalar(x_134)) {
 x_135 = lean_alloc_ctor(1, 2, 0);
} else {
 x_135 = x_134;
}
lean_ctor_set(x_135, 0, x_132);
lean_ctor_set(x_135, 1, x_133);
return x_135;
}
}
}
else
{
uint8_t x_136; 
lean_dec(x_15);
lean_dec(x_3);
lean_dec(x_1);
x_136 = !lean_is_exclusive(x_27);
if (x_136 == 0)
{
return x_27;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_137 = lean_ctor_get(x_27, 0);
x_138 = lean_ctor_get(x_27, 1);
lean_inc(x_138);
lean_inc(x_137);
lean_dec(x_27);
x_139 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_139, 0, x_137);
lean_ctor_set(x_139, 1, x_138);
return x_139;
}
}
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_140 = lean_ctor_get(x_24, 1);
lean_inc(x_140);
lean_dec(x_24);
x_141 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_141, 0, x_23);
lean_ctor_set(x_141, 1, x_140);
lean_inc(x_3);
x_142 = l_Lean_IR_EmitC_emitAllocCtor(x_3, x_6, x_141);
if (lean_obj_tag(x_142) == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
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
x_145 = l_Lean_IR_EmitC_emitMainFn___closed__21;
x_146 = lean_string_append(x_143, x_145);
x_147 = lean_string_append(x_146, x_19);
x_148 = lean_string_append(x_147, x_21);
if (lean_is_scalar(x_144)) {
 x_149 = lean_alloc_ctor(0, 2, 0);
} else {
 x_149 = x_144;
}
lean_ctor_set(x_149, 0, x_23);
lean_ctor_set(x_149, 1, x_148);
lean_inc(x_1);
x_150 = l_Lean_IR_EmitC_emitLhs(x_1, x_6, x_149);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_151 = lean_ctor_get(x_150, 1);
lean_inc(x_151);
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 lean_ctor_release(x_150, 1);
 x_152 = x_150;
} else {
 lean_dec_ref(x_150);
 x_152 = lean_box(0);
}
x_153 = lean_string_append(x_151, x_15);
lean_dec(x_15);
x_154 = l_Lean_IR_formatFnBody___main___closed__3;
x_155 = lean_string_append(x_153, x_154);
x_156 = lean_string_append(x_155, x_19);
if (x_4 == 0)
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
lean_dec(x_3);
x_157 = l_PersistentHashMap_Stats_toString___closed__5;
x_158 = lean_string_append(x_156, x_157);
x_159 = lean_string_append(x_158, x_19);
if (lean_is_scalar(x_152)) {
 x_160 = lean_alloc_ctor(0, 2, 0);
} else {
 x_160 = x_152;
}
lean_ctor_set(x_160, 0, x_23);
lean_ctor_set(x_160, 1, x_159);
x_161 = l_Lean_IR_EmitC_emitCtorSetArgs(x_1, x_5, x_6, x_160);
return x_161;
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_162 = l_Lean_IR_EmitC_emitReuse___closed__2;
x_163 = lean_string_append(x_156, x_162);
lean_inc(x_1);
x_164 = l_Nat_repr(x_1);
x_165 = lean_string_append(x_14, x_164);
lean_dec(x_164);
x_166 = lean_string_append(x_163, x_165);
lean_dec(x_165);
x_167 = l_List_reprAux___main___rarg___closed__1;
x_168 = lean_string_append(x_166, x_167);
x_169 = lean_ctor_get(x_3, 1);
lean_inc(x_169);
lean_dec(x_3);
x_170 = l_Nat_repr(x_169);
x_171 = lean_string_append(x_168, x_170);
lean_dec(x_170);
x_172 = l_Lean_IR_EmitC_emitInc___closed__1;
x_173 = lean_string_append(x_171, x_172);
x_174 = lean_string_append(x_173, x_19);
x_175 = l_PersistentHashMap_Stats_toString___closed__5;
x_176 = lean_string_append(x_174, x_175);
x_177 = lean_string_append(x_176, x_19);
if (lean_is_scalar(x_152)) {
 x_178 = lean_alloc_ctor(0, 2, 0);
} else {
 x_178 = x_152;
}
lean_ctor_set(x_178, 0, x_23);
lean_ctor_set(x_178, 1, x_177);
x_179 = l_Lean_IR_EmitC_emitCtorSetArgs(x_1, x_5, x_6, x_178);
return x_179;
}
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
lean_dec(x_15);
lean_dec(x_3);
lean_dec(x_1);
x_180 = lean_ctor_get(x_150, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_150, 1);
lean_inc(x_181);
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 lean_ctor_release(x_150, 1);
 x_182 = x_150;
} else {
 lean_dec_ref(x_150);
 x_182 = lean_box(0);
}
if (lean_is_scalar(x_182)) {
 x_183 = lean_alloc_ctor(1, 2, 0);
} else {
 x_183 = x_182;
}
lean_ctor_set(x_183, 0, x_180);
lean_ctor_set(x_183, 1, x_181);
return x_183;
}
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
lean_dec(x_15);
lean_dec(x_3);
lean_dec(x_1);
x_184 = lean_ctor_get(x_142, 0);
lean_inc(x_184);
x_185 = lean_ctor_get(x_142, 1);
lean_inc(x_185);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 lean_ctor_release(x_142, 1);
 x_186 = x_142;
} else {
 lean_dec_ref(x_142);
 x_186 = lean_box(0);
}
if (lean_is_scalar(x_186)) {
 x_187 = lean_alloc_ctor(1, 2, 0);
} else {
 x_187 = x_186;
}
lean_ctor_set(x_187, 0, x_184);
lean_ctor_set(x_187, 1, x_185);
return x_187;
}
}
}
else
{
uint8_t x_188; 
lean_dec(x_15);
lean_dec(x_3);
lean_dec(x_1);
x_188 = !lean_is_exclusive(x_24);
if (x_188 == 0)
{
return x_24;
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_189 = lean_ctor_get(x_24, 0);
x_190 = lean_ctor_get(x_24, 1);
lean_inc(x_190);
lean_inc(x_189);
lean_dec(x_24);
x_191 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_191, 0, x_189);
lean_ctor_set(x_191, 1, x_190);
return x_191;
}
}
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_192 = lean_ctor_get(x_7, 1);
lean_inc(x_192);
lean_dec(x_7);
x_193 = l_Lean_IR_EmitC_emitReuse___closed__1;
x_194 = lean_string_append(x_192, x_193);
x_195 = l_Nat_repr(x_2);
x_196 = l_Lean_IR_VarId_HasToString___closed__1;
x_197 = lean_string_append(x_196, x_195);
lean_dec(x_195);
x_198 = lean_string_append(x_194, x_197);
x_199 = l_Lean_IR_EmitC_emitReset___closed__2;
x_200 = lean_string_append(x_198, x_199);
x_201 = l_IO_println___rarg___closed__1;
x_202 = lean_string_append(x_200, x_201);
x_203 = l_Lean_Format_flatten___main___closed__1;
x_204 = lean_string_append(x_202, x_203);
x_205 = lean_box(0);
x_206 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_206, 0, x_205);
lean_ctor_set(x_206, 1, x_204);
lean_inc(x_1);
x_207 = l_Lean_IR_EmitC_emitLhs(x_1, x_6, x_206);
if (lean_obj_tag(x_207) == 0)
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; 
x_208 = lean_ctor_get(x_207, 1);
lean_inc(x_208);
if (lean_is_exclusive(x_207)) {
 lean_ctor_release(x_207, 0);
 lean_ctor_release(x_207, 1);
 x_209 = x_207;
} else {
 lean_dec_ref(x_207);
 x_209 = lean_box(0);
}
if (lean_is_scalar(x_209)) {
 x_210 = lean_alloc_ctor(0, 2, 0);
} else {
 x_210 = x_209;
}
lean_ctor_set(x_210, 0, x_205);
lean_ctor_set(x_210, 1, x_208);
lean_inc(x_3);
x_211 = l_Lean_IR_EmitC_emitAllocCtor(x_3, x_6, x_210);
if (lean_obj_tag(x_211) == 0)
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; 
x_212 = lean_ctor_get(x_211, 1);
lean_inc(x_212);
if (lean_is_exclusive(x_211)) {
 lean_ctor_release(x_211, 0);
 lean_ctor_release(x_211, 1);
 x_213 = x_211;
} else {
 lean_dec_ref(x_211);
 x_213 = lean_box(0);
}
x_214 = l_Lean_IR_EmitC_emitMainFn___closed__21;
x_215 = lean_string_append(x_212, x_214);
x_216 = lean_string_append(x_215, x_201);
x_217 = lean_string_append(x_216, x_203);
if (lean_is_scalar(x_213)) {
 x_218 = lean_alloc_ctor(0, 2, 0);
} else {
 x_218 = x_213;
}
lean_ctor_set(x_218, 0, x_205);
lean_ctor_set(x_218, 1, x_217);
lean_inc(x_1);
x_219 = l_Lean_IR_EmitC_emitLhs(x_1, x_6, x_218);
if (lean_obj_tag(x_219) == 0)
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; 
x_220 = lean_ctor_get(x_219, 1);
lean_inc(x_220);
if (lean_is_exclusive(x_219)) {
 lean_ctor_release(x_219, 0);
 lean_ctor_release(x_219, 1);
 x_221 = x_219;
} else {
 lean_dec_ref(x_219);
 x_221 = lean_box(0);
}
x_222 = lean_string_append(x_220, x_197);
lean_dec(x_197);
x_223 = l_Lean_IR_formatFnBody___main___closed__3;
x_224 = lean_string_append(x_222, x_223);
x_225 = lean_string_append(x_224, x_201);
if (x_4 == 0)
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; 
lean_dec(x_3);
x_226 = l_PersistentHashMap_Stats_toString___closed__5;
x_227 = lean_string_append(x_225, x_226);
x_228 = lean_string_append(x_227, x_201);
if (lean_is_scalar(x_221)) {
 x_229 = lean_alloc_ctor(0, 2, 0);
} else {
 x_229 = x_221;
}
lean_ctor_set(x_229, 0, x_205);
lean_ctor_set(x_229, 1, x_228);
x_230 = l_Lean_IR_EmitC_emitCtorSetArgs(x_1, x_5, x_6, x_229);
return x_230;
}
else
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; 
x_231 = l_Lean_IR_EmitC_emitReuse___closed__2;
x_232 = lean_string_append(x_225, x_231);
lean_inc(x_1);
x_233 = l_Nat_repr(x_1);
x_234 = lean_string_append(x_196, x_233);
lean_dec(x_233);
x_235 = lean_string_append(x_232, x_234);
lean_dec(x_234);
x_236 = l_List_reprAux___main___rarg___closed__1;
x_237 = lean_string_append(x_235, x_236);
x_238 = lean_ctor_get(x_3, 1);
lean_inc(x_238);
lean_dec(x_3);
x_239 = l_Nat_repr(x_238);
x_240 = lean_string_append(x_237, x_239);
lean_dec(x_239);
x_241 = l_Lean_IR_EmitC_emitInc___closed__1;
x_242 = lean_string_append(x_240, x_241);
x_243 = lean_string_append(x_242, x_201);
x_244 = l_PersistentHashMap_Stats_toString___closed__5;
x_245 = lean_string_append(x_243, x_244);
x_246 = lean_string_append(x_245, x_201);
if (lean_is_scalar(x_221)) {
 x_247 = lean_alloc_ctor(0, 2, 0);
} else {
 x_247 = x_221;
}
lean_ctor_set(x_247, 0, x_205);
lean_ctor_set(x_247, 1, x_246);
x_248 = l_Lean_IR_EmitC_emitCtorSetArgs(x_1, x_5, x_6, x_247);
return x_248;
}
}
else
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; 
lean_dec(x_197);
lean_dec(x_3);
lean_dec(x_1);
x_249 = lean_ctor_get(x_219, 0);
lean_inc(x_249);
x_250 = lean_ctor_get(x_219, 1);
lean_inc(x_250);
if (lean_is_exclusive(x_219)) {
 lean_ctor_release(x_219, 0);
 lean_ctor_release(x_219, 1);
 x_251 = x_219;
} else {
 lean_dec_ref(x_219);
 x_251 = lean_box(0);
}
if (lean_is_scalar(x_251)) {
 x_252 = lean_alloc_ctor(1, 2, 0);
} else {
 x_252 = x_251;
}
lean_ctor_set(x_252, 0, x_249);
lean_ctor_set(x_252, 1, x_250);
return x_252;
}
}
else
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; 
lean_dec(x_197);
lean_dec(x_3);
lean_dec(x_1);
x_253 = lean_ctor_get(x_211, 0);
lean_inc(x_253);
x_254 = lean_ctor_get(x_211, 1);
lean_inc(x_254);
if (lean_is_exclusive(x_211)) {
 lean_ctor_release(x_211, 0);
 lean_ctor_release(x_211, 1);
 x_255 = x_211;
} else {
 lean_dec_ref(x_211);
 x_255 = lean_box(0);
}
if (lean_is_scalar(x_255)) {
 x_256 = lean_alloc_ctor(1, 2, 0);
} else {
 x_256 = x_255;
}
lean_ctor_set(x_256, 0, x_253);
lean_ctor_set(x_256, 1, x_254);
return x_256;
}
}
else
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; 
lean_dec(x_197);
lean_dec(x_3);
lean_dec(x_1);
x_257 = lean_ctor_get(x_207, 0);
lean_inc(x_257);
x_258 = lean_ctor_get(x_207, 1);
lean_inc(x_258);
if (lean_is_exclusive(x_207)) {
 lean_ctor_release(x_207, 0);
 lean_ctor_release(x_207, 1);
 x_259 = x_207;
} else {
 lean_dec_ref(x_207);
 x_259 = lean_box(0);
}
if (lean_is_scalar(x_259)) {
 x_260 = lean_alloc_ctor(1, 2, 0);
} else {
 x_260 = x_259;
}
lean_ctor_set(x_260, 0, x_257);
lean_ctor_set(x_260, 1, x_258);
return x_260;
}
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
lean_object* x_6; 
x_6 = l_Lean_IR_EmitC_emitLhs(x_1, x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
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
else
{
uint8_t x_42; 
lean_dec(x_3);
lean_dec(x_2);
x_42 = !lean_is_exclusive(x_6);
if (x_42 == 0)
{
return x_6;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_6, 0);
x_44 = lean_ctor_get(x_6, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_6);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
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
lean_object* x_6; 
x_6 = l_Lean_IR_EmitC_emitLhs(x_1, x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
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
else
{
uint8_t x_42; 
lean_dec(x_3);
lean_dec(x_2);
x_42 = !lean_is_exclusive(x_6);
if (x_42 == 0)
{
return x_6;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_6, 0);
x_44 = lean_ctor_get(x_6, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_6);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
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
lean_object* l_Lean_IR_EmitC_emitSProj(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_38; 
x_38 = l_Lean_IR_EmitC_emitLhs(x_1, x_6, x_7);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; 
x_39 = lean_box(x_2);
switch (lean_obj_tag(x_39)) {
case 0:
{
uint8_t x_40; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_40 = !lean_is_exclusive(x_38);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_38, 0);
lean_dec(x_41);
x_42 = l_Lean_IR_EmitC_emitSSet___closed__2;
lean_ctor_set_tag(x_38, 1);
lean_ctor_set(x_38, 0, x_42);
return x_38;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_38, 1);
lean_inc(x_43);
lean_dec(x_38);
x_44 = l_Lean_IR_EmitC_emitSSet___closed__2;
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
return x_45;
}
}
case 1:
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_38, 1);
lean_inc(x_46);
lean_dec(x_38);
x_47 = l_Lean_IR_EmitC_emitSProj___closed__1;
x_48 = lean_string_append(x_46, x_47);
x_8 = x_48;
goto block_37;
}
case 2:
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_38, 1);
lean_inc(x_49);
lean_dec(x_38);
x_50 = l_Lean_IR_EmitC_emitSProj___closed__2;
x_51 = lean_string_append(x_49, x_50);
x_8 = x_51;
goto block_37;
}
case 3:
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_38, 1);
lean_inc(x_52);
lean_dec(x_38);
x_53 = l_Lean_IR_EmitC_emitSProj___closed__3;
x_54 = lean_string_append(x_52, x_53);
x_8 = x_54;
goto block_37;
}
case 4:
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_38, 1);
lean_inc(x_55);
lean_dec(x_38);
x_56 = l_Lean_IR_EmitC_emitSProj___closed__4;
x_57 = lean_string_append(x_55, x_56);
x_8 = x_57;
goto block_37;
}
default: 
{
uint8_t x_58; 
lean_dec(x_39);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_58 = !lean_is_exclusive(x_38);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_38, 0);
lean_dec(x_59);
x_60 = l_Lean_IR_EmitC_emitSSet___closed__1;
lean_ctor_set_tag(x_38, 1);
lean_ctor_set(x_38, 0, x_60);
return x_38;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_38, 1);
lean_inc(x_61);
lean_dec(x_38);
x_62 = l_Lean_IR_EmitC_emitSSet___closed__1;
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_61);
return x_63;
}
}
}
}
else
{
uint8_t x_64; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_64 = !lean_is_exclusive(x_38);
if (x_64 == 0)
{
return x_38;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_38, 0);
x_66 = lean_ctor_get(x_38, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_38);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
block_37:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
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
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = l_Lean_IR_EmitC_emitOffset(x_3, x_4, x_6, x_18);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_21 = lean_ctor_get(x_19, 1);
x_22 = lean_ctor_get(x_19, 0);
lean_dec(x_22);
x_23 = l_Lean_IR_EmitC_emitInc___closed__1;
x_24 = lean_string_append(x_21, x_23);
x_25 = l_IO_println___rarg___closed__1;
x_26 = lean_string_append(x_24, x_25);
lean_ctor_set(x_19, 1, x_26);
lean_ctor_set(x_19, 0, x_17);
return x_19;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_27 = lean_ctor_get(x_19, 1);
lean_inc(x_27);
lean_dec(x_19);
x_28 = l_Lean_IR_EmitC_emitInc___closed__1;
x_29 = lean_string_append(x_27, x_28);
x_30 = l_IO_println___rarg___closed__1;
x_31 = lean_string_append(x_29, x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_17);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
else
{
uint8_t x_33; 
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
}
}
lean_object* l_Lean_IR_EmitC_emitSProj___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = l_Lean_IR_EmitC_emitSProj(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
return x_9;
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
lean_object* _init_l_Lean_IR_EmitC_emitFullApp___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("failed to emit extern application '");
return x_1;
}
}
lean_object* l_Lean_IR_EmitC_emitFullApp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_EmitC_emitLhs(x_1, x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_6, 0);
lean_dec(x_8);
x_9 = lean_box(0);
lean_ctor_set(x_6, 0, x_9);
lean_inc(x_2);
x_10 = l_Lean_IR_EmitC_getDecl(x_2, x_4, x_6);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
lean_dec(x_11);
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_10, 0);
lean_dec(x_13);
lean_ctor_set(x_10, 0, x_9);
x_14 = l_Lean_IR_EmitC_emitCName(x_2, x_4, x_10);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_16 = lean_ctor_get(x_14, 1);
x_17 = lean_ctor_get(x_14, 0);
lean_dec(x_17);
x_18 = lean_array_get_size(x_3);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_nat_dec_lt(x_19, x_18);
lean_dec(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = l_Lean_IR_formatFnBody___main___closed__3;
x_22 = lean_string_append(x_16, x_21);
x_23 = l_IO_println___rarg___closed__1;
x_24 = lean_string_append(x_22, x_23);
lean_ctor_set(x_14, 1, x_24);
lean_ctor_set(x_14, 0, x_9);
return x_14;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = l_Prod_HasRepr___rarg___closed__1;
x_26 = lean_string_append(x_16, x_25);
lean_ctor_set(x_14, 1, x_26);
lean_ctor_set(x_14, 0, x_9);
x_27 = l_Lean_IR_EmitC_emitArgs(x_3, x_4, x_14);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_29 = lean_ctor_get(x_27, 1);
x_30 = lean_ctor_get(x_27, 0);
lean_dec(x_30);
x_31 = l_Option_HasRepr___rarg___closed__3;
x_32 = lean_string_append(x_29, x_31);
x_33 = l_Lean_IR_formatFnBody___main___closed__3;
x_34 = lean_string_append(x_32, x_33);
x_35 = l_IO_println___rarg___closed__1;
x_36 = lean_string_append(x_34, x_35);
lean_ctor_set(x_27, 1, x_36);
lean_ctor_set(x_27, 0, x_9);
return x_27;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_37 = lean_ctor_get(x_27, 1);
lean_inc(x_37);
lean_dec(x_27);
x_38 = l_Option_HasRepr___rarg___closed__3;
x_39 = lean_string_append(x_37, x_38);
x_40 = l_Lean_IR_formatFnBody___main___closed__3;
x_41 = lean_string_append(x_39, x_40);
x_42 = l_IO_println___rarg___closed__1;
x_43 = lean_string_append(x_41, x_42);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_9);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
else
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_27);
if (x_45 == 0)
{
return x_27;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_27, 0);
x_47 = lean_ctor_get(x_27, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_27);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_49 = lean_ctor_get(x_14, 1);
lean_inc(x_49);
lean_dec(x_14);
x_50 = lean_array_get_size(x_3);
x_51 = lean_unsigned_to_nat(0u);
x_52 = lean_nat_dec_lt(x_51, x_50);
lean_dec(x_50);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_53 = l_Lean_IR_formatFnBody___main___closed__3;
x_54 = lean_string_append(x_49, x_53);
x_55 = l_IO_println___rarg___closed__1;
x_56 = lean_string_append(x_54, x_55);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_9);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_58 = l_Prod_HasRepr___rarg___closed__1;
x_59 = lean_string_append(x_49, x_58);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_9);
lean_ctor_set(x_60, 1, x_59);
x_61 = l_Lean_IR_EmitC_emitArgs(x_3, x_4, x_60);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_62 = lean_ctor_get(x_61, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_63 = x_61;
} else {
 lean_dec_ref(x_61);
 x_63 = lean_box(0);
}
x_64 = l_Option_HasRepr___rarg___closed__3;
x_65 = lean_string_append(x_62, x_64);
x_66 = l_Lean_IR_formatFnBody___main___closed__3;
x_67 = lean_string_append(x_65, x_66);
x_68 = l_IO_println___rarg___closed__1;
x_69 = lean_string_append(x_67, x_68);
if (lean_is_scalar(x_63)) {
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_63;
}
lean_ctor_set(x_70, 0, x_9);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_71 = lean_ctor_get(x_61, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_61, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_73 = x_61;
} else {
 lean_dec_ref(x_61);
 x_73 = lean_box(0);
}
if (lean_is_scalar(x_73)) {
 x_74 = lean_alloc_ctor(1, 2, 0);
} else {
 x_74 = x_73;
}
lean_ctor_set(x_74, 0, x_71);
lean_ctor_set(x_74, 1, x_72);
return x_74;
}
}
}
}
else
{
uint8_t x_75; 
x_75 = !lean_is_exclusive(x_14);
if (x_75 == 0)
{
return x_14;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_14, 0);
x_77 = lean_ctor_get(x_14, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_14);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_10, 1);
lean_inc(x_79);
lean_dec(x_10);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_9);
lean_ctor_set(x_80, 1, x_79);
x_81 = l_Lean_IR_EmitC_emitCName(x_2, x_4, x_80);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_82 = lean_ctor_get(x_81, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_83 = x_81;
} else {
 lean_dec_ref(x_81);
 x_83 = lean_box(0);
}
x_84 = lean_array_get_size(x_3);
x_85 = lean_unsigned_to_nat(0u);
x_86 = lean_nat_dec_lt(x_85, x_84);
lean_dec(x_84);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_87 = l_Lean_IR_formatFnBody___main___closed__3;
x_88 = lean_string_append(x_82, x_87);
x_89 = l_IO_println___rarg___closed__1;
x_90 = lean_string_append(x_88, x_89);
if (lean_is_scalar(x_83)) {
 x_91 = lean_alloc_ctor(0, 2, 0);
} else {
 x_91 = x_83;
}
lean_ctor_set(x_91, 0, x_9);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_92 = l_Prod_HasRepr___rarg___closed__1;
x_93 = lean_string_append(x_82, x_92);
if (lean_is_scalar(x_83)) {
 x_94 = lean_alloc_ctor(0, 2, 0);
} else {
 x_94 = x_83;
}
lean_ctor_set(x_94, 0, x_9);
lean_ctor_set(x_94, 1, x_93);
x_95 = l_Lean_IR_EmitC_emitArgs(x_3, x_4, x_94);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_96 = lean_ctor_get(x_95, 1);
lean_inc(x_96);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 x_97 = x_95;
} else {
 lean_dec_ref(x_95);
 x_97 = lean_box(0);
}
x_98 = l_Option_HasRepr___rarg___closed__3;
x_99 = lean_string_append(x_96, x_98);
x_100 = l_Lean_IR_formatFnBody___main___closed__3;
x_101 = lean_string_append(x_99, x_100);
x_102 = l_IO_println___rarg___closed__1;
x_103 = lean_string_append(x_101, x_102);
if (lean_is_scalar(x_97)) {
 x_104 = lean_alloc_ctor(0, 2, 0);
} else {
 x_104 = x_97;
}
lean_ctor_set(x_104, 0, x_9);
lean_ctor_set(x_104, 1, x_103);
return x_104;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_105 = lean_ctor_get(x_95, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_95, 1);
lean_inc(x_106);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 x_107 = x_95;
} else {
 lean_dec_ref(x_95);
 x_107 = lean_box(0);
}
if (lean_is_scalar(x_107)) {
 x_108 = lean_alloc_ctor(1, 2, 0);
} else {
 x_108 = x_107;
}
lean_ctor_set(x_108, 0, x_105);
lean_ctor_set(x_108, 1, x_106);
return x_108;
}
}
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_109 = lean_ctor_get(x_81, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_81, 1);
lean_inc(x_110);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_111 = x_81;
} else {
 lean_dec_ref(x_81);
 x_111 = lean_box(0);
}
if (lean_is_scalar(x_111)) {
 x_112 = lean_alloc_ctor(1, 2, 0);
} else {
 x_112 = x_111;
}
lean_ctor_set(x_112, 0, x_109);
lean_ctor_set(x_112, 1, x_110);
return x_112;
}
}
}
else
{
uint8_t x_113; 
x_113 = !lean_is_exclusive(x_10);
if (x_113 == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_114 = lean_ctor_get(x_10, 1);
x_115 = lean_ctor_get(x_10, 0);
lean_dec(x_115);
x_116 = lean_ctor_get(x_11, 2);
lean_inc(x_116);
lean_dec(x_11);
x_117 = l_Lean_IR_EmitC_toStringArgs(x_3);
x_118 = l_List_mfor___main___at_Lean_IR_EmitC_emitFnDecls___spec__5___closed__2;
x_119 = l_Lean_mkExternCall(x_116, x_118, x_117);
lean_dec(x_116);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_120 = l_System_FilePath_dirName___closed__1;
x_121 = l_Lean_Name_toStringWithSep___main(x_120, x_2);
x_122 = l_Lean_IR_EmitC_emitFullApp___closed__1;
x_123 = lean_string_append(x_122, x_121);
lean_dec(x_121);
x_124 = l_Char_HasRepr___closed__1;
x_125 = lean_string_append(x_123, x_124);
lean_ctor_set_tag(x_10, 1);
lean_ctor_set(x_10, 0, x_125);
return x_10;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
lean_dec(x_2);
x_126 = lean_ctor_get(x_119, 0);
lean_inc(x_126);
lean_dec(x_119);
x_127 = lean_string_append(x_114, x_126);
lean_dec(x_126);
x_128 = l_Lean_IR_formatFnBody___main___closed__3;
x_129 = lean_string_append(x_127, x_128);
x_130 = l_IO_println___rarg___closed__1;
x_131 = lean_string_append(x_129, x_130);
lean_ctor_set(x_10, 1, x_131);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_132 = lean_ctor_get(x_10, 1);
lean_inc(x_132);
lean_dec(x_10);
x_133 = lean_ctor_get(x_11, 2);
lean_inc(x_133);
lean_dec(x_11);
x_134 = l_Lean_IR_EmitC_toStringArgs(x_3);
x_135 = l_List_mfor___main___at_Lean_IR_EmitC_emitFnDecls___spec__5___closed__2;
x_136 = l_Lean_mkExternCall(x_133, x_135, x_134);
lean_dec(x_133);
if (lean_obj_tag(x_136) == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_137 = l_System_FilePath_dirName___closed__1;
x_138 = l_Lean_Name_toStringWithSep___main(x_137, x_2);
x_139 = l_Lean_IR_EmitC_emitFullApp___closed__1;
x_140 = lean_string_append(x_139, x_138);
lean_dec(x_138);
x_141 = l_Char_HasRepr___closed__1;
x_142 = lean_string_append(x_140, x_141);
x_143 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_143, 0, x_142);
lean_ctor_set(x_143, 1, x_132);
return x_143;
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
lean_dec(x_2);
x_144 = lean_ctor_get(x_136, 0);
lean_inc(x_144);
lean_dec(x_136);
x_145 = lean_string_append(x_132, x_144);
lean_dec(x_144);
x_146 = l_Lean_IR_formatFnBody___main___closed__3;
x_147 = lean_string_append(x_145, x_146);
x_148 = l_IO_println___rarg___closed__1;
x_149 = lean_string_append(x_147, x_148);
x_150 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_150, 0, x_9);
lean_ctor_set(x_150, 1, x_149);
return x_150;
}
}
}
}
else
{
uint8_t x_151; 
lean_dec(x_2);
x_151 = !lean_is_exclusive(x_10);
if (x_151 == 0)
{
return x_10;
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_152 = lean_ctor_get(x_10, 0);
x_153 = lean_ctor_get(x_10, 1);
lean_inc(x_153);
lean_inc(x_152);
lean_dec(x_10);
x_154 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_154, 0, x_152);
lean_ctor_set(x_154, 1, x_153);
return x_154;
}
}
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_155 = lean_ctor_get(x_6, 1);
lean_inc(x_155);
lean_dec(x_6);
x_156 = lean_box(0);
x_157 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_155);
lean_inc(x_2);
x_158 = l_Lean_IR_EmitC_getDecl(x_2, x_4, x_157);
if (lean_obj_tag(x_158) == 0)
{
lean_object* x_159; 
x_159 = lean_ctor_get(x_158, 0);
lean_inc(x_159);
if (lean_obj_tag(x_159) == 0)
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
lean_dec(x_159);
x_160 = lean_ctor_get(x_158, 1);
lean_inc(x_160);
if (lean_is_exclusive(x_158)) {
 lean_ctor_release(x_158, 0);
 lean_ctor_release(x_158, 1);
 x_161 = x_158;
} else {
 lean_dec_ref(x_158);
 x_161 = lean_box(0);
}
if (lean_is_scalar(x_161)) {
 x_162 = lean_alloc_ctor(0, 2, 0);
} else {
 x_162 = x_161;
}
lean_ctor_set(x_162, 0, x_156);
lean_ctor_set(x_162, 1, x_160);
x_163 = l_Lean_IR_EmitC_emitCName(x_2, x_4, x_162);
if (lean_obj_tag(x_163) == 0)
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; uint8_t x_168; 
x_164 = lean_ctor_get(x_163, 1);
lean_inc(x_164);
if (lean_is_exclusive(x_163)) {
 lean_ctor_release(x_163, 0);
 lean_ctor_release(x_163, 1);
 x_165 = x_163;
} else {
 lean_dec_ref(x_163);
 x_165 = lean_box(0);
}
x_166 = lean_array_get_size(x_3);
x_167 = lean_unsigned_to_nat(0u);
x_168 = lean_nat_dec_lt(x_167, x_166);
lean_dec(x_166);
if (x_168 == 0)
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_169 = l_Lean_IR_formatFnBody___main___closed__3;
x_170 = lean_string_append(x_164, x_169);
x_171 = l_IO_println___rarg___closed__1;
x_172 = lean_string_append(x_170, x_171);
if (lean_is_scalar(x_165)) {
 x_173 = lean_alloc_ctor(0, 2, 0);
} else {
 x_173 = x_165;
}
lean_ctor_set(x_173, 0, x_156);
lean_ctor_set(x_173, 1, x_172);
return x_173;
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_174 = l_Prod_HasRepr___rarg___closed__1;
x_175 = lean_string_append(x_164, x_174);
if (lean_is_scalar(x_165)) {
 x_176 = lean_alloc_ctor(0, 2, 0);
} else {
 x_176 = x_165;
}
lean_ctor_set(x_176, 0, x_156);
lean_ctor_set(x_176, 1, x_175);
x_177 = l_Lean_IR_EmitC_emitArgs(x_3, x_4, x_176);
if (lean_obj_tag(x_177) == 0)
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_178 = lean_ctor_get(x_177, 1);
lean_inc(x_178);
if (lean_is_exclusive(x_177)) {
 lean_ctor_release(x_177, 0);
 lean_ctor_release(x_177, 1);
 x_179 = x_177;
} else {
 lean_dec_ref(x_177);
 x_179 = lean_box(0);
}
x_180 = l_Option_HasRepr___rarg___closed__3;
x_181 = lean_string_append(x_178, x_180);
x_182 = l_Lean_IR_formatFnBody___main___closed__3;
x_183 = lean_string_append(x_181, x_182);
x_184 = l_IO_println___rarg___closed__1;
x_185 = lean_string_append(x_183, x_184);
if (lean_is_scalar(x_179)) {
 x_186 = lean_alloc_ctor(0, 2, 0);
} else {
 x_186 = x_179;
}
lean_ctor_set(x_186, 0, x_156);
lean_ctor_set(x_186, 1, x_185);
return x_186;
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_187 = lean_ctor_get(x_177, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_177, 1);
lean_inc(x_188);
if (lean_is_exclusive(x_177)) {
 lean_ctor_release(x_177, 0);
 lean_ctor_release(x_177, 1);
 x_189 = x_177;
} else {
 lean_dec_ref(x_177);
 x_189 = lean_box(0);
}
if (lean_is_scalar(x_189)) {
 x_190 = lean_alloc_ctor(1, 2, 0);
} else {
 x_190 = x_189;
}
lean_ctor_set(x_190, 0, x_187);
lean_ctor_set(x_190, 1, x_188);
return x_190;
}
}
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_191 = lean_ctor_get(x_163, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_163, 1);
lean_inc(x_192);
if (lean_is_exclusive(x_163)) {
 lean_ctor_release(x_163, 0);
 lean_ctor_release(x_163, 1);
 x_193 = x_163;
} else {
 lean_dec_ref(x_163);
 x_193 = lean_box(0);
}
if (lean_is_scalar(x_193)) {
 x_194 = lean_alloc_ctor(1, 2, 0);
} else {
 x_194 = x_193;
}
lean_ctor_set(x_194, 0, x_191);
lean_ctor_set(x_194, 1, x_192);
return x_194;
}
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_195 = lean_ctor_get(x_158, 1);
lean_inc(x_195);
if (lean_is_exclusive(x_158)) {
 lean_ctor_release(x_158, 0);
 lean_ctor_release(x_158, 1);
 x_196 = x_158;
} else {
 lean_dec_ref(x_158);
 x_196 = lean_box(0);
}
x_197 = lean_ctor_get(x_159, 2);
lean_inc(x_197);
lean_dec(x_159);
x_198 = l_Lean_IR_EmitC_toStringArgs(x_3);
x_199 = l_List_mfor___main___at_Lean_IR_EmitC_emitFnDecls___spec__5___closed__2;
x_200 = l_Lean_mkExternCall(x_197, x_199, x_198);
lean_dec(x_197);
if (lean_obj_tag(x_200) == 0)
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_201 = l_System_FilePath_dirName___closed__1;
x_202 = l_Lean_Name_toStringWithSep___main(x_201, x_2);
x_203 = l_Lean_IR_EmitC_emitFullApp___closed__1;
x_204 = lean_string_append(x_203, x_202);
lean_dec(x_202);
x_205 = l_Char_HasRepr___closed__1;
x_206 = lean_string_append(x_204, x_205);
if (lean_is_scalar(x_196)) {
 x_207 = lean_alloc_ctor(1, 2, 0);
} else {
 x_207 = x_196;
 lean_ctor_set_tag(x_207, 1);
}
lean_ctor_set(x_207, 0, x_206);
lean_ctor_set(x_207, 1, x_195);
return x_207;
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; 
lean_dec(x_2);
x_208 = lean_ctor_get(x_200, 0);
lean_inc(x_208);
lean_dec(x_200);
x_209 = lean_string_append(x_195, x_208);
lean_dec(x_208);
x_210 = l_Lean_IR_formatFnBody___main___closed__3;
x_211 = lean_string_append(x_209, x_210);
x_212 = l_IO_println___rarg___closed__1;
x_213 = lean_string_append(x_211, x_212);
if (lean_is_scalar(x_196)) {
 x_214 = lean_alloc_ctor(0, 2, 0);
} else {
 x_214 = x_196;
}
lean_ctor_set(x_214, 0, x_156);
lean_ctor_set(x_214, 1, x_213);
return x_214;
}
}
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; 
lean_dec(x_2);
x_215 = lean_ctor_get(x_158, 0);
lean_inc(x_215);
x_216 = lean_ctor_get(x_158, 1);
lean_inc(x_216);
if (lean_is_exclusive(x_158)) {
 lean_ctor_release(x_158, 0);
 lean_ctor_release(x_158, 1);
 x_217 = x_158;
} else {
 lean_dec_ref(x_158);
 x_217 = lean_box(0);
}
if (lean_is_scalar(x_217)) {
 x_218 = lean_alloc_ctor(1, 2, 0);
} else {
 x_218 = x_217;
}
lean_ctor_set(x_218, 0, x_215);
lean_ctor_set(x_218, 1, x_216);
return x_218;
}
}
}
else
{
uint8_t x_219; 
lean_dec(x_2);
x_219 = !lean_is_exclusive(x_6);
if (x_219 == 0)
{
return x_6;
}
else
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; 
x_220 = lean_ctor_get(x_6, 0);
x_221 = lean_ctor_get(x_6, 1);
lean_inc(x_221);
lean_inc(x_220);
lean_dec(x_6);
x_222 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_222, 0, x_220);
lean_ctor_set(x_222, 1, x_221);
return x_222;
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
lean_object* _init_l_Nat_mforAux___main___at_Lean_IR_EmitC_emitPartialApp___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("lean_closure_set(");
return x_1;
}
}
lean_object* l_Nat_mforAux___main___at_Lean_IR_EmitC_emitPartialApp___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_eq(x_4, x_7);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_6);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_10 = lean_ctor_get(x_6, 1);
x_11 = lean_ctor_get(x_6, 0);
lean_dec(x_11);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_sub(x_4, x_12);
lean_dec(x_4);
x_14 = lean_nat_sub(x_3, x_13);
x_15 = lean_nat_sub(x_14, x_12);
lean_dec(x_14);
x_16 = l_Lean_IR_Arg_Inhabited;
x_17 = lean_array_get(x_16, x_2, x_15);
x_18 = l_Nat_mforAux___main___at_Lean_IR_EmitC_emitPartialApp___spec__1___closed__1;
x_19 = lean_string_append(x_10, x_18);
lean_inc(x_1);
x_20 = l_Nat_repr(x_1);
x_21 = l_Lean_IR_VarId_HasToString___closed__1;
x_22 = lean_string_append(x_21, x_20);
lean_dec(x_20);
x_23 = lean_string_append(x_19, x_22);
lean_dec(x_22);
x_24 = l_List_reprAux___main___rarg___closed__1;
x_25 = lean_string_append(x_23, x_24);
x_26 = l_Nat_repr(x_15);
x_27 = lean_string_append(x_25, x_26);
lean_dec(x_26);
x_28 = lean_string_append(x_27, x_24);
x_29 = lean_box(0);
lean_ctor_set(x_6, 1, x_28);
lean_ctor_set(x_6, 0, x_29);
x_30 = l_Lean_IR_EmitC_emitArg(x_17, x_5, x_6);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_32 = lean_ctor_get(x_30, 1);
x_33 = lean_ctor_get(x_30, 0);
lean_dec(x_33);
x_34 = l_Lean_IR_EmitC_emitInc___closed__1;
x_35 = lean_string_append(x_32, x_34);
x_36 = l_IO_println___rarg___closed__1;
x_37 = lean_string_append(x_35, x_36);
lean_ctor_set(x_30, 1, x_37);
lean_ctor_set(x_30, 0, x_29);
x_4 = x_13;
x_6 = x_30;
goto _start;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_39 = lean_ctor_get(x_30, 1);
lean_inc(x_39);
lean_dec(x_30);
x_40 = l_Lean_IR_EmitC_emitInc___closed__1;
x_41 = lean_string_append(x_39, x_40);
x_42 = l_IO_println___rarg___closed__1;
x_43 = lean_string_append(x_41, x_42);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_29);
lean_ctor_set(x_44, 1, x_43);
x_4 = x_13;
x_6 = x_44;
goto _start;
}
}
else
{
uint8_t x_46; 
lean_dec(x_13);
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_30);
if (x_46 == 0)
{
return x_30;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_30, 0);
x_48 = lean_ctor_get(x_30, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_30);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_50 = lean_ctor_get(x_6, 1);
lean_inc(x_50);
lean_dec(x_6);
x_51 = lean_unsigned_to_nat(1u);
x_52 = lean_nat_sub(x_4, x_51);
lean_dec(x_4);
x_53 = lean_nat_sub(x_3, x_52);
x_54 = lean_nat_sub(x_53, x_51);
lean_dec(x_53);
x_55 = l_Lean_IR_Arg_Inhabited;
x_56 = lean_array_get(x_55, x_2, x_54);
x_57 = l_Nat_mforAux___main___at_Lean_IR_EmitC_emitPartialApp___spec__1___closed__1;
x_58 = lean_string_append(x_50, x_57);
lean_inc(x_1);
x_59 = l_Nat_repr(x_1);
x_60 = l_Lean_IR_VarId_HasToString___closed__1;
x_61 = lean_string_append(x_60, x_59);
lean_dec(x_59);
x_62 = lean_string_append(x_58, x_61);
lean_dec(x_61);
x_63 = l_List_reprAux___main___rarg___closed__1;
x_64 = lean_string_append(x_62, x_63);
x_65 = l_Nat_repr(x_54);
x_66 = lean_string_append(x_64, x_65);
lean_dec(x_65);
x_67 = lean_string_append(x_66, x_63);
x_68 = lean_box(0);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_67);
x_70 = l_Lean_IR_EmitC_emitArg(x_56, x_5, x_69);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_71 = lean_ctor_get(x_70, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_72 = x_70;
} else {
 lean_dec_ref(x_70);
 x_72 = lean_box(0);
}
x_73 = l_Lean_IR_EmitC_emitInc___closed__1;
x_74 = lean_string_append(x_71, x_73);
x_75 = l_IO_println___rarg___closed__1;
x_76 = lean_string_append(x_74, x_75);
if (lean_is_scalar(x_72)) {
 x_77 = lean_alloc_ctor(0, 2, 0);
} else {
 x_77 = x_72;
}
lean_ctor_set(x_77, 0, x_68);
lean_ctor_set(x_77, 1, x_76);
x_4 = x_52;
x_6 = x_77;
goto _start;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_52);
lean_dec(x_1);
x_79 = lean_ctor_get(x_70, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_70, 1);
lean_inc(x_80);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_81 = x_70;
} else {
 lean_dec_ref(x_70);
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
else
{
uint8_t x_83; 
lean_dec(x_4);
lean_dec(x_1);
x_83 = !lean_is_exclusive(x_6);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_6, 0);
lean_dec(x_84);
x_85 = lean_box(0);
lean_ctor_set(x_6, 0, x_85);
return x_6;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_6, 1);
lean_inc(x_86);
lean_dec(x_6);
x_87 = lean_box(0);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_86);
return x_88;
}
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
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_box(0);
lean_ctor_set(x_6, 0, x_9);
x_10 = l_Lean_IR_Decl_params(x_8);
lean_dec(x_8);
x_11 = lean_array_get_size(x_10);
lean_dec(x_10);
lean_inc(x_1);
x_12 = l_Lean_IR_EmitC_emitLhs(x_1, x_4, x_6);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_12, 1);
x_15 = lean_ctor_get(x_12, 0);
lean_dec(x_15);
x_16 = l_Lean_IR_EmitC_emitPartialApp___closed__1;
x_17 = lean_string_append(x_14, x_16);
lean_ctor_set(x_12, 1, x_17);
lean_ctor_set(x_12, 0, x_9);
x_18 = l_Lean_IR_EmitC_emitCName(x_2, x_4, x_12);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_20 = lean_ctor_get(x_18, 1);
x_21 = lean_ctor_get(x_18, 0);
lean_dec(x_21);
x_22 = l_Lean_IR_EmitC_emitPartialApp___closed__2;
x_23 = lean_string_append(x_20, x_22);
x_24 = l_Nat_repr(x_11);
x_25 = lean_string_append(x_23, x_24);
lean_dec(x_24);
x_26 = l_List_reprAux___main___rarg___closed__1;
x_27 = lean_string_append(x_25, x_26);
x_28 = lean_array_get_size(x_3);
lean_inc(x_28);
x_29 = l_Nat_repr(x_28);
x_30 = lean_string_append(x_27, x_29);
lean_dec(x_29);
x_31 = l_Lean_IR_EmitC_emitInc___closed__1;
x_32 = lean_string_append(x_30, x_31);
x_33 = l_IO_println___rarg___closed__1;
x_34 = lean_string_append(x_32, x_33);
lean_ctor_set(x_18, 1, x_34);
lean_ctor_set(x_18, 0, x_9);
lean_inc(x_28);
x_35 = l_Nat_mforAux___main___at_Lean_IR_EmitC_emitPartialApp___spec__1(x_1, x_3, x_28, x_28, x_4, x_18);
lean_dec(x_28);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_36 = lean_ctor_get(x_18, 1);
lean_inc(x_36);
lean_dec(x_18);
x_37 = l_Lean_IR_EmitC_emitPartialApp___closed__2;
x_38 = lean_string_append(x_36, x_37);
x_39 = l_Nat_repr(x_11);
x_40 = lean_string_append(x_38, x_39);
lean_dec(x_39);
x_41 = l_List_reprAux___main___rarg___closed__1;
x_42 = lean_string_append(x_40, x_41);
x_43 = lean_array_get_size(x_3);
lean_inc(x_43);
x_44 = l_Nat_repr(x_43);
x_45 = lean_string_append(x_42, x_44);
lean_dec(x_44);
x_46 = l_Lean_IR_EmitC_emitInc___closed__1;
x_47 = lean_string_append(x_45, x_46);
x_48 = l_IO_println___rarg___closed__1;
x_49 = lean_string_append(x_47, x_48);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_9);
lean_ctor_set(x_50, 1, x_49);
lean_inc(x_43);
x_51 = l_Nat_mforAux___main___at_Lean_IR_EmitC_emitPartialApp___spec__1(x_1, x_3, x_43, x_43, x_4, x_50);
lean_dec(x_43);
return x_51;
}
}
else
{
uint8_t x_52; 
lean_dec(x_11);
lean_dec(x_1);
x_52 = !lean_is_exclusive(x_18);
if (x_52 == 0)
{
return x_18;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_18, 0);
x_54 = lean_ctor_get(x_18, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_18);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_56 = lean_ctor_get(x_12, 1);
lean_inc(x_56);
lean_dec(x_12);
x_57 = l_Lean_IR_EmitC_emitPartialApp___closed__1;
x_58 = lean_string_append(x_56, x_57);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_9);
lean_ctor_set(x_59, 1, x_58);
x_60 = l_Lean_IR_EmitC_emitCName(x_2, x_4, x_59);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_61 = lean_ctor_get(x_60, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_62 = x_60;
} else {
 lean_dec_ref(x_60);
 x_62 = lean_box(0);
}
x_63 = l_Lean_IR_EmitC_emitPartialApp___closed__2;
x_64 = lean_string_append(x_61, x_63);
x_65 = l_Nat_repr(x_11);
x_66 = lean_string_append(x_64, x_65);
lean_dec(x_65);
x_67 = l_List_reprAux___main___rarg___closed__1;
x_68 = lean_string_append(x_66, x_67);
x_69 = lean_array_get_size(x_3);
lean_inc(x_69);
x_70 = l_Nat_repr(x_69);
x_71 = lean_string_append(x_68, x_70);
lean_dec(x_70);
x_72 = l_Lean_IR_EmitC_emitInc___closed__1;
x_73 = lean_string_append(x_71, x_72);
x_74 = l_IO_println___rarg___closed__1;
x_75 = lean_string_append(x_73, x_74);
if (lean_is_scalar(x_62)) {
 x_76 = lean_alloc_ctor(0, 2, 0);
} else {
 x_76 = x_62;
}
lean_ctor_set(x_76, 0, x_9);
lean_ctor_set(x_76, 1, x_75);
lean_inc(x_69);
x_77 = l_Nat_mforAux___main___at_Lean_IR_EmitC_emitPartialApp___spec__1(x_1, x_3, x_69, x_69, x_4, x_76);
lean_dec(x_69);
return x_77;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_11);
lean_dec(x_1);
x_78 = lean_ctor_get(x_60, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_60, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_80 = x_60;
} else {
 lean_dec_ref(x_60);
 x_80 = lean_box(0);
}
if (lean_is_scalar(x_80)) {
 x_81 = lean_alloc_ctor(1, 2, 0);
} else {
 x_81 = x_80;
}
lean_ctor_set(x_81, 0, x_78);
lean_ctor_set(x_81, 1, x_79);
return x_81;
}
}
}
else
{
uint8_t x_82; 
lean_dec(x_11);
lean_dec(x_2);
lean_dec(x_1);
x_82 = !lean_is_exclusive(x_12);
if (x_82 == 0)
{
return x_12;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_12, 0);
x_84 = lean_ctor_get(x_12, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_12);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_86 = lean_ctor_get(x_6, 0);
x_87 = lean_ctor_get(x_6, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_6);
x_88 = lean_box(0);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_87);
x_90 = l_Lean_IR_Decl_params(x_86);
lean_dec(x_86);
x_91 = lean_array_get_size(x_90);
lean_dec(x_90);
lean_inc(x_1);
x_92 = l_Lean_IR_EmitC_emitLhs(x_1, x_4, x_89);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_93 = lean_ctor_get(x_92, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 x_94 = x_92;
} else {
 lean_dec_ref(x_92);
 x_94 = lean_box(0);
}
x_95 = l_Lean_IR_EmitC_emitPartialApp___closed__1;
x_96 = lean_string_append(x_93, x_95);
if (lean_is_scalar(x_94)) {
 x_97 = lean_alloc_ctor(0, 2, 0);
} else {
 x_97 = x_94;
}
lean_ctor_set(x_97, 0, x_88);
lean_ctor_set(x_97, 1, x_96);
x_98 = l_Lean_IR_EmitC_emitCName(x_2, x_4, x_97);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_99 = lean_ctor_get(x_98, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 lean_ctor_release(x_98, 1);
 x_100 = x_98;
} else {
 lean_dec_ref(x_98);
 x_100 = lean_box(0);
}
x_101 = l_Lean_IR_EmitC_emitPartialApp___closed__2;
x_102 = lean_string_append(x_99, x_101);
x_103 = l_Nat_repr(x_91);
x_104 = lean_string_append(x_102, x_103);
lean_dec(x_103);
x_105 = l_List_reprAux___main___rarg___closed__1;
x_106 = lean_string_append(x_104, x_105);
x_107 = lean_array_get_size(x_3);
lean_inc(x_107);
x_108 = l_Nat_repr(x_107);
x_109 = lean_string_append(x_106, x_108);
lean_dec(x_108);
x_110 = l_Lean_IR_EmitC_emitInc___closed__1;
x_111 = lean_string_append(x_109, x_110);
x_112 = l_IO_println___rarg___closed__1;
x_113 = lean_string_append(x_111, x_112);
if (lean_is_scalar(x_100)) {
 x_114 = lean_alloc_ctor(0, 2, 0);
} else {
 x_114 = x_100;
}
lean_ctor_set(x_114, 0, x_88);
lean_ctor_set(x_114, 1, x_113);
lean_inc(x_107);
x_115 = l_Nat_mforAux___main___at_Lean_IR_EmitC_emitPartialApp___spec__1(x_1, x_3, x_107, x_107, x_4, x_114);
lean_dec(x_107);
return x_115;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
lean_dec(x_91);
lean_dec(x_1);
x_116 = lean_ctor_get(x_98, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_98, 1);
lean_inc(x_117);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 lean_ctor_release(x_98, 1);
 x_118 = x_98;
} else {
 lean_dec_ref(x_98);
 x_118 = lean_box(0);
}
if (lean_is_scalar(x_118)) {
 x_119 = lean_alloc_ctor(1, 2, 0);
} else {
 x_119 = x_118;
}
lean_ctor_set(x_119, 0, x_116);
lean_ctor_set(x_119, 1, x_117);
return x_119;
}
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
lean_dec(x_91);
lean_dec(x_2);
lean_dec(x_1);
x_120 = lean_ctor_get(x_92, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_92, 1);
lean_inc(x_121);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 x_122 = x_92;
} else {
 lean_dec_ref(x_92);
 x_122 = lean_box(0);
}
if (lean_is_scalar(x_122)) {
 x_123 = lean_alloc_ctor(1, 2, 0);
} else {
 x_123 = x_122;
}
lean_ctor_set(x_123, 0, x_120);
lean_ctor_set(x_123, 1, x_121);
return x_123;
}
}
}
else
{
uint8_t x_124; 
lean_dec(x_2);
lean_dec(x_1);
x_124 = !lean_is_exclusive(x_6);
if (x_124 == 0)
{
return x_6;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_6, 0);
x_126 = lean_ctor_get(x_6, 1);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_6);
x_127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
return x_127;
}
}
}
}
lean_object* l_Nat_mforAux___main___at_Lean_IR_EmitC_emitPartialApp___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Nat_mforAux___main___at_Lean_IR_EmitC_emitPartialApp___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
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
lean_object* x_9; 
x_9 = l_Lean_IR_EmitC_emitLhs(x_1, x_4, x_5);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_11 = lean_ctor_get(x_9, 1);
x_12 = lean_ctor_get(x_9, 0);
lean_dec(x_12);
x_13 = l_Lean_IR_EmitC_emitApp___closed__1;
x_14 = lean_string_append(x_11, x_13);
x_15 = l_Nat_repr(x_6);
x_16 = lean_string_append(x_14, x_15);
lean_dec(x_15);
x_17 = l_Prod_HasRepr___rarg___closed__1;
x_18 = lean_string_append(x_16, x_17);
x_19 = l_Nat_repr(x_2);
x_20 = l_Lean_IR_VarId_HasToString___closed__1;
x_21 = lean_string_append(x_20, x_19);
lean_dec(x_19);
x_22 = lean_string_append(x_18, x_21);
lean_dec(x_21);
x_23 = l_List_reprAux___main___rarg___closed__1;
x_24 = lean_string_append(x_22, x_23);
x_25 = lean_box(0);
lean_ctor_set(x_9, 1, x_24);
lean_ctor_set(x_9, 0, x_25);
x_26 = l_Lean_IR_EmitC_emitArgs(x_3, x_4, x_9);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_28 = lean_ctor_get(x_26, 1);
x_29 = lean_ctor_get(x_26, 0);
lean_dec(x_29);
x_30 = l_Lean_IR_EmitC_emitInc___closed__1;
x_31 = lean_string_append(x_28, x_30);
x_32 = l_IO_println___rarg___closed__1;
x_33 = lean_string_append(x_31, x_32);
lean_ctor_set(x_26, 1, x_33);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_34 = lean_ctor_get(x_26, 1);
lean_inc(x_34);
lean_dec(x_26);
x_35 = l_Lean_IR_EmitC_emitInc___closed__1;
x_36 = lean_string_append(x_34, x_35);
x_37 = l_IO_println___rarg___closed__1;
x_38 = lean_string_append(x_36, x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_25);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
else
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_26);
if (x_40 == 0)
{
return x_26;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_26, 0);
x_42 = lean_ctor_get(x_26, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_26);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_44 = lean_ctor_get(x_9, 1);
lean_inc(x_44);
lean_dec(x_9);
x_45 = l_Lean_IR_EmitC_emitApp___closed__1;
x_46 = lean_string_append(x_44, x_45);
x_47 = l_Nat_repr(x_6);
x_48 = lean_string_append(x_46, x_47);
lean_dec(x_47);
x_49 = l_Prod_HasRepr___rarg___closed__1;
x_50 = lean_string_append(x_48, x_49);
x_51 = l_Nat_repr(x_2);
x_52 = l_Lean_IR_VarId_HasToString___closed__1;
x_53 = lean_string_append(x_52, x_51);
lean_dec(x_51);
x_54 = lean_string_append(x_50, x_53);
lean_dec(x_53);
x_55 = l_List_reprAux___main___rarg___closed__1;
x_56 = lean_string_append(x_54, x_55);
x_57 = lean_box(0);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_56);
x_59 = l_Lean_IR_EmitC_emitArgs(x_3, x_4, x_58);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_60 = lean_ctor_get(x_59, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_61 = x_59;
} else {
 lean_dec_ref(x_59);
 x_61 = lean_box(0);
}
x_62 = l_Lean_IR_EmitC_emitInc___closed__1;
x_63 = lean_string_append(x_60, x_62);
x_64 = l_IO_println___rarg___closed__1;
x_65 = lean_string_append(x_63, x_64);
if (lean_is_scalar(x_61)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_61;
}
lean_ctor_set(x_66, 0, x_57);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_67 = lean_ctor_get(x_59, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_59, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_69 = x_59;
} else {
 lean_dec_ref(x_59);
 x_69 = lean_box(0);
}
if (lean_is_scalar(x_69)) {
 x_70 = lean_alloc_ctor(1, 2, 0);
} else {
 x_70 = x_69;
}
lean_ctor_set(x_70, 0, x_67);
lean_ctor_set(x_70, 1, x_68);
return x_70;
}
}
}
else
{
uint8_t x_71; 
lean_dec(x_6);
lean_dec(x_2);
x_71 = !lean_is_exclusive(x_9);
if (x_71 == 0)
{
return x_9;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_9, 0);
x_73 = lean_ctor_get(x_9, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_9);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
else
{
uint8_t x_75; 
x_75 = !lean_is_exclusive(x_5);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_76 = lean_ctor_get(x_5, 1);
x_77 = lean_ctor_get(x_5, 0);
lean_dec(x_77);
x_78 = l_Lean_IR_EmitC_emitApp___closed__2;
x_79 = lean_string_append(x_76, x_78);
x_80 = lean_box(0);
lean_ctor_set(x_5, 1, x_79);
lean_ctor_set(x_5, 0, x_80);
x_81 = l_Lean_IR_EmitC_emitArgs(x_3, x_4, x_5);
if (lean_obj_tag(x_81) == 0)
{
uint8_t x_82; 
x_82 = !lean_is_exclusive(x_81);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_83 = lean_ctor_get(x_81, 1);
x_84 = lean_ctor_get(x_81, 0);
lean_dec(x_84);
x_85 = l_Lean_IR_EmitC_emitApp___closed__3;
x_86 = lean_string_append(x_83, x_85);
x_87 = l_IO_println___rarg___closed__1;
x_88 = lean_string_append(x_86, x_87);
lean_ctor_set(x_81, 1, x_88);
lean_ctor_set(x_81, 0, x_80);
x_89 = l_Lean_IR_EmitC_emitLhs(x_1, x_4, x_81);
if (lean_obj_tag(x_89) == 0)
{
uint8_t x_90; 
x_90 = !lean_is_exclusive(x_89);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_91 = lean_ctor_get(x_89, 1);
x_92 = lean_ctor_get(x_89, 0);
lean_dec(x_92);
x_93 = l_Lean_IR_EmitC_emitApp___closed__4;
x_94 = lean_string_append(x_91, x_93);
x_95 = l_Nat_repr(x_2);
x_96 = l_Lean_IR_VarId_HasToString___closed__1;
x_97 = lean_string_append(x_96, x_95);
lean_dec(x_95);
x_98 = lean_string_append(x_94, x_97);
lean_dec(x_97);
x_99 = l_List_reprAux___main___rarg___closed__1;
x_100 = lean_string_append(x_98, x_99);
x_101 = l_Nat_repr(x_6);
x_102 = lean_string_append(x_100, x_101);
lean_dec(x_101);
x_103 = l_Lean_IR_EmitC_emitApp___closed__5;
x_104 = lean_string_append(x_102, x_103);
x_105 = lean_string_append(x_104, x_87);
lean_ctor_set(x_89, 1, x_105);
lean_ctor_set(x_89, 0, x_80);
return x_89;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_106 = lean_ctor_get(x_89, 1);
lean_inc(x_106);
lean_dec(x_89);
x_107 = l_Lean_IR_EmitC_emitApp___closed__4;
x_108 = lean_string_append(x_106, x_107);
x_109 = l_Nat_repr(x_2);
x_110 = l_Lean_IR_VarId_HasToString___closed__1;
x_111 = lean_string_append(x_110, x_109);
lean_dec(x_109);
x_112 = lean_string_append(x_108, x_111);
lean_dec(x_111);
x_113 = l_List_reprAux___main___rarg___closed__1;
x_114 = lean_string_append(x_112, x_113);
x_115 = l_Nat_repr(x_6);
x_116 = lean_string_append(x_114, x_115);
lean_dec(x_115);
x_117 = l_Lean_IR_EmitC_emitApp___closed__5;
x_118 = lean_string_append(x_116, x_117);
x_119 = lean_string_append(x_118, x_87);
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_80);
lean_ctor_set(x_120, 1, x_119);
return x_120;
}
}
else
{
uint8_t x_121; 
lean_dec(x_6);
lean_dec(x_2);
x_121 = !lean_is_exclusive(x_89);
if (x_121 == 0)
{
return x_89;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_89, 0);
x_123 = lean_ctor_get(x_89, 1);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_89);
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set(x_124, 1, x_123);
return x_124;
}
}
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_125 = lean_ctor_get(x_81, 1);
lean_inc(x_125);
lean_dec(x_81);
x_126 = l_Lean_IR_EmitC_emitApp___closed__3;
x_127 = lean_string_append(x_125, x_126);
x_128 = l_IO_println___rarg___closed__1;
x_129 = lean_string_append(x_127, x_128);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_80);
lean_ctor_set(x_130, 1, x_129);
x_131 = l_Lean_IR_EmitC_emitLhs(x_1, x_4, x_130);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_132 = lean_ctor_get(x_131, 1);
lean_inc(x_132);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 x_133 = x_131;
} else {
 lean_dec_ref(x_131);
 x_133 = lean_box(0);
}
x_134 = l_Lean_IR_EmitC_emitApp___closed__4;
x_135 = lean_string_append(x_132, x_134);
x_136 = l_Nat_repr(x_2);
x_137 = l_Lean_IR_VarId_HasToString___closed__1;
x_138 = lean_string_append(x_137, x_136);
lean_dec(x_136);
x_139 = lean_string_append(x_135, x_138);
lean_dec(x_138);
x_140 = l_List_reprAux___main___rarg___closed__1;
x_141 = lean_string_append(x_139, x_140);
x_142 = l_Nat_repr(x_6);
x_143 = lean_string_append(x_141, x_142);
lean_dec(x_142);
x_144 = l_Lean_IR_EmitC_emitApp___closed__5;
x_145 = lean_string_append(x_143, x_144);
x_146 = lean_string_append(x_145, x_128);
if (lean_is_scalar(x_133)) {
 x_147 = lean_alloc_ctor(0, 2, 0);
} else {
 x_147 = x_133;
}
lean_ctor_set(x_147, 0, x_80);
lean_ctor_set(x_147, 1, x_146);
return x_147;
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
lean_dec(x_6);
lean_dec(x_2);
x_148 = lean_ctor_get(x_131, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_131, 1);
lean_inc(x_149);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 x_150 = x_131;
} else {
 lean_dec_ref(x_131);
 x_150 = lean_box(0);
}
if (lean_is_scalar(x_150)) {
 x_151 = lean_alloc_ctor(1, 2, 0);
} else {
 x_151 = x_150;
}
lean_ctor_set(x_151, 0, x_148);
lean_ctor_set(x_151, 1, x_149);
return x_151;
}
}
}
else
{
uint8_t x_152; 
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_152 = !lean_is_exclusive(x_81);
if (x_152 == 0)
{
return x_81;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_153 = lean_ctor_get(x_81, 0);
x_154 = lean_ctor_get(x_81, 1);
lean_inc(x_154);
lean_inc(x_153);
lean_dec(x_81);
x_155 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_155, 0, x_153);
lean_ctor_set(x_155, 1, x_154);
return x_155;
}
}
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_156 = lean_ctor_get(x_5, 1);
lean_inc(x_156);
lean_dec(x_5);
x_157 = l_Lean_IR_EmitC_emitApp___closed__2;
x_158 = lean_string_append(x_156, x_157);
x_159 = lean_box(0);
x_160 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_160, 1, x_158);
x_161 = l_Lean_IR_EmitC_emitArgs(x_3, x_4, x_160);
if (lean_obj_tag(x_161) == 0)
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_162 = lean_ctor_get(x_161, 1);
lean_inc(x_162);
if (lean_is_exclusive(x_161)) {
 lean_ctor_release(x_161, 0);
 lean_ctor_release(x_161, 1);
 x_163 = x_161;
} else {
 lean_dec_ref(x_161);
 x_163 = lean_box(0);
}
x_164 = l_Lean_IR_EmitC_emitApp___closed__3;
x_165 = lean_string_append(x_162, x_164);
x_166 = l_IO_println___rarg___closed__1;
x_167 = lean_string_append(x_165, x_166);
if (lean_is_scalar(x_163)) {
 x_168 = lean_alloc_ctor(0, 2, 0);
} else {
 x_168 = x_163;
}
lean_ctor_set(x_168, 0, x_159);
lean_ctor_set(x_168, 1, x_167);
x_169 = l_Lean_IR_EmitC_emitLhs(x_1, x_4, x_168);
if (lean_obj_tag(x_169) == 0)
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_170 = lean_ctor_get(x_169, 1);
lean_inc(x_170);
if (lean_is_exclusive(x_169)) {
 lean_ctor_release(x_169, 0);
 lean_ctor_release(x_169, 1);
 x_171 = x_169;
} else {
 lean_dec_ref(x_169);
 x_171 = lean_box(0);
}
x_172 = l_Lean_IR_EmitC_emitApp___closed__4;
x_173 = lean_string_append(x_170, x_172);
x_174 = l_Nat_repr(x_2);
x_175 = l_Lean_IR_VarId_HasToString___closed__1;
x_176 = lean_string_append(x_175, x_174);
lean_dec(x_174);
x_177 = lean_string_append(x_173, x_176);
lean_dec(x_176);
x_178 = l_List_reprAux___main___rarg___closed__1;
x_179 = lean_string_append(x_177, x_178);
x_180 = l_Nat_repr(x_6);
x_181 = lean_string_append(x_179, x_180);
lean_dec(x_180);
x_182 = l_Lean_IR_EmitC_emitApp___closed__5;
x_183 = lean_string_append(x_181, x_182);
x_184 = lean_string_append(x_183, x_166);
if (lean_is_scalar(x_171)) {
 x_185 = lean_alloc_ctor(0, 2, 0);
} else {
 x_185 = x_171;
}
lean_ctor_set(x_185, 0, x_159);
lean_ctor_set(x_185, 1, x_184);
return x_185;
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; 
lean_dec(x_6);
lean_dec(x_2);
x_186 = lean_ctor_get(x_169, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_169, 1);
lean_inc(x_187);
if (lean_is_exclusive(x_169)) {
 lean_ctor_release(x_169, 0);
 lean_ctor_release(x_169, 1);
 x_188 = x_169;
} else {
 lean_dec_ref(x_169);
 x_188 = lean_box(0);
}
if (lean_is_scalar(x_188)) {
 x_189 = lean_alloc_ctor(1, 2, 0);
} else {
 x_189 = x_188;
}
lean_ctor_set(x_189, 0, x_186);
lean_ctor_set(x_189, 1, x_187);
return x_189;
}
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_190 = lean_ctor_get(x_161, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_161, 1);
lean_inc(x_191);
if (lean_is_exclusive(x_161)) {
 lean_ctor_release(x_161, 0);
 lean_ctor_release(x_161, 1);
 x_192 = x_161;
} else {
 lean_dec_ref(x_161);
 x_192 = lean_box(0);
}
if (lean_is_scalar(x_192)) {
 x_193 = lean_alloc_ctor(1, 2, 0);
} else {
 x_193 = x_192;
}
lean_ctor_set(x_193, 0, x_190);
lean_ctor_set(x_193, 1, x_191);
return x_193;
}
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
lean_object* l_Lean_IR_EmitC_emitBoxFn(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_box(x_1);
switch (lean_obj_tag(x_4)) {
case 0:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_3, 0);
lean_dec(x_6);
x_7 = l_Lean_IR_EmitC_emitSSet___closed__2;
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 0, x_7);
return x_3;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_dec(x_3);
x_9 = l_Lean_IR_EmitC_emitSSet___closed__2;
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
}
case 3:
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_3);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_3, 1);
x_13 = lean_ctor_get(x_3, 0);
lean_dec(x_13);
x_14 = l_Lean_IR_EmitC_emitBoxFn___closed__2;
x_15 = lean_string_append(x_12, x_14);
x_16 = lean_box(0);
lean_ctor_set(x_3, 1, x_15);
lean_ctor_set(x_3, 0, x_16);
return x_3;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_3, 1);
lean_inc(x_17);
lean_dec(x_3);
x_18 = l_Lean_IR_EmitC_emitBoxFn___closed__2;
x_19 = lean_string_append(x_17, x_18);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
case 4:
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_3);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_3, 1);
x_24 = lean_ctor_get(x_3, 0);
lean_dec(x_24);
x_25 = l_Lean_IR_EmitC_emitBoxFn___closed__3;
x_26 = lean_string_append(x_23, x_25);
x_27 = lean_box(0);
lean_ctor_set(x_3, 1, x_26);
lean_ctor_set(x_3, 0, x_27);
return x_3;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_3, 1);
lean_inc(x_28);
lean_dec(x_3);
x_29 = l_Lean_IR_EmitC_emitBoxFn___closed__3;
x_30 = lean_string_append(x_28, x_29);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
case 5:
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_3);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_34 = lean_ctor_get(x_3, 1);
x_35 = lean_ctor_get(x_3, 0);
lean_dec(x_35);
x_36 = l_Lean_IR_EmitC_emitBoxFn___closed__4;
x_37 = lean_string_append(x_34, x_36);
x_38 = lean_box(0);
lean_ctor_set(x_3, 1, x_37);
lean_ctor_set(x_3, 0, x_38);
return x_3;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_39 = lean_ctor_get(x_3, 1);
lean_inc(x_39);
lean_dec(x_3);
x_40 = l_Lean_IR_EmitC_emitBoxFn___closed__4;
x_41 = lean_string_append(x_39, x_40);
x_42 = lean_box(0);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_41);
return x_43;
}
}
default: 
{
uint8_t x_44; 
lean_dec(x_4);
x_44 = !lean_is_exclusive(x_3);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_45 = lean_ctor_get(x_3, 1);
x_46 = lean_ctor_get(x_3, 0);
lean_dec(x_46);
x_47 = l_Lean_IR_EmitC_emitBoxFn___closed__1;
x_48 = lean_string_append(x_45, x_47);
x_49 = lean_box(0);
lean_ctor_set(x_3, 1, x_48);
lean_ctor_set(x_3, 0, x_49);
return x_3;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_50 = lean_ctor_get(x_3, 1);
lean_inc(x_50);
lean_dec(x_3);
x_51 = l_Lean_IR_EmitC_emitBoxFn___closed__1;
x_52 = lean_string_append(x_50, x_51);
x_53 = lean_box(0);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_52);
return x_54;
}
}
}
}
}
lean_object* l_Lean_IR_EmitC_emitBoxFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_Lean_IR_EmitC_emitBoxFn(x_4, x_2, x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_IR_EmitC_emitBox(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_EmitC_emitLhs(x_1, x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_6, 0);
lean_dec(x_8);
x_9 = lean_box(0);
lean_ctor_set(x_6, 0, x_9);
x_10 = l_Lean_IR_EmitC_emitBoxFn(x_3, x_4, x_6);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_12 = lean_ctor_get(x_10, 1);
x_13 = lean_ctor_get(x_10, 0);
lean_dec(x_13);
x_14 = l_Prod_HasRepr___rarg___closed__1;
x_15 = lean_string_append(x_12, x_14);
x_16 = l_Nat_repr(x_2);
x_17 = l_Lean_IR_VarId_HasToString___closed__1;
x_18 = lean_string_append(x_17, x_16);
lean_dec(x_16);
x_19 = lean_string_append(x_15, x_18);
lean_dec(x_18);
x_20 = l_Lean_IR_EmitC_emitInc___closed__1;
x_21 = lean_string_append(x_19, x_20);
x_22 = l_IO_println___rarg___closed__1;
x_23 = lean_string_append(x_21, x_22);
lean_ctor_set(x_10, 1, x_23);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_24 = lean_ctor_get(x_10, 1);
lean_inc(x_24);
lean_dec(x_10);
x_25 = l_Prod_HasRepr___rarg___closed__1;
x_26 = lean_string_append(x_24, x_25);
x_27 = l_Nat_repr(x_2);
x_28 = l_Lean_IR_VarId_HasToString___closed__1;
x_29 = lean_string_append(x_28, x_27);
lean_dec(x_27);
x_30 = lean_string_append(x_26, x_29);
lean_dec(x_29);
x_31 = l_Lean_IR_EmitC_emitInc___closed__1;
x_32 = lean_string_append(x_30, x_31);
x_33 = l_IO_println___rarg___closed__1;
x_34 = lean_string_append(x_32, x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_9);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
else
{
uint8_t x_36; 
lean_dec(x_2);
x_36 = !lean_is_exclusive(x_10);
if (x_36 == 0)
{
return x_10;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_10, 0);
x_38 = lean_ctor_get(x_10, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_10);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_6, 1);
lean_inc(x_40);
lean_dec(x_6);
x_41 = lean_box(0);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
x_43 = l_Lean_IR_EmitC_emitBoxFn(x_3, x_4, x_42);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_45 = x_43;
} else {
 lean_dec_ref(x_43);
 x_45 = lean_box(0);
}
x_46 = l_Prod_HasRepr___rarg___closed__1;
x_47 = lean_string_append(x_44, x_46);
x_48 = l_Nat_repr(x_2);
x_49 = l_Lean_IR_VarId_HasToString___closed__1;
x_50 = lean_string_append(x_49, x_48);
lean_dec(x_48);
x_51 = lean_string_append(x_47, x_50);
lean_dec(x_50);
x_52 = l_Lean_IR_EmitC_emitInc___closed__1;
x_53 = lean_string_append(x_51, x_52);
x_54 = l_IO_println___rarg___closed__1;
x_55 = lean_string_append(x_53, x_54);
if (lean_is_scalar(x_45)) {
 x_56 = lean_alloc_ctor(0, 2, 0);
} else {
 x_56 = x_45;
}
lean_ctor_set(x_56, 0, x_41);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_2);
x_57 = lean_ctor_get(x_43, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_43, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_59 = x_43;
} else {
 lean_dec_ref(x_43);
 x_59 = lean_box(0);
}
if (lean_is_scalar(x_59)) {
 x_60 = lean_alloc_ctor(1, 2, 0);
} else {
 x_60 = x_59;
}
lean_ctor_set(x_60, 0, x_57);
lean_ctor_set(x_60, 1, x_58);
return x_60;
}
}
}
else
{
uint8_t x_61; 
lean_dec(x_2);
x_61 = !lean_is_exclusive(x_6);
if (x_61 == 0)
{
return x_6;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_6, 0);
x_63 = lean_ctor_get(x_6, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_6);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
}
lean_object* l_Lean_IR_EmitC_emitBox___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_3);
lean_dec(x_3);
x_7 = l_Lean_IR_EmitC_emitBox(x_1, x_2, x_6, x_4, x_5);
lean_dec(x_4);
return x_7;
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
lean_object* l_Lean_IR_EmitC_emitUnbox(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_20; 
x_20 = l_Lean_IR_EmitC_emitLhs(x_1, x_4, x_5);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
x_21 = lean_box(x_2);
switch (lean_obj_tag(x_21)) {
case 0:
{
uint8_t x_22; 
lean_dec(x_3);
x_22 = !lean_is_exclusive(x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_20, 0);
lean_dec(x_23);
x_24 = l_Lean_IR_EmitC_emitSSet___closed__2;
lean_ctor_set_tag(x_20, 1);
lean_ctor_set(x_20, 0, x_24);
return x_20;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_20, 1);
lean_inc(x_25);
lean_dec(x_20);
x_26 = l_Lean_IR_EmitC_emitSSet___closed__2;
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
case 3:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_20, 1);
lean_inc(x_28);
lean_dec(x_20);
x_29 = l_Lean_IR_EmitC_emitUnbox___closed__2;
x_30 = lean_string_append(x_28, x_29);
x_6 = x_30;
goto block_19;
}
case 4:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_20, 1);
lean_inc(x_31);
lean_dec(x_20);
x_32 = l_Lean_IR_EmitC_emitUnbox___closed__3;
x_33 = lean_string_append(x_31, x_32);
x_6 = x_33;
goto block_19;
}
case 5:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_20, 1);
lean_inc(x_34);
lean_dec(x_20);
x_35 = l_Lean_IR_EmitC_emitUnbox___closed__4;
x_36 = lean_string_append(x_34, x_35);
x_6 = x_36;
goto block_19;
}
default: 
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_21);
x_37 = lean_ctor_get(x_20, 1);
lean_inc(x_37);
lean_dec(x_20);
x_38 = l_Lean_IR_EmitC_emitUnbox___closed__1;
x_39 = lean_string_append(x_37, x_38);
x_6 = x_39;
goto block_19;
}
}
}
else
{
uint8_t x_40; 
lean_dec(x_3);
x_40 = !lean_is_exclusive(x_20);
if (x_40 == 0)
{
return x_20;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_20, 0);
x_42 = lean_ctor_get(x_20, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_20);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
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
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = l_Lean_IR_EmitC_emitUnbox(x_1, x_6, x_3, x_4, x_5);
lean_dec(x_4);
return x_7;
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
lean_object* x_5; 
x_5 = l_Lean_IR_EmitC_emitLhs(x_1, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
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
else
{
uint8_t x_33; 
lean_dec(x_2);
x_33 = !lean_is_exclusive(x_5);
if (x_33 == 0)
{
return x_5;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_5, 0);
x_35 = lean_ctor_get(x_5, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_5);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
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
lean_object* x_5; 
x_5 = l_Lean_IR_EmitC_emitLhs(x_1, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
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
else
{
uint8_t x_33; 
lean_dec(x_2);
x_33 = !lean_is_exclusive(x_5);
if (x_33 == 0)
{
return x_5;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_5, 0);
x_35 = lean_ctor_get(x_5, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_5);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
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
uint8_t x_5; 
x_5 = lean_nat_dec_eq(x_3, x_2);
if (x_5 == 0)
{
lean_object* x_6; uint32_t x_7; uint32_t x_8; uint8_t x_9; 
x_6 = lean_string_utf8_next(x_1, x_3);
x_7 = lean_string_utf8_get(x_1, x_3);
lean_dec(x_3);
x_8 = 10;
x_9 = x_7 == x_8;
if (x_9 == 0)
{
uint32_t x_10; uint8_t x_11; uint8_t x_38; 
x_10 = 92;
x_38 = x_7 == x_10;
if (x_38 == 0)
{
uint8_t x_39; 
x_39 = 0;
x_11 = x_39;
goto block_37;
}
else
{
uint8_t x_40; 
x_40 = 1;
x_11 = x_40;
goto block_37;
}
block_37:
{
if (x_11 == 0)
{
uint32_t x_12; uint8_t x_13; 
x_12 = 34;
x_13 = x_7 == x_12;
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_uint32_to_nat(x_7);
x_15 = lean_unsigned_to_nat(31u);
x_16 = lean_nat_dec_le(x_14, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_14);
x_17 = l_String_splitAux___main___closed__1;
x_18 = lean_string_push(x_17, x_7);
x_19 = lean_string_append(x_4, x_18);
lean_dec(x_18);
x_3 = x_6;
x_4 = x_19;
goto _start;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_21 = lean_unsigned_to_nat(16u);
x_22 = lean_nat_div(x_14, x_21);
x_23 = l_Lean_IR_EmitC_toHexDigit(x_22);
lean_dec(x_22);
x_24 = l_Char_quoteCore___closed__1;
x_25 = lean_string_append(x_24, x_23);
lean_dec(x_23);
x_26 = lean_nat_mod(x_14, x_21);
lean_dec(x_14);
x_27 = l_Lean_IR_EmitC_toHexDigit(x_26);
lean_dec(x_26);
x_28 = lean_string_append(x_25, x_27);
lean_dec(x_27);
x_29 = lean_string_append(x_4, x_28);
lean_dec(x_28);
x_3 = x_6;
x_4 = x_29;
goto _start;
}
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = l_Char_quoteCore___closed__2;
x_32 = lean_string_append(x_4, x_31);
x_3 = x_6;
x_4 = x_32;
goto _start;
}
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = l_Char_quoteCore___closed__3;
x_35 = lean_string_append(x_4, x_34);
x_3 = x_6;
x_4 = x_35;
goto _start;
}
}
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = l_Char_quoteCore___closed__5;
x_42 = lean_string_append(x_4, x_41);
x_3 = x_6;
x_4 = x_42;
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
lean_object* l_Lean_IR_EmitC_emitNumLit(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Lean_IR_IRType_isObj(x_1);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_ctor_get(x_4, 0);
lean_dec(x_8);
x_9 = l_Nat_repr(x_2);
x_10 = lean_string_append(x_7, x_9);
lean_dec(x_9);
x_11 = lean_box(0);
lean_ctor_set(x_4, 1, x_10);
lean_ctor_set(x_4, 0, x_11);
return x_4;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_4, 1);
lean_inc(x_12);
lean_dec(x_4);
x_13 = l_Nat_repr(x_2);
x_14 = lean_string_append(x_12, x_13);
lean_dec(x_13);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
else
{
lean_object* x_17; uint8_t x_18; 
x_17 = l_uint32Sz;
x_18 = lean_nat_dec_lt(x_2, x_17);
if (x_18 == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_4);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_20 = lean_ctor_get(x_4, 1);
x_21 = lean_ctor_get(x_4, 0);
lean_dec(x_21);
x_22 = l_Lean_IR_EmitC_emitNumLit___closed__1;
x_23 = lean_string_append(x_20, x_22);
x_24 = l_Nat_repr(x_2);
x_25 = lean_string_append(x_23, x_24);
lean_dec(x_24);
x_26 = l_Lean_IR_EmitC_emitNumLit___closed__2;
x_27 = lean_string_append(x_25, x_26);
x_28 = lean_box(0);
lean_ctor_set(x_4, 1, x_27);
lean_ctor_set(x_4, 0, x_28);
return x_4;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_29 = lean_ctor_get(x_4, 1);
lean_inc(x_29);
lean_dec(x_4);
x_30 = l_Lean_IR_EmitC_emitNumLit___closed__1;
x_31 = lean_string_append(x_29, x_30);
x_32 = l_Nat_repr(x_2);
x_33 = lean_string_append(x_31, x_32);
lean_dec(x_32);
x_34 = l_Lean_IR_EmitC_emitNumLit___closed__2;
x_35 = lean_string_append(x_33, x_34);
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
else
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_4);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_39 = lean_ctor_get(x_4, 1);
x_40 = lean_ctor_get(x_4, 0);
lean_dec(x_40);
x_41 = l_Lean_IR_EmitC_emitNumLit___closed__3;
x_42 = lean_string_append(x_39, x_41);
x_43 = l_Nat_repr(x_2);
x_44 = lean_string_append(x_42, x_43);
lean_dec(x_43);
x_45 = l_Lean_IR_EmitC_emitNumLit___closed__4;
x_46 = lean_string_append(x_44, x_45);
x_47 = lean_box(0);
lean_ctor_set(x_4, 1, x_46);
lean_ctor_set(x_4, 0, x_47);
return x_4;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_48 = lean_ctor_get(x_4, 1);
lean_inc(x_48);
lean_dec(x_4);
x_49 = l_Lean_IR_EmitC_emitNumLit___closed__3;
x_50 = lean_string_append(x_48, x_49);
x_51 = l_Nat_repr(x_2);
x_52 = lean_string_append(x_50, x_51);
lean_dec(x_51);
x_53 = l_Lean_IR_EmitC_emitNumLit___closed__4;
x_54 = lean_string_append(x_52, x_53);
x_55 = lean_box(0);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_54);
return x_56;
}
}
}
}
}
lean_object* l_Lean_IR_EmitC_emitNumLit___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = l_Lean_IR_EmitC_emitNumLit(x_5, x_2, x_3, x_4);
lean_dec(x_3);
return x_6;
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
lean_object* l_Lean_IR_EmitC_emitLit(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_EmitC_emitLhs(x_1, x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_6, 0);
lean_dec(x_8);
x_9 = lean_ctor_get(x_3, 0);
lean_inc(x_9);
lean_dec(x_3);
x_10 = lean_box(0);
lean_ctor_set(x_6, 0, x_10);
x_11 = l_Lean_IR_EmitC_emitNumLit(x_2, x_9, x_4, x_6);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_11, 1);
x_14 = lean_ctor_get(x_11, 0);
lean_dec(x_14);
x_15 = l_Lean_IR_formatFnBody___main___closed__3;
x_16 = lean_string_append(x_13, x_15);
x_17 = l_IO_println___rarg___closed__1;
x_18 = lean_string_append(x_16, x_17);
lean_ctor_set(x_11, 1, x_18);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_19 = lean_ctor_get(x_11, 1);
lean_inc(x_19);
lean_dec(x_11);
x_20 = l_Lean_IR_formatFnBody___main___closed__3;
x_21 = lean_string_append(x_19, x_20);
x_22 = l_IO_println___rarg___closed__1;
x_23 = lean_string_append(x_21, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_10);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_11);
if (x_25 == 0)
{
return x_11;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_11, 0);
x_27 = lean_ctor_get(x_11, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_11);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_6, 1);
lean_inc(x_29);
lean_dec(x_6);
x_30 = lean_ctor_get(x_3, 0);
lean_inc(x_30);
lean_dec(x_3);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_29);
x_33 = l_Lean_IR_EmitC_emitNumLit(x_2, x_30, x_4, x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_35 = x_33;
} else {
 lean_dec_ref(x_33);
 x_35 = lean_box(0);
}
x_36 = l_Lean_IR_formatFnBody___main___closed__3;
x_37 = lean_string_append(x_34, x_36);
x_38 = l_IO_println___rarg___closed__1;
x_39 = lean_string_append(x_37, x_38);
if (lean_is_scalar(x_35)) {
 x_40 = lean_alloc_ctor(0, 2, 0);
} else {
 x_40 = x_35;
}
lean_ctor_set(x_40, 0, x_31);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_ctor_get(x_33, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_33, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_43 = x_33;
} else {
 lean_dec_ref(x_33);
 x_43 = lean_box(0);
}
if (lean_is_scalar(x_43)) {
 x_44 = lean_alloc_ctor(1, 2, 0);
} else {
 x_44 = x_43;
}
lean_ctor_set(x_44, 0, x_41);
lean_ctor_set(x_44, 1, x_42);
return x_44;
}
}
}
else
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_6);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_46 = lean_ctor_get(x_6, 1);
x_47 = lean_ctor_get(x_6, 0);
lean_dec(x_47);
x_48 = lean_ctor_get(x_3, 0);
lean_inc(x_48);
lean_dec(x_3);
x_49 = l_Lean_IR_EmitC_emitLit___closed__1;
x_50 = lean_string_append(x_46, x_49);
x_51 = l_Lean_IR_EmitC_quoteString(x_48);
lean_dec(x_48);
x_52 = lean_string_append(x_50, x_51);
lean_dec(x_51);
x_53 = l_Lean_IR_EmitC_emitInc___closed__1;
x_54 = lean_string_append(x_52, x_53);
x_55 = l_IO_println___rarg___closed__1;
x_56 = lean_string_append(x_54, x_55);
x_57 = lean_box(0);
lean_ctor_set(x_6, 1, x_56);
lean_ctor_set(x_6, 0, x_57);
return x_6;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_58 = lean_ctor_get(x_6, 1);
lean_inc(x_58);
lean_dec(x_6);
x_59 = lean_ctor_get(x_3, 0);
lean_inc(x_59);
lean_dec(x_3);
x_60 = l_Lean_IR_EmitC_emitLit___closed__1;
x_61 = lean_string_append(x_58, x_60);
x_62 = l_Lean_IR_EmitC_quoteString(x_59);
lean_dec(x_59);
x_63 = lean_string_append(x_61, x_62);
lean_dec(x_62);
x_64 = l_Lean_IR_EmitC_emitInc___closed__1;
x_65 = lean_string_append(x_63, x_64);
x_66 = l_IO_println___rarg___closed__1;
x_67 = lean_string_append(x_65, x_66);
x_68 = lean_box(0);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_67);
return x_69;
}
}
}
else
{
uint8_t x_70; 
lean_dec(x_3);
x_70 = !lean_is_exclusive(x_6);
if (x_70 == 0)
{
return x_6;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_6, 0);
x_72 = lean_ctor_get(x_6, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_6);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
}
lean_object* l_Lean_IR_EmitC_emitLit___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = l_Lean_IR_EmitC_emitLit(x_1, x_6, x_3, x_4, x_5);
lean_dec(x_4);
return x_7;
}
}
lean_object* l_Lean_IR_EmitC_emitVDecl(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
uint8_t x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get_uint8(x_3, sizeof(void*)*1);
x_37 = lean_ctor_get(x_3, 0);
lean_inc(x_37);
lean_dec(x_3);
x_38 = l_Lean_IR_EmitC_emitBox(x_1, x_37, x_36, x_4, x_5);
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
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = l_Lean_IR_EmitC_emitVDecl(x_1, x_6, x_3, x_4, x_5);
lean_dec(x_4);
return x_7;
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
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = lean_ctor_get(x_5, 0);
lean_dec(x_8);
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_ctor_get(x_6, 0);
x_11 = lean_ctor_get(x_4, 4);
x_12 = lean_name_dec_eq(x_9, x_11);
if (x_12 == 0)
{
uint8_t x_13; lean_object* x_14; 
x_13 = 0;
x_14 = lean_box(x_13);
lean_ctor_set(x_5, 0, x_14);
return x_5;
}
else
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_nat_dec_eq(x_1, x_10);
x_16 = lean_box(x_15);
lean_ctor_set(x_5, 0, x_16);
return x_5;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_17 = lean_ctor_get(x_5, 1);
lean_inc(x_17);
lean_dec(x_5);
x_18 = lean_ctor_get(x_2, 0);
x_19 = lean_ctor_get(x_6, 0);
x_20 = lean_ctor_get(x_4, 4);
x_21 = lean_name_dec_eq(x_18, x_20);
if (x_21 == 0)
{
uint8_t x_22; lean_object* x_23; lean_object* x_24; 
x_22 = 0;
x_23 = lean_box(x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_17);
return x_24;
}
else
{
uint8_t x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_nat_dec_eq(x_1, x_19);
x_26 = lean_box(x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_17);
return x_27;
}
}
}
else
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_5);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_5, 0);
lean_dec(x_29);
x_30 = 0;
x_31 = lean_box(x_30);
lean_ctor_set(x_5, 0, x_31);
return x_5;
}
else
{
lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_5, 1);
lean_inc(x_32);
lean_dec(x_5);
x_33 = 0;
x_34 = lean_box(x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_32);
return x_35;
}
}
}
else
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_5);
if (x_36 == 0)
{
lean_object* x_37; uint8_t x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_5, 0);
lean_dec(x_37);
x_38 = 0;
x_39 = lean_box(x_38);
lean_ctor_set(x_5, 0, x_39);
return x_5;
}
else
{
lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_5, 1);
lean_inc(x_40);
lean_dec(x_5);
x_41 = 0;
x_42 = lean_box(x_41);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_40);
return x_43;
}
}
}
else
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_5);
if (x_44 == 0)
{
lean_object* x_45; uint8_t x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_5, 0);
lean_dec(x_45);
x_46 = 0;
x_47 = lean_box(x_46);
lean_ctor_set(x_5, 0, x_47);
return x_5;
}
else
{
lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; 
x_48 = lean_ctor_get(x_5, 1);
lean_inc(x_48);
lean_dec(x_5);
x_49 = 0;
x_50 = lean_box(x_49);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_48);
return x_51;
}
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
lean_object* l_Nat_mforAux___main___at_Lean_IR_EmitC_emitTailCall___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_13 = l_Lean_IR_paramInh;
x_14 = lean_array_get(x_13, x_2, x_12);
x_15 = l_Lean_IR_Arg_Inhabited;
x_16 = lean_array_get(x_15, x_1, x_12);
lean_dec(x_12);
x_17 = l_Lean_IR_EmitC_paramEqArg(x_14, x_16);
if (x_17 == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_6);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_19 = lean_ctor_get(x_6, 1);
x_20 = lean_ctor_get(x_6, 0);
lean_dec(x_20);
x_21 = lean_ctor_get(x_14, 0);
lean_inc(x_21);
lean_dec(x_14);
x_22 = l_Nat_repr(x_21);
x_23 = l_Lean_IR_VarId_HasToString___closed__1;
x_24 = lean_string_append(x_23, x_22);
lean_dec(x_22);
x_25 = lean_string_append(x_19, x_24);
lean_dec(x_24);
x_26 = l_Nat_mforAux___main___at_Lean_IR_EmitC_emitJmp___spec__1___closed__1;
x_27 = lean_string_append(x_25, x_26);
x_28 = lean_box(0);
lean_ctor_set(x_6, 1, x_27);
lean_ctor_set(x_6, 0, x_28);
x_29 = l_Lean_IR_EmitC_emitArg(x_16, x_5, x_6);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_31 = lean_ctor_get(x_29, 1);
x_32 = lean_ctor_get(x_29, 0);
lean_dec(x_32);
x_33 = l_Lean_IR_formatFnBody___main___closed__3;
x_34 = lean_string_append(x_31, x_33);
x_35 = l_IO_println___rarg___closed__1;
x_36 = lean_string_append(x_34, x_35);
lean_ctor_set(x_29, 1, x_36);
lean_ctor_set(x_29, 0, x_28);
x_4 = x_10;
x_6 = x_29;
goto _start;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_38 = lean_ctor_get(x_29, 1);
lean_inc(x_38);
lean_dec(x_29);
x_39 = l_Lean_IR_formatFnBody___main___closed__3;
x_40 = lean_string_append(x_38, x_39);
x_41 = l_IO_println___rarg___closed__1;
x_42 = lean_string_append(x_40, x_41);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_28);
lean_ctor_set(x_43, 1, x_42);
x_4 = x_10;
x_6 = x_43;
goto _start;
}
}
else
{
uint8_t x_45; 
lean_dec(x_10);
x_45 = !lean_is_exclusive(x_29);
if (x_45 == 0)
{
return x_29;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_29, 0);
x_47 = lean_ctor_get(x_29, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_29);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_49 = lean_ctor_get(x_6, 1);
lean_inc(x_49);
lean_dec(x_6);
x_50 = lean_ctor_get(x_14, 0);
lean_inc(x_50);
lean_dec(x_14);
x_51 = l_Nat_repr(x_50);
x_52 = l_Lean_IR_VarId_HasToString___closed__1;
x_53 = lean_string_append(x_52, x_51);
lean_dec(x_51);
x_54 = lean_string_append(x_49, x_53);
lean_dec(x_53);
x_55 = l_Nat_mforAux___main___at_Lean_IR_EmitC_emitJmp___spec__1___closed__1;
x_56 = lean_string_append(x_54, x_55);
x_57 = lean_box(0);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_56);
x_59 = l_Lean_IR_EmitC_emitArg(x_16, x_5, x_58);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_60 = lean_ctor_get(x_59, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_61 = x_59;
} else {
 lean_dec_ref(x_59);
 x_61 = lean_box(0);
}
x_62 = l_Lean_IR_formatFnBody___main___closed__3;
x_63 = lean_string_append(x_60, x_62);
x_64 = l_IO_println___rarg___closed__1;
x_65 = lean_string_append(x_63, x_64);
if (lean_is_scalar(x_61)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_61;
}
lean_ctor_set(x_66, 0, x_57);
lean_ctor_set(x_66, 1, x_65);
x_4 = x_10;
x_6 = x_66;
goto _start;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_10);
x_68 = lean_ctor_get(x_59, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_59, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_70 = x_59;
} else {
 lean_dec_ref(x_59);
 x_70 = lean_box(0);
}
if (lean_is_scalar(x_70)) {
 x_71 = lean_alloc_ctor(1, 2, 0);
} else {
 x_71 = x_70;
}
lean_ctor_set(x_71, 0, x_68);
lean_ctor_set(x_71, 1, x_69);
return x_71;
}
}
}
else
{
uint8_t x_72; 
lean_dec(x_16);
lean_dec(x_14);
x_72 = !lean_is_exclusive(x_6);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_ctor_get(x_6, 0);
lean_dec(x_73);
x_74 = lean_box(0);
lean_ctor_set(x_6, 0, x_74);
x_4 = x_10;
goto _start;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_6, 1);
lean_inc(x_76);
lean_dec(x_6);
x_77 = lean_box(0);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_76);
x_4 = x_10;
x_6 = x_78;
goto _start;
}
}
}
else
{
uint8_t x_80; 
lean_dec(x_4);
x_80 = !lean_is_exclusive(x_6);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_6, 0);
lean_dec(x_81);
x_82 = lean_box(0);
lean_ctor_set(x_6, 0, x_82);
return x_6;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_6, 1);
lean_inc(x_83);
lean_dec(x_6);
x_84 = lean_box(0);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_83);
return x_85;
}
}
}
}
lean_object* _init_l_Nat_mforAux___main___at_Lean_IR_EmitC_emitTailCall___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" _tmp_");
return x_1;
}
}
lean_object* l_Nat_mforAux___main___at_Lean_IR_EmitC_emitTailCall___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_13 = l_Lean_IR_paramInh;
x_14 = lean_array_get(x_13, x_2, x_12);
x_15 = l_Lean_IR_Arg_Inhabited;
x_16 = lean_array_get(x_15, x_1, x_12);
x_17 = l_Lean_IR_EmitC_paramEqArg(x_14, x_16);
if (x_17 == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_6);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_19 = lean_ctor_get(x_6, 1);
x_20 = lean_ctor_get(x_6, 0);
lean_dec(x_20);
x_21 = lean_ctor_get_uint8(x_14, sizeof(void*)*1 + 1);
lean_dec(x_14);
x_22 = l_Lean_IR_EmitC_toCType(x_21);
x_23 = lean_string_append(x_19, x_22);
lean_dec(x_22);
x_24 = l_Nat_mforAux___main___at_Lean_IR_EmitC_emitTailCall___spec__2___closed__1;
x_25 = lean_string_append(x_23, x_24);
x_26 = l_Nat_repr(x_12);
x_27 = lean_string_append(x_25, x_26);
lean_dec(x_26);
x_28 = l_Nat_mforAux___main___at_Lean_IR_EmitC_emitJmp___spec__1___closed__1;
x_29 = lean_string_append(x_27, x_28);
x_30 = lean_box(0);
lean_ctor_set(x_6, 1, x_29);
lean_ctor_set(x_6, 0, x_30);
x_31 = l_Lean_IR_EmitC_emitArg(x_16, x_5, x_6);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_33 = lean_ctor_get(x_31, 1);
x_34 = lean_ctor_get(x_31, 0);
lean_dec(x_34);
x_35 = l_Lean_IR_formatFnBody___main___closed__3;
x_36 = lean_string_append(x_33, x_35);
x_37 = l_IO_println___rarg___closed__1;
x_38 = lean_string_append(x_36, x_37);
lean_ctor_set(x_31, 1, x_38);
lean_ctor_set(x_31, 0, x_30);
x_4 = x_10;
x_6 = x_31;
goto _start;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_40 = lean_ctor_get(x_31, 1);
lean_inc(x_40);
lean_dec(x_31);
x_41 = l_Lean_IR_formatFnBody___main___closed__3;
x_42 = lean_string_append(x_40, x_41);
x_43 = l_IO_println___rarg___closed__1;
x_44 = lean_string_append(x_42, x_43);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_30);
lean_ctor_set(x_45, 1, x_44);
x_4 = x_10;
x_6 = x_45;
goto _start;
}
}
else
{
uint8_t x_47; 
lean_dec(x_10);
x_47 = !lean_is_exclusive(x_31);
if (x_47 == 0)
{
return x_31;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_31, 0);
x_49 = lean_ctor_get(x_31, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_31);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
else
{
lean_object* x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_51 = lean_ctor_get(x_6, 1);
lean_inc(x_51);
lean_dec(x_6);
x_52 = lean_ctor_get_uint8(x_14, sizeof(void*)*1 + 1);
lean_dec(x_14);
x_53 = l_Lean_IR_EmitC_toCType(x_52);
x_54 = lean_string_append(x_51, x_53);
lean_dec(x_53);
x_55 = l_Nat_mforAux___main___at_Lean_IR_EmitC_emitTailCall___spec__2___closed__1;
x_56 = lean_string_append(x_54, x_55);
x_57 = l_Nat_repr(x_12);
x_58 = lean_string_append(x_56, x_57);
lean_dec(x_57);
x_59 = l_Nat_mforAux___main___at_Lean_IR_EmitC_emitJmp___spec__1___closed__1;
x_60 = lean_string_append(x_58, x_59);
x_61 = lean_box(0);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_60);
x_63 = l_Lean_IR_EmitC_emitArg(x_16, x_5, x_62);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_65 = x_63;
} else {
 lean_dec_ref(x_63);
 x_65 = lean_box(0);
}
x_66 = l_Lean_IR_formatFnBody___main___closed__3;
x_67 = lean_string_append(x_64, x_66);
x_68 = l_IO_println___rarg___closed__1;
x_69 = lean_string_append(x_67, x_68);
if (lean_is_scalar(x_65)) {
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_65;
}
lean_ctor_set(x_70, 0, x_61);
lean_ctor_set(x_70, 1, x_69);
x_4 = x_10;
x_6 = x_70;
goto _start;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_10);
x_72 = lean_ctor_get(x_63, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_63, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_74 = x_63;
} else {
 lean_dec_ref(x_63);
 x_74 = lean_box(0);
}
if (lean_is_scalar(x_74)) {
 x_75 = lean_alloc_ctor(1, 2, 0);
} else {
 x_75 = x_74;
}
lean_ctor_set(x_75, 0, x_72);
lean_ctor_set(x_75, 1, x_73);
return x_75;
}
}
}
else
{
uint8_t x_76; 
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_12);
x_76 = !lean_is_exclusive(x_6);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_6, 0);
lean_dec(x_77);
x_78 = lean_box(0);
lean_ctor_set(x_6, 0, x_78);
x_4 = x_10;
goto _start;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_6, 1);
lean_inc(x_80);
lean_dec(x_6);
x_81 = lean_box(0);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_80);
x_4 = x_10;
x_6 = x_82;
goto _start;
}
}
}
else
{
uint8_t x_84; 
lean_dec(x_4);
x_84 = !lean_is_exclusive(x_6);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; 
x_85 = lean_ctor_get(x_6, 0);
lean_dec(x_85);
x_86 = lean_box(0);
lean_ctor_set(x_6, 0, x_86);
return x_6;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_6, 1);
lean_inc(x_87);
lean_dec(x_6);
x_88 = lean_box(0);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_87);
return x_89;
}
}
}
}
lean_object* _init_l_Nat_mforAux___main___at_Lean_IR_EmitC_emitTailCall___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" = _tmp_");
return x_1;
}
}
lean_object* l_Nat_mforAux___main___at_Lean_IR_EmitC_emitTailCall___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_13 = l_Lean_IR_paramInh;
x_14 = lean_array_get(x_13, x_2, x_12);
x_15 = l_Lean_IR_Arg_Inhabited;
x_16 = lean_array_get(x_15, x_1, x_12);
x_17 = l_Lean_IR_EmitC_paramEqArg(x_14, x_16);
lean_dec(x_16);
if (x_17 == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_6);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_19 = lean_ctor_get(x_6, 1);
x_20 = lean_ctor_get(x_6, 0);
lean_dec(x_20);
x_21 = lean_ctor_get(x_14, 0);
lean_inc(x_21);
lean_dec(x_14);
x_22 = l_Nat_repr(x_21);
x_23 = l_Lean_IR_VarId_HasToString___closed__1;
x_24 = lean_string_append(x_23, x_22);
lean_dec(x_22);
x_25 = lean_string_append(x_19, x_24);
lean_dec(x_24);
x_26 = l_Nat_mforAux___main___at_Lean_IR_EmitC_emitTailCall___spec__3___closed__1;
x_27 = lean_string_append(x_25, x_26);
x_28 = l_Nat_repr(x_12);
x_29 = lean_string_append(x_27, x_28);
lean_dec(x_28);
x_30 = l_Lean_IR_formatFnBody___main___closed__3;
x_31 = lean_string_append(x_29, x_30);
x_32 = l_IO_println___rarg___closed__1;
x_33 = lean_string_append(x_31, x_32);
x_34 = lean_box(0);
lean_ctor_set(x_6, 1, x_33);
lean_ctor_set(x_6, 0, x_34);
x_4 = x_10;
goto _start;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_36 = lean_ctor_get(x_6, 1);
lean_inc(x_36);
lean_dec(x_6);
x_37 = lean_ctor_get(x_14, 0);
lean_inc(x_37);
lean_dec(x_14);
x_38 = l_Nat_repr(x_37);
x_39 = l_Lean_IR_VarId_HasToString___closed__1;
x_40 = lean_string_append(x_39, x_38);
lean_dec(x_38);
x_41 = lean_string_append(x_36, x_40);
lean_dec(x_40);
x_42 = l_Nat_mforAux___main___at_Lean_IR_EmitC_emitTailCall___spec__3___closed__1;
x_43 = lean_string_append(x_41, x_42);
x_44 = l_Nat_repr(x_12);
x_45 = lean_string_append(x_43, x_44);
lean_dec(x_44);
x_46 = l_Lean_IR_formatFnBody___main___closed__3;
x_47 = lean_string_append(x_45, x_46);
x_48 = l_IO_println___rarg___closed__1;
x_49 = lean_string_append(x_47, x_48);
x_50 = lean_box(0);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_49);
x_4 = x_10;
x_6 = x_51;
goto _start;
}
}
else
{
uint8_t x_53; 
lean_dec(x_14);
lean_dec(x_12);
x_53 = !lean_is_exclusive(x_6);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_6, 0);
lean_dec(x_54);
x_55 = lean_box(0);
lean_ctor_set(x_6, 0, x_55);
x_4 = x_10;
goto _start;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_6, 1);
lean_inc(x_57);
lean_dec(x_6);
x_58 = lean_box(0);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_57);
x_4 = x_10;
x_6 = x_59;
goto _start;
}
}
}
else
{
uint8_t x_61; 
lean_dec(x_4);
x_61 = !lean_is_exclusive(x_6);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_6, 0);
lean_dec(x_62);
x_63 = lean_box(0);
lean_ctor_set(x_6, 0, x_63);
return x_6;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_6, 1);
lean_inc(x_64);
lean_dec(x_6);
x_65 = lean_box(0);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_64);
return x_66;
}
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
lean_object* _init_l_Lean_IR_EmitC_emitTailCall___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("{");
return x_1;
}
}
lean_object* l_Lean_IR_EmitC_emitTailCall(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
if (lean_obj_tag(x_1) == 6)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_3);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_13 = lean_ctor_get(x_1, 1);
x_14 = lean_ctor_get(x_3, 1);
x_15 = lean_ctor_get(x_3, 0);
lean_dec(x_15);
x_16 = lean_ctor_get(x_2, 5);
x_17 = lean_array_get_size(x_16);
x_18 = lean_array_get_size(x_13);
x_19 = lean_nat_dec_eq(x_17, x_18);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_18);
lean_dec(x_17);
x_20 = l_Lean_IR_EmitC_emitTailCall___closed__2;
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 0, x_20);
return x_3;
}
else
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_box(0);
lean_inc(x_14);
lean_ctor_set(x_3, 0, x_21);
x_22 = l_Lean_IR_EmitC_overwriteParam(x_16, x_13);
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec(x_17);
lean_dec(x_14);
lean_inc(x_18);
x_23 = l_Nat_mforAux___main___at_Lean_IR_EmitC_emitTailCall___spec__1(x_13, x_16, x_18, x_18, x_2, x_3);
lean_dec(x_18);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_25 = lean_ctor_get(x_23, 1);
x_26 = lean_ctor_get(x_23, 0);
lean_dec(x_26);
x_27 = l_Lean_IR_EmitC_emitTailCall___closed__3;
x_28 = lean_string_append(x_25, x_27);
x_29 = l_IO_println___rarg___closed__1;
x_30 = lean_string_append(x_28, x_29);
lean_ctor_set(x_23, 1, x_30);
lean_ctor_set(x_23, 0, x_21);
return x_23;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_31 = lean_ctor_get(x_23, 1);
lean_inc(x_31);
lean_dec(x_23);
x_32 = l_Lean_IR_EmitC_emitTailCall___closed__3;
x_33 = lean_string_append(x_31, x_32);
x_34 = l_IO_println___rarg___closed__1;
x_35 = lean_string_append(x_33, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_21);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
else
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_23);
if (x_37 == 0)
{
return x_23;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_23, 0);
x_39 = lean_ctor_get(x_23, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_23);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_3);
lean_dec(x_18);
x_41 = l_Lean_IR_EmitC_emitTailCall___closed__4;
x_42 = lean_string_append(x_14, x_41);
x_43 = l_IO_println___rarg___closed__1;
x_44 = lean_string_append(x_42, x_43);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_21);
lean_ctor_set(x_45, 1, x_44);
lean_inc(x_17);
x_46 = l_Nat_mforAux___main___at_Lean_IR_EmitC_emitTailCall___spec__2(x_13, x_16, x_17, x_17, x_2, x_45);
if (lean_obj_tag(x_46) == 0)
{
uint8_t x_47; 
x_47 = !lean_is_exclusive(x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_46, 0);
lean_dec(x_48);
lean_ctor_set(x_46, 0, x_21);
lean_inc(x_17);
x_49 = l_Nat_mforAux___main___at_Lean_IR_EmitC_emitTailCall___spec__3(x_13, x_16, x_17, x_17, x_2, x_46);
lean_dec(x_17);
if (lean_obj_tag(x_49) == 0)
{
uint8_t x_50; 
x_50 = !lean_is_exclusive(x_49);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_51 = lean_ctor_get(x_49, 1);
x_52 = lean_ctor_get(x_49, 0);
lean_dec(x_52);
x_53 = l_PersistentHashMap_Stats_toString___closed__5;
x_54 = lean_string_append(x_51, x_53);
x_55 = lean_string_append(x_54, x_43);
x_56 = l_Lean_IR_EmitC_emitTailCall___closed__3;
x_57 = lean_string_append(x_55, x_56);
x_58 = lean_string_append(x_57, x_43);
lean_ctor_set(x_49, 1, x_58);
lean_ctor_set(x_49, 0, x_21);
return x_49;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_59 = lean_ctor_get(x_49, 1);
lean_inc(x_59);
lean_dec(x_49);
x_60 = l_PersistentHashMap_Stats_toString___closed__5;
x_61 = lean_string_append(x_59, x_60);
x_62 = lean_string_append(x_61, x_43);
x_63 = l_Lean_IR_EmitC_emitTailCall___closed__3;
x_64 = lean_string_append(x_62, x_63);
x_65 = lean_string_append(x_64, x_43);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_21);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
else
{
uint8_t x_67; 
x_67 = !lean_is_exclusive(x_49);
if (x_67 == 0)
{
return x_49;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_49, 0);
x_69 = lean_ctor_get(x_49, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_49);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_46, 1);
lean_inc(x_71);
lean_dec(x_46);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_21);
lean_ctor_set(x_72, 1, x_71);
lean_inc(x_17);
x_73 = l_Nat_mforAux___main___at_Lean_IR_EmitC_emitTailCall___spec__3(x_13, x_16, x_17, x_17, x_2, x_72);
lean_dec(x_17);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_74 = lean_ctor_get(x_73, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_75 = x_73;
} else {
 lean_dec_ref(x_73);
 x_75 = lean_box(0);
}
x_76 = l_PersistentHashMap_Stats_toString___closed__5;
x_77 = lean_string_append(x_74, x_76);
x_78 = lean_string_append(x_77, x_43);
x_79 = l_Lean_IR_EmitC_emitTailCall___closed__3;
x_80 = lean_string_append(x_78, x_79);
x_81 = lean_string_append(x_80, x_43);
if (lean_is_scalar(x_75)) {
 x_82 = lean_alloc_ctor(0, 2, 0);
} else {
 x_82 = x_75;
}
lean_ctor_set(x_82, 0, x_21);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_83 = lean_ctor_get(x_73, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_73, 1);
lean_inc(x_84);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_85 = x_73;
} else {
 lean_dec_ref(x_73);
 x_85 = lean_box(0);
}
if (lean_is_scalar(x_85)) {
 x_86 = lean_alloc_ctor(1, 2, 0);
} else {
 x_86 = x_85;
}
lean_ctor_set(x_86, 0, x_83);
lean_ctor_set(x_86, 1, x_84);
return x_86;
}
}
}
else
{
uint8_t x_87; 
lean_dec(x_17);
x_87 = !lean_is_exclusive(x_46);
if (x_87 == 0)
{
return x_46;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_46, 0);
x_89 = lean_ctor_get(x_46, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_46);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
}
}
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; 
x_91 = lean_ctor_get(x_1, 1);
x_92 = lean_ctor_get(x_3, 1);
lean_inc(x_92);
lean_dec(x_3);
x_93 = lean_ctor_get(x_2, 5);
x_94 = lean_array_get_size(x_93);
x_95 = lean_array_get_size(x_91);
x_96 = lean_nat_dec_eq(x_94, x_95);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; 
lean_dec(x_95);
lean_dec(x_94);
x_97 = l_Lean_IR_EmitC_emitTailCall___closed__2;
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_92);
return x_98;
}
else
{
lean_object* x_99; lean_object* x_100; uint8_t x_101; 
x_99 = lean_box(0);
lean_inc(x_92);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_92);
x_101 = l_Lean_IR_EmitC_overwriteParam(x_93, x_91);
if (x_101 == 0)
{
lean_object* x_102; 
lean_dec(x_94);
lean_dec(x_92);
lean_inc(x_95);
x_102 = l_Nat_mforAux___main___at_Lean_IR_EmitC_emitTailCall___spec__1(x_91, x_93, x_95, x_95, x_2, x_100);
lean_dec(x_95);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_103 = lean_ctor_get(x_102, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 lean_ctor_release(x_102, 1);
 x_104 = x_102;
} else {
 lean_dec_ref(x_102);
 x_104 = lean_box(0);
}
x_105 = l_Lean_IR_EmitC_emitTailCall___closed__3;
x_106 = lean_string_append(x_103, x_105);
x_107 = l_IO_println___rarg___closed__1;
x_108 = lean_string_append(x_106, x_107);
if (lean_is_scalar(x_104)) {
 x_109 = lean_alloc_ctor(0, 2, 0);
} else {
 x_109 = x_104;
}
lean_ctor_set(x_109, 0, x_99);
lean_ctor_set(x_109, 1, x_108);
return x_109;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_110 = lean_ctor_get(x_102, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_102, 1);
lean_inc(x_111);
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 lean_ctor_release(x_102, 1);
 x_112 = x_102;
} else {
 lean_dec_ref(x_102);
 x_112 = lean_box(0);
}
if (lean_is_scalar(x_112)) {
 x_113 = lean_alloc_ctor(1, 2, 0);
} else {
 x_113 = x_112;
}
lean_ctor_set(x_113, 0, x_110);
lean_ctor_set(x_113, 1, x_111);
return x_113;
}
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
lean_dec(x_100);
lean_dec(x_95);
x_114 = l_Lean_IR_EmitC_emitTailCall___closed__4;
x_115 = lean_string_append(x_92, x_114);
x_116 = l_IO_println___rarg___closed__1;
x_117 = lean_string_append(x_115, x_116);
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_99);
lean_ctor_set(x_118, 1, x_117);
lean_inc(x_94);
x_119 = l_Nat_mforAux___main___at_Lean_IR_EmitC_emitTailCall___spec__2(x_91, x_93, x_94, x_94, x_2, x_118);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
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
if (lean_is_scalar(x_121)) {
 x_122 = lean_alloc_ctor(0, 2, 0);
} else {
 x_122 = x_121;
}
lean_ctor_set(x_122, 0, x_99);
lean_ctor_set(x_122, 1, x_120);
lean_inc(x_94);
x_123 = l_Nat_mforAux___main___at_Lean_IR_EmitC_emitTailCall___spec__3(x_91, x_93, x_94, x_94, x_2, x_122);
lean_dec(x_94);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_124 = lean_ctor_get(x_123, 1);
lean_inc(x_124);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 lean_ctor_release(x_123, 1);
 x_125 = x_123;
} else {
 lean_dec_ref(x_123);
 x_125 = lean_box(0);
}
x_126 = l_PersistentHashMap_Stats_toString___closed__5;
x_127 = lean_string_append(x_124, x_126);
x_128 = lean_string_append(x_127, x_116);
x_129 = l_Lean_IR_EmitC_emitTailCall___closed__3;
x_130 = lean_string_append(x_128, x_129);
x_131 = lean_string_append(x_130, x_116);
if (lean_is_scalar(x_125)) {
 x_132 = lean_alloc_ctor(0, 2, 0);
} else {
 x_132 = x_125;
}
lean_ctor_set(x_132, 0, x_99);
lean_ctor_set(x_132, 1, x_131);
return x_132;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_133 = lean_ctor_get(x_123, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_123, 1);
lean_inc(x_134);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 lean_ctor_release(x_123, 1);
 x_135 = x_123;
} else {
 lean_dec_ref(x_123);
 x_135 = lean_box(0);
}
if (lean_is_scalar(x_135)) {
 x_136 = lean_alloc_ctor(1, 2, 0);
} else {
 x_136 = x_135;
}
lean_ctor_set(x_136, 0, x_133);
lean_ctor_set(x_136, 1, x_134);
return x_136;
}
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
lean_dec(x_94);
x_137 = lean_ctor_get(x_119, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_119, 1);
lean_inc(x_138);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 x_139 = x_119;
} else {
 lean_dec_ref(x_119);
 x_139 = lean_box(0);
}
if (lean_is_scalar(x_139)) {
 x_140 = lean_alloc_ctor(1, 2, 0);
} else {
 x_140 = x_139;
}
lean_ctor_set(x_140, 0, x_137);
lean_ctor_set(x_140, 1, x_138);
return x_140;
}
}
}
}
}
else
{
lean_object* x_141; 
x_141 = lean_box(0);
x_4 = x_141;
goto block_11;
}
block_11:
{
uint8_t x_5; 
lean_dec(x_4);
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_3, 0);
lean_dec(x_6);
x_7 = l_Lean_IR_EmitC_emitTailCall___closed__1;
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 0, x_7);
return x_3;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_dec(x_3);
x_9 = l_Lean_IR_EmitC_emitTailCall___closed__1;
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
}
}
}
lean_object* l_Nat_mforAux___main___at_Lean_IR_EmitC_emitTailCall___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Nat_mforAux___main___at_Lean_IR_EmitC_emitTailCall___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Nat_mforAux___main___at_Lean_IR_EmitC_emitTailCall___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Nat_mforAux___main___at_Lean_IR_EmitC_emitTailCall___spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Nat_mforAux___main___at_Lean_IR_EmitC_emitTailCall___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Nat_mforAux___main___at_Lean_IR_EmitC_emitTailCall___spec__3(x_1, x_2, x_3, x_4, x_5, x_6);
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
lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 2);
lean_inc(x_8);
x_9 = !lean_is_exclusive(x_4);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_4, 0);
lean_dec(x_10);
x_11 = lean_box(0);
lean_ctor_set(x_4, 0, x_11);
x_12 = lean_ctor_get(x_3, 4);
lean_inc(x_12);
x_13 = l_Lean_IR_isTailCallTo(x_12, x_2);
lean_dec(x_2);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = l_Lean_IR_EmitC_emitVDecl(x_5, x_6, x_7, x_3, x_4);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_14, 0);
lean_dec(x_16);
lean_ctor_set(x_14, 0, x_11);
x_2 = x_8;
x_4 = x_14;
goto _start;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_14, 1);
lean_inc(x_18);
lean_dec(x_14);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_11);
lean_ctor_set(x_19, 1, x_18);
x_2 = x_8;
x_4 = x_19;
goto _start;
}
}
else
{
uint8_t x_21; 
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_14);
if (x_21 == 0)
{
return x_14;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_14, 0);
x_23 = lean_ctor_get(x_14, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_14);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
else
{
lean_object* x_25; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_1);
x_25 = l_Lean_IR_EmitC_emitTailCall(x_7, x_3, x_4);
lean_dec(x_3);
lean_dec(x_7);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_26 = lean_ctor_get(x_4, 1);
lean_inc(x_26);
lean_dec(x_4);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
x_29 = lean_ctor_get(x_3, 4);
lean_inc(x_29);
x_30 = l_Lean_IR_isTailCallTo(x_29, x_2);
lean_dec(x_2);
lean_dec(x_29);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = l_Lean_IR_EmitC_emitVDecl(x_5, x_6, x_7, x_3, x_28);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_33 = x_31;
} else {
 lean_dec_ref(x_31);
 x_33 = lean_box(0);
}
if (lean_is_scalar(x_33)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_33;
}
lean_ctor_set(x_34, 0, x_27);
lean_ctor_set(x_34, 1, x_32);
x_2 = x_8;
x_4 = x_34;
goto _start;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_1);
x_36 = lean_ctor_get(x_31, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_31, 1);
lean_inc(x_37);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_38 = x_31;
} else {
 lean_dec_ref(x_31);
 x_38 = lean_box(0);
}
if (lean_is_scalar(x_38)) {
 x_39 = lean_alloc_ctor(1, 2, 0);
} else {
 x_39 = x_38;
}
lean_ctor_set(x_39, 0, x_36);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
}
else
{
lean_object* x_40; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_1);
x_40 = l_Lean_IR_EmitC_emitTailCall(x_7, x_3, x_28);
lean_dec(x_3);
lean_dec(x_7);
return x_40;
}
}
}
case 1:
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_2, 3);
lean_inc(x_41);
lean_dec(x_2);
x_2 = x_41;
goto _start;
}
case 2:
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_43 = lean_ctor_get(x_2, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_2, 1);
lean_inc(x_44);
x_45 = lean_ctor_get(x_2, 2);
lean_inc(x_45);
x_46 = lean_ctor_get(x_2, 3);
lean_inc(x_46);
lean_dec(x_2);
x_47 = l_Lean_IR_EmitC_emitSet(x_43, x_44, x_45, x_3, x_4);
if (lean_obj_tag(x_47) == 0)
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_47, 0);
lean_dec(x_49);
x_50 = lean_box(0);
lean_ctor_set(x_47, 0, x_50);
x_2 = x_46;
x_4 = x_47;
goto _start;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_47, 1);
lean_inc(x_52);
lean_dec(x_47);
x_53 = lean_box(0);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_52);
x_2 = x_46;
x_4 = x_54;
goto _start;
}
}
else
{
uint8_t x_56; 
lean_dec(x_46);
lean_dec(x_3);
lean_dec(x_1);
x_56 = !lean_is_exclusive(x_47);
if (x_56 == 0)
{
return x_47;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_47, 0);
x_58 = lean_ctor_get(x_47, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_47);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
case 3:
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_60 = lean_ctor_get(x_2, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_2, 1);
lean_inc(x_61);
x_62 = lean_ctor_get(x_2, 2);
lean_inc(x_62);
lean_dec(x_2);
x_63 = l_Lean_IR_EmitC_emitSetTag(x_60, x_61, x_3, x_4);
if (lean_obj_tag(x_63) == 0)
{
uint8_t x_64; 
x_64 = !lean_is_exclusive(x_63);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_63, 0);
lean_dec(x_65);
x_66 = lean_box(0);
lean_ctor_set(x_63, 0, x_66);
x_2 = x_62;
x_4 = x_63;
goto _start;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_63, 1);
lean_inc(x_68);
lean_dec(x_63);
x_69 = lean_box(0);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_68);
x_2 = x_62;
x_4 = x_70;
goto _start;
}
}
else
{
uint8_t x_72; 
lean_dec(x_62);
lean_dec(x_3);
lean_dec(x_1);
x_72 = !lean_is_exclusive(x_63);
if (x_72 == 0)
{
return x_63;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_63, 0);
x_74 = lean_ctor_get(x_63, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_63);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
case 4:
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_76 = lean_ctor_get(x_2, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_2, 1);
lean_inc(x_77);
x_78 = lean_ctor_get(x_2, 2);
lean_inc(x_78);
x_79 = lean_ctor_get(x_2, 3);
lean_inc(x_79);
lean_dec(x_2);
x_80 = l_Lean_IR_EmitC_emitUSet(x_76, x_77, x_78, x_3, x_4);
if (lean_obj_tag(x_80) == 0)
{
uint8_t x_81; 
x_81 = !lean_is_exclusive(x_80);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_ctor_get(x_80, 0);
lean_dec(x_82);
x_83 = lean_box(0);
lean_ctor_set(x_80, 0, x_83);
x_2 = x_79;
x_4 = x_80;
goto _start;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_80, 1);
lean_inc(x_85);
lean_dec(x_80);
x_86 = lean_box(0);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_85);
x_2 = x_79;
x_4 = x_87;
goto _start;
}
}
else
{
uint8_t x_89; 
lean_dec(x_79);
lean_dec(x_3);
lean_dec(x_1);
x_89 = !lean_is_exclusive(x_80);
if (x_89 == 0)
{
return x_80;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_80, 0);
x_91 = lean_ctor_get(x_80, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_80);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
}
}
case 5:
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; lean_object* x_98; lean_object* x_99; 
x_93 = lean_ctor_get(x_2, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_2, 1);
lean_inc(x_94);
x_95 = lean_ctor_get(x_2, 2);
lean_inc(x_95);
x_96 = lean_ctor_get(x_2, 3);
lean_inc(x_96);
x_97 = lean_ctor_get_uint8(x_2, sizeof(void*)*5);
x_98 = lean_ctor_get(x_2, 4);
lean_inc(x_98);
lean_dec(x_2);
x_99 = l_Lean_IR_EmitC_emitSSet(x_93, x_94, x_95, x_96, x_97, x_3, x_4);
if (lean_obj_tag(x_99) == 0)
{
uint8_t x_100; 
x_100 = !lean_is_exclusive(x_99);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; 
x_101 = lean_ctor_get(x_99, 0);
lean_dec(x_101);
x_102 = lean_box(0);
lean_ctor_set(x_99, 0, x_102);
x_2 = x_98;
x_4 = x_99;
goto _start;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_99, 1);
lean_inc(x_104);
lean_dec(x_99);
x_105 = lean_box(0);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_104);
x_2 = x_98;
x_4 = x_106;
goto _start;
}
}
else
{
uint8_t x_108; 
lean_dec(x_98);
lean_dec(x_3);
lean_dec(x_1);
x_108 = !lean_is_exclusive(x_99);
if (x_108 == 0)
{
return x_99;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_99, 0);
x_110 = lean_ctor_get(x_99, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_99);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
return x_111;
}
}
}
case 6:
{
lean_object* x_112; lean_object* x_113; uint8_t x_114; lean_object* x_115; lean_object* x_116; 
x_112 = lean_ctor_get(x_2, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_2, 1);
lean_inc(x_113);
x_114 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_115 = lean_ctor_get(x_2, 2);
lean_inc(x_115);
lean_dec(x_2);
x_116 = l_Lean_IR_EmitC_emitInc(x_112, x_113, x_114, x_3, x_4);
if (lean_obj_tag(x_116) == 0)
{
uint8_t x_117; 
x_117 = !lean_is_exclusive(x_116);
if (x_117 == 0)
{
lean_object* x_118; lean_object* x_119; 
x_118 = lean_ctor_get(x_116, 0);
lean_dec(x_118);
x_119 = lean_box(0);
lean_ctor_set(x_116, 0, x_119);
x_2 = x_115;
x_4 = x_116;
goto _start;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_116, 1);
lean_inc(x_121);
lean_dec(x_116);
x_122 = lean_box(0);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_121);
x_2 = x_115;
x_4 = x_123;
goto _start;
}
}
else
{
uint8_t x_125; 
lean_dec(x_115);
lean_dec(x_3);
lean_dec(x_1);
x_125 = !lean_is_exclusive(x_116);
if (x_125 == 0)
{
return x_116;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_126 = lean_ctor_get(x_116, 0);
x_127 = lean_ctor_get(x_116, 1);
lean_inc(x_127);
lean_inc(x_126);
lean_dec(x_116);
x_128 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_127);
return x_128;
}
}
}
case 7:
{
lean_object* x_129; lean_object* x_130; uint8_t x_131; lean_object* x_132; lean_object* x_133; 
x_129 = lean_ctor_get(x_2, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_2, 1);
lean_inc(x_130);
x_131 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_132 = lean_ctor_get(x_2, 2);
lean_inc(x_132);
lean_dec(x_2);
x_133 = l_Lean_IR_EmitC_emitDec(x_129, x_130, x_131, x_3, x_4);
if (lean_obj_tag(x_133) == 0)
{
uint8_t x_134; 
x_134 = !lean_is_exclusive(x_133);
if (x_134 == 0)
{
lean_object* x_135; lean_object* x_136; 
x_135 = lean_ctor_get(x_133, 0);
lean_dec(x_135);
x_136 = lean_box(0);
lean_ctor_set(x_133, 0, x_136);
x_2 = x_132;
x_4 = x_133;
goto _start;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_138 = lean_ctor_get(x_133, 1);
lean_inc(x_138);
lean_dec(x_133);
x_139 = lean_box(0);
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_138);
x_2 = x_132;
x_4 = x_140;
goto _start;
}
}
else
{
uint8_t x_142; 
lean_dec(x_132);
lean_dec(x_3);
lean_dec(x_1);
x_142 = !lean_is_exclusive(x_133);
if (x_142 == 0)
{
return x_133;
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_143 = lean_ctor_get(x_133, 0);
x_144 = lean_ctor_get(x_133, 1);
lean_inc(x_144);
lean_inc(x_143);
lean_dec(x_133);
x_145 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_145, 0, x_143);
lean_ctor_set(x_145, 1, x_144);
return x_145;
}
}
}
case 8:
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_146 = lean_ctor_get(x_2, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_2, 1);
lean_inc(x_147);
lean_dec(x_2);
x_148 = l_Lean_IR_EmitC_emitDel(x_146, x_3, x_4);
if (lean_obj_tag(x_148) == 0)
{
uint8_t x_149; 
x_149 = !lean_is_exclusive(x_148);
if (x_149 == 0)
{
lean_object* x_150; lean_object* x_151; 
x_150 = lean_ctor_get(x_148, 0);
lean_dec(x_150);
x_151 = lean_box(0);
lean_ctor_set(x_148, 0, x_151);
x_2 = x_147;
x_4 = x_148;
goto _start;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_153 = lean_ctor_get(x_148, 1);
lean_inc(x_153);
lean_dec(x_148);
x_154 = lean_box(0);
x_155 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_155, 0, x_154);
lean_ctor_set(x_155, 1, x_153);
x_2 = x_147;
x_4 = x_155;
goto _start;
}
}
else
{
uint8_t x_157; 
lean_dec(x_147);
lean_dec(x_3);
lean_dec(x_1);
x_157 = !lean_is_exclusive(x_148);
if (x_157 == 0)
{
return x_148;
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_158 = lean_ctor_get(x_148, 0);
x_159 = lean_ctor_get(x_148, 1);
lean_inc(x_159);
lean_inc(x_158);
lean_dec(x_148);
x_160 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_160, 0, x_158);
lean_ctor_set(x_160, 1, x_159);
return x_160;
}
}
}
case 9:
{
lean_object* x_161; 
x_161 = lean_ctor_get(x_2, 1);
lean_inc(x_161);
lean_dec(x_2);
x_2 = x_161;
goto _start;
}
case 10:
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_163 = lean_ctor_get(x_2, 1);
lean_inc(x_163);
x_164 = lean_ctor_get(x_2, 2);
lean_inc(x_164);
lean_dec(x_2);
x_165 = l_Lean_IR_EmitC_emitCase(x_1, x_163, x_164, x_3, x_4);
return x_165;
}
case 11:
{
lean_object* x_166; uint8_t x_167; 
lean_dec(x_1);
x_166 = lean_ctor_get(x_2, 0);
lean_inc(x_166);
lean_dec(x_2);
x_167 = !lean_is_exclusive(x_4);
if (x_167 == 0)
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_168 = lean_ctor_get(x_4, 1);
x_169 = lean_ctor_get(x_4, 0);
lean_dec(x_169);
x_170 = l_Lean_IR_EmitC_emitBlock___main___closed__1;
x_171 = lean_string_append(x_168, x_170);
x_172 = lean_box(0);
lean_ctor_set(x_4, 1, x_171);
lean_ctor_set(x_4, 0, x_172);
x_173 = l_Lean_IR_EmitC_emitArg(x_166, x_3, x_4);
lean_dec(x_3);
if (lean_obj_tag(x_173) == 0)
{
uint8_t x_174; 
x_174 = !lean_is_exclusive(x_173);
if (x_174 == 0)
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_175 = lean_ctor_get(x_173, 1);
x_176 = lean_ctor_get(x_173, 0);
lean_dec(x_176);
x_177 = l_Lean_IR_formatFnBody___main___closed__3;
x_178 = lean_string_append(x_175, x_177);
x_179 = l_IO_println___rarg___closed__1;
x_180 = lean_string_append(x_178, x_179);
lean_ctor_set(x_173, 1, x_180);
lean_ctor_set(x_173, 0, x_172);
return x_173;
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_181 = lean_ctor_get(x_173, 1);
lean_inc(x_181);
lean_dec(x_173);
x_182 = l_Lean_IR_formatFnBody___main___closed__3;
x_183 = lean_string_append(x_181, x_182);
x_184 = l_IO_println___rarg___closed__1;
x_185 = lean_string_append(x_183, x_184);
x_186 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_186, 0, x_172);
lean_ctor_set(x_186, 1, x_185);
return x_186;
}
}
else
{
uint8_t x_187; 
x_187 = !lean_is_exclusive(x_173);
if (x_187 == 0)
{
return x_173;
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_188 = lean_ctor_get(x_173, 0);
x_189 = lean_ctor_get(x_173, 1);
lean_inc(x_189);
lean_inc(x_188);
lean_dec(x_173);
x_190 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_190, 0, x_188);
lean_ctor_set(x_190, 1, x_189);
return x_190;
}
}
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_191 = lean_ctor_get(x_4, 1);
lean_inc(x_191);
lean_dec(x_4);
x_192 = l_Lean_IR_EmitC_emitBlock___main___closed__1;
x_193 = lean_string_append(x_191, x_192);
x_194 = lean_box(0);
x_195 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_195, 0, x_194);
lean_ctor_set(x_195, 1, x_193);
x_196 = l_Lean_IR_EmitC_emitArg(x_166, x_3, x_195);
lean_dec(x_3);
if (lean_obj_tag(x_196) == 0)
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_197 = lean_ctor_get(x_196, 1);
lean_inc(x_197);
if (lean_is_exclusive(x_196)) {
 lean_ctor_release(x_196, 0);
 lean_ctor_release(x_196, 1);
 x_198 = x_196;
} else {
 lean_dec_ref(x_196);
 x_198 = lean_box(0);
}
x_199 = l_Lean_IR_formatFnBody___main___closed__3;
x_200 = lean_string_append(x_197, x_199);
x_201 = l_IO_println___rarg___closed__1;
x_202 = lean_string_append(x_200, x_201);
if (lean_is_scalar(x_198)) {
 x_203 = lean_alloc_ctor(0, 2, 0);
} else {
 x_203 = x_198;
}
lean_ctor_set(x_203, 0, x_194);
lean_ctor_set(x_203, 1, x_202);
return x_203;
}
else
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_204 = lean_ctor_get(x_196, 0);
lean_inc(x_204);
x_205 = lean_ctor_get(x_196, 1);
lean_inc(x_205);
if (lean_is_exclusive(x_196)) {
 lean_ctor_release(x_196, 0);
 lean_ctor_release(x_196, 1);
 x_206 = x_196;
} else {
 lean_dec_ref(x_196);
 x_206 = lean_box(0);
}
if (lean_is_scalar(x_206)) {
 x_207 = lean_alloc_ctor(1, 2, 0);
} else {
 x_207 = x_206;
}
lean_ctor_set(x_207, 0, x_204);
lean_ctor_set(x_207, 1, x_205);
return x_207;
}
}
}
case 12:
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; 
lean_dec(x_1);
x_208 = lean_ctor_get(x_2, 0);
lean_inc(x_208);
x_209 = lean_ctor_get(x_2, 1);
lean_inc(x_209);
lean_dec(x_2);
x_210 = l_Lean_IR_EmitC_emitJmp(x_208, x_209, x_3, x_4);
lean_dec(x_3);
lean_dec(x_209);
return x_210;
}
default: 
{
uint8_t x_211; 
lean_dec(x_3);
lean_dec(x_1);
x_211 = !lean_is_exclusive(x_4);
if (x_211 == 0)
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; 
x_212 = lean_ctor_get(x_4, 1);
x_213 = lean_ctor_get(x_4, 0);
lean_dec(x_213);
x_214 = l_Lean_IR_EmitC_emitBlock___main___closed__2;
x_215 = lean_string_append(x_212, x_214);
x_216 = l_IO_println___rarg___closed__1;
x_217 = lean_string_append(x_215, x_216);
x_218 = lean_box(0);
lean_ctor_set(x_4, 1, x_217);
lean_ctor_set(x_4, 0, x_218);
return x_4;
}
else
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; 
x_219 = lean_ctor_get(x_4, 1);
lean_inc(x_219);
lean_dec(x_4);
x_220 = l_Lean_IR_EmitC_emitBlock___main___closed__2;
x_221 = lean_string_append(x_219, x_220);
x_222 = l_IO_println___rarg___closed__1;
x_223 = lean_string_append(x_221, x_222);
x_224 = lean_box(0);
x_225 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_225, 0, x_224);
lean_ctor_set(x_225, 1, x_223);
return x_225;
}
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
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_2, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_2, 2);
lean_inc(x_17);
x_18 = lean_ctor_get(x_2, 3);
lean_inc(x_18);
lean_dec(x_2);
x_19 = !lean_is_exclusive(x_4);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_20 = lean_ctor_get(x_4, 1);
x_21 = lean_ctor_get(x_4, 0);
lean_dec(x_21);
x_22 = l_Nat_repr(x_16);
x_23 = l_Lean_IR_JoinPointId_HasToString___closed__1;
x_24 = lean_string_append(x_23, x_22);
lean_dec(x_22);
x_25 = lean_string_append(x_20, x_24);
lean_dec(x_24);
x_26 = l_Array_mforAux___main___at_Lean_IR_EmitC_emitCase___spec__1___closed__1;
x_27 = lean_string_append(x_25, x_26);
x_28 = l_IO_println___rarg___closed__1;
x_29 = lean_string_append(x_27, x_28);
x_30 = lean_box(0);
lean_ctor_set(x_4, 1, x_29);
lean_ctor_set(x_4, 0, x_30);
lean_inc(x_1);
lean_inc(x_3);
x_31 = lean_apply_3(x_1, x_17, x_3, x_4);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_31, 0);
lean_dec(x_33);
lean_ctor_set(x_31, 0, x_30);
x_2 = x_18;
x_4 = x_31;
goto _start;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_31, 1);
lean_inc(x_35);
lean_dec(x_31);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_30);
lean_ctor_set(x_36, 1, x_35);
x_2 = x_18;
x_4 = x_36;
goto _start;
}
}
else
{
uint8_t x_38; 
lean_dec(x_18);
lean_dec(x_3);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_31);
if (x_38 == 0)
{
return x_31;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_31, 0);
x_40 = lean_ctor_get(x_31, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_31);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_42 = lean_ctor_get(x_4, 1);
lean_inc(x_42);
lean_dec(x_4);
x_43 = l_Nat_repr(x_16);
x_44 = l_Lean_IR_JoinPointId_HasToString___closed__1;
x_45 = lean_string_append(x_44, x_43);
lean_dec(x_43);
x_46 = lean_string_append(x_42, x_45);
lean_dec(x_45);
x_47 = l_Array_mforAux___main___at_Lean_IR_EmitC_emitCase___spec__1___closed__1;
x_48 = lean_string_append(x_46, x_47);
x_49 = l_IO_println___rarg___closed__1;
x_50 = lean_string_append(x_48, x_49);
x_51 = lean_box(0);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_50);
lean_inc(x_1);
lean_inc(x_3);
x_53 = lean_apply_3(x_1, x_17, x_3, x_52);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_55 = x_53;
} else {
 lean_dec_ref(x_53);
 x_55 = lean_box(0);
}
if (lean_is_scalar(x_55)) {
 x_56 = lean_alloc_ctor(0, 2, 0);
} else {
 x_56 = x_55;
}
lean_ctor_set(x_56, 0, x_51);
lean_ctor_set(x_56, 1, x_54);
x_2 = x_18;
x_4 = x_56;
goto _start;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_18);
lean_dec(x_3);
lean_dec(x_1);
x_58 = lean_ctor_get(x_53, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_53, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_60 = x_53;
} else {
 lean_dec_ref(x_53);
 x_60 = lean_box(0);
}
if (lean_is_scalar(x_60)) {
 x_61 = lean_alloc_ctor(1, 2, 0);
} else {
 x_61 = x_60;
}
lean_ctor_set(x_61, 0, x_58);
lean_ctor_set(x_61, 1, x_59);
return x_61;
}
}
}
else
{
lean_object* x_62; 
x_62 = lean_box(0);
x_5 = x_62;
goto block_15;
}
block_15:
{
uint8_t x_6; 
lean_dec(x_5);
x_6 = l_Lean_IR_FnBody_isTerminal(x_2);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = l_Lean_IR_FnBody_body(x_2);
lean_dec(x_2);
x_2 = x_7;
goto _start;
}
else
{
uint8_t x_9; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_9 = !lean_is_exclusive(x_4);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_4, 0);
lean_dec(x_10);
x_11 = lean_box(0);
lean_ctor_set(x_4, 0, x_11);
return x_4;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_4, 1);
lean_inc(x_12);
lean_dec(x_4);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
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
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_ctor_get(x_3, 0);
lean_dec(x_6);
x_7 = l_Lean_IR_EmitC_emitTailCall___closed__4;
x_8 = lean_string_append(x_5, x_7);
x_9 = l_IO_println___rarg___closed__1;
x_10 = lean_string_append(x_8, x_9);
x_11 = lean_box(0);
lean_ctor_set(x_3, 1, x_10);
lean_ctor_set(x_3, 0, x_11);
x_12 = 0;
lean_inc(x_1);
x_13 = l_Lean_IR_EmitC_declareVars___main(x_1, x_12, x_2, x_3);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_unbox(x_14);
lean_dec(x_14);
if (x_15 == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_13);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_13, 0);
lean_dec(x_17);
lean_ctor_set(x_13, 0, x_11);
x_18 = l_Lean_IR_EmitC_emitFnBody___main___closed__1;
lean_inc(x_2);
lean_inc(x_1);
x_19 = l_Lean_IR_EmitC_emitBlock___main(x_18, x_1, x_2, x_13);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_19, 0);
lean_dec(x_21);
lean_ctor_set(x_19, 0, x_11);
x_22 = l_Lean_IR_EmitC_emitJPs___main(x_18, x_1, x_2, x_19);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_22, 1);
x_25 = lean_ctor_get(x_22, 0);
lean_dec(x_25);
x_26 = l_PersistentHashMap_Stats_toString___closed__5;
x_27 = lean_string_append(x_24, x_26);
x_28 = lean_string_append(x_27, x_9);
lean_ctor_set(x_22, 1, x_28);
lean_ctor_set(x_22, 0, x_11);
return x_22;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_22, 1);
lean_inc(x_29);
lean_dec(x_22);
x_30 = l_PersistentHashMap_Stats_toString___closed__5;
x_31 = lean_string_append(x_29, x_30);
x_32 = lean_string_append(x_31, x_9);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_11);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
else
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_22);
if (x_34 == 0)
{
return x_22;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_22, 0);
x_36 = lean_ctor_get(x_22, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_22);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_19, 1);
lean_inc(x_38);
lean_dec(x_19);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_11);
lean_ctor_set(x_39, 1, x_38);
x_40 = l_Lean_IR_EmitC_emitJPs___main(x_18, x_1, x_2, x_39);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_42 = x_40;
} else {
 lean_dec_ref(x_40);
 x_42 = lean_box(0);
}
x_43 = l_PersistentHashMap_Stats_toString___closed__5;
x_44 = lean_string_append(x_41, x_43);
x_45 = lean_string_append(x_44, x_9);
if (lean_is_scalar(x_42)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_42;
}
lean_ctor_set(x_46, 0, x_11);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_47 = lean_ctor_get(x_40, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_40, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_49 = x_40;
} else {
 lean_dec_ref(x_40);
 x_49 = lean_box(0);
}
if (lean_is_scalar(x_49)) {
 x_50 = lean_alloc_ctor(1, 2, 0);
} else {
 x_50 = x_49;
}
lean_ctor_set(x_50, 0, x_47);
lean_ctor_set(x_50, 1, x_48);
return x_50;
}
}
}
else
{
uint8_t x_51; 
lean_dec(x_2);
lean_dec(x_1);
x_51 = !lean_is_exclusive(x_19);
if (x_51 == 0)
{
return x_19;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_19, 0);
x_53 = lean_ctor_get(x_19, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_19);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_55 = lean_ctor_get(x_13, 1);
lean_inc(x_55);
lean_dec(x_13);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_11);
lean_ctor_set(x_56, 1, x_55);
x_57 = l_Lean_IR_EmitC_emitFnBody___main___closed__1;
lean_inc(x_2);
lean_inc(x_1);
x_58 = l_Lean_IR_EmitC_emitBlock___main(x_57, x_1, x_2, x_56);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_60 = x_58;
} else {
 lean_dec_ref(x_58);
 x_60 = lean_box(0);
}
if (lean_is_scalar(x_60)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_60;
}
lean_ctor_set(x_61, 0, x_11);
lean_ctor_set(x_61, 1, x_59);
x_62 = l_Lean_IR_EmitC_emitJPs___main(x_57, x_1, x_2, x_61);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_64 = x_62;
} else {
 lean_dec_ref(x_62);
 x_64 = lean_box(0);
}
x_65 = l_PersistentHashMap_Stats_toString___closed__5;
x_66 = lean_string_append(x_63, x_65);
x_67 = lean_string_append(x_66, x_9);
if (lean_is_scalar(x_64)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_64;
}
lean_ctor_set(x_68, 0, x_11);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_69 = lean_ctor_get(x_62, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_62, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_71 = x_62;
} else {
 lean_dec_ref(x_62);
 x_71 = lean_box(0);
}
if (lean_is_scalar(x_71)) {
 x_72 = lean_alloc_ctor(1, 2, 0);
} else {
 x_72 = x_71;
}
lean_ctor_set(x_72, 0, x_69);
lean_ctor_set(x_72, 1, x_70);
return x_72;
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_2);
lean_dec(x_1);
x_73 = lean_ctor_get(x_58, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_58, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_75 = x_58;
} else {
 lean_dec_ref(x_58);
 x_75 = lean_box(0);
}
if (lean_is_scalar(x_75)) {
 x_76 = lean_alloc_ctor(1, 2, 0);
} else {
 x_76 = x_75;
}
lean_ctor_set(x_76, 0, x_73);
lean_ctor_set(x_76, 1, x_74);
return x_76;
}
}
}
else
{
uint8_t x_77; 
x_77 = !lean_is_exclusive(x_13);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_78 = lean_ctor_get(x_13, 1);
x_79 = lean_ctor_get(x_13, 0);
lean_dec(x_79);
x_80 = l_String_splitAux___main___closed__1;
x_81 = lean_string_append(x_78, x_80);
x_82 = lean_string_append(x_81, x_9);
lean_ctor_set(x_13, 1, x_82);
lean_ctor_set(x_13, 0, x_11);
x_83 = l_Lean_IR_EmitC_emitFnBody___main___closed__1;
lean_inc(x_2);
lean_inc(x_1);
x_84 = l_Lean_IR_EmitC_emitBlock___main(x_83, x_1, x_2, x_13);
if (lean_obj_tag(x_84) == 0)
{
uint8_t x_85; 
x_85 = !lean_is_exclusive(x_84);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_84, 0);
lean_dec(x_86);
lean_ctor_set(x_84, 0, x_11);
x_87 = l_Lean_IR_EmitC_emitJPs___main(x_83, x_1, x_2, x_84);
if (lean_obj_tag(x_87) == 0)
{
uint8_t x_88; 
x_88 = !lean_is_exclusive(x_87);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_89 = lean_ctor_get(x_87, 1);
x_90 = lean_ctor_get(x_87, 0);
lean_dec(x_90);
x_91 = l_PersistentHashMap_Stats_toString___closed__5;
x_92 = lean_string_append(x_89, x_91);
x_93 = lean_string_append(x_92, x_9);
lean_ctor_set(x_87, 1, x_93);
lean_ctor_set(x_87, 0, x_11);
return x_87;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_94 = lean_ctor_get(x_87, 1);
lean_inc(x_94);
lean_dec(x_87);
x_95 = l_PersistentHashMap_Stats_toString___closed__5;
x_96 = lean_string_append(x_94, x_95);
x_97 = lean_string_append(x_96, x_9);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_11);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
}
else
{
uint8_t x_99; 
x_99 = !lean_is_exclusive(x_87);
if (x_99 == 0)
{
return x_87;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_87, 0);
x_101 = lean_ctor_get(x_87, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_87);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
return x_102;
}
}
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_84, 1);
lean_inc(x_103);
lean_dec(x_84);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_11);
lean_ctor_set(x_104, 1, x_103);
x_105 = l_Lean_IR_EmitC_emitJPs___main(x_83, x_1, x_2, x_104);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_106 = lean_ctor_get(x_105, 1);
lean_inc(x_106);
if (lean_is_exclusive(x_105)) {
 lean_ctor_release(x_105, 0);
 lean_ctor_release(x_105, 1);
 x_107 = x_105;
} else {
 lean_dec_ref(x_105);
 x_107 = lean_box(0);
}
x_108 = l_PersistentHashMap_Stats_toString___closed__5;
x_109 = lean_string_append(x_106, x_108);
x_110 = lean_string_append(x_109, x_9);
if (lean_is_scalar(x_107)) {
 x_111 = lean_alloc_ctor(0, 2, 0);
} else {
 x_111 = x_107;
}
lean_ctor_set(x_111, 0, x_11);
lean_ctor_set(x_111, 1, x_110);
return x_111;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_112 = lean_ctor_get(x_105, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_105, 1);
lean_inc(x_113);
if (lean_is_exclusive(x_105)) {
 lean_ctor_release(x_105, 0);
 lean_ctor_release(x_105, 1);
 x_114 = x_105;
} else {
 lean_dec_ref(x_105);
 x_114 = lean_box(0);
}
if (lean_is_scalar(x_114)) {
 x_115 = lean_alloc_ctor(1, 2, 0);
} else {
 x_115 = x_114;
}
lean_ctor_set(x_115, 0, x_112);
lean_ctor_set(x_115, 1, x_113);
return x_115;
}
}
}
else
{
uint8_t x_116; 
lean_dec(x_2);
lean_dec(x_1);
x_116 = !lean_is_exclusive(x_84);
if (x_116 == 0)
{
return x_84;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_84, 0);
x_118 = lean_ctor_get(x_84, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_84);
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
return x_119;
}
}
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_120 = lean_ctor_get(x_13, 1);
lean_inc(x_120);
lean_dec(x_13);
x_121 = l_String_splitAux___main___closed__1;
x_122 = lean_string_append(x_120, x_121);
x_123 = lean_string_append(x_122, x_9);
x_124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_124, 0, x_11);
lean_ctor_set(x_124, 1, x_123);
x_125 = l_Lean_IR_EmitC_emitFnBody___main___closed__1;
lean_inc(x_2);
lean_inc(x_1);
x_126 = l_Lean_IR_EmitC_emitBlock___main(x_125, x_1, x_2, x_124);
if (lean_obj_tag(x_126) == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_127 = lean_ctor_get(x_126, 1);
lean_inc(x_127);
if (lean_is_exclusive(x_126)) {
 lean_ctor_release(x_126, 0);
 lean_ctor_release(x_126, 1);
 x_128 = x_126;
} else {
 lean_dec_ref(x_126);
 x_128 = lean_box(0);
}
if (lean_is_scalar(x_128)) {
 x_129 = lean_alloc_ctor(0, 2, 0);
} else {
 x_129 = x_128;
}
lean_ctor_set(x_129, 0, x_11);
lean_ctor_set(x_129, 1, x_127);
x_130 = l_Lean_IR_EmitC_emitJPs___main(x_125, x_1, x_2, x_129);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_131 = lean_ctor_get(x_130, 1);
lean_inc(x_131);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 x_132 = x_130;
} else {
 lean_dec_ref(x_130);
 x_132 = lean_box(0);
}
x_133 = l_PersistentHashMap_Stats_toString___closed__5;
x_134 = lean_string_append(x_131, x_133);
x_135 = lean_string_append(x_134, x_9);
if (lean_is_scalar(x_132)) {
 x_136 = lean_alloc_ctor(0, 2, 0);
} else {
 x_136 = x_132;
}
lean_ctor_set(x_136, 0, x_11);
lean_ctor_set(x_136, 1, x_135);
return x_136;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_137 = lean_ctor_get(x_130, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_130, 1);
lean_inc(x_138);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 x_139 = x_130;
} else {
 lean_dec_ref(x_130);
 x_139 = lean_box(0);
}
if (lean_is_scalar(x_139)) {
 x_140 = lean_alloc_ctor(1, 2, 0);
} else {
 x_140 = x_139;
}
lean_ctor_set(x_140, 0, x_137);
lean_ctor_set(x_140, 1, x_138);
return x_140;
}
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
lean_dec(x_2);
lean_dec(x_1);
x_141 = lean_ctor_get(x_126, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_126, 1);
lean_inc(x_142);
if (lean_is_exclusive(x_126)) {
 lean_ctor_release(x_126, 0);
 lean_ctor_release(x_126, 1);
 x_143 = x_126;
} else {
 lean_dec_ref(x_126);
 x_143 = lean_box(0);
}
if (lean_is_scalar(x_143)) {
 x_144 = lean_alloc_ctor(1, 2, 0);
} else {
 x_144 = x_143;
}
lean_ctor_set(x_144, 0, x_141);
lean_ctor_set(x_144, 1, x_142);
return x_144;
}
}
}
}
else
{
uint8_t x_145; 
lean_dec(x_2);
lean_dec(x_1);
x_145 = !lean_is_exclusive(x_13);
if (x_145 == 0)
{
return x_13;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_146 = lean_ctor_get(x_13, 0);
x_147 = lean_ctor_get(x_13, 1);
lean_inc(x_147);
lean_inc(x_146);
lean_dec(x_13);
x_148 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_148, 0, x_146);
lean_ctor_set(x_148, 1, x_147);
return x_148;
}
}
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; uint8_t x_156; lean_object* x_157; 
x_149 = lean_ctor_get(x_3, 1);
lean_inc(x_149);
lean_dec(x_3);
x_150 = l_Lean_IR_EmitC_emitTailCall___closed__4;
x_151 = lean_string_append(x_149, x_150);
x_152 = l_IO_println___rarg___closed__1;
x_153 = lean_string_append(x_151, x_152);
x_154 = lean_box(0);
x_155 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_155, 0, x_154);
lean_ctor_set(x_155, 1, x_153);
x_156 = 0;
lean_inc(x_1);
x_157 = l_Lean_IR_EmitC_declareVars___main(x_1, x_156, x_2, x_155);
if (lean_obj_tag(x_157) == 0)
{
lean_object* x_158; uint8_t x_159; 
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
x_159 = lean_unbox(x_158);
lean_dec(x_158);
if (x_159 == 0)
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_160 = lean_ctor_get(x_157, 1);
lean_inc(x_160);
if (lean_is_exclusive(x_157)) {
 lean_ctor_release(x_157, 0);
 lean_ctor_release(x_157, 1);
 x_161 = x_157;
} else {
 lean_dec_ref(x_157);
 x_161 = lean_box(0);
}
if (lean_is_scalar(x_161)) {
 x_162 = lean_alloc_ctor(0, 2, 0);
} else {
 x_162 = x_161;
}
lean_ctor_set(x_162, 0, x_154);
lean_ctor_set(x_162, 1, x_160);
x_163 = l_Lean_IR_EmitC_emitFnBody___main___closed__1;
lean_inc(x_2);
lean_inc(x_1);
x_164 = l_Lean_IR_EmitC_emitBlock___main(x_163, x_1, x_2, x_162);
if (lean_obj_tag(x_164) == 0)
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_165 = lean_ctor_get(x_164, 1);
lean_inc(x_165);
if (lean_is_exclusive(x_164)) {
 lean_ctor_release(x_164, 0);
 lean_ctor_release(x_164, 1);
 x_166 = x_164;
} else {
 lean_dec_ref(x_164);
 x_166 = lean_box(0);
}
if (lean_is_scalar(x_166)) {
 x_167 = lean_alloc_ctor(0, 2, 0);
} else {
 x_167 = x_166;
}
lean_ctor_set(x_167, 0, x_154);
lean_ctor_set(x_167, 1, x_165);
x_168 = l_Lean_IR_EmitC_emitJPs___main(x_163, x_1, x_2, x_167);
if (lean_obj_tag(x_168) == 0)
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_169 = lean_ctor_get(x_168, 1);
lean_inc(x_169);
if (lean_is_exclusive(x_168)) {
 lean_ctor_release(x_168, 0);
 lean_ctor_release(x_168, 1);
 x_170 = x_168;
} else {
 lean_dec_ref(x_168);
 x_170 = lean_box(0);
}
x_171 = l_PersistentHashMap_Stats_toString___closed__5;
x_172 = lean_string_append(x_169, x_171);
x_173 = lean_string_append(x_172, x_152);
if (lean_is_scalar(x_170)) {
 x_174 = lean_alloc_ctor(0, 2, 0);
} else {
 x_174 = x_170;
}
lean_ctor_set(x_174, 0, x_154);
lean_ctor_set(x_174, 1, x_173);
return x_174;
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_175 = lean_ctor_get(x_168, 0);
lean_inc(x_175);
x_176 = lean_ctor_get(x_168, 1);
lean_inc(x_176);
if (lean_is_exclusive(x_168)) {
 lean_ctor_release(x_168, 0);
 lean_ctor_release(x_168, 1);
 x_177 = x_168;
} else {
 lean_dec_ref(x_168);
 x_177 = lean_box(0);
}
if (lean_is_scalar(x_177)) {
 x_178 = lean_alloc_ctor(1, 2, 0);
} else {
 x_178 = x_177;
}
lean_ctor_set(x_178, 0, x_175);
lean_ctor_set(x_178, 1, x_176);
return x_178;
}
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
lean_dec(x_2);
lean_dec(x_1);
x_179 = lean_ctor_get(x_164, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_164, 1);
lean_inc(x_180);
if (lean_is_exclusive(x_164)) {
 lean_ctor_release(x_164, 0);
 lean_ctor_release(x_164, 1);
 x_181 = x_164;
} else {
 lean_dec_ref(x_164);
 x_181 = lean_box(0);
}
if (lean_is_scalar(x_181)) {
 x_182 = lean_alloc_ctor(1, 2, 0);
} else {
 x_182 = x_181;
}
lean_ctor_set(x_182, 0, x_179);
lean_ctor_set(x_182, 1, x_180);
return x_182;
}
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_183 = lean_ctor_get(x_157, 1);
lean_inc(x_183);
if (lean_is_exclusive(x_157)) {
 lean_ctor_release(x_157, 0);
 lean_ctor_release(x_157, 1);
 x_184 = x_157;
} else {
 lean_dec_ref(x_157);
 x_184 = lean_box(0);
}
x_185 = l_String_splitAux___main___closed__1;
x_186 = lean_string_append(x_183, x_185);
x_187 = lean_string_append(x_186, x_152);
if (lean_is_scalar(x_184)) {
 x_188 = lean_alloc_ctor(0, 2, 0);
} else {
 x_188 = x_184;
}
lean_ctor_set(x_188, 0, x_154);
lean_ctor_set(x_188, 1, x_187);
x_189 = l_Lean_IR_EmitC_emitFnBody___main___closed__1;
lean_inc(x_2);
lean_inc(x_1);
x_190 = l_Lean_IR_EmitC_emitBlock___main(x_189, x_1, x_2, x_188);
if (lean_obj_tag(x_190) == 0)
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_191 = lean_ctor_get(x_190, 1);
lean_inc(x_191);
if (lean_is_exclusive(x_190)) {
 lean_ctor_release(x_190, 0);
 lean_ctor_release(x_190, 1);
 x_192 = x_190;
} else {
 lean_dec_ref(x_190);
 x_192 = lean_box(0);
}
if (lean_is_scalar(x_192)) {
 x_193 = lean_alloc_ctor(0, 2, 0);
} else {
 x_193 = x_192;
}
lean_ctor_set(x_193, 0, x_154);
lean_ctor_set(x_193, 1, x_191);
x_194 = l_Lean_IR_EmitC_emitJPs___main(x_189, x_1, x_2, x_193);
if (lean_obj_tag(x_194) == 0)
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_195 = lean_ctor_get(x_194, 1);
lean_inc(x_195);
if (lean_is_exclusive(x_194)) {
 lean_ctor_release(x_194, 0);
 lean_ctor_release(x_194, 1);
 x_196 = x_194;
} else {
 lean_dec_ref(x_194);
 x_196 = lean_box(0);
}
x_197 = l_PersistentHashMap_Stats_toString___closed__5;
x_198 = lean_string_append(x_195, x_197);
x_199 = lean_string_append(x_198, x_152);
if (lean_is_scalar(x_196)) {
 x_200 = lean_alloc_ctor(0, 2, 0);
} else {
 x_200 = x_196;
}
lean_ctor_set(x_200, 0, x_154);
lean_ctor_set(x_200, 1, x_199);
return x_200;
}
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_201 = lean_ctor_get(x_194, 0);
lean_inc(x_201);
x_202 = lean_ctor_get(x_194, 1);
lean_inc(x_202);
if (lean_is_exclusive(x_194)) {
 lean_ctor_release(x_194, 0);
 lean_ctor_release(x_194, 1);
 x_203 = x_194;
} else {
 lean_dec_ref(x_194);
 x_203 = lean_box(0);
}
if (lean_is_scalar(x_203)) {
 x_204 = lean_alloc_ctor(1, 2, 0);
} else {
 x_204 = x_203;
}
lean_ctor_set(x_204, 0, x_201);
lean_ctor_set(x_204, 1, x_202);
return x_204;
}
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
lean_dec(x_2);
lean_dec(x_1);
x_205 = lean_ctor_get(x_190, 0);
lean_inc(x_205);
x_206 = lean_ctor_get(x_190, 1);
lean_inc(x_206);
if (lean_is_exclusive(x_190)) {
 lean_ctor_release(x_190, 0);
 lean_ctor_release(x_190, 1);
 x_207 = x_190;
} else {
 lean_dec_ref(x_190);
 x_207 = lean_box(0);
}
if (lean_is_scalar(x_207)) {
 x_208 = lean_alloc_ctor(1, 2, 0);
} else {
 x_208 = x_207;
}
lean_ctor_set(x_208, 0, x_205);
lean_ctor_set(x_208, 1, x_206);
return x_208;
}
}
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; 
lean_dec(x_2);
lean_dec(x_1);
x_209 = lean_ctor_get(x_157, 0);
lean_inc(x_209);
x_210 = lean_ctor_get(x_157, 1);
lean_inc(x_210);
if (lean_is_exclusive(x_157)) {
 lean_ctor_release(x_157, 0);
 lean_ctor_release(x_157, 1);
 x_211 = x_157;
} else {
 lean_dec_ref(x_157);
 x_211 = lean_box(0);
}
if (lean_is_scalar(x_211)) {
 x_212 = lean_alloc_ctor(1, 2, 0);
} else {
 x_212 = x_211;
}
lean_ctor_set(x_212, 0, x_209);
lean_ctor_set(x_212, 1, x_210);
return x_212;
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
lean_object* _init_l_Nat_mforAux___main___at_Lean_IR_EmitC_emitDeclAux___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("lean_object* ");
return x_1;
}
}
lean_object* _init_l_Nat_mforAux___main___at_Lean_IR_EmitC_emitDeclAux___spec__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" = _args[");
return x_1;
}
}
lean_object* _init_l_Nat_mforAux___main___at_Lean_IR_EmitC_emitDeclAux___spec__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("];");
return x_1;
}
}
lean_object* l_Nat_mforAux___main___at_Lean_IR_EmitC_emitDeclAux___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_3, x_6);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_9 = lean_ctor_get(x_5, 1);
x_10 = lean_ctor_get(x_5, 0);
lean_dec(x_10);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_sub(x_3, x_11);
lean_dec(x_3);
x_13 = lean_nat_sub(x_2, x_12);
x_14 = lean_nat_sub(x_13, x_11);
lean_dec(x_13);
x_15 = l_Lean_IR_paramInh;
x_16 = lean_array_get(x_15, x_1, x_14);
x_17 = l_Nat_mforAux___main___at_Lean_IR_EmitC_emitDeclAux___spec__1___closed__1;
x_18 = lean_string_append(x_9, x_17);
x_19 = lean_ctor_get(x_16, 0);
lean_inc(x_19);
lean_dec(x_16);
x_20 = l_Nat_repr(x_19);
x_21 = l_Lean_IR_VarId_HasToString___closed__1;
x_22 = lean_string_append(x_21, x_20);
lean_dec(x_20);
x_23 = lean_string_append(x_18, x_22);
lean_dec(x_22);
x_24 = l_Nat_mforAux___main___at_Lean_IR_EmitC_emitDeclAux___spec__1___closed__2;
x_25 = lean_string_append(x_23, x_24);
x_26 = l_Nat_repr(x_14);
x_27 = lean_string_append(x_25, x_26);
lean_dec(x_26);
x_28 = l_Nat_mforAux___main___at_Lean_IR_EmitC_emitDeclAux___spec__1___closed__3;
x_29 = lean_string_append(x_27, x_28);
x_30 = l_IO_println___rarg___closed__1;
x_31 = lean_string_append(x_29, x_30);
x_32 = lean_box(0);
lean_ctor_set(x_5, 1, x_31);
lean_ctor_set(x_5, 0, x_32);
x_3 = x_12;
goto _start;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_34 = lean_ctor_get(x_5, 1);
lean_inc(x_34);
lean_dec(x_5);
x_35 = lean_unsigned_to_nat(1u);
x_36 = lean_nat_sub(x_3, x_35);
lean_dec(x_3);
x_37 = lean_nat_sub(x_2, x_36);
x_38 = lean_nat_sub(x_37, x_35);
lean_dec(x_37);
x_39 = l_Lean_IR_paramInh;
x_40 = lean_array_get(x_39, x_1, x_38);
x_41 = l_Nat_mforAux___main___at_Lean_IR_EmitC_emitDeclAux___spec__1___closed__1;
x_42 = lean_string_append(x_34, x_41);
x_43 = lean_ctor_get(x_40, 0);
lean_inc(x_43);
lean_dec(x_40);
x_44 = l_Nat_repr(x_43);
x_45 = l_Lean_IR_VarId_HasToString___closed__1;
x_46 = lean_string_append(x_45, x_44);
lean_dec(x_44);
x_47 = lean_string_append(x_42, x_46);
lean_dec(x_46);
x_48 = l_Nat_mforAux___main___at_Lean_IR_EmitC_emitDeclAux___spec__1___closed__2;
x_49 = lean_string_append(x_47, x_48);
x_50 = l_Nat_repr(x_38);
x_51 = lean_string_append(x_49, x_50);
lean_dec(x_50);
x_52 = l_Nat_mforAux___main___at_Lean_IR_EmitC_emitDeclAux___spec__1___closed__3;
x_53 = lean_string_append(x_51, x_52);
x_54 = l_IO_println___rarg___closed__1;
x_55 = lean_string_append(x_53, x_54);
x_56 = lean_box(0);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_55);
x_3 = x_36;
x_5 = x_57;
goto _start;
}
}
else
{
uint8_t x_59; 
lean_dec(x_3);
x_59 = !lean_is_exclusive(x_5);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_5, 0);
lean_dec(x_60);
x_61 = lean_box(0);
lean_ctor_set(x_5, 0, x_61);
return x_5;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_5, 1);
lean_inc(x_62);
lean_dec(x_5);
x_63 = lean_box(0);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_62);
return x_64;
}
}
}
}
lean_object* l_Nat_mforAux___main___at_Lean_IR_EmitC_emitDeclAux___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_3, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_29; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_3, x_8);
lean_dec(x_3);
x_10 = lean_nat_sub(x_2, x_9);
x_11 = lean_nat_sub(x_10, x_8);
lean_dec(x_10);
x_29 = lean_nat_dec_lt(x_6, x_11);
if (x_29 == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_5, 1);
lean_inc(x_30);
lean_dec(x_5);
x_12 = x_30;
goto block_28;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_5, 1);
lean_inc(x_31);
lean_dec(x_5);
x_32 = l_List_reprAux___main___rarg___closed__1;
x_33 = lean_string_append(x_31, x_32);
x_12 = x_33;
goto block_28;
}
block_28:
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_13 = l_Lean_IR_paramInh;
x_14 = lean_array_get(x_13, x_1, x_11);
lean_dec(x_11);
x_15 = lean_ctor_get_uint8(x_14, sizeof(void*)*1 + 1);
x_16 = l_Lean_IR_EmitC_toCType(x_15);
x_17 = lean_string_append(x_12, x_16);
lean_dec(x_16);
x_18 = l_Lean_Format_flatten___main___closed__1;
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
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
x_3 = x_9;
x_5 = x_26;
goto _start;
}
}
else
{
uint8_t x_34; 
lean_dec(x_3);
x_34 = !lean_is_exclusive(x_5);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_5, 0);
lean_dec(x_35);
x_36 = lean_box(0);
lean_ctor_set(x_5, 0, x_36);
return x_5;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_5, 1);
lean_inc(x_37);
lean_dec(x_5);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
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
lean_object* x_4; 
x_4 = l_Lean_IR_EmitC_getEnv(x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_14; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_box(0);
lean_inc(x_7);
lean_ctor_set(x_4, 0, x_8);
lean_inc(x_1);
x_9 = l_Lean_IR_mkVarJPMaps(x_1);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_IR_Decl_name(x_1);
lean_inc(x_12);
x_13 = l_Lean_hasInitAttr(x_6, x_12);
if (x_13 == 0)
{
uint8_t x_276; 
x_276 = 0;
x_14 = x_276;
goto block_275;
}
else
{
uint8_t x_277; 
x_277 = 1;
x_14 = x_277;
goto block_275;
}
block_275:
{
if (x_14 == 0)
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; uint8_t x_19; 
lean_dec(x_7);
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
x_17 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
x_18 = lean_ctor_get(x_1, 2);
lean_inc(x_18);
lean_dec(x_1);
x_19 = !lean_is_exclusive(x_2);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_2, 0);
x_21 = lean_ctor_get(x_2, 1);
x_22 = lean_ctor_get(x_2, 3);
lean_dec(x_22);
x_23 = lean_ctor_get(x_2, 2);
lean_dec(x_23);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_21);
lean_inc(x_20);
lean_ctor_set(x_2, 3, x_11);
lean_ctor_set(x_2, 2, x_10);
lean_inc(x_15);
x_24 = l_Lean_IR_EmitC_toCName(x_15, x_2, x_4);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_130; uint8_t x_131; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_27 = x_24;
} else {
 lean_dec_ref(x_24);
 x_27 = lean_box(0);
}
x_28 = l_Lean_IR_EmitC_toCType(x_17);
x_29 = lean_string_append(x_26, x_28);
lean_dec(x_28);
x_30 = l_Lean_Format_flatten___main___closed__1;
x_31 = lean_string_append(x_29, x_30);
x_32 = lean_array_get_size(x_16);
x_130 = lean_unsigned_to_nat(0u);
x_131 = lean_nat_dec_lt(x_130, x_32);
if (x_131 == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_132 = l_Lean_IR_EmitC_toCInitName___closed__1;
x_133 = lean_string_append(x_132, x_25);
lean_dec(x_25);
x_134 = l_Unit_HasRepr___closed__1;
x_135 = lean_string_append(x_133, x_134);
x_136 = lean_string_append(x_31, x_135);
lean_dec(x_135);
x_33 = x_136;
goto block_129;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_151; uint8_t x_152; 
x_137 = lean_string_append(x_31, x_25);
lean_dec(x_25);
x_138 = l_Prod_HasRepr___rarg___closed__1;
x_139 = lean_string_append(x_137, x_138);
lean_inc(x_139);
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_8);
lean_ctor_set(x_140, 1, x_139);
x_151 = l_Lean_closureMaxArgs;
x_152 = lean_nat_dec_lt(x_151, x_32);
if (x_152 == 0)
{
lean_dec(x_139);
x_141 = x_8;
goto block_150;
}
else
{
uint8_t x_153; 
x_153 = l_Lean_IR_ExplicitBoxing_isBoxedName(x_12);
if (x_153 == 0)
{
lean_dec(x_139);
x_141 = x_8;
goto block_150;
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
lean_dec(x_140);
x_154 = l_Lean_IR_EmitC_emitDeclAux___closed__3;
x_155 = lean_string_append(x_139, x_154);
x_156 = l_Option_HasRepr___rarg___closed__3;
x_157 = lean_string_append(x_155, x_156);
x_33 = x_157;
goto block_129;
}
}
block_150:
{
lean_object* x_142; 
lean_dec(x_141);
lean_inc(x_32);
x_142 = l_Nat_mforAux___main___at_Lean_IR_EmitC_emitDeclAux___spec__2(x_16, x_32, x_32, x_2, x_140);
if (lean_obj_tag(x_142) == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_143 = lean_ctor_get(x_142, 1);
lean_inc(x_143);
lean_dec(x_142);
x_144 = l_Option_HasRepr___rarg___closed__3;
x_145 = lean_string_append(x_143, x_144);
x_33 = x_145;
goto block_129;
}
else
{
uint8_t x_146; 
lean_dec(x_32);
lean_dec(x_27);
lean_dec(x_2);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_146 = !lean_is_exclusive(x_142);
if (x_146 == 0)
{
return x_142;
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_147 = lean_ctor_get(x_142, 0);
x_148 = lean_ctor_get(x_142, 1);
lean_inc(x_148);
lean_inc(x_147);
lean_dec(x_142);
x_149 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_149, 0, x_147);
lean_ctor_set(x_149, 1, x_148);
return x_149;
}
}
}
}
block_129:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_34 = l_Lean_IR_EmitC_emitDeclAux___closed__1;
x_35 = lean_string_append(x_33, x_34);
x_36 = l_IO_println___rarg___closed__1;
x_37 = lean_string_append(x_35, x_36);
lean_inc(x_37);
if (lean_is_scalar(x_27)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_27;
}
lean_ctor_set(x_38, 0, x_8);
lean_ctor_set(x_38, 1, x_37);
x_39 = l_Lean_closureMaxArgs;
x_40 = lean_nat_dec_lt(x_39, x_32);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_2);
lean_dec(x_12);
x_41 = l_Lean_IR_EmitC_emitDeclAux___closed__2;
x_42 = lean_string_append(x_37, x_41);
x_43 = lean_string_append(x_42, x_36);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_8);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_45, 0, x_20);
lean_ctor_set(x_45, 1, x_21);
lean_ctor_set(x_45, 2, x_10);
lean_ctor_set(x_45, 3, x_11);
lean_ctor_set(x_45, 4, x_15);
lean_ctor_set(x_45, 5, x_16);
x_46 = l_Lean_IR_EmitC_emitFnBody___main(x_18, x_45, x_44);
if (lean_obj_tag(x_46) == 0)
{
uint8_t x_47; 
x_47 = !lean_is_exclusive(x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_48 = lean_ctor_get(x_46, 1);
x_49 = lean_ctor_get(x_46, 0);
lean_dec(x_49);
x_50 = l_PersistentHashMap_Stats_toString___closed__5;
x_51 = lean_string_append(x_48, x_50);
x_52 = lean_string_append(x_51, x_36);
lean_ctor_set(x_46, 1, x_52);
lean_ctor_set(x_46, 0, x_8);
return x_46;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_53 = lean_ctor_get(x_46, 1);
lean_inc(x_53);
lean_dec(x_46);
x_54 = l_PersistentHashMap_Stats_toString___closed__5;
x_55 = lean_string_append(x_53, x_54);
x_56 = lean_string_append(x_55, x_36);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_8);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
else
{
uint8_t x_58; 
x_58 = !lean_is_exclusive(x_46);
if (x_58 == 0)
{
return x_46;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_46, 0);
x_60 = lean_ctor_get(x_46, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_46);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
else
{
uint8_t x_62; 
x_62 = l_Lean_IR_ExplicitBoxing_isBoxedName(x_12);
lean_dec(x_12);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_2);
x_63 = l_Lean_IR_EmitC_emitDeclAux___closed__2;
x_64 = lean_string_append(x_37, x_63);
x_65 = lean_string_append(x_64, x_36);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_8);
lean_ctor_set(x_66, 1, x_65);
x_67 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_67, 0, x_20);
lean_ctor_set(x_67, 1, x_21);
lean_ctor_set(x_67, 2, x_10);
lean_ctor_set(x_67, 3, x_11);
lean_ctor_set(x_67, 4, x_15);
lean_ctor_set(x_67, 5, x_16);
x_68 = l_Lean_IR_EmitC_emitFnBody___main(x_18, x_67, x_66);
if (lean_obj_tag(x_68) == 0)
{
uint8_t x_69; 
x_69 = !lean_is_exclusive(x_68);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_70 = lean_ctor_get(x_68, 1);
x_71 = lean_ctor_get(x_68, 0);
lean_dec(x_71);
x_72 = l_PersistentHashMap_Stats_toString___closed__5;
x_73 = lean_string_append(x_70, x_72);
x_74 = lean_string_append(x_73, x_36);
lean_ctor_set(x_68, 1, x_74);
lean_ctor_set(x_68, 0, x_8);
return x_68;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_75 = lean_ctor_get(x_68, 1);
lean_inc(x_75);
lean_dec(x_68);
x_76 = l_PersistentHashMap_Stats_toString___closed__5;
x_77 = lean_string_append(x_75, x_76);
x_78 = lean_string_append(x_77, x_36);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_8);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
else
{
uint8_t x_80; 
x_80 = !lean_is_exclusive(x_68);
if (x_80 == 0)
{
return x_68;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_68, 0);
x_82 = lean_ctor_get(x_68, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_68);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
}
else
{
lean_object* x_84; 
lean_dec(x_37);
lean_inc(x_32);
x_84 = l_Nat_mforAux___main___at_Lean_IR_EmitC_emitDeclAux___spec__1(x_16, x_32, x_32, x_2, x_38);
lean_dec(x_2);
lean_dec(x_32);
if (lean_obj_tag(x_84) == 0)
{
uint8_t x_85; 
x_85 = !lean_is_exclusive(x_84);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_86 = lean_ctor_get(x_84, 1);
x_87 = lean_ctor_get(x_84, 0);
lean_dec(x_87);
x_88 = l_Lean_IR_EmitC_emitDeclAux___closed__2;
x_89 = lean_string_append(x_86, x_88);
x_90 = lean_string_append(x_89, x_36);
lean_ctor_set(x_84, 1, x_90);
lean_ctor_set(x_84, 0, x_8);
x_91 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_91, 0, x_20);
lean_ctor_set(x_91, 1, x_21);
lean_ctor_set(x_91, 2, x_10);
lean_ctor_set(x_91, 3, x_11);
lean_ctor_set(x_91, 4, x_15);
lean_ctor_set(x_91, 5, x_16);
x_92 = l_Lean_IR_EmitC_emitFnBody___main(x_18, x_91, x_84);
if (lean_obj_tag(x_92) == 0)
{
uint8_t x_93; 
x_93 = !lean_is_exclusive(x_92);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_94 = lean_ctor_get(x_92, 1);
x_95 = lean_ctor_get(x_92, 0);
lean_dec(x_95);
x_96 = l_PersistentHashMap_Stats_toString___closed__5;
x_97 = lean_string_append(x_94, x_96);
x_98 = lean_string_append(x_97, x_36);
lean_ctor_set(x_92, 1, x_98);
lean_ctor_set(x_92, 0, x_8);
return x_92;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_99 = lean_ctor_get(x_92, 1);
lean_inc(x_99);
lean_dec(x_92);
x_100 = l_PersistentHashMap_Stats_toString___closed__5;
x_101 = lean_string_append(x_99, x_100);
x_102 = lean_string_append(x_101, x_36);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_8);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
else
{
uint8_t x_104; 
x_104 = !lean_is_exclusive(x_92);
if (x_104 == 0)
{
return x_92;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_92, 0);
x_106 = lean_ctor_get(x_92, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_92);
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
return x_107;
}
}
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_108 = lean_ctor_get(x_84, 1);
lean_inc(x_108);
lean_dec(x_84);
x_109 = l_Lean_IR_EmitC_emitDeclAux___closed__2;
x_110 = lean_string_append(x_108, x_109);
x_111 = lean_string_append(x_110, x_36);
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_8);
lean_ctor_set(x_112, 1, x_111);
x_113 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_113, 0, x_20);
lean_ctor_set(x_113, 1, x_21);
lean_ctor_set(x_113, 2, x_10);
lean_ctor_set(x_113, 3, x_11);
lean_ctor_set(x_113, 4, x_15);
lean_ctor_set(x_113, 5, x_16);
x_114 = l_Lean_IR_EmitC_emitFnBody___main(x_18, x_113, x_112);
if (lean_obj_tag(x_114) == 0)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_115 = lean_ctor_get(x_114, 1);
lean_inc(x_115);
if (lean_is_exclusive(x_114)) {
 lean_ctor_release(x_114, 0);
 lean_ctor_release(x_114, 1);
 x_116 = x_114;
} else {
 lean_dec_ref(x_114);
 x_116 = lean_box(0);
}
x_117 = l_PersistentHashMap_Stats_toString___closed__5;
x_118 = lean_string_append(x_115, x_117);
x_119 = lean_string_append(x_118, x_36);
if (lean_is_scalar(x_116)) {
 x_120 = lean_alloc_ctor(0, 2, 0);
} else {
 x_120 = x_116;
}
lean_ctor_set(x_120, 0, x_8);
lean_ctor_set(x_120, 1, x_119);
return x_120;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_121 = lean_ctor_get(x_114, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_114, 1);
lean_inc(x_122);
if (lean_is_exclusive(x_114)) {
 lean_ctor_release(x_114, 0);
 lean_ctor_release(x_114, 1);
 x_123 = x_114;
} else {
 lean_dec_ref(x_114);
 x_123 = lean_box(0);
}
if (lean_is_scalar(x_123)) {
 x_124 = lean_alloc_ctor(1, 2, 0);
} else {
 x_124 = x_123;
}
lean_ctor_set(x_124, 0, x_121);
lean_ctor_set(x_124, 1, x_122);
return x_124;
}
}
}
else
{
uint8_t x_125; 
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
x_125 = !lean_is_exclusive(x_84);
if (x_125 == 0)
{
return x_84;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_126 = lean_ctor_get(x_84, 0);
x_127 = lean_ctor_get(x_84, 1);
lean_inc(x_127);
lean_inc(x_126);
lean_dec(x_84);
x_128 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_127);
return x_128;
}
}
}
}
}
}
else
{
uint8_t x_158; 
lean_dec(x_2);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_158 = !lean_is_exclusive(x_24);
if (x_158 == 0)
{
return x_24;
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_159 = lean_ctor_get(x_24, 0);
x_160 = lean_ctor_get(x_24, 1);
lean_inc(x_160);
lean_inc(x_159);
lean_dec(x_24);
x_161 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_161, 0, x_159);
lean_ctor_set(x_161, 1, x_160);
return x_161;
}
}
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_162 = lean_ctor_get(x_2, 0);
x_163 = lean_ctor_get(x_2, 1);
x_164 = lean_ctor_get(x_2, 4);
x_165 = lean_ctor_get(x_2, 5);
lean_inc(x_165);
lean_inc(x_164);
lean_inc(x_163);
lean_inc(x_162);
lean_dec(x_2);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_163);
lean_inc(x_162);
x_166 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_166, 0, x_162);
lean_ctor_set(x_166, 1, x_163);
lean_ctor_set(x_166, 2, x_10);
lean_ctor_set(x_166, 3, x_11);
lean_ctor_set(x_166, 4, x_164);
lean_ctor_set(x_166, 5, x_165);
lean_inc(x_15);
x_167 = l_Lean_IR_EmitC_toCName(x_15, x_166, x_4);
if (lean_obj_tag(x_167) == 0)
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_241; uint8_t x_242; 
x_168 = lean_ctor_get(x_167, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_167, 1);
lean_inc(x_169);
if (lean_is_exclusive(x_167)) {
 lean_ctor_release(x_167, 0);
 lean_ctor_release(x_167, 1);
 x_170 = x_167;
} else {
 lean_dec_ref(x_167);
 x_170 = lean_box(0);
}
x_171 = l_Lean_IR_EmitC_toCType(x_17);
x_172 = lean_string_append(x_169, x_171);
lean_dec(x_171);
x_173 = l_Lean_Format_flatten___main___closed__1;
x_174 = lean_string_append(x_172, x_173);
x_175 = lean_array_get_size(x_16);
x_241 = lean_unsigned_to_nat(0u);
x_242 = lean_nat_dec_lt(x_241, x_175);
if (x_242 == 0)
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; 
x_243 = l_Lean_IR_EmitC_toCInitName___closed__1;
x_244 = lean_string_append(x_243, x_168);
lean_dec(x_168);
x_245 = l_Unit_HasRepr___closed__1;
x_246 = lean_string_append(x_244, x_245);
x_247 = lean_string_append(x_174, x_246);
lean_dec(x_246);
x_176 = x_247;
goto block_240;
}
else
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_262; uint8_t x_263; 
x_248 = lean_string_append(x_174, x_168);
lean_dec(x_168);
x_249 = l_Prod_HasRepr___rarg___closed__1;
x_250 = lean_string_append(x_248, x_249);
lean_inc(x_250);
x_251 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_251, 0, x_8);
lean_ctor_set(x_251, 1, x_250);
x_262 = l_Lean_closureMaxArgs;
x_263 = lean_nat_dec_lt(x_262, x_175);
if (x_263 == 0)
{
lean_dec(x_250);
x_252 = x_8;
goto block_261;
}
else
{
uint8_t x_264; 
x_264 = l_Lean_IR_ExplicitBoxing_isBoxedName(x_12);
if (x_264 == 0)
{
lean_dec(x_250);
x_252 = x_8;
goto block_261;
}
else
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; 
lean_dec(x_251);
x_265 = l_Lean_IR_EmitC_emitDeclAux___closed__3;
x_266 = lean_string_append(x_250, x_265);
x_267 = l_Option_HasRepr___rarg___closed__3;
x_268 = lean_string_append(x_266, x_267);
x_176 = x_268;
goto block_240;
}
}
block_261:
{
lean_object* x_253; 
lean_dec(x_252);
lean_inc(x_175);
x_253 = l_Nat_mforAux___main___at_Lean_IR_EmitC_emitDeclAux___spec__2(x_16, x_175, x_175, x_166, x_251);
if (lean_obj_tag(x_253) == 0)
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; 
x_254 = lean_ctor_get(x_253, 1);
lean_inc(x_254);
lean_dec(x_253);
x_255 = l_Option_HasRepr___rarg___closed__3;
x_256 = lean_string_append(x_254, x_255);
x_176 = x_256;
goto block_240;
}
else
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; 
lean_dec(x_175);
lean_dec(x_170);
lean_dec(x_166);
lean_dec(x_163);
lean_dec(x_162);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_257 = lean_ctor_get(x_253, 0);
lean_inc(x_257);
x_258 = lean_ctor_get(x_253, 1);
lean_inc(x_258);
if (lean_is_exclusive(x_253)) {
 lean_ctor_release(x_253, 0);
 lean_ctor_release(x_253, 1);
 x_259 = x_253;
} else {
 lean_dec_ref(x_253);
 x_259 = lean_box(0);
}
if (lean_is_scalar(x_259)) {
 x_260 = lean_alloc_ctor(1, 2, 0);
} else {
 x_260 = x_259;
}
lean_ctor_set(x_260, 0, x_257);
lean_ctor_set(x_260, 1, x_258);
return x_260;
}
}
}
block_240:
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; uint8_t x_183; 
x_177 = l_Lean_IR_EmitC_emitDeclAux___closed__1;
x_178 = lean_string_append(x_176, x_177);
x_179 = l_IO_println___rarg___closed__1;
x_180 = lean_string_append(x_178, x_179);
lean_inc(x_180);
if (lean_is_scalar(x_170)) {
 x_181 = lean_alloc_ctor(0, 2, 0);
} else {
 x_181 = x_170;
}
lean_ctor_set(x_181, 0, x_8);
lean_ctor_set(x_181, 1, x_180);
x_182 = l_Lean_closureMaxArgs;
x_183 = lean_nat_dec_lt(x_182, x_175);
if (x_183 == 0)
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; 
lean_dec(x_181);
lean_dec(x_175);
lean_dec(x_166);
lean_dec(x_12);
x_184 = l_Lean_IR_EmitC_emitDeclAux___closed__2;
x_185 = lean_string_append(x_180, x_184);
x_186 = lean_string_append(x_185, x_179);
x_187 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_187, 0, x_8);
lean_ctor_set(x_187, 1, x_186);
x_188 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_188, 0, x_162);
lean_ctor_set(x_188, 1, x_163);
lean_ctor_set(x_188, 2, x_10);
lean_ctor_set(x_188, 3, x_11);
lean_ctor_set(x_188, 4, x_15);
lean_ctor_set(x_188, 5, x_16);
x_189 = l_Lean_IR_EmitC_emitFnBody___main(x_18, x_188, x_187);
if (lean_obj_tag(x_189) == 0)
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_190 = lean_ctor_get(x_189, 1);
lean_inc(x_190);
if (lean_is_exclusive(x_189)) {
 lean_ctor_release(x_189, 0);
 lean_ctor_release(x_189, 1);
 x_191 = x_189;
} else {
 lean_dec_ref(x_189);
 x_191 = lean_box(0);
}
x_192 = l_PersistentHashMap_Stats_toString___closed__5;
x_193 = lean_string_append(x_190, x_192);
x_194 = lean_string_append(x_193, x_179);
if (lean_is_scalar(x_191)) {
 x_195 = lean_alloc_ctor(0, 2, 0);
} else {
 x_195 = x_191;
}
lean_ctor_set(x_195, 0, x_8);
lean_ctor_set(x_195, 1, x_194);
return x_195;
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_196 = lean_ctor_get(x_189, 0);
lean_inc(x_196);
x_197 = lean_ctor_get(x_189, 1);
lean_inc(x_197);
if (lean_is_exclusive(x_189)) {
 lean_ctor_release(x_189, 0);
 lean_ctor_release(x_189, 1);
 x_198 = x_189;
} else {
 lean_dec_ref(x_189);
 x_198 = lean_box(0);
}
if (lean_is_scalar(x_198)) {
 x_199 = lean_alloc_ctor(1, 2, 0);
} else {
 x_199 = x_198;
}
lean_ctor_set(x_199, 0, x_196);
lean_ctor_set(x_199, 1, x_197);
return x_199;
}
}
else
{
uint8_t x_200; 
x_200 = l_Lean_IR_ExplicitBoxing_isBoxedName(x_12);
lean_dec(x_12);
if (x_200 == 0)
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; 
lean_dec(x_181);
lean_dec(x_175);
lean_dec(x_166);
x_201 = l_Lean_IR_EmitC_emitDeclAux___closed__2;
x_202 = lean_string_append(x_180, x_201);
x_203 = lean_string_append(x_202, x_179);
x_204 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_204, 0, x_8);
lean_ctor_set(x_204, 1, x_203);
x_205 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_205, 0, x_162);
lean_ctor_set(x_205, 1, x_163);
lean_ctor_set(x_205, 2, x_10);
lean_ctor_set(x_205, 3, x_11);
lean_ctor_set(x_205, 4, x_15);
lean_ctor_set(x_205, 5, x_16);
x_206 = l_Lean_IR_EmitC_emitFnBody___main(x_18, x_205, x_204);
if (lean_obj_tag(x_206) == 0)
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_207 = lean_ctor_get(x_206, 1);
lean_inc(x_207);
if (lean_is_exclusive(x_206)) {
 lean_ctor_release(x_206, 0);
 lean_ctor_release(x_206, 1);
 x_208 = x_206;
} else {
 lean_dec_ref(x_206);
 x_208 = lean_box(0);
}
x_209 = l_PersistentHashMap_Stats_toString___closed__5;
x_210 = lean_string_append(x_207, x_209);
x_211 = lean_string_append(x_210, x_179);
if (lean_is_scalar(x_208)) {
 x_212 = lean_alloc_ctor(0, 2, 0);
} else {
 x_212 = x_208;
}
lean_ctor_set(x_212, 0, x_8);
lean_ctor_set(x_212, 1, x_211);
return x_212;
}
else
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
x_213 = lean_ctor_get(x_206, 0);
lean_inc(x_213);
x_214 = lean_ctor_get(x_206, 1);
lean_inc(x_214);
if (lean_is_exclusive(x_206)) {
 lean_ctor_release(x_206, 0);
 lean_ctor_release(x_206, 1);
 x_215 = x_206;
} else {
 lean_dec_ref(x_206);
 x_215 = lean_box(0);
}
if (lean_is_scalar(x_215)) {
 x_216 = lean_alloc_ctor(1, 2, 0);
} else {
 x_216 = x_215;
}
lean_ctor_set(x_216, 0, x_213);
lean_ctor_set(x_216, 1, x_214);
return x_216;
}
}
else
{
lean_object* x_217; 
lean_dec(x_180);
lean_inc(x_175);
x_217 = l_Nat_mforAux___main___at_Lean_IR_EmitC_emitDeclAux___spec__1(x_16, x_175, x_175, x_166, x_181);
lean_dec(x_166);
lean_dec(x_175);
if (lean_obj_tag(x_217) == 0)
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; 
x_218 = lean_ctor_get(x_217, 1);
lean_inc(x_218);
if (lean_is_exclusive(x_217)) {
 lean_ctor_release(x_217, 0);
 lean_ctor_release(x_217, 1);
 x_219 = x_217;
} else {
 lean_dec_ref(x_217);
 x_219 = lean_box(0);
}
x_220 = l_Lean_IR_EmitC_emitDeclAux___closed__2;
x_221 = lean_string_append(x_218, x_220);
x_222 = lean_string_append(x_221, x_179);
if (lean_is_scalar(x_219)) {
 x_223 = lean_alloc_ctor(0, 2, 0);
} else {
 x_223 = x_219;
}
lean_ctor_set(x_223, 0, x_8);
lean_ctor_set(x_223, 1, x_222);
x_224 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_224, 0, x_162);
lean_ctor_set(x_224, 1, x_163);
lean_ctor_set(x_224, 2, x_10);
lean_ctor_set(x_224, 3, x_11);
lean_ctor_set(x_224, 4, x_15);
lean_ctor_set(x_224, 5, x_16);
x_225 = l_Lean_IR_EmitC_emitFnBody___main(x_18, x_224, x_223);
if (lean_obj_tag(x_225) == 0)
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; 
x_226 = lean_ctor_get(x_225, 1);
lean_inc(x_226);
if (lean_is_exclusive(x_225)) {
 lean_ctor_release(x_225, 0);
 lean_ctor_release(x_225, 1);
 x_227 = x_225;
} else {
 lean_dec_ref(x_225);
 x_227 = lean_box(0);
}
x_228 = l_PersistentHashMap_Stats_toString___closed__5;
x_229 = lean_string_append(x_226, x_228);
x_230 = lean_string_append(x_229, x_179);
if (lean_is_scalar(x_227)) {
 x_231 = lean_alloc_ctor(0, 2, 0);
} else {
 x_231 = x_227;
}
lean_ctor_set(x_231, 0, x_8);
lean_ctor_set(x_231, 1, x_230);
return x_231;
}
else
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; 
x_232 = lean_ctor_get(x_225, 0);
lean_inc(x_232);
x_233 = lean_ctor_get(x_225, 1);
lean_inc(x_233);
if (lean_is_exclusive(x_225)) {
 lean_ctor_release(x_225, 0);
 lean_ctor_release(x_225, 1);
 x_234 = x_225;
} else {
 lean_dec_ref(x_225);
 x_234 = lean_box(0);
}
if (lean_is_scalar(x_234)) {
 x_235 = lean_alloc_ctor(1, 2, 0);
} else {
 x_235 = x_234;
}
lean_ctor_set(x_235, 0, x_232);
lean_ctor_set(x_235, 1, x_233);
return x_235;
}
}
else
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; 
lean_dec(x_163);
lean_dec(x_162);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
x_236 = lean_ctor_get(x_217, 0);
lean_inc(x_236);
x_237 = lean_ctor_get(x_217, 1);
lean_inc(x_237);
if (lean_is_exclusive(x_217)) {
 lean_ctor_release(x_217, 0);
 lean_ctor_release(x_217, 1);
 x_238 = x_217;
} else {
 lean_dec_ref(x_217);
 x_238 = lean_box(0);
}
if (lean_is_scalar(x_238)) {
 x_239 = lean_alloc_ctor(1, 2, 0);
} else {
 x_239 = x_238;
}
lean_ctor_set(x_239, 0, x_236);
lean_ctor_set(x_239, 1, x_237);
return x_239;
}
}
}
}
}
else
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; 
lean_dec(x_166);
lean_dec(x_163);
lean_dec(x_162);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_269 = lean_ctor_get(x_167, 0);
lean_inc(x_269);
x_270 = lean_ctor_get(x_167, 1);
lean_inc(x_270);
if (lean_is_exclusive(x_167)) {
 lean_ctor_release(x_167, 0);
 lean_ctor_release(x_167, 1);
 x_271 = x_167;
} else {
 lean_dec_ref(x_167);
 x_271 = lean_box(0);
}
if (lean_is_scalar(x_271)) {
 x_272 = lean_alloc_ctor(1, 2, 0);
} else {
 x_272 = x_271;
}
lean_ctor_set(x_272, 0, x_269);
lean_ctor_set(x_272, 1, x_270);
return x_272;
}
}
}
else
{
lean_object* x_273; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_273 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_273, 0, x_8);
lean_ctor_set(x_273, 1, x_7);
return x_273;
}
}
else
{
lean_object* x_274; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_274 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_274, 0, x_8);
lean_ctor_set(x_274, 1, x_7);
return x_274;
}
}
}
else
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; uint8_t x_286; uint8_t x_287; 
x_278 = lean_ctor_get(x_4, 0);
x_279 = lean_ctor_get(x_4, 1);
lean_inc(x_279);
lean_inc(x_278);
lean_dec(x_4);
x_280 = lean_box(0);
lean_inc(x_279);
x_281 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_281, 0, x_280);
lean_ctor_set(x_281, 1, x_279);
lean_inc(x_1);
x_282 = l_Lean_IR_mkVarJPMaps(x_1);
x_283 = lean_ctor_get(x_282, 0);
lean_inc(x_283);
x_284 = lean_ctor_get(x_282, 1);
lean_inc(x_284);
lean_dec(x_282);
x_285 = l_Lean_IR_Decl_name(x_1);
lean_inc(x_285);
x_286 = l_Lean_hasInitAttr(x_278, x_285);
if (x_286 == 0)
{
uint8_t x_407; 
x_407 = 0;
x_287 = x_407;
goto block_406;
}
else
{
uint8_t x_408; 
x_408 = 1;
x_287 = x_408;
goto block_406;
}
block_406:
{
if (x_287 == 0)
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_288; lean_object* x_289; uint8_t x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; 
lean_dec(x_279);
x_288 = lean_ctor_get(x_1, 0);
lean_inc(x_288);
x_289 = lean_ctor_get(x_1, 1);
lean_inc(x_289);
x_290 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
x_291 = lean_ctor_get(x_1, 2);
lean_inc(x_291);
lean_dec(x_1);
x_292 = lean_ctor_get(x_2, 0);
lean_inc(x_292);
x_293 = lean_ctor_get(x_2, 1);
lean_inc(x_293);
x_294 = lean_ctor_get(x_2, 4);
lean_inc(x_294);
x_295 = lean_ctor_get(x_2, 5);
lean_inc(x_295);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 lean_ctor_release(x_2, 3);
 lean_ctor_release(x_2, 4);
 lean_ctor_release(x_2, 5);
 x_296 = x_2;
} else {
 lean_dec_ref(x_2);
 x_296 = lean_box(0);
}
lean_inc(x_284);
lean_inc(x_283);
lean_inc(x_293);
lean_inc(x_292);
if (lean_is_scalar(x_296)) {
 x_297 = lean_alloc_ctor(0, 6, 0);
} else {
 x_297 = x_296;
}
lean_ctor_set(x_297, 0, x_292);
lean_ctor_set(x_297, 1, x_293);
lean_ctor_set(x_297, 2, x_283);
lean_ctor_set(x_297, 3, x_284);
lean_ctor_set(x_297, 4, x_294);
lean_ctor_set(x_297, 5, x_295);
lean_inc(x_288);
x_298 = l_Lean_IR_EmitC_toCName(x_288, x_297, x_281);
if (lean_obj_tag(x_298) == 0)
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_372; uint8_t x_373; 
x_299 = lean_ctor_get(x_298, 0);
lean_inc(x_299);
x_300 = lean_ctor_get(x_298, 1);
lean_inc(x_300);
if (lean_is_exclusive(x_298)) {
 lean_ctor_release(x_298, 0);
 lean_ctor_release(x_298, 1);
 x_301 = x_298;
} else {
 lean_dec_ref(x_298);
 x_301 = lean_box(0);
}
x_302 = l_Lean_IR_EmitC_toCType(x_290);
x_303 = lean_string_append(x_300, x_302);
lean_dec(x_302);
x_304 = l_Lean_Format_flatten___main___closed__1;
x_305 = lean_string_append(x_303, x_304);
x_306 = lean_array_get_size(x_289);
x_372 = lean_unsigned_to_nat(0u);
x_373 = lean_nat_dec_lt(x_372, x_306);
if (x_373 == 0)
{
lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; 
x_374 = l_Lean_IR_EmitC_toCInitName___closed__1;
x_375 = lean_string_append(x_374, x_299);
lean_dec(x_299);
x_376 = l_Unit_HasRepr___closed__1;
x_377 = lean_string_append(x_375, x_376);
x_378 = lean_string_append(x_305, x_377);
lean_dec(x_377);
x_307 = x_378;
goto block_371;
}
else
{
lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_393; uint8_t x_394; 
x_379 = lean_string_append(x_305, x_299);
lean_dec(x_299);
x_380 = l_Prod_HasRepr___rarg___closed__1;
x_381 = lean_string_append(x_379, x_380);
lean_inc(x_381);
x_382 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_382, 0, x_280);
lean_ctor_set(x_382, 1, x_381);
x_393 = l_Lean_closureMaxArgs;
x_394 = lean_nat_dec_lt(x_393, x_306);
if (x_394 == 0)
{
lean_dec(x_381);
x_383 = x_280;
goto block_392;
}
else
{
uint8_t x_395; 
x_395 = l_Lean_IR_ExplicitBoxing_isBoxedName(x_285);
if (x_395 == 0)
{
lean_dec(x_381);
x_383 = x_280;
goto block_392;
}
else
{
lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; 
lean_dec(x_382);
x_396 = l_Lean_IR_EmitC_emitDeclAux___closed__3;
x_397 = lean_string_append(x_381, x_396);
x_398 = l_Option_HasRepr___rarg___closed__3;
x_399 = lean_string_append(x_397, x_398);
x_307 = x_399;
goto block_371;
}
}
block_392:
{
lean_object* x_384; 
lean_dec(x_383);
lean_inc(x_306);
x_384 = l_Nat_mforAux___main___at_Lean_IR_EmitC_emitDeclAux___spec__2(x_289, x_306, x_306, x_297, x_382);
if (lean_obj_tag(x_384) == 0)
{
lean_object* x_385; lean_object* x_386; lean_object* x_387; 
x_385 = lean_ctor_get(x_384, 1);
lean_inc(x_385);
lean_dec(x_384);
x_386 = l_Option_HasRepr___rarg___closed__3;
x_387 = lean_string_append(x_385, x_386);
x_307 = x_387;
goto block_371;
}
else
{
lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; 
lean_dec(x_306);
lean_dec(x_301);
lean_dec(x_297);
lean_dec(x_293);
lean_dec(x_292);
lean_dec(x_291);
lean_dec(x_289);
lean_dec(x_288);
lean_dec(x_285);
lean_dec(x_284);
lean_dec(x_283);
x_388 = lean_ctor_get(x_384, 0);
lean_inc(x_388);
x_389 = lean_ctor_get(x_384, 1);
lean_inc(x_389);
if (lean_is_exclusive(x_384)) {
 lean_ctor_release(x_384, 0);
 lean_ctor_release(x_384, 1);
 x_390 = x_384;
} else {
 lean_dec_ref(x_384);
 x_390 = lean_box(0);
}
if (lean_is_scalar(x_390)) {
 x_391 = lean_alloc_ctor(1, 2, 0);
} else {
 x_391 = x_390;
}
lean_ctor_set(x_391, 0, x_388);
lean_ctor_set(x_391, 1, x_389);
return x_391;
}
}
}
block_371:
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; uint8_t x_314; 
x_308 = l_Lean_IR_EmitC_emitDeclAux___closed__1;
x_309 = lean_string_append(x_307, x_308);
x_310 = l_IO_println___rarg___closed__1;
x_311 = lean_string_append(x_309, x_310);
lean_inc(x_311);
if (lean_is_scalar(x_301)) {
 x_312 = lean_alloc_ctor(0, 2, 0);
} else {
 x_312 = x_301;
}
lean_ctor_set(x_312, 0, x_280);
lean_ctor_set(x_312, 1, x_311);
x_313 = l_Lean_closureMaxArgs;
x_314 = lean_nat_dec_lt(x_313, x_306);
if (x_314 == 0)
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; 
lean_dec(x_312);
lean_dec(x_306);
lean_dec(x_297);
lean_dec(x_285);
x_315 = l_Lean_IR_EmitC_emitDeclAux___closed__2;
x_316 = lean_string_append(x_311, x_315);
x_317 = lean_string_append(x_316, x_310);
x_318 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_318, 0, x_280);
lean_ctor_set(x_318, 1, x_317);
x_319 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_319, 0, x_292);
lean_ctor_set(x_319, 1, x_293);
lean_ctor_set(x_319, 2, x_283);
lean_ctor_set(x_319, 3, x_284);
lean_ctor_set(x_319, 4, x_288);
lean_ctor_set(x_319, 5, x_289);
x_320 = l_Lean_IR_EmitC_emitFnBody___main(x_291, x_319, x_318);
if (lean_obj_tag(x_320) == 0)
{
lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; 
x_321 = lean_ctor_get(x_320, 1);
lean_inc(x_321);
if (lean_is_exclusive(x_320)) {
 lean_ctor_release(x_320, 0);
 lean_ctor_release(x_320, 1);
 x_322 = x_320;
} else {
 lean_dec_ref(x_320);
 x_322 = lean_box(0);
}
x_323 = l_PersistentHashMap_Stats_toString___closed__5;
x_324 = lean_string_append(x_321, x_323);
x_325 = lean_string_append(x_324, x_310);
if (lean_is_scalar(x_322)) {
 x_326 = lean_alloc_ctor(0, 2, 0);
} else {
 x_326 = x_322;
}
lean_ctor_set(x_326, 0, x_280);
lean_ctor_set(x_326, 1, x_325);
return x_326;
}
else
{
lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; 
x_327 = lean_ctor_get(x_320, 0);
lean_inc(x_327);
x_328 = lean_ctor_get(x_320, 1);
lean_inc(x_328);
if (lean_is_exclusive(x_320)) {
 lean_ctor_release(x_320, 0);
 lean_ctor_release(x_320, 1);
 x_329 = x_320;
} else {
 lean_dec_ref(x_320);
 x_329 = lean_box(0);
}
if (lean_is_scalar(x_329)) {
 x_330 = lean_alloc_ctor(1, 2, 0);
} else {
 x_330 = x_329;
}
lean_ctor_set(x_330, 0, x_327);
lean_ctor_set(x_330, 1, x_328);
return x_330;
}
}
else
{
uint8_t x_331; 
x_331 = l_Lean_IR_ExplicitBoxing_isBoxedName(x_285);
lean_dec(x_285);
if (x_331 == 0)
{
lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; 
lean_dec(x_312);
lean_dec(x_306);
lean_dec(x_297);
x_332 = l_Lean_IR_EmitC_emitDeclAux___closed__2;
x_333 = lean_string_append(x_311, x_332);
x_334 = lean_string_append(x_333, x_310);
x_335 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_335, 0, x_280);
lean_ctor_set(x_335, 1, x_334);
x_336 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_336, 0, x_292);
lean_ctor_set(x_336, 1, x_293);
lean_ctor_set(x_336, 2, x_283);
lean_ctor_set(x_336, 3, x_284);
lean_ctor_set(x_336, 4, x_288);
lean_ctor_set(x_336, 5, x_289);
x_337 = l_Lean_IR_EmitC_emitFnBody___main(x_291, x_336, x_335);
if (lean_obj_tag(x_337) == 0)
{
lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; 
x_338 = lean_ctor_get(x_337, 1);
lean_inc(x_338);
if (lean_is_exclusive(x_337)) {
 lean_ctor_release(x_337, 0);
 lean_ctor_release(x_337, 1);
 x_339 = x_337;
} else {
 lean_dec_ref(x_337);
 x_339 = lean_box(0);
}
x_340 = l_PersistentHashMap_Stats_toString___closed__5;
x_341 = lean_string_append(x_338, x_340);
x_342 = lean_string_append(x_341, x_310);
if (lean_is_scalar(x_339)) {
 x_343 = lean_alloc_ctor(0, 2, 0);
} else {
 x_343 = x_339;
}
lean_ctor_set(x_343, 0, x_280);
lean_ctor_set(x_343, 1, x_342);
return x_343;
}
else
{
lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; 
x_344 = lean_ctor_get(x_337, 0);
lean_inc(x_344);
x_345 = lean_ctor_get(x_337, 1);
lean_inc(x_345);
if (lean_is_exclusive(x_337)) {
 lean_ctor_release(x_337, 0);
 lean_ctor_release(x_337, 1);
 x_346 = x_337;
} else {
 lean_dec_ref(x_337);
 x_346 = lean_box(0);
}
if (lean_is_scalar(x_346)) {
 x_347 = lean_alloc_ctor(1, 2, 0);
} else {
 x_347 = x_346;
}
lean_ctor_set(x_347, 0, x_344);
lean_ctor_set(x_347, 1, x_345);
return x_347;
}
}
else
{
lean_object* x_348; 
lean_dec(x_311);
lean_inc(x_306);
x_348 = l_Nat_mforAux___main___at_Lean_IR_EmitC_emitDeclAux___spec__1(x_289, x_306, x_306, x_297, x_312);
lean_dec(x_297);
lean_dec(x_306);
if (lean_obj_tag(x_348) == 0)
{
lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; 
x_349 = lean_ctor_get(x_348, 1);
lean_inc(x_349);
if (lean_is_exclusive(x_348)) {
 lean_ctor_release(x_348, 0);
 lean_ctor_release(x_348, 1);
 x_350 = x_348;
} else {
 lean_dec_ref(x_348);
 x_350 = lean_box(0);
}
x_351 = l_Lean_IR_EmitC_emitDeclAux___closed__2;
x_352 = lean_string_append(x_349, x_351);
x_353 = lean_string_append(x_352, x_310);
if (lean_is_scalar(x_350)) {
 x_354 = lean_alloc_ctor(0, 2, 0);
} else {
 x_354 = x_350;
}
lean_ctor_set(x_354, 0, x_280);
lean_ctor_set(x_354, 1, x_353);
x_355 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_355, 0, x_292);
lean_ctor_set(x_355, 1, x_293);
lean_ctor_set(x_355, 2, x_283);
lean_ctor_set(x_355, 3, x_284);
lean_ctor_set(x_355, 4, x_288);
lean_ctor_set(x_355, 5, x_289);
x_356 = l_Lean_IR_EmitC_emitFnBody___main(x_291, x_355, x_354);
if (lean_obj_tag(x_356) == 0)
{
lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; 
x_357 = lean_ctor_get(x_356, 1);
lean_inc(x_357);
if (lean_is_exclusive(x_356)) {
 lean_ctor_release(x_356, 0);
 lean_ctor_release(x_356, 1);
 x_358 = x_356;
} else {
 lean_dec_ref(x_356);
 x_358 = lean_box(0);
}
x_359 = l_PersistentHashMap_Stats_toString___closed__5;
x_360 = lean_string_append(x_357, x_359);
x_361 = lean_string_append(x_360, x_310);
if (lean_is_scalar(x_358)) {
 x_362 = lean_alloc_ctor(0, 2, 0);
} else {
 x_362 = x_358;
}
lean_ctor_set(x_362, 0, x_280);
lean_ctor_set(x_362, 1, x_361);
return x_362;
}
else
{
lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; 
x_363 = lean_ctor_get(x_356, 0);
lean_inc(x_363);
x_364 = lean_ctor_get(x_356, 1);
lean_inc(x_364);
if (lean_is_exclusive(x_356)) {
 lean_ctor_release(x_356, 0);
 lean_ctor_release(x_356, 1);
 x_365 = x_356;
} else {
 lean_dec_ref(x_356);
 x_365 = lean_box(0);
}
if (lean_is_scalar(x_365)) {
 x_366 = lean_alloc_ctor(1, 2, 0);
} else {
 x_366 = x_365;
}
lean_ctor_set(x_366, 0, x_363);
lean_ctor_set(x_366, 1, x_364);
return x_366;
}
}
else
{
lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; 
lean_dec(x_293);
lean_dec(x_292);
lean_dec(x_291);
lean_dec(x_289);
lean_dec(x_288);
lean_dec(x_284);
lean_dec(x_283);
x_367 = lean_ctor_get(x_348, 0);
lean_inc(x_367);
x_368 = lean_ctor_get(x_348, 1);
lean_inc(x_368);
if (lean_is_exclusive(x_348)) {
 lean_ctor_release(x_348, 0);
 lean_ctor_release(x_348, 1);
 x_369 = x_348;
} else {
 lean_dec_ref(x_348);
 x_369 = lean_box(0);
}
if (lean_is_scalar(x_369)) {
 x_370 = lean_alloc_ctor(1, 2, 0);
} else {
 x_370 = x_369;
}
lean_ctor_set(x_370, 0, x_367);
lean_ctor_set(x_370, 1, x_368);
return x_370;
}
}
}
}
}
else
{
lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; 
lean_dec(x_297);
lean_dec(x_293);
lean_dec(x_292);
lean_dec(x_291);
lean_dec(x_289);
lean_dec(x_288);
lean_dec(x_285);
lean_dec(x_284);
lean_dec(x_283);
x_400 = lean_ctor_get(x_298, 0);
lean_inc(x_400);
x_401 = lean_ctor_get(x_298, 1);
lean_inc(x_401);
if (lean_is_exclusive(x_298)) {
 lean_ctor_release(x_298, 0);
 lean_ctor_release(x_298, 1);
 x_402 = x_298;
} else {
 lean_dec_ref(x_298);
 x_402 = lean_box(0);
}
if (lean_is_scalar(x_402)) {
 x_403 = lean_alloc_ctor(1, 2, 0);
} else {
 x_403 = x_402;
}
lean_ctor_set(x_403, 0, x_400);
lean_ctor_set(x_403, 1, x_401);
return x_403;
}
}
else
{
lean_object* x_404; 
lean_dec(x_285);
lean_dec(x_284);
lean_dec(x_283);
lean_dec(x_281);
lean_dec(x_2);
lean_dec(x_1);
x_404 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_404, 0, x_280);
lean_ctor_set(x_404, 1, x_279);
return x_404;
}
}
else
{
lean_object* x_405; 
lean_dec(x_285);
lean_dec(x_284);
lean_dec(x_283);
lean_dec(x_281);
lean_dec(x_2);
lean_dec(x_1);
x_405 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_405, 0, x_280);
lean_ctor_set(x_405, 1, x_279);
return x_405;
}
}
}
}
else
{
uint8_t x_409; 
lean_dec(x_2);
lean_dec(x_1);
x_409 = !lean_is_exclusive(x_4);
if (x_409 == 0)
{
return x_4;
}
else
{
lean_object* x_410; lean_object* x_411; lean_object* x_412; 
x_410 = lean_ctor_get(x_4, 0);
x_411 = lean_ctor_get(x_4, 1);
lean_inc(x_411);
lean_inc(x_410);
lean_dec(x_4);
x_412 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_412, 0, x_410);
lean_ctor_set(x_412, 1, x_411);
return x_412;
}
}
}
}
lean_object* l_Nat_mforAux___main___at_Lean_IR_EmitC_emitDeclAux___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Nat_mforAux___main___at_Lean_IR_EmitC_emitDeclAux___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Nat_mforAux___main___at_Lean_IR_EmitC_emitDeclAux___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Nat_mforAux___main___at_Lean_IR_EmitC_emitDeclAux___spec__2(x_1, x_2, x_3, x_4, x_5);
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
lean_object* l_List_mfor___main___at_Lean_IR_EmitC_emitFns___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_4; 
lean_dec(x_2);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
lean_dec(x_5);
x_6 = lean_box(0);
lean_ctor_set(x_3, 0, x_6);
return x_3;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_3, 1);
lean_inc(x_7);
lean_dec(x_3);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_dec(x_1);
lean_inc(x_2);
x_12 = l_Lean_IR_EmitC_emitDecl(x_10, x_2, x_3);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
lean_dec(x_14);
x_15 = lean_box(0);
lean_ctor_set(x_12, 0, x_15);
x_1 = x_11;
x_3 = x_12;
goto _start;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_dec(x_12);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
x_1 = x_11;
x_3 = x_19;
goto _start;
}
}
else
{
uint8_t x_21; 
lean_dec(x_11);
lean_dec(x_2);
x_21 = !lean_is_exclusive(x_12);
if (x_21 == 0)
{
return x_12;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_12, 0);
x_23 = lean_ctor_get(x_12, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_12);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
}
lean_object* l_Lean_IR_EmitC_emitFns(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_EmitC_getEnv(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_box(0);
lean_ctor_set(x_3, 0, x_6);
x_7 = l_Lean_IR_declMapExt;
x_8 = l_Lean_SimplePersistentEnvExtension_getEntries___rarg(x_7, x_5);
lean_dec(x_5);
x_9 = l_List_reverse___rarg(x_8);
x_10 = l_List_mfor___main___at_Lean_IR_EmitC_emitFns___spec__1(x_9, x_1, x_3);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_3);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
x_15 = l_Lean_IR_declMapExt;
x_16 = l_Lean_SimplePersistentEnvExtension_getEntries___rarg(x_15, x_11);
lean_dec(x_11);
x_17 = l_List_reverse___rarg(x_16);
x_18 = l_List_mfor___main___at_Lean_IR_EmitC_emitFns___spec__1(x_17, x_1, x_14);
return x_18;
}
}
else
{
uint8_t x_19; 
lean_dec(x_1);
x_19 = !lean_is_exclusive(x_3);
if (x_19 == 0)
{
return x_3;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_3, 0);
x_21 = lean_ctor_get(x_3, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_3);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
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
x_1 = lean_mk_string("lean_mark_persistent(");
return x_1;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitDeclInit___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("if (lean_io_result_is_error(w)) return w;");
return x_1;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitDeclInit___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" = lean_io_result_get_value(w);");
return x_1;
}
}
lean_object* l_Lean_IR_EmitC_emitDeclInit(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_EmitC_getEnv(x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_box(0);
lean_inc(x_7);
lean_ctor_set(x_4, 0, x_8);
x_9 = l_Lean_IR_Decl_name(x_1);
lean_inc(x_9);
x_10 = l_Lean_isIOUnitInitFn(x_6, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = l_Lean_IR_Decl_params(x_1);
x_12 = lean_array_get_size(x_11);
lean_dec(x_11);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_eq(x_12, x_13);
lean_dec(x_12);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_6);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_8);
lean_ctor_set(x_15, 1, x_7);
return x_15;
}
else
{
lean_object* x_16; 
lean_inc(x_9);
x_16 = lean_get_init_fn_name_for(x_6, x_9);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
lean_dec(x_7);
lean_inc(x_9);
x_17 = l_Lean_IR_EmitC_emitCName(x_9, x_2, x_4);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_17, 1);
x_20 = lean_ctor_get(x_17, 0);
lean_dec(x_20);
x_21 = l_Nat_mforAux___main___at_Lean_IR_EmitC_emitJmp___spec__1___closed__1;
x_22 = lean_string_append(x_19, x_21);
lean_ctor_set(x_17, 1, x_22);
lean_ctor_set(x_17, 0, x_8);
lean_inc(x_9);
x_23 = l_Lean_IR_EmitC_emitCInitName(x_9, x_2, x_17);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; uint8_t x_32; 
x_25 = lean_ctor_get(x_23, 1);
x_26 = lean_ctor_get(x_23, 0);
lean_dec(x_26);
x_27 = l_Lean_IR_EmitC_emitDeclInit___closed__1;
x_28 = lean_string_append(x_25, x_27);
x_29 = l_IO_println___rarg___closed__1;
x_30 = lean_string_append(x_28, x_29);
x_31 = l_Lean_IR_Decl_resultType(x_1);
x_32 = l_Lean_IR_IRType_isObj(x_31);
if (x_32 == 0)
{
lean_dec(x_9);
lean_ctor_set(x_23, 1, x_30);
lean_ctor_set(x_23, 0, x_8);
return x_23;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = l_Lean_IR_EmitC_emitDeclInit___closed__2;
x_34 = lean_string_append(x_30, x_33);
lean_ctor_set(x_23, 1, x_34);
lean_ctor_set(x_23, 0, x_8);
x_35 = l_Lean_IR_EmitC_emitCName(x_9, x_2, x_23);
if (lean_obj_tag(x_35) == 0)
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_37 = lean_ctor_get(x_35, 1);
x_38 = lean_ctor_get(x_35, 0);
lean_dec(x_38);
x_39 = l_Lean_IR_EmitC_emitInc___closed__1;
x_40 = lean_string_append(x_37, x_39);
x_41 = lean_string_append(x_40, x_29);
lean_ctor_set(x_35, 1, x_41);
lean_ctor_set(x_35, 0, x_8);
return x_35;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_42 = lean_ctor_get(x_35, 1);
lean_inc(x_42);
lean_dec(x_35);
x_43 = l_Lean_IR_EmitC_emitInc___closed__1;
x_44 = lean_string_append(x_42, x_43);
x_45 = lean_string_append(x_44, x_29);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_8);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
else
{
uint8_t x_47; 
x_47 = !lean_is_exclusive(x_35);
if (x_47 == 0)
{
return x_35;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_35, 0);
x_49 = lean_ctor_get(x_35, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_35);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; uint8_t x_57; 
x_51 = lean_ctor_get(x_23, 1);
lean_inc(x_51);
lean_dec(x_23);
x_52 = l_Lean_IR_EmitC_emitDeclInit___closed__1;
x_53 = lean_string_append(x_51, x_52);
x_54 = l_IO_println___rarg___closed__1;
x_55 = lean_string_append(x_53, x_54);
x_56 = l_Lean_IR_Decl_resultType(x_1);
x_57 = l_Lean_IR_IRType_isObj(x_56);
if (x_57 == 0)
{
lean_object* x_58; 
lean_dec(x_9);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_8);
lean_ctor_set(x_58, 1, x_55);
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_59 = l_Lean_IR_EmitC_emitDeclInit___closed__2;
x_60 = lean_string_append(x_55, x_59);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_8);
lean_ctor_set(x_61, 1, x_60);
x_62 = l_Lean_IR_EmitC_emitCName(x_9, x_2, x_61);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_64 = x_62;
} else {
 lean_dec_ref(x_62);
 x_64 = lean_box(0);
}
x_65 = l_Lean_IR_EmitC_emitInc___closed__1;
x_66 = lean_string_append(x_63, x_65);
x_67 = lean_string_append(x_66, x_54);
if (lean_is_scalar(x_64)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_64;
}
lean_ctor_set(x_68, 0, x_8);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_69 = lean_ctor_get(x_62, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_62, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_71 = x_62;
} else {
 lean_dec_ref(x_62);
 x_71 = lean_box(0);
}
if (lean_is_scalar(x_71)) {
 x_72 = lean_alloc_ctor(1, 2, 0);
} else {
 x_72 = x_71;
}
lean_ctor_set(x_72, 0, x_69);
lean_ctor_set(x_72, 1, x_70);
return x_72;
}
}
}
}
else
{
uint8_t x_73; 
lean_dec(x_9);
x_73 = !lean_is_exclusive(x_23);
if (x_73 == 0)
{
return x_23;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_23, 0);
x_75 = lean_ctor_get(x_23, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_23);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_77 = lean_ctor_get(x_17, 1);
lean_inc(x_77);
lean_dec(x_17);
x_78 = l_Nat_mforAux___main___at_Lean_IR_EmitC_emitJmp___spec__1___closed__1;
x_79 = lean_string_append(x_77, x_78);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_8);
lean_ctor_set(x_80, 1, x_79);
lean_inc(x_9);
x_81 = l_Lean_IR_EmitC_emitCInitName(x_9, x_2, x_80);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; uint8_t x_89; 
x_82 = lean_ctor_get(x_81, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_83 = x_81;
} else {
 lean_dec_ref(x_81);
 x_83 = lean_box(0);
}
x_84 = l_Lean_IR_EmitC_emitDeclInit___closed__1;
x_85 = lean_string_append(x_82, x_84);
x_86 = l_IO_println___rarg___closed__1;
x_87 = lean_string_append(x_85, x_86);
x_88 = l_Lean_IR_Decl_resultType(x_1);
x_89 = l_Lean_IR_IRType_isObj(x_88);
if (x_89 == 0)
{
lean_object* x_90; 
lean_dec(x_9);
if (lean_is_scalar(x_83)) {
 x_90 = lean_alloc_ctor(0, 2, 0);
} else {
 x_90 = x_83;
}
lean_ctor_set(x_90, 0, x_8);
lean_ctor_set(x_90, 1, x_87);
return x_90;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_91 = l_Lean_IR_EmitC_emitDeclInit___closed__2;
x_92 = lean_string_append(x_87, x_91);
if (lean_is_scalar(x_83)) {
 x_93 = lean_alloc_ctor(0, 2, 0);
} else {
 x_93 = x_83;
}
lean_ctor_set(x_93, 0, x_8);
lean_ctor_set(x_93, 1, x_92);
x_94 = l_Lean_IR_EmitC_emitCName(x_9, x_2, x_93);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_95 = lean_ctor_get(x_94, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 lean_ctor_release(x_94, 1);
 x_96 = x_94;
} else {
 lean_dec_ref(x_94);
 x_96 = lean_box(0);
}
x_97 = l_Lean_IR_EmitC_emitInc___closed__1;
x_98 = lean_string_append(x_95, x_97);
x_99 = lean_string_append(x_98, x_86);
if (lean_is_scalar(x_96)) {
 x_100 = lean_alloc_ctor(0, 2, 0);
} else {
 x_100 = x_96;
}
lean_ctor_set(x_100, 0, x_8);
lean_ctor_set(x_100, 1, x_99);
return x_100;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_101 = lean_ctor_get(x_94, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_94, 1);
lean_inc(x_102);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 lean_ctor_release(x_94, 1);
 x_103 = x_94;
} else {
 lean_dec_ref(x_94);
 x_103 = lean_box(0);
}
if (lean_is_scalar(x_103)) {
 x_104 = lean_alloc_ctor(1, 2, 0);
} else {
 x_104 = x_103;
}
lean_ctor_set(x_104, 0, x_101);
lean_ctor_set(x_104, 1, x_102);
return x_104;
}
}
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
lean_dec(x_9);
x_105 = lean_ctor_get(x_81, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_81, 1);
lean_inc(x_106);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_107 = x_81;
} else {
 lean_dec_ref(x_81);
 x_107 = lean_box(0);
}
if (lean_is_scalar(x_107)) {
 x_108 = lean_alloc_ctor(1, 2, 0);
} else {
 x_108 = x_107;
}
lean_ctor_set(x_108, 0, x_105);
lean_ctor_set(x_108, 1, x_106);
return x_108;
}
}
}
else
{
uint8_t x_109; 
lean_dec(x_9);
x_109 = !lean_is_exclusive(x_17);
if (x_109 == 0)
{
return x_17;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_17, 0);
x_111 = lean_ctor_get(x_17, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_17);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
return x_112;
}
}
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
lean_dec(x_4);
x_113 = lean_ctor_get(x_16, 0);
lean_inc(x_113);
lean_dec(x_16);
x_114 = l_Lean_IR_EmitC_emitMainFn___closed__11;
x_115 = lean_string_append(x_7, x_114);
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_8);
lean_ctor_set(x_116, 1, x_115);
x_117 = l_Lean_IR_EmitC_emitCName(x_113, x_2, x_116);
if (lean_obj_tag(x_117) == 0)
{
uint8_t x_118; 
x_118 = !lean_is_exclusive(x_117);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_119 = lean_ctor_get(x_117, 1);
x_120 = lean_ctor_get(x_117, 0);
lean_dec(x_120);
x_121 = l_Lean_IR_EmitC_emitMainFn___closed__4;
x_122 = lean_string_append(x_119, x_121);
x_123 = l_IO_println___rarg___closed__1;
x_124 = lean_string_append(x_122, x_123);
x_125 = l_Lean_IR_EmitC_emitDeclInit___closed__3;
x_126 = lean_string_append(x_124, x_125);
x_127 = lean_string_append(x_126, x_123);
lean_ctor_set(x_117, 1, x_127);
lean_ctor_set(x_117, 0, x_8);
lean_inc(x_9);
x_128 = l_Lean_IR_EmitC_emitCName(x_9, x_2, x_117);
if (lean_obj_tag(x_128) == 0)
{
uint8_t x_129; 
x_129 = !lean_is_exclusive(x_128);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; uint8_t x_135; uint8_t x_136; 
x_130 = lean_ctor_get(x_128, 1);
x_131 = lean_ctor_get(x_128, 0);
lean_dec(x_131);
x_132 = l_Lean_IR_EmitC_emitDeclInit___closed__4;
x_133 = lean_string_append(x_130, x_132);
x_134 = lean_string_append(x_133, x_123);
x_135 = l_Lean_IR_Decl_resultType(x_1);
x_136 = l_Lean_IR_IRType_isObj(x_135);
if (x_136 == 0)
{
lean_dec(x_9);
lean_ctor_set(x_128, 1, x_134);
lean_ctor_set(x_128, 0, x_8);
return x_128;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_137 = l_Lean_IR_EmitC_emitDeclInit___closed__2;
x_138 = lean_string_append(x_134, x_137);
lean_ctor_set(x_128, 1, x_138);
lean_ctor_set(x_128, 0, x_8);
x_139 = l_Lean_IR_EmitC_emitCName(x_9, x_2, x_128);
if (lean_obj_tag(x_139) == 0)
{
uint8_t x_140; 
x_140 = !lean_is_exclusive(x_139);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_141 = lean_ctor_get(x_139, 1);
x_142 = lean_ctor_get(x_139, 0);
lean_dec(x_142);
x_143 = l_Lean_IR_EmitC_emitInc___closed__1;
x_144 = lean_string_append(x_141, x_143);
x_145 = lean_string_append(x_144, x_123);
lean_ctor_set(x_139, 1, x_145);
lean_ctor_set(x_139, 0, x_8);
return x_139;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_146 = lean_ctor_get(x_139, 1);
lean_inc(x_146);
lean_dec(x_139);
x_147 = l_Lean_IR_EmitC_emitInc___closed__1;
x_148 = lean_string_append(x_146, x_147);
x_149 = lean_string_append(x_148, x_123);
x_150 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_150, 0, x_8);
lean_ctor_set(x_150, 1, x_149);
return x_150;
}
}
else
{
uint8_t x_151; 
x_151 = !lean_is_exclusive(x_139);
if (x_151 == 0)
{
return x_139;
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_152 = lean_ctor_get(x_139, 0);
x_153 = lean_ctor_get(x_139, 1);
lean_inc(x_153);
lean_inc(x_152);
lean_dec(x_139);
x_154 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_154, 0, x_152);
lean_ctor_set(x_154, 1, x_153);
return x_154;
}
}
}
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; uint8_t x_159; uint8_t x_160; 
x_155 = lean_ctor_get(x_128, 1);
lean_inc(x_155);
lean_dec(x_128);
x_156 = l_Lean_IR_EmitC_emitDeclInit___closed__4;
x_157 = lean_string_append(x_155, x_156);
x_158 = lean_string_append(x_157, x_123);
x_159 = l_Lean_IR_Decl_resultType(x_1);
x_160 = l_Lean_IR_IRType_isObj(x_159);
if (x_160 == 0)
{
lean_object* x_161; 
lean_dec(x_9);
x_161 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_161, 0, x_8);
lean_ctor_set(x_161, 1, x_158);
return x_161;
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_162 = l_Lean_IR_EmitC_emitDeclInit___closed__2;
x_163 = lean_string_append(x_158, x_162);
x_164 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_164, 0, x_8);
lean_ctor_set(x_164, 1, x_163);
x_165 = l_Lean_IR_EmitC_emitCName(x_9, x_2, x_164);
if (lean_obj_tag(x_165) == 0)
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
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
x_168 = l_Lean_IR_EmitC_emitInc___closed__1;
x_169 = lean_string_append(x_166, x_168);
x_170 = lean_string_append(x_169, x_123);
if (lean_is_scalar(x_167)) {
 x_171 = lean_alloc_ctor(0, 2, 0);
} else {
 x_171 = x_167;
}
lean_ctor_set(x_171, 0, x_8);
lean_ctor_set(x_171, 1, x_170);
return x_171;
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_172 = lean_ctor_get(x_165, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_165, 1);
lean_inc(x_173);
if (lean_is_exclusive(x_165)) {
 lean_ctor_release(x_165, 0);
 lean_ctor_release(x_165, 1);
 x_174 = x_165;
} else {
 lean_dec_ref(x_165);
 x_174 = lean_box(0);
}
if (lean_is_scalar(x_174)) {
 x_175 = lean_alloc_ctor(1, 2, 0);
} else {
 x_175 = x_174;
}
lean_ctor_set(x_175, 0, x_172);
lean_ctor_set(x_175, 1, x_173);
return x_175;
}
}
}
}
else
{
uint8_t x_176; 
lean_dec(x_9);
x_176 = !lean_is_exclusive(x_128);
if (x_176 == 0)
{
return x_128;
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_177 = lean_ctor_get(x_128, 0);
x_178 = lean_ctor_get(x_128, 1);
lean_inc(x_178);
lean_inc(x_177);
lean_dec(x_128);
x_179 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_179, 0, x_177);
lean_ctor_set(x_179, 1, x_178);
return x_179;
}
}
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_180 = lean_ctor_get(x_117, 1);
lean_inc(x_180);
lean_dec(x_117);
x_181 = l_Lean_IR_EmitC_emitMainFn___closed__4;
x_182 = lean_string_append(x_180, x_181);
x_183 = l_IO_println___rarg___closed__1;
x_184 = lean_string_append(x_182, x_183);
x_185 = l_Lean_IR_EmitC_emitDeclInit___closed__3;
x_186 = lean_string_append(x_184, x_185);
x_187 = lean_string_append(x_186, x_183);
x_188 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_188, 0, x_8);
lean_ctor_set(x_188, 1, x_187);
lean_inc(x_9);
x_189 = l_Lean_IR_EmitC_emitCName(x_9, x_2, x_188);
if (lean_obj_tag(x_189) == 0)
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; uint8_t x_195; uint8_t x_196; 
x_190 = lean_ctor_get(x_189, 1);
lean_inc(x_190);
if (lean_is_exclusive(x_189)) {
 lean_ctor_release(x_189, 0);
 lean_ctor_release(x_189, 1);
 x_191 = x_189;
} else {
 lean_dec_ref(x_189);
 x_191 = lean_box(0);
}
x_192 = l_Lean_IR_EmitC_emitDeclInit___closed__4;
x_193 = lean_string_append(x_190, x_192);
x_194 = lean_string_append(x_193, x_183);
x_195 = l_Lean_IR_Decl_resultType(x_1);
x_196 = l_Lean_IR_IRType_isObj(x_195);
if (x_196 == 0)
{
lean_object* x_197; 
lean_dec(x_9);
if (lean_is_scalar(x_191)) {
 x_197 = lean_alloc_ctor(0, 2, 0);
} else {
 x_197 = x_191;
}
lean_ctor_set(x_197, 0, x_8);
lean_ctor_set(x_197, 1, x_194);
return x_197;
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_198 = l_Lean_IR_EmitC_emitDeclInit___closed__2;
x_199 = lean_string_append(x_194, x_198);
if (lean_is_scalar(x_191)) {
 x_200 = lean_alloc_ctor(0, 2, 0);
} else {
 x_200 = x_191;
}
lean_ctor_set(x_200, 0, x_8);
lean_ctor_set(x_200, 1, x_199);
x_201 = l_Lean_IR_EmitC_emitCName(x_9, x_2, x_200);
if (lean_obj_tag(x_201) == 0)
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_202 = lean_ctor_get(x_201, 1);
lean_inc(x_202);
if (lean_is_exclusive(x_201)) {
 lean_ctor_release(x_201, 0);
 lean_ctor_release(x_201, 1);
 x_203 = x_201;
} else {
 lean_dec_ref(x_201);
 x_203 = lean_box(0);
}
x_204 = l_Lean_IR_EmitC_emitInc___closed__1;
x_205 = lean_string_append(x_202, x_204);
x_206 = lean_string_append(x_205, x_183);
if (lean_is_scalar(x_203)) {
 x_207 = lean_alloc_ctor(0, 2, 0);
} else {
 x_207 = x_203;
}
lean_ctor_set(x_207, 0, x_8);
lean_ctor_set(x_207, 1, x_206);
return x_207;
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; 
x_208 = lean_ctor_get(x_201, 0);
lean_inc(x_208);
x_209 = lean_ctor_get(x_201, 1);
lean_inc(x_209);
if (lean_is_exclusive(x_201)) {
 lean_ctor_release(x_201, 0);
 lean_ctor_release(x_201, 1);
 x_210 = x_201;
} else {
 lean_dec_ref(x_201);
 x_210 = lean_box(0);
}
if (lean_is_scalar(x_210)) {
 x_211 = lean_alloc_ctor(1, 2, 0);
} else {
 x_211 = x_210;
}
lean_ctor_set(x_211, 0, x_208);
lean_ctor_set(x_211, 1, x_209);
return x_211;
}
}
}
else
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; 
lean_dec(x_9);
x_212 = lean_ctor_get(x_189, 0);
lean_inc(x_212);
x_213 = lean_ctor_get(x_189, 1);
lean_inc(x_213);
if (lean_is_exclusive(x_189)) {
 lean_ctor_release(x_189, 0);
 lean_ctor_release(x_189, 1);
 x_214 = x_189;
} else {
 lean_dec_ref(x_189);
 x_214 = lean_box(0);
}
if (lean_is_scalar(x_214)) {
 x_215 = lean_alloc_ctor(1, 2, 0);
} else {
 x_215 = x_214;
}
lean_ctor_set(x_215, 0, x_212);
lean_ctor_set(x_215, 1, x_213);
return x_215;
}
}
}
else
{
uint8_t x_216; 
lean_dec(x_9);
x_216 = !lean_is_exclusive(x_117);
if (x_216 == 0)
{
return x_117;
}
else
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; 
x_217 = lean_ctor_get(x_117, 0);
x_218 = lean_ctor_get(x_117, 1);
lean_inc(x_218);
lean_inc(x_217);
lean_dec(x_117);
x_219 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_219, 0, x_217);
lean_ctor_set(x_219, 1, x_218);
return x_219;
}
}
}
}
}
else
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; 
lean_dec(x_4);
lean_dec(x_6);
x_220 = l_Lean_IR_EmitC_emitMainFn___closed__11;
x_221 = lean_string_append(x_7, x_220);
x_222 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_222, 0, x_8);
lean_ctor_set(x_222, 1, x_221);
x_223 = l_Lean_IR_EmitC_emitCName(x_9, x_2, x_222);
if (lean_obj_tag(x_223) == 0)
{
uint8_t x_224; 
x_224 = !lean_is_exclusive(x_223);
if (x_224 == 0)
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; 
x_225 = lean_ctor_get(x_223, 1);
x_226 = lean_ctor_get(x_223, 0);
lean_dec(x_226);
x_227 = l_Lean_IR_EmitC_emitMainFn___closed__4;
x_228 = lean_string_append(x_225, x_227);
x_229 = l_IO_println___rarg___closed__1;
x_230 = lean_string_append(x_228, x_229);
x_231 = l_Lean_IR_EmitC_emitDeclInit___closed__3;
x_232 = lean_string_append(x_230, x_231);
x_233 = lean_string_append(x_232, x_229);
lean_ctor_set(x_223, 1, x_233);
lean_ctor_set(x_223, 0, x_8);
return x_223;
}
else
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; 
x_234 = lean_ctor_get(x_223, 1);
lean_inc(x_234);
lean_dec(x_223);
x_235 = l_Lean_IR_EmitC_emitMainFn___closed__4;
x_236 = lean_string_append(x_234, x_235);
x_237 = l_IO_println___rarg___closed__1;
x_238 = lean_string_append(x_236, x_237);
x_239 = l_Lean_IR_EmitC_emitDeclInit___closed__3;
x_240 = lean_string_append(x_238, x_239);
x_241 = lean_string_append(x_240, x_237);
x_242 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_242, 0, x_8);
lean_ctor_set(x_242, 1, x_241);
return x_242;
}
}
else
{
uint8_t x_243; 
x_243 = !lean_is_exclusive(x_223);
if (x_243 == 0)
{
return x_223;
}
else
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; 
x_244 = lean_ctor_get(x_223, 0);
x_245 = lean_ctor_get(x_223, 1);
lean_inc(x_245);
lean_inc(x_244);
lean_dec(x_223);
x_246 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_246, 0, x_244);
lean_ctor_set(x_246, 1, x_245);
return x_246;
}
}
}
}
else
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; uint8_t x_252; 
x_247 = lean_ctor_get(x_4, 0);
x_248 = lean_ctor_get(x_4, 1);
lean_inc(x_248);
lean_inc(x_247);
lean_dec(x_4);
x_249 = lean_box(0);
lean_inc(x_248);
x_250 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_250, 0, x_249);
lean_ctor_set(x_250, 1, x_248);
x_251 = l_Lean_IR_Decl_name(x_1);
lean_inc(x_251);
x_252 = l_Lean_isIOUnitInitFn(x_247, x_251);
if (x_252 == 0)
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; uint8_t x_256; 
x_253 = l_Lean_IR_Decl_params(x_1);
x_254 = lean_array_get_size(x_253);
lean_dec(x_253);
x_255 = lean_unsigned_to_nat(0u);
x_256 = lean_nat_dec_eq(x_254, x_255);
lean_dec(x_254);
if (x_256 == 0)
{
lean_object* x_257; 
lean_dec(x_251);
lean_dec(x_250);
lean_dec(x_247);
x_257 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_257, 0, x_249);
lean_ctor_set(x_257, 1, x_248);
return x_257;
}
else
{
lean_object* x_258; 
lean_inc(x_251);
x_258 = lean_get_init_fn_name_for(x_247, x_251);
if (lean_obj_tag(x_258) == 0)
{
lean_object* x_259; 
lean_dec(x_248);
lean_inc(x_251);
x_259 = l_Lean_IR_EmitC_emitCName(x_251, x_2, x_250);
if (lean_obj_tag(x_259) == 0)
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; 
x_260 = lean_ctor_get(x_259, 1);
lean_inc(x_260);
if (lean_is_exclusive(x_259)) {
 lean_ctor_release(x_259, 0);
 lean_ctor_release(x_259, 1);
 x_261 = x_259;
} else {
 lean_dec_ref(x_259);
 x_261 = lean_box(0);
}
x_262 = l_Nat_mforAux___main___at_Lean_IR_EmitC_emitJmp___spec__1___closed__1;
x_263 = lean_string_append(x_260, x_262);
if (lean_is_scalar(x_261)) {
 x_264 = lean_alloc_ctor(0, 2, 0);
} else {
 x_264 = x_261;
}
lean_ctor_set(x_264, 0, x_249);
lean_ctor_set(x_264, 1, x_263);
lean_inc(x_251);
x_265 = l_Lean_IR_EmitC_emitCInitName(x_251, x_2, x_264);
if (lean_obj_tag(x_265) == 0)
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; uint8_t x_272; uint8_t x_273; 
x_266 = lean_ctor_get(x_265, 1);
lean_inc(x_266);
if (lean_is_exclusive(x_265)) {
 lean_ctor_release(x_265, 0);
 lean_ctor_release(x_265, 1);
 x_267 = x_265;
} else {
 lean_dec_ref(x_265);
 x_267 = lean_box(0);
}
x_268 = l_Lean_IR_EmitC_emitDeclInit___closed__1;
x_269 = lean_string_append(x_266, x_268);
x_270 = l_IO_println___rarg___closed__1;
x_271 = lean_string_append(x_269, x_270);
x_272 = l_Lean_IR_Decl_resultType(x_1);
x_273 = l_Lean_IR_IRType_isObj(x_272);
if (x_273 == 0)
{
lean_object* x_274; 
lean_dec(x_251);
if (lean_is_scalar(x_267)) {
 x_274 = lean_alloc_ctor(0, 2, 0);
} else {
 x_274 = x_267;
}
lean_ctor_set(x_274, 0, x_249);
lean_ctor_set(x_274, 1, x_271);
return x_274;
}
else
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; 
x_275 = l_Lean_IR_EmitC_emitDeclInit___closed__2;
x_276 = lean_string_append(x_271, x_275);
if (lean_is_scalar(x_267)) {
 x_277 = lean_alloc_ctor(0, 2, 0);
} else {
 x_277 = x_267;
}
lean_ctor_set(x_277, 0, x_249);
lean_ctor_set(x_277, 1, x_276);
x_278 = l_Lean_IR_EmitC_emitCName(x_251, x_2, x_277);
if (lean_obj_tag(x_278) == 0)
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; 
x_279 = lean_ctor_get(x_278, 1);
lean_inc(x_279);
if (lean_is_exclusive(x_278)) {
 lean_ctor_release(x_278, 0);
 lean_ctor_release(x_278, 1);
 x_280 = x_278;
} else {
 lean_dec_ref(x_278);
 x_280 = lean_box(0);
}
x_281 = l_Lean_IR_EmitC_emitInc___closed__1;
x_282 = lean_string_append(x_279, x_281);
x_283 = lean_string_append(x_282, x_270);
if (lean_is_scalar(x_280)) {
 x_284 = lean_alloc_ctor(0, 2, 0);
} else {
 x_284 = x_280;
}
lean_ctor_set(x_284, 0, x_249);
lean_ctor_set(x_284, 1, x_283);
return x_284;
}
else
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; 
x_285 = lean_ctor_get(x_278, 0);
lean_inc(x_285);
x_286 = lean_ctor_get(x_278, 1);
lean_inc(x_286);
if (lean_is_exclusive(x_278)) {
 lean_ctor_release(x_278, 0);
 lean_ctor_release(x_278, 1);
 x_287 = x_278;
} else {
 lean_dec_ref(x_278);
 x_287 = lean_box(0);
}
if (lean_is_scalar(x_287)) {
 x_288 = lean_alloc_ctor(1, 2, 0);
} else {
 x_288 = x_287;
}
lean_ctor_set(x_288, 0, x_285);
lean_ctor_set(x_288, 1, x_286);
return x_288;
}
}
}
else
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; 
lean_dec(x_251);
x_289 = lean_ctor_get(x_265, 0);
lean_inc(x_289);
x_290 = lean_ctor_get(x_265, 1);
lean_inc(x_290);
if (lean_is_exclusive(x_265)) {
 lean_ctor_release(x_265, 0);
 lean_ctor_release(x_265, 1);
 x_291 = x_265;
} else {
 lean_dec_ref(x_265);
 x_291 = lean_box(0);
}
if (lean_is_scalar(x_291)) {
 x_292 = lean_alloc_ctor(1, 2, 0);
} else {
 x_292 = x_291;
}
lean_ctor_set(x_292, 0, x_289);
lean_ctor_set(x_292, 1, x_290);
return x_292;
}
}
else
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; 
lean_dec(x_251);
x_293 = lean_ctor_get(x_259, 0);
lean_inc(x_293);
x_294 = lean_ctor_get(x_259, 1);
lean_inc(x_294);
if (lean_is_exclusive(x_259)) {
 lean_ctor_release(x_259, 0);
 lean_ctor_release(x_259, 1);
 x_295 = x_259;
} else {
 lean_dec_ref(x_259);
 x_295 = lean_box(0);
}
if (lean_is_scalar(x_295)) {
 x_296 = lean_alloc_ctor(1, 2, 0);
} else {
 x_296 = x_295;
}
lean_ctor_set(x_296, 0, x_293);
lean_ctor_set(x_296, 1, x_294);
return x_296;
}
}
else
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; 
lean_dec(x_250);
x_297 = lean_ctor_get(x_258, 0);
lean_inc(x_297);
lean_dec(x_258);
x_298 = l_Lean_IR_EmitC_emitMainFn___closed__11;
x_299 = lean_string_append(x_248, x_298);
x_300 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_300, 0, x_249);
lean_ctor_set(x_300, 1, x_299);
x_301 = l_Lean_IR_EmitC_emitCName(x_297, x_2, x_300);
if (lean_obj_tag(x_301) == 0)
{
lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; 
x_302 = lean_ctor_get(x_301, 1);
lean_inc(x_302);
if (lean_is_exclusive(x_301)) {
 lean_ctor_release(x_301, 0);
 lean_ctor_release(x_301, 1);
 x_303 = x_301;
} else {
 lean_dec_ref(x_301);
 x_303 = lean_box(0);
}
x_304 = l_Lean_IR_EmitC_emitMainFn___closed__4;
x_305 = lean_string_append(x_302, x_304);
x_306 = l_IO_println___rarg___closed__1;
x_307 = lean_string_append(x_305, x_306);
x_308 = l_Lean_IR_EmitC_emitDeclInit___closed__3;
x_309 = lean_string_append(x_307, x_308);
x_310 = lean_string_append(x_309, x_306);
if (lean_is_scalar(x_303)) {
 x_311 = lean_alloc_ctor(0, 2, 0);
} else {
 x_311 = x_303;
}
lean_ctor_set(x_311, 0, x_249);
lean_ctor_set(x_311, 1, x_310);
lean_inc(x_251);
x_312 = l_Lean_IR_EmitC_emitCName(x_251, x_2, x_311);
if (lean_obj_tag(x_312) == 0)
{
lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; uint8_t x_318; uint8_t x_319; 
x_313 = lean_ctor_get(x_312, 1);
lean_inc(x_313);
if (lean_is_exclusive(x_312)) {
 lean_ctor_release(x_312, 0);
 lean_ctor_release(x_312, 1);
 x_314 = x_312;
} else {
 lean_dec_ref(x_312);
 x_314 = lean_box(0);
}
x_315 = l_Lean_IR_EmitC_emitDeclInit___closed__4;
x_316 = lean_string_append(x_313, x_315);
x_317 = lean_string_append(x_316, x_306);
x_318 = l_Lean_IR_Decl_resultType(x_1);
x_319 = l_Lean_IR_IRType_isObj(x_318);
if (x_319 == 0)
{
lean_object* x_320; 
lean_dec(x_251);
if (lean_is_scalar(x_314)) {
 x_320 = lean_alloc_ctor(0, 2, 0);
} else {
 x_320 = x_314;
}
lean_ctor_set(x_320, 0, x_249);
lean_ctor_set(x_320, 1, x_317);
return x_320;
}
else
{
lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; 
x_321 = l_Lean_IR_EmitC_emitDeclInit___closed__2;
x_322 = lean_string_append(x_317, x_321);
if (lean_is_scalar(x_314)) {
 x_323 = lean_alloc_ctor(0, 2, 0);
} else {
 x_323 = x_314;
}
lean_ctor_set(x_323, 0, x_249);
lean_ctor_set(x_323, 1, x_322);
x_324 = l_Lean_IR_EmitC_emitCName(x_251, x_2, x_323);
if (lean_obj_tag(x_324) == 0)
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; 
x_325 = lean_ctor_get(x_324, 1);
lean_inc(x_325);
if (lean_is_exclusive(x_324)) {
 lean_ctor_release(x_324, 0);
 lean_ctor_release(x_324, 1);
 x_326 = x_324;
} else {
 lean_dec_ref(x_324);
 x_326 = lean_box(0);
}
x_327 = l_Lean_IR_EmitC_emitInc___closed__1;
x_328 = lean_string_append(x_325, x_327);
x_329 = lean_string_append(x_328, x_306);
if (lean_is_scalar(x_326)) {
 x_330 = lean_alloc_ctor(0, 2, 0);
} else {
 x_330 = x_326;
}
lean_ctor_set(x_330, 0, x_249);
lean_ctor_set(x_330, 1, x_329);
return x_330;
}
else
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; 
x_331 = lean_ctor_get(x_324, 0);
lean_inc(x_331);
x_332 = lean_ctor_get(x_324, 1);
lean_inc(x_332);
if (lean_is_exclusive(x_324)) {
 lean_ctor_release(x_324, 0);
 lean_ctor_release(x_324, 1);
 x_333 = x_324;
} else {
 lean_dec_ref(x_324);
 x_333 = lean_box(0);
}
if (lean_is_scalar(x_333)) {
 x_334 = lean_alloc_ctor(1, 2, 0);
} else {
 x_334 = x_333;
}
lean_ctor_set(x_334, 0, x_331);
lean_ctor_set(x_334, 1, x_332);
return x_334;
}
}
}
else
{
lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; 
lean_dec(x_251);
x_335 = lean_ctor_get(x_312, 0);
lean_inc(x_335);
x_336 = lean_ctor_get(x_312, 1);
lean_inc(x_336);
if (lean_is_exclusive(x_312)) {
 lean_ctor_release(x_312, 0);
 lean_ctor_release(x_312, 1);
 x_337 = x_312;
} else {
 lean_dec_ref(x_312);
 x_337 = lean_box(0);
}
if (lean_is_scalar(x_337)) {
 x_338 = lean_alloc_ctor(1, 2, 0);
} else {
 x_338 = x_337;
}
lean_ctor_set(x_338, 0, x_335);
lean_ctor_set(x_338, 1, x_336);
return x_338;
}
}
else
{
lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; 
lean_dec(x_251);
x_339 = lean_ctor_get(x_301, 0);
lean_inc(x_339);
x_340 = lean_ctor_get(x_301, 1);
lean_inc(x_340);
if (lean_is_exclusive(x_301)) {
 lean_ctor_release(x_301, 0);
 lean_ctor_release(x_301, 1);
 x_341 = x_301;
} else {
 lean_dec_ref(x_301);
 x_341 = lean_box(0);
}
if (lean_is_scalar(x_341)) {
 x_342 = lean_alloc_ctor(1, 2, 0);
} else {
 x_342 = x_341;
}
lean_ctor_set(x_342, 0, x_339);
lean_ctor_set(x_342, 1, x_340);
return x_342;
}
}
}
}
else
{
lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; 
lean_dec(x_250);
lean_dec(x_247);
x_343 = l_Lean_IR_EmitC_emitMainFn___closed__11;
x_344 = lean_string_append(x_248, x_343);
x_345 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_345, 0, x_249);
lean_ctor_set(x_345, 1, x_344);
x_346 = l_Lean_IR_EmitC_emitCName(x_251, x_2, x_345);
if (lean_obj_tag(x_346) == 0)
{
lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; 
x_347 = lean_ctor_get(x_346, 1);
lean_inc(x_347);
if (lean_is_exclusive(x_346)) {
 lean_ctor_release(x_346, 0);
 lean_ctor_release(x_346, 1);
 x_348 = x_346;
} else {
 lean_dec_ref(x_346);
 x_348 = lean_box(0);
}
x_349 = l_Lean_IR_EmitC_emitMainFn___closed__4;
x_350 = lean_string_append(x_347, x_349);
x_351 = l_IO_println___rarg___closed__1;
x_352 = lean_string_append(x_350, x_351);
x_353 = l_Lean_IR_EmitC_emitDeclInit___closed__3;
x_354 = lean_string_append(x_352, x_353);
x_355 = lean_string_append(x_354, x_351);
if (lean_is_scalar(x_348)) {
 x_356 = lean_alloc_ctor(0, 2, 0);
} else {
 x_356 = x_348;
}
lean_ctor_set(x_356, 0, x_249);
lean_ctor_set(x_356, 1, x_355);
return x_356;
}
else
{
lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; 
x_357 = lean_ctor_get(x_346, 0);
lean_inc(x_357);
x_358 = lean_ctor_get(x_346, 1);
lean_inc(x_358);
if (lean_is_exclusive(x_346)) {
 lean_ctor_release(x_346, 0);
 lean_ctor_release(x_346, 1);
 x_359 = x_346;
} else {
 lean_dec_ref(x_346);
 x_359 = lean_box(0);
}
if (lean_is_scalar(x_359)) {
 x_360 = lean_alloc_ctor(1, 2, 0);
} else {
 x_360 = x_359;
}
lean_ctor_set(x_360, 0, x_357);
lean_ctor_set(x_360, 1, x_358);
return x_360;
}
}
}
}
else
{
uint8_t x_361; 
x_361 = !lean_is_exclusive(x_4);
if (x_361 == 0)
{
return x_4;
}
else
{
lean_object* x_362; lean_object* x_363; lean_object* x_364; 
x_362 = lean_ctor_get(x_4, 0);
x_363 = lean_ctor_get(x_4, 1);
lean_inc(x_363);
lean_inc(x_362);
lean_dec(x_4);
x_364 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_364, 0, x_362);
lean_ctor_set(x_364, 1, x_363);
return x_364;
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
lean_object* _init_l_Array_mforAux___main___at_Lean_IR_EmitC_emitInitFn___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("lean_object* initialize_");
return x_1;
}
}
lean_object* _init_l_Array_mforAux___main___at_Lean_IR_EmitC_emitInitFn___spec__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("(lean_object*);");
return x_1;
}
}
lean_object* l_Array_mforAux___main___at_Lean_IR_EmitC_emitInitFn___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_1);
x_6 = lean_nat_dec_lt(x_2, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
uint8_t x_7; 
lean_dec(x_2);
x_7 = !lean_is_exclusive(x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_4, 0);
lean_dec(x_8);
x_9 = lean_box(0);
lean_ctor_set(x_4, 0, x_9);
return x_4;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
lean_dec(x_4);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_4);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_14 = lean_ctor_get(x_4, 1);
x_15 = lean_ctor_get(x_4, 0);
lean_dec(x_15);
x_16 = lean_array_fget(x_1, x_2);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_2, x_17);
lean_dec(x_2);
x_19 = l_String_splitAux___main___closed__1;
x_20 = l_Lean_Name_mangle(x_16, x_19);
x_21 = l_Array_mforAux___main___at_Lean_IR_EmitC_emitInitFn___spec__1___closed__1;
x_22 = lean_string_append(x_21, x_20);
lean_dec(x_20);
x_23 = l_Array_mforAux___main___at_Lean_IR_EmitC_emitInitFn___spec__1___closed__2;
x_24 = lean_string_append(x_22, x_23);
x_25 = lean_string_append(x_14, x_24);
lean_dec(x_24);
x_26 = l_IO_println___rarg___closed__1;
x_27 = lean_string_append(x_25, x_26);
x_28 = lean_box(0);
lean_ctor_set(x_4, 1, x_27);
lean_ctor_set(x_4, 0, x_28);
x_2 = x_18;
goto _start;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_30 = lean_ctor_get(x_4, 1);
lean_inc(x_30);
lean_dec(x_4);
x_31 = lean_array_fget(x_1, x_2);
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_nat_add(x_2, x_32);
lean_dec(x_2);
x_34 = l_String_splitAux___main___closed__1;
x_35 = l_Lean_Name_mangle(x_31, x_34);
x_36 = l_Array_mforAux___main___at_Lean_IR_EmitC_emitInitFn___spec__1___closed__1;
x_37 = lean_string_append(x_36, x_35);
lean_dec(x_35);
x_38 = l_Array_mforAux___main___at_Lean_IR_EmitC_emitInitFn___spec__1___closed__2;
x_39 = lean_string_append(x_37, x_38);
x_40 = lean_string_append(x_30, x_39);
lean_dec(x_39);
x_41 = l_IO_println___rarg___closed__1;
x_42 = lean_string_append(x_40, x_41);
x_43 = lean_box(0);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_42);
x_2 = x_33;
x_4 = x_44;
goto _start;
}
}
}
}
lean_object* l_Array_mforAux___main___at_Lean_IR_EmitC_emitInitFn___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_2);
x_7 = lean_nat_dec_lt(x_3, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_3);
lean_dec(x_1);
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_5, 0);
lean_dec(x_9);
x_10 = lean_box(0);
lean_ctor_set(x_5, 0, x_10);
return x_5;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
lean_dec(x_5);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_14 = lean_array_fget(x_2, x_3);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_3, x_15);
lean_dec(x_3);
x_17 = l_String_splitAux___main___closed__1;
x_18 = l_Lean_Name_mangle(x_14, x_17);
x_19 = l_Lean_IR_EmitC_emitMainFn___closed__3;
x_20 = lean_string_append(x_19, x_18);
lean_dec(x_18);
x_21 = l_Lean_IR_EmitC_emitMainFn___closed__4;
x_22 = lean_string_append(x_20, x_21);
lean_inc(x_1);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_1);
x_24 = l_List_mfor___main___at_Lean_IR_EmitC_emitMainFn___spec__2(x_23, x_4, x_5);
lean_dec(x_23);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_24, 0);
lean_dec(x_26);
x_27 = lean_box(0);
lean_ctor_set(x_24, 0, x_27);
x_3 = x_16;
x_5 = x_24;
goto _start;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_24, 1);
lean_inc(x_29);
lean_dec(x_24);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
x_3 = x_16;
x_5 = x_31;
goto _start;
}
}
else
{
uint8_t x_33; 
lean_dec(x_16);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_24);
if (x_33 == 0)
{
return x_24;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_24, 0);
x_35 = lean_ctor_get(x_24, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_24);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
}
lean_object* l_List_mfor___main___at_Lean_IR_EmitC_emitInitFn___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
lean_dec(x_5);
x_6 = lean_box(0);
lean_ctor_set(x_3, 0, x_6);
return x_3;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_3, 1);
lean_inc(x_7);
lean_dec(x_3);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 1);
x_12 = l_Lean_IR_EmitC_emitDeclInit(x_10, x_2, x_3);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
lean_dec(x_14);
x_15 = lean_box(0);
lean_ctor_set(x_12, 0, x_15);
x_1 = x_11;
x_3 = x_12;
goto _start;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_dec(x_12);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
x_1 = x_11;
x_3 = x_19;
goto _start;
}
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_12);
if (x_21 == 0)
{
return x_12;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_12, 0);
x_23 = lean_ctor_get(x_12, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_12);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_IR_EmitC_emitDeclInit___closed__3;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitInitFn___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_G_initialized = true;");
return x_1;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitInitFn___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_EmitC_emitInitFn___closed__3;
x_2 = l_Lean_IR_EmitC_emitInitFn___closed__2;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitInitFn___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("if (_G_initialized) return w;");
return x_1;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitInitFn___closed__6() {
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
lean_object* _init_l_Lean_IR_EmitC_emitInitFn___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("static bool _G_initialized = false;");
return x_1;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitInitFn___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("return w;");
return x_1;
}
}
lean_object* _init_l_Lean_IR_EmitC_emitInitFn___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_EmitC_emitInitFn___closed__8;
x_2 = l_Lean_IR_EmitC_emitMainFn___closed__14;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_IR_EmitC_emitInitFn(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_EmitC_getEnv(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_box(0);
lean_ctor_set(x_3, 0, x_6);
x_7 = l_Lean_IR_EmitC_getModName(x_1, x_3);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_7, 0);
lean_ctor_set(x_7, 0, x_6);
x_10 = l_Lean_Environment_imports(x_5);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Array_mforAux___main___at_Lean_IR_EmitC_emitInitFn___spec__1(x_10, x_11, x_1, x_7);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_14 = lean_ctor_get(x_12, 0);
lean_dec(x_14);
lean_ctor_set(x_12, 0, x_6);
x_15 = l_String_splitAux___main___closed__1;
x_16 = l_Lean_Name_mangle(x_9, x_15);
x_17 = l_Array_mforAux___main___at_Lean_IR_EmitC_emitInitFn___spec__1___closed__1;
x_18 = lean_string_append(x_17, x_16);
lean_dec(x_16);
x_19 = l_Lean_IR_EmitC_emitInitFn___closed__1;
x_20 = lean_string_append(x_18, x_19);
x_21 = l_Lean_IR_EmitC_emitInitFn___closed__6;
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lean_IR_EmitC_emitInitFn___closed__7;
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
x_25 = l_List_mfor___main___at_Lean_IR_EmitC_emitMainFn___spec__2(x_24, x_1, x_12);
lean_dec(x_24);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_25, 0);
lean_dec(x_27);
lean_ctor_set(x_25, 0, x_6);
x_28 = l_Lean_IR_EmitC_emitInitFn___closed__2;
x_29 = l_Array_mforAux___main___at_Lean_IR_EmitC_emitInitFn___spec__2(x_28, x_10, x_11, x_1, x_25);
lean_dec(x_10);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_31 = lean_ctor_get(x_29, 0);
lean_dec(x_31);
lean_ctor_set(x_29, 0, x_6);
x_32 = l_Lean_IR_declMapExt;
x_33 = l_Lean_SimplePersistentEnvExtension_getEntries___rarg(x_32, x_5);
lean_dec(x_5);
x_34 = l_List_reverse___rarg(x_33);
x_35 = l_List_mfor___main___at_Lean_IR_EmitC_emitInitFn___spec__3(x_34, x_1, x_29);
lean_dec(x_34);
if (lean_obj_tag(x_35) == 0)
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_35, 0);
lean_dec(x_37);
lean_ctor_set(x_35, 0, x_6);
x_38 = l_Lean_IR_EmitC_emitInitFn___closed__9;
x_39 = l_List_mfor___main___at_Lean_IR_EmitC_emitMainFn___spec__2(x_38, x_1, x_35);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_35, 1);
lean_inc(x_40);
lean_dec(x_35);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_6);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_Lean_IR_EmitC_emitInitFn___closed__9;
x_43 = l_List_mfor___main___at_Lean_IR_EmitC_emitMainFn___spec__2(x_42, x_1, x_41);
return x_43;
}
}
else
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_35);
if (x_44 == 0)
{
return x_35;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_35, 0);
x_46 = lean_ctor_get(x_35, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_35);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_48 = lean_ctor_get(x_29, 1);
lean_inc(x_48);
lean_dec(x_29);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_6);
lean_ctor_set(x_49, 1, x_48);
x_50 = l_Lean_IR_declMapExt;
x_51 = l_Lean_SimplePersistentEnvExtension_getEntries___rarg(x_50, x_5);
lean_dec(x_5);
x_52 = l_List_reverse___rarg(x_51);
x_53 = l_List_mfor___main___at_Lean_IR_EmitC_emitInitFn___spec__3(x_52, x_1, x_49);
lean_dec(x_52);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_55 = x_53;
} else {
 lean_dec_ref(x_53);
 x_55 = lean_box(0);
}
if (lean_is_scalar(x_55)) {
 x_56 = lean_alloc_ctor(0, 2, 0);
} else {
 x_56 = x_55;
}
lean_ctor_set(x_56, 0, x_6);
lean_ctor_set(x_56, 1, x_54);
x_57 = l_Lean_IR_EmitC_emitInitFn___closed__9;
x_58 = l_List_mfor___main___at_Lean_IR_EmitC_emitMainFn___spec__2(x_57, x_1, x_56);
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_59 = lean_ctor_get(x_53, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_53, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_61 = x_53;
} else {
 lean_dec_ref(x_53);
 x_61 = lean_box(0);
}
if (lean_is_scalar(x_61)) {
 x_62 = lean_alloc_ctor(1, 2, 0);
} else {
 x_62 = x_61;
}
lean_ctor_set(x_62, 0, x_59);
lean_ctor_set(x_62, 1, x_60);
return x_62;
}
}
}
else
{
uint8_t x_63; 
lean_dec(x_5);
x_63 = !lean_is_exclusive(x_29);
if (x_63 == 0)
{
return x_29;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_29, 0);
x_65 = lean_ctor_get(x_29, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_29);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_67 = lean_ctor_get(x_25, 1);
lean_inc(x_67);
lean_dec(x_25);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_6);
lean_ctor_set(x_68, 1, x_67);
x_69 = l_Lean_IR_EmitC_emitInitFn___closed__2;
x_70 = l_Array_mforAux___main___at_Lean_IR_EmitC_emitInitFn___spec__2(x_69, x_10, x_11, x_1, x_68);
lean_dec(x_10);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_71 = lean_ctor_get(x_70, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_72 = x_70;
} else {
 lean_dec_ref(x_70);
 x_72 = lean_box(0);
}
if (lean_is_scalar(x_72)) {
 x_73 = lean_alloc_ctor(0, 2, 0);
} else {
 x_73 = x_72;
}
lean_ctor_set(x_73, 0, x_6);
lean_ctor_set(x_73, 1, x_71);
x_74 = l_Lean_IR_declMapExt;
x_75 = l_Lean_SimplePersistentEnvExtension_getEntries___rarg(x_74, x_5);
lean_dec(x_5);
x_76 = l_List_reverse___rarg(x_75);
x_77 = l_List_mfor___main___at_Lean_IR_EmitC_emitInitFn___spec__3(x_76, x_1, x_73);
lean_dec(x_76);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_78 = lean_ctor_get(x_77, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 x_79 = x_77;
} else {
 lean_dec_ref(x_77);
 x_79 = lean_box(0);
}
if (lean_is_scalar(x_79)) {
 x_80 = lean_alloc_ctor(0, 2, 0);
} else {
 x_80 = x_79;
}
lean_ctor_set(x_80, 0, x_6);
lean_ctor_set(x_80, 1, x_78);
x_81 = l_Lean_IR_EmitC_emitInitFn___closed__9;
x_82 = l_List_mfor___main___at_Lean_IR_EmitC_emitMainFn___spec__2(x_81, x_1, x_80);
return x_82;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_83 = lean_ctor_get(x_77, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_77, 1);
lean_inc(x_84);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 x_85 = x_77;
} else {
 lean_dec_ref(x_77);
 x_85 = lean_box(0);
}
if (lean_is_scalar(x_85)) {
 x_86 = lean_alloc_ctor(1, 2, 0);
} else {
 x_86 = x_85;
}
lean_ctor_set(x_86, 0, x_83);
lean_ctor_set(x_86, 1, x_84);
return x_86;
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_5);
x_87 = lean_ctor_get(x_70, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_70, 1);
lean_inc(x_88);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_89 = x_70;
} else {
 lean_dec_ref(x_70);
 x_89 = lean_box(0);
}
if (lean_is_scalar(x_89)) {
 x_90 = lean_alloc_ctor(1, 2, 0);
} else {
 x_90 = x_89;
}
lean_ctor_set(x_90, 0, x_87);
lean_ctor_set(x_90, 1, x_88);
return x_90;
}
}
}
else
{
uint8_t x_91; 
lean_dec(x_10);
lean_dec(x_5);
x_91 = !lean_is_exclusive(x_25);
if (x_91 == 0)
{
return x_25;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_25, 0);
x_93 = lean_ctor_get(x_25, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_25);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_95 = lean_ctor_get(x_12, 1);
lean_inc(x_95);
lean_dec(x_12);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_6);
lean_ctor_set(x_96, 1, x_95);
x_97 = l_String_splitAux___main___closed__1;
x_98 = l_Lean_Name_mangle(x_9, x_97);
x_99 = l_Array_mforAux___main___at_Lean_IR_EmitC_emitInitFn___spec__1___closed__1;
x_100 = lean_string_append(x_99, x_98);
lean_dec(x_98);
x_101 = l_Lean_IR_EmitC_emitInitFn___closed__1;
x_102 = lean_string_append(x_100, x_101);
x_103 = l_Lean_IR_EmitC_emitInitFn___closed__6;
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
x_105 = l_Lean_IR_EmitC_emitInitFn___closed__7;
x_106 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_104);
x_107 = l_List_mfor___main___at_Lean_IR_EmitC_emitMainFn___spec__2(x_106, x_1, x_96);
lean_dec(x_106);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_108 = lean_ctor_get(x_107, 1);
lean_inc(x_108);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_109 = x_107;
} else {
 lean_dec_ref(x_107);
 x_109 = lean_box(0);
}
if (lean_is_scalar(x_109)) {
 x_110 = lean_alloc_ctor(0, 2, 0);
} else {
 x_110 = x_109;
}
lean_ctor_set(x_110, 0, x_6);
lean_ctor_set(x_110, 1, x_108);
x_111 = l_Lean_IR_EmitC_emitInitFn___closed__2;
x_112 = l_Array_mforAux___main___at_Lean_IR_EmitC_emitInitFn___spec__2(x_111, x_10, x_11, x_1, x_110);
lean_dec(x_10);
if (lean_obj_tag(x_112) == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_113 = lean_ctor_get(x_112, 1);
lean_inc(x_113);
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 lean_ctor_release(x_112, 1);
 x_114 = x_112;
} else {
 lean_dec_ref(x_112);
 x_114 = lean_box(0);
}
if (lean_is_scalar(x_114)) {
 x_115 = lean_alloc_ctor(0, 2, 0);
} else {
 x_115 = x_114;
}
lean_ctor_set(x_115, 0, x_6);
lean_ctor_set(x_115, 1, x_113);
x_116 = l_Lean_IR_declMapExt;
x_117 = l_Lean_SimplePersistentEnvExtension_getEntries___rarg(x_116, x_5);
lean_dec(x_5);
x_118 = l_List_reverse___rarg(x_117);
x_119 = l_List_mfor___main___at_Lean_IR_EmitC_emitInitFn___spec__3(x_118, x_1, x_115);
lean_dec(x_118);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
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
if (lean_is_scalar(x_121)) {
 x_122 = lean_alloc_ctor(0, 2, 0);
} else {
 x_122 = x_121;
}
lean_ctor_set(x_122, 0, x_6);
lean_ctor_set(x_122, 1, x_120);
x_123 = l_Lean_IR_EmitC_emitInitFn___closed__9;
x_124 = l_List_mfor___main___at_Lean_IR_EmitC_emitMainFn___spec__2(x_123, x_1, x_122);
return x_124;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_125 = lean_ctor_get(x_119, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_119, 1);
lean_inc(x_126);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 x_127 = x_119;
} else {
 lean_dec_ref(x_119);
 x_127 = lean_box(0);
}
if (lean_is_scalar(x_127)) {
 x_128 = lean_alloc_ctor(1, 2, 0);
} else {
 x_128 = x_127;
}
lean_ctor_set(x_128, 0, x_125);
lean_ctor_set(x_128, 1, x_126);
return x_128;
}
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
lean_dec(x_5);
x_129 = lean_ctor_get(x_112, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_112, 1);
lean_inc(x_130);
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 lean_ctor_release(x_112, 1);
 x_131 = x_112;
} else {
 lean_dec_ref(x_112);
 x_131 = lean_box(0);
}
if (lean_is_scalar(x_131)) {
 x_132 = lean_alloc_ctor(1, 2, 0);
} else {
 x_132 = x_131;
}
lean_ctor_set(x_132, 0, x_129);
lean_ctor_set(x_132, 1, x_130);
return x_132;
}
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
lean_dec(x_10);
lean_dec(x_5);
x_133 = lean_ctor_get(x_107, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_107, 1);
lean_inc(x_134);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_135 = x_107;
} else {
 lean_dec_ref(x_107);
 x_135 = lean_box(0);
}
if (lean_is_scalar(x_135)) {
 x_136 = lean_alloc_ctor(1, 2, 0);
} else {
 x_136 = x_135;
}
lean_ctor_set(x_136, 0, x_133);
lean_ctor_set(x_136, 1, x_134);
return x_136;
}
}
}
else
{
uint8_t x_137; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
x_137 = !lean_is_exclusive(x_12);
if (x_137 == 0)
{
return x_12;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_138 = lean_ctor_get(x_12, 0);
x_139 = lean_ctor_get(x_12, 1);
lean_inc(x_139);
lean_inc(x_138);
lean_dec(x_12);
x_140 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_140, 0, x_138);
lean_ctor_set(x_140, 1, x_139);
return x_140;
}
}
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_141 = lean_ctor_get(x_7, 0);
x_142 = lean_ctor_get(x_7, 1);
lean_inc(x_142);
lean_inc(x_141);
lean_dec(x_7);
x_143 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_143, 0, x_6);
lean_ctor_set(x_143, 1, x_142);
x_144 = l_Lean_Environment_imports(x_5);
x_145 = lean_unsigned_to_nat(0u);
x_146 = l_Array_mforAux___main___at_Lean_IR_EmitC_emitInitFn___spec__1(x_144, x_145, x_1, x_143);
if (lean_obj_tag(x_146) == 0)
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_147 = lean_ctor_get(x_146, 1);
lean_inc(x_147);
if (lean_is_exclusive(x_146)) {
 lean_ctor_release(x_146, 0);
 lean_ctor_release(x_146, 1);
 x_148 = x_146;
} else {
 lean_dec_ref(x_146);
 x_148 = lean_box(0);
}
if (lean_is_scalar(x_148)) {
 x_149 = lean_alloc_ctor(0, 2, 0);
} else {
 x_149 = x_148;
}
lean_ctor_set(x_149, 0, x_6);
lean_ctor_set(x_149, 1, x_147);
x_150 = l_String_splitAux___main___closed__1;
x_151 = l_Lean_Name_mangle(x_141, x_150);
x_152 = l_Array_mforAux___main___at_Lean_IR_EmitC_emitInitFn___spec__1___closed__1;
x_153 = lean_string_append(x_152, x_151);
lean_dec(x_151);
x_154 = l_Lean_IR_EmitC_emitInitFn___closed__1;
x_155 = lean_string_append(x_153, x_154);
x_156 = l_Lean_IR_EmitC_emitInitFn___closed__6;
x_157 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_157, 0, x_155);
lean_ctor_set(x_157, 1, x_156);
x_158 = l_Lean_IR_EmitC_emitInitFn___closed__7;
x_159 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_159, 0, x_158);
lean_ctor_set(x_159, 1, x_157);
x_160 = l_List_mfor___main___at_Lean_IR_EmitC_emitMainFn___spec__2(x_159, x_1, x_149);
lean_dec(x_159);
if (lean_obj_tag(x_160) == 0)
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
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
if (lean_is_scalar(x_162)) {
 x_163 = lean_alloc_ctor(0, 2, 0);
} else {
 x_163 = x_162;
}
lean_ctor_set(x_163, 0, x_6);
lean_ctor_set(x_163, 1, x_161);
x_164 = l_Lean_IR_EmitC_emitInitFn___closed__2;
x_165 = l_Array_mforAux___main___at_Lean_IR_EmitC_emitInitFn___spec__2(x_164, x_144, x_145, x_1, x_163);
lean_dec(x_144);
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
if (lean_is_scalar(x_167)) {
 x_168 = lean_alloc_ctor(0, 2, 0);
} else {
 x_168 = x_167;
}
lean_ctor_set(x_168, 0, x_6);
lean_ctor_set(x_168, 1, x_166);
x_169 = l_Lean_IR_declMapExt;
x_170 = l_Lean_SimplePersistentEnvExtension_getEntries___rarg(x_169, x_5);
lean_dec(x_5);
x_171 = l_List_reverse___rarg(x_170);
x_172 = l_List_mfor___main___at_Lean_IR_EmitC_emitInitFn___spec__3(x_171, x_1, x_168);
lean_dec(x_171);
if (lean_obj_tag(x_172) == 0)
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_173 = lean_ctor_get(x_172, 1);
lean_inc(x_173);
if (lean_is_exclusive(x_172)) {
 lean_ctor_release(x_172, 0);
 lean_ctor_release(x_172, 1);
 x_174 = x_172;
} else {
 lean_dec_ref(x_172);
 x_174 = lean_box(0);
}
if (lean_is_scalar(x_174)) {
 x_175 = lean_alloc_ctor(0, 2, 0);
} else {
 x_175 = x_174;
}
lean_ctor_set(x_175, 0, x_6);
lean_ctor_set(x_175, 1, x_173);
x_176 = l_Lean_IR_EmitC_emitInitFn___closed__9;
x_177 = l_List_mfor___main___at_Lean_IR_EmitC_emitMainFn___spec__2(x_176, x_1, x_175);
return x_177;
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_178 = lean_ctor_get(x_172, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_172, 1);
lean_inc(x_179);
if (lean_is_exclusive(x_172)) {
 lean_ctor_release(x_172, 0);
 lean_ctor_release(x_172, 1);
 x_180 = x_172;
} else {
 lean_dec_ref(x_172);
 x_180 = lean_box(0);
}
if (lean_is_scalar(x_180)) {
 x_181 = lean_alloc_ctor(1, 2, 0);
} else {
 x_181 = x_180;
}
lean_ctor_set(x_181, 0, x_178);
lean_ctor_set(x_181, 1, x_179);
return x_181;
}
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
lean_dec(x_5);
x_182 = lean_ctor_get(x_165, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_165, 1);
lean_inc(x_183);
if (lean_is_exclusive(x_165)) {
 lean_ctor_release(x_165, 0);
 lean_ctor_release(x_165, 1);
 x_184 = x_165;
} else {
 lean_dec_ref(x_165);
 x_184 = lean_box(0);
}
if (lean_is_scalar(x_184)) {
 x_185 = lean_alloc_ctor(1, 2, 0);
} else {
 x_185 = x_184;
}
lean_ctor_set(x_185, 0, x_182);
lean_ctor_set(x_185, 1, x_183);
return x_185;
}
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; 
lean_dec(x_144);
lean_dec(x_5);
x_186 = lean_ctor_get(x_160, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_160, 1);
lean_inc(x_187);
if (lean_is_exclusive(x_160)) {
 lean_ctor_release(x_160, 0);
 lean_ctor_release(x_160, 1);
 x_188 = x_160;
} else {
 lean_dec_ref(x_160);
 x_188 = lean_box(0);
}
if (lean_is_scalar(x_188)) {
 x_189 = lean_alloc_ctor(1, 2, 0);
} else {
 x_189 = x_188;
}
lean_ctor_set(x_189, 0, x_186);
lean_ctor_set(x_189, 1, x_187);
return x_189;
}
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
lean_dec(x_144);
lean_dec(x_141);
lean_dec(x_5);
x_190 = lean_ctor_get(x_146, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_146, 1);
lean_inc(x_191);
if (lean_is_exclusive(x_146)) {
 lean_ctor_release(x_146, 0);
 lean_ctor_release(x_146, 1);
 x_192 = x_146;
} else {
 lean_dec_ref(x_146);
 x_192 = lean_box(0);
}
if (lean_is_scalar(x_192)) {
 x_193 = lean_alloc_ctor(1, 2, 0);
} else {
 x_193 = x_192;
}
lean_ctor_set(x_193, 0, x_190);
lean_ctor_set(x_193, 1, x_191);
return x_193;
}
}
}
else
{
uint8_t x_194; 
lean_dec(x_5);
x_194 = !lean_is_exclusive(x_7);
if (x_194 == 0)
{
return x_7;
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_195 = lean_ctor_get(x_7, 0);
x_196 = lean_ctor_get(x_7, 1);
lean_inc(x_196);
lean_inc(x_195);
lean_dec(x_7);
x_197 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_197, 0, x_195);
lean_ctor_set(x_197, 1, x_196);
return x_197;
}
}
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_198 = lean_ctor_get(x_3, 0);
x_199 = lean_ctor_get(x_3, 1);
lean_inc(x_199);
lean_inc(x_198);
lean_dec(x_3);
x_200 = lean_box(0);
x_201 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_201, 0, x_200);
lean_ctor_set(x_201, 1, x_199);
x_202 = l_Lean_IR_EmitC_getModName(x_1, x_201);
if (lean_obj_tag(x_202) == 0)
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_203 = lean_ctor_get(x_202, 0);
lean_inc(x_203);
x_204 = lean_ctor_get(x_202, 1);
lean_inc(x_204);
if (lean_is_exclusive(x_202)) {
 lean_ctor_release(x_202, 0);
 lean_ctor_release(x_202, 1);
 x_205 = x_202;
} else {
 lean_dec_ref(x_202);
 x_205 = lean_box(0);
}
if (lean_is_scalar(x_205)) {
 x_206 = lean_alloc_ctor(0, 2, 0);
} else {
 x_206 = x_205;
}
lean_ctor_set(x_206, 0, x_200);
lean_ctor_set(x_206, 1, x_204);
x_207 = l_Lean_Environment_imports(x_198);
x_208 = lean_unsigned_to_nat(0u);
x_209 = l_Array_mforAux___main___at_Lean_IR_EmitC_emitInitFn___spec__1(x_207, x_208, x_1, x_206);
if (lean_obj_tag(x_209) == 0)
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; 
x_210 = lean_ctor_get(x_209, 1);
lean_inc(x_210);
if (lean_is_exclusive(x_209)) {
 lean_ctor_release(x_209, 0);
 lean_ctor_release(x_209, 1);
 x_211 = x_209;
} else {
 lean_dec_ref(x_209);
 x_211 = lean_box(0);
}
if (lean_is_scalar(x_211)) {
 x_212 = lean_alloc_ctor(0, 2, 0);
} else {
 x_212 = x_211;
}
lean_ctor_set(x_212, 0, x_200);
lean_ctor_set(x_212, 1, x_210);
x_213 = l_String_splitAux___main___closed__1;
x_214 = l_Lean_Name_mangle(x_203, x_213);
x_215 = l_Array_mforAux___main___at_Lean_IR_EmitC_emitInitFn___spec__1___closed__1;
x_216 = lean_string_append(x_215, x_214);
lean_dec(x_214);
x_217 = l_Lean_IR_EmitC_emitInitFn___closed__1;
x_218 = lean_string_append(x_216, x_217);
x_219 = l_Lean_IR_EmitC_emitInitFn___closed__6;
x_220 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_220, 0, x_218);
lean_ctor_set(x_220, 1, x_219);
x_221 = l_Lean_IR_EmitC_emitInitFn___closed__7;
x_222 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_222, 0, x_221);
lean_ctor_set(x_222, 1, x_220);
x_223 = l_List_mfor___main___at_Lean_IR_EmitC_emitMainFn___spec__2(x_222, x_1, x_212);
lean_dec(x_222);
if (lean_obj_tag(x_223) == 0)
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; 
x_224 = lean_ctor_get(x_223, 1);
lean_inc(x_224);
if (lean_is_exclusive(x_223)) {
 lean_ctor_release(x_223, 0);
 lean_ctor_release(x_223, 1);
 x_225 = x_223;
} else {
 lean_dec_ref(x_223);
 x_225 = lean_box(0);
}
if (lean_is_scalar(x_225)) {
 x_226 = lean_alloc_ctor(0, 2, 0);
} else {
 x_226 = x_225;
}
lean_ctor_set(x_226, 0, x_200);
lean_ctor_set(x_226, 1, x_224);
x_227 = l_Lean_IR_EmitC_emitInitFn___closed__2;
x_228 = l_Array_mforAux___main___at_Lean_IR_EmitC_emitInitFn___spec__2(x_227, x_207, x_208, x_1, x_226);
lean_dec(x_207);
if (lean_obj_tag(x_228) == 0)
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; 
x_229 = lean_ctor_get(x_228, 1);
lean_inc(x_229);
if (lean_is_exclusive(x_228)) {
 lean_ctor_release(x_228, 0);
 lean_ctor_release(x_228, 1);
 x_230 = x_228;
} else {
 lean_dec_ref(x_228);
 x_230 = lean_box(0);
}
if (lean_is_scalar(x_230)) {
 x_231 = lean_alloc_ctor(0, 2, 0);
} else {
 x_231 = x_230;
}
lean_ctor_set(x_231, 0, x_200);
lean_ctor_set(x_231, 1, x_229);
x_232 = l_Lean_IR_declMapExt;
x_233 = l_Lean_SimplePersistentEnvExtension_getEntries___rarg(x_232, x_198);
lean_dec(x_198);
x_234 = l_List_reverse___rarg(x_233);
x_235 = l_List_mfor___main___at_Lean_IR_EmitC_emitInitFn___spec__3(x_234, x_1, x_231);
lean_dec(x_234);
if (lean_obj_tag(x_235) == 0)
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; 
x_236 = lean_ctor_get(x_235, 1);
lean_inc(x_236);
if (lean_is_exclusive(x_235)) {
 lean_ctor_release(x_235, 0);
 lean_ctor_release(x_235, 1);
 x_237 = x_235;
} else {
 lean_dec_ref(x_235);
 x_237 = lean_box(0);
}
if (lean_is_scalar(x_237)) {
 x_238 = lean_alloc_ctor(0, 2, 0);
} else {
 x_238 = x_237;
}
lean_ctor_set(x_238, 0, x_200);
lean_ctor_set(x_238, 1, x_236);
x_239 = l_Lean_IR_EmitC_emitInitFn___closed__9;
x_240 = l_List_mfor___main___at_Lean_IR_EmitC_emitMainFn___spec__2(x_239, x_1, x_238);
return x_240;
}
else
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
x_241 = lean_ctor_get(x_235, 0);
lean_inc(x_241);
x_242 = lean_ctor_get(x_235, 1);
lean_inc(x_242);
if (lean_is_exclusive(x_235)) {
 lean_ctor_release(x_235, 0);
 lean_ctor_release(x_235, 1);
 x_243 = x_235;
} else {
 lean_dec_ref(x_235);
 x_243 = lean_box(0);
}
if (lean_is_scalar(x_243)) {
 x_244 = lean_alloc_ctor(1, 2, 0);
} else {
 x_244 = x_243;
}
lean_ctor_set(x_244, 0, x_241);
lean_ctor_set(x_244, 1, x_242);
return x_244;
}
}
else
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; 
lean_dec(x_198);
x_245 = lean_ctor_get(x_228, 0);
lean_inc(x_245);
x_246 = lean_ctor_get(x_228, 1);
lean_inc(x_246);
if (lean_is_exclusive(x_228)) {
 lean_ctor_release(x_228, 0);
 lean_ctor_release(x_228, 1);
 x_247 = x_228;
} else {
 lean_dec_ref(x_228);
 x_247 = lean_box(0);
}
if (lean_is_scalar(x_247)) {
 x_248 = lean_alloc_ctor(1, 2, 0);
} else {
 x_248 = x_247;
}
lean_ctor_set(x_248, 0, x_245);
lean_ctor_set(x_248, 1, x_246);
return x_248;
}
}
else
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; 
lean_dec(x_207);
lean_dec(x_198);
x_249 = lean_ctor_get(x_223, 0);
lean_inc(x_249);
x_250 = lean_ctor_get(x_223, 1);
lean_inc(x_250);
if (lean_is_exclusive(x_223)) {
 lean_ctor_release(x_223, 0);
 lean_ctor_release(x_223, 1);
 x_251 = x_223;
} else {
 lean_dec_ref(x_223);
 x_251 = lean_box(0);
}
if (lean_is_scalar(x_251)) {
 x_252 = lean_alloc_ctor(1, 2, 0);
} else {
 x_252 = x_251;
}
lean_ctor_set(x_252, 0, x_249);
lean_ctor_set(x_252, 1, x_250);
return x_252;
}
}
else
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; 
lean_dec(x_207);
lean_dec(x_203);
lean_dec(x_198);
x_253 = lean_ctor_get(x_209, 0);
lean_inc(x_253);
x_254 = lean_ctor_get(x_209, 1);
lean_inc(x_254);
if (lean_is_exclusive(x_209)) {
 lean_ctor_release(x_209, 0);
 lean_ctor_release(x_209, 1);
 x_255 = x_209;
} else {
 lean_dec_ref(x_209);
 x_255 = lean_box(0);
}
if (lean_is_scalar(x_255)) {
 x_256 = lean_alloc_ctor(1, 2, 0);
} else {
 x_256 = x_255;
}
lean_ctor_set(x_256, 0, x_253);
lean_ctor_set(x_256, 1, x_254);
return x_256;
}
}
else
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; 
lean_dec(x_198);
x_257 = lean_ctor_get(x_202, 0);
lean_inc(x_257);
x_258 = lean_ctor_get(x_202, 1);
lean_inc(x_258);
if (lean_is_exclusive(x_202)) {
 lean_ctor_release(x_202, 0);
 lean_ctor_release(x_202, 1);
 x_259 = x_202;
} else {
 lean_dec_ref(x_202);
 x_259 = lean_box(0);
}
if (lean_is_scalar(x_259)) {
 x_260 = lean_alloc_ctor(1, 2, 0);
} else {
 x_260 = x_259;
}
lean_ctor_set(x_260, 0, x_257);
lean_ctor_set(x_260, 1, x_258);
return x_260;
}
}
}
else
{
uint8_t x_261; 
x_261 = !lean_is_exclusive(x_3);
if (x_261 == 0)
{
return x_3;
}
else
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; 
x_262 = lean_ctor_get(x_3, 0);
x_263 = lean_ctor_get(x_3, 1);
lean_inc(x_263);
lean_inc(x_262);
lean_dec(x_3);
x_264 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_264, 0, x_262);
lean_ctor_set(x_264, 1, x_263);
return x_264;
}
}
}
}
lean_object* l_Array_mforAux___main___at_Lean_IR_EmitC_emitInitFn___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_mforAux___main___at_Lean_IR_EmitC_emitInitFn___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_mforAux___main___at_Lean_IR_EmitC_emitInitFn___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_mforAux___main___at_Lean_IR_EmitC_emitInitFn___spec__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_List_mfor___main___at_Lean_IR_EmitC_emitInitFn___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_mfor___main___at_Lean_IR_EmitC_emitInitFn___spec__3(x_1, x_2, x_3);
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
lean_object* x_3; 
x_3 = l_Lean_IR_EmitC_emitFileHeader(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
lean_dec(x_5);
x_6 = lean_box(0);
lean_ctor_set(x_3, 0, x_6);
x_7 = l_Lean_IR_EmitC_emitFnDecls(x_1, x_3);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 0);
lean_dec(x_9);
lean_ctor_set(x_7, 0, x_6);
lean_inc(x_1);
x_10 = l_Lean_IR_EmitC_emitFns(x_1, x_7);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
lean_dec(x_12);
lean_ctor_set(x_10, 0, x_6);
x_13 = l_Lean_IR_EmitC_emitInitFn(x_1, x_10);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
lean_dec(x_15);
lean_ctor_set(x_13, 0, x_6);
x_16 = l_Lean_IR_EmitC_emitMainFnIfNeeded(x_1, x_13);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
lean_dec(x_18);
lean_ctor_set(x_16, 0, x_6);
x_19 = l_Lean_IR_EmitC_emitFileFooter(x_1, x_16);
lean_dec(x_1);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_16, 1);
lean_inc(x_20);
lean_dec(x_16);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_6);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_Lean_IR_EmitC_emitFileFooter(x_1, x_21);
lean_dec(x_1);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_16);
if (x_23 == 0)
{
return x_16;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_16, 0);
x_25 = lean_ctor_get(x_16, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_16);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_13, 1);
lean_inc(x_27);
lean_dec(x_13);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_6);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_Lean_IR_EmitC_emitMainFnIfNeeded(x_1, x_28);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_31 = x_29;
} else {
 lean_dec_ref(x_29);
 x_31 = lean_box(0);
}
if (lean_is_scalar(x_31)) {
 x_32 = lean_alloc_ctor(0, 2, 0);
} else {
 x_32 = x_31;
}
lean_ctor_set(x_32, 0, x_6);
lean_ctor_set(x_32, 1, x_30);
x_33 = l_Lean_IR_EmitC_emitFileFooter(x_1, x_32);
lean_dec(x_1);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_1);
x_34 = lean_ctor_get(x_29, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_29, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_36 = x_29;
} else {
 lean_dec_ref(x_29);
 x_36 = lean_box(0);
}
if (lean_is_scalar(x_36)) {
 x_37 = lean_alloc_ctor(1, 2, 0);
} else {
 x_37 = x_36;
}
lean_ctor_set(x_37, 0, x_34);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
}
else
{
uint8_t x_38; 
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_13);
if (x_38 == 0)
{
return x_13;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_13, 0);
x_40 = lean_ctor_get(x_13, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_13);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_10, 1);
lean_inc(x_42);
lean_dec(x_10);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_6);
lean_ctor_set(x_43, 1, x_42);
x_44 = l_Lean_IR_EmitC_emitInitFn(x_1, x_43);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_46 = x_44;
} else {
 lean_dec_ref(x_44);
 x_46 = lean_box(0);
}
if (lean_is_scalar(x_46)) {
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_46;
}
lean_ctor_set(x_47, 0, x_6);
lean_ctor_set(x_47, 1, x_45);
x_48 = l_Lean_IR_EmitC_emitMainFnIfNeeded(x_1, x_47);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_50 = x_48;
} else {
 lean_dec_ref(x_48);
 x_50 = lean_box(0);
}
if (lean_is_scalar(x_50)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_50;
}
lean_ctor_set(x_51, 0, x_6);
lean_ctor_set(x_51, 1, x_49);
x_52 = l_Lean_IR_EmitC_emitFileFooter(x_1, x_51);
lean_dec(x_1);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_1);
x_53 = lean_ctor_get(x_48, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_48, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_55 = x_48;
} else {
 lean_dec_ref(x_48);
 x_55 = lean_box(0);
}
if (lean_is_scalar(x_55)) {
 x_56 = lean_alloc_ctor(1, 2, 0);
} else {
 x_56 = x_55;
}
lean_ctor_set(x_56, 0, x_53);
lean_ctor_set(x_56, 1, x_54);
return x_56;
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_1);
x_57 = lean_ctor_get(x_44, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_44, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_59 = x_44;
} else {
 lean_dec_ref(x_44);
 x_59 = lean_box(0);
}
if (lean_is_scalar(x_59)) {
 x_60 = lean_alloc_ctor(1, 2, 0);
} else {
 x_60 = x_59;
}
lean_ctor_set(x_60, 0, x_57);
lean_ctor_set(x_60, 1, x_58);
return x_60;
}
}
}
else
{
uint8_t x_61; 
lean_dec(x_1);
x_61 = !lean_is_exclusive(x_10);
if (x_61 == 0)
{
return x_10;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_10, 0);
x_63 = lean_ctor_get(x_10, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_10);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_7, 1);
lean_inc(x_65);
lean_dec(x_7);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_6);
lean_ctor_set(x_66, 1, x_65);
lean_inc(x_1);
x_67 = l_Lean_IR_EmitC_emitFns(x_1, x_66);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_68 = lean_ctor_get(x_67, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_69 = x_67;
} else {
 lean_dec_ref(x_67);
 x_69 = lean_box(0);
}
if (lean_is_scalar(x_69)) {
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_69;
}
lean_ctor_set(x_70, 0, x_6);
lean_ctor_set(x_70, 1, x_68);
x_71 = l_Lean_IR_EmitC_emitInitFn(x_1, x_70);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_72 = lean_ctor_get(x_71, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_73 = x_71;
} else {
 lean_dec_ref(x_71);
 x_73 = lean_box(0);
}
if (lean_is_scalar(x_73)) {
 x_74 = lean_alloc_ctor(0, 2, 0);
} else {
 x_74 = x_73;
}
lean_ctor_set(x_74, 0, x_6);
lean_ctor_set(x_74, 1, x_72);
x_75 = l_Lean_IR_EmitC_emitMainFnIfNeeded(x_1, x_74);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_76 = lean_ctor_get(x_75, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 x_77 = x_75;
} else {
 lean_dec_ref(x_75);
 x_77 = lean_box(0);
}
if (lean_is_scalar(x_77)) {
 x_78 = lean_alloc_ctor(0, 2, 0);
} else {
 x_78 = x_77;
}
lean_ctor_set(x_78, 0, x_6);
lean_ctor_set(x_78, 1, x_76);
x_79 = l_Lean_IR_EmitC_emitFileFooter(x_1, x_78);
lean_dec(x_1);
return x_79;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_dec(x_1);
x_80 = lean_ctor_get(x_75, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_75, 1);
lean_inc(x_81);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 x_82 = x_75;
} else {
 lean_dec_ref(x_75);
 x_82 = lean_box(0);
}
if (lean_is_scalar(x_82)) {
 x_83 = lean_alloc_ctor(1, 2, 0);
} else {
 x_83 = x_82;
}
lean_ctor_set(x_83, 0, x_80);
lean_ctor_set(x_83, 1, x_81);
return x_83;
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_dec(x_1);
x_84 = lean_ctor_get(x_71, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_71, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_86 = x_71;
} else {
 lean_dec_ref(x_71);
 x_86 = lean_box(0);
}
if (lean_is_scalar(x_86)) {
 x_87 = lean_alloc_ctor(1, 2, 0);
} else {
 x_87 = x_86;
}
lean_ctor_set(x_87, 0, x_84);
lean_ctor_set(x_87, 1, x_85);
return x_87;
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_dec(x_1);
x_88 = lean_ctor_get(x_67, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_67, 1);
lean_inc(x_89);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_90 = x_67;
} else {
 lean_dec_ref(x_67);
 x_90 = lean_box(0);
}
if (lean_is_scalar(x_90)) {
 x_91 = lean_alloc_ctor(1, 2, 0);
} else {
 x_91 = x_90;
}
lean_ctor_set(x_91, 0, x_88);
lean_ctor_set(x_91, 1, x_89);
return x_91;
}
}
}
else
{
uint8_t x_92; 
lean_dec(x_1);
x_92 = !lean_is_exclusive(x_7);
if (x_92 == 0)
{
return x_7;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_7, 0);
x_94 = lean_ctor_get(x_7, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_7);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_96 = lean_ctor_get(x_3, 1);
lean_inc(x_96);
lean_dec(x_3);
x_97 = lean_box(0);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_96);
x_99 = l_Lean_IR_EmitC_emitFnDecls(x_1, x_98);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_100 = lean_ctor_get(x_99, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 x_101 = x_99;
} else {
 lean_dec_ref(x_99);
 x_101 = lean_box(0);
}
if (lean_is_scalar(x_101)) {
 x_102 = lean_alloc_ctor(0, 2, 0);
} else {
 x_102 = x_101;
}
lean_ctor_set(x_102, 0, x_97);
lean_ctor_set(x_102, 1, x_100);
lean_inc(x_1);
x_103 = l_Lean_IR_EmitC_emitFns(x_1, x_102);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_104 = lean_ctor_get(x_103, 1);
lean_inc(x_104);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 x_105 = x_103;
} else {
 lean_dec_ref(x_103);
 x_105 = lean_box(0);
}
if (lean_is_scalar(x_105)) {
 x_106 = lean_alloc_ctor(0, 2, 0);
} else {
 x_106 = x_105;
}
lean_ctor_set(x_106, 0, x_97);
lean_ctor_set(x_106, 1, x_104);
x_107 = l_Lean_IR_EmitC_emitInitFn(x_1, x_106);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_108 = lean_ctor_get(x_107, 1);
lean_inc(x_108);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_109 = x_107;
} else {
 lean_dec_ref(x_107);
 x_109 = lean_box(0);
}
if (lean_is_scalar(x_109)) {
 x_110 = lean_alloc_ctor(0, 2, 0);
} else {
 x_110 = x_109;
}
lean_ctor_set(x_110, 0, x_97);
lean_ctor_set(x_110, 1, x_108);
x_111 = l_Lean_IR_EmitC_emitMainFnIfNeeded(x_1, x_110);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_112 = lean_ctor_get(x_111, 1);
lean_inc(x_112);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 x_113 = x_111;
} else {
 lean_dec_ref(x_111);
 x_113 = lean_box(0);
}
if (lean_is_scalar(x_113)) {
 x_114 = lean_alloc_ctor(0, 2, 0);
} else {
 x_114 = x_113;
}
lean_ctor_set(x_114, 0, x_97);
lean_ctor_set(x_114, 1, x_112);
x_115 = l_Lean_IR_EmitC_emitFileFooter(x_1, x_114);
lean_dec(x_1);
return x_115;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
lean_dec(x_1);
x_116 = lean_ctor_get(x_111, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_111, 1);
lean_inc(x_117);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 x_118 = x_111;
} else {
 lean_dec_ref(x_111);
 x_118 = lean_box(0);
}
if (lean_is_scalar(x_118)) {
 x_119 = lean_alloc_ctor(1, 2, 0);
} else {
 x_119 = x_118;
}
lean_ctor_set(x_119, 0, x_116);
lean_ctor_set(x_119, 1, x_117);
return x_119;
}
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
lean_dec(x_1);
x_120 = lean_ctor_get(x_107, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_107, 1);
lean_inc(x_121);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_122 = x_107;
} else {
 lean_dec_ref(x_107);
 x_122 = lean_box(0);
}
if (lean_is_scalar(x_122)) {
 x_123 = lean_alloc_ctor(1, 2, 0);
} else {
 x_123 = x_122;
}
lean_ctor_set(x_123, 0, x_120);
lean_ctor_set(x_123, 1, x_121);
return x_123;
}
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
lean_dec(x_1);
x_124 = lean_ctor_get(x_103, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_103, 1);
lean_inc(x_125);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 x_126 = x_103;
} else {
 lean_dec_ref(x_103);
 x_126 = lean_box(0);
}
if (lean_is_scalar(x_126)) {
 x_127 = lean_alloc_ctor(1, 2, 0);
} else {
 x_127 = x_126;
}
lean_ctor_set(x_127, 0, x_124);
lean_ctor_set(x_127, 1, x_125);
return x_127;
}
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
lean_dec(x_1);
x_128 = lean_ctor_get(x_99, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_99, 1);
lean_inc(x_129);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 x_130 = x_99;
} else {
 lean_dec_ref(x_99);
 x_130 = lean_box(0);
}
if (lean_is_scalar(x_130)) {
 x_131 = lean_alloc_ctor(1, 2, 0);
} else {
 x_131 = x_130;
}
lean_ctor_set(x_131, 0, x_128);
lean_ctor_set(x_131, 1, x_129);
return x_131;
}
}
}
else
{
uint8_t x_132; 
lean_dec(x_1);
x_132 = !lean_is_exclusive(x_3);
if (x_132 == 0)
{
return x_3;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_133 = lean_ctor_get(x_3, 0);
x_134 = lean_ctor_get(x_3, 1);
lean_inc(x_134);
lean_inc(x_133);
lean_dec(x_3);
x_135 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_135, 0, x_133);
lean_ctor_set(x_135, 1, x_134);
return x_135;
}
}
}
}
lean_object* _init_l_Lean_IR_emitC___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_String_splitAux___main___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* lean_ir_emit_c(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = l_HashMap_Inhabited___closed__1;
x_4 = lean_box(0);
x_5 = l_Array_empty___closed__1;
x_6 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_3);
lean_ctor_set(x_6, 4, x_4);
lean_ctor_set(x_6, 5, x_5);
x_7 = l_Lean_IR_emitC___closed__1;
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
lean_object* initialize_init_control_conditional(lean_object*);
lean_object* initialize_init_lean_runtime(lean_object*);
lean_object* initialize_init_lean_compiler_namemangling(lean_object*);
lean_object* initialize_init_lean_compiler_exportattr(lean_object*);
lean_object* initialize_init_lean_compiler_initattr(lean_object*);
lean_object* initialize_init_lean_compiler_ir_compilerm(lean_object*);
lean_object* initialize_init_lean_compiler_ir_emitutil(lean_object*);
lean_object* initialize_init_lean_compiler_ir_normids(lean_object*);
lean_object* initialize_init_lean_compiler_ir_simpcase(lean_object*);
lean_object* initialize_init_lean_compiler_ir_boxing(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_init_lean_compiler_ir_emitc(lean_object* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (lean_io_result_is_error(w)) return w;
w = initialize_init_control_conditional(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_init_lean_runtime(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_namemangling(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_exportattr(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_initattr(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_ir_compilerm(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_ir_emitutil(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_ir_normids(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_ir_simpcase(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_ir_boxing(w);
if (lean_io_result_is_error(w)) return w;
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
l_List_mfor___main___at_Lean_IR_EmitC_emitFnDecls___spec__5___closed__1 = _init_l_List_mfor___main___at_Lean_IR_EmitC_emitFnDecls___spec__5___closed__1();
lean_mark_persistent(l_List_mfor___main___at_Lean_IR_EmitC_emitFnDecls___spec__5___closed__1);
l_List_mfor___main___at_Lean_IR_EmitC_emitFnDecls___spec__5___closed__2 = _init_l_List_mfor___main___at_Lean_IR_EmitC_emitFnDecls___spec__5___closed__2();
lean_mark_persistent(l_List_mfor___main___at_Lean_IR_EmitC_emitFnDecls___spec__5___closed__2);
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
l_Array_mforAux___main___at_Lean_IR_EmitC_emitCase___spec__1___closed__1 = _init_l_Array_mforAux___main___at_Lean_IR_EmitC_emitCase___spec__1___closed__1();
lean_mark_persistent(l_Array_mforAux___main___at_Lean_IR_EmitC_emitCase___spec__1___closed__1);
l_Array_mforAux___main___at_Lean_IR_EmitC_emitCase___spec__1___closed__2 = _init_l_Array_mforAux___main___at_Lean_IR_EmitC_emitCase___spec__1___closed__2();
lean_mark_persistent(l_Array_mforAux___main___at_Lean_IR_EmitC_emitCase___spec__1___closed__2);
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
l_Nat_mforAux___main___at_Lean_IR_EmitC_emitJmp___spec__1___closed__1 = _init_l_Nat_mforAux___main___at_Lean_IR_EmitC_emitJmp___spec__1___closed__1();
lean_mark_persistent(l_Nat_mforAux___main___at_Lean_IR_EmitC_emitJmp___spec__1___closed__1);
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
l_Nat_mforAux___main___at_Lean_IR_EmitC_emitReset___spec__1___closed__1 = _init_l_Nat_mforAux___main___at_Lean_IR_EmitC_emitReset___spec__1___closed__1();
lean_mark_persistent(l_Nat_mforAux___main___at_Lean_IR_EmitC_emitReset___spec__1___closed__1);
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
l_Lean_IR_EmitC_emitFullApp___closed__1 = _init_l_Lean_IR_EmitC_emitFullApp___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_emitFullApp___closed__1);
l_Nat_mforAux___main___at_Lean_IR_EmitC_emitPartialApp___spec__1___closed__1 = _init_l_Nat_mforAux___main___at_Lean_IR_EmitC_emitPartialApp___spec__1___closed__1();
lean_mark_persistent(l_Nat_mforAux___main___at_Lean_IR_EmitC_emitPartialApp___spec__1___closed__1);
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
l_Nat_mforAux___main___at_Lean_IR_EmitC_emitTailCall___spec__2___closed__1 = _init_l_Nat_mforAux___main___at_Lean_IR_EmitC_emitTailCall___spec__2___closed__1();
lean_mark_persistent(l_Nat_mforAux___main___at_Lean_IR_EmitC_emitTailCall___spec__2___closed__1);
l_Nat_mforAux___main___at_Lean_IR_EmitC_emitTailCall___spec__3___closed__1 = _init_l_Nat_mforAux___main___at_Lean_IR_EmitC_emitTailCall___spec__3___closed__1();
lean_mark_persistent(l_Nat_mforAux___main___at_Lean_IR_EmitC_emitTailCall___spec__3___closed__1);
l_Lean_IR_EmitC_emitTailCall___closed__1 = _init_l_Lean_IR_EmitC_emitTailCall___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_emitTailCall___closed__1);
l_Lean_IR_EmitC_emitTailCall___closed__2 = _init_l_Lean_IR_EmitC_emitTailCall___closed__2();
lean_mark_persistent(l_Lean_IR_EmitC_emitTailCall___closed__2);
l_Lean_IR_EmitC_emitTailCall___closed__3 = _init_l_Lean_IR_EmitC_emitTailCall___closed__3();
lean_mark_persistent(l_Lean_IR_EmitC_emitTailCall___closed__3);
l_Lean_IR_EmitC_emitTailCall___closed__4 = _init_l_Lean_IR_EmitC_emitTailCall___closed__4();
lean_mark_persistent(l_Lean_IR_EmitC_emitTailCall___closed__4);
l_Lean_IR_EmitC_emitBlock___main___closed__1 = _init_l_Lean_IR_EmitC_emitBlock___main___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_emitBlock___main___closed__1);
l_Lean_IR_EmitC_emitBlock___main___closed__2 = _init_l_Lean_IR_EmitC_emitBlock___main___closed__2();
lean_mark_persistent(l_Lean_IR_EmitC_emitBlock___main___closed__2);
l_Lean_IR_EmitC_emitFnBody___main___closed__1 = _init_l_Lean_IR_EmitC_emitFnBody___main___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_emitFnBody___main___closed__1);
l_Nat_mforAux___main___at_Lean_IR_EmitC_emitDeclAux___spec__1___closed__1 = _init_l_Nat_mforAux___main___at_Lean_IR_EmitC_emitDeclAux___spec__1___closed__1();
lean_mark_persistent(l_Nat_mforAux___main___at_Lean_IR_EmitC_emitDeclAux___spec__1___closed__1);
l_Nat_mforAux___main___at_Lean_IR_EmitC_emitDeclAux___spec__1___closed__2 = _init_l_Nat_mforAux___main___at_Lean_IR_EmitC_emitDeclAux___spec__1___closed__2();
lean_mark_persistent(l_Nat_mforAux___main___at_Lean_IR_EmitC_emitDeclAux___spec__1___closed__2);
l_Nat_mforAux___main___at_Lean_IR_EmitC_emitDeclAux___spec__1___closed__3 = _init_l_Nat_mforAux___main___at_Lean_IR_EmitC_emitDeclAux___spec__1___closed__3();
lean_mark_persistent(l_Nat_mforAux___main___at_Lean_IR_EmitC_emitDeclAux___spec__1___closed__3);
l_Lean_IR_EmitC_emitDeclAux___closed__1 = _init_l_Lean_IR_EmitC_emitDeclAux___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_emitDeclAux___closed__1);
l_Lean_IR_EmitC_emitDeclAux___closed__2 = _init_l_Lean_IR_EmitC_emitDeclAux___closed__2();
lean_mark_persistent(l_Lean_IR_EmitC_emitDeclAux___closed__2);
l_Lean_IR_EmitC_emitDeclAux___closed__3 = _init_l_Lean_IR_EmitC_emitDeclAux___closed__3();
lean_mark_persistent(l_Lean_IR_EmitC_emitDeclAux___closed__3);
l_Lean_IR_EmitC_emitDecl___closed__1 = _init_l_Lean_IR_EmitC_emitDecl___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_emitDecl___closed__1);
l_Lean_IR_EmitC_emitDeclInit___closed__1 = _init_l_Lean_IR_EmitC_emitDeclInit___closed__1();
lean_mark_persistent(l_Lean_IR_EmitC_emitDeclInit___closed__1);
l_Lean_IR_EmitC_emitDeclInit___closed__2 = _init_l_Lean_IR_EmitC_emitDeclInit___closed__2();
lean_mark_persistent(l_Lean_IR_EmitC_emitDeclInit___closed__2);
l_Lean_IR_EmitC_emitDeclInit___closed__3 = _init_l_Lean_IR_EmitC_emitDeclInit___closed__3();
lean_mark_persistent(l_Lean_IR_EmitC_emitDeclInit___closed__3);
l_Lean_IR_EmitC_emitDeclInit___closed__4 = _init_l_Lean_IR_EmitC_emitDeclInit___closed__4();
lean_mark_persistent(l_Lean_IR_EmitC_emitDeclInit___closed__4);
l_Array_mforAux___main___at_Lean_IR_EmitC_emitInitFn___spec__1___closed__1 = _init_l_Array_mforAux___main___at_Lean_IR_EmitC_emitInitFn___spec__1___closed__1();
lean_mark_persistent(l_Array_mforAux___main___at_Lean_IR_EmitC_emitInitFn___spec__1___closed__1);
l_Array_mforAux___main___at_Lean_IR_EmitC_emitInitFn___spec__1___closed__2 = _init_l_Array_mforAux___main___at_Lean_IR_EmitC_emitInitFn___spec__1___closed__2();
lean_mark_persistent(l_Array_mforAux___main___at_Lean_IR_EmitC_emitInitFn___spec__1___closed__2);
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
l_Lean_IR_emitC___closed__1 = _init_l_Lean_IR_emitC___closed__1();
lean_mark_persistent(l_Lean_IR_emitC___closed__1);
return w;
}
#ifdef __cplusplus
}
#endif
