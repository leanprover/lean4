// Lean compiler output
// Module: init.lean.compiler.ir.emitcpp
// Imports: init.control.conditional init.lean.name_mangling init.lean.compiler.initattr init.lean.compiler.ir.compilerm init.lean.compiler.ir.emitutil init.lean.compiler.ir.normids
#include "runtime/object.h"
#include "runtime/apply.h"
typedef lean::object obj;    typedef lean::usize  usize;
typedef lean::uint8  uint8;  typedef lean::uint16 uint16;
typedef lean::uint32 uint32; typedef lean::uint64 uint64;
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
obj* l_Lean_IR_EmitCpp_emitProj___closed__1;
extern obj* l_Lean_IR_getDecl___closed__1;
obj* l_Lean_Name_mangle(obj*, obj*);
obj* l_Lean_IR_EmitCpp_isObj(obj*, obj*, obj*);
obj* l_Lean_IR_EmitCpp_declareVars(obj*, uint8, obj*, obj*);
obj* l_HashMapImp_find___at_Lean_IR_EmitCpp_getJPParams___spec__1___boxed(obj*, obj*);
obj* l_Lean_IR_EmitCpp_toCppType___main___closed__1;
obj* l_Lean_IR_EmitCpp_emitNumLit___closed__1;
obj* l_Lean_IR_EmitCpp_leanMainFn;
obj* l_Lean_IR_EmitCpp_emit(obj*);
obj* l_List_mfor___main___at_Lean_IR_EmitCpp_emitMainFn___spec__2(obj*, obj*, obj*);
obj* l_Lean_IR_EmitCpp_openNamespacesAux___main___closed__1;
obj* l_Lean_getExternNameFor(obj*, obj*, obj*);
extern "C" uint8 lean_name_dec_eq(obj*, obj*);
obj* l_Lean_IR_EmitCpp_emitLns___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_EmitCpp_emitArgs___boxed(obj*, obj*, obj*);
obj* l_Lean_IR_EmitCpp_emitFileHeader___closed__5;
obj* l_Lean_IR_EmitCpp_emitOffset___closed__2;
obj* l_Lean_IR_EmitCpp_emit___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_EmitCpp_getJPParams___closed__1;
obj* l_Lean_IR_EmitCpp_throwInvalidExportName___rarg___boxed(obj*, obj*, obj*);
obj* l_Lean_IR_EmitCpp_toCppType(uint8);
obj* l_List_map___main___at_Lean_IR_EmitCpp_toStringArgs___spec__1(obj*);
extern obj* l_Array_empty___closed__1;
namespace lean {
obj* nat_sub(obj*, obj*);
}
obj* l_Lean_IR_EmitCpp_emitJmp___closed__1;
obj* l_Lean_IR_EmitCpp_emitMainFn___closed__14;
obj* l_Lean_IR_EmitCpp_emitReset___boxed(obj*, obj*, obj*, obj*);
obj* l_Nat_mforAux___main___at_Lean_IR_EmitCpp_emitFnDeclAux___spec__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_EmitCpp_emitMainFn___closed__1;
obj* l_Lean_IR_EmitCpp_emitMainFn___closed__8;
obj* l_Lean_IR_EmitCpp_emitSProj___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_EmitCpp_closeNamespacesFor(obj*, obj*, obj*);
obj* l_Lean_IR_EmitCpp_emitUSet___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_List_foldl___main___at_Lean_IR_EmitCpp_emitFnDecls___spec__1(obj*, obj*);
obj* l_Nat_mforAux___main___at_Lean_IR_EmitCpp_emitDeclAux___spec__1___boxed(obj*, obj*, obj*, obj*, obj*);
extern obj* l_Lean_IR_JoinPointId_HasToString___closed__1;
obj* l_Lean_IR_EmitCpp_emitArg___boxed(obj*, obj*, obj*);
obj* l_Lean_IR_EmitCpp_emitSProj___rarg(obj*);
obj* l_List_mfor___main___at_Lean_IR_EmitCpp_emitFns___spec__1(obj*, obj*, obj*);
obj* l_Nat_mforAux___main___at_Lean_IR_EmitCpp_emitFnDeclAux___spec__1(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_EmitCpp_emitDec(obj*, obj*, uint8, obj*, obj*);
obj* l_Lean_IR_EmitCpp_closeNamespacesAux(obj*, obj*, obj*);
obj* l_Lean_IR_EmitCpp_emitIf___closed__2;
obj* l_Lean_IR_EmitCpp_emitBox___closed__4;
obj* l_Array_mforAux___main___at_Lean_IR_EmitCpp_emitFileHeader___spec__1___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_EmitCpp_declareVars___main___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_EmitCpp_closeNamespaces___boxed(obj*, obj*, obj*);
obj* l_HashMapImp_find___at_Lean_IR_EmitCpp_isObj___spec__1___boxed(obj*, obj*);
obj* l_Lean_IR_EmitCpp_emit___rarg(obj*, obj*, obj*, obj*);
extern obj* l_Char_quoteCore___closed__3;
obj* l_Lean_IR_EmitCpp_emitBlock___main___closed__1;
obj* l_Lean_IR_EmitCpp_openNamespacesAux___boxed(obj*, obj*, obj*);
obj* l_Lean_IR_EmitCpp_closeNamespaces(obj*, obj*, obj*);
obj* l_Lean_IR_EmitCpp_emitLit___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_EmitCpp_emitLns___boxed(obj*);
obj* l_Lean_IR_EmitCpp_emitMainFn___closed__11;
obj* l_Lean_IR_EmitCpp_emitUProj(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_EmitCpp_toCppType___main___closed__7;
obj* l_Lean_IR_EmitCpp_emitApp(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_EmitCpp_emitInc___closed__2;
obj* l_Nat_mforAux___main___at_Lean_IR_EmitCpp_emitPartialApp___spec__1___closed__1;
obj* l_Lean_IR_Decl_normalizeIds(obj*);
obj* l_Lean_PersistentEnvExtension_getEntries___rarg(obj*, obj*);
obj* l_Lean_IR_EmitCpp_emitIsTaggedPtr___closed__1;
obj* l_Lean_IR_EmitCpp_emitJPs(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_EmitCpp_emitReset___rarg(obj*);
uint8 l_Lean_IR_Decl_resultType___main(obj*);
obj* l_Lean_IR_EmitCpp_emitVDecl(obj*, uint8, obj*, obj*, obj*);
obj* l_Lean_IR_EmitCpp_closeNamespacesFor___boxed(obj*, obj*, obj*);
obj* l_Lean_IR_EmitCpp_emitFnDeclAux___closed__3;
obj* l_Lean_IR_EmitCpp_emitDeclAux___closed__1;
obj* l_List_reverse___rarg(obj*);
namespace lean {
obj* mk_extern_call_core(obj*, obj*, obj*);
}
obj* l_Lean_IR_EmitCpp_emitMainFn___closed__13;
obj* l_Lean_IR_EmitCpp_emitLn___boxed(obj*);
obj* l_Nat_mforAux___main___at_Lean_IR_EmitCpp_emitDeclAux___spec__1(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_EmitCpp_isIf(obj*);
obj* l_List_foldr___main___at_Lean_IR_EmitCpp_hasMainFn___spec__1___boxed(obj*, obj*);
obj* l_Lean_IR_EmitCpp_closeNamespacesAux___main(obj*, obj*, obj*);
obj* l_Array_mforAux___main___at_Lean_IR_EmitCpp_emitCase___spec__1(obj*, obj*, obj*, obj*, obj*);
obj* l_Nat_mforAux___main___at_Lean_IR_EmitCpp_emitJmp___spec__1___closed__1;
uint8 l_List_foldr___main___at_Lean_IR_EmitCpp_hasMainFn___spec__1(uint8, obj*);
obj* l_Lean_IR_EmitCpp_emitUnbox___closed__2;
namespace lean {
namespace ir {
obj* decl_to_string_core(obj*);
}}
obj* l_Lean_IR_EmitCpp_emitDecl(obj*, obj*, obj*);
obj* l_Lean_Name_toStringWithSep___main(obj*, obj*);
obj* l_Lean_IR_EmitCpp_openNamespaces___boxed(obj*, obj*, obj*);
obj* l_Lean_IR_EmitCpp_isObj___boxed(obj*, obj*, obj*);
obj* l_Lean_IR_EmitCpp_emitRelease___boxed(obj*, obj*, obj*, obj*);
obj* l_String_foldlAux___main___at_Lean_IR_EmitCpp_quoteString___spec__1(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_EmitCpp_emitCase___closed__1;
obj* l_Lean_IR_EmitCpp_emitFileHeader(obj*, obj*);
obj* l_Lean_IR_EmitCpp_emitUnbox___closed__3;
obj* l_Lean_IR_EmitCpp_emitLn___rarg(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_EmitCpp_emitFnDecl(obj*, uint8, obj*, obj*);
uint8 l_Lean_IR_IRType_isObj___main(uint8);
obj* l_Lean_IR_EmitCpp_emitJmp___closed__2;
extern obj* l_uint32Sz;
obj* l_Lean_IR_EmitCpp_emitBox___closed__1;
obj* l_Nat_mforAux___main___at_Lean_IR_EmitCpp_emitPartialApp___spec__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_String_foldlAux___main___at_Lean_IR_EmitCpp_quoteString___spec__1___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_EmitCpp_emitIsTaggedPtr(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_EmitCpp_throwUnknownVar___rarg___closed__1;
obj* l_Lean_IR_EmitCpp_emitBlock___main(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_EmitCpp_emitInc___closed__1;
obj* l_AssocList_find___main___at_Lean_IR_EmitCpp_getJPParams___spec__2___boxed(obj*, obj*);
obj* l_Lean_IR_EmitCpp_emitSSet___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_EmitCpp_toBaseCppName(obj*, obj*, obj*);
obj* l_Lean_IR_emitCpp___closed__1;
obj* l_Lean_IR_EmitCpp_emitCase___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_EmitCpp_toCppType___main___closed__5;
obj* l_Lean_IR_EmitCpp_emitNumLit___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_EmitCpp_emitBox___closed__5;
extern obj* l_Char_quoteCore___closed__1;
extern "C" obj* lean_get_export_name_for(obj*, obj*);
namespace lean {
obj* string_push(obj*, uint32);
}
obj* l_Lean_IR_EmitCpp_emitSet___closed__1;
obj* l_Lean_IR_EmitCpp_getJPParams___boxed(obj*, obj*, obj*);
obj* l_Lean_IR_EmitCpp_emitReset(obj*, obj*, obj*, obj*);
obj* l_Array_toList___rarg(obj*);
obj* l_Lean_IR_EmitCpp_emitLhs(obj*, obj*, obj*);
obj* l_Lean_IR_usesLeanNamespace___main(obj*, obj*);
uint8 l_Lean_NameSet_contains(obj*, obj*);
obj* l_Lean_IR_EmitCpp_hasMainFn(obj*, obj*);
obj* l_Lean_IR_EmitCpp_emitNumLit___closed__2;
obj* l_Lean_IR_EmitCpp_emitPartialApp___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Nat_repr(obj*);
obj* l_Lean_IR_EmitCpp_closeNamespacesAux___main___closed__1;
extern obj* l_String_quote___closed__1;
obj* l_Lean_IR_EmitCpp_declareParams___boxed(obj*, obj*, obj*);
uint8 l_Lean_hasInitAttr(obj*, obj*);
obj* l_RBNode_insert___at_Lean_NameSet_insert___spec__1(obj*, obj*, obj*);
obj* l_Lean_IR_EmitCpp_emit___boxed(obj*);
obj* l_Nat_mforAux___main___at_Lean_IR_EmitCpp_emitArgs___spec__1(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_mkVarJPMaps(obj*);
obj* l_Lean_IR_EmitCpp_emitJPs___main(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_EmitCpp_emitFileHeader___closed__7;
obj* l_Lean_IR_EmitCpp_closeNamespacesAux___main___boxed(obj*, obj*, obj*);
obj* l_Lean_IR_EmitCpp_emitMainFn___closed__6;
obj* l_Lean_IR_EmitCpp_emitInc___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_EmitCpp_emitIsShared___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_EmitCpp_throwInvalidExportName___rarg___closed__1;
obj* l_Lean_IR_EmitCpp_toCppType___main___closed__4;
obj* l_Lean_IR_EmitCpp_emitApp___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_EmitCpp_emitMainFn___closed__7;
obj* l_Nat_mforAux___main___at_Lean_IR_EmitCpp_emitArgs___spec__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_EmitCpp_emitFnDecls(obj*, obj*);
obj* l_Lean_IR_EmitCpp_closeNamespacesAux___boxed(obj*, obj*, obj*);
extern obj* l_Char_quoteCore___closed__2;
obj* l_Lean_IR_EmitCpp_emitOffset___closed__1;
obj* l_Lean_IR_EmitCpp_emitExternDeclAux___closed__2;
obj* l_Lean_IR_EmitCpp_emitFileHeader___closed__4;
namespace lean {
obj* string_append(obj*, obj*);
}
obj* l_Lean_IR_EmitCpp_emitOffset(obj*, obj*, obj*, obj*);
obj* l_Array_mforAux___main___at_Lean_IR_EmitCpp_emitCase___spec__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_EmitCpp_getDecl(obj*, obj*, obj*);
obj* l_Lean_IR_EmitCpp_emitTag___closed__1;
obj* l_Lean_IR_EmitCpp_emitUnbox(obj*, uint8, obj*, obj*, obj*);
obj* l_Lean_IR_EmitCpp_emitLns___at_Lean_IR_EmitCpp_emitMainFn___spec__1(obj*, obj*, obj*);
extern obj* l_List_reprAux___main___rarg___closed__1;
obj* l_List_mfor___main___at_Lean_IR_EmitCpp_emitFnDecls___spec__5___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_EmitCpp_emitUnbox___closed__4;
obj* l_Lean_IR_EmitCpp_emitNumLit(uint8, obj*, obj*, obj*);
obj* l_Lean_IR_EmitCpp_emitExternDeclAux___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_EmitCpp_emitUSet(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_EmitCpp_emitLn(obj*);
obj* l_Lean_IR_EmitCpp_emitFnDeclAux___closed__2;
extern obj* l_Option_HasRepr___rarg___closed__3;
namespace lean {
uint8 nat_dec_lt(obj*, obj*);
}
obj* l_Lean_IR_EmitCpp_emitMainFn(obj*, obj*);
uint8 l_Lean_isExternC(obj*, obj*);
obj* l_Array_mforAux___main___at_Lean_IR_EmitCpp_declareParams___spec__1___boxed(obj*, obj*, obj*, obj*);
obj* l_RBTree_toList___at_Lean_IR_EmitCpp_emitFnDecls___spec__3(obj*);
obj* l_Lean_IR_EmitCpp_emitCase___closed__2;
namespace lean {
obj* nat_mod(obj*, obj*);
}
obj* l_HashMapImp_find___at_Lean_IR_EmitCpp_isObj___spec__1(obj*, obj*);
uint8 l_Lean_IR_FnBody_isTerminal___main(obj*);
obj* l_Lean_IR_EmitCpp_emitLit(obj*, uint8, obj*, obj*, obj*);
obj* l_Lean_IR_EmitCpp_emitApp___rarg(obj*);
obj* l_Lean_IR_EmitCpp_emitFns(obj*, obj*);
extern obj* l_Char_HasRepr___closed__1;
obj* l_Lean_IR_EmitCpp_emitProj___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_EmitCpp_emitReuse___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
extern obj* l_Lean_IR_declMapExt;
obj* l_Lean_IR_EmitCpp_openNamespacesAux___main___closed__3;
extern "C" obj* lean_name_mk_string(obj*, obj*);
obj* l_Lean_IR_EmitCpp_openNamespacesAux(obj*, obj*, obj*);
obj* l_Lean_IR_Decl_name___main(obj*);
obj* l_Lean_IR_EmitCpp_toCppType___main(uint8);
obj* l_Lean_IR_EmitCpp_argToCppString(obj*);
obj* l_Array_mforAux___main___at_Lean_IR_EmitCpp_emitCase___spec__1___closed__1;
extern obj* l_Char_quoteCore___closed__5;
namespace lean {
obj* nat_add(obj*, obj*);
}
obj* l_Nat_mforAux___main___at_Lean_IR_EmitCpp_emitJmp___spec__1(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_getExportNameFor___boxed(obj*, obj*);
obj* l_Lean_IR_EmitCpp_emitBlock___main___closed__2;
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
obj* l_Lean_IR_EmitCpp_emitJmp(obj*, obj*, obj*, obj*);
extern obj* l_Prod_HasRepr___rarg___closed__1;
extern obj* l_Lean_IR_paramInh;
obj* l_Lean_IR_EmitCpp_openNamespacesAux___main___closed__2;
uint8 l_Array_isEmpty___rarg(obj*);
obj* l_Lean_IR_EmitCpp_emitIsTaggedPtr___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_EmitCpp_emitProj(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_EmitCpp_argToCppString___closed__1;
obj* l_Lean_IR_EmitCpp_emitCase(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_EmitCpp_emitMainFn___closed__12;
obj* l_Lean_IR_EmitCpp_emitSet(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_EmitCpp_emitFnDeclAux(obj*, obj*, uint8, obj*, obj*);
obj* l_Lean_IR_EmitCpp_emitMainFn___closed__2;
obj* l_Lean_IR_EmitCpp_emitFullApp___closed__1;
obj* l_Lean_IR_EmitCpp_emitMainFn___closed__3;
extern obj* l_Lean_IR_altInh;
obj* l_Lean_IR_EmitCpp_emitMainFn___closed__4;
obj* l_Lean_IR_EmitCpp_throwUnknownVar___boxed(obj*);
namespace lean {
uint32 string_utf8_get(obj*, obj*);
}
obj* l_Lean_IR_EmitCpp_emitJmp___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_EmitCpp_emitCtor___rarg(obj*);
obj* l_List_mfor___main___at_Lean_IR_EmitCpp_emitLns___spec__1___rarg(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_EmitCpp_emitFileHeader___closed__2;
obj* l_Lean_IR_collectUsedDecls(obj*, obj*);
obj* l_Lean_IR_EmitCpp_emitBox(obj*, obj*, uint8, obj*, obj*);
obj* l_Array_mforAux___main___at_Lean_IR_EmitCpp_emitCase___spec__1___closed__2;
obj* l_Lean_IR_EmitCpp_toCppInitName___closed__1;
obj* l_Lean_IR_EmitCpp_emitVDecl___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_EmitCpp_declareVars___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_EmitCpp_emitUProj___rarg(obj*);
obj* l_Lean_IR_EmitCpp_emitArg(obj*, obj*, obj*);
obj* l_Lean_IR_EmitCpp_emitInc___closed__3;
obj* l_Lean_IR_EmitCpp_emitBox___closed__2;
obj* l_Lean_IR_EmitCpp_emitSProj(obj*, uint8, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_EmitCpp_toCppType___main___boxed(obj*);
obj* l_Lean_IR_EmitCpp_quoteString___boxed(obj*);
obj* l_Lean_IR_EmitCpp_emitLhs___boxed(obj*, obj*, obj*);
obj* l_Lean_IR_EmitCpp_emitBox___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_EmitCpp_emitBlock(obj*, obj*, obj*, obj*);
obj* l_HashMapImp_find___at_Lean_IR_EmitCpp_getJPParams___spec__1(obj*, obj*);
obj* l_Lean_IR_EmitCpp_emitLit___closed__1;
obj* l_Lean_IR_EmitCpp_emitFnBody___main___closed__1;
obj* l_Lean_IR_EmitCpp_toBaseCppName___closed__2;
obj* l_Lean_IR_EmitCpp_main(obj*, obj*);
obj* l_Lean_IR_EmitCpp_emitExternDeclAux___closed__1;
obj* l_Lean_IR_EmitCpp_cppQualifiedNameToName(obj*);
obj* l_Lean_IR_EmitCpp_emitTag___boxed(obj*, obj*, obj*);
obj* l_String_split(obj*, obj*);
obj* l_Lean_IR_EmitCpp_emitFnBody___main___closed__2;
obj* l_Lean_IR_EmitCpp_emitReuse___rarg(obj*);
obj* l_Lean_IR_EmitCpp_emitCtor(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_AltCore_body___main(obj*);
obj* l_Lean_IR_EmitCpp_emitLns___rarg(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_EmitCpp_toCppInitName(obj*, obj*, obj*);
obj* l_Lean_IR_EmitCpp_emitOffset___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_findEnvDecl(obj*, obj*);
namespace lean {
usize usize_modn(usize, obj*);
}
obj* l_Lean_IR_EmitCpp_toCppName(obj*, obj*, obj*);
obj* l_Lean_IR_EmitCpp_getJPParams(obj*, obj*, obj*);
obj* l_AssocList_find___main___at_Lean_IR_EmitCpp_isObj___spec__2(obj*, obj*);
obj* l_Lean_IR_EmitCpp_emitFnBody___main(obj*, obj*, obj*);
obj* l_Lean_IR_EmitCpp_throwUnknownVar(obj*);
obj* l_Lean_IR_EmitCpp_emitIsShared(obj*, obj*, obj*, obj*);
obj* l_Array_mforAux___main___at_Lean_IR_EmitCpp_declareParams___spec__1(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_EmitCpp_emitIf___closed__1;
obj* l_Lean_IR_EmitCpp_getModName(obj*, obj*);
extern obj* l_HashMap_Inhabited___closed__1;
obj* l_Lean_IR_EmitCpp_emitFnDeclAux___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_EmitCpp_emitLn___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_Array_mforAux___main___at_Lean_IR_EmitCpp_emitCase___spec__1___closed__3;
obj* l_Lean_IR_EmitCpp_emitPartialApp___closed__1;
extern obj* l_Lean_IR_VarId_HasToString___closed__1;
obj* l_Lean_IR_Decl_params___main(obj*);
obj* l_Lean_IR_EmitCpp_emitMainFn___closed__5;
obj* l_Lean_IR_EmitCpp_emitIf___closed__3;
obj* l_List_mfor___main___at_Lean_IR_EmitCpp_emitFnDecls___spec__5___closed__1;
obj* l_Lean_IR_EmitCpp_emitSet___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_List_foldl___main___at_Lean_IR_EmitCpp_emitFnDecls___spec__1___boxed(obj*, obj*);
obj* l_RBNode_revFold___main___at_Lean_IR_EmitCpp_emitFnDecls___spec__4(obj*, obj*);
obj* l_Lean_IR_EmitCpp_openNamespacesFor___boxed(obj*, obj*, obj*);
obj* l_Lean_IR_EmitCpp_emitRelease(obj*, obj*, obj*, obj*);
obj* l_List_foldl___main___at_Lean_IR_EmitCpp_cppQualifiedNameToName___spec__1(obj*, obj*);
obj* l_Lean_IR_EmitCpp_emitFileHeader___closed__6;
obj* l_Lean_IR_EmitCpp_emitReuse(obj*, obj*, obj*, uint8, obj*, obj*);
obj* l_Lean_IR_EmitCpp_toBaseCppName___closed__1;
obj* l_Lean_Name_getPrefix___main(obj*);
obj* l_Lean_IR_EmitCpp_emitFullApp(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_EmitCpp_toCppType___main___closed__3;
obj* l_List_mfor___main___at_Lean_IR_EmitCpp_emitMainFn___spec__2___boxed(obj*, obj*, obj*);
obj* l_Lean_IR_EmitCpp_throwUnknownVar___rarg(obj*, obj*, obj*);
obj* l_Lean_IR_EmitCpp_toCppName___closed__1;
obj* l_AssocList_find___main___at_Lean_IR_EmitCpp_getJPParams___spec__2(obj*, obj*);
obj* l_List_foldl___main___at_Lean_IR_EmitCpp_emitFnDecls___spec__2(obj*, obj*);
obj* l_Lean_IR_EmitCpp_emitArgs(obj*, obj*, obj*);
obj* l_List_mfor___main___at_Lean_IR_EmitCpp_emitLns___spec__1___boxed(obj*);
obj* l_Lean_IR_EmitCpp_toCppType___main___closed__2;
namespace lean {
obj* string_utf8_next(obj*, obj*);
}
obj* l_Lean_IR_EmitCpp_emitCtor___boxed(obj*, obj*, obj*, obj*);
namespace lean {
uint32 uint32_of_nat(obj*);
}
obj* l_Lean_IR_FnBody_body___main(obj*);
extern obj* l_Lean_Name_toString___closed__1;
obj* l_Lean_IR_EmitCpp_emitDec___closed__2;
obj* l_Lean_IR_EmitCpp_declareVar(obj*, uint8, obj*, obj*);
obj* l_Lean_IR_EmitCpp_toCppType___boxed(obj*);
obj* l_Lean_IR_EmitCpp_openNamespacesFor(obj*, obj*, obj*);
namespace lean {
uint8 nat_dec_le(obj*, obj*);
}
obj* l_AssocList_find___main___at_Lean_IR_EmitCpp_isObj___spec__2___boxed(obj*, obj*);
obj* l_Lean_IR_EmitCpp_toStringArgs___boxed(obj*);
obj* l_List_mfor___main___at_Lean_IR_EmitCpp_emitLns___spec__1(obj*);
obj* l_Lean_IR_EmitCpp_emitFileHeader___closed__3;
namespace lean {
usize usize_of_nat(obj*);
}
obj* l_Lean_IR_EmitCpp_declareVar___closed__1;
obj* l_Lean_IR_EmitCpp_openNamespaces(obj*, obj*, obj*);
obj* l_Array_mforAux___main___at_Lean_IR_EmitCpp_emitFileHeader___spec__1(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_EmitCpp_emitPartialApp(obj*, obj*, obj*, obj*, obj*);
namespace lean {
obj* string_utf8_byte_size(obj*);
}
namespace lean {
obj* nat_div(obj*, obj*);
}
obj* l_Lean_IR_EmitCpp_emitDec___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_EmitCpp_emitIsShared___closed__1;
obj* l_Lean_IR_EmitCpp_emitFnBody(obj*, obj*, obj*);
obj* l_Lean_IR_EmitCpp_emitUnbox___closed__1;
namespace lean {
obj* uint32_to_nat(uint32);
}
obj* l_Lean_IR_EmitCpp_emitRelease___closed__1;
obj* l_Lean_IR_EmitCpp_quoteString(obj*);
obj* l_Lean_IR_EmitCpp_emitLns___at_Lean_IR_EmitCpp_emitMainFn___spec__1___boxed(obj*, obj*, obj*);
obj* l_Lean_IR_EmitCpp_emitInc(obj*, obj*, uint8, obj*, obj*);
obj* l_Lean_IR_EmitCpp_emitUSet___closed__1;
uint32 l_Nat_digitChar(obj*);
obj* l_Lean_IR_EmitCpp_toHexDigit___boxed(obj*);
obj* l_Lean_IR_EmitCpp_emitExternDeclAux(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_EmitCpp_declareVar___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_EmitCpp_declareParams(obj*, obj*, obj*);
obj* l_Lean_IR_EmitCpp_emitDecl___closed__1;
obj* l_Lean_IR_EmitCpp_emitTag(obj*, obj*, obj*);
obj* l_Nat_mforAux___main___at_Lean_IR_EmitCpp_emitPartialApp___spec__1(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_EmitCpp_emitDec___closed__1;
obj* l_Lean_IR_EmitCpp_emitDeclAux(obj*, obj*, obj*);
obj* l_List_mfor___main___at_Lean_IR_EmitCpp_emitFnDecls___spec__5(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_EmitCpp_throwInvalidExportName___boxed(obj*);
obj* l_Lean_IR_EmitCpp_emitFullApp___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_EmitCpp_throwInvalidExportName___rarg(obj*, obj*, obj*);
obj* l_Lean_IR_EmitCpp_emitMainFn___closed__10;
obj* l_Lean_IR_EmitCpp_emitFnDecl___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_EmitCpp_declareVars___main(obj*, uint8, obj*, obj*);
obj* l_Lean_IR_EmitCpp_toCppType___main___closed__6;
namespace lean {
namespace ir {
obj* emit_cpp_core(obj*, obj*);
}}
obj* l_Lean_IR_EmitCpp_throwInvalidExportName(obj*);
obj* l_Lean_IR_EmitCpp_emitSSet(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_EmitCpp_emitMainFn___closed__9;
obj* l_Lean_IR_EmitCpp_emitIf(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_EmitCpp_toStringArgs(obj*);
extern obj* l_IO_println___rarg___closed__1;
obj* l_Lean_IR_EmitCpp_emitFileHeader___closed__1;
obj* l_Lean_IR_EmitCpp_openNamespacesAux___main___boxed(obj*, obj*, obj*);
obj* l_Lean_IR_EmitCpp_emitUProj___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_EmitCpp_emitMainFnIfNeeded(obj*, obj*);
obj* l_Lean_IR_EmitCpp_throwUnknownVar___rarg___boxed(obj*, obj*, obj*);
obj* l_Nat_mforAux___main___at_Lean_IR_EmitCpp_emitJmp___spec__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_EmitCpp_toHexDigit(obj*);
obj* l_Lean_IR_EmitCpp_openNamespacesAux___main(obj*, obj*, obj*);
obj* l_Lean_IR_EmitCpp_isIf___boxed(obj*);
obj* l_Lean_IR_EmitCpp_emitUnbox___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_EmitCpp_emitFnDeclAux___closed__1;
obj* l_Lean_IR_EmitCpp_emitLns(obj*);
extern obj* l_Lean_IR_Arg_Inhabited;
extern obj* l_Unit_HasRepr___closed__1;
obj* l_Lean_IR_EmitCpp_emitPartialApp___closed__2;
obj* l_List_mfor___main___at_Lean_IR_EmitCpp_emitLns___spec__1___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_EmitCpp_getEnv(obj*, obj*);
extern obj* l_String_splitAux___main___closed__1;
obj* l_Lean_IR_EmitCpp_emitBox___closed__3;
obj* l_Lean_IR_getExportNameFor___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean_get_export_name_for(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_Lean_IR_EmitCpp_leanMainFn() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("_lean_main");
return x_0;
}
}
obj* l_Lean_IR_EmitCpp_getEnv(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_5; obj* x_8; 
x_2 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 x_4 = x_1;
} else {
 lean::inc(x_2);
 lean::dec(x_1);
 x_4 = lean::box(0);
}
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
lean::dec(x_0);
if (lean::is_scalar(x_4)) {
 x_8 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_8 = x_4;
}
lean::cnstr_set(x_8, 0, x_5);
lean::cnstr_set(x_8, 1, x_2);
return x_8;
}
}
obj* l_Lean_IR_EmitCpp_getModName(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_5; obj* x_8; 
x_2 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 x_4 = x_1;
} else {
 lean::inc(x_2);
 lean::dec(x_1);
 x_4 = lean::box(0);
}
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
lean::dec(x_0);
if (lean::is_scalar(x_4)) {
 x_8 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_8 = x_4;
}
lean::cnstr_set(x_8, 0, x_5);
lean::cnstr_set(x_8, 1, x_2);
return x_8;
}
}
obj* l_Lean_IR_EmitCpp_getDecl(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_EmitCpp_getEnv(x_1, x_2);
if (lean::obj_tag(x_3) == 0)
{
obj* x_4; obj* x_6; obj* x_8; obj* x_9; 
x_4 = lean::cnstr_get(x_3, 0);
x_6 = lean::cnstr_get(x_3, 1);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_set(x_3, 0, lean::box(0));
 lean::cnstr_set(x_3, 1, lean::box(0));
 x_8 = x_3;
} else {
 lean::inc(x_4);
 lean::inc(x_6);
 lean::dec(x_3);
 x_8 = lean::box(0);
}
x_9 = l_Lean_IR_findEnvDecl(x_4, x_0);
lean::dec(x_4);
if (lean::obj_tag(x_9) == 0)
{
obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_16; obj* x_17; obj* x_18; 
x_11 = l_Lean_Name_toString___closed__1;
x_12 = l_Lean_Name_toStringWithSep___main(x_11, x_0);
x_13 = l_Lean_IR_getDecl___closed__1;
x_14 = lean::string_append(x_13, x_12);
lean::dec(x_12);
x_16 = l_Char_HasRepr___closed__1;
x_17 = lean::string_append(x_14, x_16);
if (lean::is_scalar(x_8)) {
 x_18 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_18 = x_8;
 lean::cnstr_set_tag(x_8, 1);
}
lean::cnstr_set(x_18, 0, x_17);
lean::cnstr_set(x_18, 1, x_6);
return x_18;
}
else
{
obj* x_20; obj* x_23; 
lean::dec(x_0);
x_20 = lean::cnstr_get(x_9, 0);
lean::inc(x_20);
lean::dec(x_9);
if (lean::is_scalar(x_8)) {
 x_23 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_23 = x_8;
}
lean::cnstr_set(x_23, 0, x_20);
lean::cnstr_set(x_23, 1, x_6);
return x_23;
}
}
else
{
obj* x_25; obj* x_27; obj* x_29; obj* x_30; 
lean::dec(x_0);
x_25 = lean::cnstr_get(x_3, 0);
x_27 = lean::cnstr_get(x_3, 1);
if (lean::is_exclusive(x_3)) {
 x_29 = x_3;
} else {
 lean::inc(x_25);
 lean::inc(x_27);
 lean::dec(x_3);
 x_29 = lean::box(0);
}
if (lean::is_scalar(x_29)) {
 x_30 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_30 = x_29;
}
lean::cnstr_set(x_30, 0, x_25);
lean::cnstr_set(x_30, 1, x_27);
return x_30;
}
}
}
obj* l_Lean_IR_EmitCpp_emit___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_6; obj* x_7; obj* x_8; obj* x_10; obj* x_11; 
x_4 = lean::cnstr_get(x_3, 1);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 x_6 = x_3;
} else {
 lean::inc(x_4);
 lean::dec(x_3);
 x_6 = lean::box(0);
}
x_7 = lean::apply_1(x_0, x_1);
x_8 = lean::string_append(x_4, x_7);
lean::dec(x_7);
x_10 = lean::box(0);
if (lean::is_scalar(x_6)) {
 x_11 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_11 = x_6;
}
lean::cnstr_set(x_11, 0, x_10);
lean::cnstr_set(x_11, 1, x_8);
return x_11;
}
}
obj* l_Lean_IR_EmitCpp_emit(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_IR_EmitCpp_emit___rarg___boxed), 4, 0);
return x_1;
}
}
obj* l_Lean_IR_EmitCpp_emit___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_IR_EmitCpp_emit___rarg(x_0, x_1, x_2, x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l_Lean_IR_EmitCpp_emit___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_IR_EmitCpp_emit(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_IR_EmitCpp_emitLn___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_6; obj* x_7; obj* x_8; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_4 = lean::cnstr_get(x_3, 1);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 x_6 = x_3;
} else {
 lean::inc(x_4);
 lean::dec(x_3);
 x_6 = lean::box(0);
}
x_7 = lean::apply_1(x_0, x_1);
x_8 = lean::string_append(x_4, x_7);
lean::dec(x_7);
x_10 = l_IO_println___rarg___closed__1;
x_11 = lean::string_append(x_8, x_10);
x_12 = lean::box(0);
if (lean::is_scalar(x_6)) {
 x_13 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_13 = x_6;
}
lean::cnstr_set(x_13, 0, x_12);
lean::cnstr_set(x_13, 1, x_11);
return x_13;
}
}
obj* l_Lean_IR_EmitCpp_emitLn(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_IR_EmitCpp_emitLn___rarg___boxed), 4, 0);
return x_1;
}
}
obj* l_Lean_IR_EmitCpp_emitLn___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_IR_EmitCpp_emitLn___rarg(x_0, x_1, x_2, x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l_Lean_IR_EmitCpp_emitLn___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_IR_EmitCpp_emitLn(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_List_mfor___main___at_Lean_IR_EmitCpp_emitLns___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_5; obj* x_7; obj* x_8; obj* x_9; 
lean::dec(x_0);
x_5 = lean::cnstr_get(x_3, 1);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 x_7 = x_3;
} else {
 lean::inc(x_5);
 lean::dec(x_3);
 x_7 = lean::box(0);
}
x_8 = lean::box(0);
if (lean::is_scalar(x_7)) {
 x_9 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_9 = x_7;
}
lean::cnstr_set(x_9, 0, x_8);
lean::cnstr_set(x_9, 1, x_5);
return x_9;
}
else
{
obj* x_10; obj* x_12; obj* x_15; obj* x_17; obj* x_19; obj* x_20; obj* x_22; obj* x_23; obj* x_24; obj* x_25; 
x_10 = lean::cnstr_get(x_1, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_1, 1);
lean::inc(x_12);
lean::dec(x_1);
x_15 = lean::cnstr_get(x_3, 1);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 x_17 = x_3;
} else {
 lean::inc(x_15);
 lean::dec(x_3);
 x_17 = lean::box(0);
}
lean::inc(x_0);
x_19 = lean::apply_1(x_0, x_10);
x_20 = lean::string_append(x_15, x_19);
lean::dec(x_19);
x_22 = l_IO_println___rarg___closed__1;
x_23 = lean::string_append(x_20, x_22);
x_24 = lean::box(0);
if (lean::is_scalar(x_17)) {
 x_25 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_25 = x_17;
}
lean::cnstr_set(x_25, 0, x_24);
lean::cnstr_set(x_25, 1, x_23);
x_1 = x_12;
x_3 = x_25;
goto _start;
}
}
}
obj* l_List_mfor___main___at_Lean_IR_EmitCpp_emitLns___spec__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_List_mfor___main___at_Lean_IR_EmitCpp_emitLns___spec__1___rarg___boxed), 4, 0);
return x_1;
}
}
obj* l_Lean_IR_EmitCpp_emitLns___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_List_mfor___main___at_Lean_IR_EmitCpp_emitLns___spec__1___rarg(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_Lean_IR_EmitCpp_emitLns(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_IR_EmitCpp_emitLns___rarg___boxed), 4, 0);
return x_1;
}
}
obj* l_List_mfor___main___at_Lean_IR_EmitCpp_emitLns___spec__1___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_List_mfor___main___at_Lean_IR_EmitCpp_emitLns___spec__1___rarg(x_0, x_1, x_2, x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l_List_mfor___main___at_Lean_IR_EmitCpp_emitLns___spec__1___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_List_mfor___main___at_Lean_IR_EmitCpp_emitLns___spec__1(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_IR_EmitCpp_emitLns___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_IR_EmitCpp_emitLns___rarg(x_0, x_1, x_2, x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l_Lean_IR_EmitCpp_emitLns___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_IR_EmitCpp_emitLns(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* _init_l_Lean_IR_EmitCpp_argToCppString___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("lean::box(0)");
return x_0;
}
}
obj* l_Lean_IR_EmitCpp_argToCppString(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_1; obj* x_4; obj* x_5; obj* x_6; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
lean::dec(x_0);
x_4 = l_Nat_repr(x_1);
x_5 = l_Lean_IR_VarId_HasToString___closed__1;
x_6 = lean::string_append(x_5, x_4);
lean::dec(x_4);
return x_6;
}
else
{
obj* x_8; 
x_8 = l_Lean_IR_EmitCpp_argToCppString___closed__1;
return x_8;
}
}
}
obj* l_Lean_IR_EmitCpp_emitArg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_6; obj* x_7; obj* x_9; obj* x_10; 
x_3 = lean::cnstr_get(x_2, 1);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_release(x_2, 0);
 x_5 = x_2;
} else {
 lean::inc(x_3);
 lean::dec(x_2);
 x_5 = lean::box(0);
}
x_6 = l_Lean_IR_EmitCpp_argToCppString(x_0);
x_7 = lean::string_append(x_3, x_6);
lean::dec(x_6);
x_9 = lean::box(0);
if (lean::is_scalar(x_5)) {
 x_10 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_10 = x_5;
}
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_7);
return x_10;
}
}
obj* l_Lean_IR_EmitCpp_emitArg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_EmitCpp_emitArg(x_0, x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* _init_l_Lean_IR_EmitCpp_toCppType___main___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("double");
return x_0;
}
}
obj* _init_l_Lean_IR_EmitCpp_toCppType___main___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("uint8");
return x_0;
}
}
obj* _init_l_Lean_IR_EmitCpp_toCppType___main___closed__3() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("uint16");
return x_0;
}
}
obj* _init_l_Lean_IR_EmitCpp_toCppType___main___closed__4() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("uint32");
return x_0;
}
}
obj* _init_l_Lean_IR_EmitCpp_toCppType___main___closed__5() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("uint64");
return x_0;
}
}
obj* _init_l_Lean_IR_EmitCpp_toCppType___main___closed__6() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("usize");
return x_0;
}
}
obj* _init_l_Lean_IR_EmitCpp_toCppType___main___closed__7() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("obj*");
return x_0;
}
}
obj* l_Lean_IR_EmitCpp_toCppType___main(uint8 x_0) {
_start:
{
switch (x_0) {
case 0:
{
obj* x_1; 
x_1 = l_Lean_IR_EmitCpp_toCppType___main___closed__1;
return x_1;
}
case 1:
{
obj* x_2; 
x_2 = l_Lean_IR_EmitCpp_toCppType___main___closed__2;
return x_2;
}
case 2:
{
obj* x_3; 
x_3 = l_Lean_IR_EmitCpp_toCppType___main___closed__3;
return x_3;
}
case 3:
{
obj* x_4; 
x_4 = l_Lean_IR_EmitCpp_toCppType___main___closed__4;
return x_4;
}
case 4:
{
obj* x_5; 
x_5 = l_Lean_IR_EmitCpp_toCppType___main___closed__5;
return x_5;
}
case 5:
{
obj* x_6; 
x_6 = l_Lean_IR_EmitCpp_toCppType___main___closed__6;
return x_6;
}
default:
{
obj* x_7; 
x_7 = l_Lean_IR_EmitCpp_toCppType___main___closed__7;
return x_7;
}
}
}
}
obj* l_Lean_IR_EmitCpp_toCppType___main___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = lean::unbox(x_0);
x_2 = l_Lean_IR_EmitCpp_toCppType___main(x_1);
return x_2;
}
}
obj* l_Lean_IR_EmitCpp_toCppType(uint8 x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_IR_EmitCpp_toCppType___main(x_0);
return x_1;
}
}
obj* l_Lean_IR_EmitCpp_toCppType___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = lean::unbox(x_0);
x_2 = l_Lean_IR_EmitCpp_toCppType(x_1);
return x_2;
}
}
obj* _init_l_Lean_IR_EmitCpp_openNamespacesAux___main___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("namespace ");
return x_0;
}
}
obj* _init_l_Lean_IR_EmitCpp_openNamespacesAux___main___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string(" {");
return x_0;
}
}
obj* _init_l_Lean_IR_EmitCpp_openNamespacesAux___main___closed__3() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("invalid namespace '");
return x_0;
}
}
obj* l_Lean_IR_EmitCpp_openNamespacesAux___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_3; obj* x_5; obj* x_6; obj* x_7; 
x_3 = lean::cnstr_get(x_2, 1);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_release(x_2, 0);
 x_5 = x_2;
} else {
 lean::inc(x_3);
 lean::dec(x_2);
 x_5 = lean::box(0);
}
x_6 = lean::box(0);
if (lean::is_scalar(x_5)) {
 x_7 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_7 = x_5;
}
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_3);
return x_7;
}
case 1:
{
obj* x_8; obj* x_10; obj* x_13; obj* x_14; obj* x_16; obj* x_17; obj* x_18; 
x_8 = lean::cnstr_get(x_0, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_0, 1);
lean::inc(x_10);
lean::dec(x_0);
x_13 = l_Lean_IR_EmitCpp_openNamespacesAux___main___closed__1;
x_14 = lean::string_append(x_13, x_10);
lean::dec(x_10);
x_16 = l_Lean_IR_EmitCpp_openNamespacesAux___main___closed__2;
x_17 = lean::string_append(x_14, x_16);
x_18 = l_Lean_IR_EmitCpp_openNamespacesAux___main(x_8, x_1, x_2);
if (lean::obj_tag(x_18) == 0)
{
obj* x_19; obj* x_21; obj* x_22; obj* x_24; obj* x_25; obj* x_26; obj* x_27; 
x_19 = lean::cnstr_get(x_18, 1);
if (lean::is_exclusive(x_18)) {
 lean::cnstr_release(x_18, 0);
 x_21 = x_18;
} else {
 lean::inc(x_19);
 lean::dec(x_18);
 x_21 = lean::box(0);
}
x_22 = lean::string_append(x_19, x_17);
lean::dec(x_17);
x_24 = l_IO_println___rarg___closed__1;
x_25 = lean::string_append(x_22, x_24);
x_26 = lean::box(0);
if (lean::is_scalar(x_21)) {
 x_27 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_27 = x_21;
}
lean::cnstr_set(x_27, 0, x_26);
lean::cnstr_set(x_27, 1, x_25);
return x_27;
}
else
{
obj* x_29; obj* x_31; obj* x_33; obj* x_34; 
lean::dec(x_17);
x_29 = lean::cnstr_get(x_18, 0);
x_31 = lean::cnstr_get(x_18, 1);
if (lean::is_exclusive(x_18)) {
 x_33 = x_18;
} else {
 lean::inc(x_29);
 lean::inc(x_31);
 lean::dec(x_18);
 x_33 = lean::box(0);
}
if (lean::is_scalar(x_33)) {
 x_34 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_34 = x_33;
}
lean::cnstr_set(x_34, 0, x_29);
lean::cnstr_set(x_34, 1, x_31);
return x_34;
}
}
default:
{
obj* x_35; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_43; obj* x_44; obj* x_45; 
x_35 = lean::cnstr_get(x_2, 1);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_release(x_2, 0);
 x_37 = x_2;
} else {
 lean::inc(x_35);
 lean::dec(x_2);
 x_37 = lean::box(0);
}
x_38 = l_Lean_Name_toString___closed__1;
x_39 = l_Lean_Name_toStringWithSep___main(x_38, x_0);
x_40 = l_Lean_IR_EmitCpp_openNamespacesAux___main___closed__3;
x_41 = lean::string_append(x_40, x_39);
lean::dec(x_39);
x_43 = l_Char_HasRepr___closed__1;
x_44 = lean::string_append(x_41, x_43);
if (lean::is_scalar(x_37)) {
 x_45 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_45 = x_37;
 lean::cnstr_set_tag(x_37, 1);
}
lean::cnstr_set(x_45, 0, x_44);
lean::cnstr_set(x_45, 1, x_35);
return x_45;
}
}
}
}
obj* l_Lean_IR_EmitCpp_openNamespacesAux___main___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_EmitCpp_openNamespacesAux___main(x_0, x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_IR_EmitCpp_openNamespacesAux(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_EmitCpp_openNamespacesAux___main(x_0, x_1, x_2);
return x_3;
}
}
obj* l_Lean_IR_EmitCpp_openNamespacesAux___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_EmitCpp_openNamespacesAux(x_0, x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_IR_EmitCpp_openNamespaces(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = l_Lean_Name_getPrefix___main(x_0);
x_4 = l_Lean_IR_EmitCpp_openNamespacesAux___main(x_3, x_1, x_2);
return x_4;
}
}
obj* l_Lean_IR_EmitCpp_openNamespaces___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_EmitCpp_openNamespaces(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_IR_EmitCpp_openNamespacesFor(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; 
lean::inc(x_1);
x_4 = l_Lean_IR_EmitCpp_getEnv(x_1, x_2);
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; obj* x_7; obj* x_9; obj* x_10; obj* x_12; obj* x_13; 
x_5 = lean::cnstr_get(x_4, 0);
x_7 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 x_9 = x_4;
} else {
 lean::inc(x_5);
 lean::inc(x_7);
 lean::dec(x_4);
 x_9 = lean::box(0);
}
x_10 = lean::box(0);
lean::inc(x_7);
if (lean::is_scalar(x_9)) {
 x_12 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_12 = x_9;
}
lean::cnstr_set(x_12, 0, x_10);
lean::cnstr_set(x_12, 1, x_7);
x_13 = lean_get_export_name_for(x_5, x_0);
lean::dec(x_5);
if (lean::obj_tag(x_13) == 0)
{
obj* x_17; 
lean::dec(x_1);
lean::dec(x_12);
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_10);
lean::cnstr_set(x_17, 1, x_7);
return x_17;
}
else
{
obj* x_19; obj* x_22; 
lean::dec(x_7);
x_19 = lean::cnstr_get(x_13, 0);
lean::inc(x_19);
lean::dec(x_13);
x_22 = l_Lean_IR_EmitCpp_openNamespaces(x_19, x_1, x_12);
lean::dec(x_1);
lean::dec(x_19);
return x_22;
}
}
else
{
obj* x_26; obj* x_28; obj* x_30; obj* x_31; 
lean::dec(x_1);
x_26 = lean::cnstr_get(x_4, 0);
x_28 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 x_30 = x_4;
} else {
 lean::inc(x_26);
 lean::inc(x_28);
 lean::dec(x_4);
 x_30 = lean::box(0);
}
if (lean::is_scalar(x_30)) {
 x_31 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_31 = x_30;
}
lean::cnstr_set(x_31, 0, x_26);
lean::cnstr_set(x_31, 1, x_28);
return x_31;
}
}
}
obj* l_Lean_IR_EmitCpp_openNamespacesFor___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_EmitCpp_openNamespacesFor(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
}
}
obj* _init_l_Lean_IR_EmitCpp_closeNamespacesAux___main___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("}");
return x_0;
}
}
obj* l_Lean_IR_EmitCpp_closeNamespacesAux___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_3; obj* x_5; obj* x_6; obj* x_7; 
x_3 = lean::cnstr_get(x_2, 1);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_release(x_2, 0);
 x_5 = x_2;
} else {
 lean::inc(x_3);
 lean::dec(x_2);
 x_5 = lean::box(0);
}
x_6 = lean::box(0);
if (lean::is_scalar(x_5)) {
 x_7 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_7 = x_5;
}
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_3);
return x_7;
}
case 1:
{
obj* x_8; obj* x_11; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_8 = lean::cnstr_get(x_0, 0);
lean::inc(x_8);
lean::dec(x_0);
x_11 = lean::cnstr_get(x_2, 1);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_release(x_2, 0);
 x_13 = x_2;
} else {
 lean::inc(x_11);
 lean::dec(x_2);
 x_13 = lean::box(0);
}
x_14 = l_Lean_IR_EmitCpp_closeNamespacesAux___main___closed__1;
x_15 = lean::string_append(x_11, x_14);
x_16 = l_IO_println___rarg___closed__1;
x_17 = lean::string_append(x_15, x_16);
x_18 = lean::box(0);
if (lean::is_scalar(x_13)) {
 x_19 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_19 = x_13;
}
lean::cnstr_set(x_19, 0, x_18);
lean::cnstr_set(x_19, 1, x_17);
x_0 = x_8;
x_2 = x_19;
goto _start;
}
default:
{
obj* x_21; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_29; obj* x_30; obj* x_31; 
x_21 = lean::cnstr_get(x_2, 1);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_release(x_2, 0);
 x_23 = x_2;
} else {
 lean::inc(x_21);
 lean::dec(x_2);
 x_23 = lean::box(0);
}
x_24 = l_Lean_Name_toString___closed__1;
x_25 = l_Lean_Name_toStringWithSep___main(x_24, x_0);
x_26 = l_Lean_IR_EmitCpp_openNamespacesAux___main___closed__3;
x_27 = lean::string_append(x_26, x_25);
lean::dec(x_25);
x_29 = l_Char_HasRepr___closed__1;
x_30 = lean::string_append(x_27, x_29);
if (lean::is_scalar(x_23)) {
 x_31 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_31 = x_23;
 lean::cnstr_set_tag(x_23, 1);
}
lean::cnstr_set(x_31, 0, x_30);
lean::cnstr_set(x_31, 1, x_21);
return x_31;
}
}
}
}
obj* l_Lean_IR_EmitCpp_closeNamespacesAux___main___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_EmitCpp_closeNamespacesAux___main(x_0, x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_IR_EmitCpp_closeNamespacesAux(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_EmitCpp_closeNamespacesAux___main(x_0, x_1, x_2);
return x_3;
}
}
obj* l_Lean_IR_EmitCpp_closeNamespacesAux___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_EmitCpp_closeNamespacesAux(x_0, x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_IR_EmitCpp_closeNamespaces(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = l_Lean_Name_getPrefix___main(x_0);
x_4 = l_Lean_IR_EmitCpp_closeNamespacesAux___main(x_3, x_1, x_2);
return x_4;
}
}
obj* l_Lean_IR_EmitCpp_closeNamespaces___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_EmitCpp_closeNamespaces(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_IR_EmitCpp_closeNamespacesFor(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; 
lean::inc(x_1);
x_4 = l_Lean_IR_EmitCpp_getEnv(x_1, x_2);
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; obj* x_7; obj* x_9; obj* x_10; obj* x_12; obj* x_13; 
x_5 = lean::cnstr_get(x_4, 0);
x_7 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 x_9 = x_4;
} else {
 lean::inc(x_5);
 lean::inc(x_7);
 lean::dec(x_4);
 x_9 = lean::box(0);
}
x_10 = lean::box(0);
lean::inc(x_7);
if (lean::is_scalar(x_9)) {
 x_12 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_12 = x_9;
}
lean::cnstr_set(x_12, 0, x_10);
lean::cnstr_set(x_12, 1, x_7);
x_13 = lean_get_export_name_for(x_5, x_0);
lean::dec(x_5);
if (lean::obj_tag(x_13) == 0)
{
obj* x_17; 
lean::dec(x_1);
lean::dec(x_12);
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_10);
lean::cnstr_set(x_17, 1, x_7);
return x_17;
}
else
{
obj* x_19; obj* x_22; 
lean::dec(x_7);
x_19 = lean::cnstr_get(x_13, 0);
lean::inc(x_19);
lean::dec(x_13);
x_22 = l_Lean_IR_EmitCpp_closeNamespaces(x_19, x_1, x_12);
lean::dec(x_1);
lean::dec(x_19);
return x_22;
}
}
else
{
obj* x_26; obj* x_28; obj* x_30; obj* x_31; 
lean::dec(x_1);
x_26 = lean::cnstr_get(x_4, 0);
x_28 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 x_30 = x_4;
} else {
 lean::inc(x_26);
 lean::inc(x_28);
 lean::dec(x_4);
 x_30 = lean::box(0);
}
if (lean::is_scalar(x_30)) {
 x_31 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_31 = x_30;
}
lean::cnstr_set(x_31, 0, x_26);
lean::cnstr_set(x_31, 1, x_28);
return x_31;
}
}
}
obj* l_Lean_IR_EmitCpp_closeNamespacesFor___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_EmitCpp_closeNamespacesFor(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
}
}
obj* _init_l_Lean_IR_EmitCpp_throwInvalidExportName___rarg___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("invalid export name '");
return x_0;
}
}
obj* l_Lean_IR_EmitCpp_throwInvalidExportName___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_11; obj* x_12; obj* x_13; 
x_3 = lean::cnstr_get(x_2, 1);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_release(x_2, 0);
 x_5 = x_2;
} else {
 lean::inc(x_3);
 lean::dec(x_2);
 x_5 = lean::box(0);
}
x_6 = l_Lean_Name_toString___closed__1;
x_7 = l_Lean_Name_toStringWithSep___main(x_6, x_0);
x_8 = l_Lean_IR_EmitCpp_throwInvalidExportName___rarg___closed__1;
x_9 = lean::string_append(x_8, x_7);
lean::dec(x_7);
x_11 = l_Char_HasRepr___closed__1;
x_12 = lean::string_append(x_9, x_11);
if (lean::is_scalar(x_5)) {
 x_13 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_13 = x_5;
 lean::cnstr_set_tag(x_5, 1);
}
lean::cnstr_set(x_13, 0, x_12);
lean::cnstr_set(x_13, 1, x_3);
return x_13;
}
}
obj* l_Lean_IR_EmitCpp_throwInvalidExportName(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_IR_EmitCpp_throwInvalidExportName___rarg___boxed), 3, 0);
return x_1;
}
}
obj* l_Lean_IR_EmitCpp_throwInvalidExportName___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_EmitCpp_throwInvalidExportName___rarg(x_0, x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_IR_EmitCpp_throwInvalidExportName___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_IR_EmitCpp_throwInvalidExportName(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* _init_l_Lean_IR_EmitCpp_toBaseCppName___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("main");
x_2 = lean_name_mk_string(x_0, x_1);
return x_2;
}
}
obj* _init_l_Lean_IR_EmitCpp_toBaseCppName___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("l_");
return x_0;
}
}
obj* l_Lean_IR_EmitCpp_toBaseCppName(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; 
lean::inc(x_1);
x_4 = l_Lean_IR_EmitCpp_getEnv(x_1, x_2);
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; obj* x_7; obj* x_9; obj* x_10; obj* x_12; obj* x_13; 
x_5 = lean::cnstr_get(x_4, 0);
x_7 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 x_9 = x_4;
} else {
 lean::inc(x_5);
 lean::inc(x_7);
 lean::dec(x_4);
 x_9 = lean::box(0);
}
x_10 = lean::box(0);
lean::inc(x_7);
if (lean::is_scalar(x_9)) {
 x_12 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_12 = x_9;
}
lean::cnstr_set(x_12, 0, x_10);
lean::cnstr_set(x_12, 1, x_7);
x_13 = lean_get_export_name_for(x_5, x_0);
lean::dec(x_5);
if (lean::obj_tag(x_13) == 0)
{
obj* x_17; uint8 x_18; 
lean::dec(x_1);
lean::dec(x_12);
x_17 = l_Lean_IR_EmitCpp_toBaseCppName___closed__1;
x_18 = lean_name_dec_eq(x_0, x_17);
if (x_18 == 0)
{
obj* x_19; obj* x_20; obj* x_21; 
x_19 = l_Lean_IR_EmitCpp_toBaseCppName___closed__2;
x_20 = l_Lean_Name_mangle(x_0, x_19);
x_21 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_21, 0, x_20);
lean::cnstr_set(x_21, 1, x_7);
return x_21;
}
else
{
obj* x_23; obj* x_24; 
lean::dec(x_0);
x_23 = l_Lean_IR_EmitCpp_leanMainFn;
x_24 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_24, 0, x_23);
lean::cnstr_set(x_24, 1, x_7);
return x_24;
}
}
else
{
obj* x_25; 
x_25 = lean::cnstr_get(x_13, 0);
lean::inc(x_25);
lean::dec(x_13);
switch (lean::obj_tag(x_25)) {
case 0:
{
obj* x_29; 
lean::dec(x_7);
x_29 = l_Lean_IR_EmitCpp_throwInvalidExportName___rarg(x_0, x_1, x_12);
lean::dec(x_1);
return x_29;
}
case 1:
{
obj* x_34; obj* x_37; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_12);
x_34 = lean::cnstr_get(x_25, 1);
lean::inc(x_34);
lean::dec(x_25);
x_37 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_37, 0, x_34);
lean::cnstr_set(x_37, 1, x_7);
return x_37;
}
default:
{
obj* x_40; 
lean::dec(x_7);
lean::dec(x_25);
x_40 = l_Lean_IR_EmitCpp_throwInvalidExportName___rarg(x_0, x_1, x_12);
lean::dec(x_1);
return x_40;
}
}
}
}
else
{
obj* x_44; obj* x_46; obj* x_48; obj* x_49; 
lean::dec(x_1);
lean::dec(x_0);
x_44 = lean::cnstr_get(x_4, 0);
x_46 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 x_48 = x_4;
} else {
 lean::inc(x_44);
 lean::inc(x_46);
 lean::dec(x_4);
 x_48 = lean::box(0);
}
if (lean::is_scalar(x_48)) {
 x_49 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_49 = x_48;
}
lean::cnstr_set(x_49, 0, x_44);
lean::cnstr_set(x_49, 1, x_46);
return x_49;
}
}
}
obj* _init_l_Lean_IR_EmitCpp_toCppName___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("::");
return x_0;
}
}
obj* l_Lean_IR_EmitCpp_toCppName(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_EmitCpp_getEnv(x_1, x_2);
if (lean::obj_tag(x_3) == 0)
{
obj* x_4; obj* x_6; obj* x_8; obj* x_9; 
x_4 = lean::cnstr_get(x_3, 0);
x_6 = lean::cnstr_get(x_3, 1);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_set(x_3, 0, lean::box(0));
 lean::cnstr_set(x_3, 1, lean::box(0));
 x_8 = x_3;
} else {
 lean::inc(x_4);
 lean::inc(x_6);
 lean::dec(x_3);
 x_8 = lean::box(0);
}
x_9 = lean_get_export_name_for(x_4, x_0);
lean::dec(x_4);
if (lean::obj_tag(x_9) == 0)
{
obj* x_11; uint8 x_12; 
x_11 = l_Lean_IR_EmitCpp_toBaseCppName___closed__1;
x_12 = lean_name_dec_eq(x_0, x_11);
if (x_12 == 0)
{
obj* x_13; obj* x_14; obj* x_15; 
x_13 = l_Lean_IR_EmitCpp_toBaseCppName___closed__2;
x_14 = l_Lean_Name_mangle(x_0, x_13);
if (lean::is_scalar(x_8)) {
 x_15 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_15 = x_8;
}
lean::cnstr_set(x_15, 0, x_14);
lean::cnstr_set(x_15, 1, x_6);
return x_15;
}
else
{
obj* x_17; obj* x_18; 
lean::dec(x_0);
x_17 = l_Lean_IR_EmitCpp_leanMainFn;
if (lean::is_scalar(x_8)) {
 x_18 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_18 = x_8;
}
lean::cnstr_set(x_18, 0, x_17);
lean::cnstr_set(x_18, 1, x_6);
return x_18;
}
}
else
{
obj* x_20; obj* x_23; obj* x_24; obj* x_25; 
lean::dec(x_0);
x_20 = lean::cnstr_get(x_9, 0);
lean::inc(x_20);
lean::dec(x_9);
x_23 = l_Lean_IR_EmitCpp_toCppName___closed__1;
x_24 = l_Lean_Name_toStringWithSep___main(x_23, x_20);
if (lean::is_scalar(x_8)) {
 x_25 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_25 = x_8;
}
lean::cnstr_set(x_25, 0, x_24);
lean::cnstr_set(x_25, 1, x_6);
return x_25;
}
}
else
{
obj* x_27; obj* x_29; obj* x_31; obj* x_32; 
lean::dec(x_0);
x_27 = lean::cnstr_get(x_3, 0);
x_29 = lean::cnstr_get(x_3, 1);
if (lean::is_exclusive(x_3)) {
 x_31 = x_3;
} else {
 lean::inc(x_27);
 lean::inc(x_29);
 lean::dec(x_3);
 x_31 = lean::box(0);
}
if (lean::is_scalar(x_31)) {
 x_32 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_32 = x_31;
}
lean::cnstr_set(x_32, 0, x_27);
lean::cnstr_set(x_32, 1, x_29);
return x_32;
}
}
}
obj* _init_l_Lean_IR_EmitCpp_toCppInitName___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("_init_");
return x_0;
}
}
obj* l_Lean_IR_EmitCpp_toCppInitName(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; 
lean::inc(x_1);
x_4 = l_Lean_IR_EmitCpp_getEnv(x_1, x_2);
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; obj* x_7; obj* x_9; obj* x_10; obj* x_12; obj* x_13; 
x_5 = lean::cnstr_get(x_4, 0);
x_7 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 x_9 = x_4;
} else {
 lean::inc(x_5);
 lean::inc(x_7);
 lean::dec(x_4);
 x_9 = lean::box(0);
}
x_10 = lean::box(0);
lean::inc(x_7);
if (lean::is_scalar(x_9)) {
 x_12 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_12 = x_9;
}
lean::cnstr_set(x_12, 0, x_10);
lean::cnstr_set(x_12, 1, x_7);
x_13 = lean_get_export_name_for(x_5, x_0);
lean::dec(x_5);
if (lean::obj_tag(x_13) == 0)
{
obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_22; 
lean::dec(x_1);
lean::dec(x_12);
x_17 = l_Lean_IR_EmitCpp_toBaseCppName___closed__2;
x_18 = l_Lean_Name_mangle(x_0, x_17);
x_19 = l_Lean_IR_EmitCpp_toCppInitName___closed__1;
x_20 = lean::string_append(x_19, x_18);
lean::dec(x_18);
x_22 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_22, 0, x_20);
lean::cnstr_set(x_22, 1, x_7);
return x_22;
}
else
{
obj* x_23; 
x_23 = lean::cnstr_get(x_13, 0);
lean::inc(x_23);
lean::dec(x_13);
switch (lean::obj_tag(x_23)) {
case 0:
{
obj* x_27; 
lean::dec(x_7);
x_27 = l_Lean_IR_EmitCpp_throwInvalidExportName___rarg(x_0, x_1, x_12);
lean::dec(x_1);
return x_27;
}
case 1:
{
obj* x_32; obj* x_34; obj* x_37; obj* x_38; obj* x_40; obj* x_41; obj* x_42; obj* x_43; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_12);
x_32 = lean::cnstr_get(x_23, 0);
lean::inc(x_32);
x_34 = lean::cnstr_get(x_23, 1);
lean::inc(x_34);
lean::dec(x_23);
x_37 = l_Lean_IR_EmitCpp_toCppInitName___closed__1;
x_38 = lean::string_append(x_37, x_34);
lean::dec(x_34);
x_40 = lean_name_mk_string(x_32, x_38);
x_41 = l_Lean_IR_EmitCpp_toCppName___closed__1;
x_42 = l_Lean_Name_toStringWithSep___main(x_41, x_40);
x_43 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_43, 0, x_42);
lean::cnstr_set(x_43, 1, x_7);
return x_43;
}
default:
{
obj* x_46; 
lean::dec(x_7);
lean::dec(x_23);
x_46 = l_Lean_IR_EmitCpp_throwInvalidExportName___rarg(x_0, x_1, x_12);
lean::dec(x_1);
return x_46;
}
}
}
}
else
{
obj* x_50; obj* x_52; obj* x_54; obj* x_55; 
lean::dec(x_1);
lean::dec(x_0);
x_50 = lean::cnstr_get(x_4, 0);
x_52 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 x_54 = x_4;
} else {
 lean::inc(x_50);
 lean::inc(x_52);
 lean::dec(x_4);
 x_54 = lean::box(0);
}
if (lean::is_scalar(x_54)) {
 x_55 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_55 = x_54;
}
lean::cnstr_set(x_55, 0, x_50);
lean::cnstr_set(x_55, 1, x_52);
return x_55;
}
}
}
obj* l_Nat_mforAux___main___at_Lean_IR_EmitCpp_emitFnDeclAux___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean::mk_nat_obj(0ul);
x_6 = lean::nat_dec_eq(x_2, x_5);
if (x_6 == 0)
{
obj* x_7; obj* x_8; obj* x_10; obj* x_11; uint8 x_13; 
x_7 = lean::mk_nat_obj(1ul);
x_8 = lean::nat_sub(x_2, x_7);
lean::dec(x_2);
x_10 = lean::nat_sub(x_1, x_8);
x_11 = lean::nat_sub(x_10, x_7);
lean::dec(x_10);
x_13 = lean::nat_dec_lt(x_5, x_11);
if (x_13 == 0)
{
obj* x_14; obj* x_16; obj* x_17; obj* x_18; uint8 x_20; obj* x_22; obj* x_23; obj* x_25; obj* x_26; 
x_14 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 x_16 = x_4;
} else {
 lean::inc(x_14);
 lean::dec(x_4);
 x_16 = lean::box(0);
}
x_17 = l_Lean_IR_paramInh;
x_18 = lean::array_get(x_17, x_0, x_11);
lean::dec(x_11);
x_20 = lean::cnstr_get_scalar<uint8>(x_18, sizeof(void*)*1 + 1);
lean::dec(x_18);
x_22 = l_Lean_IR_EmitCpp_toCppType___main(x_20);
x_23 = lean::string_append(x_14, x_22);
lean::dec(x_22);
x_25 = lean::box(0);
if (lean::is_scalar(x_16)) {
 x_26 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_26 = x_16;
}
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_23);
x_2 = x_8;
x_4 = x_26;
goto _start;
}
else
{
obj* x_28; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; uint8 x_36; obj* x_38; obj* x_39; obj* x_41; obj* x_42; 
x_28 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 x_30 = x_4;
} else {
 lean::inc(x_28);
 lean::dec(x_4);
 x_30 = lean::box(0);
}
x_31 = l_List_reprAux___main___rarg___closed__1;
x_32 = lean::string_append(x_28, x_31);
x_33 = l_Lean_IR_paramInh;
x_34 = lean::array_get(x_33, x_0, x_11);
lean::dec(x_11);
x_36 = lean::cnstr_get_scalar<uint8>(x_34, sizeof(void*)*1 + 1);
lean::dec(x_34);
x_38 = l_Lean_IR_EmitCpp_toCppType___main(x_36);
x_39 = lean::string_append(x_32, x_38);
lean::dec(x_38);
x_41 = lean::box(0);
if (lean::is_scalar(x_30)) {
 x_42 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_42 = x_30;
}
lean::cnstr_set(x_42, 0, x_41);
lean::cnstr_set(x_42, 1, x_39);
x_2 = x_8;
x_4 = x_42;
goto _start;
}
}
else
{
obj* x_45; obj* x_47; obj* x_48; obj* x_49; 
lean::dec(x_2);
x_45 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 x_47 = x_4;
} else {
 lean::inc(x_45);
 lean::dec(x_4);
 x_47 = lean::box(0);
}
x_48 = lean::box(0);
if (lean::is_scalar(x_47)) {
 x_49 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_49 = x_47;
}
lean::cnstr_set(x_49, 0, x_48);
lean::cnstr_set(x_49, 1, x_45);
return x_49;
}
}
}
obj* _init_l_Lean_IR_EmitCpp_emitFnDeclAux___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string(" ");
return x_0;
}
}
obj* _init_l_Lean_IR_EmitCpp_emitFnDeclAux___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string(";");
return x_0;
}
}
obj* _init_l_Lean_IR_EmitCpp_emitFnDeclAux___closed__3() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("extern ");
return x_0;
}
}
obj* l_Lean_IR_EmitCpp_emitFnDeclAux(obj* x_0, obj* x_1, uint8 x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; obj* x_7; 
x_5 = l_Lean_IR_Decl_params___main(x_0);
x_6 = l_Array_isEmpty___rarg(x_5);
if (x_6 == 0)
{
obj* x_9; 
x_9 = lean::cnstr_get(x_4, 1);
lean::inc(x_9);
lean::dec(x_4);
x_7 = x_9;
goto lbl_8;
}
else
{
if (x_2 == 0)
{
obj* x_12; 
x_12 = lean::cnstr_get(x_4, 1);
lean::inc(x_12);
lean::dec(x_4);
x_7 = x_12;
goto lbl_8;
}
else
{
obj* x_15; obj* x_18; obj* x_19; 
x_15 = lean::cnstr_get(x_4, 1);
lean::inc(x_15);
lean::dec(x_4);
x_18 = l_Lean_IR_EmitCpp_emitFnDeclAux___closed__3;
x_19 = lean::string_append(x_15, x_18);
x_7 = x_19;
goto lbl_8;
}
}
lbl_8:
{
uint8 x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; 
x_20 = l_Lean_IR_Decl_resultType___main(x_0);
x_21 = l_Lean_IR_EmitCpp_toCppType___main(x_20);
x_22 = l_Lean_IR_EmitCpp_emitFnDeclAux___closed__1;
x_23 = lean::string_append(x_21, x_22);
x_24 = lean::string_append(x_23, x_1);
x_25 = lean::string_append(x_7, x_24);
lean::dec(x_24);
if (x_6 == 0)
{
obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_33; 
x_27 = l_Prod_HasRepr___rarg___closed__1;
x_28 = lean::string_append(x_25, x_27);
x_29 = lean::box(0);
x_30 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_30, 0, x_29);
lean::cnstr_set(x_30, 1, x_28);
x_31 = lean::array_get_size(x_5);
lean::inc(x_31);
x_33 = l_Nat_mforAux___main___at_Lean_IR_EmitCpp_emitFnDeclAux___spec__1(x_5, x_31, x_31, x_3, x_30);
lean::dec(x_31);
lean::dec(x_5);
if (lean::obj_tag(x_33) == 0)
{
obj* x_36; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; 
x_36 = lean::cnstr_get(x_33, 1);
if (lean::is_exclusive(x_33)) {
 lean::cnstr_release(x_33, 0);
 x_38 = x_33;
} else {
 lean::inc(x_36);
 lean::dec(x_33);
 x_38 = lean::box(0);
}
x_39 = l_Option_HasRepr___rarg___closed__3;
x_40 = lean::string_append(x_36, x_39);
x_41 = l_Lean_IR_EmitCpp_emitFnDeclAux___closed__2;
x_42 = lean::string_append(x_40, x_41);
x_43 = l_IO_println___rarg___closed__1;
x_44 = lean::string_append(x_42, x_43);
if (lean::is_scalar(x_38)) {
 x_45 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_45 = x_38;
}
lean::cnstr_set(x_45, 0, x_29);
lean::cnstr_set(x_45, 1, x_44);
return x_45;
}
else
{
obj* x_46; obj* x_48; obj* x_50; obj* x_51; 
x_46 = lean::cnstr_get(x_33, 0);
x_48 = lean::cnstr_get(x_33, 1);
if (lean::is_exclusive(x_33)) {
 x_50 = x_33;
} else {
 lean::inc(x_46);
 lean::inc(x_48);
 lean::dec(x_33);
 x_50 = lean::box(0);
}
if (lean::is_scalar(x_50)) {
 x_51 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_51 = x_50;
}
lean::cnstr_set(x_51, 0, x_46);
lean::cnstr_set(x_51, 1, x_48);
return x_51;
}
}
else
{
obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; 
lean::dec(x_5);
x_53 = l_Lean_IR_EmitCpp_emitFnDeclAux___closed__2;
x_54 = lean::string_append(x_25, x_53);
x_55 = l_IO_println___rarg___closed__1;
x_56 = lean::string_append(x_54, x_55);
x_57 = lean::box(0);
x_58 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_58, 0, x_57);
lean::cnstr_set(x_58, 1, x_56);
return x_58;
}
}
}
}
obj* l_Nat_mforAux___main___at_Lean_IR_EmitCpp_emitFnDeclAux___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Nat_mforAux___main___at_Lean_IR_EmitCpp_emitFnDeclAux___spec__1(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_3);
return x_5;
}
}
obj* l_Lean_IR_EmitCpp_emitFnDeclAux___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; obj* x_6; 
x_5 = lean::unbox(x_2);
x_6 = l_Lean_IR_EmitCpp_emitFnDeclAux(x_0, x_1, x_5, x_3, x_4);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_3);
return x_6;
}
}
obj* l_Lean_IR_EmitCpp_emitFnDecl(obj* x_0, uint8 x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_6; 
x_4 = l_Lean_IR_Decl_name___main(x_0);
lean::inc(x_2);
x_6 = l_Lean_IR_EmitCpp_openNamespacesFor(x_4, x_2, x_3);
if (lean::obj_tag(x_6) == 0)
{
obj* x_7; obj* x_9; obj* x_10; obj* x_11; obj* x_14; 
x_7 = lean::cnstr_get(x_6, 1);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 x_9 = x_6;
} else {
 lean::inc(x_7);
 lean::dec(x_6);
 x_9 = lean::box(0);
}
x_10 = lean::box(0);
if (lean::is_scalar(x_9)) {
 x_11 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_11 = x_9;
}
lean::cnstr_set(x_11, 0, x_10);
lean::cnstr_set(x_11, 1, x_7);
lean::inc(x_2);
lean::inc(x_4);
x_14 = l_Lean_IR_EmitCpp_toBaseCppName(x_4, x_2, x_11);
if (lean::obj_tag(x_14) == 0)
{
obj* x_15; obj* x_17; obj* x_19; obj* x_20; obj* x_21; 
x_15 = lean::cnstr_get(x_14, 0);
x_17 = lean::cnstr_get(x_14, 1);
if (lean::is_exclusive(x_14)) {
 x_19 = x_14;
} else {
 lean::inc(x_15);
 lean::inc(x_17);
 lean::dec(x_14);
 x_19 = lean::box(0);
}
if (lean::is_scalar(x_19)) {
 x_20 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_20 = x_19;
}
lean::cnstr_set(x_20, 0, x_10);
lean::cnstr_set(x_20, 1, x_17);
x_21 = l_Lean_IR_EmitCpp_emitFnDeclAux(x_0, x_15, x_1, x_2, x_20);
lean::dec(x_15);
if (lean::obj_tag(x_21) == 0)
{
obj* x_23; obj* x_25; obj* x_26; obj* x_27; 
x_23 = lean::cnstr_get(x_21, 1);
if (lean::is_exclusive(x_21)) {
 lean::cnstr_release(x_21, 0);
 x_25 = x_21;
} else {
 lean::inc(x_23);
 lean::dec(x_21);
 x_25 = lean::box(0);
}
if (lean::is_scalar(x_25)) {
 x_26 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_26 = x_25;
}
lean::cnstr_set(x_26, 0, x_10);
lean::cnstr_set(x_26, 1, x_23);
x_27 = l_Lean_IR_EmitCpp_closeNamespacesFor(x_4, x_2, x_26);
lean::dec(x_4);
return x_27;
}
else
{
obj* x_31; obj* x_33; obj* x_35; obj* x_36; 
lean::dec(x_4);
lean::dec(x_2);
x_31 = lean::cnstr_get(x_21, 0);
x_33 = lean::cnstr_get(x_21, 1);
if (lean::is_exclusive(x_21)) {
 x_35 = x_21;
} else {
 lean::inc(x_31);
 lean::inc(x_33);
 lean::dec(x_21);
 x_35 = lean::box(0);
}
if (lean::is_scalar(x_35)) {
 x_36 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_36 = x_35;
}
lean::cnstr_set(x_36, 0, x_31);
lean::cnstr_set(x_36, 1, x_33);
return x_36;
}
}
else
{
obj* x_39; obj* x_41; obj* x_43; obj* x_44; 
lean::dec(x_4);
lean::dec(x_2);
x_39 = lean::cnstr_get(x_14, 0);
x_41 = lean::cnstr_get(x_14, 1);
if (lean::is_exclusive(x_14)) {
 x_43 = x_14;
} else {
 lean::inc(x_39);
 lean::inc(x_41);
 lean::dec(x_14);
 x_43 = lean::box(0);
}
if (lean::is_scalar(x_43)) {
 x_44 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_44 = x_43;
}
lean::cnstr_set(x_44, 0, x_39);
lean::cnstr_set(x_44, 1, x_41);
return x_44;
}
}
else
{
obj* x_47; obj* x_49; obj* x_51; obj* x_52; 
lean::dec(x_4);
lean::dec(x_2);
x_47 = lean::cnstr_get(x_6, 0);
x_49 = lean::cnstr_get(x_6, 1);
if (lean::is_exclusive(x_6)) {
 x_51 = x_6;
} else {
 lean::inc(x_47);
 lean::inc(x_49);
 lean::dec(x_6);
 x_51 = lean::box(0);
}
if (lean::is_scalar(x_51)) {
 x_52 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_52 = x_51;
}
lean::cnstr_set(x_52, 0, x_47);
lean::cnstr_set(x_52, 1, x_49);
return x_52;
}
}
}
obj* l_Lean_IR_EmitCpp_emitFnDecl___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = lean::unbox(x_1);
x_5 = l_Lean_IR_EmitCpp_emitFnDecl(x_0, x_4, x_2, x_3);
lean::dec(x_0);
return x_5;
}
}
obj* l_List_foldl___main___at_Lean_IR_EmitCpp_cppQualifiedNameToName___spec__1(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
return x_0;
}
else
{
obj* x_2; obj* x_4; obj* x_7; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
lean::dec(x_1);
x_7 = lean_name_mk_string(x_0, x_2);
x_0 = x_7;
x_1 = x_4;
goto _start;
}
}
}
obj* l_Lean_IR_EmitCpp_cppQualifiedNameToName(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_1 = l_Lean_IR_EmitCpp_toCppName___closed__1;
x_2 = l_String_split(x_0, x_1);
x_3 = lean::box(0);
x_4 = l_List_foldl___main___at_Lean_IR_EmitCpp_cppQualifiedNameToName___spec__1(x_3, x_2);
return x_4;
}
}
obj* _init_l_Lean_IR_EmitCpp_emitExternDeclAux___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("invalid name");
return x_0;
}
}
obj* _init_l_Lean_IR_EmitCpp_emitExternDeclAux___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("extern \"C\" ");
return x_0;
}
}
obj* l_Lean_IR_EmitCpp_emitExternDeclAux(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = l_Lean_IR_EmitCpp_cppQualifiedNameToName(x_1);
x_5 = l_Lean_IR_EmitCpp_openNamespaces(x_4, x_2, x_3);
if (lean::obj_tag(x_5) == 0)
{
obj* x_6; obj* x_8; obj* x_9; obj* x_10; obj* x_12; 
x_6 = lean::cnstr_get(x_5, 1);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_release(x_5, 0);
 x_8 = x_5;
} else {
 lean::inc(x_6);
 lean::dec(x_5);
 x_8 = lean::box(0);
}
x_9 = lean::box(0);
if (lean::is_scalar(x_8)) {
 x_10 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_10 = x_8;
}
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_6);
lean::inc(x_2);
x_12 = l_Lean_IR_EmitCpp_getEnv(x_2, x_10);
if (lean::obj_tag(x_12) == 0)
{
obj* x_13; obj* x_15; obj* x_17; obj* x_18; uint8 x_19; 
x_13 = lean::cnstr_get(x_12, 0);
x_15 = lean::cnstr_get(x_12, 1);
if (lean::is_exclusive(x_12)) {
 lean::cnstr_set(x_12, 0, lean::box(0));
 lean::cnstr_set(x_12, 1, lean::box(0));
 x_17 = x_12;
} else {
 lean::inc(x_13);
 lean::inc(x_15);
 lean::dec(x_12);
 x_17 = lean::box(0);
}
x_18 = l_Lean_IR_Decl_name___main(x_0);
x_19 = l_Lean_isExternC(x_13, x_18);
lean::dec(x_18);
lean::dec(x_13);
if (x_19 == 0)
{
switch (lean::obj_tag(x_4)) {
case 0:
{
obj* x_23; obj* x_24; 
lean::dec(x_2);
x_23 = l_Lean_IR_EmitCpp_emitExternDeclAux___closed__1;
if (lean::is_scalar(x_17)) {
 x_24 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_24 = x_17;
 lean::cnstr_set_tag(x_17, 1);
}
lean::cnstr_set(x_24, 0, x_23);
lean::cnstr_set(x_24, 1, x_15);
return x_24;
}
case 1:
{
obj* x_25; obj* x_27; uint8 x_28; obj* x_29; 
x_25 = lean::cnstr_get(x_4, 1);
lean::inc(x_25);
if (lean::is_scalar(x_17)) {
 x_27 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_27 = x_17;
}
lean::cnstr_set(x_27, 0, x_9);
lean::cnstr_set(x_27, 1, x_15);
x_28 = 1;
x_29 = l_Lean_IR_EmitCpp_emitFnDeclAux(x_0, x_25, x_28, x_2, x_27);
lean::dec(x_25);
if (lean::obj_tag(x_29) == 0)
{
obj* x_31; obj* x_33; obj* x_34; obj* x_35; 
x_31 = lean::cnstr_get(x_29, 1);
if (lean::is_exclusive(x_29)) {
 lean::cnstr_release(x_29, 0);
 x_33 = x_29;
} else {
 lean::inc(x_31);
 lean::dec(x_29);
 x_33 = lean::box(0);
}
if (lean::is_scalar(x_33)) {
 x_34 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_34 = x_33;
}
lean::cnstr_set(x_34, 0, x_9);
lean::cnstr_set(x_34, 1, x_31);
x_35 = l_Lean_IR_EmitCpp_closeNamespaces(x_4, x_2, x_34);
lean::dec(x_2);
lean::dec(x_4);
return x_35;
}
else
{
obj* x_40; obj* x_42; obj* x_44; obj* x_45; 
lean::dec(x_4);
lean::dec(x_2);
x_40 = lean::cnstr_get(x_29, 0);
x_42 = lean::cnstr_get(x_29, 1);
if (lean::is_exclusive(x_29)) {
 x_44 = x_29;
} else {
 lean::inc(x_40);
 lean::inc(x_42);
 lean::dec(x_29);
 x_44 = lean::box(0);
}
if (lean::is_scalar(x_44)) {
 x_45 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_45 = x_44;
}
lean::cnstr_set(x_45, 0, x_40);
lean::cnstr_set(x_45, 1, x_42);
return x_45;
}
}
default:
{
obj* x_48; obj* x_49; 
lean::dec(x_4);
lean::dec(x_2);
x_48 = l_Lean_IR_EmitCpp_emitExternDeclAux___closed__1;
if (lean::is_scalar(x_17)) {
 x_49 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_49 = x_17;
 lean::cnstr_set_tag(x_17, 1);
}
lean::cnstr_set(x_49, 0, x_48);
lean::cnstr_set(x_49, 1, x_15);
return x_49;
}
}
}
else
{
obj* x_50; obj* x_51; 
x_50 = l_Lean_IR_EmitCpp_emitExternDeclAux___closed__2;
x_51 = lean::string_append(x_15, x_50);
switch (lean::obj_tag(x_4)) {
case 0:
{
obj* x_53; obj* x_54; 
lean::dec(x_2);
x_53 = l_Lean_IR_EmitCpp_emitExternDeclAux___closed__1;
if (lean::is_scalar(x_17)) {
 x_54 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_54 = x_17;
 lean::cnstr_set_tag(x_17, 1);
}
lean::cnstr_set(x_54, 0, x_53);
lean::cnstr_set(x_54, 1, x_51);
return x_54;
}
case 1:
{
obj* x_55; obj* x_57; uint8 x_58; obj* x_59; 
x_55 = lean::cnstr_get(x_4, 1);
lean::inc(x_55);
if (lean::is_scalar(x_17)) {
 x_57 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_57 = x_17;
}
lean::cnstr_set(x_57, 0, x_9);
lean::cnstr_set(x_57, 1, x_51);
x_58 = 0;
x_59 = l_Lean_IR_EmitCpp_emitFnDeclAux(x_0, x_55, x_58, x_2, x_57);
lean::dec(x_55);
if (lean::obj_tag(x_59) == 0)
{
obj* x_61; obj* x_63; obj* x_64; obj* x_65; 
x_61 = lean::cnstr_get(x_59, 1);
if (lean::is_exclusive(x_59)) {
 lean::cnstr_release(x_59, 0);
 x_63 = x_59;
} else {
 lean::inc(x_61);
 lean::dec(x_59);
 x_63 = lean::box(0);
}
if (lean::is_scalar(x_63)) {
 x_64 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_64 = x_63;
}
lean::cnstr_set(x_64, 0, x_9);
lean::cnstr_set(x_64, 1, x_61);
x_65 = l_Lean_IR_EmitCpp_closeNamespaces(x_4, x_2, x_64);
lean::dec(x_2);
lean::dec(x_4);
return x_65;
}
else
{
obj* x_70; obj* x_72; obj* x_74; obj* x_75; 
lean::dec(x_4);
lean::dec(x_2);
x_70 = lean::cnstr_get(x_59, 0);
x_72 = lean::cnstr_get(x_59, 1);
if (lean::is_exclusive(x_59)) {
 x_74 = x_59;
} else {
 lean::inc(x_70);
 lean::inc(x_72);
 lean::dec(x_59);
 x_74 = lean::box(0);
}
if (lean::is_scalar(x_74)) {
 x_75 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_75 = x_74;
}
lean::cnstr_set(x_75, 0, x_70);
lean::cnstr_set(x_75, 1, x_72);
return x_75;
}
}
default:
{
obj* x_78; obj* x_79; 
lean::dec(x_4);
lean::dec(x_2);
x_78 = l_Lean_IR_EmitCpp_emitExternDeclAux___closed__1;
if (lean::is_scalar(x_17)) {
 x_79 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_79 = x_17;
 lean::cnstr_set_tag(x_17, 1);
}
lean::cnstr_set(x_79, 0, x_78);
lean::cnstr_set(x_79, 1, x_51);
return x_79;
}
}
}
}
else
{
obj* x_82; obj* x_84; obj* x_86; obj* x_87; 
lean::dec(x_4);
lean::dec(x_2);
x_82 = lean::cnstr_get(x_12, 0);
x_84 = lean::cnstr_get(x_12, 1);
if (lean::is_exclusive(x_12)) {
 x_86 = x_12;
} else {
 lean::inc(x_82);
 lean::inc(x_84);
 lean::dec(x_12);
 x_86 = lean::box(0);
}
if (lean::is_scalar(x_86)) {
 x_87 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_87 = x_86;
}
lean::cnstr_set(x_87, 0, x_82);
lean::cnstr_set(x_87, 1, x_84);
return x_87;
}
}
else
{
obj* x_90; obj* x_92; obj* x_94; obj* x_95; 
lean::dec(x_4);
lean::dec(x_2);
x_90 = lean::cnstr_get(x_5, 0);
x_92 = lean::cnstr_get(x_5, 1);
if (lean::is_exclusive(x_5)) {
 x_94 = x_5;
} else {
 lean::inc(x_90);
 lean::inc(x_92);
 lean::dec(x_5);
 x_94 = lean::box(0);
}
if (lean::is_scalar(x_94)) {
 x_95 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_95 = x_94;
}
lean::cnstr_set(x_95, 0, x_90);
lean::cnstr_set(x_95, 1, x_92);
return x_95;
}
}
}
obj* l_Lean_IR_EmitCpp_emitExternDeclAux___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_IR_EmitCpp_emitExternDeclAux(x_0, x_1, x_2, x_3);
lean::dec(x_0);
return x_4;
}
}
obj* l_List_foldl___main___at_Lean_IR_EmitCpp_emitFnDecls___spec__1(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
return x_0;
}
else
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_2 = lean::cnstr_get(x_1, 0);
x_3 = lean::cnstr_get(x_1, 1);
x_4 = l_Lean_IR_Decl_name___main(x_2);
x_5 = lean::box(0);
x_6 = l_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_0, x_4, x_5);
x_0 = x_6;
x_1 = x_3;
goto _start;
}
}
}
obj* l_List_foldl___main___at_Lean_IR_EmitCpp_emitFnDecls___spec__2(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
return x_0;
}
else
{
obj* x_2; obj* x_4; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
lean::dec(x_1);
x_7 = l_Lean_IR_Decl_name___main(x_2);
x_8 = lean::box(0);
x_9 = l_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_0, x_7, x_8);
x_10 = l_Lean_IR_collectUsedDecls(x_2, x_9);
x_0 = x_10;
x_1 = x_4;
goto _start;
}
}
}
obj* l_RBNode_revFold___main___at_Lean_IR_EmitCpp_emitFnDecls___spec__4(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
return x_0;
}
else
{
obj* x_2; obj* x_4; obj* x_6; obj* x_9; obj* x_10; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_1, 3);
lean::inc(x_6);
lean::dec(x_1);
x_9 = l_RBNode_revFold___main___at_Lean_IR_EmitCpp_emitFnDecls___spec__4(x_0, x_6);
x_10 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_10, 0, x_4);
lean::cnstr_set(x_10, 1, x_9);
x_0 = x_10;
x_1 = x_2;
goto _start;
}
}
}
obj* l_RBTree_toList___at_Lean_IR_EmitCpp_emitFnDecls___spec__3(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::box(0);
x_2 = l_RBNode_revFold___main___at_Lean_IR_EmitCpp_emitFnDecls___spec__4(x_1, x_0);
return x_2;
}
}
obj* _init_l_List_mfor___main___at_Lean_IR_EmitCpp_emitFnDecls___spec__5___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("cpp");
x_2 = lean_name_mk_string(x_0, x_1);
return x_2;
}
}
obj* l_List_mfor___main___at_Lean_IR_EmitCpp_emitFnDecls___spec__5(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_7; obj* x_9; obj* x_10; obj* x_11; 
lean::dec(x_1);
lean::dec(x_3);
x_7 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 x_9 = x_4;
} else {
 lean::inc(x_7);
 lean::dec(x_4);
 x_9 = lean::box(0);
}
x_10 = lean::box(0);
if (lean::is_scalar(x_9)) {
 x_11 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_11 = x_9;
}
lean::cnstr_set(x_11, 0, x_10);
lean::cnstr_set(x_11, 1, x_7);
return x_11;
}
else
{
obj* x_12; obj* x_14; obj* x_19; 
x_12 = lean::cnstr_get(x_2, 0);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_2, 1);
lean::inc(x_14);
lean::dec(x_2);
lean::inc(x_3);
lean::inc(x_12);
x_19 = l_Lean_IR_EmitCpp_getDecl(x_12, x_3, x_4);
if (lean::obj_tag(x_19) == 0)
{
obj* x_20; obj* x_22; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; 
x_20 = lean::cnstr_get(x_19, 0);
x_22 = lean::cnstr_get(x_19, 1);
if (lean::is_exclusive(x_19)) {
 x_24 = x_19;
} else {
 lean::inc(x_20);
 lean::inc(x_22);
 lean::dec(x_19);
 x_24 = lean::box(0);
}
x_25 = lean::box(0);
if (lean::is_scalar(x_24)) {
 x_26 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_26 = x_24;
}
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_22);
x_27 = l_Lean_IR_Decl_name___main(x_20);
x_28 = l_List_mfor___main___at_Lean_IR_EmitCpp_emitFnDecls___spec__5___closed__1;
x_29 = l_Lean_getExternNameFor(x_0, x_28, x_27);
lean::dec(x_27);
if (lean::obj_tag(x_29) == 0)
{
uint8 x_32; 
lean::inc(x_1);
x_32 = l_Lean_NameSet_contains(x_1, x_12);
lean::dec(x_12);
if (x_32 == 0)
{
uint8 x_34; obj* x_36; 
x_34 = 1;
lean::inc(x_3);
x_36 = l_Lean_IR_EmitCpp_emitFnDecl(x_20, x_34, x_3, x_26);
lean::dec(x_20);
if (lean::obj_tag(x_36) == 0)
{
obj* x_38; obj* x_40; obj* x_41; 
x_38 = lean::cnstr_get(x_36, 1);
if (lean::is_exclusive(x_36)) {
 lean::cnstr_release(x_36, 0);
 x_40 = x_36;
} else {
 lean::inc(x_38);
 lean::dec(x_36);
 x_40 = lean::box(0);
}
if (lean::is_scalar(x_40)) {
 x_41 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_41 = x_40;
}
lean::cnstr_set(x_41, 0, x_25);
lean::cnstr_set(x_41, 1, x_38);
x_2 = x_14;
x_4 = x_41;
goto _start;
}
else
{
obj* x_46; obj* x_48; obj* x_50; obj* x_51; 
lean::dec(x_14);
lean::dec(x_1);
lean::dec(x_3);
x_46 = lean::cnstr_get(x_36, 0);
x_48 = lean::cnstr_get(x_36, 1);
if (lean::is_exclusive(x_36)) {
 x_50 = x_36;
} else {
 lean::inc(x_46);
 lean::inc(x_48);
 lean::dec(x_36);
 x_50 = lean::box(0);
}
if (lean::is_scalar(x_50)) {
 x_51 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_51 = x_50;
}
lean::cnstr_set(x_51, 0, x_46);
lean::cnstr_set(x_51, 1, x_48);
return x_51;
}
}
else
{
uint8 x_52; obj* x_54; 
x_52 = 0;
lean::inc(x_3);
x_54 = l_Lean_IR_EmitCpp_emitFnDecl(x_20, x_52, x_3, x_26);
lean::dec(x_20);
if (lean::obj_tag(x_54) == 0)
{
obj* x_56; obj* x_58; obj* x_59; 
x_56 = lean::cnstr_get(x_54, 1);
if (lean::is_exclusive(x_54)) {
 lean::cnstr_release(x_54, 0);
 x_58 = x_54;
} else {
 lean::inc(x_56);
 lean::dec(x_54);
 x_58 = lean::box(0);
}
if (lean::is_scalar(x_58)) {
 x_59 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_59 = x_58;
}
lean::cnstr_set(x_59, 0, x_25);
lean::cnstr_set(x_59, 1, x_56);
x_2 = x_14;
x_4 = x_59;
goto _start;
}
else
{
obj* x_64; obj* x_66; obj* x_68; obj* x_69; 
lean::dec(x_14);
lean::dec(x_1);
lean::dec(x_3);
x_64 = lean::cnstr_get(x_54, 0);
x_66 = lean::cnstr_get(x_54, 1);
if (lean::is_exclusive(x_54)) {
 x_68 = x_54;
} else {
 lean::inc(x_64);
 lean::inc(x_66);
 lean::dec(x_54);
 x_68 = lean::box(0);
}
if (lean::is_scalar(x_68)) {
 x_69 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_69 = x_68;
}
lean::cnstr_set(x_69, 0, x_64);
lean::cnstr_set(x_69, 1, x_66);
return x_69;
}
}
}
else
{
obj* x_71; obj* x_75; 
lean::dec(x_12);
x_71 = lean::cnstr_get(x_29, 0);
lean::inc(x_71);
lean::dec(x_29);
lean::inc(x_3);
x_75 = l_Lean_IR_EmitCpp_emitExternDeclAux(x_20, x_71, x_3, x_26);
lean::dec(x_20);
if (lean::obj_tag(x_75) == 0)
{
obj* x_77; obj* x_79; obj* x_80; 
x_77 = lean::cnstr_get(x_75, 1);
if (lean::is_exclusive(x_75)) {
 lean::cnstr_release(x_75, 0);
 x_79 = x_75;
} else {
 lean::inc(x_77);
 lean::dec(x_75);
 x_79 = lean::box(0);
}
if (lean::is_scalar(x_79)) {
 x_80 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_80 = x_79;
}
lean::cnstr_set(x_80, 0, x_25);
lean::cnstr_set(x_80, 1, x_77);
x_2 = x_14;
x_4 = x_80;
goto _start;
}
else
{
obj* x_85; obj* x_87; obj* x_89; obj* x_90; 
lean::dec(x_14);
lean::dec(x_1);
lean::dec(x_3);
x_85 = lean::cnstr_get(x_75, 0);
x_87 = lean::cnstr_get(x_75, 1);
if (lean::is_exclusive(x_75)) {
 x_89 = x_75;
} else {
 lean::inc(x_85);
 lean::inc(x_87);
 lean::dec(x_75);
 x_89 = lean::box(0);
}
if (lean::is_scalar(x_89)) {
 x_90 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_90 = x_89;
}
lean::cnstr_set(x_90, 0, x_85);
lean::cnstr_set(x_90, 1, x_87);
return x_90;
}
}
}
else
{
obj* x_95; obj* x_97; obj* x_99; obj* x_100; 
lean::dec(x_12);
lean::dec(x_14);
lean::dec(x_1);
lean::dec(x_3);
x_95 = lean::cnstr_get(x_19, 0);
x_97 = lean::cnstr_get(x_19, 1);
if (lean::is_exclusive(x_19)) {
 x_99 = x_19;
} else {
 lean::inc(x_95);
 lean::inc(x_97);
 lean::dec(x_19);
 x_99 = lean::box(0);
}
if (lean::is_scalar(x_99)) {
 x_100 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_100 = x_99;
}
lean::cnstr_set(x_100, 0, x_95);
lean::cnstr_set(x_100, 1, x_97);
return x_100;
}
}
}
}
obj* l_Lean_IR_EmitCpp_emitFnDecls(obj* x_0, obj* x_1) {
_start:
{
obj* x_3; 
lean::inc(x_0);
x_3 = l_Lean_IR_EmitCpp_getEnv(x_0, x_1);
if (lean::obj_tag(x_3) == 0)
{
obj* x_4; obj* x_6; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
x_4 = lean::cnstr_get(x_3, 0);
x_6 = lean::cnstr_get(x_3, 1);
if (lean::is_exclusive(x_3)) {
 x_8 = x_3;
} else {
 lean::inc(x_4);
 lean::inc(x_6);
 lean::dec(x_3);
 x_8 = lean::box(0);
}
x_9 = lean::box(0);
if (lean::is_scalar(x_8)) {
 x_10 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_10 = x_8;
}
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_6);
x_11 = l_Lean_IR_declMapExt;
x_12 = l_Lean_PersistentEnvExtension_getEntries___rarg(x_11, x_4);
x_13 = lean::box(0);
x_14 = l_List_foldl___main___at_Lean_IR_EmitCpp_emitFnDecls___spec__1(x_13, x_12);
x_15 = l_List_foldl___main___at_Lean_IR_EmitCpp_emitFnDecls___spec__2(x_13, x_12);
x_16 = l_RBTree_toList___at_Lean_IR_EmitCpp_emitFnDecls___spec__3(x_15);
x_17 = l_List_mfor___main___at_Lean_IR_EmitCpp_emitFnDecls___spec__5(x_4, x_14, x_16, x_0, x_10);
lean::dec(x_4);
return x_17;
}
else
{
obj* x_20; obj* x_22; obj* x_24; obj* x_25; 
lean::dec(x_0);
x_20 = lean::cnstr_get(x_3, 0);
x_22 = lean::cnstr_get(x_3, 1);
if (lean::is_exclusive(x_3)) {
 x_24 = x_3;
} else {
 lean::inc(x_20);
 lean::inc(x_22);
 lean::dec(x_3);
 x_24 = lean::box(0);
}
if (lean::is_scalar(x_24)) {
 x_25 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_25 = x_24;
}
lean::cnstr_set(x_25, 0, x_20);
lean::cnstr_set(x_25, 1, x_22);
return x_25;
}
}
}
obj* l_List_foldl___main___at_Lean_IR_EmitCpp_emitFnDecls___spec__1___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_List_foldl___main___at_Lean_IR_EmitCpp_emitFnDecls___spec__1(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_List_mfor___main___at_Lean_IR_EmitCpp_emitFnDecls___spec__5___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_List_mfor___main___at_Lean_IR_EmitCpp_emitFnDecls___spec__5(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_0);
return x_5;
}
}
obj* l_List_mfor___main___at_Lean_IR_EmitCpp_emitMainFn___spec__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_3; obj* x_5; obj* x_6; obj* x_7; 
x_3 = lean::cnstr_get(x_2, 1);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_release(x_2, 0);
 x_5 = x_2;
} else {
 lean::inc(x_3);
 lean::dec(x_2);
 x_5 = lean::box(0);
}
x_6 = lean::box(0);
if (lean::is_scalar(x_5)) {
 x_7 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_7 = x_5;
}
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_3);
return x_7;
}
else
{
obj* x_8; obj* x_9; obj* x_10; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
x_8 = lean::cnstr_get(x_0, 0);
x_9 = lean::cnstr_get(x_0, 1);
x_10 = lean::cnstr_get(x_2, 1);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_release(x_2, 0);
 x_12 = x_2;
} else {
 lean::inc(x_10);
 lean::dec(x_2);
 x_12 = lean::box(0);
}
x_13 = lean::string_append(x_10, x_8);
x_14 = l_IO_println___rarg___closed__1;
x_15 = lean::string_append(x_13, x_14);
x_16 = lean::box(0);
if (lean::is_scalar(x_12)) {
 x_17 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_17 = x_12;
}
lean::cnstr_set(x_17, 0, x_16);
lean::cnstr_set(x_17, 1, x_15);
x_0 = x_9;
x_2 = x_17;
goto _start;
}
}
}
obj* l_Lean_IR_EmitCpp_emitLns___at_Lean_IR_EmitCpp_emitMainFn___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_List_mfor___main___at_Lean_IR_EmitCpp_emitMainFn___spec__2(x_0, x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_IR_EmitCpp_emitMainFn___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("invalid main function, incorrect arity when generating code");
return x_0;
}
}
obj* _init_l_Lean_IR_EmitCpp_emitMainFn___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("obj * w = lean::io_mk_world();");
return x_0;
}
}
obj* _init_l_Lean_IR_EmitCpp_emitMainFn___closed__3() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("w = initialize_");
return x_0;
}
}
obj* _init_l_Lean_IR_EmitCpp_emitMainFn___closed__4() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("(w);");
return x_0;
}
}
obj* _init_l_Lean_IR_EmitCpp_emitMainFn___closed__5() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_0 = lean::box(0);
x_1 = lean::mk_string("lean::scoped_task_manager tmanager(lean::hardware_concurrency());");
x_2 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_2, 0, x_1);
lean::cnstr_set(x_2, 1, x_0);
x_3 = lean::mk_string("if (io_result_is_ok(w)) {");
x_4 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_4, 0, x_3);
lean::cnstr_set(x_4, 1, x_2);
x_5 = lean::mk_string("lean::io_mark_end_initialization();");
x_6 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_4);
return x_6;
}
}
obj* _init_l_Lean_IR_EmitCpp_emitMainFn___closed__6() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_0 = lean::mk_string("w = ");
x_1 = l_Lean_IR_EmitCpp_leanMainFn;
x_2 = lean::string_append(x_0, x_1);
x_3 = lean::mk_string("(w);");
x_4 = lean::string_append(x_2, x_3);
lean::dec(x_3);
return x_4;
}
}
obj* _init_l_Lean_IR_EmitCpp_emitMainFn___closed__7() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_0 = lean::box(0);
x_1 = lean::mk_string("}");
x_2 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_2, 0, x_1);
lean::cnstr_set(x_2, 1, x_0);
x_3 = lean::mk_string("  return 1;");
x_4 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_4, 0, x_3);
lean::cnstr_set(x_4, 1, x_2);
x_5 = lean::mk_string("  lean::dec_ref(w);");
lean::inc(x_5);
x_7 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_7, 0, x_5);
lean::cnstr_set(x_7, 1, x_4);
x_8 = lean::mk_string("  lean::io_result_show_error(w);");
x_9 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_9, 0, x_8);
lean::cnstr_set(x_9, 1, x_7);
x_10 = lean::mk_string("} else {");
x_11 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_11, 0, x_10);
lean::cnstr_set(x_11, 1, x_9);
x_12 = lean::mk_string("  return ret;");
x_13 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_13, 0, x_12);
lean::cnstr_set(x_13, 1, x_11);
x_14 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_14, 0, x_5);
lean::cnstr_set(x_14, 1, x_13);
x_15 = lean::mk_string("  int ret = lean::unbox(io_result_get_value(w));");
x_16 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_16, 0, x_15);
lean::cnstr_set(x_16, 1, x_14);
x_17 = lean::mk_string("if (io_result_is_ok(w)) {");
x_18 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_18, 0, x_17);
lean::cnstr_set(x_18, 1, x_16);
return x_18;
}
}
obj* _init_l_Lean_IR_EmitCpp_emitMainFn___closed__8() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("int main(int argc, char ** argv) {");
return x_0;
}
}
obj* _init_l_Lean_IR_EmitCpp_emitMainFn___closed__9() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("lean::initialize_runtime_module();");
return x_0;
}
}
obj* _init_l_Lean_IR_EmitCpp_emitMainFn___closed__10() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("namespace lean { void initialize(); }");
return x_0;
}
}
obj* _init_l_Lean_IR_EmitCpp_emitMainFn___closed__11() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("lean::initialize();");
return x_0;
}
}
obj* _init_l_Lean_IR_EmitCpp_emitMainFn___closed__12() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_0 = lean::box(0);
x_1 = lean::mk_string("}");
x_2 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_2, 0, x_1);
lean::cnstr_set(x_2, 1, x_0);
x_3 = lean::mk_string(" in = n;");
x_4 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_4, 0, x_3);
lean::cnstr_set(x_4, 1, x_2);
x_5 = lean::mk_string(" obj* n = lean::alloc_cnstr(1,2,0); lean::cnstr_set(n, 0, lean::mk_string(argv[i])); lean::cnstr_set(n, 1, in);");
x_6 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_4);
x_7 = lean::mk_string(" i--;");
x_8 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_6);
x_9 = lean::mk_string("while (i > 1) {");
x_10 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_8);
x_11 = lean::mk_string("int i = argc;");
x_12 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_12, 0, x_11);
lean::cnstr_set(x_12, 1, x_10);
x_13 = lean::mk_string("obj* in = lean::box(0);");
x_14 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_14, 0, x_13);
lean::cnstr_set(x_14, 1, x_12);
return x_14;
}
}
obj* _init_l_Lean_IR_EmitCpp_emitMainFn___closed__13() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_0 = lean::mk_string("w = ");
x_1 = l_Lean_IR_EmitCpp_leanMainFn;
x_2 = lean::string_append(x_0, x_1);
x_3 = lean::mk_string("(in, w);");
x_4 = lean::string_append(x_2, x_3);
lean::dec(x_3);
return x_4;
}
}
obj* _init_l_Lean_IR_EmitCpp_emitMainFn___closed__14() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("function declaration expected");
return x_0;
}
}
obj* l_Lean_IR_EmitCpp_emitMainFn(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; 
x_2 = l_Lean_IR_EmitCpp_toBaseCppName___closed__1;
lean::inc(x_0);
x_4 = l_Lean_IR_EmitCpp_getDecl(x_2, x_0, x_1);
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; 
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
if (lean::obj_tag(x_5) == 0)
{
obj* x_7; obj* x_9; obj* x_10; obj* x_12; obj* x_14; uint8 x_15; 
x_7 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 lean::cnstr_set(x_4, 1, lean::box(0));
 x_9 = x_4;
} else {
 lean::inc(x_7);
 lean::dec(x_4);
 x_9 = lean::box(0);
}
x_10 = lean::cnstr_get(x_5, 1);
lean::inc(x_10);
x_12 = lean::array_get_size(x_10);
lean::dec(x_10);
x_14 = lean::mk_nat_obj(2ul);
x_15 = lean::nat_dec_eq(x_12, x_14);
if (x_15 == 0)
{
obj* x_16; uint8 x_17; 
x_16 = lean::mk_nat_obj(1ul);
x_17 = lean::nat_dec_eq(x_12, x_16);
lean::dec(x_12);
if (x_17 == 0)
{
obj* x_21; obj* x_22; 
lean::dec(x_5);
lean::dec(x_0);
x_21 = l_Lean_IR_EmitCpp_emitMainFn___closed__1;
if (lean::is_scalar(x_9)) {
 x_22 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_22 = x_9;
 lean::cnstr_set_tag(x_9, 1);
}
lean::cnstr_set(x_22, 0, x_21);
lean::cnstr_set(x_22, 1, x_7);
return x_22;
}
else
{
obj* x_23; obj* x_24; obj* x_25; obj* x_28; 
x_23 = lean::box(0);
if (lean::is_scalar(x_9)) {
 x_24 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_24 = x_9;
}
lean::cnstr_set(x_24, 0, x_23);
lean::cnstr_set(x_24, 1, x_7);
lean::inc(x_0);
x_28 = l_Lean_IR_EmitCpp_getEnv(x_0, x_24);
if (lean::obj_tag(x_28) == 0)
{
obj* x_29; obj* x_31; obj* x_34; uint8 x_36; 
x_29 = lean::cnstr_get(x_28, 0);
lean::inc(x_29);
x_31 = lean::cnstr_get(x_28, 1);
lean::inc(x_31);
lean::dec(x_28);
x_34 = l_Lean_IR_usesLeanNamespace___main(x_29, x_5);
lean::dec(x_29);
x_36 = lean::unbox(x_34);
if (x_36 == 0)
{
obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; 
x_37 = l_Lean_IR_EmitCpp_emitMainFn___closed__8;
x_38 = lean::string_append(x_31, x_37);
x_39 = l_IO_println___rarg___closed__1;
x_40 = lean::string_append(x_38, x_39);
x_41 = l_Lean_IR_EmitCpp_emitMainFn___closed__9;
x_42 = lean::string_append(x_40, x_41);
x_43 = lean::string_append(x_42, x_39);
x_25 = x_43;
goto lbl_26;
}
else
{
obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; 
x_44 = l_Lean_IR_EmitCpp_emitMainFn___closed__10;
x_45 = lean::string_append(x_31, x_44);
x_46 = l_IO_println___rarg___closed__1;
x_47 = lean::string_append(x_45, x_46);
x_48 = l_Lean_IR_EmitCpp_emitMainFn___closed__8;
x_49 = lean::string_append(x_47, x_48);
x_50 = lean::string_append(x_49, x_46);
x_51 = l_Lean_IR_EmitCpp_emitMainFn___closed__11;
x_52 = lean::string_append(x_50, x_51);
x_53 = lean::string_append(x_52, x_46);
x_25 = x_53;
goto lbl_26;
}
}
else
{
obj* x_56; obj* x_58; obj* x_60; obj* x_61; 
lean::dec(x_5);
lean::dec(x_0);
x_56 = lean::cnstr_get(x_28, 0);
x_58 = lean::cnstr_get(x_28, 1);
if (lean::is_exclusive(x_28)) {
 x_60 = x_28;
} else {
 lean::inc(x_56);
 lean::inc(x_58);
 lean::dec(x_28);
 x_60 = lean::box(0);
}
if (lean::is_scalar(x_60)) {
 x_61 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_61 = x_60;
}
lean::cnstr_set(x_61, 0, x_56);
lean::cnstr_set(x_61, 1, x_58);
return x_61;
}
lbl_26:
{
obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_68; 
x_62 = l_Lean_IR_EmitCpp_emitMainFn___closed__2;
x_63 = lean::string_append(x_25, x_62);
x_64 = l_IO_println___rarg___closed__1;
x_65 = lean::string_append(x_63, x_64);
x_66 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_66, 0, x_23);
lean::cnstr_set(x_66, 1, x_65);
lean::inc(x_0);
x_68 = l_Lean_IR_EmitCpp_getModName(x_0, x_66);
if (lean::obj_tag(x_68) == 0)
{
obj* x_69; obj* x_71; obj* x_73; obj* x_74; obj* x_75; obj* x_76; obj* x_77; obj* x_79; obj* x_80; obj* x_81; obj* x_83; obj* x_84; obj* x_85; obj* x_86; 
x_69 = lean::cnstr_get(x_68, 0);
x_71 = lean::cnstr_get(x_68, 1);
if (lean::is_exclusive(x_68)) {
 x_73 = x_68;
} else {
 lean::inc(x_69);
 lean::inc(x_71);
 lean::dec(x_68);
 x_73 = lean::box(0);
}
x_74 = l_String_splitAux___main___closed__1;
x_75 = l_Lean_Name_mangle(x_69, x_74);
x_76 = l_Lean_IR_EmitCpp_emitMainFn___closed__3;
x_77 = lean::string_append(x_76, x_75);
lean::dec(x_75);
x_79 = l_Lean_IR_EmitCpp_emitMainFn___closed__4;
x_80 = lean::string_append(x_77, x_79);
x_81 = lean::string_append(x_71, x_80);
lean::dec(x_80);
x_83 = lean::string_append(x_81, x_64);
if (lean::is_scalar(x_73)) {
 x_84 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_84 = x_73;
}
lean::cnstr_set(x_84, 0, x_23);
lean::cnstr_set(x_84, 1, x_83);
x_85 = l_Lean_IR_EmitCpp_emitMainFn___closed__5;
x_86 = l_List_mfor___main___at_Lean_IR_EmitCpp_emitMainFn___spec__2(x_85, x_0, x_84);
if (lean::obj_tag(x_86) == 0)
{
obj* x_87; obj* x_89; obj* x_90; obj* x_91; obj* x_92; obj* x_93; obj* x_94; obj* x_95; obj* x_96; obj* x_97; obj* x_98; 
x_87 = lean::cnstr_get(x_86, 1);
if (lean::is_exclusive(x_86)) {
 lean::cnstr_release(x_86, 0);
 x_89 = x_86;
} else {
 lean::inc(x_87);
 lean::dec(x_86);
 x_89 = lean::box(0);
}
x_90 = l_Lean_IR_EmitCpp_emitMainFn___closed__6;
x_91 = lean::string_append(x_87, x_90);
x_92 = lean::string_append(x_91, x_64);
x_93 = l_Lean_IR_EmitCpp_closeNamespacesAux___main___closed__1;
x_94 = lean::string_append(x_92, x_93);
x_95 = lean::string_append(x_94, x_64);
if (lean::is_scalar(x_89)) {
 x_96 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_96 = x_89;
}
lean::cnstr_set(x_96, 0, x_23);
lean::cnstr_set(x_96, 1, x_95);
x_97 = l_Lean_IR_EmitCpp_emitMainFn___closed__7;
x_98 = l_List_mfor___main___at_Lean_IR_EmitCpp_emitMainFn___spec__2(x_97, x_0, x_96);
lean::dec(x_0);
if (lean::obj_tag(x_98) == 0)
{
obj* x_100; obj* x_102; obj* x_103; obj* x_104; obj* x_105; 
x_100 = lean::cnstr_get(x_98, 1);
if (lean::is_exclusive(x_98)) {
 lean::cnstr_release(x_98, 0);
 x_102 = x_98;
} else {
 lean::inc(x_100);
 lean::dec(x_98);
 x_102 = lean::box(0);
}
x_103 = lean::string_append(x_100, x_93);
x_104 = lean::string_append(x_103, x_64);
if (lean::is_scalar(x_102)) {
 x_105 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_105 = x_102;
}
lean::cnstr_set(x_105, 0, x_23);
lean::cnstr_set(x_105, 1, x_104);
return x_105;
}
else
{
obj* x_106; obj* x_108; obj* x_110; obj* x_111; 
x_106 = lean::cnstr_get(x_98, 0);
x_108 = lean::cnstr_get(x_98, 1);
if (lean::is_exclusive(x_98)) {
 x_110 = x_98;
} else {
 lean::inc(x_106);
 lean::inc(x_108);
 lean::dec(x_98);
 x_110 = lean::box(0);
}
if (lean::is_scalar(x_110)) {
 x_111 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_111 = x_110;
}
lean::cnstr_set(x_111, 0, x_106);
lean::cnstr_set(x_111, 1, x_108);
return x_111;
}
}
else
{
obj* x_113; obj* x_115; obj* x_117; obj* x_118; 
lean::dec(x_0);
x_113 = lean::cnstr_get(x_86, 0);
x_115 = lean::cnstr_get(x_86, 1);
if (lean::is_exclusive(x_86)) {
 x_117 = x_86;
} else {
 lean::inc(x_113);
 lean::inc(x_115);
 lean::dec(x_86);
 x_117 = lean::box(0);
}
if (lean::is_scalar(x_117)) {
 x_118 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_118 = x_117;
}
lean::cnstr_set(x_118, 0, x_113);
lean::cnstr_set(x_118, 1, x_115);
return x_118;
}
}
else
{
obj* x_120; obj* x_122; obj* x_124; obj* x_125; 
lean::dec(x_0);
x_120 = lean::cnstr_get(x_68, 0);
x_122 = lean::cnstr_get(x_68, 1);
if (lean::is_exclusive(x_68)) {
 x_124 = x_68;
} else {
 lean::inc(x_120);
 lean::inc(x_122);
 lean::dec(x_68);
 x_124 = lean::box(0);
}
if (lean::is_scalar(x_124)) {
 x_125 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_125 = x_124;
}
lean::cnstr_set(x_125, 0, x_120);
lean::cnstr_set(x_125, 1, x_122);
return x_125;
}
}
}
}
else
{
obj* x_127; obj* x_128; obj* x_129; obj* x_132; 
lean::dec(x_12);
x_127 = lean::box(0);
if (lean::is_scalar(x_9)) {
 x_128 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_128 = x_9;
}
lean::cnstr_set(x_128, 0, x_127);
lean::cnstr_set(x_128, 1, x_7);
lean::inc(x_0);
x_132 = l_Lean_IR_EmitCpp_getEnv(x_0, x_128);
if (lean::obj_tag(x_132) == 0)
{
obj* x_133; obj* x_135; obj* x_138; uint8 x_140; 
x_133 = lean::cnstr_get(x_132, 0);
lean::inc(x_133);
x_135 = lean::cnstr_get(x_132, 1);
lean::inc(x_135);
lean::dec(x_132);
x_138 = l_Lean_IR_usesLeanNamespace___main(x_133, x_5);
lean::dec(x_133);
x_140 = lean::unbox(x_138);
if (x_140 == 0)
{
obj* x_141; obj* x_142; obj* x_143; obj* x_144; obj* x_145; obj* x_146; obj* x_147; 
x_141 = l_Lean_IR_EmitCpp_emitMainFn___closed__8;
x_142 = lean::string_append(x_135, x_141);
x_143 = l_IO_println___rarg___closed__1;
x_144 = lean::string_append(x_142, x_143);
x_145 = l_Lean_IR_EmitCpp_emitMainFn___closed__9;
x_146 = lean::string_append(x_144, x_145);
x_147 = lean::string_append(x_146, x_143);
x_129 = x_147;
goto lbl_130;
}
else
{
obj* x_148; obj* x_149; obj* x_150; obj* x_151; obj* x_152; obj* x_153; obj* x_154; obj* x_155; obj* x_156; obj* x_157; 
x_148 = l_Lean_IR_EmitCpp_emitMainFn___closed__10;
x_149 = lean::string_append(x_135, x_148);
x_150 = l_IO_println___rarg___closed__1;
x_151 = lean::string_append(x_149, x_150);
x_152 = l_Lean_IR_EmitCpp_emitMainFn___closed__8;
x_153 = lean::string_append(x_151, x_152);
x_154 = lean::string_append(x_153, x_150);
x_155 = l_Lean_IR_EmitCpp_emitMainFn___closed__11;
x_156 = lean::string_append(x_154, x_155);
x_157 = lean::string_append(x_156, x_150);
x_129 = x_157;
goto lbl_130;
}
}
else
{
obj* x_160; obj* x_162; obj* x_164; obj* x_165; 
lean::dec(x_5);
lean::dec(x_0);
x_160 = lean::cnstr_get(x_132, 0);
x_162 = lean::cnstr_get(x_132, 1);
if (lean::is_exclusive(x_132)) {
 x_164 = x_132;
} else {
 lean::inc(x_160);
 lean::inc(x_162);
 lean::dec(x_132);
 x_164 = lean::box(0);
}
if (lean::is_scalar(x_164)) {
 x_165 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_165 = x_164;
}
lean::cnstr_set(x_165, 0, x_160);
lean::cnstr_set(x_165, 1, x_162);
return x_165;
}
lbl_130:
{
obj* x_166; obj* x_167; obj* x_168; obj* x_169; obj* x_170; obj* x_172; 
x_166 = l_Lean_IR_EmitCpp_emitMainFn___closed__2;
x_167 = lean::string_append(x_129, x_166);
x_168 = l_IO_println___rarg___closed__1;
x_169 = lean::string_append(x_167, x_168);
x_170 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_170, 0, x_127);
lean::cnstr_set(x_170, 1, x_169);
lean::inc(x_0);
x_172 = l_Lean_IR_EmitCpp_getModName(x_0, x_170);
if (lean::obj_tag(x_172) == 0)
{
obj* x_173; obj* x_175; obj* x_177; obj* x_178; obj* x_179; obj* x_180; obj* x_181; obj* x_183; obj* x_184; obj* x_185; obj* x_187; obj* x_188; obj* x_189; obj* x_190; 
x_173 = lean::cnstr_get(x_172, 0);
x_175 = lean::cnstr_get(x_172, 1);
if (lean::is_exclusive(x_172)) {
 x_177 = x_172;
} else {
 lean::inc(x_173);
 lean::inc(x_175);
 lean::dec(x_172);
 x_177 = lean::box(0);
}
x_178 = l_String_splitAux___main___closed__1;
x_179 = l_Lean_Name_mangle(x_173, x_178);
x_180 = l_Lean_IR_EmitCpp_emitMainFn___closed__3;
x_181 = lean::string_append(x_180, x_179);
lean::dec(x_179);
x_183 = l_Lean_IR_EmitCpp_emitMainFn___closed__4;
x_184 = lean::string_append(x_181, x_183);
x_185 = lean::string_append(x_175, x_184);
lean::dec(x_184);
x_187 = lean::string_append(x_185, x_168);
if (lean::is_scalar(x_177)) {
 x_188 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_188 = x_177;
}
lean::cnstr_set(x_188, 0, x_127);
lean::cnstr_set(x_188, 1, x_187);
x_189 = l_Lean_IR_EmitCpp_emitMainFn___closed__5;
x_190 = l_List_mfor___main___at_Lean_IR_EmitCpp_emitMainFn___spec__2(x_189, x_0, x_188);
if (lean::obj_tag(x_190) == 0)
{
obj* x_191; obj* x_193; obj* x_194; obj* x_195; obj* x_196; 
x_191 = lean::cnstr_get(x_190, 1);
if (lean::is_exclusive(x_190)) {
 lean::cnstr_release(x_190, 0);
 x_193 = x_190;
} else {
 lean::inc(x_191);
 lean::dec(x_190);
 x_193 = lean::box(0);
}
if (lean::is_scalar(x_193)) {
 x_194 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_194 = x_193;
}
lean::cnstr_set(x_194, 0, x_127);
lean::cnstr_set(x_194, 1, x_191);
x_195 = l_Lean_IR_EmitCpp_emitMainFn___closed__12;
x_196 = l_List_mfor___main___at_Lean_IR_EmitCpp_emitMainFn___spec__2(x_195, x_0, x_194);
if (lean::obj_tag(x_196) == 0)
{
obj* x_197; obj* x_199; obj* x_200; obj* x_201; obj* x_202; obj* x_203; obj* x_204; obj* x_205; obj* x_206; obj* x_207; obj* x_208; 
x_197 = lean::cnstr_get(x_196, 1);
if (lean::is_exclusive(x_196)) {
 lean::cnstr_release(x_196, 0);
 x_199 = x_196;
} else {
 lean::inc(x_197);
 lean::dec(x_196);
 x_199 = lean::box(0);
}
x_200 = l_Lean_IR_EmitCpp_emitMainFn___closed__13;
x_201 = lean::string_append(x_197, x_200);
x_202 = lean::string_append(x_201, x_168);
x_203 = l_Lean_IR_EmitCpp_closeNamespacesAux___main___closed__1;
x_204 = lean::string_append(x_202, x_203);
x_205 = lean::string_append(x_204, x_168);
if (lean::is_scalar(x_199)) {
 x_206 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_206 = x_199;
}
lean::cnstr_set(x_206, 0, x_127);
lean::cnstr_set(x_206, 1, x_205);
x_207 = l_Lean_IR_EmitCpp_emitMainFn___closed__7;
x_208 = l_List_mfor___main___at_Lean_IR_EmitCpp_emitMainFn___spec__2(x_207, x_0, x_206);
lean::dec(x_0);
if (lean::obj_tag(x_208) == 0)
{
obj* x_210; obj* x_212; obj* x_213; obj* x_214; obj* x_215; 
x_210 = lean::cnstr_get(x_208, 1);
if (lean::is_exclusive(x_208)) {
 lean::cnstr_release(x_208, 0);
 x_212 = x_208;
} else {
 lean::inc(x_210);
 lean::dec(x_208);
 x_212 = lean::box(0);
}
x_213 = lean::string_append(x_210, x_203);
x_214 = lean::string_append(x_213, x_168);
if (lean::is_scalar(x_212)) {
 x_215 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_215 = x_212;
}
lean::cnstr_set(x_215, 0, x_127);
lean::cnstr_set(x_215, 1, x_214);
return x_215;
}
else
{
obj* x_216; obj* x_218; obj* x_220; obj* x_221; 
x_216 = lean::cnstr_get(x_208, 0);
x_218 = lean::cnstr_get(x_208, 1);
if (lean::is_exclusive(x_208)) {
 x_220 = x_208;
} else {
 lean::inc(x_216);
 lean::inc(x_218);
 lean::dec(x_208);
 x_220 = lean::box(0);
}
if (lean::is_scalar(x_220)) {
 x_221 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_221 = x_220;
}
lean::cnstr_set(x_221, 0, x_216);
lean::cnstr_set(x_221, 1, x_218);
return x_221;
}
}
else
{
obj* x_223; obj* x_225; obj* x_227; obj* x_228; 
lean::dec(x_0);
x_223 = lean::cnstr_get(x_196, 0);
x_225 = lean::cnstr_get(x_196, 1);
if (lean::is_exclusive(x_196)) {
 x_227 = x_196;
} else {
 lean::inc(x_223);
 lean::inc(x_225);
 lean::dec(x_196);
 x_227 = lean::box(0);
}
if (lean::is_scalar(x_227)) {
 x_228 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_228 = x_227;
}
lean::cnstr_set(x_228, 0, x_223);
lean::cnstr_set(x_228, 1, x_225);
return x_228;
}
}
else
{
obj* x_230; obj* x_232; obj* x_234; obj* x_235; 
lean::dec(x_0);
x_230 = lean::cnstr_get(x_190, 0);
x_232 = lean::cnstr_get(x_190, 1);
if (lean::is_exclusive(x_190)) {
 x_234 = x_190;
} else {
 lean::inc(x_230);
 lean::inc(x_232);
 lean::dec(x_190);
 x_234 = lean::box(0);
}
if (lean::is_scalar(x_234)) {
 x_235 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_235 = x_234;
}
lean::cnstr_set(x_235, 0, x_230);
lean::cnstr_set(x_235, 1, x_232);
return x_235;
}
}
else
{
obj* x_237; obj* x_239; obj* x_241; obj* x_242; 
lean::dec(x_0);
x_237 = lean::cnstr_get(x_172, 0);
x_239 = lean::cnstr_get(x_172, 1);
if (lean::is_exclusive(x_172)) {
 x_241 = x_172;
} else {
 lean::inc(x_237);
 lean::inc(x_239);
 lean::dec(x_172);
 x_241 = lean::box(0);
}
if (lean::is_scalar(x_241)) {
 x_242 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_242 = x_241;
}
lean::cnstr_set(x_242, 0, x_237);
lean::cnstr_set(x_242, 1, x_239);
return x_242;
}
}
}
}
else
{
obj* x_245; obj* x_247; obj* x_248; obj* x_249; 
lean::dec(x_5);
lean::dec(x_0);
x_245 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 x_247 = x_4;
} else {
 lean::inc(x_245);
 lean::dec(x_4);
 x_247 = lean::box(0);
}
x_248 = l_Lean_IR_EmitCpp_emitMainFn___closed__14;
if (lean::is_scalar(x_247)) {
 x_249 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_249 = x_247;
 lean::cnstr_set_tag(x_247, 1);
}
lean::cnstr_set(x_249, 0, x_248);
lean::cnstr_set(x_249, 1, x_245);
return x_249;
}
}
else
{
obj* x_251; obj* x_253; obj* x_255; obj* x_256; 
lean::dec(x_0);
x_251 = lean::cnstr_get(x_4, 0);
x_253 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 x_255 = x_4;
} else {
 lean::inc(x_251);
 lean::inc(x_253);
 lean::dec(x_4);
 x_255 = lean::box(0);
}
if (lean::is_scalar(x_255)) {
 x_256 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_256 = x_255;
}
lean::cnstr_set(x_256, 0, x_251);
lean::cnstr_set(x_256, 1, x_253);
return x_256;
}
}
}
obj* l_List_mfor___main___at_Lean_IR_EmitCpp_emitMainFn___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_List_mfor___main___at_Lean_IR_EmitCpp_emitMainFn___spec__2(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_IR_EmitCpp_emitLns___at_Lean_IR_EmitCpp_emitMainFn___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_EmitCpp_emitLns___at_Lean_IR_EmitCpp_emitMainFn___spec__1(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
return x_3;
}
}
uint8 l_List_foldr___main___at_Lean_IR_EmitCpp_hasMainFn___spec__1(uint8 x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
return x_0;
}
else
{
obj* x_2; obj* x_3; uint8 x_4; obj* x_5; obj* x_6; uint8 x_7; 
x_2 = lean::cnstr_get(x_1, 0);
x_3 = lean::cnstr_get(x_1, 1);
x_4 = l_List_foldr___main___at_Lean_IR_EmitCpp_hasMainFn___spec__1(x_0, x_3);
x_5 = l_Lean_IR_Decl_name___main(x_2);
x_6 = l_Lean_IR_EmitCpp_toBaseCppName___closed__1;
x_7 = lean_name_dec_eq(x_5, x_6);
lean::dec(x_5);
if (x_7 == 0)
{
return x_4;
}
else
{
uint8 x_9; 
x_9 = 1;
return x_9;
}
}
}
}
obj* l_Lean_IR_EmitCpp_hasMainFn(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_IR_EmitCpp_getEnv(x_0, x_1);
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; obj* x_5; obj* x_7; obj* x_8; obj* x_9; uint8 x_11; uint8 x_12; obj* x_14; obj* x_15; 
x_3 = lean::cnstr_get(x_2, 0);
x_5 = lean::cnstr_get(x_2, 1);
if (lean::is_exclusive(x_2)) {
 x_7 = x_2;
} else {
 lean::inc(x_3);
 lean::inc(x_5);
 lean::dec(x_2);
 x_7 = lean::box(0);
}
x_8 = l_Lean_IR_declMapExt;
x_9 = l_Lean_PersistentEnvExtension_getEntries___rarg(x_8, x_3);
lean::dec(x_3);
x_11 = 0;
x_12 = l_List_foldr___main___at_Lean_IR_EmitCpp_hasMainFn___spec__1(x_11, x_9);
lean::dec(x_9);
x_14 = lean::box(x_12);
if (lean::is_scalar(x_7)) {
 x_15 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_15 = x_7;
}
lean::cnstr_set(x_15, 0, x_14);
lean::cnstr_set(x_15, 1, x_5);
return x_15;
}
else
{
obj* x_16; obj* x_18; obj* x_20; obj* x_21; 
x_16 = lean::cnstr_get(x_2, 0);
x_18 = lean::cnstr_get(x_2, 1);
if (lean::is_exclusive(x_2)) {
 x_20 = x_2;
} else {
 lean::inc(x_16);
 lean::inc(x_18);
 lean::dec(x_2);
 x_20 = lean::box(0);
}
if (lean::is_scalar(x_20)) {
 x_21 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_21 = x_20;
}
lean::cnstr_set(x_21, 0, x_16);
lean::cnstr_set(x_21, 1, x_18);
return x_21;
}
}
}
obj* l_List_foldr___main___at_Lean_IR_EmitCpp_hasMainFn___spec__1___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; uint8 x_3; obj* x_4; 
x_2 = lean::unbox(x_0);
x_3 = l_List_foldr___main___at_Lean_IR_EmitCpp_hasMainFn___spec__1(x_2, x_1);
x_4 = lean::box(x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_IR_EmitCpp_emitMainFnIfNeeded(obj* x_0, obj* x_1) {
_start:
{
obj* x_3; 
lean::inc(x_0);
x_3 = l_Lean_IR_EmitCpp_hasMainFn(x_0, x_1);
if (lean::obj_tag(x_3) == 0)
{
obj* x_4; uint8 x_6; 
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_6 = lean::unbox(x_4);
if (x_6 == 0)
{
obj* x_8; obj* x_10; obj* x_11; obj* x_12; 
lean::dec(x_0);
x_8 = lean::cnstr_get(x_3, 1);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 x_10 = x_3;
} else {
 lean::inc(x_8);
 lean::dec(x_3);
 x_10 = lean::box(0);
}
x_11 = lean::box(0);
if (lean::is_scalar(x_10)) {
 x_12 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_12 = x_10;
}
lean::cnstr_set(x_12, 0, x_11);
lean::cnstr_set(x_12, 1, x_8);
return x_12;
}
else
{
obj* x_13; obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_13 = lean::cnstr_get(x_3, 1);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 x_15 = x_3;
} else {
 lean::inc(x_13);
 lean::dec(x_3);
 x_15 = lean::box(0);
}
x_16 = lean::box(0);
if (lean::is_scalar(x_15)) {
 x_17 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_17 = x_15;
}
lean::cnstr_set(x_17, 0, x_16);
lean::cnstr_set(x_17, 1, x_13);
x_18 = l_Lean_IR_EmitCpp_emitMainFn(x_0, x_17);
return x_18;
}
}
else
{
obj* x_20; obj* x_22; obj* x_24; obj* x_25; 
lean::dec(x_0);
x_20 = lean::cnstr_get(x_3, 0);
x_22 = lean::cnstr_get(x_3, 1);
if (lean::is_exclusive(x_3)) {
 x_24 = x_3;
} else {
 lean::inc(x_20);
 lean::inc(x_22);
 lean::dec(x_3);
 x_24 = lean::box(0);
}
if (lean::is_scalar(x_24)) {
 x_25 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_25 = x_24;
}
lean::cnstr_set(x_25, 0, x_20);
lean::cnstr_set(x_25, 1, x_22);
return x_25;
}
}
}
obj* l_Array_mforAux___main___at_Lean_IR_EmitCpp_emitFileHeader___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::array_get_size(x_0);
x_5 = lean::nat_dec_lt(x_1, x_4);
lean::dec(x_4);
if (x_5 == 0)
{
obj* x_8; obj* x_10; obj* x_11; obj* x_12; 
lean::dec(x_1);
x_8 = lean::cnstr_get(x_3, 1);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 x_10 = x_3;
} else {
 lean::inc(x_8);
 lean::dec(x_3);
 x_10 = lean::box(0);
}
x_11 = lean::box(0);
if (lean::is_scalar(x_10)) {
 x_12 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_12 = x_10;
}
lean::cnstr_set(x_12, 0, x_11);
lean::cnstr_set(x_12, 1, x_8);
return x_12;
}
else
{
obj* x_13; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_25; obj* x_27; obj* x_28; 
x_13 = lean::cnstr_get(x_3, 1);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 x_15 = x_3;
} else {
 lean::inc(x_13);
 lean::dec(x_3);
 x_15 = lean::box(0);
}
x_16 = lean::array_fget(x_0, x_1);
x_17 = lean::mk_nat_obj(1ul);
x_18 = lean::nat_add(x_1, x_17);
lean::dec(x_1);
x_20 = l_Lean_Name_toString___closed__1;
x_21 = l_Lean_Name_toStringWithSep___main(x_20, x_16);
x_22 = l_Lean_IR_EmitCpp_emitFnDeclAux___closed__1;
x_23 = lean::string_append(x_22, x_21);
lean::dec(x_21);
x_25 = lean::string_append(x_13, x_23);
lean::dec(x_23);
x_27 = lean::box(0);
if (lean::is_scalar(x_15)) {
 x_28 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_28 = x_15;
}
lean::cnstr_set(x_28, 0, x_27);
lean::cnstr_set(x_28, 1, x_25);
x_1 = x_18;
x_3 = x_28;
goto _start;
}
}
}
obj* _init_l_Lean_IR_EmitCpp_emitFileHeader___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
x_0 = lean::box(0);
x_1 = lean::mk_string("#endif");
x_2 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_2, 0, x_1);
lean::cnstr_set(x_2, 1, x_0);
x_3 = lean::mk_string("#pragma GCC diagnostic ignored \"-Wunused-but-set-variable\"");
x_4 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_4, 0, x_3);
lean::cnstr_set(x_4, 1, x_2);
x_5 = lean::mk_string("#pragma GCC diagnostic ignored \"-Wunused-label\"");
x_6 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_4);
x_7 = lean::mk_string("#pragma GCC diagnostic ignored \"-Wunused-parameter\"");
x_8 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_6);
x_9 = lean::mk_string("#elif defined(__GNUC__) && !defined(__CLANG__)");
x_10 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_8);
x_11 = lean::mk_string("#pragma clang diagnostic ignored \"-Wunused-label\"");
x_12 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_12, 0, x_11);
lean::cnstr_set(x_12, 1, x_10);
x_13 = lean::mk_string("#pragma clang diagnostic ignored \"-Wunused-parameter\"");
x_14 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_14, 0, x_13);
lean::cnstr_set(x_14, 1, x_12);
x_15 = lean::mk_string("#if defined(__clang__)");
x_16 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_16, 0, x_15);
lean::cnstr_set(x_16, 1, x_14);
x_17 = lean::mk_string("typedef lean::uint32 uint32; typedef lean::uint64 uint64;");
x_18 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_18, 0, x_17);
lean::cnstr_set(x_18, 1, x_16);
x_19 = lean::mk_string("typedef lean::uint8  uint8;  typedef lean::uint16 uint16;");
x_20 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_18);
x_21 = lean::mk_string("typedef lean::object obj;    typedef lean::usize  usize;");
x_22 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_22, 0, x_21);
lean::cnstr_set(x_22, 1, x_20);
return x_22;
}
}
obj* _init_l_Lean_IR_EmitCpp_emitFileHeader___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("// Lean compiler output");
return x_0;
}
}
obj* _init_l_Lean_IR_EmitCpp_emitFileHeader___closed__3() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("// Module: ");
return x_0;
}
}
obj* _init_l_Lean_IR_EmitCpp_emitFileHeader___closed__4() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("// Imports:");
return x_0;
}
}
obj* _init_l_Lean_IR_EmitCpp_emitFileHeader___closed__5() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("#include \"runtime/object.h\"");
return x_0;
}
}
obj* _init_l_Lean_IR_EmitCpp_emitFileHeader___closed__6() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("#include \"runtime/apply.h\"");
return x_0;
}
}
obj* _init_l_Lean_IR_EmitCpp_emitFileHeader___closed__7() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("#include \"runtime/init_module.h\"");
return x_0;
}
}
obj* l_Lean_IR_EmitCpp_emitFileHeader(obj* x_0, obj* x_1) {
_start:
{
obj* x_3; 
lean::inc(x_0);
x_3 = l_Lean_IR_EmitCpp_getEnv(x_0, x_1);
if (lean::obj_tag(x_3) == 0)
{
obj* x_4; obj* x_6; obj* x_8; obj* x_9; obj* x_10; obj* x_12; 
x_4 = lean::cnstr_get(x_3, 0);
x_6 = lean::cnstr_get(x_3, 1);
if (lean::is_exclusive(x_3)) {
 x_8 = x_3;
} else {
 lean::inc(x_4);
 lean::inc(x_6);
 lean::dec(x_3);
 x_8 = lean::box(0);
}
x_9 = lean::box(0);
if (lean::is_scalar(x_8)) {
 x_10 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_10 = x_8;
}
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_6);
lean::inc(x_0);
x_12 = l_Lean_IR_EmitCpp_getModName(x_0, x_10);
if (lean::obj_tag(x_12) == 0)
{
obj* x_13; obj* x_15; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_27; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_36; obj* x_37; 
x_13 = lean::cnstr_get(x_12, 0);
x_15 = lean::cnstr_get(x_12, 1);
if (lean::is_exclusive(x_12)) {
 x_17 = x_12;
} else {
 lean::inc(x_13);
 lean::inc(x_15);
 lean::dec(x_12);
 x_17 = lean::box(0);
}
x_18 = l_Lean_IR_EmitCpp_emitFileHeader___closed__2;
x_19 = lean::string_append(x_15, x_18);
x_20 = l_IO_println___rarg___closed__1;
x_21 = lean::string_append(x_19, x_20);
x_22 = l_Lean_Name_toString___closed__1;
x_23 = l_Lean_Name_toStringWithSep___main(x_22, x_13);
x_24 = l_Lean_IR_EmitCpp_emitFileHeader___closed__3;
x_25 = lean::string_append(x_24, x_23);
lean::dec(x_23);
x_27 = lean::string_append(x_21, x_25);
lean::dec(x_25);
x_29 = lean::string_append(x_27, x_20);
x_30 = l_Lean_IR_EmitCpp_emitFileHeader___closed__4;
x_31 = lean::string_append(x_29, x_30);
if (lean::is_scalar(x_17)) {
 x_32 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_32 = x_17;
}
lean::cnstr_set(x_32, 0, x_9);
lean::cnstr_set(x_32, 1, x_31);
x_33 = lean::cnstr_get(x_4, 3);
lean::inc(x_33);
lean::dec(x_4);
x_36 = lean::mk_nat_obj(0ul);
x_37 = l_Array_mforAux___main___at_Lean_IR_EmitCpp_emitFileHeader___spec__1(x_33, x_36, x_0, x_32);
lean::dec(x_33);
if (lean::obj_tag(x_37) == 0)
{
obj* x_39; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_53; 
x_39 = lean::cnstr_get(x_37, 1);
if (lean::is_exclusive(x_37)) {
 lean::cnstr_release(x_37, 0);
 x_41 = x_37;
} else {
 lean::inc(x_39);
 lean::dec(x_37);
 x_41 = lean::box(0);
}
x_42 = l_String_splitAux___main___closed__1;
x_43 = lean::string_append(x_39, x_42);
x_44 = lean::string_append(x_43, x_20);
x_45 = l_Lean_IR_EmitCpp_emitFileHeader___closed__5;
x_46 = lean::string_append(x_44, x_45);
x_47 = lean::string_append(x_46, x_20);
x_48 = l_Lean_IR_EmitCpp_emitFileHeader___closed__6;
x_49 = lean::string_append(x_47, x_48);
x_50 = lean::string_append(x_49, x_20);
if (lean::is_scalar(x_41)) {
 x_51 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_51 = x_41;
}
lean::cnstr_set(x_51, 0, x_9);
lean::cnstr_set(x_51, 1, x_50);
lean::inc(x_0);
x_53 = l_Lean_IR_EmitCpp_hasMainFn(x_0, x_51);
if (lean::obj_tag(x_53) == 0)
{
obj* x_54; uint8 x_56; 
x_54 = lean::cnstr_get(x_53, 0);
lean::inc(x_54);
x_56 = lean::unbox(x_54);
if (x_56 == 0)
{
obj* x_57; obj* x_59; obj* x_60; obj* x_61; obj* x_62; 
x_57 = lean::cnstr_get(x_53, 1);
if (lean::is_exclusive(x_53)) {
 lean::cnstr_release(x_53, 0);
 x_59 = x_53;
} else {
 lean::inc(x_57);
 lean::dec(x_53);
 x_59 = lean::box(0);
}
if (lean::is_scalar(x_59)) {
 x_60 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_60 = x_59;
}
lean::cnstr_set(x_60, 0, x_9);
lean::cnstr_set(x_60, 1, x_57);
x_61 = l_Lean_IR_EmitCpp_emitFileHeader___closed__1;
x_62 = l_List_mfor___main___at_Lean_IR_EmitCpp_emitMainFn___spec__2(x_61, x_0, x_60);
lean::dec(x_0);
return x_62;
}
else
{
obj* x_64; obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; 
x_64 = lean::cnstr_get(x_53, 1);
if (lean::is_exclusive(x_53)) {
 lean::cnstr_release(x_53, 0);
 x_66 = x_53;
} else {
 lean::inc(x_64);
 lean::dec(x_53);
 x_66 = lean::box(0);
}
x_67 = l_Lean_IR_EmitCpp_emitFileHeader___closed__7;
x_68 = lean::string_append(x_64, x_67);
x_69 = lean::string_append(x_68, x_20);
if (lean::is_scalar(x_66)) {
 x_70 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_70 = x_66;
}
lean::cnstr_set(x_70, 0, x_9);
lean::cnstr_set(x_70, 1, x_69);
x_71 = l_Lean_IR_EmitCpp_emitFileHeader___closed__1;
x_72 = l_List_mfor___main___at_Lean_IR_EmitCpp_emitMainFn___spec__2(x_71, x_0, x_70);
lean::dec(x_0);
return x_72;
}
}
else
{
obj* x_75; obj* x_77; obj* x_79; obj* x_80; 
lean::dec(x_0);
x_75 = lean::cnstr_get(x_53, 0);
x_77 = lean::cnstr_get(x_53, 1);
if (lean::is_exclusive(x_53)) {
 x_79 = x_53;
} else {
 lean::inc(x_75);
 lean::inc(x_77);
 lean::dec(x_53);
 x_79 = lean::box(0);
}
if (lean::is_scalar(x_79)) {
 x_80 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_80 = x_79;
}
lean::cnstr_set(x_80, 0, x_75);
lean::cnstr_set(x_80, 1, x_77);
return x_80;
}
}
else
{
obj* x_82; obj* x_84; obj* x_86; obj* x_87; 
lean::dec(x_0);
x_82 = lean::cnstr_get(x_37, 0);
x_84 = lean::cnstr_get(x_37, 1);
if (lean::is_exclusive(x_37)) {
 x_86 = x_37;
} else {
 lean::inc(x_82);
 lean::inc(x_84);
 lean::dec(x_37);
 x_86 = lean::box(0);
}
if (lean::is_scalar(x_86)) {
 x_87 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_87 = x_86;
}
lean::cnstr_set(x_87, 0, x_82);
lean::cnstr_set(x_87, 1, x_84);
return x_87;
}
}
else
{
obj* x_90; obj* x_92; obj* x_94; obj* x_95; 
lean::dec(x_4);
lean::dec(x_0);
x_90 = lean::cnstr_get(x_12, 0);
x_92 = lean::cnstr_get(x_12, 1);
if (lean::is_exclusive(x_12)) {
 x_94 = x_12;
} else {
 lean::inc(x_90);
 lean::inc(x_92);
 lean::dec(x_12);
 x_94 = lean::box(0);
}
if (lean::is_scalar(x_94)) {
 x_95 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_95 = x_94;
}
lean::cnstr_set(x_95, 0, x_90);
lean::cnstr_set(x_95, 1, x_92);
return x_95;
}
}
else
{
obj* x_97; obj* x_99; obj* x_101; obj* x_102; 
lean::dec(x_0);
x_97 = lean::cnstr_get(x_3, 0);
x_99 = lean::cnstr_get(x_3, 1);
if (lean::is_exclusive(x_3)) {
 x_101 = x_3;
} else {
 lean::inc(x_97);
 lean::inc(x_99);
 lean::dec(x_3);
 x_101 = lean::box(0);
}
if (lean::is_scalar(x_101)) {
 x_102 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_102 = x_101;
}
lean::cnstr_set(x_102, 0, x_97);
lean::cnstr_set(x_102, 1, x_99);
return x_102;
}
}
}
obj* l_Array_mforAux___main___at_Lean_IR_EmitCpp_emitFileHeader___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Array_mforAux___main___at_Lean_IR_EmitCpp_emitFileHeader___spec__1(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_2);
return x_4;
}
}
obj* _init_l_Lean_IR_EmitCpp_throwUnknownVar___rarg___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("unknown variable '");
return x_0;
}
}
obj* l_Lean_IR_EmitCpp_throwUnknownVar___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_10; obj* x_11; obj* x_13; obj* x_14; obj* x_15; 
x_3 = lean::cnstr_get(x_2, 1);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_release(x_2, 0);
 x_5 = x_2;
} else {
 lean::inc(x_3);
 lean::dec(x_2);
 x_5 = lean::box(0);
}
x_6 = l_Nat_repr(x_0);
x_7 = l_Lean_IR_VarId_HasToString___closed__1;
x_8 = lean::string_append(x_7, x_6);
lean::dec(x_6);
x_10 = l_Lean_IR_EmitCpp_throwUnknownVar___rarg___closed__1;
x_11 = lean::string_append(x_10, x_8);
lean::dec(x_8);
x_13 = l_Char_HasRepr___closed__1;
x_14 = lean::string_append(x_11, x_13);
if (lean::is_scalar(x_5)) {
 x_15 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_15 = x_5;
 lean::cnstr_set_tag(x_5, 1);
}
lean::cnstr_set(x_15, 0, x_14);
lean::cnstr_set(x_15, 1, x_3);
return x_15;
}
}
obj* l_Lean_IR_EmitCpp_throwUnknownVar(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_IR_EmitCpp_throwUnknownVar___rarg___boxed), 3, 0);
return x_1;
}
}
obj* l_Lean_IR_EmitCpp_throwUnknownVar___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_EmitCpp_throwUnknownVar___rarg(x_0, x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_IR_EmitCpp_throwUnknownVar___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_IR_EmitCpp_throwUnknownVar(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_AssocList_find___main___at_Lean_IR_EmitCpp_isObj___spec__2(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_2; 
x_2 = lean::box(0);
return x_2;
}
else
{
obj* x_3; obj* x_5; obj* x_7; uint8 x_10; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_1, 1);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_1, 2);
lean::inc(x_7);
lean::dec(x_1);
x_10 = lean::nat_dec_eq(x_3, x_0);
lean::dec(x_3);
if (x_10 == 0)
{
lean::dec(x_5);
x_1 = x_7;
goto _start;
}
else
{
obj* x_15; 
lean::dec(x_7);
x_15 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_15, 0, x_5);
return x_15;
}
}
}
}
obj* l_HashMapImp_find___at_Lean_IR_EmitCpp_isObj___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; usize x_4; usize x_5; obj* x_7; obj* x_8; 
x_2 = lean::cnstr_get(x_0, 1);
x_3 = lean::array_get_size(x_2);
x_4 = lean::usize_of_nat(x_1);
x_5 = lean::usize_modn(x_4, x_3);
lean::dec(x_3);
x_7 = lean::array_uget(x_2, x_5);
x_8 = l_AssocList_find___main___at_Lean_IR_EmitCpp_isObj___spec__2(x_1, x_7);
return x_8;
}
}
obj* l_Lean_IR_EmitCpp_isObj(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_6; obj* x_8; obj* x_9; obj* x_10; 
x_3 = lean::cnstr_get(x_2, 1);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_release(x_2, 0);
 x_5 = x_2;
} else {
 lean::inc(x_3);
 lean::dec(x_2);
 x_5 = lean::box(0);
}
x_6 = lean::box(0);
lean::inc(x_3);
if (lean::is_scalar(x_5)) {
 x_8 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_8 = x_5;
}
lean::cnstr_set(x_8, 0, x_6);
lean::cnstr_set(x_8, 1, x_3);
x_9 = lean::cnstr_get(x_1, 2);
x_10 = l_HashMapImp_find___at_Lean_IR_EmitCpp_isObj___spec__1(x_9, x_0);
if (lean::obj_tag(x_10) == 0)
{
obj* x_12; 
lean::dec(x_3);
x_12 = l_Lean_IR_EmitCpp_throwUnknownVar___rarg(x_0, x_1, x_8);
return x_12;
}
else
{
obj* x_15; uint8 x_18; uint8 x_19; obj* x_20; obj* x_21; 
lean::dec(x_8);
lean::dec(x_0);
x_15 = lean::cnstr_get(x_10, 0);
lean::inc(x_15);
lean::dec(x_10);
x_18 = lean::unbox(x_15);
x_19 = l_Lean_IR_IRType_isObj___main(x_18);
x_20 = lean::box(x_19);
x_21 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_21, 0, x_20);
lean::cnstr_set(x_21, 1, x_3);
return x_21;
}
}
}
obj* l_AssocList_find___main___at_Lean_IR_EmitCpp_isObj___spec__2___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_AssocList_find___main___at_Lean_IR_EmitCpp_isObj___spec__2(x_0, x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_HashMapImp_find___at_Lean_IR_EmitCpp_isObj___spec__1___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_HashMapImp_find___at_Lean_IR_EmitCpp_isObj___spec__1(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_IR_EmitCpp_isObj___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_EmitCpp_isObj(x_0, x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_AssocList_find___main___at_Lean_IR_EmitCpp_getJPParams___spec__2(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_2; 
x_2 = lean::box(0);
return x_2;
}
else
{
obj* x_3; obj* x_5; obj* x_7; uint8 x_10; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_1, 1);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_1, 2);
lean::inc(x_7);
lean::dec(x_1);
x_10 = lean::nat_dec_eq(x_3, x_0);
lean::dec(x_3);
if (x_10 == 0)
{
lean::dec(x_5);
x_1 = x_7;
goto _start;
}
else
{
obj* x_15; 
lean::dec(x_7);
x_15 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_15, 0, x_5);
return x_15;
}
}
}
}
obj* l_HashMapImp_find___at_Lean_IR_EmitCpp_getJPParams___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; usize x_4; usize x_5; obj* x_7; obj* x_8; 
x_2 = lean::cnstr_get(x_0, 1);
x_3 = lean::array_get_size(x_2);
x_4 = lean::usize_of_nat(x_1);
x_5 = lean::usize_modn(x_4, x_3);
lean::dec(x_3);
x_7 = lean::array_uget(x_2, x_5);
x_8 = l_AssocList_find___main___at_Lean_IR_EmitCpp_getJPParams___spec__2(x_1, x_7);
return x_8;
}
}
obj* _init_l_Lean_IR_EmitCpp_getJPParams___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("unknown join point");
return x_0;
}
}
obj* l_Lean_IR_EmitCpp_getJPParams(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_6; obj* x_7; 
x_3 = lean::cnstr_get(x_2, 1);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_release(x_2, 0);
 lean::cnstr_set(x_2, 1, lean::box(0));
 x_5 = x_2;
} else {
 lean::inc(x_3);
 lean::dec(x_2);
 x_5 = lean::box(0);
}
x_6 = lean::cnstr_get(x_1, 3);
x_7 = l_HashMapImp_find___at_Lean_IR_EmitCpp_getJPParams___spec__1(x_6, x_0);
if (lean::obj_tag(x_7) == 0)
{
obj* x_8; obj* x_9; 
x_8 = l_Lean_IR_EmitCpp_getJPParams___closed__1;
if (lean::is_scalar(x_5)) {
 x_9 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_9 = x_5;
 lean::cnstr_set_tag(x_5, 1);
}
lean::cnstr_set(x_9, 0, x_8);
lean::cnstr_set(x_9, 1, x_3);
return x_9;
}
else
{
obj* x_10; obj* x_13; 
x_10 = lean::cnstr_get(x_7, 0);
lean::inc(x_10);
lean::dec(x_7);
if (lean::is_scalar(x_5)) {
 x_13 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_13 = x_5;
}
lean::cnstr_set(x_13, 0, x_10);
lean::cnstr_set(x_13, 1, x_3);
return x_13;
}
}
}
obj* l_AssocList_find___main___at_Lean_IR_EmitCpp_getJPParams___spec__2___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_AssocList_find___main___at_Lean_IR_EmitCpp_getJPParams___spec__2(x_0, x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_HashMapImp_find___at_Lean_IR_EmitCpp_getJPParams___spec__1___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_HashMapImp_find___at_Lean_IR_EmitCpp_getJPParams___spec__1(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_IR_EmitCpp_getJPParams___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_EmitCpp_getJPParams(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
return x_3;
}
}
obj* _init_l_Lean_IR_EmitCpp_declareVar___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("; ");
return x_0;
}
}
obj* l_Lean_IR_EmitCpp_declareVar(obj* x_0, uint8 x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_6; obj* x_7; obj* x_8; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_16; obj* x_18; obj* x_19; obj* x_20; obj* x_21; 
x_4 = lean::cnstr_get(x_3, 1);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 x_6 = x_3;
} else {
 lean::inc(x_4);
 lean::dec(x_3);
 x_6 = lean::box(0);
}
x_7 = l_Lean_IR_EmitCpp_toCppType___main(x_1);
x_8 = lean::string_append(x_4, x_7);
lean::dec(x_7);
x_10 = l_Lean_IR_EmitCpp_emitFnDeclAux___closed__1;
x_11 = lean::string_append(x_8, x_10);
x_12 = l_Nat_repr(x_0);
x_13 = l_Lean_IR_VarId_HasToString___closed__1;
x_14 = lean::string_append(x_13, x_12);
lean::dec(x_12);
x_16 = lean::string_append(x_11, x_14);
lean::dec(x_14);
x_18 = l_Lean_IR_EmitCpp_declareVar___closed__1;
x_19 = lean::string_append(x_16, x_18);
x_20 = lean::box(0);
if (lean::is_scalar(x_6)) {
 x_21 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_21 = x_6;
}
lean::cnstr_set(x_21, 0, x_20);
lean::cnstr_set(x_21, 1, x_19);
return x_21;
}
}
obj* l_Lean_IR_EmitCpp_declareVar___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = lean::unbox(x_1);
x_5 = l_Lean_IR_EmitCpp_declareVar(x_0, x_4, x_2, x_3);
lean::dec(x_2);
return x_5;
}
}
obj* l_Array_mforAux___main___at_Lean_IR_EmitCpp_declareParams___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::array_get_size(x_0);
x_5 = lean::nat_dec_lt(x_1, x_4);
lean::dec(x_4);
if (x_5 == 0)
{
obj* x_8; obj* x_10; obj* x_11; obj* x_12; 
lean::dec(x_1);
x_8 = lean::cnstr_get(x_3, 1);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 x_10 = x_3;
} else {
 lean::inc(x_8);
 lean::dec(x_3);
 x_10 = lean::box(0);
}
x_11 = lean::box(0);
if (lean::is_scalar(x_10)) {
 x_12 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_12 = x_10;
}
lean::cnstr_set(x_12, 0, x_11);
lean::cnstr_set(x_12, 1, x_8);
return x_12;
}
else
{
obj* x_13; obj* x_14; obj* x_15; obj* x_17; uint8 x_19; obj* x_21; 
x_13 = lean::array_fget(x_0, x_1);
x_14 = lean::mk_nat_obj(1ul);
x_15 = lean::nat_add(x_1, x_14);
lean::dec(x_1);
x_17 = lean::cnstr_get(x_13, 0);
lean::inc(x_17);
x_19 = lean::cnstr_get_scalar<uint8>(x_13, sizeof(void*)*1 + 1);
lean::dec(x_13);
x_21 = l_Lean_IR_EmitCpp_declareVar(x_17, x_19, x_2, x_3);
if (lean::obj_tag(x_21) == 0)
{
obj* x_22; obj* x_24; obj* x_25; obj* x_26; 
x_22 = lean::cnstr_get(x_21, 1);
if (lean::is_exclusive(x_21)) {
 lean::cnstr_release(x_21, 0);
 x_24 = x_21;
} else {
 lean::inc(x_22);
 lean::dec(x_21);
 x_24 = lean::box(0);
}
x_25 = lean::box(0);
if (lean::is_scalar(x_24)) {
 x_26 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_26 = x_24;
}
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_22);
x_1 = x_15;
x_3 = x_26;
goto _start;
}
else
{
obj* x_29; obj* x_31; obj* x_33; obj* x_34; 
lean::dec(x_15);
x_29 = lean::cnstr_get(x_21, 0);
x_31 = lean::cnstr_get(x_21, 1);
if (lean::is_exclusive(x_21)) {
 x_33 = x_21;
} else {
 lean::inc(x_29);
 lean::inc(x_31);
 lean::dec(x_21);
 x_33 = lean::box(0);
}
if (lean::is_scalar(x_33)) {
 x_34 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_34 = x_33;
}
lean::cnstr_set(x_34, 0, x_29);
lean::cnstr_set(x_34, 1, x_31);
return x_34;
}
}
}
}
obj* l_Lean_IR_EmitCpp_declareParams(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::mk_nat_obj(0ul);
x_4 = l_Array_mforAux___main___at_Lean_IR_EmitCpp_declareParams___spec__1(x_0, x_3, x_1, x_2);
return x_4;
}
}
obj* l_Array_mforAux___main___at_Lean_IR_EmitCpp_declareParams___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Array_mforAux___main___at_Lean_IR_EmitCpp_declareParams___spec__1(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_2);
return x_4;
}
}
obj* l_Lean_IR_EmitCpp_declareParams___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_EmitCpp_declareParams(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_IR_EmitCpp_declareVars___main(obj* x_0, uint8 x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_6; uint8 x_8; obj* x_9; obj* x_12; 
x_6 = lean::cnstr_get(x_0, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*3);
x_9 = lean::cnstr_get(x_0, 2);
lean::inc(x_9);
lean::dec(x_0);
x_12 = l_Lean_IR_EmitCpp_declareVar(x_6, x_8, x_2, x_3);
if (lean::obj_tag(x_12) == 0)
{
obj* x_13; obj* x_15; obj* x_16; obj* x_17; uint8 x_18; 
x_13 = lean::cnstr_get(x_12, 1);
if (lean::is_exclusive(x_12)) {
 lean::cnstr_release(x_12, 0);
 x_15 = x_12;
} else {
 lean::inc(x_13);
 lean::dec(x_12);
 x_15 = lean::box(0);
}
x_16 = lean::box(0);
if (lean::is_scalar(x_15)) {
 x_17 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_17 = x_15;
}
lean::cnstr_set(x_17, 0, x_16);
lean::cnstr_set(x_17, 1, x_13);
x_18 = 1;
x_0 = x_9;
x_1 = x_18;
x_3 = x_17;
goto _start;
}
else
{
obj* x_21; obj* x_23; obj* x_25; obj* x_26; 
lean::dec(x_9);
x_21 = lean::cnstr_get(x_12, 0);
x_23 = lean::cnstr_get(x_12, 1);
if (lean::is_exclusive(x_12)) {
 x_25 = x_12;
} else {
 lean::inc(x_21);
 lean::inc(x_23);
 lean::dec(x_12);
 x_25 = lean::box(0);
}
if (lean::is_scalar(x_25)) {
 x_26 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_26 = x_25;
}
lean::cnstr_set(x_26, 0, x_21);
lean::cnstr_set(x_26, 1, x_23);
return x_26;
}
}
case 1:
{
obj* x_27; obj* x_29; obj* x_32; obj* x_33; 
x_27 = lean::cnstr_get(x_0, 1);
lean::inc(x_27);
x_29 = lean::cnstr_get(x_0, 3);
lean::inc(x_29);
lean::dec(x_0);
x_32 = lean::mk_nat_obj(0ul);
x_33 = l_Array_mforAux___main___at_Lean_IR_EmitCpp_declareParams___spec__1(x_27, x_32, x_2, x_3);
if (x_1 == 0)
{
if (lean::obj_tag(x_33) == 0)
{
obj* x_34; obj* x_36; obj* x_37; uint8 x_39; obj* x_41; obj* x_42; 
x_34 = lean::cnstr_get(x_33, 1);
if (lean::is_exclusive(x_33)) {
 lean::cnstr_release(x_33, 0);
 x_36 = x_33;
} else {
 lean::inc(x_34);
 lean::dec(x_33);
 x_36 = lean::box(0);
}
x_37 = lean::array_get_size(x_27);
lean::dec(x_27);
x_39 = lean::nat_dec_lt(x_32, x_37);
lean::dec(x_37);
x_41 = lean::box(0);
if (lean::is_scalar(x_36)) {
 x_42 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_42 = x_36;
}
lean::cnstr_set(x_42, 0, x_41);
lean::cnstr_set(x_42, 1, x_34);
x_0 = x_29;
x_1 = x_39;
x_3 = x_42;
goto _start;
}
else
{
obj* x_46; obj* x_48; obj* x_50; obj* x_51; 
lean::dec(x_27);
lean::dec(x_29);
x_46 = lean::cnstr_get(x_33, 0);
x_48 = lean::cnstr_get(x_33, 1);
if (lean::is_exclusive(x_33)) {
 x_50 = x_33;
} else {
 lean::inc(x_46);
 lean::inc(x_48);
 lean::dec(x_33);
 x_50 = lean::box(0);
}
if (lean::is_scalar(x_50)) {
 x_51 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_51 = x_50;
}
lean::cnstr_set(x_51, 0, x_46);
lean::cnstr_set(x_51, 1, x_48);
return x_51;
}
}
else
{
lean::dec(x_27);
if (lean::obj_tag(x_33) == 0)
{
obj* x_53; obj* x_55; obj* x_56; obj* x_57; uint8 x_58; 
x_53 = lean::cnstr_get(x_33, 1);
if (lean::is_exclusive(x_33)) {
 lean::cnstr_release(x_33, 0);
 x_55 = x_33;
} else {
 lean::inc(x_53);
 lean::dec(x_33);
 x_55 = lean::box(0);
}
x_56 = lean::box(0);
if (lean::is_scalar(x_55)) {
 x_57 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_57 = x_55;
}
lean::cnstr_set(x_57, 0, x_56);
lean::cnstr_set(x_57, 1, x_53);
x_58 = 1;
x_0 = x_29;
x_1 = x_58;
x_3 = x_57;
goto _start;
}
else
{
obj* x_61; obj* x_63; obj* x_65; obj* x_66; 
lean::dec(x_29);
x_61 = lean::cnstr_get(x_33, 0);
x_63 = lean::cnstr_get(x_33, 1);
if (lean::is_exclusive(x_33)) {
 x_65 = x_33;
} else {
 lean::inc(x_61);
 lean::inc(x_63);
 lean::dec(x_33);
 x_65 = lean::box(0);
}
if (lean::is_scalar(x_65)) {
 x_66 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_66 = x_65;
}
lean::cnstr_set(x_66, 0, x_61);
lean::cnstr_set(x_66, 1, x_63);
return x_66;
}
}
}
default:
{
obj* x_67; 
x_67 = lean::box(0);
x_4 = x_67;
goto lbl_5;
}
}
lbl_5:
{
uint8 x_69; 
lean::dec(x_4);
x_69 = l_Lean_IR_FnBody_isTerminal___main(x_0);
if (x_69 == 0)
{
obj* x_70; 
x_70 = l_Lean_IR_FnBody_body___main(x_0);
lean::dec(x_0);
x_0 = x_70;
goto _start;
}
else
{
obj* x_74; obj* x_76; obj* x_77; obj* x_78; 
lean::dec(x_0);
x_74 = lean::cnstr_get(x_3, 1);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 x_76 = x_3;
} else {
 lean::inc(x_74);
 lean::dec(x_3);
 x_76 = lean::box(0);
}
x_77 = lean::box(x_1);
if (lean::is_scalar(x_76)) {
 x_78 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_78 = x_76;
}
lean::cnstr_set(x_78, 0, x_77);
lean::cnstr_set(x_78, 1, x_74);
return x_78;
}
}
}
}
obj* l_Lean_IR_EmitCpp_declareVars___main___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = lean::unbox(x_1);
x_5 = l_Lean_IR_EmitCpp_declareVars___main(x_0, x_4, x_2, x_3);
lean::dec(x_2);
return x_5;
}
}
obj* l_Lean_IR_EmitCpp_declareVars(obj* x_0, uint8 x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_IR_EmitCpp_declareVars___main(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_Lean_IR_EmitCpp_declareVars___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = lean::unbox(x_1);
x_5 = l_Lean_IR_EmitCpp_declareVars(x_0, x_4, x_2, x_3);
lean::dec(x_2);
return x_5;
}
}
obj* _init_l_Lean_IR_EmitCpp_emitTag___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("lean::obj_tag(");
return x_0;
}
}
obj* l_Lean_IR_EmitCpp_emitTag(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; 
lean::inc(x_0);
x_4 = l_Lean_IR_EmitCpp_isObj(x_0, x_1, x_2);
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; uint8 x_7; 
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
x_7 = lean::unbox(x_5);
if (x_7 == 0)
{
obj* x_8; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_15; obj* x_17; obj* x_18; 
x_8 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 x_10 = x_4;
} else {
 lean::inc(x_8);
 lean::dec(x_4);
 x_10 = lean::box(0);
}
x_11 = l_Nat_repr(x_0);
x_12 = l_Lean_IR_VarId_HasToString___closed__1;
x_13 = lean::string_append(x_12, x_11);
lean::dec(x_11);
x_15 = lean::string_append(x_8, x_13);
lean::dec(x_13);
x_17 = lean::box(0);
if (lean::is_scalar(x_10)) {
 x_18 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_18 = x_10;
}
lean::cnstr_set(x_18, 0, x_17);
lean::cnstr_set(x_18, 1, x_15);
return x_18;
}
else
{
obj* x_19; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_28; obj* x_30; obj* x_31; obj* x_32; obj* x_33; 
x_19 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 x_21 = x_4;
} else {
 lean::inc(x_19);
 lean::dec(x_4);
 x_21 = lean::box(0);
}
x_22 = l_Lean_IR_EmitCpp_emitTag___closed__1;
x_23 = lean::string_append(x_19, x_22);
x_24 = l_Nat_repr(x_0);
x_25 = l_Lean_IR_VarId_HasToString___closed__1;
x_26 = lean::string_append(x_25, x_24);
lean::dec(x_24);
x_28 = lean::string_append(x_23, x_26);
lean::dec(x_26);
x_30 = l_Option_HasRepr___rarg___closed__3;
x_31 = lean::string_append(x_28, x_30);
x_32 = lean::box(0);
if (lean::is_scalar(x_21)) {
 x_33 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_33 = x_21;
}
lean::cnstr_set(x_33, 0, x_32);
lean::cnstr_set(x_33, 1, x_31);
return x_33;
}
}
else
{
obj* x_35; obj* x_37; obj* x_39; obj* x_40; 
lean::dec(x_0);
x_35 = lean::cnstr_get(x_4, 0);
x_37 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 x_39 = x_4;
} else {
 lean::inc(x_35);
 lean::inc(x_37);
 lean::dec(x_4);
 x_39 = lean::box(0);
}
if (lean::is_scalar(x_39)) {
 x_40 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_40 = x_39;
}
lean::cnstr_set(x_40, 0, x_35);
lean::cnstr_set(x_40, 1, x_37);
return x_40;
}
}
}
obj* l_Lean_IR_EmitCpp_emitTag___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_EmitCpp_emitTag(x_0, x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_IR_EmitCpp_isIf(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; uint8 x_3; 
x_1 = lean::array_get_size(x_0);
x_2 = lean::mk_nat_obj(2ul);
x_3 = lean::nat_dec_eq(x_1, x_2);
lean::dec(x_1);
if (x_3 == 0)
{
obj* x_5; 
x_5 = lean::box(0);
return x_5;
}
else
{
obj* x_6; obj* x_7; obj* x_8; 
x_6 = l_Lean_IR_altInh;
x_7 = lean::mk_nat_obj(0ul);
x_8 = lean::array_get(x_6, x_0, x_7);
if (lean::obj_tag(x_8) == 0)
{
obj* x_9; obj* x_11; obj* x_14; obj* x_17; obj* x_18; obj* x_19; obj* x_21; obj* x_22; obj* x_23; 
x_9 = lean::cnstr_get(x_8, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_8, 1);
lean::inc(x_11);
lean::dec(x_8);
x_14 = lean::cnstr_get(x_9, 1);
lean::inc(x_14);
lean::dec(x_9);
x_17 = lean::mk_nat_obj(1ul);
x_18 = lean::array_get(x_6, x_0, x_17);
x_19 = l_Lean_IR_AltCore_body___main(x_18);
lean::dec(x_18);
x_21 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_21, 0, x_11);
lean::cnstr_set(x_21, 1, x_19);
x_22 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_22, 0, x_14);
lean::cnstr_set(x_22, 1, x_21);
x_23 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_23, 0, x_22);
return x_23;
}
else
{
obj* x_25; 
lean::dec(x_8);
x_25 = lean::box(0);
return x_25;
}
}
}
}
obj* l_Lean_IR_EmitCpp_isIf___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_IR_EmitCpp_isIf(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* _init_l_Lean_IR_EmitCpp_emitIf___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("if (");
return x_0;
}
}
obj* _init_l_Lean_IR_EmitCpp_emitIf___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string(" == ");
return x_0;
}
}
obj* _init_l_Lean_IR_EmitCpp_emitIf___closed__3() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("else");
return x_0;
}
}
obj* l_Lean_IR_EmitCpp_emitIf(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_7 = lean::cnstr_get(x_6, 1);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 x_9 = x_6;
} else {
 lean::inc(x_7);
 lean::dec(x_6);
 x_9 = lean::box(0);
}
x_10 = l_Lean_IR_EmitCpp_emitIf___closed__1;
x_11 = lean::string_append(x_7, x_10);
x_12 = lean::box(0);
if (lean::is_scalar(x_9)) {
 x_13 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_13 = x_9;
}
lean::cnstr_set(x_13, 0, x_12);
lean::cnstr_set(x_13, 1, x_11);
x_14 = l_Lean_IR_EmitCpp_emitTag(x_1, x_5, x_13);
if (lean::obj_tag(x_14) == 0)
{
obj* x_15; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_30; 
x_15 = lean::cnstr_get(x_14, 1);
if (lean::is_exclusive(x_14)) {
 lean::cnstr_release(x_14, 0);
 x_17 = x_14;
} else {
 lean::inc(x_15);
 lean::dec(x_14);
 x_17 = lean::box(0);
}
x_18 = l_Lean_IR_EmitCpp_emitIf___closed__2;
x_19 = lean::string_append(x_15, x_18);
x_20 = l_Nat_repr(x_2);
x_21 = lean::string_append(x_19, x_20);
lean::dec(x_20);
x_23 = l_Option_HasRepr___rarg___closed__3;
x_24 = lean::string_append(x_21, x_23);
x_25 = l_IO_println___rarg___closed__1;
x_26 = lean::string_append(x_24, x_25);
if (lean::is_scalar(x_17)) {
 x_27 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_27 = x_17;
}
lean::cnstr_set(x_27, 0, x_12);
lean::cnstr_set(x_27, 1, x_26);
lean::inc(x_5);
lean::inc(x_0);
x_30 = lean::apply_3(x_0, x_3, x_5, x_27);
if (lean::obj_tag(x_30) == 0)
{
obj* x_31; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; 
x_31 = lean::cnstr_get(x_30, 1);
if (lean::is_exclusive(x_30)) {
 lean::cnstr_release(x_30, 0);
 x_33 = x_30;
} else {
 lean::inc(x_31);
 lean::dec(x_30);
 x_33 = lean::box(0);
}
x_34 = l_Lean_IR_EmitCpp_emitIf___closed__3;
x_35 = lean::string_append(x_31, x_34);
x_36 = lean::string_append(x_35, x_25);
if (lean::is_scalar(x_33)) {
 x_37 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_37 = x_33;
}
lean::cnstr_set(x_37, 0, x_12);
lean::cnstr_set(x_37, 1, x_36);
x_38 = lean::apply_3(x_0, x_4, x_5, x_37);
return x_38;
}
else
{
obj* x_42; obj* x_44; obj* x_46; obj* x_47; 
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_0);
x_42 = lean::cnstr_get(x_30, 0);
x_44 = lean::cnstr_get(x_30, 1);
if (lean::is_exclusive(x_30)) {
 x_46 = x_30;
} else {
 lean::inc(x_42);
 lean::inc(x_44);
 lean::dec(x_30);
 x_46 = lean::box(0);
}
if (lean::is_scalar(x_46)) {
 x_47 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_47 = x_46;
}
lean::cnstr_set(x_47, 0, x_42);
lean::cnstr_set(x_47, 1, x_44);
return x_47;
}
}
else
{
obj* x_53; obj* x_55; obj* x_57; obj* x_58; 
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_2);
x_53 = lean::cnstr_get(x_14, 0);
x_55 = lean::cnstr_get(x_14, 1);
if (lean::is_exclusive(x_14)) {
 x_57 = x_14;
} else {
 lean::inc(x_53);
 lean::inc(x_55);
 lean::dec(x_14);
 x_57 = lean::box(0);
}
if (lean::is_scalar(x_57)) {
 x_58 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_58 = x_57;
}
lean::cnstr_set(x_58, 0, x_53);
lean::cnstr_set(x_58, 1, x_55);
return x_58;
}
}
}
obj* _init_l_Array_mforAux___main___at_Lean_IR_EmitCpp_emitCase___spec__1___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("case ");
return x_0;
}
}
obj* _init_l_Array_mforAux___main___at_Lean_IR_EmitCpp_emitCase___spec__1___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string(":");
return x_0;
}
}
obj* _init_l_Array_mforAux___main___at_Lean_IR_EmitCpp_emitCase___spec__1___closed__3() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("default: ");
return x_0;
}
}
obj* l_Array_mforAux___main___at_Lean_IR_EmitCpp_emitCase___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean::array_get_size(x_1);
x_6 = lean::nat_dec_lt(x_2, x_5);
lean::dec(x_5);
if (x_6 == 0)
{
obj* x_11; obj* x_13; obj* x_14; obj* x_15; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_2);
x_11 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 x_13 = x_4;
} else {
 lean::inc(x_11);
 lean::dec(x_4);
 x_13 = lean::box(0);
}
x_14 = lean::box(0);
if (lean::is_scalar(x_13)) {
 x_15 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_15 = x_13;
}
lean::cnstr_set(x_15, 0, x_14);
lean::cnstr_set(x_15, 1, x_11);
return x_15;
}
else
{
obj* x_16; obj* x_17; obj* x_18; 
x_16 = lean::array_fget(x_1, x_2);
x_17 = lean::mk_nat_obj(1ul);
x_18 = lean::nat_add(x_2, x_17);
lean::dec(x_2);
if (lean::obj_tag(x_16) == 0)
{
obj* x_20; obj* x_22; obj* x_25; obj* x_27; obj* x_28; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_44; 
x_20 = lean::cnstr_get(x_16, 0);
lean::inc(x_20);
x_22 = lean::cnstr_get(x_16, 1);
lean::inc(x_22);
lean::dec(x_16);
x_25 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 x_27 = x_4;
} else {
 lean::inc(x_25);
 lean::dec(x_4);
 x_27 = lean::box(0);
}
x_28 = lean::cnstr_get(x_20, 1);
lean::inc(x_28);
lean::dec(x_20);
x_31 = l_Array_mforAux___main___at_Lean_IR_EmitCpp_emitCase___spec__1___closed__1;
x_32 = lean::string_append(x_25, x_31);
x_33 = l_Nat_repr(x_28);
x_34 = lean::string_append(x_32, x_33);
lean::dec(x_33);
x_36 = l_Array_mforAux___main___at_Lean_IR_EmitCpp_emitCase___spec__1___closed__2;
x_37 = lean::string_append(x_34, x_36);
x_38 = l_IO_println___rarg___closed__1;
x_39 = lean::string_append(x_37, x_38);
x_40 = lean::box(0);
if (lean::is_scalar(x_27)) {
 x_41 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_41 = x_27;
}
lean::cnstr_set(x_41, 0, x_40);
lean::cnstr_set(x_41, 1, x_39);
lean::inc(x_3);
lean::inc(x_0);
x_44 = lean::apply_3(x_0, x_22, x_3, x_41);
if (lean::obj_tag(x_44) == 0)
{
obj* x_45; obj* x_47; obj* x_48; 
x_45 = lean::cnstr_get(x_44, 1);
if (lean::is_exclusive(x_44)) {
 lean::cnstr_release(x_44, 0);
 x_47 = x_44;
} else {
 lean::inc(x_45);
 lean::dec(x_44);
 x_47 = lean::box(0);
}
if (lean::is_scalar(x_47)) {
 x_48 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_48 = x_47;
}
lean::cnstr_set(x_48, 0, x_40);
lean::cnstr_set(x_48, 1, x_45);
x_2 = x_18;
x_4 = x_48;
goto _start;
}
else
{
obj* x_53; obj* x_55; obj* x_57; obj* x_58; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_18);
x_53 = lean::cnstr_get(x_44, 0);
x_55 = lean::cnstr_get(x_44, 1);
if (lean::is_exclusive(x_44)) {
 x_57 = x_44;
} else {
 lean::inc(x_53);
 lean::inc(x_55);
 lean::dec(x_44);
 x_57 = lean::box(0);
}
if (lean::is_scalar(x_57)) {
 x_58 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_58 = x_57;
}
lean::cnstr_set(x_58, 0, x_53);
lean::cnstr_set(x_58, 1, x_55);
return x_58;
}
}
else
{
obj* x_59; obj* x_62; obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_73; 
x_59 = lean::cnstr_get(x_16, 0);
lean::inc(x_59);
lean::dec(x_16);
x_62 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 x_64 = x_4;
} else {
 lean::inc(x_62);
 lean::dec(x_4);
 x_64 = lean::box(0);
}
x_65 = l_Array_mforAux___main___at_Lean_IR_EmitCpp_emitCase___spec__1___closed__3;
x_66 = lean::string_append(x_62, x_65);
x_67 = l_IO_println___rarg___closed__1;
x_68 = lean::string_append(x_66, x_67);
x_69 = lean::box(0);
if (lean::is_scalar(x_64)) {
 x_70 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_70 = x_64;
}
lean::cnstr_set(x_70, 0, x_69);
lean::cnstr_set(x_70, 1, x_68);
lean::inc(x_3);
lean::inc(x_0);
x_73 = lean::apply_3(x_0, x_59, x_3, x_70);
if (lean::obj_tag(x_73) == 0)
{
obj* x_74; obj* x_76; obj* x_77; 
x_74 = lean::cnstr_get(x_73, 1);
if (lean::is_exclusive(x_73)) {
 lean::cnstr_release(x_73, 0);
 x_76 = x_73;
} else {
 lean::inc(x_74);
 lean::dec(x_73);
 x_76 = lean::box(0);
}
if (lean::is_scalar(x_76)) {
 x_77 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_77 = x_76;
}
lean::cnstr_set(x_77, 0, x_69);
lean::cnstr_set(x_77, 1, x_74);
x_2 = x_18;
x_4 = x_77;
goto _start;
}
else
{
obj* x_82; obj* x_84; obj* x_86; obj* x_87; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_18);
x_82 = lean::cnstr_get(x_73, 0);
x_84 = lean::cnstr_get(x_73, 1);
if (lean::is_exclusive(x_73)) {
 x_86 = x_73;
} else {
 lean::inc(x_82);
 lean::inc(x_84);
 lean::dec(x_73);
 x_86 = lean::box(0);
}
if (lean::is_scalar(x_86)) {
 x_87 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_87 = x_86;
}
lean::cnstr_set(x_87, 0, x_82);
lean::cnstr_set(x_87, 1, x_84);
return x_87;
}
}
}
}
}
obj* _init_l_Lean_IR_EmitCpp_emitCase___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("switch (");
return x_0;
}
}
obj* _init_l_Lean_IR_EmitCpp_emitCase___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string(") {");
return x_0;
}
}
obj* l_Lean_IR_EmitCpp_emitCase(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_IR_EmitCpp_isIf(x_2);
if (lean::obj_tag(x_5) == 0)
{
obj* x_6; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_6 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 x_8 = x_4;
} else {
 lean::inc(x_6);
 lean::dec(x_4);
 x_8 = lean::box(0);
}
x_9 = l_Lean_IR_EmitCpp_emitCase___closed__1;
x_10 = lean::string_append(x_6, x_9);
x_11 = lean::box(0);
if (lean::is_scalar(x_8)) {
 x_12 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_12 = x_8;
}
lean::cnstr_set(x_12, 0, x_11);
lean::cnstr_set(x_12, 1, x_10);
x_13 = l_Lean_IR_EmitCpp_emitTag(x_1, x_3, x_12);
if (lean::obj_tag(x_13) == 0)
{
obj* x_14; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; 
x_14 = lean::cnstr_get(x_13, 1);
if (lean::is_exclusive(x_13)) {
 lean::cnstr_release(x_13, 0);
 x_16 = x_13;
} else {
 lean::inc(x_14);
 lean::dec(x_13);
 x_16 = lean::box(0);
}
x_17 = l_Lean_IR_EmitCpp_emitCase___closed__2;
x_18 = lean::string_append(x_14, x_17);
x_19 = l_IO_println___rarg___closed__1;
x_20 = lean::string_append(x_18, x_19);
if (lean::is_scalar(x_16)) {
 x_21 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_21 = x_16;
}
lean::cnstr_set(x_21, 0, x_11);
lean::cnstr_set(x_21, 1, x_20);
x_22 = lean::mk_nat_obj(0ul);
x_23 = l_Array_mforAux___main___at_Lean_IR_EmitCpp_emitCase___spec__1(x_0, x_2, x_22, x_3, x_21);
if (lean::obj_tag(x_23) == 0)
{
obj* x_24; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
x_24 = lean::cnstr_get(x_23, 1);
if (lean::is_exclusive(x_23)) {
 lean::cnstr_release(x_23, 0);
 x_26 = x_23;
} else {
 lean::inc(x_24);
 lean::dec(x_23);
 x_26 = lean::box(0);
}
x_27 = l_Lean_IR_EmitCpp_closeNamespacesAux___main___closed__1;
x_28 = lean::string_append(x_24, x_27);
x_29 = lean::string_append(x_28, x_19);
if (lean::is_scalar(x_26)) {
 x_30 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_30 = x_26;
}
lean::cnstr_set(x_30, 0, x_11);
lean::cnstr_set(x_30, 1, x_29);
return x_30;
}
else
{
obj* x_31; obj* x_33; obj* x_35; obj* x_36; 
x_31 = lean::cnstr_get(x_23, 0);
x_33 = lean::cnstr_get(x_23, 1);
if (lean::is_exclusive(x_23)) {
 x_35 = x_23;
} else {
 lean::inc(x_31);
 lean::inc(x_33);
 lean::dec(x_23);
 x_35 = lean::box(0);
}
if (lean::is_scalar(x_35)) {
 x_36 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_36 = x_35;
}
lean::cnstr_set(x_36, 0, x_31);
lean::cnstr_set(x_36, 1, x_33);
return x_36;
}
}
else
{
obj* x_39; obj* x_41; obj* x_43; obj* x_44; 
lean::dec(x_3);
lean::dec(x_0);
x_39 = lean::cnstr_get(x_13, 0);
x_41 = lean::cnstr_get(x_13, 1);
if (lean::is_exclusive(x_13)) {
 x_43 = x_13;
} else {
 lean::inc(x_39);
 lean::inc(x_41);
 lean::dec(x_13);
 x_43 = lean::box(0);
}
if (lean::is_scalar(x_43)) {
 x_44 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_44 = x_43;
}
lean::cnstr_set(x_44, 0, x_39);
lean::cnstr_set(x_44, 1, x_41);
return x_44;
}
}
else
{
obj* x_45; obj* x_48; obj* x_50; obj* x_53; obj* x_55; obj* x_58; 
x_45 = lean::cnstr_get(x_5, 0);
lean::inc(x_45);
lean::dec(x_5);
x_48 = lean::cnstr_get(x_45, 1);
lean::inc(x_48);
x_50 = lean::cnstr_get(x_45, 0);
lean::inc(x_50);
lean::dec(x_45);
x_53 = lean::cnstr_get(x_48, 0);
lean::inc(x_53);
x_55 = lean::cnstr_get(x_48, 1);
lean::inc(x_55);
lean::dec(x_48);
x_58 = l_Lean_IR_EmitCpp_emitIf(x_0, x_1, x_50, x_53, x_55, x_3, x_4);
return x_58;
}
}
}
obj* l_Array_mforAux___main___at_Lean_IR_EmitCpp_emitCase___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Array_mforAux___main___at_Lean_IR_EmitCpp_emitCase___spec__1(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_1);
return x_5;
}
}
obj* l_Lean_IR_EmitCpp_emitCase___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_IR_EmitCpp_emitCase(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_2);
return x_5;
}
}
obj* _init_l_Lean_IR_EmitCpp_emitInc___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("lean::inc_ref");
return x_0;
}
}
obj* _init_l_Lean_IR_EmitCpp_emitInc___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string(");");
return x_0;
}
}
obj* _init_l_Lean_IR_EmitCpp_emitInc___closed__3() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("lean::inc");
return x_0;
}
}
obj* l_Lean_IR_EmitCpp_emitInc(obj* x_0, obj* x_1, uint8 x_2, obj* x_3, obj* x_4) {
_start:
{
if (x_2 == 0)
{
obj* x_5; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_16; obj* x_18; uint8 x_19; 
x_5 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 lean::cnstr_set(x_4, 1, lean::box(0));
 x_7 = x_4;
} else {
 lean::inc(x_5);
 lean::dec(x_4);
 x_7 = lean::box(0);
}
x_8 = l_Lean_IR_EmitCpp_emitInc___closed__1;
x_9 = lean::string_append(x_5, x_8);
x_10 = l_Prod_HasRepr___rarg___closed__1;
x_11 = lean::string_append(x_9, x_10);
x_12 = l_Nat_repr(x_0);
x_13 = l_Lean_IR_VarId_HasToString___closed__1;
x_14 = lean::string_append(x_13, x_12);
lean::dec(x_12);
x_16 = lean::string_append(x_11, x_14);
lean::dec(x_14);
x_18 = lean::mk_nat_obj(1ul);
x_19 = lean::nat_dec_eq(x_1, x_18);
if (x_19 == 0)
{
obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
x_20 = l_List_reprAux___main___rarg___closed__1;
x_21 = lean::string_append(x_16, x_20);
x_22 = l_Nat_repr(x_1);
x_23 = lean::string_append(x_21, x_22);
lean::dec(x_22);
x_25 = l_Lean_IR_EmitCpp_emitInc___closed__2;
x_26 = lean::string_append(x_23, x_25);
x_27 = l_IO_println___rarg___closed__1;
x_28 = lean::string_append(x_26, x_27);
x_29 = lean::box(0);
if (lean::is_scalar(x_7)) {
 x_30 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_30 = x_7;
}
lean::cnstr_set(x_30, 0, x_29);
lean::cnstr_set(x_30, 1, x_28);
return x_30;
}
else
{
obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; 
lean::dec(x_1);
x_32 = l_Lean_IR_EmitCpp_emitInc___closed__2;
x_33 = lean::string_append(x_16, x_32);
x_34 = l_IO_println___rarg___closed__1;
x_35 = lean::string_append(x_33, x_34);
x_36 = lean::box(0);
if (lean::is_scalar(x_7)) {
 x_37 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_37 = x_7;
}
lean::cnstr_set(x_37, 0, x_36);
lean::cnstr_set(x_37, 1, x_35);
return x_37;
}
}
else
{
obj* x_38; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_49; obj* x_51; uint8 x_52; 
x_38 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 lean::cnstr_set(x_4, 1, lean::box(0));
 x_40 = x_4;
} else {
 lean::inc(x_38);
 lean::dec(x_4);
 x_40 = lean::box(0);
}
x_41 = l_Lean_IR_EmitCpp_emitInc___closed__3;
x_42 = lean::string_append(x_38, x_41);
x_43 = l_Prod_HasRepr___rarg___closed__1;
x_44 = lean::string_append(x_42, x_43);
x_45 = l_Nat_repr(x_0);
x_46 = l_Lean_IR_VarId_HasToString___closed__1;
x_47 = lean::string_append(x_46, x_45);
lean::dec(x_45);
x_49 = lean::string_append(x_44, x_47);
lean::dec(x_47);
x_51 = lean::mk_nat_obj(1ul);
x_52 = lean::nat_dec_eq(x_1, x_51);
if (x_52 == 0)
{
obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; 
x_53 = l_List_reprAux___main___rarg___closed__1;
x_54 = lean::string_append(x_49, x_53);
x_55 = l_Nat_repr(x_1);
x_56 = lean::string_append(x_54, x_55);
lean::dec(x_55);
x_58 = l_Lean_IR_EmitCpp_emitInc___closed__2;
x_59 = lean::string_append(x_56, x_58);
x_60 = l_IO_println___rarg___closed__1;
x_61 = lean::string_append(x_59, x_60);
x_62 = lean::box(0);
if (lean::is_scalar(x_40)) {
 x_63 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_63 = x_40;
}
lean::cnstr_set(x_63, 0, x_62);
lean::cnstr_set(x_63, 1, x_61);
return x_63;
}
else
{
obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; 
lean::dec(x_1);
x_65 = l_Lean_IR_EmitCpp_emitInc___closed__2;
x_66 = lean::string_append(x_49, x_65);
x_67 = l_IO_println___rarg___closed__1;
x_68 = lean::string_append(x_66, x_67);
x_69 = lean::box(0);
if (lean::is_scalar(x_40)) {
 x_70 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_70 = x_40;
}
lean::cnstr_set(x_70, 0, x_69);
lean::cnstr_set(x_70, 1, x_68);
return x_70;
}
}
}
}
obj* l_Lean_IR_EmitCpp_emitInc___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; obj* x_6; 
x_5 = lean::unbox(x_2);
x_6 = l_Lean_IR_EmitCpp_emitInc(x_0, x_1, x_5, x_3, x_4);
lean::dec(x_3);
return x_6;
}
}
obj* _init_l_Lean_IR_EmitCpp_emitDec___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("lean::dec_ref");
return x_0;
}
}
obj* _init_l_Lean_IR_EmitCpp_emitDec___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("lean::dec");
return x_0;
}
}
obj* l_Lean_IR_EmitCpp_emitDec(obj* x_0, obj* x_1, uint8 x_2, obj* x_3, obj* x_4) {
_start:
{
if (x_2 == 0)
{
obj* x_5; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_16; obj* x_18; uint8 x_19; 
x_5 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 lean::cnstr_set(x_4, 1, lean::box(0));
 x_7 = x_4;
} else {
 lean::inc(x_5);
 lean::dec(x_4);
 x_7 = lean::box(0);
}
x_8 = l_Lean_IR_EmitCpp_emitDec___closed__1;
x_9 = lean::string_append(x_5, x_8);
x_10 = l_Prod_HasRepr___rarg___closed__1;
x_11 = lean::string_append(x_9, x_10);
x_12 = l_Nat_repr(x_0);
x_13 = l_Lean_IR_VarId_HasToString___closed__1;
x_14 = lean::string_append(x_13, x_12);
lean::dec(x_12);
x_16 = lean::string_append(x_11, x_14);
lean::dec(x_14);
x_18 = lean::mk_nat_obj(1ul);
x_19 = lean::nat_dec_eq(x_1, x_18);
if (x_19 == 0)
{
obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
x_20 = l_List_reprAux___main___rarg___closed__1;
x_21 = lean::string_append(x_16, x_20);
x_22 = l_Nat_repr(x_1);
x_23 = lean::string_append(x_21, x_22);
lean::dec(x_22);
x_25 = l_Lean_IR_EmitCpp_emitInc___closed__2;
x_26 = lean::string_append(x_23, x_25);
x_27 = l_IO_println___rarg___closed__1;
x_28 = lean::string_append(x_26, x_27);
x_29 = lean::box(0);
if (lean::is_scalar(x_7)) {
 x_30 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_30 = x_7;
}
lean::cnstr_set(x_30, 0, x_29);
lean::cnstr_set(x_30, 1, x_28);
return x_30;
}
else
{
obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; 
lean::dec(x_1);
x_32 = l_Lean_IR_EmitCpp_emitInc___closed__2;
x_33 = lean::string_append(x_16, x_32);
x_34 = l_IO_println___rarg___closed__1;
x_35 = lean::string_append(x_33, x_34);
x_36 = lean::box(0);
if (lean::is_scalar(x_7)) {
 x_37 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_37 = x_7;
}
lean::cnstr_set(x_37, 0, x_36);
lean::cnstr_set(x_37, 1, x_35);
return x_37;
}
}
else
{
obj* x_38; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_49; obj* x_51; uint8 x_52; 
x_38 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 lean::cnstr_set(x_4, 1, lean::box(0));
 x_40 = x_4;
} else {
 lean::inc(x_38);
 lean::dec(x_4);
 x_40 = lean::box(0);
}
x_41 = l_Lean_IR_EmitCpp_emitDec___closed__2;
x_42 = lean::string_append(x_38, x_41);
x_43 = l_Prod_HasRepr___rarg___closed__1;
x_44 = lean::string_append(x_42, x_43);
x_45 = l_Nat_repr(x_0);
x_46 = l_Lean_IR_VarId_HasToString___closed__1;
x_47 = lean::string_append(x_46, x_45);
lean::dec(x_45);
x_49 = lean::string_append(x_44, x_47);
lean::dec(x_47);
x_51 = lean::mk_nat_obj(1ul);
x_52 = lean::nat_dec_eq(x_1, x_51);
if (x_52 == 0)
{
obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; 
x_53 = l_List_reprAux___main___rarg___closed__1;
x_54 = lean::string_append(x_49, x_53);
x_55 = l_Nat_repr(x_1);
x_56 = lean::string_append(x_54, x_55);
lean::dec(x_55);
x_58 = l_Lean_IR_EmitCpp_emitInc___closed__2;
x_59 = lean::string_append(x_56, x_58);
x_60 = l_IO_println___rarg___closed__1;
x_61 = lean::string_append(x_59, x_60);
x_62 = lean::box(0);
if (lean::is_scalar(x_40)) {
 x_63 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_63 = x_40;
}
lean::cnstr_set(x_63, 0, x_62);
lean::cnstr_set(x_63, 1, x_61);
return x_63;
}
else
{
obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; 
lean::dec(x_1);
x_65 = l_Lean_IR_EmitCpp_emitInc___closed__2;
x_66 = lean::string_append(x_49, x_65);
x_67 = l_IO_println___rarg___closed__1;
x_68 = lean::string_append(x_66, x_67);
x_69 = lean::box(0);
if (lean::is_scalar(x_40)) {
 x_70 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_70 = x_40;
}
lean::cnstr_set(x_70, 0, x_69);
lean::cnstr_set(x_70, 1, x_68);
return x_70;
}
}
}
}
obj* l_Lean_IR_EmitCpp_emitDec___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; obj* x_6; 
x_5 = lean::unbox(x_2);
x_6 = l_Lean_IR_EmitCpp_emitDec(x_0, x_1, x_5, x_3, x_4);
lean::dec(x_3);
return x_6;
}
}
obj* _init_l_Lean_IR_EmitCpp_emitRelease___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("lean::cnstr_release(");
return x_0;
}
}
obj* l_Lean_IR_EmitCpp_emitRelease(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_13; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; 
x_4 = lean::cnstr_get(x_3, 1);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 x_6 = x_3;
} else {
 lean::inc(x_4);
 lean::dec(x_3);
 x_6 = lean::box(0);
}
x_7 = l_Lean_IR_EmitCpp_emitRelease___closed__1;
x_8 = lean::string_append(x_4, x_7);
x_9 = l_Nat_repr(x_0);
x_10 = l_Lean_IR_VarId_HasToString___closed__1;
x_11 = lean::string_append(x_10, x_9);
lean::dec(x_9);
x_13 = lean::string_append(x_8, x_11);
lean::dec(x_11);
x_15 = l_List_reprAux___main___rarg___closed__1;
x_16 = lean::string_append(x_13, x_15);
x_17 = l_Nat_repr(x_1);
x_18 = lean::string_append(x_16, x_17);
lean::dec(x_17);
x_20 = l_Lean_IR_EmitCpp_emitInc___closed__2;
x_21 = lean::string_append(x_18, x_20);
x_22 = l_IO_println___rarg___closed__1;
x_23 = lean::string_append(x_21, x_22);
x_24 = lean::box(0);
if (lean::is_scalar(x_6)) {
 x_25 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_25 = x_6;
}
lean::cnstr_set(x_25, 0, x_24);
lean::cnstr_set(x_25, 1, x_23);
return x_25;
}
}
obj* l_Lean_IR_EmitCpp_emitRelease___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_IR_EmitCpp_emitRelease(x_0, x_1, x_2, x_3);
lean::dec(x_2);
return x_4;
}
}
obj* _init_l_Lean_IR_EmitCpp_emitSet___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("lean::cnstr_set(");
return x_0;
}
}
obj* l_Lean_IR_EmitCpp_emitSet(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_14; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_21; obj* x_22; obj* x_23; obj* x_25; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; 
x_5 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 x_7 = x_4;
} else {
 lean::inc(x_5);
 lean::dec(x_4);
 x_7 = lean::box(0);
}
x_8 = l_Lean_IR_EmitCpp_emitSet___closed__1;
x_9 = lean::string_append(x_5, x_8);
x_10 = l_Nat_repr(x_0);
x_11 = l_Lean_IR_VarId_HasToString___closed__1;
x_12 = lean::string_append(x_11, x_10);
lean::dec(x_10);
x_14 = lean::string_append(x_9, x_12);
lean::dec(x_12);
x_16 = l_List_reprAux___main___rarg___closed__1;
x_17 = lean::string_append(x_14, x_16);
x_18 = l_Nat_repr(x_1);
x_19 = lean::string_append(x_17, x_18);
lean::dec(x_18);
x_21 = lean::string_append(x_19, x_16);
x_22 = l_Nat_repr(x_2);
x_23 = lean::string_append(x_11, x_22);
lean::dec(x_22);
x_25 = lean::string_append(x_21, x_23);
lean::dec(x_23);
x_27 = l_Lean_IR_EmitCpp_emitInc___closed__2;
x_28 = lean::string_append(x_25, x_27);
x_29 = l_IO_println___rarg___closed__1;
x_30 = lean::string_append(x_28, x_29);
x_31 = lean::box(0);
if (lean::is_scalar(x_7)) {
 x_32 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_32 = x_7;
}
lean::cnstr_set(x_32, 0, x_31);
lean::cnstr_set(x_32, 1, x_30);
return x_32;
}
}
obj* l_Lean_IR_EmitCpp_emitSet___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_IR_EmitCpp_emitSet(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_3);
return x_5;
}
}
obj* _init_l_Lean_IR_EmitCpp_emitOffset___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("sizeof(void*)*");
return x_0;
}
}
obj* _init_l_Lean_IR_EmitCpp_emitOffset___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string(" + ");
return x_0;
}
}
obj* l_Lean_IR_EmitCpp_emitOffset(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::mk_nat_obj(0ul);
x_5 = lean::nat_dec_lt(x_4, x_0);
if (x_5 == 0)
{
obj* x_7; obj* x_9; obj* x_10; obj* x_11; obj* x_13; obj* x_14; 
lean::dec(x_0);
x_7 = lean::cnstr_get(x_3, 1);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 x_9 = x_3;
} else {
 lean::inc(x_7);
 lean::dec(x_3);
 x_9 = lean::box(0);
}
x_10 = l_Nat_repr(x_1);
x_11 = lean::string_append(x_7, x_10);
lean::dec(x_10);
x_13 = lean::box(0);
if (lean::is_scalar(x_9)) {
 x_14 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_14 = x_9;
}
lean::cnstr_set(x_14, 0, x_13);
lean::cnstr_set(x_14, 1, x_11);
return x_14;
}
else
{
obj* x_15; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; uint8 x_23; 
x_15 = lean::cnstr_get(x_3, 1);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 lean::cnstr_set(x_3, 1, lean::box(0));
 x_17 = x_3;
} else {
 lean::inc(x_15);
 lean::dec(x_3);
 x_17 = lean::box(0);
}
x_18 = l_Lean_IR_EmitCpp_emitOffset___closed__1;
x_19 = lean::string_append(x_15, x_18);
x_20 = l_Nat_repr(x_0);
x_21 = lean::string_append(x_19, x_20);
lean::dec(x_20);
x_23 = lean::nat_dec_lt(x_4, x_1);
if (x_23 == 0)
{
obj* x_25; obj* x_26; 
lean::dec(x_1);
x_25 = lean::box(0);
if (lean::is_scalar(x_17)) {
 x_26 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_26 = x_17;
}
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_21);
return x_26;
}
else
{
obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_32; obj* x_33; 
x_27 = l_Lean_IR_EmitCpp_emitOffset___closed__2;
x_28 = lean::string_append(x_21, x_27);
x_29 = l_Nat_repr(x_1);
x_30 = lean::string_append(x_28, x_29);
lean::dec(x_29);
x_32 = lean::box(0);
if (lean::is_scalar(x_17)) {
 x_33 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_33 = x_17;
}
lean::cnstr_set(x_33, 0, x_32);
lean::cnstr_set(x_33, 1, x_30);
return x_33;
}
}
}
}
obj* l_Lean_IR_EmitCpp_emitOffset___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_IR_EmitCpp_emitOffset(x_0, x_1, x_2, x_3);
lean::dec(x_2);
return x_4;
}
}
obj* _init_l_Lean_IR_EmitCpp_emitUSet___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("lean::cnstr_set_scalar(");
return x_0;
}
}
obj* l_Lean_IR_EmitCpp_emitUSet(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_14; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; 
x_5 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 x_7 = x_4;
} else {
 lean::inc(x_5);
 lean::dec(x_4);
 x_7 = lean::box(0);
}
x_8 = l_Lean_IR_EmitCpp_emitUSet___closed__1;
x_9 = lean::string_append(x_5, x_8);
x_10 = l_Nat_repr(x_0);
x_11 = l_Lean_IR_VarId_HasToString___closed__1;
x_12 = lean::string_append(x_11, x_10);
lean::dec(x_10);
x_14 = lean::string_append(x_9, x_12);
lean::dec(x_12);
x_16 = l_List_reprAux___main___rarg___closed__1;
x_17 = lean::string_append(x_14, x_16);
x_18 = lean::box(0);
if (lean::is_scalar(x_7)) {
 x_19 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_19 = x_7;
}
lean::cnstr_set(x_19, 0, x_18);
lean::cnstr_set(x_19, 1, x_17);
x_20 = lean::mk_nat_obj(0ul);
x_21 = l_Lean_IR_EmitCpp_emitOffset(x_1, x_20, x_3, x_19);
if (lean::obj_tag(x_21) == 0)
{
obj* x_22; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_29; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; 
x_22 = lean::cnstr_get(x_21, 1);
if (lean::is_exclusive(x_21)) {
 lean::cnstr_release(x_21, 0);
 x_24 = x_21;
} else {
 lean::inc(x_22);
 lean::dec(x_21);
 x_24 = lean::box(0);
}
x_25 = lean::string_append(x_22, x_16);
x_26 = l_Nat_repr(x_2);
x_27 = lean::string_append(x_11, x_26);
lean::dec(x_26);
x_29 = lean::string_append(x_25, x_27);
lean::dec(x_27);
x_31 = l_Lean_IR_EmitCpp_emitInc___closed__2;
x_32 = lean::string_append(x_29, x_31);
x_33 = l_IO_println___rarg___closed__1;
x_34 = lean::string_append(x_32, x_33);
if (lean::is_scalar(x_24)) {
 x_35 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_35 = x_24;
}
lean::cnstr_set(x_35, 0, x_18);
lean::cnstr_set(x_35, 1, x_34);
return x_35;
}
else
{
obj* x_37; obj* x_39; obj* x_41; obj* x_42; 
lean::dec(x_2);
x_37 = lean::cnstr_get(x_21, 0);
x_39 = lean::cnstr_get(x_21, 1);
if (lean::is_exclusive(x_21)) {
 x_41 = x_21;
} else {
 lean::inc(x_37);
 lean::inc(x_39);
 lean::dec(x_21);
 x_41 = lean::box(0);
}
if (lean::is_scalar(x_41)) {
 x_42 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_42 = x_41;
}
lean::cnstr_set(x_42, 0, x_37);
lean::cnstr_set(x_42, 1, x_39);
return x_42;
}
}
}
obj* l_Lean_IR_EmitCpp_emitUSet___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_IR_EmitCpp_emitUSet(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_3);
return x_5;
}
}
obj* l_Lean_IR_EmitCpp_emitSSet(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_15; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; 
x_6 = lean::cnstr_get(x_5, 1);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_release(x_5, 0);
 x_8 = x_5;
} else {
 lean::inc(x_6);
 lean::dec(x_5);
 x_8 = lean::box(0);
}
x_9 = l_Lean_IR_EmitCpp_emitUSet___closed__1;
x_10 = lean::string_append(x_6, x_9);
x_11 = l_Nat_repr(x_0);
x_12 = l_Lean_IR_VarId_HasToString___closed__1;
x_13 = lean::string_append(x_12, x_11);
lean::dec(x_11);
x_15 = lean::string_append(x_10, x_13);
lean::dec(x_13);
x_17 = l_List_reprAux___main___rarg___closed__1;
x_18 = lean::string_append(x_15, x_17);
x_19 = lean::box(0);
if (lean::is_scalar(x_8)) {
 x_20 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_20 = x_8;
}
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_18);
x_21 = l_Lean_IR_EmitCpp_emitOffset(x_1, x_2, x_4, x_20);
if (lean::obj_tag(x_21) == 0)
{
obj* x_22; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_29; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; 
x_22 = lean::cnstr_get(x_21, 1);
if (lean::is_exclusive(x_21)) {
 lean::cnstr_release(x_21, 0);
 x_24 = x_21;
} else {
 lean::inc(x_22);
 lean::dec(x_21);
 x_24 = lean::box(0);
}
x_25 = lean::string_append(x_22, x_17);
x_26 = l_Nat_repr(x_3);
x_27 = lean::string_append(x_12, x_26);
lean::dec(x_26);
x_29 = lean::string_append(x_25, x_27);
lean::dec(x_27);
x_31 = l_Lean_IR_EmitCpp_emitInc___closed__2;
x_32 = lean::string_append(x_29, x_31);
x_33 = l_IO_println___rarg___closed__1;
x_34 = lean::string_append(x_32, x_33);
if (lean::is_scalar(x_24)) {
 x_35 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_35 = x_24;
}
lean::cnstr_set(x_35, 0, x_19);
lean::cnstr_set(x_35, 1, x_34);
return x_35;
}
else
{
obj* x_37; obj* x_39; obj* x_41; obj* x_42; 
lean::dec(x_3);
x_37 = lean::cnstr_get(x_21, 0);
x_39 = lean::cnstr_get(x_21, 1);
if (lean::is_exclusive(x_21)) {
 x_41 = x_21;
} else {
 lean::inc(x_37);
 lean::inc(x_39);
 lean::dec(x_21);
 x_41 = lean::box(0);
}
if (lean::is_scalar(x_41)) {
 x_42 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_42 = x_41;
}
lean::cnstr_set(x_42, 0, x_37);
lean::cnstr_set(x_42, 1, x_39);
return x_42;
}
}
}
obj* l_Lean_IR_EmitCpp_emitSSet___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_IR_EmitCpp_emitSSet(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_4);
return x_6;
}
}
obj* _init_l_Nat_mforAux___main___at_Lean_IR_EmitCpp_emitJmp___spec__1___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string(" = ");
return x_0;
}
}
obj* l_Nat_mforAux___main___at_Lean_IR_EmitCpp_emitJmp___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; uint8 x_7; 
x_6 = lean::mk_nat_obj(0ul);
x_7 = lean::nat_dec_eq(x_3, x_6);
if (x_7 == 0)
{
obj* x_8; obj* x_10; obj* x_11; obj* x_12; obj* x_14; obj* x_15; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_22; obj* x_25; obj* x_26; obj* x_27; obj* x_29; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; 
x_8 = lean::cnstr_get(x_5, 1);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_release(x_5, 0);
 x_10 = x_5;
} else {
 lean::inc(x_8);
 lean::dec(x_5);
 x_10 = lean::box(0);
}
x_11 = lean::mk_nat_obj(1ul);
x_12 = lean::nat_sub(x_3, x_11);
lean::dec(x_3);
x_14 = lean::nat_sub(x_2, x_12);
x_15 = lean::nat_sub(x_14, x_11);
lean::dec(x_14);
x_17 = l_Lean_IR_paramInh;
x_18 = lean::array_get(x_17, x_1, x_15);
x_19 = l_Lean_IR_Arg_Inhabited;
x_20 = lean::array_get(x_19, x_0, x_15);
lean::dec(x_15);
x_22 = lean::cnstr_get(x_18, 0);
lean::inc(x_22);
lean::dec(x_18);
x_25 = l_Nat_repr(x_22);
x_26 = l_Lean_IR_VarId_HasToString___closed__1;
x_27 = lean::string_append(x_26, x_25);
lean::dec(x_25);
x_29 = lean::string_append(x_8, x_27);
lean::dec(x_27);
x_31 = l_Nat_mforAux___main___at_Lean_IR_EmitCpp_emitJmp___spec__1___closed__1;
x_32 = lean::string_append(x_29, x_31);
x_33 = lean::box(0);
if (lean::is_scalar(x_10)) {
 x_34 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_34 = x_10;
}
lean::cnstr_set(x_34, 0, x_33);
lean::cnstr_set(x_34, 1, x_32);
x_35 = l_Lean_IR_EmitCpp_emitArg(x_20, x_4, x_34);
if (lean::obj_tag(x_35) == 0)
{
obj* x_36; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; 
x_36 = lean::cnstr_get(x_35, 1);
if (lean::is_exclusive(x_35)) {
 lean::cnstr_release(x_35, 0);
 x_38 = x_35;
} else {
 lean::inc(x_36);
 lean::dec(x_35);
 x_38 = lean::box(0);
}
x_39 = l_Lean_IR_EmitCpp_emitFnDeclAux___closed__2;
x_40 = lean::string_append(x_36, x_39);
x_41 = l_IO_println___rarg___closed__1;
x_42 = lean::string_append(x_40, x_41);
if (lean::is_scalar(x_38)) {
 x_43 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_43 = x_38;
}
lean::cnstr_set(x_43, 0, x_33);
lean::cnstr_set(x_43, 1, x_42);
x_3 = x_12;
x_5 = x_43;
goto _start;
}
else
{
obj* x_46; obj* x_48; obj* x_50; obj* x_51; 
lean::dec(x_12);
x_46 = lean::cnstr_get(x_35, 0);
x_48 = lean::cnstr_get(x_35, 1);
if (lean::is_exclusive(x_35)) {
 x_50 = x_35;
} else {
 lean::inc(x_46);
 lean::inc(x_48);
 lean::dec(x_35);
 x_50 = lean::box(0);
}
if (lean::is_scalar(x_50)) {
 x_51 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_51 = x_50;
}
lean::cnstr_set(x_51, 0, x_46);
lean::cnstr_set(x_51, 1, x_48);
return x_51;
}
}
else
{
obj* x_53; obj* x_55; obj* x_56; obj* x_57; 
lean::dec(x_3);
x_53 = lean::cnstr_get(x_5, 1);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_release(x_5, 0);
 x_55 = x_5;
} else {
 lean::inc(x_53);
 lean::dec(x_5);
 x_55 = lean::box(0);
}
x_56 = lean::box(0);
if (lean::is_scalar(x_55)) {
 x_57 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_57 = x_55;
}
lean::cnstr_set(x_57, 0, x_56);
lean::cnstr_set(x_57, 1, x_53);
return x_57;
}
}
}
obj* _init_l_Lean_IR_EmitCpp_emitJmp___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("invalid goto");
return x_0;
}
}
obj* _init_l_Lean_IR_EmitCpp_emitJmp___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("goto ");
return x_0;
}
}
obj* l_Lean_IR_EmitCpp_emitJmp(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_IR_EmitCpp_getJPParams(x_0, x_2, x_3);
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; obj* x_7; obj* x_9; obj* x_10; obj* x_11; uint8 x_12; 
x_5 = lean::cnstr_get(x_4, 0);
x_7 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_set(x_4, 0, lean::box(0));
 lean::cnstr_set(x_4, 1, lean::box(0));
 x_9 = x_4;
} else {
 lean::inc(x_5);
 lean::inc(x_7);
 lean::dec(x_4);
 x_9 = lean::box(0);
}
x_10 = lean::array_get_size(x_1);
x_11 = lean::array_get_size(x_5);
x_12 = lean::nat_dec_eq(x_10, x_11);
lean::dec(x_11);
if (x_12 == 0)
{
obj* x_17; obj* x_18; 
lean::dec(x_5);
lean::dec(x_0);
lean::dec(x_10);
x_17 = l_Lean_IR_EmitCpp_emitJmp___closed__1;
if (lean::is_scalar(x_9)) {
 x_18 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_18 = x_9;
 lean::cnstr_set_tag(x_9, 1);
}
lean::cnstr_set(x_18, 0, x_17);
lean::cnstr_set(x_18, 1, x_7);
return x_18;
}
else
{
obj* x_19; obj* x_20; obj* x_22; 
x_19 = lean::box(0);
if (lean::is_scalar(x_9)) {
 x_20 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_20 = x_9;
}
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_7);
lean::inc(x_10);
x_22 = l_Nat_mforAux___main___at_Lean_IR_EmitCpp_emitJmp___spec__1(x_1, x_5, x_10, x_10, x_2, x_20);
lean::dec(x_10);
lean::dec(x_5);
if (lean::obj_tag(x_22) == 0)
{
obj* x_25; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_34; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; 
x_25 = lean::cnstr_get(x_22, 1);
if (lean::is_exclusive(x_22)) {
 lean::cnstr_release(x_22, 0);
 x_27 = x_22;
} else {
 lean::inc(x_25);
 lean::dec(x_22);
 x_27 = lean::box(0);
}
x_28 = l_Lean_IR_EmitCpp_emitJmp___closed__2;
x_29 = lean::string_append(x_25, x_28);
x_30 = l_Nat_repr(x_0);
x_31 = l_Lean_IR_JoinPointId_HasToString___closed__1;
x_32 = lean::string_append(x_31, x_30);
lean::dec(x_30);
x_34 = lean::string_append(x_29, x_32);
lean::dec(x_32);
x_36 = l_Lean_IR_EmitCpp_emitFnDeclAux___closed__2;
x_37 = lean::string_append(x_34, x_36);
x_38 = l_IO_println___rarg___closed__1;
x_39 = lean::string_append(x_37, x_38);
if (lean::is_scalar(x_27)) {
 x_40 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_40 = x_27;
}
lean::cnstr_set(x_40, 0, x_19);
lean::cnstr_set(x_40, 1, x_39);
return x_40;
}
else
{
obj* x_42; obj* x_44; obj* x_46; obj* x_47; 
lean::dec(x_0);
x_42 = lean::cnstr_get(x_22, 0);
x_44 = lean::cnstr_get(x_22, 1);
if (lean::is_exclusive(x_22)) {
 x_46 = x_22;
} else {
 lean::inc(x_42);
 lean::inc(x_44);
 lean::dec(x_22);
 x_46 = lean::box(0);
}
if (lean::is_scalar(x_46)) {
 x_47 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_47 = x_46;
}
lean::cnstr_set(x_47, 0, x_42);
lean::cnstr_set(x_47, 1, x_44);
return x_47;
}
}
}
else
{
obj* x_49; obj* x_51; obj* x_53; obj* x_54; 
lean::dec(x_0);
x_49 = lean::cnstr_get(x_4, 0);
x_51 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 x_53 = x_4;
} else {
 lean::inc(x_49);
 lean::inc(x_51);
 lean::dec(x_4);
 x_53 = lean::box(0);
}
if (lean::is_scalar(x_53)) {
 x_54 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_54 = x_53;
}
lean::cnstr_set(x_54, 0, x_49);
lean::cnstr_set(x_54, 1, x_51);
return x_54;
}
}
}
obj* l_Nat_mforAux___main___at_Lean_IR_EmitCpp_emitJmp___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Nat_mforAux___main___at_Lean_IR_EmitCpp_emitJmp___spec__1(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_4);
return x_6;
}
}
obj* l_Lean_IR_EmitCpp_emitJmp___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_IR_EmitCpp_emitJmp(x_0, x_1, x_2, x_3);
lean::dec(x_1);
lean::dec(x_2);
return x_4;
}
}
obj* l_Lean_IR_EmitCpp_emitLhs(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_10; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_3 = lean::cnstr_get(x_2, 1);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_release(x_2, 0);
 x_5 = x_2;
} else {
 lean::inc(x_3);
 lean::dec(x_2);
 x_5 = lean::box(0);
}
x_6 = l_Nat_repr(x_0);
x_7 = l_Lean_IR_VarId_HasToString___closed__1;
x_8 = lean::string_append(x_7, x_6);
lean::dec(x_6);
x_10 = lean::string_append(x_3, x_8);
lean::dec(x_8);
x_12 = l_Nat_mforAux___main___at_Lean_IR_EmitCpp_emitJmp___spec__1___closed__1;
x_13 = lean::string_append(x_10, x_12);
x_14 = lean::box(0);
if (lean::is_scalar(x_5)) {
 x_15 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_15 = x_5;
}
lean::cnstr_set(x_15, 0, x_14);
lean::cnstr_set(x_15, 1, x_13);
return x_15;
}
}
obj* l_Lean_IR_EmitCpp_emitLhs___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_EmitCpp_emitLhs(x_0, x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Nat_mforAux___main___at_Lean_IR_EmitCpp_emitArgs___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean::mk_nat_obj(0ul);
x_6 = lean::nat_dec_eq(x_2, x_5);
if (x_6 == 0)
{
obj* x_7; obj* x_8; obj* x_10; obj* x_11; uint8 x_13; 
x_7 = lean::mk_nat_obj(1ul);
x_8 = lean::nat_sub(x_2, x_7);
lean::dec(x_2);
x_10 = lean::nat_sub(x_1, x_8);
x_11 = lean::nat_sub(x_10, x_7);
lean::dec(x_10);
x_13 = lean::nat_dec_lt(x_5, x_11);
if (x_13 == 0)
{
obj* x_14; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_22; 
x_14 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 x_16 = x_4;
} else {
 lean::inc(x_14);
 lean::dec(x_4);
 x_16 = lean::box(0);
}
x_17 = lean::box(0);
if (lean::is_scalar(x_16)) {
 x_18 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_18 = x_16;
}
lean::cnstr_set(x_18, 0, x_17);
lean::cnstr_set(x_18, 1, x_14);
x_19 = l_Lean_IR_Arg_Inhabited;
x_20 = lean::array_get(x_19, x_0, x_11);
lean::dec(x_11);
x_22 = l_Lean_IR_EmitCpp_emitArg(x_20, x_3, x_18);
if (lean::obj_tag(x_22) == 0)
{
obj* x_23; obj* x_25; obj* x_26; 
x_23 = lean::cnstr_get(x_22, 1);
if (lean::is_exclusive(x_22)) {
 lean::cnstr_release(x_22, 0);
 x_25 = x_22;
} else {
 lean::inc(x_23);
 lean::dec(x_22);
 x_25 = lean::box(0);
}
if (lean::is_scalar(x_25)) {
 x_26 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_26 = x_25;
}
lean::cnstr_set(x_26, 0, x_17);
lean::cnstr_set(x_26, 1, x_23);
x_2 = x_8;
x_4 = x_26;
goto _start;
}
else
{
obj* x_29; obj* x_31; obj* x_33; obj* x_34; 
lean::dec(x_8);
x_29 = lean::cnstr_get(x_22, 0);
x_31 = lean::cnstr_get(x_22, 1);
if (lean::is_exclusive(x_22)) {
 x_33 = x_22;
} else {
 lean::inc(x_29);
 lean::inc(x_31);
 lean::dec(x_22);
 x_33 = lean::box(0);
}
if (lean::is_scalar(x_33)) {
 x_34 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_34 = x_33;
}
lean::cnstr_set(x_34, 0, x_29);
lean::cnstr_set(x_34, 1, x_31);
return x_34;
}
}
else
{
obj* x_35; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_45; 
x_35 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 x_37 = x_4;
} else {
 lean::inc(x_35);
 lean::dec(x_4);
 x_37 = lean::box(0);
}
x_38 = l_List_reprAux___main___rarg___closed__1;
x_39 = lean::string_append(x_35, x_38);
x_40 = lean::box(0);
if (lean::is_scalar(x_37)) {
 x_41 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_41 = x_37;
}
lean::cnstr_set(x_41, 0, x_40);
lean::cnstr_set(x_41, 1, x_39);
x_42 = l_Lean_IR_Arg_Inhabited;
x_43 = lean::array_get(x_42, x_0, x_11);
lean::dec(x_11);
x_45 = l_Lean_IR_EmitCpp_emitArg(x_43, x_3, x_41);
if (lean::obj_tag(x_45) == 0)
{
obj* x_46; obj* x_48; obj* x_49; 
x_46 = lean::cnstr_get(x_45, 1);
if (lean::is_exclusive(x_45)) {
 lean::cnstr_release(x_45, 0);
 x_48 = x_45;
} else {
 lean::inc(x_46);
 lean::dec(x_45);
 x_48 = lean::box(0);
}
if (lean::is_scalar(x_48)) {
 x_49 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_49 = x_48;
}
lean::cnstr_set(x_49, 0, x_40);
lean::cnstr_set(x_49, 1, x_46);
x_2 = x_8;
x_4 = x_49;
goto _start;
}
else
{
obj* x_52; obj* x_54; obj* x_56; obj* x_57; 
lean::dec(x_8);
x_52 = lean::cnstr_get(x_45, 0);
x_54 = lean::cnstr_get(x_45, 1);
if (lean::is_exclusive(x_45)) {
 x_56 = x_45;
} else {
 lean::inc(x_52);
 lean::inc(x_54);
 lean::dec(x_45);
 x_56 = lean::box(0);
}
if (lean::is_scalar(x_56)) {
 x_57 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_57 = x_56;
}
lean::cnstr_set(x_57, 0, x_52);
lean::cnstr_set(x_57, 1, x_54);
return x_57;
}
}
}
else
{
obj* x_59; obj* x_61; obj* x_62; obj* x_63; 
lean::dec(x_2);
x_59 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 x_61 = x_4;
} else {
 lean::inc(x_59);
 lean::dec(x_4);
 x_61 = lean::box(0);
}
x_62 = lean::box(0);
if (lean::is_scalar(x_61)) {
 x_63 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_63 = x_61;
}
lean::cnstr_set(x_63, 0, x_62);
lean::cnstr_set(x_63, 1, x_59);
return x_63;
}
}
}
obj* l_Lean_IR_EmitCpp_emitArgs(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; 
x_3 = lean::array_get_size(x_0);
lean::inc(x_3);
x_5 = l_Nat_mforAux___main___at_Lean_IR_EmitCpp_emitArgs___spec__1(x_0, x_3, x_3, x_1, x_2);
lean::dec(x_3);
return x_5;
}
}
obj* l_Nat_mforAux___main___at_Lean_IR_EmitCpp_emitArgs___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Nat_mforAux___main___at_Lean_IR_EmitCpp_emitArgs___spec__1(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_3);
return x_5;
}
}
obj* l_Lean_IR_EmitCpp_emitArgs___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_EmitCpp_emitArgs(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_IR_EmitCpp_emitCtor___rarg(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_4; obj* x_5; 
x_1 = lean::cnstr_get(x_0, 1);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 x_3 = x_0;
} else {
 lean::inc(x_1);
 lean::dec(x_0);
 x_3 = lean::box(0);
}
x_4 = lean::box(0);
if (lean::is_scalar(x_3)) {
 x_5 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_5 = x_3;
}
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_1);
return x_5;
}
}
obj* l_Lean_IR_EmitCpp_emitCtor(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_IR_EmitCpp_emitCtor___rarg), 1, 0);
return x_4;
}
}
obj* l_Lean_IR_EmitCpp_emitCtor___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_IR_EmitCpp_emitCtor(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
return x_4;
}
}
obj* l_Lean_IR_EmitCpp_emitReset___rarg(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_4; obj* x_5; 
x_1 = lean::cnstr_get(x_0, 1);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 x_3 = x_0;
} else {
 lean::inc(x_1);
 lean::dec(x_0);
 x_3 = lean::box(0);
}
x_4 = lean::box(0);
if (lean::is_scalar(x_3)) {
 x_5 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_5 = x_3;
}
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_1);
return x_5;
}
}
obj* l_Lean_IR_EmitCpp_emitReset(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_IR_EmitCpp_emitReset___rarg), 1, 0);
return x_4;
}
}
obj* l_Lean_IR_EmitCpp_emitReset___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_IR_EmitCpp_emitReset(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
return x_4;
}
}
obj* l_Lean_IR_EmitCpp_emitReuse___rarg(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_4; obj* x_5; 
x_1 = lean::cnstr_get(x_0, 1);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 x_3 = x_0;
} else {
 lean::inc(x_1);
 lean::dec(x_0);
 x_3 = lean::box(0);
}
x_4 = lean::box(0);
if (lean::is_scalar(x_3)) {
 x_5 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_5 = x_3;
}
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_1);
return x_5;
}
}
obj* l_Lean_IR_EmitCpp_emitReuse(obj* x_0, obj* x_1, obj* x_2, uint8 x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_IR_EmitCpp_emitReuse___rarg), 1, 0);
return x_6;
}
}
obj* l_Lean_IR_EmitCpp_emitReuse___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
uint8 x_6; obj* x_7; 
x_6 = lean::unbox(x_3);
x_7 = l_Lean_IR_EmitCpp_emitReuse(x_0, x_1, x_2, x_6, x_4, x_5);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_4);
lean::dec(x_5);
return x_7;
}
}
obj* _init_l_Lean_IR_EmitCpp_emitProj___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("lean::cnstr_get(");
return x_0;
}
}
obj* l_Lean_IR_EmitCpp_emitProj(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_IR_EmitCpp_emitLhs(x_0, x_3, x_4);
if (lean::obj_tag(x_5) == 0)
{
obj* x_6; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_15; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; 
x_6 = lean::cnstr_get(x_5, 1);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_release(x_5, 0);
 x_8 = x_5;
} else {
 lean::inc(x_6);
 lean::dec(x_5);
 x_8 = lean::box(0);
}
x_9 = l_Lean_IR_EmitCpp_emitProj___closed__1;
x_10 = lean::string_append(x_6, x_9);
x_11 = l_Nat_repr(x_2);
x_12 = l_Lean_IR_VarId_HasToString___closed__1;
x_13 = lean::string_append(x_12, x_11);
lean::dec(x_11);
x_15 = lean::string_append(x_10, x_13);
lean::dec(x_13);
x_17 = l_List_reprAux___main___rarg___closed__1;
x_18 = lean::string_append(x_15, x_17);
x_19 = l_Nat_repr(x_1);
x_20 = lean::string_append(x_18, x_19);
lean::dec(x_19);
x_22 = l_Lean_IR_EmitCpp_emitInc___closed__2;
x_23 = lean::string_append(x_20, x_22);
x_24 = l_IO_println___rarg___closed__1;
x_25 = lean::string_append(x_23, x_24);
x_26 = lean::box(0);
if (lean::is_scalar(x_8)) {
 x_27 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_27 = x_8;
}
lean::cnstr_set(x_27, 0, x_26);
lean::cnstr_set(x_27, 1, x_25);
return x_27;
}
else
{
obj* x_30; obj* x_32; obj* x_34; obj* x_35; 
lean::dec(x_1);
lean::dec(x_2);
x_30 = lean::cnstr_get(x_5, 0);
x_32 = lean::cnstr_get(x_5, 1);
if (lean::is_exclusive(x_5)) {
 x_34 = x_5;
} else {
 lean::inc(x_30);
 lean::inc(x_32);
 lean::dec(x_5);
 x_34 = lean::box(0);
}
if (lean::is_scalar(x_34)) {
 x_35 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_35 = x_34;
}
lean::cnstr_set(x_35, 0, x_30);
lean::cnstr_set(x_35, 1, x_32);
return x_35;
}
}
}
obj* l_Lean_IR_EmitCpp_emitProj___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_IR_EmitCpp_emitProj(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_3);
return x_5;
}
}
obj* l_Lean_IR_EmitCpp_emitUProj___rarg(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_4; obj* x_5; 
x_1 = lean::cnstr_get(x_0, 1);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 x_3 = x_0;
} else {
 lean::inc(x_1);
 lean::dec(x_0);
 x_3 = lean::box(0);
}
x_4 = lean::box(0);
if (lean::is_scalar(x_3)) {
 x_5 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_5 = x_3;
}
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_1);
return x_5;
}
}
obj* l_Lean_IR_EmitCpp_emitUProj(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_IR_EmitCpp_emitUProj___rarg), 1, 0);
return x_4;
}
}
obj* l_Lean_IR_EmitCpp_emitUProj___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_IR_EmitCpp_emitUProj(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
return x_4;
}
}
obj* l_Lean_IR_EmitCpp_emitSProj___rarg(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_4; obj* x_5; 
x_1 = lean::cnstr_get(x_0, 1);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 x_3 = x_0;
} else {
 lean::inc(x_1);
 lean::dec(x_0);
 x_3 = lean::box(0);
}
x_4 = lean::box(0);
if (lean::is_scalar(x_3)) {
 x_5 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_5 = x_3;
}
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_1);
return x_5;
}
}
obj* l_Lean_IR_EmitCpp_emitSProj(obj* x_0, uint8 x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_IR_EmitCpp_emitSProj___rarg), 1, 0);
return x_6;
}
}
obj* l_Lean_IR_EmitCpp_emitSProj___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
uint8 x_6; obj* x_7; 
x_6 = lean::unbox(x_1);
x_7 = l_Lean_IR_EmitCpp_emitSProj(x_0, x_6, x_2, x_3, x_4, x_5);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_3);
lean::dec(x_4);
lean::dec(x_5);
return x_7;
}
}
obj* l_List_map___main___at_Lean_IR_EmitCpp_toStringArgs___spec__1(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_1; 
x_1 = lean::box(0);
return x_1;
}
else
{
obj* x_2; obj* x_4; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_2 = lean::cnstr_get(x_0, 0);
x_4 = lean::cnstr_get(x_0, 1);
if (lean::is_exclusive(x_0)) {
 x_6 = x_0;
} else {
 lean::inc(x_2);
 lean::inc(x_4);
 lean::dec(x_0);
 x_6 = lean::box(0);
}
x_7 = l_Lean_IR_EmitCpp_argToCppString(x_2);
x_8 = l_List_map___main___at_Lean_IR_EmitCpp_toStringArgs___spec__1(x_4);
if (lean::is_scalar(x_6)) {
 x_9 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_9 = x_6;
}
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set(x_9, 1, x_8);
return x_9;
}
}
}
obj* l_Lean_IR_EmitCpp_toStringArgs(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_Array_toList___rarg(x_0);
x_2 = l_List_map___main___at_Lean_IR_EmitCpp_toStringArgs___spec__1(x_1);
return x_2;
}
}
obj* l_Lean_IR_EmitCpp_toStringArgs___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_IR_EmitCpp_toStringArgs(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* _init_l_Lean_IR_EmitCpp_emitFullApp___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("failed to emit extern application");
return x_0;
}
}
obj* l_Lean_IR_EmitCpp_emitFullApp(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_IR_EmitCpp_emitLhs(x_0, x_3, x_4);
if (lean::obj_tag(x_5) == 0)
{
obj* x_6; obj* x_8; obj* x_9; obj* x_10; obj* x_13; 
x_6 = lean::cnstr_get(x_5, 1);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_release(x_5, 0);
 x_8 = x_5;
} else {
 lean::inc(x_6);
 lean::dec(x_5);
 x_8 = lean::box(0);
}
x_9 = lean::box(0);
if (lean::is_scalar(x_8)) {
 x_10 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_10 = x_8;
}
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_6);
lean::inc(x_3);
lean::inc(x_1);
x_13 = l_Lean_IR_EmitCpp_getDecl(x_1, x_3, x_10);
if (lean::obj_tag(x_13) == 0)
{
obj* x_14; 
x_14 = lean::cnstr_get(x_13, 0);
lean::inc(x_14);
if (lean::obj_tag(x_14) == 0)
{
obj* x_17; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_24; obj* x_25; obj* x_26; obj* x_27; 
lean::dec(x_14);
x_17 = lean::cnstr_get(x_13, 1);
if (lean::is_exclusive(x_13)) {
 lean::cnstr_release(x_13, 0);
 x_19 = x_13;
} else {
 lean::inc(x_17);
 lean::dec(x_13);
 x_19 = lean::box(0);
}
x_20 = l_Lean_Name_toString___closed__1;
x_21 = l_Lean_Name_toStringWithSep___main(x_20, x_1);
x_22 = lean::string_append(x_17, x_21);
lean::dec(x_21);
x_24 = l_Prod_HasRepr___rarg___closed__1;
x_25 = lean::string_append(x_22, x_24);
if (lean::is_scalar(x_19)) {
 x_26 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_26 = x_19;
}
lean::cnstr_set(x_26, 0, x_9);
lean::cnstr_set(x_26, 1, x_25);
x_27 = l_Lean_IR_EmitCpp_emitArgs(x_2, x_3, x_26);
lean::dec(x_3);
if (lean::obj_tag(x_27) == 0)
{
obj* x_29; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; 
x_29 = lean::cnstr_get(x_27, 1);
if (lean::is_exclusive(x_27)) {
 lean::cnstr_release(x_27, 0);
 x_31 = x_27;
} else {
 lean::inc(x_29);
 lean::dec(x_27);
 x_31 = lean::box(0);
}
x_32 = l_Lean_IR_EmitCpp_emitInc___closed__2;
x_33 = lean::string_append(x_29, x_32);
x_34 = l_IO_println___rarg___closed__1;
x_35 = lean::string_append(x_33, x_34);
if (lean::is_scalar(x_31)) {
 x_36 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_36 = x_31;
}
lean::cnstr_set(x_36, 0, x_9);
lean::cnstr_set(x_36, 1, x_35);
return x_36;
}
else
{
obj* x_37; obj* x_39; obj* x_41; obj* x_42; 
x_37 = lean::cnstr_get(x_27, 0);
x_39 = lean::cnstr_get(x_27, 1);
if (lean::is_exclusive(x_27)) {
 x_41 = x_27;
} else {
 lean::inc(x_37);
 lean::inc(x_39);
 lean::dec(x_27);
 x_41 = lean::box(0);
}
if (lean::is_scalar(x_41)) {
 x_42 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_42 = x_41;
}
lean::cnstr_set(x_42, 0, x_37);
lean::cnstr_set(x_42, 1, x_39);
return x_42;
}
}
else
{
obj* x_45; obj* x_47; obj* x_48; obj* x_51; obj* x_52; obj* x_53; 
lean::dec(x_1);
lean::dec(x_3);
x_45 = lean::cnstr_get(x_13, 1);
if (lean::is_exclusive(x_13)) {
 lean::cnstr_release(x_13, 0);
 lean::cnstr_set(x_13, 1, lean::box(0));
 x_47 = x_13;
} else {
 lean::inc(x_45);
 lean::dec(x_13);
 x_47 = lean::box(0);
}
x_48 = lean::cnstr_get(x_14, 2);
lean::inc(x_48);
lean::dec(x_14);
x_51 = l_Lean_IR_EmitCpp_toStringArgs(x_2);
x_52 = l_List_mfor___main___at_Lean_IR_EmitCpp_emitFnDecls___spec__5___closed__1;
x_53 = lean::mk_extern_call_core(x_48, x_52, x_51);
if (lean::obj_tag(x_53) == 0)
{
obj* x_54; obj* x_55; 
x_54 = l_Lean_IR_EmitCpp_emitFullApp___closed__1;
if (lean::is_scalar(x_47)) {
 x_55 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_55 = x_47;
 lean::cnstr_set_tag(x_47, 1);
}
lean::cnstr_set(x_55, 0, x_54);
lean::cnstr_set(x_55, 1, x_45);
return x_55;
}
else
{
obj* x_56; obj* x_59; obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; 
x_56 = lean::cnstr_get(x_53, 0);
lean::inc(x_56);
lean::dec(x_53);
x_59 = lean::string_append(x_45, x_56);
lean::dec(x_56);
x_61 = l_Lean_IR_EmitCpp_emitFnDeclAux___closed__2;
x_62 = lean::string_append(x_59, x_61);
x_63 = l_IO_println___rarg___closed__1;
x_64 = lean::string_append(x_62, x_63);
if (lean::is_scalar(x_47)) {
 x_65 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_65 = x_47;
}
lean::cnstr_set(x_65, 0, x_9);
lean::cnstr_set(x_65, 1, x_64);
return x_65;
}
}
}
else
{
obj* x_68; obj* x_70; obj* x_72; obj* x_73; 
lean::dec(x_1);
lean::dec(x_3);
x_68 = lean::cnstr_get(x_13, 0);
x_70 = lean::cnstr_get(x_13, 1);
if (lean::is_exclusive(x_13)) {
 x_72 = x_13;
} else {
 lean::inc(x_68);
 lean::inc(x_70);
 lean::dec(x_13);
 x_72 = lean::box(0);
}
if (lean::is_scalar(x_72)) {
 x_73 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_73 = x_72;
}
lean::cnstr_set(x_73, 0, x_68);
lean::cnstr_set(x_73, 1, x_70);
return x_73;
}
}
else
{
obj* x_76; obj* x_78; obj* x_80; obj* x_81; 
lean::dec(x_1);
lean::dec(x_3);
x_76 = lean::cnstr_get(x_5, 0);
x_78 = lean::cnstr_get(x_5, 1);
if (lean::is_exclusive(x_5)) {
 x_80 = x_5;
} else {
 lean::inc(x_76);
 lean::inc(x_78);
 lean::dec(x_5);
 x_80 = lean::box(0);
}
if (lean::is_scalar(x_80)) {
 x_81 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_81 = x_80;
}
lean::cnstr_set(x_81, 0, x_76);
lean::cnstr_set(x_81, 1, x_78);
return x_81;
}
}
}
obj* l_Lean_IR_EmitCpp_emitFullApp___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_IR_EmitCpp_emitFullApp(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_2);
return x_5;
}
}
obj* _init_l_Nat_mforAux___main___at_Lean_IR_EmitCpp_emitPartialApp___spec__1___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("lean::closure_set(");
return x_0;
}
}
obj* l_Nat_mforAux___main___at_Lean_IR_EmitCpp_emitPartialApp___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; uint8 x_7; 
x_6 = lean::mk_nat_obj(0ul);
x_7 = lean::nat_dec_eq(x_3, x_6);
if (x_7 == 0)
{
obj* x_8; obj* x_10; obj* x_11; obj* x_12; obj* x_14; obj* x_15; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_22; obj* x_23; obj* x_24; obj* x_26; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_33; obj* x_34; obj* x_35; obj* x_36; 
x_8 = lean::cnstr_get(x_5, 1);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_release(x_5, 0);
 x_10 = x_5;
} else {
 lean::inc(x_8);
 lean::dec(x_5);
 x_10 = lean::box(0);
}
x_11 = lean::mk_nat_obj(1ul);
x_12 = lean::nat_sub(x_3, x_11);
lean::dec(x_3);
x_14 = lean::nat_sub(x_2, x_12);
x_15 = lean::nat_sub(x_14, x_11);
lean::dec(x_14);
x_17 = l_Lean_IR_Arg_Inhabited;
x_18 = lean::array_get(x_17, x_1, x_15);
x_19 = l_Nat_mforAux___main___at_Lean_IR_EmitCpp_emitPartialApp___spec__1___closed__1;
x_20 = lean::string_append(x_8, x_19);
lean::inc(x_0);
x_22 = l_Nat_repr(x_0);
x_23 = l_Lean_IR_VarId_HasToString___closed__1;
x_24 = lean::string_append(x_23, x_22);
lean::dec(x_22);
x_26 = lean::string_append(x_20, x_24);
lean::dec(x_24);
x_28 = l_List_reprAux___main___rarg___closed__1;
x_29 = lean::string_append(x_26, x_28);
x_30 = l_Nat_repr(x_15);
x_31 = lean::string_append(x_29, x_30);
lean::dec(x_30);
x_33 = lean::string_append(x_31, x_28);
x_34 = lean::box(0);
if (lean::is_scalar(x_10)) {
 x_35 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_35 = x_10;
}
lean::cnstr_set(x_35, 0, x_34);
lean::cnstr_set(x_35, 1, x_33);
x_36 = l_Lean_IR_EmitCpp_emitArg(x_18, x_4, x_35);
if (lean::obj_tag(x_36) == 0)
{
obj* x_37; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; 
x_37 = lean::cnstr_get(x_36, 1);
if (lean::is_exclusive(x_36)) {
 lean::cnstr_release(x_36, 0);
 x_39 = x_36;
} else {
 lean::inc(x_37);
 lean::dec(x_36);
 x_39 = lean::box(0);
}
x_40 = l_Lean_IR_EmitCpp_emitInc___closed__2;
x_41 = lean::string_append(x_37, x_40);
x_42 = l_IO_println___rarg___closed__1;
x_43 = lean::string_append(x_41, x_42);
if (lean::is_scalar(x_39)) {
 x_44 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_44 = x_39;
}
lean::cnstr_set(x_44, 0, x_34);
lean::cnstr_set(x_44, 1, x_43);
x_3 = x_12;
x_5 = x_44;
goto _start;
}
else
{
obj* x_48; obj* x_50; obj* x_52; obj* x_53; 
lean::dec(x_0);
lean::dec(x_12);
x_48 = lean::cnstr_get(x_36, 0);
x_50 = lean::cnstr_get(x_36, 1);
if (lean::is_exclusive(x_36)) {
 x_52 = x_36;
} else {
 lean::inc(x_48);
 lean::inc(x_50);
 lean::dec(x_36);
 x_52 = lean::box(0);
}
if (lean::is_scalar(x_52)) {
 x_53 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_53 = x_52;
}
lean::cnstr_set(x_53, 0, x_48);
lean::cnstr_set(x_53, 1, x_50);
return x_53;
}
}
else
{
obj* x_56; obj* x_58; obj* x_59; obj* x_60; 
lean::dec(x_3);
lean::dec(x_0);
x_56 = lean::cnstr_get(x_5, 1);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_release(x_5, 0);
 x_58 = x_5;
} else {
 lean::inc(x_56);
 lean::dec(x_5);
 x_58 = lean::box(0);
}
x_59 = lean::box(0);
if (lean::is_scalar(x_58)) {
 x_60 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_60 = x_58;
}
lean::cnstr_set(x_60, 0, x_59);
lean::cnstr_set(x_60, 1, x_56);
return x_60;
}
}
}
obj* _init_l_Lean_IR_EmitCpp_emitPartialApp___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("lean::alloc_closure(reinterpret_cast<void*>(");
return x_0;
}
}
obj* _init_l_Lean_IR_EmitCpp_emitPartialApp___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("), ");
return x_0;
}
}
obj* l_Lean_IR_EmitCpp_emitPartialApp(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_7; 
lean::inc(x_3);
lean::inc(x_1);
x_7 = l_Lean_IR_EmitCpp_getDecl(x_1, x_3, x_4);
if (lean::obj_tag(x_7) == 0)
{
obj* x_8; obj* x_10; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_17; obj* x_20; 
x_8 = lean::cnstr_get(x_7, 0);
x_10 = lean::cnstr_get(x_7, 1);
if (lean::is_exclusive(x_7)) {
 x_12 = x_7;
} else {
 lean::inc(x_8);
 lean::inc(x_10);
 lean::dec(x_7);
 x_12 = lean::box(0);
}
x_13 = lean::box(0);
if (lean::is_scalar(x_12)) {
 x_14 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_14 = x_12;
}
lean::cnstr_set(x_14, 0, x_13);
lean::cnstr_set(x_14, 1, x_10);
x_15 = l_Lean_IR_Decl_params___main(x_8);
lean::dec(x_8);
x_17 = lean::array_get_size(x_15);
lean::dec(x_15);
lean::inc(x_0);
x_20 = l_Lean_IR_EmitCpp_emitLhs(x_0, x_3, x_14);
if (lean::obj_tag(x_20) == 0)
{
obj* x_21; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_35; obj* x_36; obj* x_37; obj* x_39; obj* x_40; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_48; 
x_21 = lean::cnstr_get(x_20, 1);
if (lean::is_exclusive(x_20)) {
 lean::cnstr_release(x_20, 0);
 x_23 = x_20;
} else {
 lean::inc(x_21);
 lean::dec(x_20);
 x_23 = lean::box(0);
}
x_24 = l_Lean_IR_EmitCpp_emitPartialApp___closed__1;
x_25 = lean::string_append(x_21, x_24);
x_26 = l_Lean_Name_toString___closed__1;
x_27 = l_Lean_Name_toStringWithSep___main(x_26, x_1);
x_28 = lean::string_append(x_25, x_27);
lean::dec(x_27);
x_30 = l_Lean_IR_EmitCpp_emitPartialApp___closed__2;
x_31 = lean::string_append(x_28, x_30);
x_32 = l_Nat_repr(x_17);
x_33 = lean::string_append(x_31, x_32);
lean::dec(x_32);
x_35 = l_List_reprAux___main___rarg___closed__1;
x_36 = lean::string_append(x_33, x_35);
x_37 = lean::array_get_size(x_2);
lean::inc(x_37);
x_39 = l_Nat_repr(x_37);
x_40 = lean::string_append(x_36, x_39);
lean::dec(x_39);
x_42 = l_Lean_IR_EmitCpp_emitInc___closed__2;
x_43 = lean::string_append(x_40, x_42);
x_44 = l_IO_println___rarg___closed__1;
x_45 = lean::string_append(x_43, x_44);
if (lean::is_scalar(x_23)) {
 x_46 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_46 = x_23;
}
lean::cnstr_set(x_46, 0, x_13);
lean::cnstr_set(x_46, 1, x_45);
lean::inc(x_37);
x_48 = l_Nat_mforAux___main___at_Lean_IR_EmitCpp_emitPartialApp___spec__1(x_0, x_2, x_37, x_37, x_3, x_46);
lean::dec(x_3);
lean::dec(x_37);
return x_48;
}
else
{
obj* x_55; obj* x_57; obj* x_59; obj* x_60; 
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_17);
x_55 = lean::cnstr_get(x_20, 0);
x_57 = lean::cnstr_get(x_20, 1);
if (lean::is_exclusive(x_20)) {
 x_59 = x_20;
} else {
 lean::inc(x_55);
 lean::inc(x_57);
 lean::dec(x_20);
 x_59 = lean::box(0);
}
if (lean::is_scalar(x_59)) {
 x_60 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_60 = x_59;
}
lean::cnstr_set(x_60, 0, x_55);
lean::cnstr_set(x_60, 1, x_57);
return x_60;
}
}
else
{
obj* x_64; obj* x_66; obj* x_68; obj* x_69; 
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_0);
x_64 = lean::cnstr_get(x_7, 0);
x_66 = lean::cnstr_get(x_7, 1);
if (lean::is_exclusive(x_7)) {
 x_68 = x_7;
} else {
 lean::inc(x_64);
 lean::inc(x_66);
 lean::dec(x_7);
 x_68 = lean::box(0);
}
if (lean::is_scalar(x_68)) {
 x_69 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_69 = x_68;
}
lean::cnstr_set(x_69, 0, x_64);
lean::cnstr_set(x_69, 1, x_66);
return x_69;
}
}
}
obj* l_Nat_mforAux___main___at_Lean_IR_EmitCpp_emitPartialApp___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Nat_mforAux___main___at_Lean_IR_EmitCpp_emitPartialApp___spec__1(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_4);
return x_6;
}
}
obj* l_Lean_IR_EmitCpp_emitPartialApp___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_IR_EmitCpp_emitPartialApp(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_2);
return x_5;
}
}
obj* l_Lean_IR_EmitCpp_emitApp___rarg(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_4; obj* x_5; 
x_1 = lean::cnstr_get(x_0, 1);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 x_3 = x_0;
} else {
 lean::inc(x_1);
 lean::dec(x_0);
 x_3 = lean::box(0);
}
x_4 = lean::box(0);
if (lean::is_scalar(x_3)) {
 x_5 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_5 = x_3;
}
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_1);
return x_5;
}
}
obj* l_Lean_IR_EmitCpp_emitApp(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_IR_EmitCpp_emitApp___rarg), 1, 0);
return x_4;
}
}
obj* l_Lean_IR_EmitCpp_emitApp___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_IR_EmitCpp_emitApp(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
return x_4;
}
}
obj* _init_l_Lean_IR_EmitCpp_emitBox___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("floats are not supported yet");
return x_0;
}
}
obj* _init_l_Lean_IR_EmitCpp_emitBox___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("lean::box");
return x_0;
}
}
obj* _init_l_Lean_IR_EmitCpp_emitBox___closed__3() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("lean::box_uint32");
return x_0;
}
}
obj* _init_l_Lean_IR_EmitCpp_emitBox___closed__4() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("lean::box_uint64");
return x_0;
}
}
obj* _init_l_Lean_IR_EmitCpp_emitBox___closed__5() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("lean::box_size_t");
return x_0;
}
}
obj* l_Lean_IR_EmitCpp_emitBox(obj* x_0, obj* x_1, uint8 x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_7; 
x_7 = l_Lean_IR_EmitCpp_emitLhs(x_0, x_3, x_4);
if (lean::obj_tag(x_7) == 0)
{
switch (x_2) {
case 0:
{
obj* x_9; obj* x_11; obj* x_12; obj* x_13; 
lean::dec(x_1);
x_9 = lean::cnstr_get(x_7, 1);
if (lean::is_exclusive(x_7)) {
 lean::cnstr_release(x_7, 0);
 x_11 = x_7;
} else {
 lean::inc(x_9);
 lean::dec(x_7);
 x_11 = lean::box(0);
}
x_12 = l_Lean_IR_EmitCpp_emitBox___closed__1;
if (lean::is_scalar(x_11)) {
 x_13 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_13 = x_11;
 lean::cnstr_set_tag(x_11, 1);
}
lean::cnstr_set(x_13, 0, x_12);
lean::cnstr_set(x_13, 1, x_9);
return x_13;
}
case 3:
{
obj* x_14; obj* x_17; obj* x_18; 
x_14 = lean::cnstr_get(x_7, 1);
lean::inc(x_14);
lean::dec(x_7);
x_17 = l_Lean_IR_EmitCpp_emitBox___closed__3;
x_18 = lean::string_append(x_14, x_17);
x_5 = x_18;
goto lbl_6;
}
case 4:
{
obj* x_19; obj* x_22; obj* x_23; 
x_19 = lean::cnstr_get(x_7, 1);
lean::inc(x_19);
lean::dec(x_7);
x_22 = l_Lean_IR_EmitCpp_emitBox___closed__4;
x_23 = lean::string_append(x_19, x_22);
x_5 = x_23;
goto lbl_6;
}
case 5:
{
obj* x_24; obj* x_27; obj* x_28; 
x_24 = lean::cnstr_get(x_7, 1);
lean::inc(x_24);
lean::dec(x_7);
x_27 = l_Lean_IR_EmitCpp_emitBox___closed__5;
x_28 = lean::string_append(x_24, x_27);
x_5 = x_28;
goto lbl_6;
}
default:
{
obj* x_29; obj* x_32; obj* x_33; 
x_29 = lean::cnstr_get(x_7, 1);
lean::inc(x_29);
lean::dec(x_7);
x_32 = l_Lean_IR_EmitCpp_emitBox___closed__2;
x_33 = lean::string_append(x_29, x_32);
x_5 = x_33;
goto lbl_6;
}
}
}
else
{
obj* x_35; obj* x_37; obj* x_39; obj* x_40; 
lean::dec(x_1);
x_35 = lean::cnstr_get(x_7, 0);
x_37 = lean::cnstr_get(x_7, 1);
if (lean::is_exclusive(x_7)) {
 x_39 = x_7;
} else {
 lean::inc(x_35);
 lean::inc(x_37);
 lean::dec(x_7);
 x_39 = lean::box(0);
}
if (lean::is_scalar(x_39)) {
 x_40 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_40 = x_39;
}
lean::cnstr_set(x_40, 0, x_35);
lean::cnstr_set(x_40, 1, x_37);
return x_40;
}
lbl_6:
{
obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_47; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; 
x_41 = l_Prod_HasRepr___rarg___closed__1;
x_42 = lean::string_append(x_5, x_41);
x_43 = l_Nat_repr(x_1);
x_44 = l_Lean_IR_VarId_HasToString___closed__1;
x_45 = lean::string_append(x_44, x_43);
lean::dec(x_43);
x_47 = lean::string_append(x_42, x_45);
lean::dec(x_45);
x_49 = l_Lean_IR_EmitCpp_emitInc___closed__2;
x_50 = lean::string_append(x_47, x_49);
x_51 = l_IO_println___rarg___closed__1;
x_52 = lean::string_append(x_50, x_51);
x_53 = lean::box(0);
x_54 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_54, 0, x_53);
lean::cnstr_set(x_54, 1, x_52);
return x_54;
}
}
}
obj* l_Lean_IR_EmitCpp_emitBox___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; obj* x_6; 
x_5 = lean::unbox(x_2);
x_6 = l_Lean_IR_EmitCpp_emitBox(x_0, x_1, x_5, x_3, x_4);
lean::dec(x_3);
return x_6;
}
}
obj* _init_l_Lean_IR_EmitCpp_emitUnbox___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("lean::unbox");
return x_0;
}
}
obj* _init_l_Lean_IR_EmitCpp_emitUnbox___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("lean::unbox_uint32");
return x_0;
}
}
obj* _init_l_Lean_IR_EmitCpp_emitUnbox___closed__3() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("lean::unbox_uint64");
return x_0;
}
}
obj* _init_l_Lean_IR_EmitCpp_emitUnbox___closed__4() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("lean::unbox_size_t");
return x_0;
}
}
obj* l_Lean_IR_EmitCpp_emitUnbox(obj* x_0, uint8 x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_7; 
x_7 = l_Lean_IR_EmitCpp_emitLhs(x_0, x_3, x_4);
if (lean::obj_tag(x_7) == 0)
{
switch (x_1) {
case 0:
{
obj* x_9; obj* x_11; obj* x_12; obj* x_13; 
lean::dec(x_2);
x_9 = lean::cnstr_get(x_7, 1);
if (lean::is_exclusive(x_7)) {
 lean::cnstr_release(x_7, 0);
 x_11 = x_7;
} else {
 lean::inc(x_9);
 lean::dec(x_7);
 x_11 = lean::box(0);
}
x_12 = l_Lean_IR_EmitCpp_emitBox___closed__1;
if (lean::is_scalar(x_11)) {
 x_13 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_13 = x_11;
 lean::cnstr_set_tag(x_11, 1);
}
lean::cnstr_set(x_13, 0, x_12);
lean::cnstr_set(x_13, 1, x_9);
return x_13;
}
case 3:
{
obj* x_14; obj* x_17; obj* x_18; 
x_14 = lean::cnstr_get(x_7, 1);
lean::inc(x_14);
lean::dec(x_7);
x_17 = l_Lean_IR_EmitCpp_emitUnbox___closed__2;
x_18 = lean::string_append(x_14, x_17);
x_5 = x_18;
goto lbl_6;
}
case 4:
{
obj* x_19; obj* x_22; obj* x_23; 
x_19 = lean::cnstr_get(x_7, 1);
lean::inc(x_19);
lean::dec(x_7);
x_22 = l_Lean_IR_EmitCpp_emitUnbox___closed__3;
x_23 = lean::string_append(x_19, x_22);
x_5 = x_23;
goto lbl_6;
}
case 5:
{
obj* x_24; obj* x_27; obj* x_28; 
x_24 = lean::cnstr_get(x_7, 1);
lean::inc(x_24);
lean::dec(x_7);
x_27 = l_Lean_IR_EmitCpp_emitUnbox___closed__4;
x_28 = lean::string_append(x_24, x_27);
x_5 = x_28;
goto lbl_6;
}
default:
{
obj* x_29; obj* x_32; obj* x_33; 
x_29 = lean::cnstr_get(x_7, 1);
lean::inc(x_29);
lean::dec(x_7);
x_32 = l_Lean_IR_EmitCpp_emitUnbox___closed__1;
x_33 = lean::string_append(x_29, x_32);
x_5 = x_33;
goto lbl_6;
}
}
}
else
{
obj* x_35; obj* x_37; obj* x_39; obj* x_40; 
lean::dec(x_2);
x_35 = lean::cnstr_get(x_7, 0);
x_37 = lean::cnstr_get(x_7, 1);
if (lean::is_exclusive(x_7)) {
 x_39 = x_7;
} else {
 lean::inc(x_35);
 lean::inc(x_37);
 lean::dec(x_7);
 x_39 = lean::box(0);
}
if (lean::is_scalar(x_39)) {
 x_40 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_40 = x_39;
}
lean::cnstr_set(x_40, 0, x_35);
lean::cnstr_set(x_40, 1, x_37);
return x_40;
}
lbl_6:
{
obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_47; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; 
x_41 = l_Prod_HasRepr___rarg___closed__1;
x_42 = lean::string_append(x_5, x_41);
x_43 = l_Nat_repr(x_2);
x_44 = l_Lean_IR_VarId_HasToString___closed__1;
x_45 = lean::string_append(x_44, x_43);
lean::dec(x_43);
x_47 = lean::string_append(x_42, x_45);
lean::dec(x_45);
x_49 = l_Lean_IR_EmitCpp_emitInc___closed__2;
x_50 = lean::string_append(x_47, x_49);
x_51 = l_IO_println___rarg___closed__1;
x_52 = lean::string_append(x_50, x_51);
x_53 = lean::box(0);
x_54 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_54, 0, x_53);
lean::cnstr_set(x_54, 1, x_52);
return x_54;
}
}
}
obj* l_Lean_IR_EmitCpp_emitUnbox___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; obj* x_6; 
x_5 = lean::unbox(x_1);
x_6 = l_Lean_IR_EmitCpp_emitUnbox(x_0, x_5, x_2, x_3, x_4);
lean::dec(x_3);
return x_6;
}
}
obj* _init_l_Lean_IR_EmitCpp_emitIsShared___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("!lean::is_exclusive(");
return x_0;
}
}
obj* l_Lean_IR_EmitCpp_emitIsShared(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_IR_EmitCpp_emitLhs(x_0, x_2, x_3);
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_14; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; 
x_5 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 x_7 = x_4;
} else {
 lean::inc(x_5);
 lean::dec(x_4);
 x_7 = lean::box(0);
}
x_8 = l_Lean_IR_EmitCpp_emitIsShared___closed__1;
x_9 = lean::string_append(x_5, x_8);
x_10 = l_Nat_repr(x_1);
x_11 = l_Lean_IR_VarId_HasToString___closed__1;
x_12 = lean::string_append(x_11, x_10);
lean::dec(x_10);
x_14 = lean::string_append(x_9, x_12);
lean::dec(x_12);
x_16 = l_Lean_IR_EmitCpp_emitInc___closed__2;
x_17 = lean::string_append(x_14, x_16);
x_18 = l_IO_println___rarg___closed__1;
x_19 = lean::string_append(x_17, x_18);
x_20 = lean::box(0);
if (lean::is_scalar(x_7)) {
 x_21 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_21 = x_7;
}
lean::cnstr_set(x_21, 0, x_20);
lean::cnstr_set(x_21, 1, x_19);
return x_21;
}
else
{
obj* x_23; obj* x_25; obj* x_27; obj* x_28; 
lean::dec(x_1);
x_23 = lean::cnstr_get(x_4, 0);
x_25 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 x_27 = x_4;
} else {
 lean::inc(x_23);
 lean::inc(x_25);
 lean::dec(x_4);
 x_27 = lean::box(0);
}
if (lean::is_scalar(x_27)) {
 x_28 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_28 = x_27;
}
lean::cnstr_set(x_28, 0, x_23);
lean::cnstr_set(x_28, 1, x_25);
return x_28;
}
}
}
obj* l_Lean_IR_EmitCpp_emitIsShared___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_IR_EmitCpp_emitIsShared(x_0, x_1, x_2, x_3);
lean::dec(x_2);
return x_4;
}
}
obj* _init_l_Lean_IR_EmitCpp_emitIsTaggedPtr___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("!lean::is_scalar(");
return x_0;
}
}
obj* l_Lean_IR_EmitCpp_emitIsTaggedPtr(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_IR_EmitCpp_emitLhs(x_0, x_2, x_3);
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_14; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; 
x_5 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 x_7 = x_4;
} else {
 lean::inc(x_5);
 lean::dec(x_4);
 x_7 = lean::box(0);
}
x_8 = l_Lean_IR_EmitCpp_emitIsTaggedPtr___closed__1;
x_9 = lean::string_append(x_5, x_8);
x_10 = l_Nat_repr(x_1);
x_11 = l_Lean_IR_VarId_HasToString___closed__1;
x_12 = lean::string_append(x_11, x_10);
lean::dec(x_10);
x_14 = lean::string_append(x_9, x_12);
lean::dec(x_12);
x_16 = l_Lean_IR_EmitCpp_emitInc___closed__2;
x_17 = lean::string_append(x_14, x_16);
x_18 = l_IO_println___rarg___closed__1;
x_19 = lean::string_append(x_17, x_18);
x_20 = lean::box(0);
if (lean::is_scalar(x_7)) {
 x_21 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_21 = x_7;
}
lean::cnstr_set(x_21, 0, x_20);
lean::cnstr_set(x_21, 1, x_19);
return x_21;
}
else
{
obj* x_23; obj* x_25; obj* x_27; obj* x_28; 
lean::dec(x_1);
x_23 = lean::cnstr_get(x_4, 0);
x_25 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 x_27 = x_4;
} else {
 lean::inc(x_23);
 lean::inc(x_25);
 lean::dec(x_4);
 x_27 = lean::box(0);
}
if (lean::is_scalar(x_27)) {
 x_28 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_28 = x_27;
}
lean::cnstr_set(x_28, 0, x_23);
lean::cnstr_set(x_28, 1, x_25);
return x_28;
}
}
}
obj* l_Lean_IR_EmitCpp_emitIsTaggedPtr___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_IR_EmitCpp_emitIsTaggedPtr(x_0, x_1, x_2, x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l_Lean_IR_EmitCpp_toHexDigit(obj* x_0) {
_start:
{
uint32 x_1; obj* x_2; obj* x_3; 
x_1 = l_Nat_digitChar(x_0);
x_2 = l_String_splitAux___main___closed__1;
x_3 = lean::string_push(x_2, x_1);
return x_3;
}
}
obj* l_Lean_IR_EmitCpp_toHexDigit___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_IR_EmitCpp_toHexDigit(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_String_foldlAux___main___at_Lean_IR_EmitCpp_quoteString___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = lean::nat_dec_eq(x_2, x_1);
if (x_4 == 0)
{
obj* x_5; uint32 x_6; uint32 x_8; uint8 x_9; 
x_5 = lean::string_utf8_next(x_0, x_2);
x_6 = lean::string_utf8_get(x_0, x_2);
lean::dec(x_2);
x_8 = 10;
x_9 = x_6 == x_8;
if (x_9 == 0)
{
uint32 x_10; uint8 x_11; 
x_10 = 92;
x_11 = x_6 == x_10;
if (x_11 == 0)
{
uint32 x_12; uint8 x_13; 
x_12 = 34;
x_13 = x_6 == x_12;
if (x_13 == 0)
{
obj* x_14; obj* x_15; uint8 x_16; 
x_14 = lean::uint32_to_nat(x_6);
x_15 = lean::mk_nat_obj(31ul);
x_16 = lean::nat_dec_le(x_14, x_15);
if (x_16 == 0)
{
obj* x_17; uint8 x_18; 
x_17 = lean::mk_nat_obj(127ul);
x_18 = lean::nat_dec_le(x_17, x_14);
if (x_18 == 0)
{
obj* x_20; obj* x_21; obj* x_22; 
lean::dec(x_14);
x_20 = l_String_splitAux___main___closed__1;
x_21 = lean::string_push(x_20, x_6);
x_22 = lean::string_append(x_3, x_21);
lean::dec(x_21);
x_2 = x_5;
x_3 = x_22;
goto _start;
}
else
{
obj* x_25; obj* x_26; obj* x_27; obj* x_29; obj* x_30; obj* x_32; obj* x_34; obj* x_36; obj* x_38; 
x_25 = lean::mk_nat_obj(16ul);
x_26 = lean::nat_div(x_14, x_25);
x_27 = l_Lean_IR_EmitCpp_toHexDigit(x_26);
lean::dec(x_26);
x_29 = l_Char_quoteCore___closed__1;
x_30 = lean::string_append(x_29, x_27);
lean::dec(x_27);
x_32 = lean::nat_mod(x_14, x_25);
lean::dec(x_14);
x_34 = l_Lean_IR_EmitCpp_toHexDigit(x_32);
lean::dec(x_32);
x_36 = lean::string_append(x_30, x_34);
lean::dec(x_34);
x_38 = lean::string_append(x_3, x_36);
lean::dec(x_36);
x_2 = x_5;
x_3 = x_38;
goto _start;
}
}
else
{
obj* x_41; obj* x_42; obj* x_43; obj* x_45; obj* x_46; obj* x_48; obj* x_50; obj* x_52; obj* x_54; 
x_41 = lean::mk_nat_obj(16ul);
x_42 = lean::nat_div(x_14, x_41);
x_43 = l_Lean_IR_EmitCpp_toHexDigit(x_42);
lean::dec(x_42);
x_45 = l_Char_quoteCore___closed__1;
x_46 = lean::string_append(x_45, x_43);
lean::dec(x_43);
x_48 = lean::nat_mod(x_14, x_41);
lean::dec(x_14);
x_50 = l_Lean_IR_EmitCpp_toHexDigit(x_48);
lean::dec(x_48);
x_52 = lean::string_append(x_46, x_50);
lean::dec(x_50);
x_54 = lean::string_append(x_3, x_52);
lean::dec(x_52);
x_2 = x_5;
x_3 = x_54;
goto _start;
}
}
else
{
obj* x_57; obj* x_58; 
x_57 = l_Char_quoteCore___closed__2;
x_58 = lean::string_append(x_3, x_57);
x_2 = x_5;
x_3 = x_58;
goto _start;
}
}
else
{
obj* x_60; obj* x_61; 
x_60 = l_Char_quoteCore___closed__3;
x_61 = lean::string_append(x_3, x_60);
x_2 = x_5;
x_3 = x_61;
goto _start;
}
}
else
{
obj* x_63; obj* x_64; 
x_63 = l_Char_quoteCore___closed__5;
x_64 = lean::string_append(x_3, x_63);
x_2 = x_5;
x_3 = x_64;
goto _start;
}
}
else
{
lean::dec(x_2);
return x_3;
}
}
}
obj* l_Lean_IR_EmitCpp_quoteString(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_6; 
x_1 = lean::string_utf8_byte_size(x_0);
x_2 = lean::mk_nat_obj(0ul);
x_3 = l_String_quote___closed__1;
x_4 = l_String_foldlAux___main___at_Lean_IR_EmitCpp_quoteString___spec__1(x_0, x_1, x_2, x_3);
lean::dec(x_1);
x_6 = lean::string_append(x_4, x_3);
return x_6;
}
}
obj* l_String_foldlAux___main___at_Lean_IR_EmitCpp_quoteString___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_String_foldlAux___main___at_Lean_IR_EmitCpp_quoteString___spec__1(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_IR_EmitCpp_quoteString___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_IR_EmitCpp_quoteString(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* _init_l_Lean_IR_EmitCpp_emitNumLit___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("lean::mk_nat_obj(");
return x_0;
}
}
obj* _init_l_Lean_IR_EmitCpp_emitNumLit___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("lean::mpz(\"");
return x_0;
}
}
obj* l_Lean_IR_EmitCpp_emitNumLit(uint8 x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = l_Lean_IR_IRType_isObj___main(x_0);
if (x_4 == 0)
{
obj* x_5; obj* x_7; obj* x_8; obj* x_9; obj* x_11; obj* x_12; 
x_5 = lean::cnstr_get(x_3, 1);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 x_7 = x_3;
} else {
 lean::inc(x_5);
 lean::dec(x_3);
 x_7 = lean::box(0);
}
x_8 = l_Nat_repr(x_1);
x_9 = lean::string_append(x_5, x_8);
lean::dec(x_8);
x_11 = lean::box(0);
if (lean::is_scalar(x_7)) {
 x_12 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_12 = x_7;
}
lean::cnstr_set(x_12, 0, x_11);
lean::cnstr_set(x_12, 1, x_9);
return x_12;
}
else
{
obj* x_13; obj* x_15; obj* x_16; obj* x_17; obj* x_18; uint8 x_19; 
x_13 = lean::cnstr_get(x_3, 1);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 lean::cnstr_set(x_3, 1, lean::box(0));
 x_15 = x_3;
} else {
 lean::inc(x_13);
 lean::dec(x_3);
 x_15 = lean::box(0);
}
x_16 = l_Lean_IR_EmitCpp_emitNumLit___closed__1;
x_17 = lean::string_append(x_13, x_16);
x_18 = l_uint32Sz;
x_19 = lean::nat_dec_lt(x_1, x_18);
if (x_19 == 0)
{
obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
x_20 = l_Lean_IR_EmitCpp_emitNumLit___closed__2;
x_21 = lean::string_append(x_17, x_20);
x_22 = l_Nat_repr(x_1);
x_23 = lean::string_append(x_21, x_22);
lean::dec(x_22);
x_25 = l_String_quote___closed__1;
x_26 = lean::string_append(x_23, x_25);
x_27 = l_Option_HasRepr___rarg___closed__3;
x_28 = lean::string_append(x_26, x_27);
x_29 = lean::box(0);
if (lean::is_scalar(x_15)) {
 x_30 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_30 = x_15;
}
lean::cnstr_set(x_30, 0, x_29);
lean::cnstr_set(x_30, 1, x_28);
return x_30;
}
else
{
obj* x_31; obj* x_32; obj* x_34; obj* x_35; obj* x_36; obj* x_37; 
x_31 = l_Nat_repr(x_1);
x_32 = lean::string_append(x_17, x_31);
lean::dec(x_31);
x_34 = l_Option_HasRepr___rarg___closed__3;
x_35 = lean::string_append(x_32, x_34);
x_36 = lean::box(0);
if (lean::is_scalar(x_15)) {
 x_37 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_37 = x_15;
}
lean::cnstr_set(x_37, 0, x_36);
lean::cnstr_set(x_37, 1, x_35);
return x_37;
}
}
}
}
obj* l_Lean_IR_EmitCpp_emitNumLit___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = lean::unbox(x_0);
x_5 = l_Lean_IR_EmitCpp_emitNumLit(x_4, x_1, x_2, x_3);
lean::dec(x_2);
return x_5;
}
}
obj* _init_l_Lean_IR_EmitCpp_emitLit___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("lean::mk_string(");
return x_0;
}
}
obj* l_Lean_IR_EmitCpp_emitLit(obj* x_0, uint8 x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_IR_EmitCpp_emitLhs(x_0, x_3, x_4);
if (lean::obj_tag(x_5) == 0)
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_6; obj* x_8; obj* x_9; obj* x_12; obj* x_13; obj* x_14; 
x_6 = lean::cnstr_get(x_5, 1);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_release(x_5, 0);
 x_8 = x_5;
} else {
 lean::inc(x_6);
 lean::dec(x_5);
 x_8 = lean::box(0);
}
x_9 = lean::cnstr_get(x_2, 0);
lean::inc(x_9);
lean::dec(x_2);
x_12 = lean::box(0);
if (lean::is_scalar(x_8)) {
 x_13 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_13 = x_8;
}
lean::cnstr_set(x_13, 0, x_12);
lean::cnstr_set(x_13, 1, x_6);
x_14 = l_Lean_IR_EmitCpp_emitNumLit(x_1, x_9, x_3, x_13);
if (lean::obj_tag(x_14) == 0)
{
obj* x_15; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
x_15 = lean::cnstr_get(x_14, 1);
if (lean::is_exclusive(x_14)) {
 lean::cnstr_release(x_14, 0);
 x_17 = x_14;
} else {
 lean::inc(x_15);
 lean::dec(x_14);
 x_17 = lean::box(0);
}
x_18 = l_Lean_IR_EmitCpp_emitFnDeclAux___closed__2;
x_19 = lean::string_append(x_15, x_18);
x_20 = l_IO_println___rarg___closed__1;
x_21 = lean::string_append(x_19, x_20);
if (lean::is_scalar(x_17)) {
 x_22 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_22 = x_17;
}
lean::cnstr_set(x_22, 0, x_12);
lean::cnstr_set(x_22, 1, x_21);
return x_22;
}
else
{
obj* x_23; obj* x_25; obj* x_27; obj* x_28; 
x_23 = lean::cnstr_get(x_14, 0);
x_25 = lean::cnstr_get(x_14, 1);
if (lean::is_exclusive(x_14)) {
 x_27 = x_14;
} else {
 lean::inc(x_23);
 lean::inc(x_25);
 lean::dec(x_14);
 x_27 = lean::box(0);
}
if (lean::is_scalar(x_27)) {
 x_28 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_28 = x_27;
}
lean::cnstr_set(x_28, 0, x_23);
lean::cnstr_set(x_28, 1, x_25);
return x_28;
}
}
else
{
obj* x_29; obj* x_31; obj* x_32; obj* x_35; obj* x_36; obj* x_37; obj* x_39; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; 
x_29 = lean::cnstr_get(x_5, 1);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_release(x_5, 0);
 x_31 = x_5;
} else {
 lean::inc(x_29);
 lean::dec(x_5);
 x_31 = lean::box(0);
}
x_32 = lean::cnstr_get(x_2, 0);
lean::inc(x_32);
lean::dec(x_2);
x_35 = l_Lean_IR_EmitCpp_emitLit___closed__1;
x_36 = lean::string_append(x_29, x_35);
x_37 = l_Lean_IR_EmitCpp_quoteString(x_32);
lean::dec(x_32);
x_39 = lean::string_append(x_36, x_37);
lean::dec(x_37);
x_41 = l_Lean_IR_EmitCpp_emitInc___closed__2;
x_42 = lean::string_append(x_39, x_41);
x_43 = l_IO_println___rarg___closed__1;
x_44 = lean::string_append(x_42, x_43);
x_45 = lean::box(0);
if (lean::is_scalar(x_31)) {
 x_46 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_46 = x_31;
}
lean::cnstr_set(x_46, 0, x_45);
lean::cnstr_set(x_46, 1, x_44);
return x_46;
}
}
else
{
obj* x_48; obj* x_50; obj* x_52; obj* x_53; 
lean::dec(x_2);
x_48 = lean::cnstr_get(x_5, 0);
x_50 = lean::cnstr_get(x_5, 1);
if (lean::is_exclusive(x_5)) {
 x_52 = x_5;
} else {
 lean::inc(x_48);
 lean::inc(x_50);
 lean::dec(x_5);
 x_52 = lean::box(0);
}
if (lean::is_scalar(x_52)) {
 x_53 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_53 = x_52;
}
lean::cnstr_set(x_53, 0, x_48);
lean::cnstr_set(x_53, 1, x_50);
return x_53;
}
}
}
obj* l_Lean_IR_EmitCpp_emitLit___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; obj* x_6; 
x_5 = lean::unbox(x_1);
x_6 = l_Lean_IR_EmitCpp_emitLit(x_0, x_5, x_2, x_3, x_4);
lean::dec(x_3);
return x_6;
}
}
obj* l_Lean_IR_EmitCpp_emitVDecl(obj* x_0, uint8 x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
switch (lean::obj_tag(x_2)) {
case 0:
{
obj* x_8; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_2);
x_8 = l_Lean_IR_EmitCpp_emitCtor___rarg(x_4);
return x_8;
}
case 1:
{
obj* x_12; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_2);
x_12 = l_Lean_IR_EmitCpp_emitReset___rarg(x_4);
return x_12;
}
case 2:
{
obj* x_16; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_2);
x_16 = l_Lean_IR_EmitCpp_emitReuse___rarg(x_4);
return x_16;
}
case 3:
{
obj* x_17; obj* x_19; obj* x_22; 
x_17 = lean::cnstr_get(x_2, 0);
lean::inc(x_17);
x_19 = lean::cnstr_get(x_2, 1);
lean::inc(x_19);
lean::dec(x_2);
x_22 = l_Lean_IR_EmitCpp_emitProj(x_0, x_17, x_19, x_3, x_4);
lean::dec(x_3);
return x_22;
}
case 4:
{
obj* x_27; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_2);
x_27 = l_Lean_IR_EmitCpp_emitUProj___rarg(x_4);
return x_27;
}
case 5:
{
obj* x_31; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_2);
x_31 = l_Lean_IR_EmitCpp_emitSProj___rarg(x_4);
return x_31;
}
case 6:
{
obj* x_32; obj* x_34; obj* x_37; 
x_32 = lean::cnstr_get(x_2, 0);
lean::inc(x_32);
x_34 = lean::cnstr_get(x_2, 1);
lean::inc(x_34);
lean::dec(x_2);
x_37 = l_Lean_IR_EmitCpp_emitFullApp(x_0, x_32, x_34, x_3, x_4);
lean::dec(x_34);
return x_37;
}
case 7:
{
obj* x_39; obj* x_41; obj* x_44; 
x_39 = lean::cnstr_get(x_2, 0);
lean::inc(x_39);
x_41 = lean::cnstr_get(x_2, 1);
lean::inc(x_41);
lean::dec(x_2);
x_44 = l_Lean_IR_EmitCpp_emitPartialApp(x_0, x_39, x_41, x_3, x_4);
lean::dec(x_41);
return x_44;
}
case 8:
{
obj* x_49; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_2);
x_49 = l_Lean_IR_EmitCpp_emitApp___rarg(x_4);
return x_49;
}
case 9:
{
uint8 x_50; obj* x_51; obj* x_54; 
x_50 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*1);
x_51 = lean::cnstr_get(x_2, 0);
lean::inc(x_51);
lean::dec(x_2);
x_54 = l_Lean_IR_EmitCpp_emitBox(x_0, x_51, x_50, x_3, x_4);
lean::dec(x_3);
return x_54;
}
case 10:
{
obj* x_56; obj* x_59; 
x_56 = lean::cnstr_get(x_2, 0);
lean::inc(x_56);
lean::dec(x_2);
x_59 = l_Lean_IR_EmitCpp_emitUnbox(x_0, x_1, x_56, x_3, x_4);
lean::dec(x_3);
return x_59;
}
case 11:
{
obj* x_61; obj* x_64; 
x_61 = lean::cnstr_get(x_2, 0);
lean::inc(x_61);
lean::dec(x_2);
x_64 = l_Lean_IR_EmitCpp_emitLit(x_0, x_1, x_61, x_3, x_4);
lean::dec(x_3);
return x_64;
}
case 12:
{
obj* x_66; obj* x_69; 
x_66 = lean::cnstr_get(x_2, 0);
lean::inc(x_66);
lean::dec(x_2);
x_69 = l_Lean_IR_EmitCpp_emitIsShared(x_0, x_66, x_3, x_4);
lean::dec(x_3);
return x_69;
}
default:
{
obj* x_71; obj* x_74; 
x_71 = lean::cnstr_get(x_2, 0);
lean::inc(x_71);
lean::dec(x_2);
x_74 = l_Lean_IR_EmitCpp_emitIsTaggedPtr(x_0, x_71, x_3, x_4);
lean::dec(x_3);
return x_74;
}
}
}
}
obj* l_Lean_IR_EmitCpp_emitVDecl___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; obj* x_6; 
x_5 = lean::unbox(x_1);
x_6 = l_Lean_IR_EmitCpp_emitVDecl(x_0, x_5, x_2, x_3, x_4);
return x_6;
}
}
obj* _init_l_Lean_IR_EmitCpp_emitBlock___main___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("return ");
return x_0;
}
}
obj* _init_l_Lean_IR_EmitCpp_emitBlock___main___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("lean_unreachable();");
return x_0;
}
}
obj* l_Lean_IR_EmitCpp_emitBlock___main(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_4; uint8 x_6; obj* x_7; obj* x_9; obj* x_13; 
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*3);
x_7 = lean::cnstr_get(x_1, 1);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_1, 2);
lean::inc(x_9);
lean::dec(x_1);
lean::inc(x_2);
x_13 = l_Lean_IR_EmitCpp_emitVDecl(x_4, x_6, x_7, x_2, x_3);
if (lean::obj_tag(x_13) == 0)
{
obj* x_14; obj* x_16; obj* x_17; obj* x_18; 
x_14 = lean::cnstr_get(x_13, 1);
if (lean::is_exclusive(x_13)) {
 lean::cnstr_release(x_13, 0);
 x_16 = x_13;
} else {
 lean::inc(x_14);
 lean::dec(x_13);
 x_16 = lean::box(0);
}
x_17 = lean::box(0);
if (lean::is_scalar(x_16)) {
 x_18 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_18 = x_16;
}
lean::cnstr_set(x_18, 0, x_17);
lean::cnstr_set(x_18, 1, x_14);
x_1 = x_9;
x_3 = x_18;
goto _start;
}
else
{
obj* x_23; obj* x_25; obj* x_27; obj* x_28; 
lean::dec(x_9);
lean::dec(x_0);
lean::dec(x_2);
x_23 = lean::cnstr_get(x_13, 0);
x_25 = lean::cnstr_get(x_13, 1);
if (lean::is_exclusive(x_13)) {
 x_27 = x_13;
} else {
 lean::inc(x_23);
 lean::inc(x_25);
 lean::dec(x_13);
 x_27 = lean::box(0);
}
if (lean::is_scalar(x_27)) {
 x_28 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_28 = x_27;
}
lean::cnstr_set(x_28, 0, x_23);
lean::cnstr_set(x_28, 1, x_25);
return x_28;
}
}
case 1:
{
obj* x_29; 
x_29 = lean::cnstr_get(x_1, 3);
lean::inc(x_29);
lean::dec(x_1);
x_1 = x_29;
goto _start;
}
case 2:
{
obj* x_33; obj* x_35; obj* x_37; obj* x_39; obj* x_42; 
x_33 = lean::cnstr_get(x_1, 0);
lean::inc(x_33);
x_35 = lean::cnstr_get(x_1, 1);
lean::inc(x_35);
x_37 = lean::cnstr_get(x_1, 2);
lean::inc(x_37);
x_39 = lean::cnstr_get(x_1, 3);
lean::inc(x_39);
lean::dec(x_1);
x_42 = l_Lean_IR_EmitCpp_emitSet(x_33, x_35, x_37, x_2, x_3);
if (lean::obj_tag(x_42) == 0)
{
obj* x_43; obj* x_45; obj* x_46; obj* x_47; 
x_43 = lean::cnstr_get(x_42, 1);
if (lean::is_exclusive(x_42)) {
 lean::cnstr_release(x_42, 0);
 x_45 = x_42;
} else {
 lean::inc(x_43);
 lean::dec(x_42);
 x_45 = lean::box(0);
}
x_46 = lean::box(0);
if (lean::is_scalar(x_45)) {
 x_47 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_47 = x_45;
}
lean::cnstr_set(x_47, 0, x_46);
lean::cnstr_set(x_47, 1, x_43);
x_1 = x_39;
x_3 = x_47;
goto _start;
}
else
{
obj* x_52; obj* x_54; obj* x_56; obj* x_57; 
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_39);
x_52 = lean::cnstr_get(x_42, 0);
x_54 = lean::cnstr_get(x_42, 1);
if (lean::is_exclusive(x_42)) {
 x_56 = x_42;
} else {
 lean::inc(x_52);
 lean::inc(x_54);
 lean::dec(x_42);
 x_56 = lean::box(0);
}
if (lean::is_scalar(x_56)) {
 x_57 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_57 = x_56;
}
lean::cnstr_set(x_57, 0, x_52);
lean::cnstr_set(x_57, 1, x_54);
return x_57;
}
}
case 3:
{
obj* x_58; obj* x_60; obj* x_62; obj* x_64; obj* x_67; 
x_58 = lean::cnstr_get(x_1, 0);
lean::inc(x_58);
x_60 = lean::cnstr_get(x_1, 1);
lean::inc(x_60);
x_62 = lean::cnstr_get(x_1, 2);
lean::inc(x_62);
x_64 = lean::cnstr_get(x_1, 3);
lean::inc(x_64);
lean::dec(x_1);
x_67 = l_Lean_IR_EmitCpp_emitUSet(x_58, x_60, x_62, x_2, x_3);
if (lean::obj_tag(x_67) == 0)
{
obj* x_68; obj* x_70; obj* x_71; obj* x_72; 
x_68 = lean::cnstr_get(x_67, 1);
if (lean::is_exclusive(x_67)) {
 lean::cnstr_release(x_67, 0);
 x_70 = x_67;
} else {
 lean::inc(x_68);
 lean::dec(x_67);
 x_70 = lean::box(0);
}
x_71 = lean::box(0);
if (lean::is_scalar(x_70)) {
 x_72 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_72 = x_70;
}
lean::cnstr_set(x_72, 0, x_71);
lean::cnstr_set(x_72, 1, x_68);
x_1 = x_64;
x_3 = x_72;
goto _start;
}
else
{
obj* x_77; obj* x_79; obj* x_81; obj* x_82; 
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_64);
x_77 = lean::cnstr_get(x_67, 0);
x_79 = lean::cnstr_get(x_67, 1);
if (lean::is_exclusive(x_67)) {
 x_81 = x_67;
} else {
 lean::inc(x_77);
 lean::inc(x_79);
 lean::dec(x_67);
 x_81 = lean::box(0);
}
if (lean::is_scalar(x_81)) {
 x_82 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_82 = x_81;
}
lean::cnstr_set(x_82, 0, x_77);
lean::cnstr_set(x_82, 1, x_79);
return x_82;
}
}
case 4:
{
obj* x_83; obj* x_85; obj* x_87; obj* x_89; obj* x_91; obj* x_94; 
x_83 = lean::cnstr_get(x_1, 0);
lean::inc(x_83);
x_85 = lean::cnstr_get(x_1, 1);
lean::inc(x_85);
x_87 = lean::cnstr_get(x_1, 2);
lean::inc(x_87);
x_89 = lean::cnstr_get(x_1, 3);
lean::inc(x_89);
x_91 = lean::cnstr_get(x_1, 4);
lean::inc(x_91);
lean::dec(x_1);
x_94 = l_Lean_IR_EmitCpp_emitSSet(x_83, x_85, x_87, x_89, x_2, x_3);
if (lean::obj_tag(x_94) == 0)
{
obj* x_95; obj* x_97; obj* x_98; obj* x_99; 
x_95 = lean::cnstr_get(x_94, 1);
if (lean::is_exclusive(x_94)) {
 lean::cnstr_release(x_94, 0);
 x_97 = x_94;
} else {
 lean::inc(x_95);
 lean::dec(x_94);
 x_97 = lean::box(0);
}
x_98 = lean::box(0);
if (lean::is_scalar(x_97)) {
 x_99 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_99 = x_97;
}
lean::cnstr_set(x_99, 0, x_98);
lean::cnstr_set(x_99, 1, x_95);
x_1 = x_91;
x_3 = x_99;
goto _start;
}
else
{
obj* x_104; obj* x_106; obj* x_108; obj* x_109; 
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_91);
x_104 = lean::cnstr_get(x_94, 0);
x_106 = lean::cnstr_get(x_94, 1);
if (lean::is_exclusive(x_94)) {
 x_108 = x_94;
} else {
 lean::inc(x_104);
 lean::inc(x_106);
 lean::dec(x_94);
 x_108 = lean::box(0);
}
if (lean::is_scalar(x_108)) {
 x_109 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_109 = x_108;
}
lean::cnstr_set(x_109, 0, x_104);
lean::cnstr_set(x_109, 1, x_106);
return x_109;
}
}
case 5:
{
obj* x_110; obj* x_112; obj* x_114; obj* x_117; 
x_110 = lean::cnstr_get(x_1, 0);
lean::inc(x_110);
x_112 = lean::cnstr_get(x_1, 1);
lean::inc(x_112);
x_114 = lean::cnstr_get(x_1, 2);
lean::inc(x_114);
lean::dec(x_1);
x_117 = l_Lean_IR_EmitCpp_emitRelease(x_110, x_112, x_2, x_3);
if (lean::obj_tag(x_117) == 0)
{
obj* x_118; obj* x_120; obj* x_121; obj* x_122; 
x_118 = lean::cnstr_get(x_117, 1);
if (lean::is_exclusive(x_117)) {
 lean::cnstr_release(x_117, 0);
 x_120 = x_117;
} else {
 lean::inc(x_118);
 lean::dec(x_117);
 x_120 = lean::box(0);
}
x_121 = lean::box(0);
if (lean::is_scalar(x_120)) {
 x_122 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_122 = x_120;
}
lean::cnstr_set(x_122, 0, x_121);
lean::cnstr_set(x_122, 1, x_118);
x_1 = x_114;
x_3 = x_122;
goto _start;
}
else
{
obj* x_127; obj* x_129; obj* x_131; obj* x_132; 
lean::dec(x_114);
lean::dec(x_0);
lean::dec(x_2);
x_127 = lean::cnstr_get(x_117, 0);
x_129 = lean::cnstr_get(x_117, 1);
if (lean::is_exclusive(x_117)) {
 x_131 = x_117;
} else {
 lean::inc(x_127);
 lean::inc(x_129);
 lean::dec(x_117);
 x_131 = lean::box(0);
}
if (lean::is_scalar(x_131)) {
 x_132 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_132 = x_131;
}
lean::cnstr_set(x_132, 0, x_127);
lean::cnstr_set(x_132, 1, x_129);
return x_132;
}
}
case 6:
{
obj* x_133; obj* x_135; uint8 x_137; obj* x_138; obj* x_141; 
x_133 = lean::cnstr_get(x_1, 0);
lean::inc(x_133);
x_135 = lean::cnstr_get(x_1, 1);
lean::inc(x_135);
x_137 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*3);
x_138 = lean::cnstr_get(x_1, 2);
lean::inc(x_138);
lean::dec(x_1);
x_141 = l_Lean_IR_EmitCpp_emitInc(x_133, x_135, x_137, x_2, x_3);
if (lean::obj_tag(x_141) == 0)
{
obj* x_142; obj* x_144; obj* x_145; obj* x_146; 
x_142 = lean::cnstr_get(x_141, 1);
if (lean::is_exclusive(x_141)) {
 lean::cnstr_release(x_141, 0);
 x_144 = x_141;
} else {
 lean::inc(x_142);
 lean::dec(x_141);
 x_144 = lean::box(0);
}
x_145 = lean::box(0);
if (lean::is_scalar(x_144)) {
 x_146 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_146 = x_144;
}
lean::cnstr_set(x_146, 0, x_145);
lean::cnstr_set(x_146, 1, x_142);
x_1 = x_138;
x_3 = x_146;
goto _start;
}
else
{
obj* x_151; obj* x_153; obj* x_155; obj* x_156; 
lean::dec(x_138);
lean::dec(x_0);
lean::dec(x_2);
x_151 = lean::cnstr_get(x_141, 0);
x_153 = lean::cnstr_get(x_141, 1);
if (lean::is_exclusive(x_141)) {
 x_155 = x_141;
} else {
 lean::inc(x_151);
 lean::inc(x_153);
 lean::dec(x_141);
 x_155 = lean::box(0);
}
if (lean::is_scalar(x_155)) {
 x_156 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_156 = x_155;
}
lean::cnstr_set(x_156, 0, x_151);
lean::cnstr_set(x_156, 1, x_153);
return x_156;
}
}
case 7:
{
obj* x_157; obj* x_159; uint8 x_161; obj* x_162; obj* x_165; 
x_157 = lean::cnstr_get(x_1, 0);
lean::inc(x_157);
x_159 = lean::cnstr_get(x_1, 1);
lean::inc(x_159);
x_161 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*3);
x_162 = lean::cnstr_get(x_1, 2);
lean::inc(x_162);
lean::dec(x_1);
x_165 = l_Lean_IR_EmitCpp_emitDec(x_157, x_159, x_161, x_2, x_3);
if (lean::obj_tag(x_165) == 0)
{
obj* x_166; obj* x_168; obj* x_169; obj* x_170; 
x_166 = lean::cnstr_get(x_165, 1);
if (lean::is_exclusive(x_165)) {
 lean::cnstr_release(x_165, 0);
 x_168 = x_165;
} else {
 lean::inc(x_166);
 lean::dec(x_165);
 x_168 = lean::box(0);
}
x_169 = lean::box(0);
if (lean::is_scalar(x_168)) {
 x_170 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_170 = x_168;
}
lean::cnstr_set(x_170, 0, x_169);
lean::cnstr_set(x_170, 1, x_166);
x_1 = x_162;
x_3 = x_170;
goto _start;
}
else
{
obj* x_175; obj* x_177; obj* x_179; obj* x_180; 
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_162);
x_175 = lean::cnstr_get(x_165, 0);
x_177 = lean::cnstr_get(x_165, 1);
if (lean::is_exclusive(x_165)) {
 x_179 = x_165;
} else {
 lean::inc(x_175);
 lean::inc(x_177);
 lean::dec(x_165);
 x_179 = lean::box(0);
}
if (lean::is_scalar(x_179)) {
 x_180 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_180 = x_179;
}
lean::cnstr_set(x_180, 0, x_175);
lean::cnstr_set(x_180, 1, x_177);
return x_180;
}
}
case 8:
{
obj* x_181; 
x_181 = lean::cnstr_get(x_1, 1);
lean::inc(x_181);
lean::dec(x_1);
x_1 = x_181;
goto _start;
}
case 9:
{
obj* x_185; obj* x_187; obj* x_190; 
x_185 = lean::cnstr_get(x_1, 1);
lean::inc(x_185);
x_187 = lean::cnstr_get(x_1, 2);
lean::inc(x_187);
lean::dec(x_1);
x_190 = l_Lean_IR_EmitCpp_emitCase(x_0, x_185, x_187, x_2, x_3);
lean::dec(x_187);
return x_190;
}
case 10:
{
obj* x_193; obj* x_196; obj* x_198; obj* x_199; obj* x_200; obj* x_201; obj* x_202; obj* x_203; 
lean::dec(x_0);
x_193 = lean::cnstr_get(x_1, 0);
lean::inc(x_193);
lean::dec(x_1);
x_196 = lean::cnstr_get(x_3, 1);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 x_198 = x_3;
} else {
 lean::inc(x_196);
 lean::dec(x_3);
 x_198 = lean::box(0);
}
x_199 = l_Lean_IR_EmitCpp_emitBlock___main___closed__1;
x_200 = lean::string_append(x_196, x_199);
x_201 = lean::box(0);
if (lean::is_scalar(x_198)) {
 x_202 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_202 = x_198;
}
lean::cnstr_set(x_202, 0, x_201);
lean::cnstr_set(x_202, 1, x_200);
x_203 = l_Lean_IR_EmitCpp_emitArg(x_193, x_2, x_202);
lean::dec(x_2);
if (lean::obj_tag(x_203) == 0)
{
obj* x_205; obj* x_207; obj* x_208; obj* x_209; obj* x_210; obj* x_211; obj* x_212; 
x_205 = lean::cnstr_get(x_203, 1);
if (lean::is_exclusive(x_203)) {
 lean::cnstr_release(x_203, 0);
 x_207 = x_203;
} else {
 lean::inc(x_205);
 lean::dec(x_203);
 x_207 = lean::box(0);
}
x_208 = l_Lean_IR_EmitCpp_emitFnDeclAux___closed__2;
x_209 = lean::string_append(x_205, x_208);
x_210 = l_IO_println___rarg___closed__1;
x_211 = lean::string_append(x_209, x_210);
if (lean::is_scalar(x_207)) {
 x_212 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_212 = x_207;
}
lean::cnstr_set(x_212, 0, x_201);
lean::cnstr_set(x_212, 1, x_211);
return x_212;
}
else
{
obj* x_213; obj* x_215; obj* x_217; obj* x_218; 
x_213 = lean::cnstr_get(x_203, 0);
x_215 = lean::cnstr_get(x_203, 1);
if (lean::is_exclusive(x_203)) {
 x_217 = x_203;
} else {
 lean::inc(x_213);
 lean::inc(x_215);
 lean::dec(x_203);
 x_217 = lean::box(0);
}
if (lean::is_scalar(x_217)) {
 x_218 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_218 = x_217;
}
lean::cnstr_set(x_218, 0, x_213);
lean::cnstr_set(x_218, 1, x_215);
return x_218;
}
}
case 11:
{
obj* x_220; obj* x_222; obj* x_225; 
lean::dec(x_0);
x_220 = lean::cnstr_get(x_1, 0);
lean::inc(x_220);
x_222 = lean::cnstr_get(x_1, 1);
lean::inc(x_222);
lean::dec(x_1);
x_225 = l_Lean_IR_EmitCpp_emitJmp(x_220, x_222, x_2, x_3);
lean::dec(x_2);
lean::dec(x_222);
return x_225;
}
default:
{
obj* x_230; obj* x_232; obj* x_233; obj* x_234; obj* x_235; obj* x_236; obj* x_237; obj* x_238; 
lean::dec(x_0);
lean::dec(x_2);
x_230 = lean::cnstr_get(x_3, 1);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 x_232 = x_3;
} else {
 lean::inc(x_230);
 lean::dec(x_3);
 x_232 = lean::box(0);
}
x_233 = l_Lean_IR_EmitCpp_emitBlock___main___closed__2;
x_234 = lean::string_append(x_230, x_233);
x_235 = l_IO_println___rarg___closed__1;
x_236 = lean::string_append(x_234, x_235);
x_237 = lean::box(0);
if (lean::is_scalar(x_232)) {
 x_238 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_238 = x_232;
}
lean::cnstr_set(x_238, 0, x_237);
lean::cnstr_set(x_238, 1, x_236);
return x_238;
}
}
}
}
obj* l_Lean_IR_EmitCpp_emitBlock(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_IR_EmitCpp_emitBlock___main(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_Lean_IR_EmitCpp_emitJPs___main(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
switch (lean::obj_tag(x_1)) {
case 1:
{
obj* x_6; obj* x_8; obj* x_10; obj* x_13; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_20; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_30; 
x_6 = lean::cnstr_get(x_1, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_1, 2);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_1, 3);
lean::inc(x_10);
lean::dec(x_1);
x_13 = lean::cnstr_get(x_3, 1);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 x_15 = x_3;
} else {
 lean::inc(x_13);
 lean::dec(x_3);
 x_15 = lean::box(0);
}
x_16 = l_Nat_repr(x_6);
x_17 = l_Lean_IR_JoinPointId_HasToString___closed__1;
x_18 = lean::string_append(x_17, x_16);
lean::dec(x_16);
x_20 = lean::string_append(x_13, x_18);
lean::dec(x_18);
x_22 = l_Array_mforAux___main___at_Lean_IR_EmitCpp_emitCase___spec__1___closed__2;
x_23 = lean::string_append(x_20, x_22);
x_24 = l_IO_println___rarg___closed__1;
x_25 = lean::string_append(x_23, x_24);
x_26 = lean::box(0);
if (lean::is_scalar(x_15)) {
 x_27 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_27 = x_15;
}
lean::cnstr_set(x_27, 0, x_26);
lean::cnstr_set(x_27, 1, x_25);
lean::inc(x_2);
lean::inc(x_0);
x_30 = lean::apply_3(x_0, x_8, x_2, x_27);
if (lean::obj_tag(x_30) == 0)
{
obj* x_31; obj* x_33; obj* x_34; 
x_31 = lean::cnstr_get(x_30, 1);
if (lean::is_exclusive(x_30)) {
 lean::cnstr_release(x_30, 0);
 x_33 = x_30;
} else {
 lean::inc(x_31);
 lean::dec(x_30);
 x_33 = lean::box(0);
}
if (lean::is_scalar(x_33)) {
 x_34 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_34 = x_33;
}
lean::cnstr_set(x_34, 0, x_26);
lean::cnstr_set(x_34, 1, x_31);
x_1 = x_10;
x_3 = x_34;
goto _start;
}
else
{
obj* x_39; obj* x_41; obj* x_43; obj* x_44; 
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_10);
x_39 = lean::cnstr_get(x_30, 0);
x_41 = lean::cnstr_get(x_30, 1);
if (lean::is_exclusive(x_30)) {
 x_43 = x_30;
} else {
 lean::inc(x_39);
 lean::inc(x_41);
 lean::dec(x_30);
 x_43 = lean::box(0);
}
if (lean::is_scalar(x_43)) {
 x_44 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_44 = x_43;
}
lean::cnstr_set(x_44, 0, x_39);
lean::cnstr_set(x_44, 1, x_41);
return x_44;
}
}
default:
{
obj* x_45; 
x_45 = lean::box(0);
x_4 = x_45;
goto lbl_5;
}
}
lbl_5:
{
uint8 x_47; 
lean::dec(x_4);
x_47 = l_Lean_IR_FnBody_isTerminal___main(x_1);
if (x_47 == 0)
{
obj* x_48; 
x_48 = l_Lean_IR_FnBody_body___main(x_1);
lean::dec(x_1);
x_1 = x_48;
goto _start;
}
else
{
obj* x_54; obj* x_56; obj* x_57; obj* x_58; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_54 = lean::cnstr_get(x_3, 1);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 x_56 = x_3;
} else {
 lean::inc(x_54);
 lean::dec(x_3);
 x_56 = lean::box(0);
}
x_57 = lean::box(0);
if (lean::is_scalar(x_56)) {
 x_58 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_58 = x_56;
}
lean::cnstr_set(x_58, 0, x_57);
lean::cnstr_set(x_58, 1, x_54);
return x_58;
}
}
}
}
obj* l_Lean_IR_EmitCpp_emitJPs(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_IR_EmitCpp_emitJPs___main(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* _init_l_Lean_IR_EmitCpp_emitFnBody___main___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("{");
return x_0;
}
}
obj* _init_l_Lean_IR_EmitCpp_emitFnBody___main___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_IR_EmitCpp_emitFnBody___main), 3, 0);
return x_0;
}
}
obj* l_Lean_IR_EmitCpp_emitFnBody___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; uint8 x_12; obj* x_14; 
x_3 = lean::cnstr_get(x_2, 1);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_release(x_2, 0);
 x_5 = x_2;
} else {
 lean::inc(x_3);
 lean::dec(x_2);
 x_5 = lean::box(0);
}
x_6 = l_Lean_IR_EmitCpp_emitFnBody___main___closed__1;
x_7 = lean::string_append(x_3, x_6);
x_8 = l_IO_println___rarg___closed__1;
x_9 = lean::string_append(x_7, x_8);
x_10 = lean::box(0);
if (lean::is_scalar(x_5)) {
 x_11 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_11 = x_5;
}
lean::cnstr_set(x_11, 0, x_10);
lean::cnstr_set(x_11, 1, x_9);
x_12 = 0;
lean::inc(x_0);
x_14 = l_Lean_IR_EmitCpp_declareVars___main(x_0, x_12, x_1, x_11);
if (lean::obj_tag(x_14) == 0)
{
obj* x_15; uint8 x_17; 
x_15 = lean::cnstr_get(x_14, 0);
lean::inc(x_15);
x_17 = lean::unbox(x_15);
if (x_17 == 0)
{
obj* x_18; obj* x_20; obj* x_21; obj* x_22; obj* x_25; 
x_18 = lean::cnstr_get(x_14, 1);
if (lean::is_exclusive(x_14)) {
 lean::cnstr_release(x_14, 0);
 x_20 = x_14;
} else {
 lean::inc(x_18);
 lean::dec(x_14);
 x_20 = lean::box(0);
}
if (lean::is_scalar(x_20)) {
 x_21 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_21 = x_20;
}
lean::cnstr_set(x_21, 0, x_10);
lean::cnstr_set(x_21, 1, x_18);
x_22 = l_Lean_IR_EmitCpp_emitFnBody___main___closed__2;
lean::inc(x_1);
lean::inc(x_0);
x_25 = l_Lean_IR_EmitCpp_emitBlock___main(x_22, x_0, x_1, x_21);
if (lean::obj_tag(x_25) == 0)
{
obj* x_26; obj* x_28; obj* x_29; obj* x_30; 
x_26 = lean::cnstr_get(x_25, 1);
if (lean::is_exclusive(x_25)) {
 lean::cnstr_release(x_25, 0);
 x_28 = x_25;
} else {
 lean::inc(x_26);
 lean::dec(x_25);
 x_28 = lean::box(0);
}
if (lean::is_scalar(x_28)) {
 x_29 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_29 = x_28;
}
lean::cnstr_set(x_29, 0, x_10);
lean::cnstr_set(x_29, 1, x_26);
x_30 = l_Lean_IR_EmitCpp_emitJPs___main(x_22, x_0, x_1, x_29);
if (lean::obj_tag(x_30) == 0)
{
obj* x_31; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; 
x_31 = lean::cnstr_get(x_30, 1);
if (lean::is_exclusive(x_30)) {
 lean::cnstr_release(x_30, 0);
 x_33 = x_30;
} else {
 lean::inc(x_31);
 lean::dec(x_30);
 x_33 = lean::box(0);
}
x_34 = l_Lean_IR_EmitCpp_closeNamespacesAux___main___closed__1;
x_35 = lean::string_append(x_31, x_34);
x_36 = lean::string_append(x_35, x_8);
if (lean::is_scalar(x_33)) {
 x_37 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_37 = x_33;
}
lean::cnstr_set(x_37, 0, x_10);
lean::cnstr_set(x_37, 1, x_36);
return x_37;
}
else
{
obj* x_38; obj* x_40; obj* x_42; obj* x_43; 
x_38 = lean::cnstr_get(x_30, 0);
x_40 = lean::cnstr_get(x_30, 1);
if (lean::is_exclusive(x_30)) {
 x_42 = x_30;
} else {
 lean::inc(x_38);
 lean::inc(x_40);
 lean::dec(x_30);
 x_42 = lean::box(0);
}
if (lean::is_scalar(x_42)) {
 x_43 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_43 = x_42;
}
lean::cnstr_set(x_43, 0, x_38);
lean::cnstr_set(x_43, 1, x_40);
return x_43;
}
}
else
{
obj* x_46; obj* x_48; obj* x_50; obj* x_51; 
lean::dec(x_1);
lean::dec(x_0);
x_46 = lean::cnstr_get(x_25, 0);
x_48 = lean::cnstr_get(x_25, 1);
if (lean::is_exclusive(x_25)) {
 x_50 = x_25;
} else {
 lean::inc(x_46);
 lean::inc(x_48);
 lean::dec(x_25);
 x_50 = lean::box(0);
}
if (lean::is_scalar(x_50)) {
 x_51 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_51 = x_50;
}
lean::cnstr_set(x_51, 0, x_46);
lean::cnstr_set(x_51, 1, x_48);
return x_51;
}
}
else
{
obj* x_52; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_62; 
x_52 = lean::cnstr_get(x_14, 1);
if (lean::is_exclusive(x_14)) {
 lean::cnstr_release(x_14, 0);
 x_54 = x_14;
} else {
 lean::inc(x_52);
 lean::dec(x_14);
 x_54 = lean::box(0);
}
x_55 = l_String_splitAux___main___closed__1;
x_56 = lean::string_append(x_52, x_55);
x_57 = lean::string_append(x_56, x_8);
if (lean::is_scalar(x_54)) {
 x_58 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_58 = x_54;
}
lean::cnstr_set(x_58, 0, x_10);
lean::cnstr_set(x_58, 1, x_57);
x_59 = l_Lean_IR_EmitCpp_emitFnBody___main___closed__2;
lean::inc(x_1);
lean::inc(x_0);
x_62 = l_Lean_IR_EmitCpp_emitBlock___main(x_59, x_0, x_1, x_58);
if (lean::obj_tag(x_62) == 0)
{
obj* x_63; obj* x_65; obj* x_66; obj* x_67; 
x_63 = lean::cnstr_get(x_62, 1);
if (lean::is_exclusive(x_62)) {
 lean::cnstr_release(x_62, 0);
 x_65 = x_62;
} else {
 lean::inc(x_63);
 lean::dec(x_62);
 x_65 = lean::box(0);
}
if (lean::is_scalar(x_65)) {
 x_66 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_66 = x_65;
}
lean::cnstr_set(x_66, 0, x_10);
lean::cnstr_set(x_66, 1, x_63);
x_67 = l_Lean_IR_EmitCpp_emitJPs___main(x_59, x_0, x_1, x_66);
if (lean::obj_tag(x_67) == 0)
{
obj* x_68; obj* x_70; obj* x_71; obj* x_72; obj* x_73; obj* x_74; 
x_68 = lean::cnstr_get(x_67, 1);
if (lean::is_exclusive(x_67)) {
 lean::cnstr_release(x_67, 0);
 x_70 = x_67;
} else {
 lean::inc(x_68);
 lean::dec(x_67);
 x_70 = lean::box(0);
}
x_71 = l_Lean_IR_EmitCpp_closeNamespacesAux___main___closed__1;
x_72 = lean::string_append(x_68, x_71);
x_73 = lean::string_append(x_72, x_8);
if (lean::is_scalar(x_70)) {
 x_74 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_74 = x_70;
}
lean::cnstr_set(x_74, 0, x_10);
lean::cnstr_set(x_74, 1, x_73);
return x_74;
}
else
{
obj* x_75; obj* x_77; obj* x_79; obj* x_80; 
x_75 = lean::cnstr_get(x_67, 0);
x_77 = lean::cnstr_get(x_67, 1);
if (lean::is_exclusive(x_67)) {
 x_79 = x_67;
} else {
 lean::inc(x_75);
 lean::inc(x_77);
 lean::dec(x_67);
 x_79 = lean::box(0);
}
if (lean::is_scalar(x_79)) {
 x_80 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_80 = x_79;
}
lean::cnstr_set(x_80, 0, x_75);
lean::cnstr_set(x_80, 1, x_77);
return x_80;
}
}
else
{
obj* x_83; obj* x_85; obj* x_87; obj* x_88; 
lean::dec(x_1);
lean::dec(x_0);
x_83 = lean::cnstr_get(x_62, 0);
x_85 = lean::cnstr_get(x_62, 1);
if (lean::is_exclusive(x_62)) {
 x_87 = x_62;
} else {
 lean::inc(x_83);
 lean::inc(x_85);
 lean::dec(x_62);
 x_87 = lean::box(0);
}
if (lean::is_scalar(x_87)) {
 x_88 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_88 = x_87;
}
lean::cnstr_set(x_88, 0, x_83);
lean::cnstr_set(x_88, 1, x_85);
return x_88;
}
}
}
else
{
obj* x_91; obj* x_93; obj* x_95; obj* x_96; 
lean::dec(x_1);
lean::dec(x_0);
x_91 = lean::cnstr_get(x_14, 0);
x_93 = lean::cnstr_get(x_14, 1);
if (lean::is_exclusive(x_14)) {
 x_95 = x_14;
} else {
 lean::inc(x_91);
 lean::inc(x_93);
 lean::dec(x_14);
 x_95 = lean::box(0);
}
if (lean::is_scalar(x_95)) {
 x_96 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_96 = x_95;
}
lean::cnstr_set(x_96, 0, x_91);
lean::cnstr_set(x_96, 1, x_93);
return x_96;
}
}
}
obj* l_Lean_IR_EmitCpp_emitFnBody(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_EmitCpp_emitFnBody___main(x_0, x_1, x_2);
return x_3;
}
}
obj* l_Nat_mforAux___main___at_Lean_IR_EmitCpp_emitDeclAux___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean::mk_nat_obj(0ul);
x_6 = lean::nat_dec_eq(x_2, x_5);
if (x_6 == 0)
{
obj* x_7; obj* x_8; obj* x_10; obj* x_11; obj* x_13; uint8 x_15; 
x_7 = lean::mk_nat_obj(1ul);
x_8 = lean::nat_sub(x_2, x_7);
lean::dec(x_2);
x_10 = lean::nat_sub(x_1, x_8);
x_11 = lean::nat_sub(x_10, x_7);
lean::dec(x_10);
x_15 = lean::nat_dec_lt(x_5, x_11);
if (x_15 == 0)
{
obj* x_16; 
x_16 = lean::cnstr_get(x_4, 1);
lean::inc(x_16);
lean::dec(x_4);
x_13 = x_16;
goto lbl_14;
}
else
{
obj* x_19; obj* x_22; obj* x_23; 
x_19 = lean::cnstr_get(x_4, 1);
lean::inc(x_19);
lean::dec(x_4);
x_22 = l_List_reprAux___main___rarg___closed__1;
x_23 = lean::string_append(x_19, x_22);
x_13 = x_23;
goto lbl_14;
}
lbl_14:
{
obj* x_24; obj* x_25; uint8 x_27; obj* x_28; obj* x_29; obj* x_31; obj* x_32; obj* x_33; obj* x_36; obj* x_37; obj* x_38; obj* x_40; obj* x_42; obj* x_43; 
x_24 = l_Lean_IR_paramInh;
x_25 = lean::array_get(x_24, x_0, x_11);
lean::dec(x_11);
x_27 = lean::cnstr_get_scalar<uint8>(x_25, sizeof(void*)*1 + 1);
x_28 = l_Lean_IR_EmitCpp_toCppType___main(x_27);
x_29 = lean::string_append(x_13, x_28);
lean::dec(x_28);
x_31 = l_Lean_IR_EmitCpp_emitFnDeclAux___closed__1;
x_32 = lean::string_append(x_29, x_31);
x_33 = lean::cnstr_get(x_25, 0);
lean::inc(x_33);
lean::dec(x_25);
x_36 = l_Nat_repr(x_33);
x_37 = l_Lean_IR_VarId_HasToString___closed__1;
x_38 = lean::string_append(x_37, x_36);
lean::dec(x_36);
x_40 = lean::string_append(x_32, x_38);
lean::dec(x_38);
x_42 = lean::box(0);
x_43 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_43, 0, x_42);
lean::cnstr_set(x_43, 1, x_40);
x_2 = x_8;
x_4 = x_43;
goto _start;
}
}
else
{
obj* x_46; obj* x_48; obj* x_49; obj* x_50; 
lean::dec(x_2);
x_46 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 x_48 = x_4;
} else {
 lean::inc(x_46);
 lean::dec(x_4);
 x_48 = lean::box(0);
}
x_49 = lean::box(0);
if (lean::is_scalar(x_48)) {
 x_50 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_50 = x_48;
}
lean::cnstr_set(x_50, 0, x_49);
lean::cnstr_set(x_50, 1, x_46);
return x_50;
}
}
}
obj* _init_l_Lean_IR_EmitCpp_emitDeclAux___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("_start:");
return x_0;
}
}
obj* l_Lean_IR_EmitCpp_emitDeclAux(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; 
lean::inc(x_1);
x_4 = l_Lean_IR_EmitCpp_getEnv(x_1, x_2);
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; obj* x_7; obj* x_9; obj* x_10; obj* x_12; obj* x_14; obj* x_15; obj* x_17; obj* x_20; uint8 x_21; uint8 x_24; 
x_5 = lean::cnstr_get(x_4, 0);
x_7 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 x_9 = x_4;
} else {
 lean::inc(x_5);
 lean::inc(x_7);
 lean::dec(x_4);
 x_9 = lean::box(0);
}
x_10 = lean::box(0);
lean::inc(x_7);
if (lean::is_scalar(x_9)) {
 x_12 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_12 = x_9;
}
lean::cnstr_set(x_12, 0, x_10);
lean::cnstr_set(x_12, 1, x_7);
lean::inc(x_0);
x_14 = l_Lean_IR_mkVarJPMaps(x_0);
x_15 = lean::cnstr_get(x_14, 0);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_14, 1);
lean::inc(x_17);
lean::dec(x_14);
x_20 = l_Lean_IR_Decl_name___main(x_0);
x_21 = l_Lean_hasInitAttr(x_5, x_20);
lean::dec(x_20);
lean::dec(x_5);
if (x_21 == 0)
{
uint8 x_26; 
x_26 = 0;
x_24 = x_26;
goto lbl_25;
}
else
{
uint8 x_27; 
x_27 = 1;
x_24 = x_27;
goto lbl_25;
}
lbl_25:
{
if (x_24 == 0)
{
if (lean::obj_tag(x_0) == 0)
{
uint8 x_29; obj* x_30; obj* x_32; obj* x_34; obj* x_37; obj* x_39; obj* x_41; obj* x_43; obj* x_45; obj* x_50; obj* x_52; 
lean::dec(x_7);
x_29 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*3);
x_30 = lean::cnstr_get(x_0, 0);
lean::inc(x_30);
x_32 = lean::cnstr_get(x_0, 1);
lean::inc(x_32);
x_34 = lean::cnstr_get(x_0, 2);
lean::inc(x_34);
lean::dec(x_0);
x_37 = lean::cnstr_get(x_1, 0);
x_39 = lean::cnstr_get(x_1, 1);
x_41 = lean::cnstr_get(x_1, 4);
x_43 = lean::cnstr_get(x_1, 5);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 2);
 lean::cnstr_release(x_1, 3);
 x_45 = x_1;
} else {
 lean::inc(x_37);
 lean::inc(x_39);
 lean::inc(x_41);
 lean::inc(x_43);
 lean::dec(x_1);
 x_45 = lean::box(0);
}
lean::inc(x_17);
lean::inc(x_15);
lean::inc(x_39);
lean::inc(x_37);
if (lean::is_scalar(x_45)) {
 x_50 = lean::alloc_cnstr(0, 6, 0);
} else {
 x_50 = x_45;
}
lean::cnstr_set(x_50, 0, x_37);
lean::cnstr_set(x_50, 1, x_39);
lean::cnstr_set(x_50, 2, x_15);
lean::cnstr_set(x_50, 3, x_17);
lean::cnstr_set(x_50, 4, x_41);
lean::cnstr_set(x_50, 5, x_43);
lean::inc(x_50);
x_52 = l_Lean_IR_EmitCpp_openNamespacesFor(x_30, x_50, x_12);
if (lean::obj_tag(x_52) == 0)
{
obj* x_53; obj* x_55; obj* x_56; obj* x_57; obj* x_61; 
x_53 = lean::cnstr_get(x_52, 1);
if (lean::is_exclusive(x_52)) {
 lean::cnstr_release(x_52, 0);
 x_55 = x_52;
} else {
 lean::inc(x_53);
 lean::dec(x_52);
 x_55 = lean::box(0);
}
if (lean::is_scalar(x_55)) {
 x_56 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_56 = x_55;
}
lean::cnstr_set(x_56, 0, x_10);
lean::cnstr_set(x_56, 1, x_53);
lean::inc(x_50);
lean::inc(x_30);
x_61 = l_Lean_IR_EmitCpp_toBaseCppName(x_30, x_50, x_56);
if (lean::obj_tag(x_61) == 0)
{
obj* x_62; obj* x_64; obj* x_66; obj* x_67; obj* x_68; obj* x_70; obj* x_71; obj* x_72; obj* x_73; uint8 x_74; 
x_62 = lean::cnstr_get(x_61, 0);
x_64 = lean::cnstr_get(x_61, 1);
if (lean::is_exclusive(x_61)) {
 lean::cnstr_set(x_61, 0, lean::box(0));
 lean::cnstr_set(x_61, 1, lean::box(0));
 x_66 = x_61;
} else {
 lean::inc(x_62);
 lean::inc(x_64);
 lean::dec(x_61);
 x_66 = lean::box(0);
}
x_67 = l_Lean_IR_EmitCpp_toCppType___main(x_29);
x_68 = lean::string_append(x_64, x_67);
lean::dec(x_67);
x_70 = l_Lean_IR_EmitCpp_emitFnDeclAux___closed__1;
x_71 = lean::string_append(x_68, x_70);
x_72 = lean::array_get_size(x_32);
x_73 = lean::mk_nat_obj(0ul);
x_74 = lean::nat_dec_lt(x_73, x_72);
if (x_74 == 0)
{
obj* x_77; obj* x_78; obj* x_80; obj* x_81; obj* x_82; 
lean::dec(x_66);
lean::dec(x_72);
x_77 = l_Lean_IR_EmitCpp_toCppInitName___closed__1;
x_78 = lean::string_append(x_77, x_62);
lean::dec(x_62);
x_80 = l_Unit_HasRepr___closed__1;
x_81 = lean::string_append(x_78, x_80);
x_82 = lean::string_append(x_71, x_81);
lean::dec(x_81);
x_57 = x_82;
goto lbl_58;
}
else
{
obj* x_84; obj* x_86; obj* x_87; obj* x_88; obj* x_90; 
x_84 = lean::string_append(x_71, x_62);
lean::dec(x_62);
x_86 = l_Prod_HasRepr___rarg___closed__1;
x_87 = lean::string_append(x_84, x_86);
if (lean::is_scalar(x_66)) {
 x_88 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_88 = x_66;
}
lean::cnstr_set(x_88, 0, x_10);
lean::cnstr_set(x_88, 1, x_87);
lean::inc(x_72);
x_90 = l_Nat_mforAux___main___at_Lean_IR_EmitCpp_emitDeclAux___spec__1(x_32, x_72, x_72, x_50, x_88);
lean::dec(x_72);
if (lean::obj_tag(x_90) == 0)
{
obj* x_92; obj* x_95; obj* x_96; 
x_92 = lean::cnstr_get(x_90, 1);
lean::inc(x_92);
lean::dec(x_90);
x_95 = l_Option_HasRepr___rarg___closed__3;
x_96 = lean::string_append(x_92, x_95);
x_57 = x_96;
goto lbl_58;
}
else
{
obj* x_105; obj* x_107; obj* x_109; obj* x_110; 
lean::dec(x_15);
lean::dec(x_30);
lean::dec(x_32);
lean::dec(x_17);
lean::dec(x_34);
lean::dec(x_50);
lean::dec(x_37);
lean::dec(x_39);
x_105 = lean::cnstr_get(x_90, 0);
x_107 = lean::cnstr_get(x_90, 1);
if (lean::is_exclusive(x_90)) {
 x_109 = x_90;
} else {
 lean::inc(x_105);
 lean::inc(x_107);
 lean::dec(x_90);
 x_109 = lean::box(0);
}
if (lean::is_scalar(x_109)) {
 x_110 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_110 = x_109;
}
lean::cnstr_set(x_110, 0, x_105);
lean::cnstr_set(x_110, 1, x_107);
return x_110;
}
}
}
else
{
obj* x_119; obj* x_121; obj* x_123; obj* x_124; 
lean::dec(x_15);
lean::dec(x_30);
lean::dec(x_32);
lean::dec(x_17);
lean::dec(x_34);
lean::dec(x_50);
lean::dec(x_37);
lean::dec(x_39);
x_119 = lean::cnstr_get(x_61, 0);
x_121 = lean::cnstr_get(x_61, 1);
if (lean::is_exclusive(x_61)) {
 x_123 = x_61;
} else {
 lean::inc(x_119);
 lean::inc(x_121);
 lean::dec(x_61);
 x_123 = lean::box(0);
}
if (lean::is_scalar(x_123)) {
 x_124 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_124 = x_123;
}
lean::cnstr_set(x_124, 0, x_119);
lean::cnstr_set(x_124, 1, x_121);
return x_124;
}
lbl_58:
{
obj* x_125; obj* x_126; obj* x_127; obj* x_128; obj* x_129; obj* x_130; obj* x_131; obj* x_132; obj* x_134; obj* x_135; 
x_125 = l_Lean_IR_EmitCpp_openNamespacesAux___main___closed__2;
x_126 = lean::string_append(x_57, x_125);
x_127 = l_IO_println___rarg___closed__1;
x_128 = lean::string_append(x_126, x_127);
x_129 = l_Lean_IR_EmitCpp_emitDeclAux___closed__1;
x_130 = lean::string_append(x_128, x_129);
x_131 = lean::string_append(x_130, x_127);
x_132 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_132, 0, x_10);
lean::cnstr_set(x_132, 1, x_131);
lean::inc(x_30);
x_134 = lean::alloc_cnstr(0, 6, 0);
lean::cnstr_set(x_134, 0, x_37);
lean::cnstr_set(x_134, 1, x_39);
lean::cnstr_set(x_134, 2, x_15);
lean::cnstr_set(x_134, 3, x_17);
lean::cnstr_set(x_134, 4, x_30);
lean::cnstr_set(x_134, 5, x_32);
x_135 = l_Lean_IR_EmitCpp_emitFnBody___main(x_34, x_134, x_132);
if (lean::obj_tag(x_135) == 0)
{
obj* x_136; obj* x_138; obj* x_139; obj* x_140; obj* x_141; obj* x_142; obj* x_143; 
x_136 = lean::cnstr_get(x_135, 1);
if (lean::is_exclusive(x_135)) {
 lean::cnstr_release(x_135, 0);
 x_138 = x_135;
} else {
 lean::inc(x_136);
 lean::dec(x_135);
 x_138 = lean::box(0);
}
x_139 = l_Lean_IR_EmitCpp_closeNamespacesAux___main___closed__1;
x_140 = lean::string_append(x_136, x_139);
x_141 = lean::string_append(x_140, x_127);
if (lean::is_scalar(x_138)) {
 x_142 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_142 = x_138;
}
lean::cnstr_set(x_142, 0, x_10);
lean::cnstr_set(x_142, 1, x_141);
x_143 = l_Lean_IR_EmitCpp_closeNamespacesFor(x_30, x_50, x_142);
lean::dec(x_30);
return x_143;
}
else
{
obj* x_147; obj* x_149; obj* x_151; obj* x_152; 
lean::dec(x_30);
lean::dec(x_50);
x_147 = lean::cnstr_get(x_135, 0);
x_149 = lean::cnstr_get(x_135, 1);
if (lean::is_exclusive(x_135)) {
 x_151 = x_135;
} else {
 lean::inc(x_147);
 lean::inc(x_149);
 lean::dec(x_135);
 x_151 = lean::box(0);
}
if (lean::is_scalar(x_151)) {
 x_152 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_152 = x_151;
}
lean::cnstr_set(x_152, 0, x_147);
lean::cnstr_set(x_152, 1, x_149);
return x_152;
}
}
}
else
{
obj* x_161; obj* x_163; obj* x_165; obj* x_166; 
lean::dec(x_15);
lean::dec(x_30);
lean::dec(x_32);
lean::dec(x_17);
lean::dec(x_34);
lean::dec(x_50);
lean::dec(x_37);
lean::dec(x_39);
x_161 = lean::cnstr_get(x_52, 0);
x_163 = lean::cnstr_get(x_52, 1);
if (lean::is_exclusive(x_52)) {
 x_165 = x_52;
} else {
 lean::inc(x_161);
 lean::inc(x_163);
 lean::dec(x_52);
 x_165 = lean::box(0);
}
if (lean::is_scalar(x_165)) {
 x_166 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_166 = x_165;
}
lean::cnstr_set(x_166, 0, x_161);
lean::cnstr_set(x_166, 1, x_163);
return x_166;
}
}
else
{
obj* x_172; 
lean::dec(x_15);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_12);
lean::dec(x_17);
x_172 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_172, 0, x_10);
lean::cnstr_set(x_172, 1, x_7);
return x_172;
}
}
else
{
obj* x_178; 
lean::dec(x_15);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_12);
lean::dec(x_17);
x_178 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_178, 0, x_10);
lean::cnstr_set(x_178, 1, x_7);
return x_178;
}
}
}
else
{
obj* x_181; obj* x_183; obj* x_185; obj* x_186; 
lean::dec(x_1);
lean::dec(x_0);
x_181 = lean::cnstr_get(x_4, 0);
x_183 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 x_185 = x_4;
} else {
 lean::inc(x_181);
 lean::inc(x_183);
 lean::dec(x_4);
 x_185 = lean::box(0);
}
if (lean::is_scalar(x_185)) {
 x_186 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_186 = x_185;
}
lean::cnstr_set(x_186, 0, x_181);
lean::cnstr_set(x_186, 1, x_183);
return x_186;
}
}
}
obj* l_Nat_mforAux___main___at_Lean_IR_EmitCpp_emitDeclAux___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Nat_mforAux___main___at_Lean_IR_EmitCpp_emitDeclAux___spec__1(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_3);
return x_5;
}
}
obj* _init_l_Lean_IR_EmitCpp_emitDecl___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("\ncompiling:\n");
return x_0;
}
}
obj* l_Lean_IR_EmitCpp_emitDecl(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; 
x_3 = l_Lean_IR_Decl_normalizeIds(x_0);
lean::inc(x_3);
x_5 = l_Lean_IR_EmitCpp_emitDeclAux(x_3, x_1, x_2);
if (lean::obj_tag(x_5) == 0)
{
lean::dec(x_3);
return x_5;
}
else
{
obj* x_7; obj* x_9; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_17; 
x_7 = lean::cnstr_get(x_5, 0);
x_9 = lean::cnstr_get(x_5, 1);
if (lean::is_exclusive(x_5)) {
 x_11 = x_5;
} else {
 lean::inc(x_7);
 lean::inc(x_9);
 lean::dec(x_5);
 x_11 = lean::box(0);
}
x_12 = l_Lean_IR_EmitCpp_emitDecl___closed__1;
x_13 = lean::string_append(x_7, x_12);
x_14 = lean::ir::decl_to_string_core(x_3);
x_15 = lean::string_append(x_13, x_14);
lean::dec(x_14);
if (lean::is_scalar(x_11)) {
 x_17 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_17 = x_11;
}
lean::cnstr_set(x_17, 0, x_15);
lean::cnstr_set(x_17, 1, x_9);
return x_17;
}
}
}
obj* l_List_mfor___main___at_Lean_IR_EmitCpp_emitFns___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_4; obj* x_6; obj* x_7; obj* x_8; 
lean::dec(x_1);
x_4 = lean::cnstr_get(x_2, 1);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_release(x_2, 0);
 x_6 = x_2;
} else {
 lean::inc(x_4);
 lean::dec(x_2);
 x_6 = lean::box(0);
}
x_7 = lean::box(0);
if (lean::is_scalar(x_6)) {
 x_8 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_8 = x_6;
}
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_4);
return x_8;
}
else
{
obj* x_9; obj* x_11; obj* x_15; 
x_9 = lean::cnstr_get(x_0, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_0, 1);
lean::inc(x_11);
lean::dec(x_0);
lean::inc(x_1);
x_15 = l_Lean_IR_EmitCpp_emitDecl(x_9, x_1, x_2);
if (lean::obj_tag(x_15) == 0)
{
obj* x_16; obj* x_18; obj* x_19; obj* x_20; 
x_16 = lean::cnstr_get(x_15, 1);
if (lean::is_exclusive(x_15)) {
 lean::cnstr_release(x_15, 0);
 x_18 = x_15;
} else {
 lean::inc(x_16);
 lean::dec(x_15);
 x_18 = lean::box(0);
}
x_19 = lean::box(0);
if (lean::is_scalar(x_18)) {
 x_20 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_20 = x_18;
}
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_16);
x_0 = x_11;
x_2 = x_20;
goto _start;
}
else
{
obj* x_24; obj* x_26; obj* x_28; obj* x_29; 
lean::dec(x_1);
lean::dec(x_11);
x_24 = lean::cnstr_get(x_15, 0);
x_26 = lean::cnstr_get(x_15, 1);
if (lean::is_exclusive(x_15)) {
 x_28 = x_15;
} else {
 lean::inc(x_24);
 lean::inc(x_26);
 lean::dec(x_15);
 x_28 = lean::box(0);
}
if (lean::is_scalar(x_28)) {
 x_29 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_29 = x_28;
}
lean::cnstr_set(x_29, 0, x_24);
lean::cnstr_set(x_29, 1, x_26);
return x_29;
}
}
}
}
obj* l_Lean_IR_EmitCpp_emitFns(obj* x_0, obj* x_1) {
_start:
{
obj* x_3; 
lean::inc(x_0);
x_3 = l_Lean_IR_EmitCpp_getEnv(x_0, x_1);
if (lean::obj_tag(x_3) == 0)
{
obj* x_4; obj* x_6; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_14; obj* x_15; 
x_4 = lean::cnstr_get(x_3, 0);
x_6 = lean::cnstr_get(x_3, 1);
if (lean::is_exclusive(x_3)) {
 x_8 = x_3;
} else {
 lean::inc(x_4);
 lean::inc(x_6);
 lean::dec(x_3);
 x_8 = lean::box(0);
}
x_9 = lean::box(0);
if (lean::is_scalar(x_8)) {
 x_10 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_10 = x_8;
}
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_6);
x_11 = l_Lean_IR_declMapExt;
x_12 = l_Lean_PersistentEnvExtension_getEntries___rarg(x_11, x_4);
lean::dec(x_4);
x_14 = l_List_reverse___rarg(x_12);
x_15 = l_List_mfor___main___at_Lean_IR_EmitCpp_emitFns___spec__1(x_14, x_0, x_10);
return x_15;
}
else
{
obj* x_17; obj* x_19; obj* x_21; obj* x_22; 
lean::dec(x_0);
x_17 = lean::cnstr_get(x_3, 0);
x_19 = lean::cnstr_get(x_3, 1);
if (lean::is_exclusive(x_3)) {
 x_21 = x_3;
} else {
 lean::inc(x_17);
 lean::inc(x_19);
 lean::dec(x_3);
 x_21 = lean::box(0);
}
if (lean::is_scalar(x_21)) {
 x_22 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_22 = x_21;
}
lean::cnstr_set(x_22, 0, x_17);
lean::cnstr_set(x_22, 1, x_19);
return x_22;
}
}
}
obj* l_Lean_IR_EmitCpp_main(obj* x_0, obj* x_1) {
_start:
{
obj* x_3; 
lean::inc(x_0);
x_3 = l_Lean_IR_EmitCpp_emitFileHeader(x_0, x_1);
if (lean::obj_tag(x_3) == 0)
{
obj* x_4; obj* x_6; obj* x_7; obj* x_8; obj* x_10; 
x_4 = lean::cnstr_get(x_3, 1);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 x_6 = x_3;
} else {
 lean::inc(x_4);
 lean::dec(x_3);
 x_6 = lean::box(0);
}
x_7 = lean::box(0);
if (lean::is_scalar(x_6)) {
 x_8 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_8 = x_6;
}
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_4);
lean::inc(x_0);
x_10 = l_Lean_IR_EmitCpp_emitFnDecls(x_0, x_8);
if (lean::obj_tag(x_10) == 0)
{
obj* x_11; obj* x_13; obj* x_14; obj* x_16; 
x_11 = lean::cnstr_get(x_10, 1);
if (lean::is_exclusive(x_10)) {
 lean::cnstr_release(x_10, 0);
 x_13 = x_10;
} else {
 lean::inc(x_11);
 lean::dec(x_10);
 x_13 = lean::box(0);
}
if (lean::is_scalar(x_13)) {
 x_14 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_14 = x_13;
}
lean::cnstr_set(x_14, 0, x_7);
lean::cnstr_set(x_14, 1, x_11);
lean::inc(x_0);
x_16 = l_Lean_IR_EmitCpp_emitFns(x_0, x_14);
if (lean::obj_tag(x_16) == 0)
{
obj* x_17; obj* x_19; obj* x_20; obj* x_21; 
x_17 = lean::cnstr_get(x_16, 1);
if (lean::is_exclusive(x_16)) {
 lean::cnstr_release(x_16, 0);
 x_19 = x_16;
} else {
 lean::inc(x_17);
 lean::dec(x_16);
 x_19 = lean::box(0);
}
if (lean::is_scalar(x_19)) {
 x_20 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_20 = x_19;
}
lean::cnstr_set(x_20, 0, x_7);
lean::cnstr_set(x_20, 1, x_17);
x_21 = l_Lean_IR_EmitCpp_emitMainFnIfNeeded(x_0, x_20);
return x_21;
}
else
{
obj* x_23; obj* x_25; obj* x_27; obj* x_28; 
lean::dec(x_0);
x_23 = lean::cnstr_get(x_16, 0);
x_25 = lean::cnstr_get(x_16, 1);
if (lean::is_exclusive(x_16)) {
 x_27 = x_16;
} else {
 lean::inc(x_23);
 lean::inc(x_25);
 lean::dec(x_16);
 x_27 = lean::box(0);
}
if (lean::is_scalar(x_27)) {
 x_28 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_28 = x_27;
}
lean::cnstr_set(x_28, 0, x_23);
lean::cnstr_set(x_28, 1, x_25);
return x_28;
}
}
else
{
obj* x_30; obj* x_32; obj* x_34; obj* x_35; 
lean::dec(x_0);
x_30 = lean::cnstr_get(x_10, 0);
x_32 = lean::cnstr_get(x_10, 1);
if (lean::is_exclusive(x_10)) {
 x_34 = x_10;
} else {
 lean::inc(x_30);
 lean::inc(x_32);
 lean::dec(x_10);
 x_34 = lean::box(0);
}
if (lean::is_scalar(x_34)) {
 x_35 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_35 = x_34;
}
lean::cnstr_set(x_35, 0, x_30);
lean::cnstr_set(x_35, 1, x_32);
return x_35;
}
}
else
{
obj* x_37; obj* x_39; obj* x_41; obj* x_42; 
lean::dec(x_0);
x_37 = lean::cnstr_get(x_3, 0);
x_39 = lean::cnstr_get(x_3, 1);
if (lean::is_exclusive(x_3)) {
 x_41 = x_3;
} else {
 lean::inc(x_37);
 lean::inc(x_39);
 lean::dec(x_3);
 x_41 = lean::box(0);
}
if (lean::is_scalar(x_41)) {
 x_42 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_42 = x_41;
}
lean::cnstr_set(x_42, 0, x_37);
lean::cnstr_set(x_42, 1, x_39);
return x_42;
}
}
}
obj* _init_l_Lean_IR_emitCpp___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("");
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
namespace lean {
namespace ir {
obj* emit_cpp_core(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_2 = l_HashMap_Inhabited___closed__1;
x_3 = lean::box(0);
x_4 = l_Array_empty___closed__1;
x_5 = lean::alloc_cnstr(0, 6, 0);
lean::cnstr_set(x_5, 0, x_0);
lean::cnstr_set(x_5, 1, x_1);
lean::cnstr_set(x_5, 2, x_2);
lean::cnstr_set(x_5, 3, x_2);
lean::cnstr_set(x_5, 4, x_3);
lean::cnstr_set(x_5, 5, x_4);
x_6 = l_Lean_IR_emitCpp___closed__1;
x_7 = l_Lean_IR_EmitCpp_main(x_5, x_6);
if (lean::obj_tag(x_7) == 0)
{
obj* x_8; obj* x_11; 
x_8 = lean::cnstr_get(x_7, 1);
lean::inc(x_8);
lean::dec(x_7);
x_11 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_11, 0, x_8);
return x_11;
}
else
{
obj* x_12; obj* x_15; 
x_12 = lean::cnstr_get(x_7, 0);
lean::inc(x_12);
lean::dec(x_7);
x_15 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_15, 0, x_12);
return x_15;
}
}
}
}}
obj* initialize_init_control_conditional(obj*);
obj* initialize_init_lean_name__mangling(obj*);
obj* initialize_init_lean_compiler_initattr(obj*);
obj* initialize_init_lean_compiler_ir_compilerm(obj*);
obj* initialize_init_lean_compiler_ir_emitutil(obj*);
obj* initialize_init_lean_compiler_ir_normids(obj*);
static bool _G_initialized = false;
obj* initialize_init_lean_compiler_ir_emitcpp(obj* w) {
 if (_G_initialized) return w;
 _G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_control_conditional(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_name__mangling(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_initattr(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_ir_compilerm(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_ir_emitutil(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_ir_normids(w);
if (io_result_is_error(w)) return w;
 l_Lean_IR_EmitCpp_leanMainFn = _init_l_Lean_IR_EmitCpp_leanMainFn();
lean::mark_persistent(l_Lean_IR_EmitCpp_leanMainFn);
 l_Lean_IR_EmitCpp_argToCppString___closed__1 = _init_l_Lean_IR_EmitCpp_argToCppString___closed__1();
lean::mark_persistent(l_Lean_IR_EmitCpp_argToCppString___closed__1);
 l_Lean_IR_EmitCpp_toCppType___main___closed__1 = _init_l_Lean_IR_EmitCpp_toCppType___main___closed__1();
lean::mark_persistent(l_Lean_IR_EmitCpp_toCppType___main___closed__1);
 l_Lean_IR_EmitCpp_toCppType___main___closed__2 = _init_l_Lean_IR_EmitCpp_toCppType___main___closed__2();
lean::mark_persistent(l_Lean_IR_EmitCpp_toCppType___main___closed__2);
 l_Lean_IR_EmitCpp_toCppType___main___closed__3 = _init_l_Lean_IR_EmitCpp_toCppType___main___closed__3();
lean::mark_persistent(l_Lean_IR_EmitCpp_toCppType___main___closed__3);
 l_Lean_IR_EmitCpp_toCppType___main___closed__4 = _init_l_Lean_IR_EmitCpp_toCppType___main___closed__4();
lean::mark_persistent(l_Lean_IR_EmitCpp_toCppType___main___closed__4);
 l_Lean_IR_EmitCpp_toCppType___main___closed__5 = _init_l_Lean_IR_EmitCpp_toCppType___main___closed__5();
lean::mark_persistent(l_Lean_IR_EmitCpp_toCppType___main___closed__5);
 l_Lean_IR_EmitCpp_toCppType___main___closed__6 = _init_l_Lean_IR_EmitCpp_toCppType___main___closed__6();
lean::mark_persistent(l_Lean_IR_EmitCpp_toCppType___main___closed__6);
 l_Lean_IR_EmitCpp_toCppType___main___closed__7 = _init_l_Lean_IR_EmitCpp_toCppType___main___closed__7();
lean::mark_persistent(l_Lean_IR_EmitCpp_toCppType___main___closed__7);
 l_Lean_IR_EmitCpp_openNamespacesAux___main___closed__1 = _init_l_Lean_IR_EmitCpp_openNamespacesAux___main___closed__1();
lean::mark_persistent(l_Lean_IR_EmitCpp_openNamespacesAux___main___closed__1);
 l_Lean_IR_EmitCpp_openNamespacesAux___main___closed__2 = _init_l_Lean_IR_EmitCpp_openNamespacesAux___main___closed__2();
lean::mark_persistent(l_Lean_IR_EmitCpp_openNamespacesAux___main___closed__2);
 l_Lean_IR_EmitCpp_openNamespacesAux___main___closed__3 = _init_l_Lean_IR_EmitCpp_openNamespacesAux___main___closed__3();
lean::mark_persistent(l_Lean_IR_EmitCpp_openNamespacesAux___main___closed__3);
 l_Lean_IR_EmitCpp_closeNamespacesAux___main___closed__1 = _init_l_Lean_IR_EmitCpp_closeNamespacesAux___main___closed__1();
lean::mark_persistent(l_Lean_IR_EmitCpp_closeNamespacesAux___main___closed__1);
 l_Lean_IR_EmitCpp_throwInvalidExportName___rarg___closed__1 = _init_l_Lean_IR_EmitCpp_throwInvalidExportName___rarg___closed__1();
lean::mark_persistent(l_Lean_IR_EmitCpp_throwInvalidExportName___rarg___closed__1);
 l_Lean_IR_EmitCpp_toBaseCppName___closed__1 = _init_l_Lean_IR_EmitCpp_toBaseCppName___closed__1();
lean::mark_persistent(l_Lean_IR_EmitCpp_toBaseCppName___closed__1);
 l_Lean_IR_EmitCpp_toBaseCppName___closed__2 = _init_l_Lean_IR_EmitCpp_toBaseCppName___closed__2();
lean::mark_persistent(l_Lean_IR_EmitCpp_toBaseCppName___closed__2);
 l_Lean_IR_EmitCpp_toCppName___closed__1 = _init_l_Lean_IR_EmitCpp_toCppName___closed__1();
lean::mark_persistent(l_Lean_IR_EmitCpp_toCppName___closed__1);
 l_Lean_IR_EmitCpp_toCppInitName___closed__1 = _init_l_Lean_IR_EmitCpp_toCppInitName___closed__1();
lean::mark_persistent(l_Lean_IR_EmitCpp_toCppInitName___closed__1);
 l_Lean_IR_EmitCpp_emitFnDeclAux___closed__1 = _init_l_Lean_IR_EmitCpp_emitFnDeclAux___closed__1();
lean::mark_persistent(l_Lean_IR_EmitCpp_emitFnDeclAux___closed__1);
 l_Lean_IR_EmitCpp_emitFnDeclAux___closed__2 = _init_l_Lean_IR_EmitCpp_emitFnDeclAux___closed__2();
lean::mark_persistent(l_Lean_IR_EmitCpp_emitFnDeclAux___closed__2);
 l_Lean_IR_EmitCpp_emitFnDeclAux___closed__3 = _init_l_Lean_IR_EmitCpp_emitFnDeclAux___closed__3();
lean::mark_persistent(l_Lean_IR_EmitCpp_emitFnDeclAux___closed__3);
 l_Lean_IR_EmitCpp_emitExternDeclAux___closed__1 = _init_l_Lean_IR_EmitCpp_emitExternDeclAux___closed__1();
lean::mark_persistent(l_Lean_IR_EmitCpp_emitExternDeclAux___closed__1);
 l_Lean_IR_EmitCpp_emitExternDeclAux___closed__2 = _init_l_Lean_IR_EmitCpp_emitExternDeclAux___closed__2();
lean::mark_persistent(l_Lean_IR_EmitCpp_emitExternDeclAux___closed__2);
 l_List_mfor___main___at_Lean_IR_EmitCpp_emitFnDecls___spec__5___closed__1 = _init_l_List_mfor___main___at_Lean_IR_EmitCpp_emitFnDecls___spec__5___closed__1();
lean::mark_persistent(l_List_mfor___main___at_Lean_IR_EmitCpp_emitFnDecls___spec__5___closed__1);
 l_Lean_IR_EmitCpp_emitMainFn___closed__1 = _init_l_Lean_IR_EmitCpp_emitMainFn___closed__1();
lean::mark_persistent(l_Lean_IR_EmitCpp_emitMainFn___closed__1);
 l_Lean_IR_EmitCpp_emitMainFn___closed__2 = _init_l_Lean_IR_EmitCpp_emitMainFn___closed__2();
lean::mark_persistent(l_Lean_IR_EmitCpp_emitMainFn___closed__2);
 l_Lean_IR_EmitCpp_emitMainFn___closed__3 = _init_l_Lean_IR_EmitCpp_emitMainFn___closed__3();
lean::mark_persistent(l_Lean_IR_EmitCpp_emitMainFn___closed__3);
 l_Lean_IR_EmitCpp_emitMainFn___closed__4 = _init_l_Lean_IR_EmitCpp_emitMainFn___closed__4();
lean::mark_persistent(l_Lean_IR_EmitCpp_emitMainFn___closed__4);
 l_Lean_IR_EmitCpp_emitMainFn___closed__5 = _init_l_Lean_IR_EmitCpp_emitMainFn___closed__5();
lean::mark_persistent(l_Lean_IR_EmitCpp_emitMainFn___closed__5);
 l_Lean_IR_EmitCpp_emitMainFn___closed__6 = _init_l_Lean_IR_EmitCpp_emitMainFn___closed__6();
lean::mark_persistent(l_Lean_IR_EmitCpp_emitMainFn___closed__6);
 l_Lean_IR_EmitCpp_emitMainFn___closed__7 = _init_l_Lean_IR_EmitCpp_emitMainFn___closed__7();
lean::mark_persistent(l_Lean_IR_EmitCpp_emitMainFn___closed__7);
 l_Lean_IR_EmitCpp_emitMainFn___closed__8 = _init_l_Lean_IR_EmitCpp_emitMainFn___closed__8();
lean::mark_persistent(l_Lean_IR_EmitCpp_emitMainFn___closed__8);
 l_Lean_IR_EmitCpp_emitMainFn___closed__9 = _init_l_Lean_IR_EmitCpp_emitMainFn___closed__9();
lean::mark_persistent(l_Lean_IR_EmitCpp_emitMainFn___closed__9);
 l_Lean_IR_EmitCpp_emitMainFn___closed__10 = _init_l_Lean_IR_EmitCpp_emitMainFn___closed__10();
lean::mark_persistent(l_Lean_IR_EmitCpp_emitMainFn___closed__10);
 l_Lean_IR_EmitCpp_emitMainFn___closed__11 = _init_l_Lean_IR_EmitCpp_emitMainFn___closed__11();
lean::mark_persistent(l_Lean_IR_EmitCpp_emitMainFn___closed__11);
 l_Lean_IR_EmitCpp_emitMainFn___closed__12 = _init_l_Lean_IR_EmitCpp_emitMainFn___closed__12();
lean::mark_persistent(l_Lean_IR_EmitCpp_emitMainFn___closed__12);
 l_Lean_IR_EmitCpp_emitMainFn___closed__13 = _init_l_Lean_IR_EmitCpp_emitMainFn___closed__13();
lean::mark_persistent(l_Lean_IR_EmitCpp_emitMainFn___closed__13);
 l_Lean_IR_EmitCpp_emitMainFn___closed__14 = _init_l_Lean_IR_EmitCpp_emitMainFn___closed__14();
lean::mark_persistent(l_Lean_IR_EmitCpp_emitMainFn___closed__14);
 l_Lean_IR_EmitCpp_emitFileHeader___closed__1 = _init_l_Lean_IR_EmitCpp_emitFileHeader___closed__1();
lean::mark_persistent(l_Lean_IR_EmitCpp_emitFileHeader___closed__1);
 l_Lean_IR_EmitCpp_emitFileHeader___closed__2 = _init_l_Lean_IR_EmitCpp_emitFileHeader___closed__2();
lean::mark_persistent(l_Lean_IR_EmitCpp_emitFileHeader___closed__2);
 l_Lean_IR_EmitCpp_emitFileHeader___closed__3 = _init_l_Lean_IR_EmitCpp_emitFileHeader___closed__3();
lean::mark_persistent(l_Lean_IR_EmitCpp_emitFileHeader___closed__3);
 l_Lean_IR_EmitCpp_emitFileHeader___closed__4 = _init_l_Lean_IR_EmitCpp_emitFileHeader___closed__4();
lean::mark_persistent(l_Lean_IR_EmitCpp_emitFileHeader___closed__4);
 l_Lean_IR_EmitCpp_emitFileHeader___closed__5 = _init_l_Lean_IR_EmitCpp_emitFileHeader___closed__5();
lean::mark_persistent(l_Lean_IR_EmitCpp_emitFileHeader___closed__5);
 l_Lean_IR_EmitCpp_emitFileHeader___closed__6 = _init_l_Lean_IR_EmitCpp_emitFileHeader___closed__6();
lean::mark_persistent(l_Lean_IR_EmitCpp_emitFileHeader___closed__6);
 l_Lean_IR_EmitCpp_emitFileHeader___closed__7 = _init_l_Lean_IR_EmitCpp_emitFileHeader___closed__7();
lean::mark_persistent(l_Lean_IR_EmitCpp_emitFileHeader___closed__7);
 l_Lean_IR_EmitCpp_throwUnknownVar___rarg___closed__1 = _init_l_Lean_IR_EmitCpp_throwUnknownVar___rarg___closed__1();
lean::mark_persistent(l_Lean_IR_EmitCpp_throwUnknownVar___rarg___closed__1);
 l_Lean_IR_EmitCpp_getJPParams___closed__1 = _init_l_Lean_IR_EmitCpp_getJPParams___closed__1();
lean::mark_persistent(l_Lean_IR_EmitCpp_getJPParams___closed__1);
 l_Lean_IR_EmitCpp_declareVar___closed__1 = _init_l_Lean_IR_EmitCpp_declareVar___closed__1();
lean::mark_persistent(l_Lean_IR_EmitCpp_declareVar___closed__1);
 l_Lean_IR_EmitCpp_emitTag___closed__1 = _init_l_Lean_IR_EmitCpp_emitTag___closed__1();
lean::mark_persistent(l_Lean_IR_EmitCpp_emitTag___closed__1);
 l_Lean_IR_EmitCpp_emitIf___closed__1 = _init_l_Lean_IR_EmitCpp_emitIf___closed__1();
lean::mark_persistent(l_Lean_IR_EmitCpp_emitIf___closed__1);
 l_Lean_IR_EmitCpp_emitIf___closed__2 = _init_l_Lean_IR_EmitCpp_emitIf___closed__2();
lean::mark_persistent(l_Lean_IR_EmitCpp_emitIf___closed__2);
 l_Lean_IR_EmitCpp_emitIf___closed__3 = _init_l_Lean_IR_EmitCpp_emitIf___closed__3();
lean::mark_persistent(l_Lean_IR_EmitCpp_emitIf___closed__3);
 l_Array_mforAux___main___at_Lean_IR_EmitCpp_emitCase___spec__1___closed__1 = _init_l_Array_mforAux___main___at_Lean_IR_EmitCpp_emitCase___spec__1___closed__1();
lean::mark_persistent(l_Array_mforAux___main___at_Lean_IR_EmitCpp_emitCase___spec__1___closed__1);
 l_Array_mforAux___main___at_Lean_IR_EmitCpp_emitCase___spec__1___closed__2 = _init_l_Array_mforAux___main___at_Lean_IR_EmitCpp_emitCase___spec__1___closed__2();
lean::mark_persistent(l_Array_mforAux___main___at_Lean_IR_EmitCpp_emitCase___spec__1___closed__2);
 l_Array_mforAux___main___at_Lean_IR_EmitCpp_emitCase___spec__1___closed__3 = _init_l_Array_mforAux___main___at_Lean_IR_EmitCpp_emitCase___spec__1___closed__3();
lean::mark_persistent(l_Array_mforAux___main___at_Lean_IR_EmitCpp_emitCase___spec__1___closed__3);
 l_Lean_IR_EmitCpp_emitCase___closed__1 = _init_l_Lean_IR_EmitCpp_emitCase___closed__1();
lean::mark_persistent(l_Lean_IR_EmitCpp_emitCase___closed__1);
 l_Lean_IR_EmitCpp_emitCase___closed__2 = _init_l_Lean_IR_EmitCpp_emitCase___closed__2();
lean::mark_persistent(l_Lean_IR_EmitCpp_emitCase___closed__2);
 l_Lean_IR_EmitCpp_emitInc___closed__1 = _init_l_Lean_IR_EmitCpp_emitInc___closed__1();
lean::mark_persistent(l_Lean_IR_EmitCpp_emitInc___closed__1);
 l_Lean_IR_EmitCpp_emitInc___closed__2 = _init_l_Lean_IR_EmitCpp_emitInc___closed__2();
lean::mark_persistent(l_Lean_IR_EmitCpp_emitInc___closed__2);
 l_Lean_IR_EmitCpp_emitInc___closed__3 = _init_l_Lean_IR_EmitCpp_emitInc___closed__3();
lean::mark_persistent(l_Lean_IR_EmitCpp_emitInc___closed__3);
 l_Lean_IR_EmitCpp_emitDec___closed__1 = _init_l_Lean_IR_EmitCpp_emitDec___closed__1();
lean::mark_persistent(l_Lean_IR_EmitCpp_emitDec___closed__1);
 l_Lean_IR_EmitCpp_emitDec___closed__2 = _init_l_Lean_IR_EmitCpp_emitDec___closed__2();
lean::mark_persistent(l_Lean_IR_EmitCpp_emitDec___closed__2);
 l_Lean_IR_EmitCpp_emitRelease___closed__1 = _init_l_Lean_IR_EmitCpp_emitRelease___closed__1();
lean::mark_persistent(l_Lean_IR_EmitCpp_emitRelease___closed__1);
 l_Lean_IR_EmitCpp_emitSet___closed__1 = _init_l_Lean_IR_EmitCpp_emitSet___closed__1();
lean::mark_persistent(l_Lean_IR_EmitCpp_emitSet___closed__1);
 l_Lean_IR_EmitCpp_emitOffset___closed__1 = _init_l_Lean_IR_EmitCpp_emitOffset___closed__1();
lean::mark_persistent(l_Lean_IR_EmitCpp_emitOffset___closed__1);
 l_Lean_IR_EmitCpp_emitOffset___closed__2 = _init_l_Lean_IR_EmitCpp_emitOffset___closed__2();
lean::mark_persistent(l_Lean_IR_EmitCpp_emitOffset___closed__2);
 l_Lean_IR_EmitCpp_emitUSet___closed__1 = _init_l_Lean_IR_EmitCpp_emitUSet___closed__1();
lean::mark_persistent(l_Lean_IR_EmitCpp_emitUSet___closed__1);
 l_Nat_mforAux___main___at_Lean_IR_EmitCpp_emitJmp___spec__1___closed__1 = _init_l_Nat_mforAux___main___at_Lean_IR_EmitCpp_emitJmp___spec__1___closed__1();
lean::mark_persistent(l_Nat_mforAux___main___at_Lean_IR_EmitCpp_emitJmp___spec__1___closed__1);
 l_Lean_IR_EmitCpp_emitJmp___closed__1 = _init_l_Lean_IR_EmitCpp_emitJmp___closed__1();
lean::mark_persistent(l_Lean_IR_EmitCpp_emitJmp___closed__1);
 l_Lean_IR_EmitCpp_emitJmp___closed__2 = _init_l_Lean_IR_EmitCpp_emitJmp___closed__2();
lean::mark_persistent(l_Lean_IR_EmitCpp_emitJmp___closed__2);
 l_Lean_IR_EmitCpp_emitProj___closed__1 = _init_l_Lean_IR_EmitCpp_emitProj___closed__1();
lean::mark_persistent(l_Lean_IR_EmitCpp_emitProj___closed__1);
 l_Lean_IR_EmitCpp_emitFullApp___closed__1 = _init_l_Lean_IR_EmitCpp_emitFullApp___closed__1();
lean::mark_persistent(l_Lean_IR_EmitCpp_emitFullApp___closed__1);
 l_Nat_mforAux___main___at_Lean_IR_EmitCpp_emitPartialApp___spec__1___closed__1 = _init_l_Nat_mforAux___main___at_Lean_IR_EmitCpp_emitPartialApp___spec__1___closed__1();
lean::mark_persistent(l_Nat_mforAux___main___at_Lean_IR_EmitCpp_emitPartialApp___spec__1___closed__1);
 l_Lean_IR_EmitCpp_emitPartialApp___closed__1 = _init_l_Lean_IR_EmitCpp_emitPartialApp___closed__1();
lean::mark_persistent(l_Lean_IR_EmitCpp_emitPartialApp___closed__1);
 l_Lean_IR_EmitCpp_emitPartialApp___closed__2 = _init_l_Lean_IR_EmitCpp_emitPartialApp___closed__2();
lean::mark_persistent(l_Lean_IR_EmitCpp_emitPartialApp___closed__2);
 l_Lean_IR_EmitCpp_emitBox___closed__1 = _init_l_Lean_IR_EmitCpp_emitBox___closed__1();
lean::mark_persistent(l_Lean_IR_EmitCpp_emitBox___closed__1);
 l_Lean_IR_EmitCpp_emitBox___closed__2 = _init_l_Lean_IR_EmitCpp_emitBox___closed__2();
lean::mark_persistent(l_Lean_IR_EmitCpp_emitBox___closed__2);
 l_Lean_IR_EmitCpp_emitBox___closed__3 = _init_l_Lean_IR_EmitCpp_emitBox___closed__3();
lean::mark_persistent(l_Lean_IR_EmitCpp_emitBox___closed__3);
 l_Lean_IR_EmitCpp_emitBox___closed__4 = _init_l_Lean_IR_EmitCpp_emitBox___closed__4();
lean::mark_persistent(l_Lean_IR_EmitCpp_emitBox___closed__4);
 l_Lean_IR_EmitCpp_emitBox___closed__5 = _init_l_Lean_IR_EmitCpp_emitBox___closed__5();
lean::mark_persistent(l_Lean_IR_EmitCpp_emitBox___closed__5);
 l_Lean_IR_EmitCpp_emitUnbox___closed__1 = _init_l_Lean_IR_EmitCpp_emitUnbox___closed__1();
lean::mark_persistent(l_Lean_IR_EmitCpp_emitUnbox___closed__1);
 l_Lean_IR_EmitCpp_emitUnbox___closed__2 = _init_l_Lean_IR_EmitCpp_emitUnbox___closed__2();
lean::mark_persistent(l_Lean_IR_EmitCpp_emitUnbox___closed__2);
 l_Lean_IR_EmitCpp_emitUnbox___closed__3 = _init_l_Lean_IR_EmitCpp_emitUnbox___closed__3();
lean::mark_persistent(l_Lean_IR_EmitCpp_emitUnbox___closed__3);
 l_Lean_IR_EmitCpp_emitUnbox___closed__4 = _init_l_Lean_IR_EmitCpp_emitUnbox___closed__4();
lean::mark_persistent(l_Lean_IR_EmitCpp_emitUnbox___closed__4);
 l_Lean_IR_EmitCpp_emitIsShared___closed__1 = _init_l_Lean_IR_EmitCpp_emitIsShared___closed__1();
lean::mark_persistent(l_Lean_IR_EmitCpp_emitIsShared___closed__1);
 l_Lean_IR_EmitCpp_emitIsTaggedPtr___closed__1 = _init_l_Lean_IR_EmitCpp_emitIsTaggedPtr___closed__1();
lean::mark_persistent(l_Lean_IR_EmitCpp_emitIsTaggedPtr___closed__1);
 l_Lean_IR_EmitCpp_emitNumLit___closed__1 = _init_l_Lean_IR_EmitCpp_emitNumLit___closed__1();
lean::mark_persistent(l_Lean_IR_EmitCpp_emitNumLit___closed__1);
 l_Lean_IR_EmitCpp_emitNumLit___closed__2 = _init_l_Lean_IR_EmitCpp_emitNumLit___closed__2();
lean::mark_persistent(l_Lean_IR_EmitCpp_emitNumLit___closed__2);
 l_Lean_IR_EmitCpp_emitLit___closed__1 = _init_l_Lean_IR_EmitCpp_emitLit___closed__1();
lean::mark_persistent(l_Lean_IR_EmitCpp_emitLit___closed__1);
 l_Lean_IR_EmitCpp_emitBlock___main___closed__1 = _init_l_Lean_IR_EmitCpp_emitBlock___main___closed__1();
lean::mark_persistent(l_Lean_IR_EmitCpp_emitBlock___main___closed__1);
 l_Lean_IR_EmitCpp_emitBlock___main___closed__2 = _init_l_Lean_IR_EmitCpp_emitBlock___main___closed__2();
lean::mark_persistent(l_Lean_IR_EmitCpp_emitBlock___main___closed__2);
 l_Lean_IR_EmitCpp_emitFnBody___main___closed__1 = _init_l_Lean_IR_EmitCpp_emitFnBody___main___closed__1();
lean::mark_persistent(l_Lean_IR_EmitCpp_emitFnBody___main___closed__1);
 l_Lean_IR_EmitCpp_emitFnBody___main___closed__2 = _init_l_Lean_IR_EmitCpp_emitFnBody___main___closed__2();
lean::mark_persistent(l_Lean_IR_EmitCpp_emitFnBody___main___closed__2);
 l_Lean_IR_EmitCpp_emitDeclAux___closed__1 = _init_l_Lean_IR_EmitCpp_emitDeclAux___closed__1();
lean::mark_persistent(l_Lean_IR_EmitCpp_emitDeclAux___closed__1);
 l_Lean_IR_EmitCpp_emitDecl___closed__1 = _init_l_Lean_IR_EmitCpp_emitDecl___closed__1();
lean::mark_persistent(l_Lean_IR_EmitCpp_emitDecl___closed__1);
 l_Lean_IR_emitCpp___closed__1 = _init_l_Lean_IR_emitCpp___closed__1();
lean::mark_persistent(l_Lean_IR_emitCpp___closed__1);
return w;
}
