// Lean compiler output
// Module: Lean.Elab.Deriving.Ord
// Imports: Init Lean.Meta.Transform Lean.Elab.Deriving.Basic Lean.Elab.Deriving.Util
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
lean_object* l_List_reverse___rarg(lean_object*);
static lean_object* l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__23;
lean_object* l_Lean_getConstInfo___at_Lean_Elab_Term_mkConst___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__6;
uint8_t l_Lean_Expr_hasAnyFVar_visit___at_Lean_Expr_containsFVar___spec__1(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__9;
static lean_object* l_Lean_Elab_Deriving_Ord_initFn____x40_Lean_Elab_Deriving_Ord___hyg_2892____closed__1;
static lean_object* l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__13;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_List_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__7___lambda__2___closed__11;
static lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__33;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__6(size_t, size_t, lean_object*);
static lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__3;
static lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__22;
lean_object* l_Lean_Elab_Command_liftTermElabM___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__43;
static lean_object* l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__12;
static lean_object* l_Lean_Elab_Deriving_Ord_mkMutualBlock___closed__2;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Elab_registerDerivingHandler(lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__2;
static lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__35;
lean_object* lean_environment_find(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__16;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__39;
static lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__5;
static lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__36;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Ord_mkOrdHeader(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_betaReduce___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
static lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__46;
static lean_object* l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__10;
static lean_object* l_Lean_Elab_Deriving_Ord_mkMutualBlock___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__20;
static lean_object* l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__21;
static lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__6;
static lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__5;
static lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__29;
static lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__8;
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Elab_Deriving_Ord_mkOrdInstanceHandler___spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__25;
lean_object* l_Lean_Elab_Deriving_mkLocalInstanceLetDecls(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__7___lambda__2___closed__7;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__1;
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Deriving_Ord_mkMutualBlock___closed__3;
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMutualBlock___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_getConstInfoCtor___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__1___closed__4;
static lean_object* l_Lean_Elab_Deriving_Ord_mkOrdHeader___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__7;
static lean_object* l_List_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__7___lambda__2___closed__13;
static lean_object* l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__24;
lean_object* l_Lean_Elab_Deriving_mkDiscrs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_getConstInfoCtor___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__1___closed__1;
static lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__10;
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__19;
lean_object* l_Array_mapMUnsafe_map___at___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___spec__3(size_t, size_t, lean_object*);
static lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__32;
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__7;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Ord_mkMatch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_getConstInfoCtor___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__1___closed__2;
static lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__11;
static lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__19;
static lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__4;
static lean_object* l_List_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__7___lambda__2___closed__2;
lean_object* l_Lean_Elab_Deriving_mkInstanceCmds(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Deriving_Ord_mkMatch___spec__1(size_t, size_t, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___closed__4;
static lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__2;
static lean_object* l_List_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__7___lambda__2___closed__12;
static lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__34;
lean_object* l_Lean_Elab_Deriving_mkLet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Ord_mkOrdInstanceHandler(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
static lean_object* l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__5;
lean_object* l_panic___at_Lean_Expr_getRevArg_x21___spec__1(lean_object*);
static lean_object* l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__25;
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Ord_mkMutualBlock(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__22;
LEAN_EXPORT lean_object* l_Lean_isInductive___at_Lean_Elab_Deriving_Ord_mkOrdInstanceHandler___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___closed__8;
lean_object* l_Lean_Elab_addMacroStack___at_Lean_Elab_Term_instAddErrorMessageContextTermElabM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__7;
static lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__24;
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__7___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__13;
static lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___closed__6;
lean_object* l_Array_mkArray4___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__14;
lean_object* lean_array_to_list(lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__16;
static lean_object* l_List_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__7___lambda__2___closed__5;
lean_object* l_panic___at___private_Init_Prelude_0__Lean_assembleParts___spec__1(lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__6;
lean_object* l_Lean_mkSepArray(lean_object*, lean_object*);
lean_object* l_panic___at_Lean_Elab_Deriving_mkLocalInstanceLetDecls___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_transform___at_Lean_Core_betaReduce___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__31;
lean_object* l_Lean_Elab_Deriving_mkContext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__7___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__21;
static lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__38;
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
static lean_object* l_List_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__7___lambda__2___closed__3;
static lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__6;
static lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__20;
static lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__41;
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Ord_initFn____x40_Lean_Elab_Deriving_Ord___hyg_2892_(lean_object*);
lean_object* l_Lean_Elab_Deriving_mkHeader(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__23;
static lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__37;
static lean_object* l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__4;
static lean_object* l_Lean_getConstInfoCtor___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__7___lambda__2___closed__9;
static lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__42;
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
static lean_object* l_List_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__7___lambda__2___closed__4;
lean_object* l_Array_mkArray5___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMutualBlock___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray1___rarg(lean_object*);
static lean_object* l_List_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__7___lambda__2___closed__8;
lean_object* lean_environment_main_module(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__6___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__17;
static lean_object* l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__8;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__12;
lean_object* l_String_toSubstring_x27(lean_object*);
static lean_object* l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__1;
lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_exprToSyntax___spec__1___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Deriving_Ord_mkOrdHeader___closed__1;
lean_object* l_Array_mkArray7___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__2;
lean_object* l_Array_mkArray2___rarg(lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__26;
lean_object* l_Lean_addTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__3;
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__1;
static lean_object* l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__15;
lean_object* l_Lean_isTracingEnabledFor___at_Lean_Elab_Term_traceAtCmdPos___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___closed__7;
static lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__44;
lean_object* l_Array_mkArray6___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__47;
static lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___closed__1;
lean_object* lean_array_pop(lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Elab_Deriving_Ord_mkOrdInstanceHandler___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Ord_mkAuxFunction(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__5;
static lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__18;
LEAN_EXPORT lean_object* l_Lean_isInductive___at_Lean_Elab_Deriving_Ord_mkOrdInstanceHandler___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__30;
static lean_object* l_List_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__7___lambda__2___closed__1;
static lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___closed__5;
lean_object* l_Lean_Meta_forallTelescopeReducing___at_Lean_Elab_Deriving_mkInductArgNames___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__14;
static lean_object* l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__9;
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__7___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__27;
static lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__28;
lean_object* lean_mk_syntax_ident(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__1;
static lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__4;
static lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__15;
lean_object* l_Array_mkArray3___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__3;
static lean_object* l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__26;
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabCommand___spec__19(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__7___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_betaReduce___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__7___lambda__2___closed__10;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Ord_mkMatch_mkAlts(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Deriving_Ord_mkMatch___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__40;
static lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__9;
static lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__27;
static lean_object* l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__18;
static lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__45;
static lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__3;
static lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__17;
static lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__8;
static lean_object* l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__11;
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__4;
static lean_object* l_List_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__7___lambda__2___closed__6;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___closed__3;
static lean_object* _init_l_Lean_Elab_Deriving_Ord_mkOrdHeader___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Ord", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_Ord_mkOrdHeader___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Deriving_Ord_mkOrdHeader___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Ord_mkOrdHeader(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = l_Lean_Elab_Deriving_Ord_mkOrdHeader___closed__2;
x_10 = lean_unsigned_to_nat(2u);
x_11 = l_Lean_Elab_Deriving_mkHeader(x_9, x_10, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_9 = lean_ctor_get(x_6, 5);
x_10 = lean_ctor_get(x_2, 2);
lean_inc(x_10);
lean_inc(x_10);
x_11 = l_Lean_Elab_getBetterRef(x_9, x_10);
x_12 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_4, x_5, x_6, x_7, x_8);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Elab_addMacroStack___at_Lean_Elab_Term_instAddErrorMessageContextTermElabM___spec__1(x_13, x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_14);
lean_dec(x_2);
lean_dec(x_10);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set_tag(x_15, 1);
lean_ctor_set(x_15, 0, x_18);
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_15);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_11);
lean_ctor_set(x_21, 1, x_19);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("'", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_getConstInfoCtor___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("' is not a constructor", 22);
return x_1;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_getConstInfoCtor___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__1___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_2);
lean_inc(x_1);
x_9 = l_Lean_getConstInfo___at_Lean_Elab_Term_mkConst___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 6)
{
uint8_t x_11; 
lean_dec(x_2);
lean_dec(x_1);
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_9, 0);
lean_dec(x_12);
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec(x_10);
lean_ctor_set(x_9, 0, x_13);
return x_9;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_dec(x_9);
x_15 = lean_ctor_get(x_10, 0);
lean_inc(x_15);
lean_dec(x_10);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_10);
x_17 = lean_ctor_get(x_9, 1);
lean_inc(x_17);
lean_dec(x_9);
x_18 = lean_box(0);
x_19 = l_Lean_Expr_const___override(x_1, x_18);
x_20 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = l_Lean_getConstInfoCtor___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__1___closed__2;
x_22 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
x_23 = l_Lean_getConstInfoCtor___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__1___closed__4;
x_24 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Lean_throwError___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__2(x_24, x_2, x_3, x_4, x_5, x_6, x_7, x_17);
return x_25;
}
}
else
{
uint8_t x_26; 
lean_dec(x_2);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_9);
if (x_26 == 0)
{
return x_9;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_9, 0);
x_28 = lean_ctor_get(x_9, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_9);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean", 4);
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Parser", 6);
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Term", 4);
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("hole", 4);
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__1;
x_2 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__2;
x_3 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__3;
x_4 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__4;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_", 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_nat_dec_le(x_3, x_2);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_eq(x_1, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_sub(x_1, x_16);
lean_dec(x_1);
lean_inc(x_10);
x_18 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_exprToSyntax___spec__1___rarg(x_10, x_11, x_12);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_st_ref_get(x_11, x_20);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__6;
lean_inc(x_19);
x_24 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_24, 0, x_19);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Array_mkArray1___rarg(x_24);
x_26 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__5;
x_27 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_27, 0, x_19);
lean_ctor_set(x_27, 1, x_26);
lean_ctor_set(x_27, 2, x_25);
x_28 = lean_array_push(x_5, x_27);
x_29 = lean_nat_add(x_2, x_4);
lean_dec(x_2);
x_1 = x_17;
x_2 = x_29;
x_5 = x_28;
x_12 = x_22;
goto _start;
}
else
{
lean_object* x_31; 
lean_dec(x_10);
lean_dec(x_2);
lean_dec(x_1);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_5);
lean_ctor_set(x_31, 1, x_12);
return x_31;
}
}
else
{
lean_object* x_32; 
lean_dec(x_10);
lean_dec(x_2);
lean_dec(x_1);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_5);
lean_ctor_set(x_32, 1, x_12);
return x_32;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_nat_dec_le(x_3, x_2);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_eq(x_1, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_sub(x_1, x_16);
lean_dec(x_1);
x_18 = lean_ctor_get(x_5, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_5, 1);
lean_inc(x_19);
lean_dec(x_5);
lean_inc(x_10);
x_20 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_exprToSyntax___spec__1___rarg(x_10, x_11, x_12);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_st_ref_get(x_11, x_22);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__6;
lean_inc(x_21);
x_26 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_26, 0, x_21);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_Array_mkArray1___rarg(x_26);
x_28 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__5;
x_29 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_29, 0, x_21);
lean_ctor_set(x_29, 1, x_28);
lean_ctor_set(x_29, 2, x_27);
x_30 = lean_array_push(x_18, x_29);
lean_inc(x_10);
x_31 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_exprToSyntax___spec__1___rarg(x_10, x_11, x_24);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_st_ref_get(x_11, x_33);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
lean_inc(x_32);
x_36 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_36, 0, x_32);
lean_ctor_set(x_36, 1, x_25);
x_37 = l_Array_mkArray1___rarg(x_36);
x_38 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_38, 0, x_32);
lean_ctor_set(x_38, 1, x_28);
lean_ctor_set(x_38, 2, x_37);
x_39 = lean_array_push(x_19, x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_30);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_nat_add(x_2, x_4);
lean_dec(x_2);
x_1 = x_17;
x_2 = x_41;
x_5 = x_40;
x_12 = x_35;
goto _start;
}
else
{
lean_object* x_43; 
lean_dec(x_10);
lean_dec(x_2);
lean_dec(x_1);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_5);
lean_ctor_set(x_43, 1, x_12);
return x_43;
}
}
else
{
lean_object* x_44; 
lean_dec(x_10);
lean_dec(x_2);
lean_dec(x_1);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_5);
lean_ctor_set(x_44, 1, x_12);
return x_44;
}
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("match", 5);
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__1;
x_2 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__2;
x_3 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__3;
x_4 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("null", 4);
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("matchDiscr", 10);
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__1;
x_2 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__2;
x_3 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__3;
x_4 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__6;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("app", 3);
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__1;
x_2 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__2;
x_3 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__3;
x_4 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__8;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("compare", 7);
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__10;
x_2 = l_String_toSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__10;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Deriving_Ord_mkOrdHeader___closed__1;
x_2 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__10;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__13;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__14;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("with", 4);
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("matchAlts", 9);
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__1;
x_2 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__2;
x_3 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__3;
x_4 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__17;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("matchAlt", 8);
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__1;
x_2 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__2;
x_3 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__3;
x_4 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__19;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__21() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("|", 1);
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__22() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Ordering.lt", 11);
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__22;
x_2 = l_String_toSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__24() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Ordering", 8);
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__25() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("lt", 2);
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__24;
x_2 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__25;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__26;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__28() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__26;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__29() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__28;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__30() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__27;
x_2 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__29;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__31() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("=>", 2);
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__32() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Ordering.gt", 11);
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__33() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__32;
x_2 = l_String_toSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__34() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("gt", 2);
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__35() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__24;
x_2 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__34;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__36() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__35;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__37() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__35;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__38() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__37;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__39() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__36;
x_2 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__38;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__40() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Ordering.eq", 11);
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__41() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__40;
x_2 = l_String_toSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__42() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("eq", 2);
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__43() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__24;
x_2 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__42;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__44() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__43;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__45() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__43;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__46() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__45;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__47() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__44;
x_2 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__46;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_inc(x_9);
x_12 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_exprToSyntax___spec__1___rarg(x_9, x_10, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_9, 10);
lean_inc(x_15);
x_16 = lean_st_ref_get(x_10, x_14);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_environment_main_module(x_19);
x_21 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__1;
lean_inc(x_13);
x_22 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_22, 0, x_13);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__4;
x_24 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__5;
lean_inc(x_13);
x_25 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_25, 0, x_13);
lean_ctor_set(x_25, 1, x_23);
lean_ctor_set(x_25, 2, x_24);
x_26 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__12;
lean_inc(x_15);
lean_inc(x_20);
x_27 = l_Lean_addMacroScope(x_20, x_26, x_15);
x_28 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__11;
x_29 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__15;
lean_inc(x_13);
x_30 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_30, 0, x_13);
lean_ctor_set(x_30, 1, x_28);
lean_ctor_set(x_30, 2, x_27);
lean_ctor_set(x_30, 3, x_29);
x_31 = l_Array_mkArray2___rarg(x_1, x_2);
lean_inc(x_13);
x_32 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_32, 0, x_13);
lean_ctor_set(x_32, 1, x_23);
lean_ctor_set(x_32, 2, x_31);
x_33 = l_Array_mkArray2___rarg(x_30, x_32);
x_34 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__9;
lean_inc(x_13);
x_35 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_35, 0, x_13);
lean_ctor_set(x_35, 1, x_34);
lean_ctor_set(x_35, 2, x_33);
lean_inc(x_25);
x_36 = l_Array_mkArray2___rarg(x_25, x_35);
x_37 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__7;
lean_inc(x_13);
x_38 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_38, 0, x_13);
lean_ctor_set(x_38, 1, x_37);
lean_ctor_set(x_38, 2, x_36);
x_39 = l_Array_mkArray1___rarg(x_38);
lean_inc(x_13);
x_40 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_40, 0, x_13);
lean_ctor_set(x_40, 1, x_23);
lean_ctor_set(x_40, 2, x_39);
x_41 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__16;
lean_inc(x_13);
x_42 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_42, 0, x_13);
lean_ctor_set(x_42, 1, x_41);
x_43 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__21;
lean_inc(x_13);
x_44 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_44, 0, x_13);
lean_ctor_set(x_44, 1, x_43);
x_45 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__26;
lean_inc(x_15);
lean_inc(x_20);
x_46 = l_Lean_addMacroScope(x_20, x_45, x_15);
x_47 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__23;
x_48 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__30;
lean_inc(x_13);
x_49 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_49, 0, x_13);
lean_ctor_set(x_49, 1, x_47);
lean_ctor_set(x_49, 2, x_46);
lean_ctor_set(x_49, 3, x_48);
lean_inc(x_49);
x_50 = l_Array_mkArray1___rarg(x_49);
lean_inc(x_13);
x_51 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_51, 0, x_13);
lean_ctor_set(x_51, 1, x_23);
lean_ctor_set(x_51, 2, x_50);
x_52 = l_Array_mkArray1___rarg(x_51);
lean_inc(x_13);
x_53 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_53, 0, x_13);
lean_ctor_set(x_53, 1, x_23);
lean_ctor_set(x_53, 2, x_52);
x_54 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__31;
lean_inc(x_13);
x_55 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_55, 0, x_13);
lean_ctor_set(x_55, 1, x_54);
lean_inc(x_55);
lean_inc(x_44);
x_56 = l_Array_mkArray4___rarg(x_44, x_53, x_55, x_49);
x_57 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__20;
lean_inc(x_13);
x_58 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_58, 0, x_13);
lean_ctor_set(x_58, 1, x_57);
lean_ctor_set(x_58, 2, x_56);
x_59 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__35;
lean_inc(x_15);
lean_inc(x_20);
x_60 = l_Lean_addMacroScope(x_20, x_59, x_15);
x_61 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__33;
x_62 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__39;
lean_inc(x_13);
x_63 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_63, 0, x_13);
lean_ctor_set(x_63, 1, x_61);
lean_ctor_set(x_63, 2, x_60);
lean_ctor_set(x_63, 3, x_62);
lean_inc(x_63);
x_64 = l_Array_mkArray1___rarg(x_63);
lean_inc(x_13);
x_65 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_65, 0, x_13);
lean_ctor_set(x_65, 1, x_23);
lean_ctor_set(x_65, 2, x_64);
x_66 = l_Array_mkArray1___rarg(x_65);
lean_inc(x_13);
x_67 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_67, 0, x_13);
lean_ctor_set(x_67, 1, x_23);
lean_ctor_set(x_67, 2, x_66);
lean_inc(x_55);
lean_inc(x_44);
x_68 = l_Array_mkArray4___rarg(x_44, x_67, x_55, x_63);
lean_inc(x_13);
x_69 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_69, 0, x_13);
lean_ctor_set(x_69, 1, x_57);
lean_ctor_set(x_69, 2, x_68);
x_70 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__43;
x_71 = l_Lean_addMacroScope(x_20, x_70, x_15);
x_72 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__41;
x_73 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__47;
lean_inc(x_13);
x_74 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_74, 0, x_13);
lean_ctor_set(x_74, 1, x_72);
lean_ctor_set(x_74, 2, x_71);
lean_ctor_set(x_74, 3, x_73);
x_75 = l_Array_mkArray1___rarg(x_74);
lean_inc(x_13);
x_76 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_76, 0, x_13);
lean_ctor_set(x_76, 1, x_23);
lean_ctor_set(x_76, 2, x_75);
x_77 = l_Array_mkArray1___rarg(x_76);
lean_inc(x_13);
x_78 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_78, 0, x_13);
lean_ctor_set(x_78, 1, x_23);
lean_ctor_set(x_78, 2, x_77);
x_79 = l_Array_mkArray4___rarg(x_44, x_78, x_55, x_4);
lean_inc(x_13);
x_80 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_80, 0, x_13);
lean_ctor_set(x_80, 1, x_57);
lean_ctor_set(x_80, 2, x_79);
x_81 = l_Array_mkArray3___rarg(x_58, x_69, x_80);
lean_inc(x_13);
x_82 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_82, 0, x_13);
lean_ctor_set(x_82, 1, x_23);
lean_ctor_set(x_82, 2, x_81);
x_83 = l_Array_mkArray1___rarg(x_82);
x_84 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__18;
lean_inc(x_13);
x_85 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_85, 0, x_13);
lean_ctor_set(x_85, 1, x_84);
lean_ctor_set(x_85, 2, x_83);
lean_inc(x_25);
x_86 = l_Array_mkArray6___rarg(x_22, x_25, x_25, x_40, x_42, x_85);
x_87 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__2;
x_88 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_88, 0, x_13);
lean_ctor_set(x_88, 1, x_87);
lean_ctor_set(x_88, 2, x_86);
x_89 = lean_apply_8(x_3, x_88, x_5, x_6, x_7, x_8, x_9, x_10, x_18);
return x_89;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("a", 1);
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("b", 1);
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Init.Util", 9);
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("getElem!", 8);
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("index out of bounds", 19);
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___closed__5;
x_2 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___closed__6;
x_3 = lean_unsigned_to_nat(77u);
x_4 = lean_unsigned_to_nat(36u);
x_5 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___closed__7;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; 
x_16 = lean_nat_dec_le(x_6, x_5);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_nat_dec_eq(x_4, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_94; lean_object* x_95; uint8_t x_96; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_sub(x_4, x_19);
lean_dec(x_4);
x_27 = lean_ctor_get(x_8, 1);
lean_inc(x_27);
x_28 = lean_ctor_get(x_8, 0);
lean_inc(x_28);
lean_dec(x_8);
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_31 = x_27;
} else {
 lean_dec_ref(x_27);
 x_31 = lean_box(0);
}
x_94 = lean_nat_add(x_3, x_5);
x_95 = lean_array_get_size(x_1);
x_96 = lean_nat_dec_lt(x_94, x_95);
lean_dec(x_95);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; 
lean_dec(x_94);
x_97 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___closed__8;
x_98 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_97);
x_32 = x_98;
goto block_93;
}
else
{
lean_object* x_99; 
x_99 = lean_array_fget(x_1, x_94);
lean_dec(x_94);
x_32 = x_99;
goto block_93;
}
block_26:
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_nat_add(x_5, x_7);
lean_dec(x_5);
x_4 = x_20;
x_5 = x_24;
x_8 = x_23;
x_15 = x_22;
goto _start;
}
block_93:
{
lean_object* x_33; 
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_32);
x_33 = lean_infer_type(x_32, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_36 = l_Lean_Meta_isProp(x_34, x_11, x_12, x_13, x_14, x_35);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_64; uint8_t x_65; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_64 = l_Lean_Expr_fvarId_x21(x_32);
x_65 = l_Lean_Expr_hasAnyFVar_visit___at_Lean_Expr_containsFVar___spec__1(x_64, x_2);
lean_dec(x_64);
if (x_65 == 0)
{
uint8_t x_66; 
x_66 = lean_unbox(x_37);
lean_dec(x_37);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_31);
x_67 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___closed__2;
x_68 = l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(x_67, x_13, x_14, x_38);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_71 = lean_mk_syntax_ident(x_69);
x_72 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___closed__4;
x_73 = l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(x_72, x_13, x_14, x_70);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec(x_73);
x_76 = lean_mk_syntax_ident(x_74);
lean_inc(x_71);
x_77 = lean_array_push(x_28, x_71);
lean_inc(x_76);
x_78 = lean_array_push(x_29, x_76);
x_79 = lean_alloc_closure((void*)(l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1), 11, 3);
lean_closure_set(x_79, 0, x_71);
lean_closure_set(x_79, 1, x_76);
lean_closure_set(x_79, 2, x_30);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_77);
lean_ctor_set(x_81, 1, x_80);
x_82 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_82, 0, x_81);
x_21 = x_82;
x_22 = x_75;
goto block_26;
}
else
{
lean_object* x_83; 
x_83 = lean_box(0);
x_39 = x_83;
goto block_63;
}
}
else
{
lean_object* x_84; 
lean_dec(x_37);
x_84 = lean_box(0);
x_39 = x_84;
goto block_63;
}
block_63:
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_39);
lean_inc(x_13);
x_40 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_exprToSyntax___spec__1___rarg(x_13, x_14, x_38);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_st_ref_get(x_14, x_42);
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
lean_dec(x_43);
x_45 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__6;
lean_inc(x_41);
x_46 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_46, 0, x_41);
lean_ctor_set(x_46, 1, x_45);
x_47 = l_Array_mkArray1___rarg(x_46);
x_48 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__5;
x_49 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_49, 0, x_41);
lean_ctor_set(x_49, 1, x_48);
lean_ctor_set(x_49, 2, x_47);
x_50 = lean_array_push(x_28, x_49);
lean_inc(x_13);
x_51 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_exprToSyntax___spec__1___rarg(x_13, x_14, x_44);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = lean_st_ref_get(x_14, x_53);
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
lean_dec(x_54);
lean_inc(x_52);
x_56 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_56, 0, x_52);
lean_ctor_set(x_56, 1, x_45);
x_57 = l_Array_mkArray1___rarg(x_56);
x_58 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_58, 0, x_52);
lean_ctor_set(x_58, 1, x_48);
lean_ctor_set(x_58, 2, x_57);
x_59 = lean_array_push(x_29, x_58);
if (lean_is_scalar(x_31)) {
 x_60 = lean_alloc_ctor(0, 2, 0);
} else {
 x_60 = x_31;
}
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_30);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_50);
lean_ctor_set(x_61, 1, x_60);
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_61);
x_21 = x_62;
x_22 = x_55;
goto block_26;
}
}
else
{
uint8_t x_85; 
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_20);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_5);
x_85 = !lean_is_exclusive(x_36);
if (x_85 == 0)
{
return x_36;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_36, 0);
x_87 = lean_ctor_get(x_36, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_36);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
else
{
uint8_t x_89; 
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_20);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_5);
x_89 = !lean_is_exclusive(x_33);
if (x_89 == 0)
{
return x_33;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_33, 0);
x_91 = lean_ctor_get(x_33, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_33);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
}
}
}
else
{
lean_object* x_100; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_8);
lean_ctor_set(x_100, 1, x_15);
return x_100;
}
}
else
{
lean_object* x_101; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_8);
lean_ctor_set(x_101, 1, x_15);
return x_101;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__6(size_t x_1, size_t x_2, lean_object* x_3) {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; lean_object* x_10; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
x_10 = lean_array_uset(x_7, x_2, x_5);
x_2 = x_9;
x_3 = x_10;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__7___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
static lean_object* _init_l_List_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__7___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_betaReduce___lambda__1___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_List_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__7___lambda__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_betaReduce___lambda__2___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_List_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__7___lambda__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__5;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_List_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__7___lambda__2___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_List_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__7___lambda__1___boxed), 8, 0);
return x_1;
}
}
static lean_object* _init_l_List_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__7___lambda__2___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("explicit", 8);
return x_1;
}
}
static lean_object* _init_l_List_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__7___lambda__2___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__1;
x_2 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__2;
x_3 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__3;
x_4 = l_List_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__7___lambda__2___closed__5;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_List_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__7___lambda__2___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("@", 1);
return x_1;
}
}
static lean_object* _init_l_List_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__7___lambda__2___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_List_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__7___lambda__2___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__43;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_List_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__7___lambda__2___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_List_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__7___lambda__2___closed__9;
x_2 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__46;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_List_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__7___lambda__2___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(",", 1);
return x_1;
}
}
static lean_object* _init_l_List_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__7___lambda__2___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(2);
x_2 = l_List_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__7___lambda__2___closed__11;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_List_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__7___lambda__2___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__7___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = l_List_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__7___lambda__2___closed__1;
x_14 = l_List_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__7___lambda__2___closed__2;
lean_inc(x_11);
lean_inc(x_10);
x_15 = l_Lean_Core_transform___at_Lean_Core_betaReduce___spec__1(x_5, x_13, x_14, x_10, x_11, x_12);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_1, 2);
lean_inc(x_18);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_unsigned_to_nat(1u);
x_21 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__5;
lean_inc(x_10);
lean_inc(x_18);
x_22 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3(x_18, x_19, x_18, x_20, x_21, x_6, x_7, x_8, x_9, x_10, x_11, x_17);
lean_dec(x_18);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_ctor_get(x_1, 1);
lean_inc(x_25);
lean_dec(x_1);
x_26 = l_List_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__7___lambda__2___closed__3;
lean_inc(x_10);
lean_inc(x_25);
x_27 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__4(x_25, x_19, x_25, x_20, x_26, x_6, x_7, x_8, x_9, x_10, x_11, x_24);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = !lean_is_exclusive(x_28);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_31 = lean_ctor_get(x_28, 0);
x_32 = lean_ctor_get(x_28, 1);
x_33 = lean_ctor_get(x_2, 4);
lean_inc(x_33);
lean_dec(x_2);
x_34 = l_List_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__7___lambda__2___closed__4;
lean_ctor_set(x_28, 1, x_34);
lean_ctor_set(x_28, 0, x_32);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_31);
lean_ctor_set(x_35, 1, x_28);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_33);
x_36 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5(x_4, x_16, x_25, x_33, x_19, x_33, x_20, x_35, x_6, x_7, x_8, x_9, x_10, x_11, x_29);
lean_dec(x_33);
lean_dec(x_25);
lean_dec(x_16);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_dec(x_36);
x_40 = lean_ctor_get(x_37, 0);
lean_inc(x_40);
lean_dec(x_37);
x_41 = lean_ctor_get(x_38, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_38, 1);
lean_inc(x_42);
lean_dec(x_38);
lean_inc(x_10);
x_43 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_exprToSyntax___spec__1___rarg(x_10, x_11, x_39);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = lean_st_ref_get(x_11, x_45);
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
lean_dec(x_46);
x_48 = l_List_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__7___lambda__2___closed__7;
lean_inc(x_44);
x_49 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_49, 0, x_44);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_mk_syntax_ident(x_3);
lean_inc(x_50);
x_51 = l_Array_mkArray2___rarg(x_49, x_50);
x_52 = l_List_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__7___lambda__2___closed__6;
lean_inc(x_44);
x_53 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_53, 0, x_44);
lean_ctor_set(x_53, 1, x_52);
lean_ctor_set(x_53, 2, x_51);
x_54 = l_Array_append___rarg(x_21, x_40);
x_55 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__4;
lean_inc(x_44);
x_56 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_56, 0, x_44);
lean_ctor_set(x_56, 1, x_55);
lean_ctor_set(x_56, 2, x_54);
x_57 = l_Array_mkArray2___rarg(x_53, x_56);
x_58 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__9;
x_59 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_59, 0, x_44);
lean_ctor_set(x_59, 1, x_58);
lean_ctor_set(x_59, 2, x_57);
lean_inc(x_10);
x_60 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_exprToSyntax___spec__1___rarg(x_10, x_11, x_47);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_63 = lean_st_ref_get(x_11, x_62);
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
lean_dec(x_63);
lean_inc(x_61);
x_65 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_65, 0, x_61);
lean_ctor_set(x_65, 1, x_48);
x_66 = l_Array_mkArray2___rarg(x_65, x_50);
lean_inc(x_61);
x_67 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_67, 0, x_61);
lean_ctor_set(x_67, 1, x_52);
lean_ctor_set(x_67, 2, x_66);
x_68 = l_Array_append___rarg(x_21, x_41);
lean_inc(x_61);
x_69 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_69, 0, x_61);
lean_ctor_set(x_69, 1, x_55);
lean_ctor_set(x_69, 2, x_68);
x_70 = l_Array_mkArray2___rarg(x_67, x_69);
x_71 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_71, 0, x_61);
lean_ctor_set(x_71, 1, x_58);
lean_ctor_set(x_71, 2, x_70);
x_72 = l_List_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__7___lambda__2___closed__8;
x_73 = lean_array_push(x_72, x_59);
lean_inc(x_71);
lean_inc(x_73);
x_74 = lean_array_push(x_73, x_71);
lean_inc(x_23);
x_75 = l_Array_append___rarg(x_23, x_74);
lean_inc(x_10);
x_76 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_exprToSyntax___spec__1___rarg(x_10, x_11, x_64);
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_79 = lean_st_ref_get(x_11, x_78);
x_80 = lean_ctor_get(x_79, 1);
lean_inc(x_80);
lean_dec(x_79);
x_81 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__6;
lean_inc(x_77);
x_82 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_82, 0, x_77);
lean_ctor_set(x_82, 1, x_81);
x_83 = l_Array_mkArray1___rarg(x_82);
x_84 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__5;
x_85 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_85, 0, x_77);
lean_ctor_set(x_85, 1, x_84);
lean_ctor_set(x_85, 2, x_83);
x_86 = lean_array_push(x_73, x_85);
lean_inc(x_23);
x_87 = l_Array_append___rarg(x_23, x_86);
lean_inc(x_10);
x_88 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_exprToSyntax___spec__1___rarg(x_10, x_11, x_80);
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
lean_dec(x_88);
x_91 = lean_st_ref_get(x_11, x_90);
x_92 = lean_ctor_get(x_91, 1);
lean_inc(x_92);
lean_dec(x_91);
lean_inc(x_89);
x_93 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_93, 0, x_89);
lean_ctor_set(x_93, 1, x_81);
x_94 = l_Array_mkArray1___rarg(x_93);
x_95 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_95, 0, x_89);
lean_ctor_set(x_95, 1, x_84);
lean_ctor_set(x_95, 2, x_94);
x_96 = lean_array_push(x_72, x_95);
x_97 = lean_array_push(x_96, x_71);
x_98 = l_Array_append___rarg(x_23, x_97);
lean_inc(x_10);
x_99 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_exprToSyntax___spec__1___rarg(x_10, x_11, x_92);
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_99, 1);
lean_inc(x_101);
lean_dec(x_99);
x_102 = lean_ctor_get(x_10, 10);
lean_inc(x_102);
x_103 = lean_st_ref_get(x_11, x_101);
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
lean_dec(x_103);
x_106 = lean_ctor_get(x_104, 0);
lean_inc(x_106);
lean_dec(x_104);
x_107 = lean_environment_main_module(x_106);
x_108 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__43;
lean_inc(x_102);
x_109 = l_Lean_addMacroScope(x_107, x_108, x_102);
x_110 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__41;
x_111 = l_List_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__7___lambda__2___closed__10;
x_112 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_112, 0, x_100);
lean_ctor_set(x_112, 1, x_110);
lean_ctor_set(x_112, 2, x_109);
lean_ctor_set(x_112, 3, x_111);
lean_inc(x_11);
lean_inc(x_10);
x_113 = lean_apply_8(x_42, x_112, x_6, x_7, x_8, x_9, x_10, x_11, x_105);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; size_t x_124; size_t x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; size_t x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; uint8_t x_167; 
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_113, 1);
lean_inc(x_115);
lean_dec(x_113);
lean_inc(x_10);
x_116 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_exprToSyntax___spec__1___rarg(x_10, x_11, x_115);
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_116, 1);
lean_inc(x_118);
lean_dec(x_116);
x_119 = lean_st_ref_get(x_11, x_118);
x_120 = lean_ctor_get(x_119, 1);
lean_inc(x_120);
lean_dec(x_119);
x_121 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__21;
lean_inc(x_117);
x_122 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_122, 0, x_117);
lean_ctor_set(x_122, 1, x_121);
x_123 = lean_array_get_size(x_75);
x_124 = lean_usize_of_nat(x_123);
lean_dec(x_123);
x_125 = 0;
x_126 = l_Array_mapMUnsafe_map___at___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___spec__3(x_124, x_125, x_75);
x_127 = l_List_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__7___lambda__2___closed__12;
x_128 = l_Lean_mkSepArray(x_126, x_127);
lean_dec(x_126);
x_129 = l_Array_append___rarg(x_21, x_128);
lean_inc(x_117);
x_130 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_130, 0, x_117);
lean_ctor_set(x_130, 1, x_55);
lean_ctor_set(x_130, 2, x_129);
x_131 = l_Array_mkArray1___rarg(x_130);
lean_inc(x_117);
x_132 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_132, 0, x_117);
lean_ctor_set(x_132, 1, x_55);
lean_ctor_set(x_132, 2, x_131);
x_133 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__31;
lean_inc(x_117);
x_134 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_134, 0, x_117);
lean_ctor_set(x_134, 1, x_133);
x_135 = l_Array_mkArray4___rarg(x_122, x_132, x_134, x_114);
x_136 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__20;
x_137 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_137, 0, x_117);
lean_ctor_set(x_137, 1, x_136);
lean_ctor_set(x_137, 2, x_135);
lean_inc(x_10);
x_138 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_exprToSyntax___spec__1___rarg(x_10, x_11, x_120);
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_138, 1);
lean_inc(x_140);
lean_dec(x_138);
x_141 = lean_st_ref_get(x_11, x_140);
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_141, 1);
lean_inc(x_143);
lean_dec(x_141);
x_144 = lean_ctor_get(x_142, 0);
lean_inc(x_144);
lean_dec(x_142);
x_145 = lean_environment_main_module(x_144);
lean_inc(x_139);
x_146 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_146, 0, x_139);
lean_ctor_set(x_146, 1, x_121);
x_147 = lean_array_get_size(x_87);
x_148 = lean_usize_of_nat(x_147);
lean_dec(x_147);
x_149 = l_Array_mapMUnsafe_map___at___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___spec__3(x_148, x_125, x_87);
x_150 = l_Lean_mkSepArray(x_149, x_127);
lean_dec(x_149);
x_151 = l_Array_append___rarg(x_21, x_150);
lean_inc(x_139);
x_152 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_152, 0, x_139);
lean_ctor_set(x_152, 1, x_55);
lean_ctor_set(x_152, 2, x_151);
x_153 = l_Array_mkArray1___rarg(x_152);
lean_inc(x_139);
x_154 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_154, 0, x_139);
lean_ctor_set(x_154, 1, x_55);
lean_ctor_set(x_154, 2, x_153);
lean_inc(x_139);
x_155 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_155, 0, x_139);
lean_ctor_set(x_155, 1, x_133);
x_156 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__26;
lean_inc(x_102);
x_157 = l_Lean_addMacroScope(x_145, x_156, x_102);
x_158 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__23;
x_159 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__30;
lean_inc(x_139);
x_160 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_160, 0, x_139);
lean_ctor_set(x_160, 1, x_158);
lean_ctor_set(x_160, 2, x_157);
lean_ctor_set(x_160, 3, x_159);
x_161 = l_Array_mkArray4___rarg(x_146, x_154, x_155, x_160);
x_162 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_162, 0, x_139);
lean_ctor_set(x_162, 1, x_136);
lean_ctor_set(x_162, 2, x_161);
x_163 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_exprToSyntax___spec__1___rarg(x_10, x_11, x_143);
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_163, 1);
lean_inc(x_165);
lean_dec(x_163);
x_166 = lean_st_ref_get(x_11, x_165);
lean_dec(x_11);
x_167 = !lean_is_exclusive(x_166);
if (x_167 == 0)
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; size_t x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_168 = lean_ctor_get(x_166, 0);
x_169 = lean_ctor_get(x_168, 0);
lean_inc(x_169);
lean_dec(x_168);
x_170 = lean_environment_main_module(x_169);
lean_inc(x_164);
x_171 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_171, 0, x_164);
lean_ctor_set(x_171, 1, x_121);
x_172 = lean_array_get_size(x_98);
x_173 = lean_usize_of_nat(x_172);
lean_dec(x_172);
x_174 = l_Array_mapMUnsafe_map___at___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___spec__3(x_173, x_125, x_98);
x_175 = l_Lean_mkSepArray(x_174, x_127);
lean_dec(x_174);
x_176 = l_Array_append___rarg(x_21, x_175);
lean_inc(x_164);
x_177 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_177, 0, x_164);
lean_ctor_set(x_177, 1, x_55);
lean_ctor_set(x_177, 2, x_176);
x_178 = l_Array_mkArray1___rarg(x_177);
lean_inc(x_164);
x_179 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_179, 0, x_164);
lean_ctor_set(x_179, 1, x_55);
lean_ctor_set(x_179, 2, x_178);
lean_inc(x_164);
x_180 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_180, 0, x_164);
lean_ctor_set(x_180, 1, x_133);
x_181 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__35;
x_182 = l_Lean_addMacroScope(x_170, x_181, x_102);
x_183 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__33;
x_184 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__39;
lean_inc(x_164);
x_185 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_185, 0, x_164);
lean_ctor_set(x_185, 1, x_183);
lean_ctor_set(x_185, 2, x_182);
lean_ctor_set(x_185, 3, x_184);
x_186 = l_Array_mkArray4___rarg(x_171, x_179, x_180, x_185);
x_187 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_187, 0, x_164);
lean_ctor_set(x_187, 1, x_136);
lean_ctor_set(x_187, 2, x_186);
x_188 = l_List_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__7___lambda__2___closed__13;
x_189 = lean_array_push(x_188, x_137);
x_190 = lean_array_push(x_189, x_162);
x_191 = lean_array_push(x_190, x_187);
lean_ctor_set(x_166, 0, x_191);
return x_166;
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; size_t x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; 
x_192 = lean_ctor_get(x_166, 0);
x_193 = lean_ctor_get(x_166, 1);
lean_inc(x_193);
lean_inc(x_192);
lean_dec(x_166);
x_194 = lean_ctor_get(x_192, 0);
lean_inc(x_194);
lean_dec(x_192);
x_195 = lean_environment_main_module(x_194);
lean_inc(x_164);
x_196 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_196, 0, x_164);
lean_ctor_set(x_196, 1, x_121);
x_197 = lean_array_get_size(x_98);
x_198 = lean_usize_of_nat(x_197);
lean_dec(x_197);
x_199 = l_Array_mapMUnsafe_map___at___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___spec__3(x_198, x_125, x_98);
x_200 = l_Lean_mkSepArray(x_199, x_127);
lean_dec(x_199);
x_201 = l_Array_append___rarg(x_21, x_200);
lean_inc(x_164);
x_202 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_202, 0, x_164);
lean_ctor_set(x_202, 1, x_55);
lean_ctor_set(x_202, 2, x_201);
x_203 = l_Array_mkArray1___rarg(x_202);
lean_inc(x_164);
x_204 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_204, 0, x_164);
lean_ctor_set(x_204, 1, x_55);
lean_ctor_set(x_204, 2, x_203);
lean_inc(x_164);
x_205 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_205, 0, x_164);
lean_ctor_set(x_205, 1, x_133);
x_206 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__35;
x_207 = l_Lean_addMacroScope(x_195, x_206, x_102);
x_208 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__33;
x_209 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__39;
lean_inc(x_164);
x_210 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_210, 0, x_164);
lean_ctor_set(x_210, 1, x_208);
lean_ctor_set(x_210, 2, x_207);
lean_ctor_set(x_210, 3, x_209);
x_211 = l_Array_mkArray4___rarg(x_196, x_204, x_205, x_210);
x_212 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_212, 0, x_164);
lean_ctor_set(x_212, 1, x_136);
lean_ctor_set(x_212, 2, x_211);
x_213 = l_List_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__7___lambda__2___closed__13;
x_214 = lean_array_push(x_213, x_137);
x_215 = lean_array_push(x_214, x_162);
x_216 = lean_array_push(x_215, x_212);
x_217 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_217, 0, x_216);
lean_ctor_set(x_217, 1, x_193);
return x_217;
}
}
else
{
uint8_t x_218; 
lean_dec(x_102);
lean_dec(x_98);
lean_dec(x_87);
lean_dec(x_75);
lean_dec(x_11);
lean_dec(x_10);
x_218 = !lean_is_exclusive(x_113);
if (x_218 == 0)
{
return x_113;
}
else
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; 
x_219 = lean_ctor_get(x_113, 0);
x_220 = lean_ctor_get(x_113, 1);
lean_inc(x_220);
lean_inc(x_219);
lean_dec(x_113);
x_221 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_221, 0, x_219);
lean_ctor_set(x_221, 1, x_220);
return x_221;
}
}
}
else
{
uint8_t x_222; 
lean_dec(x_23);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
x_222 = !lean_is_exclusive(x_36);
if (x_222 == 0)
{
return x_36;
}
else
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; 
x_223 = lean_ctor_get(x_36, 0);
x_224 = lean_ctor_get(x_36, 1);
lean_inc(x_224);
lean_inc(x_223);
lean_dec(x_36);
x_225 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_225, 0, x_223);
lean_ctor_set(x_225, 1, x_224);
return x_225;
}
}
}
else
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; 
x_226 = lean_ctor_get(x_28, 0);
x_227 = lean_ctor_get(x_28, 1);
lean_inc(x_227);
lean_inc(x_226);
lean_dec(x_28);
x_228 = lean_ctor_get(x_2, 4);
lean_inc(x_228);
lean_dec(x_2);
x_229 = l_List_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__7___lambda__2___closed__4;
x_230 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_230, 0, x_227);
lean_ctor_set(x_230, 1, x_229);
x_231 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_231, 0, x_226);
lean_ctor_set(x_231, 1, x_230);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_228);
x_232 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5(x_4, x_16, x_25, x_228, x_19, x_228, x_20, x_231, x_6, x_7, x_8, x_9, x_10, x_11, x_29);
lean_dec(x_228);
lean_dec(x_25);
lean_dec(x_16);
if (lean_obj_tag(x_232) == 0)
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; 
x_233 = lean_ctor_get(x_232, 0);
lean_inc(x_233);
x_234 = lean_ctor_get(x_233, 1);
lean_inc(x_234);
x_235 = lean_ctor_get(x_232, 1);
lean_inc(x_235);
lean_dec(x_232);
x_236 = lean_ctor_get(x_233, 0);
lean_inc(x_236);
lean_dec(x_233);
x_237 = lean_ctor_get(x_234, 0);
lean_inc(x_237);
x_238 = lean_ctor_get(x_234, 1);
lean_inc(x_238);
lean_dec(x_234);
lean_inc(x_10);
x_239 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_exprToSyntax___spec__1___rarg(x_10, x_11, x_235);
x_240 = lean_ctor_get(x_239, 0);
lean_inc(x_240);
x_241 = lean_ctor_get(x_239, 1);
lean_inc(x_241);
lean_dec(x_239);
x_242 = lean_st_ref_get(x_11, x_241);
x_243 = lean_ctor_get(x_242, 1);
lean_inc(x_243);
lean_dec(x_242);
x_244 = l_List_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__7___lambda__2___closed__7;
lean_inc(x_240);
x_245 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_245, 0, x_240);
lean_ctor_set(x_245, 1, x_244);
x_246 = lean_mk_syntax_ident(x_3);
lean_inc(x_246);
x_247 = l_Array_mkArray2___rarg(x_245, x_246);
x_248 = l_List_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__7___lambda__2___closed__6;
lean_inc(x_240);
x_249 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_249, 0, x_240);
lean_ctor_set(x_249, 1, x_248);
lean_ctor_set(x_249, 2, x_247);
x_250 = l_Array_append___rarg(x_21, x_236);
x_251 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__4;
lean_inc(x_240);
x_252 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_252, 0, x_240);
lean_ctor_set(x_252, 1, x_251);
lean_ctor_set(x_252, 2, x_250);
x_253 = l_Array_mkArray2___rarg(x_249, x_252);
x_254 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__9;
x_255 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_255, 0, x_240);
lean_ctor_set(x_255, 1, x_254);
lean_ctor_set(x_255, 2, x_253);
lean_inc(x_10);
x_256 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_exprToSyntax___spec__1___rarg(x_10, x_11, x_243);
x_257 = lean_ctor_get(x_256, 0);
lean_inc(x_257);
x_258 = lean_ctor_get(x_256, 1);
lean_inc(x_258);
lean_dec(x_256);
x_259 = lean_st_ref_get(x_11, x_258);
x_260 = lean_ctor_get(x_259, 1);
lean_inc(x_260);
lean_dec(x_259);
lean_inc(x_257);
x_261 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_261, 0, x_257);
lean_ctor_set(x_261, 1, x_244);
x_262 = l_Array_mkArray2___rarg(x_261, x_246);
lean_inc(x_257);
x_263 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_263, 0, x_257);
lean_ctor_set(x_263, 1, x_248);
lean_ctor_set(x_263, 2, x_262);
x_264 = l_Array_append___rarg(x_21, x_237);
lean_inc(x_257);
x_265 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_265, 0, x_257);
lean_ctor_set(x_265, 1, x_251);
lean_ctor_set(x_265, 2, x_264);
x_266 = l_Array_mkArray2___rarg(x_263, x_265);
x_267 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_267, 0, x_257);
lean_ctor_set(x_267, 1, x_254);
lean_ctor_set(x_267, 2, x_266);
x_268 = l_List_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__7___lambda__2___closed__8;
x_269 = lean_array_push(x_268, x_255);
lean_inc(x_267);
lean_inc(x_269);
x_270 = lean_array_push(x_269, x_267);
lean_inc(x_23);
x_271 = l_Array_append___rarg(x_23, x_270);
lean_inc(x_10);
x_272 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_exprToSyntax___spec__1___rarg(x_10, x_11, x_260);
x_273 = lean_ctor_get(x_272, 0);
lean_inc(x_273);
x_274 = lean_ctor_get(x_272, 1);
lean_inc(x_274);
lean_dec(x_272);
x_275 = lean_st_ref_get(x_11, x_274);
x_276 = lean_ctor_get(x_275, 1);
lean_inc(x_276);
lean_dec(x_275);
x_277 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__6;
lean_inc(x_273);
x_278 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_278, 0, x_273);
lean_ctor_set(x_278, 1, x_277);
x_279 = l_Array_mkArray1___rarg(x_278);
x_280 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__5;
x_281 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_281, 0, x_273);
lean_ctor_set(x_281, 1, x_280);
lean_ctor_set(x_281, 2, x_279);
x_282 = lean_array_push(x_269, x_281);
lean_inc(x_23);
x_283 = l_Array_append___rarg(x_23, x_282);
lean_inc(x_10);
x_284 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_exprToSyntax___spec__1___rarg(x_10, x_11, x_276);
x_285 = lean_ctor_get(x_284, 0);
lean_inc(x_285);
x_286 = lean_ctor_get(x_284, 1);
lean_inc(x_286);
lean_dec(x_284);
x_287 = lean_st_ref_get(x_11, x_286);
x_288 = lean_ctor_get(x_287, 1);
lean_inc(x_288);
lean_dec(x_287);
lean_inc(x_285);
x_289 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_289, 0, x_285);
lean_ctor_set(x_289, 1, x_277);
x_290 = l_Array_mkArray1___rarg(x_289);
x_291 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_291, 0, x_285);
lean_ctor_set(x_291, 1, x_280);
lean_ctor_set(x_291, 2, x_290);
x_292 = lean_array_push(x_268, x_291);
x_293 = lean_array_push(x_292, x_267);
x_294 = l_Array_append___rarg(x_23, x_293);
lean_inc(x_10);
x_295 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_exprToSyntax___spec__1___rarg(x_10, x_11, x_288);
x_296 = lean_ctor_get(x_295, 0);
lean_inc(x_296);
x_297 = lean_ctor_get(x_295, 1);
lean_inc(x_297);
lean_dec(x_295);
x_298 = lean_ctor_get(x_10, 10);
lean_inc(x_298);
x_299 = lean_st_ref_get(x_11, x_297);
x_300 = lean_ctor_get(x_299, 0);
lean_inc(x_300);
x_301 = lean_ctor_get(x_299, 1);
lean_inc(x_301);
lean_dec(x_299);
x_302 = lean_ctor_get(x_300, 0);
lean_inc(x_302);
lean_dec(x_300);
x_303 = lean_environment_main_module(x_302);
x_304 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__43;
lean_inc(x_298);
x_305 = l_Lean_addMacroScope(x_303, x_304, x_298);
x_306 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__41;
x_307 = l_List_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__7___lambda__2___closed__10;
x_308 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_308, 0, x_296);
lean_ctor_set(x_308, 1, x_306);
lean_ctor_set(x_308, 2, x_305);
lean_ctor_set(x_308, 3, x_307);
lean_inc(x_11);
lean_inc(x_10);
x_309 = lean_apply_8(x_238, x_308, x_6, x_7, x_8, x_9, x_10, x_11, x_301);
if (lean_obj_tag(x_309) == 0)
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; size_t x_320; size_t x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; size_t x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; size_t x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; 
x_310 = lean_ctor_get(x_309, 0);
lean_inc(x_310);
x_311 = lean_ctor_get(x_309, 1);
lean_inc(x_311);
lean_dec(x_309);
lean_inc(x_10);
x_312 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_exprToSyntax___spec__1___rarg(x_10, x_11, x_311);
x_313 = lean_ctor_get(x_312, 0);
lean_inc(x_313);
x_314 = lean_ctor_get(x_312, 1);
lean_inc(x_314);
lean_dec(x_312);
x_315 = lean_st_ref_get(x_11, x_314);
x_316 = lean_ctor_get(x_315, 1);
lean_inc(x_316);
lean_dec(x_315);
x_317 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__21;
lean_inc(x_313);
x_318 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_318, 0, x_313);
lean_ctor_set(x_318, 1, x_317);
x_319 = lean_array_get_size(x_271);
x_320 = lean_usize_of_nat(x_319);
lean_dec(x_319);
x_321 = 0;
x_322 = l_Array_mapMUnsafe_map___at___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___spec__3(x_320, x_321, x_271);
x_323 = l_List_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__7___lambda__2___closed__12;
x_324 = l_Lean_mkSepArray(x_322, x_323);
lean_dec(x_322);
x_325 = l_Array_append___rarg(x_21, x_324);
lean_inc(x_313);
x_326 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_326, 0, x_313);
lean_ctor_set(x_326, 1, x_251);
lean_ctor_set(x_326, 2, x_325);
x_327 = l_Array_mkArray1___rarg(x_326);
lean_inc(x_313);
x_328 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_328, 0, x_313);
lean_ctor_set(x_328, 1, x_251);
lean_ctor_set(x_328, 2, x_327);
x_329 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__31;
lean_inc(x_313);
x_330 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_330, 0, x_313);
lean_ctor_set(x_330, 1, x_329);
x_331 = l_Array_mkArray4___rarg(x_318, x_328, x_330, x_310);
x_332 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__20;
x_333 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_333, 0, x_313);
lean_ctor_set(x_333, 1, x_332);
lean_ctor_set(x_333, 2, x_331);
lean_inc(x_10);
x_334 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_exprToSyntax___spec__1___rarg(x_10, x_11, x_316);
x_335 = lean_ctor_get(x_334, 0);
lean_inc(x_335);
x_336 = lean_ctor_get(x_334, 1);
lean_inc(x_336);
lean_dec(x_334);
x_337 = lean_st_ref_get(x_11, x_336);
x_338 = lean_ctor_get(x_337, 0);
lean_inc(x_338);
x_339 = lean_ctor_get(x_337, 1);
lean_inc(x_339);
lean_dec(x_337);
x_340 = lean_ctor_get(x_338, 0);
lean_inc(x_340);
lean_dec(x_338);
x_341 = lean_environment_main_module(x_340);
lean_inc(x_335);
x_342 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_342, 0, x_335);
lean_ctor_set(x_342, 1, x_317);
x_343 = lean_array_get_size(x_283);
x_344 = lean_usize_of_nat(x_343);
lean_dec(x_343);
x_345 = l_Array_mapMUnsafe_map___at___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___spec__3(x_344, x_321, x_283);
x_346 = l_Lean_mkSepArray(x_345, x_323);
lean_dec(x_345);
x_347 = l_Array_append___rarg(x_21, x_346);
lean_inc(x_335);
x_348 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_348, 0, x_335);
lean_ctor_set(x_348, 1, x_251);
lean_ctor_set(x_348, 2, x_347);
x_349 = l_Array_mkArray1___rarg(x_348);
lean_inc(x_335);
x_350 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_350, 0, x_335);
lean_ctor_set(x_350, 1, x_251);
lean_ctor_set(x_350, 2, x_349);
lean_inc(x_335);
x_351 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_351, 0, x_335);
lean_ctor_set(x_351, 1, x_329);
x_352 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__26;
lean_inc(x_298);
x_353 = l_Lean_addMacroScope(x_341, x_352, x_298);
x_354 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__23;
x_355 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__30;
lean_inc(x_335);
x_356 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_356, 0, x_335);
lean_ctor_set(x_356, 1, x_354);
lean_ctor_set(x_356, 2, x_353);
lean_ctor_set(x_356, 3, x_355);
x_357 = l_Array_mkArray4___rarg(x_342, x_350, x_351, x_356);
x_358 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_358, 0, x_335);
lean_ctor_set(x_358, 1, x_332);
lean_ctor_set(x_358, 2, x_357);
x_359 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_exprToSyntax___spec__1___rarg(x_10, x_11, x_339);
x_360 = lean_ctor_get(x_359, 0);
lean_inc(x_360);
x_361 = lean_ctor_get(x_359, 1);
lean_inc(x_361);
lean_dec(x_359);
x_362 = lean_st_ref_get(x_11, x_361);
lean_dec(x_11);
x_363 = lean_ctor_get(x_362, 0);
lean_inc(x_363);
x_364 = lean_ctor_get(x_362, 1);
lean_inc(x_364);
if (lean_is_exclusive(x_362)) {
 lean_ctor_release(x_362, 0);
 lean_ctor_release(x_362, 1);
 x_365 = x_362;
} else {
 lean_dec_ref(x_362);
 x_365 = lean_box(0);
}
x_366 = lean_ctor_get(x_363, 0);
lean_inc(x_366);
lean_dec(x_363);
x_367 = lean_environment_main_module(x_366);
lean_inc(x_360);
x_368 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_368, 0, x_360);
lean_ctor_set(x_368, 1, x_317);
x_369 = lean_array_get_size(x_294);
x_370 = lean_usize_of_nat(x_369);
lean_dec(x_369);
x_371 = l_Array_mapMUnsafe_map___at___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___spec__3(x_370, x_321, x_294);
x_372 = l_Lean_mkSepArray(x_371, x_323);
lean_dec(x_371);
x_373 = l_Array_append___rarg(x_21, x_372);
lean_inc(x_360);
x_374 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_374, 0, x_360);
lean_ctor_set(x_374, 1, x_251);
lean_ctor_set(x_374, 2, x_373);
x_375 = l_Array_mkArray1___rarg(x_374);
lean_inc(x_360);
x_376 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_376, 0, x_360);
lean_ctor_set(x_376, 1, x_251);
lean_ctor_set(x_376, 2, x_375);
lean_inc(x_360);
x_377 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_377, 0, x_360);
lean_ctor_set(x_377, 1, x_329);
x_378 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__35;
x_379 = l_Lean_addMacroScope(x_367, x_378, x_298);
x_380 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__33;
x_381 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__39;
lean_inc(x_360);
x_382 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_382, 0, x_360);
lean_ctor_set(x_382, 1, x_380);
lean_ctor_set(x_382, 2, x_379);
lean_ctor_set(x_382, 3, x_381);
x_383 = l_Array_mkArray4___rarg(x_368, x_376, x_377, x_382);
x_384 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_384, 0, x_360);
lean_ctor_set(x_384, 1, x_332);
lean_ctor_set(x_384, 2, x_383);
x_385 = l_List_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__7___lambda__2___closed__13;
x_386 = lean_array_push(x_385, x_333);
x_387 = lean_array_push(x_386, x_358);
x_388 = lean_array_push(x_387, x_384);
if (lean_is_scalar(x_365)) {
 x_389 = lean_alloc_ctor(0, 2, 0);
} else {
 x_389 = x_365;
}
lean_ctor_set(x_389, 0, x_388);
lean_ctor_set(x_389, 1, x_364);
return x_389;
}
else
{
lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; 
lean_dec(x_298);
lean_dec(x_294);
lean_dec(x_283);
lean_dec(x_271);
lean_dec(x_11);
lean_dec(x_10);
x_390 = lean_ctor_get(x_309, 0);
lean_inc(x_390);
x_391 = lean_ctor_get(x_309, 1);
lean_inc(x_391);
if (lean_is_exclusive(x_309)) {
 lean_ctor_release(x_309, 0);
 lean_ctor_release(x_309, 1);
 x_392 = x_309;
} else {
 lean_dec_ref(x_309);
 x_392 = lean_box(0);
}
if (lean_is_scalar(x_392)) {
 x_393 = lean_alloc_ctor(1, 2, 0);
} else {
 x_393 = x_392;
}
lean_ctor_set(x_393, 0, x_390);
lean_ctor_set(x_393, 1, x_391);
return x_393;
}
}
else
{
lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; 
lean_dec(x_23);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
x_394 = lean_ctor_get(x_232, 0);
lean_inc(x_394);
x_395 = lean_ctor_get(x_232, 1);
lean_inc(x_395);
if (lean_is_exclusive(x_232)) {
 lean_ctor_release(x_232, 0);
 lean_ctor_release(x_232, 1);
 x_396 = x_232;
} else {
 lean_dec_ref(x_232);
 x_396 = lean_box(0);
}
if (lean_is_scalar(x_396)) {
 x_397 = lean_alloc_ctor(1, 2, 0);
} else {
 x_397 = x_396;
}
lean_ctor_set(x_397, 0, x_394);
lean_ctor_set(x_397, 1, x_395);
return x_397;
}
}
}
else
{
uint8_t x_398; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_398 = !lean_is_exclusive(x_15);
if (x_398 == 0)
{
return x_15;
}
else
{
lean_object* x_399; lean_object* x_400; lean_object* x_401; 
x_399 = lean_ctor_get(x_15, 0);
x_400 = lean_ctor_get(x_15, 1);
lean_inc(x_400);
lean_inc(x_399);
lean_dec(x_15);
x_401 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_401, 0, x_399);
lean_ctor_set(x_401, 1, x_400);
return x_401;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_11; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_3);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 1);
lean_inc(x_13);
lean_dec(x_2);
lean_inc(x_4);
lean_inc(x_12);
x_14 = l_Lean_getConstInfoCtor___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__1(x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_17, 2);
lean_inc(x_18);
lean_dec(x_17);
lean_inc(x_1);
x_19 = lean_alloc_closure((void*)(l_List_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__7___lambda__2___boxed), 12, 3);
lean_closure_set(x_19, 0, x_1);
lean_closure_set(x_19, 1, x_15);
lean_closure_set(x_19, 2, x_12);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_20 = l_Lean_Meta_forallTelescopeReducing___at_Lean_Elab_Deriving_mkInductArgNames___spec__2___rarg(x_18, x_19, x_4, x_5, x_6, x_7, x_8, x_9, x_16);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; size_t x_24; size_t x_25; lean_object* x_26; lean_object* x_27; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_array_get_size(x_21);
x_24 = lean_usize_of_nat(x_23);
lean_dec(x_23);
x_25 = 0;
x_26 = l_Array_mapMUnsafe_map___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__6(x_24, x_25, x_21);
x_27 = l_Array_append___rarg(x_3, x_26);
x_2 = x_13;
x_3 = x_27;
x_10 = x_22;
goto _start;
}
else
{
uint8_t x_29; 
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_20);
if (x_29 == 0)
{
return x_20;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_20, 0);
x_31 = lean_ctor_get(x_20, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_20);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
uint8_t x_33; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_14);
if (x_33 == 0)
{
return x_14;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_14, 0);
x_35 = lean_ctor_get(x_14, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_14);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Ord_mkMatch_mkAlts(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_1, 4);
lean_inc(x_9);
x_10 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__5;
x_11 = l_List_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__7(x_1, x_9, x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_array_pop(x_13);
x_15 = lean_array_pop(x_14);
lean_ctor_set(x_11, 0, x_15);
return x_11;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_11, 0);
x_17 = lean_ctor_get(x_11, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_11);
x_18 = lean_array_pop(x_16);
x_19 = lean_array_pop(x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_17);
return x_20;
}
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_11);
if (x_21 == 0)
{
return x_11;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_11, 0);
x_23 = lean_ctor_get(x_11, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_11);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwError___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_getConstInfoCtor___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__6(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__7___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_List_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__7___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__7___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_List_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__7___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Deriving_Ord_mkMatch___spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; lean_object* x_10; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
x_10 = lean_array_uset(x_7, x_2, x_5);
x_2 = x_9;
x_3 = x_10;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Ord_mkMatch(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_inc(x_7);
lean_inc(x_2);
x_10 = l_Lean_Elab_Deriving_mkDiscrs(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_8);
lean_inc(x_7);
x_13 = l_Lean_Elab_Deriving_Ord_mkMatch_mkAlts(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_exprToSyntax___spec__1___rarg(x_7, x_8, x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_st_ref_get(x_8, x_18);
lean_dec(x_8);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; size_t x_28; size_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_21 = lean_ctor_get(x_19, 0);
lean_dec(x_21);
x_22 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__1;
lean_inc(x_17);
x_23 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_23, 0, x_17);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__4;
x_25 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__5;
lean_inc(x_17);
x_26 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_26, 0, x_17);
lean_ctor_set(x_26, 1, x_24);
lean_ctor_set(x_26, 2, x_25);
x_27 = lean_array_get_size(x_11);
x_28 = lean_usize_of_nat(x_27);
lean_dec(x_27);
x_29 = 0;
x_30 = l_Array_mapMUnsafe_map___at_Lean_Elab_Deriving_Ord_mkMatch___spec__1(x_28, x_29, x_11);
x_31 = l_List_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__7___lambda__2___closed__12;
x_32 = l_Lean_mkSepArray(x_30, x_31);
lean_dec(x_30);
x_33 = l_Array_append___rarg(x_25, x_32);
lean_inc(x_17);
x_34 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_34, 0, x_17);
lean_ctor_set(x_34, 1, x_24);
lean_ctor_set(x_34, 2, x_33);
x_35 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__16;
lean_inc(x_17);
x_36 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_36, 0, x_17);
lean_ctor_set(x_36, 1, x_35);
x_37 = l_Array_append___rarg(x_25, x_14);
lean_inc(x_17);
x_38 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_38, 0, x_17);
lean_ctor_set(x_38, 1, x_24);
lean_ctor_set(x_38, 2, x_37);
x_39 = l_Array_mkArray1___rarg(x_38);
x_40 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__18;
lean_inc(x_17);
x_41 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_41, 0, x_17);
lean_ctor_set(x_41, 1, x_40);
lean_ctor_set(x_41, 2, x_39);
lean_inc(x_26);
x_42 = l_Array_mkArray6___rarg(x_23, x_26, x_26, x_34, x_36, x_41);
x_43 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__2;
x_44 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_44, 0, x_17);
lean_ctor_set(x_44, 1, x_43);
lean_ctor_set(x_44, 2, x_42);
lean_ctor_set(x_19, 0, x_44);
return x_19;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; size_t x_52; size_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_45 = lean_ctor_get(x_19, 1);
lean_inc(x_45);
lean_dec(x_19);
x_46 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__1;
lean_inc(x_17);
x_47 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_47, 0, x_17);
lean_ctor_set(x_47, 1, x_46);
x_48 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__4;
x_49 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__5;
lean_inc(x_17);
x_50 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_50, 0, x_17);
lean_ctor_set(x_50, 1, x_48);
lean_ctor_set(x_50, 2, x_49);
x_51 = lean_array_get_size(x_11);
x_52 = lean_usize_of_nat(x_51);
lean_dec(x_51);
x_53 = 0;
x_54 = l_Array_mapMUnsafe_map___at_Lean_Elab_Deriving_Ord_mkMatch___spec__1(x_52, x_53, x_11);
x_55 = l_List_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__7___lambda__2___closed__12;
x_56 = l_Lean_mkSepArray(x_54, x_55);
lean_dec(x_54);
x_57 = l_Array_append___rarg(x_49, x_56);
lean_inc(x_17);
x_58 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_58, 0, x_17);
lean_ctor_set(x_58, 1, x_48);
lean_ctor_set(x_58, 2, x_57);
x_59 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__16;
lean_inc(x_17);
x_60 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_60, 0, x_17);
lean_ctor_set(x_60, 1, x_59);
x_61 = l_Array_append___rarg(x_49, x_14);
lean_inc(x_17);
x_62 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_62, 0, x_17);
lean_ctor_set(x_62, 1, x_48);
lean_ctor_set(x_62, 2, x_61);
x_63 = l_Array_mkArray1___rarg(x_62);
x_64 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__18;
lean_inc(x_17);
x_65 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_65, 0, x_17);
lean_ctor_set(x_65, 1, x_64);
lean_ctor_set(x_65, 2, x_63);
lean_inc(x_50);
x_66 = l_Array_mkArray6___rarg(x_47, x_50, x_50, x_58, x_60, x_65);
x_67 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__2;
x_68 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_68, 0, x_17);
lean_ctor_set(x_68, 1, x_67);
lean_ctor_set(x_68, 2, x_66);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_45);
return x_69;
}
}
else
{
uint8_t x_70; 
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
x_70 = !lean_is_exclusive(x_13);
if (x_70 == 0)
{
return x_13;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_13, 0);
x_72 = lean_ctor_get(x_13, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_13);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Deriving_Ord_mkMatch___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lean_Elab_Deriving_Ord_mkMatch___spec__1(x_4, x_5, x_3);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Command", 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("declaration", 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__1;
x_2 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__2;
x_3 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__1;
x_4 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__2;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("declModifiers", 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__1;
x_2 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__2;
x_3 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__1;
x_4 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__4;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("private", 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__1;
x_2 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__2;
x_3 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__1;
x_4 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__6;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("partial", 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__1;
x_2 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__2;
x_3 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__1;
x_4 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__8;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("def", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__1;
x_2 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__2;
x_3 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__1;
x_4 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__10;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("declId", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__1;
x_2 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__2;
x_3 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__1;
x_4 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__12;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("optDeclSig", 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__1;
x_2 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__2;
x_3 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__1;
x_4 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__14;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("typeSpec", 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__1;
x_2 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__2;
x_3 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__3;
x_4 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__16;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__18() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(":", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__24;
x_2 = l_String_toSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__24;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__20;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__20;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__22;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__21;
x_2 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__23;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__25() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("declValSimple", 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__1;
x_2 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__2;
x_3 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__1;
x_4 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__25;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__27() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(":=", 2);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; uint8_t x_139; 
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
lean_dec(x_1);
x_139 = lean_ctor_get_uint8(x_3, sizeof(void*)*2);
if (x_139 == 0)
{
uint8_t x_140; 
x_140 = lean_ctor_get_uint8(x_4, sizeof(void*)*5);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; uint8_t x_146; 
lean_inc(x_11);
x_141 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_exprToSyntax___spec__1___rarg(x_11, x_12, x_13);
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_141, 1);
lean_inc(x_143);
lean_dec(x_141);
x_144 = lean_ctor_get(x_11, 10);
lean_inc(x_144);
lean_dec(x_11);
x_145 = lean_st_ref_get(x_12, x_143);
x_146 = !lean_is_exclusive(x_145);
if (x_146 == 0)
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_147 = lean_ctor_get(x_145, 0);
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
lean_dec(x_147);
x_149 = lean_environment_main_module(x_148);
x_150 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__4;
x_151 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__5;
lean_inc(x_142);
x_152 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_152, 0, x_142);
lean_ctor_set(x_152, 1, x_150);
lean_ctor_set(x_152, 2, x_151);
x_153 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__6;
lean_inc(x_142);
x_154 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_154, 0, x_142);
lean_ctor_set(x_154, 1, x_153);
x_155 = l_Array_mkArray1___rarg(x_154);
x_156 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__7;
lean_inc(x_142);
x_157 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_157, 0, x_142);
lean_ctor_set(x_157, 1, x_156);
lean_ctor_set(x_157, 2, x_155);
x_158 = l_Array_mkArray1___rarg(x_157);
lean_inc(x_142);
x_159 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_159, 0, x_142);
lean_ctor_set(x_159, 1, x_150);
lean_ctor_set(x_159, 2, x_158);
lean_inc_n(x_152, 5);
x_160 = l_Array_mkArray6___rarg(x_152, x_152, x_159, x_152, x_152, x_152);
x_161 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__5;
lean_inc(x_142);
x_162 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_162, 0, x_142);
lean_ctor_set(x_162, 1, x_161);
lean_ctor_set(x_162, 2, x_160);
x_163 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__10;
lean_inc(x_142);
x_164 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_164, 0, x_142);
lean_ctor_set(x_164, 1, x_163);
x_165 = lean_mk_syntax_ident(x_2);
lean_inc(x_152);
x_166 = l_Array_mkArray2___rarg(x_165, x_152);
x_167 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__13;
lean_inc(x_142);
x_168 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_168, 0, x_142);
lean_ctor_set(x_168, 1, x_167);
lean_ctor_set(x_168, 2, x_166);
x_169 = l_Array_append___rarg(x_151, x_14);
lean_inc(x_142);
x_170 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_170, 0, x_142);
lean_ctor_set(x_170, 1, x_150);
lean_ctor_set(x_170, 2, x_169);
x_171 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__18;
lean_inc(x_142);
x_172 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_172, 0, x_142);
lean_ctor_set(x_172, 1, x_171);
x_173 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__20;
x_174 = l_Lean_addMacroScope(x_149, x_173, x_144);
x_175 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__19;
x_176 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__24;
lean_inc(x_142);
x_177 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_177, 0, x_142);
lean_ctor_set(x_177, 1, x_175);
lean_ctor_set(x_177, 2, x_174);
lean_ctor_set(x_177, 3, x_176);
x_178 = l_Array_mkArray2___rarg(x_172, x_177);
x_179 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__17;
lean_inc(x_142);
x_180 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_180, 0, x_142);
lean_ctor_set(x_180, 1, x_179);
lean_ctor_set(x_180, 2, x_178);
x_181 = l_Array_mkArray1___rarg(x_180);
lean_inc(x_142);
x_182 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_182, 0, x_142);
lean_ctor_set(x_182, 1, x_150);
lean_ctor_set(x_182, 2, x_181);
x_183 = l_Array_mkArray2___rarg(x_170, x_182);
x_184 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__15;
lean_inc(x_142);
x_185 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_185, 0, x_142);
lean_ctor_set(x_185, 1, x_184);
lean_ctor_set(x_185, 2, x_183);
x_186 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__27;
lean_inc(x_142);
x_187 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_187, 0, x_142);
lean_ctor_set(x_187, 1, x_186);
lean_inc(x_152);
x_188 = l_Array_mkArray3___rarg(x_187, x_5, x_152);
x_189 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__26;
lean_inc(x_142);
x_190 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_190, 0, x_142);
lean_ctor_set(x_190, 1, x_189);
lean_ctor_set(x_190, 2, x_188);
lean_inc_n(x_152, 2);
x_191 = l_Array_mkArray7___rarg(x_164, x_168, x_185, x_190, x_152, x_152, x_152);
x_192 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__11;
lean_inc(x_142);
x_193 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_193, 0, x_142);
lean_ctor_set(x_193, 1, x_192);
lean_ctor_set(x_193, 2, x_191);
x_194 = l_Array_mkArray2___rarg(x_162, x_193);
x_195 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__3;
x_196 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_196, 0, x_142);
lean_ctor_set(x_196, 1, x_195);
lean_ctor_set(x_196, 2, x_194);
lean_ctor_set(x_145, 0, x_196);
return x_145;
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; 
x_197 = lean_ctor_get(x_145, 0);
x_198 = lean_ctor_get(x_145, 1);
lean_inc(x_198);
lean_inc(x_197);
lean_dec(x_145);
x_199 = lean_ctor_get(x_197, 0);
lean_inc(x_199);
lean_dec(x_197);
x_200 = lean_environment_main_module(x_199);
x_201 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__4;
x_202 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__5;
lean_inc(x_142);
x_203 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_203, 0, x_142);
lean_ctor_set(x_203, 1, x_201);
lean_ctor_set(x_203, 2, x_202);
x_204 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__6;
lean_inc(x_142);
x_205 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_205, 0, x_142);
lean_ctor_set(x_205, 1, x_204);
x_206 = l_Array_mkArray1___rarg(x_205);
x_207 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__7;
lean_inc(x_142);
x_208 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_208, 0, x_142);
lean_ctor_set(x_208, 1, x_207);
lean_ctor_set(x_208, 2, x_206);
x_209 = l_Array_mkArray1___rarg(x_208);
lean_inc(x_142);
x_210 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_210, 0, x_142);
lean_ctor_set(x_210, 1, x_201);
lean_ctor_set(x_210, 2, x_209);
lean_inc_n(x_203, 5);
x_211 = l_Array_mkArray6___rarg(x_203, x_203, x_210, x_203, x_203, x_203);
x_212 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__5;
lean_inc(x_142);
x_213 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_213, 0, x_142);
lean_ctor_set(x_213, 1, x_212);
lean_ctor_set(x_213, 2, x_211);
x_214 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__10;
lean_inc(x_142);
x_215 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_215, 0, x_142);
lean_ctor_set(x_215, 1, x_214);
x_216 = lean_mk_syntax_ident(x_2);
lean_inc(x_203);
x_217 = l_Array_mkArray2___rarg(x_216, x_203);
x_218 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__13;
lean_inc(x_142);
x_219 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_219, 0, x_142);
lean_ctor_set(x_219, 1, x_218);
lean_ctor_set(x_219, 2, x_217);
x_220 = l_Array_append___rarg(x_202, x_14);
lean_inc(x_142);
x_221 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_221, 0, x_142);
lean_ctor_set(x_221, 1, x_201);
lean_ctor_set(x_221, 2, x_220);
x_222 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__18;
lean_inc(x_142);
x_223 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_223, 0, x_142);
lean_ctor_set(x_223, 1, x_222);
x_224 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__20;
x_225 = l_Lean_addMacroScope(x_200, x_224, x_144);
x_226 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__19;
x_227 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__24;
lean_inc(x_142);
x_228 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_228, 0, x_142);
lean_ctor_set(x_228, 1, x_226);
lean_ctor_set(x_228, 2, x_225);
lean_ctor_set(x_228, 3, x_227);
x_229 = l_Array_mkArray2___rarg(x_223, x_228);
x_230 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__17;
lean_inc(x_142);
x_231 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_231, 0, x_142);
lean_ctor_set(x_231, 1, x_230);
lean_ctor_set(x_231, 2, x_229);
x_232 = l_Array_mkArray1___rarg(x_231);
lean_inc(x_142);
x_233 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_233, 0, x_142);
lean_ctor_set(x_233, 1, x_201);
lean_ctor_set(x_233, 2, x_232);
x_234 = l_Array_mkArray2___rarg(x_221, x_233);
x_235 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__15;
lean_inc(x_142);
x_236 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_236, 0, x_142);
lean_ctor_set(x_236, 1, x_235);
lean_ctor_set(x_236, 2, x_234);
x_237 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__27;
lean_inc(x_142);
x_238 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_238, 0, x_142);
lean_ctor_set(x_238, 1, x_237);
lean_inc(x_203);
x_239 = l_Array_mkArray3___rarg(x_238, x_5, x_203);
x_240 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__26;
lean_inc(x_142);
x_241 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_241, 0, x_142);
lean_ctor_set(x_241, 1, x_240);
lean_ctor_set(x_241, 2, x_239);
lean_inc_n(x_203, 2);
x_242 = l_Array_mkArray7___rarg(x_215, x_219, x_236, x_241, x_203, x_203, x_203);
x_243 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__11;
lean_inc(x_142);
x_244 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_244, 0, x_142);
lean_ctor_set(x_244, 1, x_243);
lean_ctor_set(x_244, 2, x_242);
x_245 = l_Array_mkArray2___rarg(x_213, x_244);
x_246 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__3;
x_247 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_247, 0, x_142);
lean_ctor_set(x_247, 1, x_246);
lean_ctor_set(x_247, 2, x_245);
x_248 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_248, 0, x_247);
lean_ctor_set(x_248, 1, x_198);
return x_248;
}
}
else
{
lean_object* x_249; 
x_249 = lean_box(0);
x_15 = x_249;
goto block_138;
}
}
else
{
lean_object* x_250; 
x_250 = lean_box(0);
x_15 = x_250;
goto block_138;
}
block_138:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
lean_dec(x_15);
lean_inc(x_11);
x_16 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_exprToSyntax___spec__1___rarg(x_11, x_12, x_13);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_11, 10);
lean_inc(x_19);
lean_dec(x_11);
x_20 = lean_st_ref_get(x_12, x_18);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_environment_main_module(x_23);
x_25 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__4;
x_26 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__5;
lean_inc(x_17);
x_27 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_27, 0, x_17);
lean_ctor_set(x_27, 1, x_25);
lean_ctor_set(x_27, 2, x_26);
x_28 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__6;
lean_inc(x_17);
x_29 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_29, 0, x_17);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_Array_mkArray1___rarg(x_29);
x_31 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__7;
lean_inc(x_17);
x_32 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_32, 0, x_17);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set(x_32, 2, x_30);
x_33 = l_Array_mkArray1___rarg(x_32);
lean_inc(x_17);
x_34 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_34, 0, x_17);
lean_ctor_set(x_34, 1, x_25);
lean_ctor_set(x_34, 2, x_33);
x_35 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__8;
lean_inc(x_17);
x_36 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_36, 0, x_17);
lean_ctor_set(x_36, 1, x_35);
x_37 = l_Array_mkArray1___rarg(x_36);
x_38 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__9;
lean_inc(x_17);
x_39 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_39, 0, x_17);
lean_ctor_set(x_39, 1, x_38);
lean_ctor_set(x_39, 2, x_37);
x_40 = l_Array_mkArray1___rarg(x_39);
lean_inc(x_17);
x_41 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_41, 0, x_17);
lean_ctor_set(x_41, 1, x_25);
lean_ctor_set(x_41, 2, x_40);
lean_inc_n(x_27, 4);
x_42 = l_Array_mkArray6___rarg(x_27, x_27, x_34, x_27, x_27, x_41);
x_43 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__5;
lean_inc(x_17);
x_44 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_44, 0, x_17);
lean_ctor_set(x_44, 1, x_43);
lean_ctor_set(x_44, 2, x_42);
x_45 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__10;
lean_inc(x_17);
x_46 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_46, 0, x_17);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_mk_syntax_ident(x_2);
lean_inc(x_27);
x_48 = l_Array_mkArray2___rarg(x_47, x_27);
x_49 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__13;
lean_inc(x_17);
x_50 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_50, 0, x_17);
lean_ctor_set(x_50, 1, x_49);
lean_ctor_set(x_50, 2, x_48);
x_51 = l_Array_append___rarg(x_26, x_14);
lean_inc(x_17);
x_52 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_52, 0, x_17);
lean_ctor_set(x_52, 1, x_25);
lean_ctor_set(x_52, 2, x_51);
x_53 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__18;
lean_inc(x_17);
x_54 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_54, 0, x_17);
lean_ctor_set(x_54, 1, x_53);
x_55 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__20;
x_56 = l_Lean_addMacroScope(x_24, x_55, x_19);
x_57 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__19;
x_58 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__24;
lean_inc(x_17);
x_59 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_59, 0, x_17);
lean_ctor_set(x_59, 1, x_57);
lean_ctor_set(x_59, 2, x_56);
lean_ctor_set(x_59, 3, x_58);
x_60 = l_Array_mkArray2___rarg(x_54, x_59);
x_61 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__17;
lean_inc(x_17);
x_62 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_62, 0, x_17);
lean_ctor_set(x_62, 1, x_61);
lean_ctor_set(x_62, 2, x_60);
x_63 = l_Array_mkArray1___rarg(x_62);
lean_inc(x_17);
x_64 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_64, 0, x_17);
lean_ctor_set(x_64, 1, x_25);
lean_ctor_set(x_64, 2, x_63);
x_65 = l_Array_mkArray2___rarg(x_52, x_64);
x_66 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__15;
lean_inc(x_17);
x_67 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_67, 0, x_17);
lean_ctor_set(x_67, 1, x_66);
lean_ctor_set(x_67, 2, x_65);
x_68 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__27;
lean_inc(x_17);
x_69 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_69, 0, x_17);
lean_ctor_set(x_69, 1, x_68);
lean_inc(x_27);
x_70 = l_Array_mkArray3___rarg(x_69, x_5, x_27);
x_71 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__26;
lean_inc(x_17);
x_72 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_72, 0, x_17);
lean_ctor_set(x_72, 1, x_71);
lean_ctor_set(x_72, 2, x_70);
lean_inc_n(x_27, 2);
x_73 = l_Array_mkArray7___rarg(x_46, x_50, x_67, x_72, x_27, x_27, x_27);
x_74 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__11;
lean_inc(x_17);
x_75 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_75, 0, x_17);
lean_ctor_set(x_75, 1, x_74);
lean_ctor_set(x_75, 2, x_73);
x_76 = l_Array_mkArray2___rarg(x_44, x_75);
x_77 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__3;
x_78 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_78, 0, x_17);
lean_ctor_set(x_78, 1, x_77);
lean_ctor_set(x_78, 2, x_76);
lean_ctor_set(x_20, 0, x_78);
return x_20;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_79 = lean_ctor_get(x_20, 0);
x_80 = lean_ctor_get(x_20, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_20);
x_81 = lean_ctor_get(x_79, 0);
lean_inc(x_81);
lean_dec(x_79);
x_82 = lean_environment_main_module(x_81);
x_83 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__4;
x_84 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__5;
lean_inc(x_17);
x_85 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_85, 0, x_17);
lean_ctor_set(x_85, 1, x_83);
lean_ctor_set(x_85, 2, x_84);
x_86 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__6;
lean_inc(x_17);
x_87 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_87, 0, x_17);
lean_ctor_set(x_87, 1, x_86);
x_88 = l_Array_mkArray1___rarg(x_87);
x_89 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__7;
lean_inc(x_17);
x_90 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_90, 0, x_17);
lean_ctor_set(x_90, 1, x_89);
lean_ctor_set(x_90, 2, x_88);
x_91 = l_Array_mkArray1___rarg(x_90);
lean_inc(x_17);
x_92 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_92, 0, x_17);
lean_ctor_set(x_92, 1, x_83);
lean_ctor_set(x_92, 2, x_91);
x_93 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__8;
lean_inc(x_17);
x_94 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_94, 0, x_17);
lean_ctor_set(x_94, 1, x_93);
x_95 = l_Array_mkArray1___rarg(x_94);
x_96 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__9;
lean_inc(x_17);
x_97 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_97, 0, x_17);
lean_ctor_set(x_97, 1, x_96);
lean_ctor_set(x_97, 2, x_95);
x_98 = l_Array_mkArray1___rarg(x_97);
lean_inc(x_17);
x_99 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_99, 0, x_17);
lean_ctor_set(x_99, 1, x_83);
lean_ctor_set(x_99, 2, x_98);
lean_inc_n(x_85, 4);
x_100 = l_Array_mkArray6___rarg(x_85, x_85, x_92, x_85, x_85, x_99);
x_101 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__5;
lean_inc(x_17);
x_102 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_102, 0, x_17);
lean_ctor_set(x_102, 1, x_101);
lean_ctor_set(x_102, 2, x_100);
x_103 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__10;
lean_inc(x_17);
x_104 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_104, 0, x_17);
lean_ctor_set(x_104, 1, x_103);
x_105 = lean_mk_syntax_ident(x_2);
lean_inc(x_85);
x_106 = l_Array_mkArray2___rarg(x_105, x_85);
x_107 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__13;
lean_inc(x_17);
x_108 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_108, 0, x_17);
lean_ctor_set(x_108, 1, x_107);
lean_ctor_set(x_108, 2, x_106);
x_109 = l_Array_append___rarg(x_84, x_14);
lean_inc(x_17);
x_110 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_110, 0, x_17);
lean_ctor_set(x_110, 1, x_83);
lean_ctor_set(x_110, 2, x_109);
x_111 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__18;
lean_inc(x_17);
x_112 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_112, 0, x_17);
lean_ctor_set(x_112, 1, x_111);
x_113 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__20;
x_114 = l_Lean_addMacroScope(x_82, x_113, x_19);
x_115 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__19;
x_116 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__24;
lean_inc(x_17);
x_117 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_117, 0, x_17);
lean_ctor_set(x_117, 1, x_115);
lean_ctor_set(x_117, 2, x_114);
lean_ctor_set(x_117, 3, x_116);
x_118 = l_Array_mkArray2___rarg(x_112, x_117);
x_119 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__17;
lean_inc(x_17);
x_120 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_120, 0, x_17);
lean_ctor_set(x_120, 1, x_119);
lean_ctor_set(x_120, 2, x_118);
x_121 = l_Array_mkArray1___rarg(x_120);
lean_inc(x_17);
x_122 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_122, 0, x_17);
lean_ctor_set(x_122, 1, x_83);
lean_ctor_set(x_122, 2, x_121);
x_123 = l_Array_mkArray2___rarg(x_110, x_122);
x_124 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__15;
lean_inc(x_17);
x_125 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_125, 0, x_17);
lean_ctor_set(x_125, 1, x_124);
lean_ctor_set(x_125, 2, x_123);
x_126 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__27;
lean_inc(x_17);
x_127 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_127, 0, x_17);
lean_ctor_set(x_127, 1, x_126);
lean_inc(x_85);
x_128 = l_Array_mkArray3___rarg(x_127, x_5, x_85);
x_129 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__26;
lean_inc(x_17);
x_130 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_130, 0, x_17);
lean_ctor_set(x_130, 1, x_129);
lean_ctor_set(x_130, 2, x_128);
lean_inc_n(x_85, 2);
x_131 = l_Array_mkArray7___rarg(x_104, x_108, x_125, x_130, x_85, x_85, x_85);
x_132 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__11;
lean_inc(x_17);
x_133 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_133, 0, x_17);
lean_ctor_set(x_133, 1, x_132);
lean_ctor_set(x_133, 2, x_131);
x_134 = l_Array_mkArray2___rarg(x_102, x_133);
x_135 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__3;
x_136 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_136, 0, x_17);
lean_ctor_set(x_136, 1, x_135);
lean_ctor_set(x_136, 2, x_134);
x_137 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_80);
return x_137;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Ord_mkAuxFunction(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
x_11 = lean_array_get_size(x_10);
x_12 = lean_nat_dec_lt(x_2, x_11);
lean_dec(x_11);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
x_14 = lean_array_get_size(x_13);
x_15 = lean_nat_dec_lt(x_2, x_14);
lean_dec(x_14);
if (x_12 == 0)
{
lean_object* x_73; lean_object* x_74; 
lean_dec(x_10);
x_73 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___closed__8;
x_74 = l_panic___at___private_Init_Prelude_0__Lean_assembleParts___spec__1(x_73);
x_16 = x_74;
goto block_72;
}
else
{
lean_object* x_75; 
x_75 = lean_array_fget(x_10, x_2);
lean_dec(x_10);
x_16 = x_75;
goto block_72;
}
block_72:
{
lean_object* x_17; 
if (x_15 == 0)
{
lean_object* x_69; lean_object* x_70; 
lean_dec(x_13);
lean_dec(x_2);
x_69 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___closed__8;
x_70 = l_panic___at_Lean_Elab_Deriving_mkLocalInstanceLetDecls___spec__1(x_69);
x_17 = x_70;
goto block_68;
}
else
{
lean_object* x_71; 
x_71 = lean_array_fget(x_13, x_2);
lean_dec(x_2);
lean_dec(x_13);
x_17 = x_71;
goto block_68;
}
block_68:
{
lean_object* x_18; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_17);
x_18 = l_Lean_Elab_Deriving_Ord_mkOrdHeader(x_17, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_17);
lean_inc(x_19);
x_21 = l_Lean_Elab_Deriving_Ord_mkMatch(x_19, x_17, x_3, x_4, x_5, x_6, x_7, x_8, x_20);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
if (x_22 == 0)
{
uint8_t x_23; 
x_23 = lean_ctor_get_uint8(x_17, sizeof(void*)*5);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_21, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_21, 1);
lean_inc(x_25);
lean_dec(x_21);
x_26 = lean_box(0);
x_27 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1(x_19, x_16, x_1, x_17, x_24, x_26, x_3, x_4, x_5, x_6, x_7, x_8, x_25);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_17);
lean_dec(x_1);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_21, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_21, 1);
lean_inc(x_29);
lean_dec(x_21);
x_30 = lean_ctor_get(x_19, 1);
lean_inc(x_30);
x_31 = l_Lean_Elab_Deriving_Ord_mkOrdHeader___closed__2;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_32 = l_Lean_Elab_Deriving_mkLocalInstanceLetDecls(x_1, x_31, x_30, x_3, x_4, x_5, x_6, x_7, x_8, x_29);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_35 = l_Lean_Elab_Deriving_mkLet(x_33, x_28, x_3, x_4, x_5, x_6, x_7, x_8, x_34);
lean_dec(x_33);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_box(0);
x_39 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1(x_19, x_16, x_1, x_17, x_36, x_38, x_3, x_4, x_5, x_6, x_7, x_8, x_37);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_17);
lean_dec(x_1);
return x_39;
}
else
{
uint8_t x_40; 
lean_dec(x_28);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_32);
if (x_40 == 0)
{
return x_32;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_32, 0);
x_42 = lean_ctor_get(x_32, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_32);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_44 = lean_ctor_get(x_21, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_21, 1);
lean_inc(x_45);
lean_dec(x_21);
x_46 = lean_ctor_get(x_19, 1);
lean_inc(x_46);
x_47 = l_Lean_Elab_Deriving_Ord_mkOrdHeader___closed__2;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_48 = l_Lean_Elab_Deriving_mkLocalInstanceLetDecls(x_1, x_47, x_46, x_3, x_4, x_5, x_6, x_7, x_8, x_45);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_51 = l_Lean_Elab_Deriving_mkLet(x_49, x_44, x_3, x_4, x_5, x_6, x_7, x_8, x_50);
lean_dec(x_49);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = lean_box(0);
x_55 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1(x_19, x_16, x_1, x_17, x_52, x_54, x_3, x_4, x_5, x_6, x_7, x_8, x_53);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_17);
lean_dec(x_1);
return x_55;
}
else
{
uint8_t x_56; 
lean_dec(x_44);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_56 = !lean_is_exclusive(x_48);
if (x_56 == 0)
{
return x_48;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_48, 0);
x_58 = lean_ctor_get(x_48, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_48);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
}
else
{
uint8_t x_60; 
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_60 = !lean_is_exclusive(x_21);
if (x_60 == 0)
{
return x_21;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_21, 0);
x_62 = lean_ctor_get(x_21, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_21);
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
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_64 = !lean_is_exclusive(x_18);
if (x_64 == 0)
{
return x_18;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_18, 0);
x_66 = lean_ctor_get(x_18, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_18);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMutualBlock___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = lean_nat_dec_le(x_4, x_3);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_nat_dec_eq(x_2, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_sub(x_2, x_17);
lean_dec(x_2);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_3);
lean_inc(x_1);
x_19 = l_Lean_Elab_Deriving_Ord_mkAuxFunction(x_1, x_3, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_array_push(x_6, x_20);
x_23 = lean_nat_add(x_3, x_5);
lean_dec(x_3);
x_2 = x_18;
x_3 = x_23;
x_6 = x_22;
x_13 = x_21;
goto _start;
}
else
{
uint8_t x_25; 
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_19);
if (x_25 == 0)
{
return x_19;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_19, 0);
x_27 = lean_ctor_get(x_19, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_19);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
else
{
lean_object* x_29; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_6);
lean_ctor_set(x_29, 1, x_13);
return x_29;
}
}
else
{
lean_object* x_30; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_6);
lean_ctor_set(x_30, 1, x_13);
return x_30;
}
}
}
static lean_object* _init_l_Lean_Elab_Deriving_Ord_mkMutualBlock___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("mutual", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_Ord_mkMutualBlock___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__1;
x_2 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__2;
x_3 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__1;
x_4 = l_Lean_Elab_Deriving_Ord_mkMutualBlock___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_Ord_mkMutualBlock___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("end", 3);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Ord_mkMutualBlock(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_array_get_size(x_9);
lean_dec(x_9);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_unsigned_to_nat(1u);
x_13 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__5;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_10);
x_14 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMutualBlock___spec__1(x_1, x_10, x_11, x_10, x_12, x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_10);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_exprToSyntax___spec__1___rarg(x_6, x_7, x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_st_ref_get(x_7, x_19);
lean_dec(x_7);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_22 = lean_ctor_get(x_20, 0);
lean_dec(x_22);
x_23 = l_Lean_Elab_Deriving_Ord_mkMutualBlock___closed__1;
lean_inc(x_18);
x_24 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_24, 0, x_18);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Array_append___rarg(x_13, x_15);
x_26 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__4;
lean_inc(x_18);
x_27 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_27, 0, x_18);
lean_ctor_set(x_27, 1, x_26);
lean_ctor_set(x_27, 2, x_25);
x_28 = l_Lean_Elab_Deriving_Ord_mkMutualBlock___closed__3;
lean_inc(x_18);
x_29 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_29, 0, x_18);
lean_ctor_set(x_29, 1, x_28);
lean_inc(x_18);
x_30 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_30, 0, x_18);
lean_ctor_set(x_30, 1, x_26);
lean_ctor_set(x_30, 2, x_13);
lean_inc(x_30);
x_31 = l_Array_mkArray5___rarg(x_24, x_27, x_29, x_30, x_30);
x_32 = l_Lean_Elab_Deriving_Ord_mkMutualBlock___closed__2;
x_33 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_33, 0, x_18);
lean_ctor_set(x_33, 1, x_32);
lean_ctor_set(x_33, 2, x_31);
lean_ctor_set(x_20, 0, x_33);
return x_20;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_34 = lean_ctor_get(x_20, 1);
lean_inc(x_34);
lean_dec(x_20);
x_35 = l_Lean_Elab_Deriving_Ord_mkMutualBlock___closed__1;
lean_inc(x_18);
x_36 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_36, 0, x_18);
lean_ctor_set(x_36, 1, x_35);
x_37 = l_Array_append___rarg(x_13, x_15);
x_38 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__4;
lean_inc(x_18);
x_39 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_39, 0, x_18);
lean_ctor_set(x_39, 1, x_38);
lean_ctor_set(x_39, 2, x_37);
x_40 = l_Lean_Elab_Deriving_Ord_mkMutualBlock___closed__3;
lean_inc(x_18);
x_41 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_41, 0, x_18);
lean_ctor_set(x_41, 1, x_40);
lean_inc(x_18);
x_42 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_42, 0, x_18);
lean_ctor_set(x_42, 1, x_38);
lean_ctor_set(x_42, 2, x_13);
lean_inc(x_42);
x_43 = l_Array_mkArray5___rarg(x_36, x_39, x_41, x_42, x_42);
x_44 = l_Lean_Elab_Deriving_Ord_mkMutualBlock___closed__2;
x_45 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_45, 0, x_18);
lean_ctor_set(x_45, 1, x_44);
lean_ctor_set(x_45, 2, x_43);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_34);
return x_46;
}
}
else
{
uint8_t x_47; 
lean_dec(x_7);
lean_dec(x_6);
x_47 = !lean_is_exclusive(x_14);
if (x_47 == 0)
{
return x_14;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_14, 0);
x_49 = lean_ctor_get(x_14, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_14);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMutualBlock___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMutualBlock___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_5);
lean_dec(x_4);
return x_14;
}
}
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___spec__1(lean_object* x_1, lean_object* x_2) {
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
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_5);
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
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_9);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("ord", 3);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Elab", 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Deriving", 8);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__3;
x_2 = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__4;
x_3 = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("\n", 1);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__6;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("", 0);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__8;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_60 = lean_array_get_size(x_1);
x_61 = lean_unsigned_to_nat(0u);
x_62 = lean_nat_dec_lt(x_61, x_60);
lean_dec(x_60);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; 
x_63 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___closed__8;
x_64 = l_panic___at___private_Init_Prelude_0__Lean_assembleParts___spec__1(x_63);
x_9 = x_64;
goto block_59;
}
else
{
lean_object* x_65; 
x_65 = lean_array_fget(x_1, x_61);
x_9 = x_65;
goto block_59;
}
block_59:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__1;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_11 = l_Lean_Elab_Deriving_mkContext(x_10, x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_12);
x_14 = l_Lean_Elab_Deriving_Ord_mkMutualBlock(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Elab_Deriving_Ord_mkOrdHeader___closed__2;
x_18 = 1;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_19 = l_Lean_Elab_Deriving_mkInstanceCmds(x_12, x_17, x_1, x_18, x_2, x_3, x_4, x_5, x_6, x_7, x_16);
lean_dec(x_12);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__2;
x_23 = lean_array_push(x_22, x_15);
x_24 = l_Array_append___rarg(x_23, x_20);
x_25 = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__5;
x_26 = l_Lean_isTracingEnabledFor___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_25, x_2, x_3, x_4, x_5, x_6, x_7, x_21);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_unbox(x_27);
lean_dec(x_27);
if (x_28 == 0)
{
uint8_t x_29; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_29 = !lean_is_exclusive(x_26);
if (x_29 == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_26, 0);
lean_dec(x_30);
lean_ctor_set(x_26, 0, x_24);
return x_26;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_26, 1);
lean_inc(x_31);
lean_dec(x_26);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_24);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_33 = lean_ctor_get(x_26, 1);
lean_inc(x_33);
lean_dec(x_26);
lean_inc(x_24);
x_34 = lean_array_to_list(lean_box(0), x_24);
x_35 = lean_box(0);
x_36 = l_List_mapTRAux___at___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___spec__1(x_34, x_35);
x_37 = l_Lean_MessageData_ofList(x_36);
lean_dec(x_36);
x_38 = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__7;
x_39 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
x_40 = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__9;
x_41 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_Lean_addTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__2(x_25, x_41, x_2, x_3, x_4, x_5, x_6, x_7, x_33);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_42, 0);
lean_dec(x_44);
lean_ctor_set(x_42, 0, x_24);
return x_42;
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_42, 1);
lean_inc(x_45);
lean_dec(x_42);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_24);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
else
{
uint8_t x_47; 
lean_dec(x_15);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_47 = !lean_is_exclusive(x_19);
if (x_47 == 0)
{
return x_19;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_19, 0);
x_49 = lean_ctor_get(x_19, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_19);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
else
{
uint8_t x_51; 
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_51 = !lean_is_exclusive(x_14);
if (x_51 == 0)
{
return x_14;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_14, 0);
x_53 = lean_ctor_get(x_14, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_14);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
else
{
uint8_t x_55; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_55 = !lean_is_exclusive(x_11);
if (x_55 == 0)
{
return x_11;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_11, 0);
x_57 = lean_ctor_get(x_11, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_11);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at_Lean_Elab_Deriving_Ord_mkOrdInstanceHandler___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_environment_find(x_8, x_1);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; lean_object* x_11; 
x_10 = 0;
x_11 = lean_box(x_10);
lean_ctor_set(x_5, 0, x_11);
return x_5;
}
else
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_9, 0);
lean_inc(x_12);
lean_dec(x_9);
if (lean_obj_tag(x_12) == 5)
{
uint8_t x_13; lean_object* x_14; 
lean_dec(x_12);
x_13 = 1;
x_14 = lean_box(x_13);
lean_ctor_set(x_5, 0, x_14);
return x_5;
}
else
{
uint8_t x_15; lean_object* x_16; 
lean_dec(x_12);
x_15 = 0;
x_16 = lean_box(x_15);
lean_ctor_set(x_5, 0, x_16);
return x_5;
}
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_5, 0);
x_18 = lean_ctor_get(x_5, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_5);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_environment_find(x_19, x_1);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; lean_object* x_22; lean_object* x_23; 
x_21 = 0;
x_22 = lean_box(x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_18);
return x_23;
}
else
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_20, 0);
lean_inc(x_24);
lean_dec(x_20);
if (lean_obj_tag(x_24) == 5)
{
uint8_t x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_24);
x_25 = 1;
x_26 = lean_box(x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_18);
return x_27;
}
else
{
uint8_t x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_24);
x_28 = 0;
x_29 = lean_box(x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_18);
return x_30;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Elab_Deriving_Ord_mkOrdInstanceHandler___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_2, x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_array_uget(x_1, x_2);
x_9 = l_Lean_isInductive___at_Lean_Elab_Deriving_Ord_mkOrdInstanceHandler___spec__1(x_8, x_4, x_5, x_6);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_unbox(x_10);
lean_dec(x_10);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_9);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_9, 0);
lean_dec(x_13);
x_14 = 1;
x_15 = lean_box(x_14);
lean_ctor_set(x_9, 0, x_15);
return x_9;
}
else
{
lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_9, 1);
lean_inc(x_16);
lean_dec(x_9);
x_17 = 1;
x_18 = lean_box(x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_16);
return x_19;
}
}
else
{
lean_object* x_20; size_t x_21; size_t x_22; 
x_20 = lean_ctor_get(x_9, 1);
lean_inc(x_20);
lean_dec(x_9);
x_21 = 1;
x_22 = lean_usize_add(x_2, x_21);
x_2 = x_22;
x_6 = x_20;
goto _start;
}
}
else
{
uint8_t x_24; lean_object* x_25; lean_object* x_26; 
x_24 = 0;
x_25 = lean_box(x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_6);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Ord_mkOrdInstanceHandler(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_73; uint8_t x_74; 
x_5 = lean_array_get_size(x_1);
x_73 = lean_unsigned_to_nat(0u);
x_74 = lean_nat_dec_lt(x_73, x_5);
if (x_74 == 0)
{
uint8_t x_75; 
x_75 = 1;
x_6 = x_75;
x_7 = x_4;
goto block_72;
}
else
{
uint8_t x_76; 
x_76 = lean_nat_dec_le(x_5, x_5);
if (x_76 == 0)
{
uint8_t x_77; 
x_77 = 1;
x_6 = x_77;
x_7 = x_4;
goto block_72;
}
else
{
size_t x_78; size_t x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; 
x_78 = 0;
x_79 = lean_usize_of_nat(x_5);
x_80 = l_Array_anyMUnsafe_any___at_Lean_Elab_Deriving_Ord_mkOrdInstanceHandler___spec__2(x_1, x_78, x_79, x_2, x_3, x_4);
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_unbox(x_81);
lean_dec(x_81);
if (x_82 == 0)
{
lean_object* x_83; uint8_t x_84; 
x_83 = lean_ctor_get(x_80, 1);
lean_inc(x_83);
lean_dec(x_80);
x_84 = 1;
x_6 = x_84;
x_7 = x_83;
goto block_72;
}
else
{
lean_object* x_85; uint8_t x_86; 
x_85 = lean_ctor_get(x_80, 1);
lean_inc(x_85);
lean_dec(x_80);
x_86 = 0;
x_6 = x_86;
x_7 = x_85;
goto block_72;
}
}
}
block_72:
{
if (x_6 == 0)
{
uint8_t x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_8 = 0;
x_9 = lean_box(x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
else
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_nat_dec_lt(x_11, x_5);
lean_dec(x_5);
if (x_12 == 0)
{
uint8_t x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_13 = 0;
x_14 = lean_box(x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_7);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___boxed), 8, 1);
lean_closure_set(x_16, 0, x_1);
lean_inc(x_2);
x_17 = l_Lean_Elab_Command_liftTermElabM___rarg(x_16, x_2, x_3, x_7);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_17, 1);
x_21 = lean_array_get_size(x_19);
x_22 = lean_nat_dec_lt(x_11, x_21);
if (x_22 == 0)
{
uint8_t x_23; lean_object* x_24; 
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_3);
lean_dec(x_2);
x_23 = 1;
x_24 = lean_box(x_23);
lean_ctor_set(x_17, 0, x_24);
return x_17;
}
else
{
uint8_t x_25; 
x_25 = lean_nat_dec_le(x_21, x_21);
if (x_25 == 0)
{
uint8_t x_26; lean_object* x_27; 
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_3);
lean_dec(x_2);
x_26 = 1;
x_27 = lean_box(x_26);
lean_ctor_set(x_17, 0, x_27);
return x_17;
}
else
{
size_t x_28; size_t x_29; lean_object* x_30; lean_object* x_31; 
lean_free_object(x_17);
x_28 = 0;
x_29 = lean_usize_of_nat(x_21);
lean_dec(x_21);
x_30 = lean_box(0);
x_31 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabCommand___spec__19(x_19, x_28, x_29, x_30, x_2, x_3, x_20);
lean_dec(x_19);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_31, 0);
lean_dec(x_33);
x_34 = 1;
x_35 = lean_box(x_34);
lean_ctor_set(x_31, 0, x_35);
return x_31;
}
else
{
lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_31, 1);
lean_inc(x_36);
lean_dec(x_31);
x_37 = 1;
x_38 = lean_box(x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_36);
return x_39;
}
}
else
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_31);
if (x_40 == 0)
{
return x_31;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_31, 0);
x_42 = lean_ctor_get(x_31, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_31);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_44 = lean_ctor_get(x_17, 0);
x_45 = lean_ctor_get(x_17, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_17);
x_46 = lean_array_get_size(x_44);
x_47 = lean_nat_dec_lt(x_11, x_46);
if (x_47 == 0)
{
uint8_t x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_46);
lean_dec(x_44);
lean_dec(x_3);
lean_dec(x_2);
x_48 = 1;
x_49 = lean_box(x_48);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_45);
return x_50;
}
else
{
uint8_t x_51; 
x_51 = lean_nat_dec_le(x_46, x_46);
if (x_51 == 0)
{
uint8_t x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_46);
lean_dec(x_44);
lean_dec(x_3);
lean_dec(x_2);
x_52 = 1;
x_53 = lean_box(x_52);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_45);
return x_54;
}
else
{
size_t x_55; size_t x_56; lean_object* x_57; lean_object* x_58; 
x_55 = 0;
x_56 = lean_usize_of_nat(x_46);
lean_dec(x_46);
x_57 = lean_box(0);
x_58 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabCommand___spec__19(x_44, x_55, x_56, x_57, x_2, x_3, x_45);
lean_dec(x_44);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; 
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
x_61 = 1;
x_62 = lean_box(x_61);
if (lean_is_scalar(x_60)) {
 x_63 = lean_alloc_ctor(0, 2, 0);
} else {
 x_63 = x_60;
}
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_59);
return x_63;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_64 = lean_ctor_get(x_58, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_58, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_66 = x_58;
} else {
 lean_dec_ref(x_58);
 x_66 = lean_box(0);
}
if (lean_is_scalar(x_66)) {
 x_67 = lean_alloc_ctor(1, 2, 0);
} else {
 x_67 = x_66;
}
lean_ctor_set(x_67, 0, x_64);
lean_ctor_set(x_67, 1, x_65);
return x_67;
}
}
}
}
}
else
{
uint8_t x_68; 
lean_dec(x_3);
lean_dec(x_2);
x_68 = !lean_is_exclusive(x_17);
if (x_68 == 0)
{
return x_17;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_17, 0);
x_70 = lean_ctor_get(x_17, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_17);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at_Lean_Elab_Deriving_Ord_mkOrdInstanceHandler___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_isInductive___at_Lean_Elab_Deriving_Ord_mkOrdInstanceHandler___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Elab_Deriving_Ord_mkOrdInstanceHandler___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l_Array_anyMUnsafe_any___at_Lean_Elab_Deriving_Ord_mkOrdInstanceHandler___spec__2(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_9;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_Ord_initFn____x40_Lean_Elab_Deriving_Ord___hyg_2892____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Deriving_Ord_mkOrdInstanceHandler), 4, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Ord_initFn____x40_Lean_Elab_Deriving_Ord___hyg_2892_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Elab_Deriving_Ord_mkOrdHeader___closed__2;
x_3 = l_Lean_Elab_Deriving_Ord_initFn____x40_Lean_Elab_Deriving_Ord___hyg_2892____closed__1;
x_4 = l_Lean_Elab_registerDerivingHandler(x_2, x_3, x_1);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__5;
x_7 = 0;
x_8 = l_Lean_registerTraceClass(x_6, x_7, x_5);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_4);
if (x_9 == 0)
{
return x_4;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_4, 0);
x_11 = lean_ctor_get(x_4, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_4);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Transform(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Deriving_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Deriving_Util(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Deriving_Ord(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Transform(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Deriving_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Deriving_Util(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Deriving_Ord_mkOrdHeader___closed__1 = _init_l_Lean_Elab_Deriving_Ord_mkOrdHeader___closed__1();
lean_mark_persistent(l_Lean_Elab_Deriving_Ord_mkOrdHeader___closed__1);
l_Lean_Elab_Deriving_Ord_mkOrdHeader___closed__2 = _init_l_Lean_Elab_Deriving_Ord_mkOrdHeader___closed__2();
lean_mark_persistent(l_Lean_Elab_Deriving_Ord_mkOrdHeader___closed__2);
l_Lean_getConstInfoCtor___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__1___closed__1 = _init_l_Lean_getConstInfoCtor___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__1___closed__1();
lean_mark_persistent(l_Lean_getConstInfoCtor___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__1___closed__1);
l_Lean_getConstInfoCtor___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__1___closed__2 = _init_l_Lean_getConstInfoCtor___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__1___closed__2();
lean_mark_persistent(l_Lean_getConstInfoCtor___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__1___closed__2);
l_Lean_getConstInfoCtor___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__1___closed__3 = _init_l_Lean_getConstInfoCtor___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__1___closed__3();
lean_mark_persistent(l_Lean_getConstInfoCtor___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__1___closed__3);
l_Lean_getConstInfoCtor___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__1___closed__4 = _init_l_Lean_getConstInfoCtor___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__1___closed__4();
lean_mark_persistent(l_Lean_getConstInfoCtor___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__1___closed__4);
l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__1 = _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__1();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__1);
l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__2 = _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__2();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__2);
l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__3 = _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__3();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__3);
l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__4 = _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__4();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__4);
l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__5 = _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__5();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__5);
l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__6 = _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__6();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__6);
l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__1 = _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__1();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__1);
l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__2 = _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__2();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__2);
l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__3 = _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__3();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__3);
l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__4 = _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__4();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__4);
l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__5 = _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__5();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__5);
l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__6 = _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__6();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__6);
l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__7 = _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__7();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__7);
l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__8 = _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__8();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__8);
l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__9 = _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__9();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__9);
l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__10 = _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__10();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__10);
l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__11 = _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__11();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__11);
l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__12 = _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__12();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__12);
l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__13 = _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__13();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__13);
l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__14 = _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__14();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__14);
l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__15 = _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__15();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__15);
l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__16 = _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__16();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__16);
l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__17 = _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__17();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__17);
l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__18 = _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__18();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__18);
l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__19 = _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__19();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__19);
l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__20 = _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__20();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__20);
l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__21 = _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__21();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__21);
l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__22 = _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__22();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__22);
l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__23 = _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__23();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__23);
l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__24 = _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__24();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__24);
l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__25 = _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__25();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__25);
l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__26 = _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__26();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__26);
l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__27 = _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__27();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__27);
l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__28 = _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__28();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__28);
l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__29 = _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__29();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__29);
l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__30 = _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__30();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__30);
l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__31 = _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__31();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__31);
l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__32 = _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__32();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__32);
l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__33 = _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__33();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__33);
l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__34 = _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__34();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__34);
l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__35 = _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__35();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__35);
l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__36 = _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__36();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__36);
l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__37 = _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__37();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__37);
l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__38 = _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__38();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__38);
l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__39 = _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__39();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__39);
l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__40 = _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__40();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__40);
l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__41 = _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__41();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__41);
l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__42 = _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__42();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__42);
l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__43 = _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__43();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__43);
l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__44 = _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__44();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__44);
l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__45 = _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__45();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__45);
l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__46 = _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__46();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__46);
l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__47 = _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__47();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__47);
l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___closed__1 = _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___closed__1();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___closed__1);
l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___closed__2 = _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___closed__2();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___closed__2);
l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___closed__3 = _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___closed__3();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___closed__3);
l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___closed__4 = _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___closed__4();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___closed__4);
l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___closed__5 = _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___closed__5();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___closed__5);
l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___closed__6 = _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___closed__6();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___closed__6);
l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___closed__7 = _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___closed__7();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___closed__7);
l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___closed__8 = _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___closed__8();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___closed__8);
l_List_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__7___lambda__2___closed__1 = _init_l_List_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__7___lambda__2___closed__1();
lean_mark_persistent(l_List_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__7___lambda__2___closed__1);
l_List_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__7___lambda__2___closed__2 = _init_l_List_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__7___lambda__2___closed__2();
lean_mark_persistent(l_List_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__7___lambda__2___closed__2);
l_List_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__7___lambda__2___closed__3 = _init_l_List_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__7___lambda__2___closed__3();
lean_mark_persistent(l_List_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__7___lambda__2___closed__3);
l_List_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__7___lambda__2___closed__4 = _init_l_List_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__7___lambda__2___closed__4();
lean_mark_persistent(l_List_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__7___lambda__2___closed__4);
l_List_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__7___lambda__2___closed__5 = _init_l_List_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__7___lambda__2___closed__5();
lean_mark_persistent(l_List_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__7___lambda__2___closed__5);
l_List_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__7___lambda__2___closed__6 = _init_l_List_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__7___lambda__2___closed__6();
lean_mark_persistent(l_List_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__7___lambda__2___closed__6);
l_List_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__7___lambda__2___closed__7 = _init_l_List_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__7___lambda__2___closed__7();
lean_mark_persistent(l_List_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__7___lambda__2___closed__7);
l_List_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__7___lambda__2___closed__8 = _init_l_List_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__7___lambda__2___closed__8();
lean_mark_persistent(l_List_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__7___lambda__2___closed__8);
l_List_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__7___lambda__2___closed__9 = _init_l_List_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__7___lambda__2___closed__9();
lean_mark_persistent(l_List_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__7___lambda__2___closed__9);
l_List_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__7___lambda__2___closed__10 = _init_l_List_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__7___lambda__2___closed__10();
lean_mark_persistent(l_List_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__7___lambda__2___closed__10);
l_List_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__7___lambda__2___closed__11 = _init_l_List_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__7___lambda__2___closed__11();
lean_mark_persistent(l_List_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__7___lambda__2___closed__11);
l_List_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__7___lambda__2___closed__12 = _init_l_List_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__7___lambda__2___closed__12();
lean_mark_persistent(l_List_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__7___lambda__2___closed__12);
l_List_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__7___lambda__2___closed__13 = _init_l_List_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__7___lambda__2___closed__13();
lean_mark_persistent(l_List_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__7___lambda__2___closed__13);
l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__1 = _init_l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__1);
l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__2 = _init_l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__2);
l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__3 = _init_l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__3);
l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__4 = _init_l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__4);
l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__5 = _init_l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__5();
lean_mark_persistent(l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__5);
l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__6 = _init_l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__6();
lean_mark_persistent(l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__6);
l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__7 = _init_l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__7();
lean_mark_persistent(l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__7);
l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__8 = _init_l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__8();
lean_mark_persistent(l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__8);
l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__9 = _init_l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__9();
lean_mark_persistent(l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__9);
l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__10 = _init_l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__10();
lean_mark_persistent(l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__10);
l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__11 = _init_l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__11();
lean_mark_persistent(l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__11);
l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__12 = _init_l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__12();
lean_mark_persistent(l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__12);
l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__13 = _init_l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__13();
lean_mark_persistent(l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__13);
l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__14 = _init_l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__14();
lean_mark_persistent(l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__14);
l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__15 = _init_l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__15();
lean_mark_persistent(l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__15);
l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__16 = _init_l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__16();
lean_mark_persistent(l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__16);
l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__17 = _init_l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__17();
lean_mark_persistent(l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__17);
l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__18 = _init_l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__18();
lean_mark_persistent(l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__18);
l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__19 = _init_l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__19();
lean_mark_persistent(l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__19);
l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__20 = _init_l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__20();
lean_mark_persistent(l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__20);
l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__21 = _init_l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__21();
lean_mark_persistent(l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__21);
l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__22 = _init_l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__22();
lean_mark_persistent(l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__22);
l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__23 = _init_l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__23();
lean_mark_persistent(l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__23);
l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__24 = _init_l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__24();
lean_mark_persistent(l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__24);
l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__25 = _init_l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__25();
lean_mark_persistent(l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__25);
l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__26 = _init_l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__26();
lean_mark_persistent(l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__26);
l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__27 = _init_l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__27();
lean_mark_persistent(l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__27);
l_Lean_Elab_Deriving_Ord_mkMutualBlock___closed__1 = _init_l_Lean_Elab_Deriving_Ord_mkMutualBlock___closed__1();
lean_mark_persistent(l_Lean_Elab_Deriving_Ord_mkMutualBlock___closed__1);
l_Lean_Elab_Deriving_Ord_mkMutualBlock___closed__2 = _init_l_Lean_Elab_Deriving_Ord_mkMutualBlock___closed__2();
lean_mark_persistent(l_Lean_Elab_Deriving_Ord_mkMutualBlock___closed__2);
l_Lean_Elab_Deriving_Ord_mkMutualBlock___closed__3 = _init_l_Lean_Elab_Deriving_Ord_mkMutualBlock___closed__3();
lean_mark_persistent(l_Lean_Elab_Deriving_Ord_mkMutualBlock___closed__3);
l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__1 = _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__1);
l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__2 = _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__2);
l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__3 = _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__3);
l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__4 = _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__4);
l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__5 = _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__5();
lean_mark_persistent(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__5);
l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__6 = _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__6();
lean_mark_persistent(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__6);
l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__7 = _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__7();
lean_mark_persistent(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__7);
l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__8 = _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__8();
lean_mark_persistent(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__8);
l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__9 = _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__9();
lean_mark_persistent(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__9);
l_Lean_Elab_Deriving_Ord_initFn____x40_Lean_Elab_Deriving_Ord___hyg_2892____closed__1 = _init_l_Lean_Elab_Deriving_Ord_initFn____x40_Lean_Elab_Deriving_Ord___hyg_2892____closed__1();
lean_mark_persistent(l_Lean_Elab_Deriving_Ord_initFn____x40_Lean_Elab_Deriving_Ord___hyg_2892____closed__1);
res = l_Lean_Elab_Deriving_Ord_initFn____x40_Lean_Elab_Deriving_Ord___hyg_2892_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
