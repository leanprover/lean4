// Lean compiler output
// Module: Lean.Elab.Deriving.DecEq
// Imports: Init Lean.Meta.Transform Lean.Meta.Inductive Lean.Elab.Deriving.Basic Lean.Elab.Deriving.Util
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
lean_object* l_Lean_getConstInfo___at_Lean_Elab_Term_mkConst___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getConstInfo___at_Lean_Elab_elabDeriving___spec__17(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkEnumOfNatThm___closed__1;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__2;
uint8_t l_Lean_Expr_hasAnyFVar_visit___at_Lean_Expr_containsFVar___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkDecEqCmds___closed__5;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__15;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__3___closed__10;
size_t lean_usize_add(size_t, size_t);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__25;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__22;
lean_object* l_Lean_addTrace___at___private_Lean_Elab_Term_0__Lean_Elab_Term_tryCoe___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkEnumOfNat_mkDecTree___closed__4;
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__37;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__55;
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__62;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkEnumOfNatThm___closed__3;
lean_object* l_Lean_getConstInfoInduct___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoForKernelRec___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__54;
static lean_object* l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1___closed__3;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkDecEqCmds___closed__2;
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__14;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__24;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__1;
lean_object* l_Lean_Elab_Command_liftTermElabM___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__7;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__58;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__50;
lean_object* lean_array_uget(lean_object*, size_t);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__17;
uint8_t l_Lean_Expr_isProp(lean_object*);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkEnumOfNatThm___closed__9;
static lean_object* l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___closed__2;
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__2;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__3___closed__7;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__3;
LEAN_EXPORT lean_object* l_List_allM___at_Lean_Elab_Deriving_DecEq_mkDecEqInstanceHandler___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1___closed__6;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__48;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkDecEqCmds___closed__3;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__46;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__12;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__29;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__9;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkEnumOfNatThm___closed__2;
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_registerDerivingHandler(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkEnumOfNatThm___closed__8;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__4;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkEnumOfNat_mkDecTree___closed__6;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__52;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch___closed__1;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__2;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__3;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__18;
lean_object* l_Lean_Meta_compatibleCtors(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Command_mkDefViewOfInstance___spec__11(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch___closed__2;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__16;
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabCommand___spec__20(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__47;
uint8_t lean_name_eq(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__15;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkEnumOfNatThm___closed__4;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__6;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__1;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__28;
static lean_object* l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___closed__1;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__30;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__37;
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
static lean_object* l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___closed__4;
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__26;
lean_object* lean_array_get_size(lean_object*);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch___closed__4;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__7;
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__22;
lean_object* l_Lean_Core_betaReduce___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__19;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__13;
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkEnumOfNat_mkDecTree___closed__5;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkDecEqHeader___closed__2;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__3___closed__11;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkDecEqHeader___closed__1;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkEnumOfNat___lambda__1___closed__3;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__33;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__12;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Deriving_DecEq_mkDecEq___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__5;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__22;
lean_object* lean_string_utf8_byte_size(lean_object*);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__5;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__30;
lean_object* l_Lean_addTrace___at_Lean_Elab_Command_elabCommand___spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__18;
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkEnumOfNatThm___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__53;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__21;
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_DecEq_mkDecEqInstanceHandler___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isEnumType___at_Lean_Elab_Deriving_DecEq_mkDecEqInstanceHandler___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__42;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__42;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__53;
extern lean_object* l_Lean_levelZero;
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__11;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__20;
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_DecEq_mkEnumOfNat_mkDecTree___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__49;
static lean_object* l_Lean_Elab_Deriving_DecEq_initFn____x40_Lean_Elab_Deriving_DecEq___hyg_5366____closed__1;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkEnumOfNat_mkDecTree___closed__1;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__16;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__6;
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addAndCompile___at_Lean_Meta_evalExprCore___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__24;
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Deriving_mkDiscrs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__3___closed__4;
lean_object* l_Lean_Core_withFreshMacroScope___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__6;
static lean_object* l_Lean_getConstInfoCtor___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__1___closed__2;
lean_object* l_Array_mapMUnsafe_map___at___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___spec__3(size_t, size_t, lean_object*);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__48;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__19;
static lean_object* l_Lean_getConstInfoCtor___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__1___closed__1;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__43;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__32;
LEAN_EXPORT lean_object* l_Lean_isEnumType___at_Lean_Elab_Deriving_DecEq_mkDecEqInstanceHandler___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__3___closed__9;
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__3___closed__6;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__23;
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__50;
static lean_object* l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1___closed__7;
static lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__5___closed__1;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__55;
static lean_object* l_Lean_getConstInfoCtor___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__1___closed__3;
lean_object* l_Lean_Elab_Deriving_mkInstanceCmds(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTRAux___at_Lean_Elab_Deriving_DecEq_mkDecEqCmds___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__49;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__56;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__56;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__8;
static lean_object* l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1___closed__10;
lean_object* l_Lean_mkRawNatLit(lean_object*);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkDecEqCmds___closed__7;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__3___closed__8;
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__4;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__3;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_DecEq_mkEnumOfNat___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__25;
static lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__5___closed__2;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__9;
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__14;
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__17;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkEnumOfNat_mkDecTree___closed__2;
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_PrettyPrinter_Delaborator_delabAppMatch___spec__9(size_t, size_t, lean_object*);
lean_object* l_panic___at_Lean_Expr_getRevArg_x21___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_DecEq_mkDecEqCmds(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__11;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__13;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__10;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__41;
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_DecEq_mkAuxFunction___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkEnumOfNatThm___closed__5;
static lean_object* l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1___closed__5;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__8;
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_DecEq_mkEnumOfNat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__13;
lean_object* l_Lean_Elab_addMacroStack___at_Lean_Elab_Term_instAddErrorMessageContextTermElabM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__27;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__10;
static lean_object* l_Lean_getConstInfoCtor___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__1___closed__4;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__5;
static lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__5___closed__4;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__4;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__38;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__21;
LEAN_EXPORT lean_object* l_List_allM___at_Lean_Elab_Deriving_DecEq_mkDecEqInstanceHandler___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMessageContextPartial___at_Lean_Elab_Command_instAddMessageContextCommandElabM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__34;
lean_object* lean_array_to_list(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__18;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkEnumOfNat_mkDecTree___closed__8;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__15;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__20;
lean_object* l_Lean_mkArrow(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkEnumOfNat___lambda__1___closed__2;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__12;
static lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__5___closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_DecEq_mkEnumOfNatThm___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__7;
lean_object* l_panic___at___private_Init_Prelude_0__Lean_assembleParts___spec__1(lean_object*);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkEnumOfNatThm___closed__10;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__31;
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__13;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__35;
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_DecEq_mkEnumOfNat___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkSepArray(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__23;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__3___closed__12;
lean_object* l_Lean_Elab_Command_elabCommand(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkEnumOfNat___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Deriving_DecEq_mkDecEq___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__1;
lean_object* l_panic___at_Lean_Elab_Deriving_mkLocalInstanceLetDecls___spec__1(lean_object*);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__6;
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at_Lean_Elab_Deriving_DecEq_mkDecEq___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_transform___at_Lean_Core_betaReduce___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__45;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__10;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__11;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkDecEqCmds___closed__10;
lean_object* l_Lean_Elab_Deriving_mkContext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__5___closed__8;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__8___boxed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__29;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch___closed__3;
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__36;
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__21;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__51;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__46;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_DecEq_mkDecEqEnum(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__16;
lean_object* l_Lean_Elab_Deriving_mkHeader(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_DecEq_mkDecEqCmds___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_DecEq_mkEnumOfNat_mkDecTree(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__26;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__52;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__51;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__20;
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_redLength___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_DecEq_mkDecEqHeader(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__5___closed__5;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__57;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__4;
lean_object* lean_environment_main_module(lean_object*);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__35;
lean_object* l_Lean_Elab_addMacroStack___at_Lean_Elab_Command_instAddErrorMessageContextCommandElabM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__43;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__45;
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getCurrMacroScope(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkEnumOfNatThm___closed__7;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__19;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__59;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__31;
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__8(size_t, size_t, lean_object*);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__3___closed__3;
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__25;
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Elab_Command_elabCommand___spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__61;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__32;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkEnumOfNatThm___lambda__1___closed__1;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__10;
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_DecEq_initFn____x40_Lean_Elab_Deriving_DecEq___hyg_5366_(lean_object*);
lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_exprToSyntax___spec__1___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__3___closed__14;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__39;
lean_object* l_Lean_Elab_Command_getMainModule___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__39;
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__3___closed__13;
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__5;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__57;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__3;
lean_object* l_Lean_Elab_Command_getRef(lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__5___closed__7;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__27;
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__4;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__14;
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_DecEq_mkDecEq(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_toArrayAux___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_DecEq_mkDecEqCmds___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch___closed__6;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__3;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__47;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__5;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__60;
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_DecEq_mkAuxFunction(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1___closed__1;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__17;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__17;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__58;
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___spec__1___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__7;
static lean_object* l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1___closed__9;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__8;
static lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__5___closed__3;
lean_object* l_Lean_Meta_forallTelescopeReducing___at_Lean_Elab_Deriving_mkInductArgNames___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_getConstInfoInduct___at_Lean_Elab_Deriving_DecEq_mkDecEq___spec__1___closed__2;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__18;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__36;
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at_Lean_Elab_Deriving_DecEq_mkDecEq___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_DecEq_mkEnumOfNatThm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkEnumOfNat_mkDecTree___closed__3;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__9;
lean_object* l_List_lengthTRAux___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__9;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__27;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__40;
static lean_object* l_Lean_getConstInfoInduct___at_Lean_Elab_Deriving_DecEq_mkDecEq___spec__1___closed__1;
lean_object* lean_mk_syntax_ident(lean_object*);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__15;
static lean_object* l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1___closed__2;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__8;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__44;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkEnumOfNat_mkDecTree___closed__7;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__44;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__40;
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_tryCoe___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__12;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__23;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__41;
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkEnumOfNatThm___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___closed__3;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__24;
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_DecEq_mkDecEqInstanceHandler(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__38;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__21;
lean_object* l_Lean_Core_betaReduce___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_isEmpty___rarg(lean_object*);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkDecEqCmds___closed__9;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__11;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__16;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__54;
extern lean_object* l_Lean_levelOne;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__26;
static lean_object* l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1___closed__8;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__7;
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__14;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch___closed__5;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__6;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__28;
static lean_object* l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1___closed__4;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkEnumOfNatThm___closed__6;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkDecEqCmds___closed__6;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__3___closed__5;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__3___closed__2;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkEnumOfNat___closed__1;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__19;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__20;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkDecEqCmds___closed__1;
static lean_object* l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1___closed__11;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__33;
extern lean_object* l_Lean_casesOnSuffix;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__2;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkDecEqCmds___closed__4;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___closed__5;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkDecEqCmds___closed__8;
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__34;
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkDecEqHeader___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("DecidableEq", 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkDecEqHeader___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Deriving_DecEq_mkDecEqHeader___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_DecEq_mkDecEqHeader(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = l_Lean_Elab_Deriving_DecEq_mkDecEqHeader___closed__2;
x_10 = lean_unsigned_to_nat(2u);
x_11 = l_Lean_Elab_Deriving_mkHeader(x_9, x_10, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Parser", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__2;
x_2 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Term", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__4;
x_2 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("let", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__6;
x_2 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__7;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("letDecl", 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__6;
x_2 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__9;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("letIdDecl", 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__6;
x_2 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__11;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("inst", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__13;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__13;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__14;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__13;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("null", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__17;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__20() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(":=", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__21() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("app", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__6;
x_2 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__21;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(5u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__26() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(";", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (x_1 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_5);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
lean_inc(x_10);
x_14 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_exprToSyntax___spec__1___rarg(x_10, x_11, x_12);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_10, 10);
lean_inc(x_17);
lean_dec(x_10);
x_18 = lean_st_ref_get(x_11, x_16);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_environment_main_module(x_21);
x_23 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__7;
lean_inc(x_15);
x_24 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_24, 0, x_15);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__16;
x_26 = l_Lean_addMacroScope(x_22, x_25, x_17);
x_27 = lean_box(0);
x_28 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__15;
lean_inc(x_15);
x_29 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_29, 0, x_15);
lean_ctor_set(x_29, 1, x_28);
lean_ctor_set(x_29, 2, x_26);
lean_ctor_set(x_29, 3, x_27);
x_30 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__18;
x_31 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__19;
lean_inc(x_15);
x_32 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_32, 0, x_15);
lean_ctor_set(x_32, 1, x_30);
lean_ctor_set(x_32, 2, x_31);
x_33 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__20;
lean_inc(x_15);
x_34 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_34, 0, x_15);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_mk_syntax_ident(x_2);
x_36 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__23;
x_37 = lean_array_push(x_36, x_3);
x_38 = lean_array_push(x_37, x_4);
lean_inc(x_15);
x_39 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_39, 0, x_15);
lean_ctor_set(x_39, 1, x_30);
lean_ctor_set(x_39, 2, x_38);
x_40 = lean_array_push(x_36, x_35);
x_41 = lean_array_push(x_40, x_39);
x_42 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__22;
lean_inc(x_15);
x_43 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_43, 0, x_15);
lean_ctor_set(x_43, 1, x_42);
lean_ctor_set(x_43, 2, x_41);
x_44 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__24;
x_45 = lean_array_push(x_44, x_29);
lean_inc(x_32);
x_46 = lean_array_push(x_45, x_32);
x_47 = lean_array_push(x_46, x_32);
x_48 = lean_array_push(x_47, x_34);
x_49 = lean_array_push(x_48, x_43);
x_50 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__12;
lean_inc(x_15);
x_51 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_51, 0, x_15);
lean_ctor_set(x_51, 1, x_50);
lean_ctor_set(x_51, 2, x_49);
x_52 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__25;
x_53 = lean_array_push(x_52, x_51);
x_54 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__10;
lean_inc(x_15);
x_55 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_55, 0, x_15);
lean_ctor_set(x_55, 1, x_54);
lean_ctor_set(x_55, 2, x_53);
x_56 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__26;
lean_inc(x_15);
x_57 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_57, 0, x_15);
lean_ctor_set(x_57, 1, x_56);
x_58 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__27;
x_59 = lean_array_push(x_58, x_24);
x_60 = lean_array_push(x_59, x_55);
x_61 = lean_array_push(x_60, x_57);
x_62 = lean_array_push(x_61, x_5);
x_63 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__8;
x_64 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_64, 0, x_15);
lean_ctor_set(x_64, 1, x_63);
lean_ctor_set(x_64, 2, x_62);
lean_ctor_set(x_18, 0, x_64);
return x_18;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_65 = lean_ctor_get(x_18, 0);
x_66 = lean_ctor_get(x_18, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_18);
x_67 = lean_ctor_get(x_65, 0);
lean_inc(x_67);
lean_dec(x_65);
x_68 = lean_environment_main_module(x_67);
x_69 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__7;
lean_inc(x_15);
x_70 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_70, 0, x_15);
lean_ctor_set(x_70, 1, x_69);
x_71 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__16;
x_72 = l_Lean_addMacroScope(x_68, x_71, x_17);
x_73 = lean_box(0);
x_74 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__15;
lean_inc(x_15);
x_75 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_75, 0, x_15);
lean_ctor_set(x_75, 1, x_74);
lean_ctor_set(x_75, 2, x_72);
lean_ctor_set(x_75, 3, x_73);
x_76 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__18;
x_77 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__19;
lean_inc(x_15);
x_78 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_78, 0, x_15);
lean_ctor_set(x_78, 1, x_76);
lean_ctor_set(x_78, 2, x_77);
x_79 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__20;
lean_inc(x_15);
x_80 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_80, 0, x_15);
lean_ctor_set(x_80, 1, x_79);
x_81 = lean_mk_syntax_ident(x_2);
x_82 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__23;
x_83 = lean_array_push(x_82, x_3);
x_84 = lean_array_push(x_83, x_4);
lean_inc(x_15);
x_85 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_85, 0, x_15);
lean_ctor_set(x_85, 1, x_76);
lean_ctor_set(x_85, 2, x_84);
x_86 = lean_array_push(x_82, x_81);
x_87 = lean_array_push(x_86, x_85);
x_88 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__22;
lean_inc(x_15);
x_89 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_89, 0, x_15);
lean_ctor_set(x_89, 1, x_88);
lean_ctor_set(x_89, 2, x_87);
x_90 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__24;
x_91 = lean_array_push(x_90, x_75);
lean_inc(x_78);
x_92 = lean_array_push(x_91, x_78);
x_93 = lean_array_push(x_92, x_78);
x_94 = lean_array_push(x_93, x_80);
x_95 = lean_array_push(x_94, x_89);
x_96 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__12;
lean_inc(x_15);
x_97 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_97, 0, x_15);
lean_ctor_set(x_97, 1, x_96);
lean_ctor_set(x_97, 2, x_95);
x_98 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__25;
x_99 = lean_array_push(x_98, x_97);
x_100 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__10;
lean_inc(x_15);
x_101 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_101, 0, x_15);
lean_ctor_set(x_101, 1, x_100);
lean_ctor_set(x_101, 2, x_99);
x_102 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__26;
lean_inc(x_15);
x_103 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_103, 0, x_15);
lean_ctor_set(x_103, 1, x_102);
x_104 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__27;
x_105 = lean_array_push(x_104, x_70);
x_106 = lean_array_push(x_105, x_101);
x_107 = lean_array_push(x_106, x_103);
x_108 = lean_array_push(x_107, x_5);
x_109 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__8;
x_110 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_110, 0, x_15);
lean_ctor_set(x_110, 1, x_109);
lean_ctor_set(x_110, 2, x_108);
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_66);
return x_111;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("termDepIfThenElse", 17);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("if", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("h", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__4;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__4;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__5;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__4;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(":", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("term_=_", 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__9;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("=", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("then", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("byTactic", 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__6;
x_2 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__14;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("by", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Tactic", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__4;
x_2 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__17;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("tacticSeq", 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__18;
x_2 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__19;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__21() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("tacticSeq1Indented", 18);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__18;
x_2 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__21;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__23() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("group", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__23;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__25() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("subst", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__18;
x_2 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__25;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__27() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("exact", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__28() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__18;
x_2 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__27;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__29() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("else", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__30() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("isFalse", 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__31() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__30;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__32() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__30;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__31;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__33() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__30;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__34() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Decidable", 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__35() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__34;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__36() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__35;
x_2 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__30;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__37() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__36;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__38() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__37;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__39() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("paren", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__40() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__6;
x_2 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__39;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__41() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("(", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__42() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("intro", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__43() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__18;
x_2 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__42;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__44() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("n", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__45() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__44;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__46() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__44;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__45;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__47() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__44;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__48() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("injection", 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__49() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__18;
x_2 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__48;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__50() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("apply", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__51() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__18;
x_2 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__50;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__52() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("hole", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__53() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__6;
x_2 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__52;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__54() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__55() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("assumption", 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__56() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__18;
x_2 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__55;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__57() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(")", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__58() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_13 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs(x_1, x_2, x_3, x_4, x_5, x_6, x_10, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_10);
x_16 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_exprToSyntax___spec__1___rarg(x_10, x_11, x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_10, 10);
lean_inc(x_19);
x_20 = lean_st_ref_get(x_11, x_18);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_environment_main_module(x_23);
x_25 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__3;
lean_inc(x_17);
x_26 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_26, 0, x_17);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__7;
lean_inc(x_19);
lean_inc(x_24);
x_28 = l_Lean_addMacroScope(x_24, x_27, x_19);
x_29 = lean_box(0);
x_30 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__6;
lean_inc(x_17);
x_31 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_31, 0, x_17);
lean_ctor_set(x_31, 1, x_30);
lean_ctor_set(x_31, 2, x_28);
lean_ctor_set(x_31, 3, x_29);
x_32 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__8;
lean_inc(x_17);
x_33 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_33, 0, x_17);
lean_ctor_set(x_33, 1, x_32);
x_34 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__11;
lean_inc(x_17);
x_35 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_35, 0, x_17);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__12;
x_37 = lean_array_push(x_36, x_7);
x_38 = lean_array_push(x_37, x_35);
x_39 = lean_array_push(x_38, x_8);
x_40 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__10;
lean_inc(x_17);
x_41 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_41, 0, x_17);
lean_ctor_set(x_41, 1, x_40);
lean_ctor_set(x_41, 2, x_39);
x_42 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__13;
lean_inc(x_17);
x_43 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_43, 0, x_17);
lean_ctor_set(x_43, 1, x_42);
x_44 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__16;
lean_inc(x_17);
x_45 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_45, 0, x_17);
lean_ctor_set(x_45, 1, x_44);
x_46 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__25;
lean_inc(x_17);
x_47 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_47, 0, x_17);
lean_ctor_set(x_47, 1, x_46);
x_48 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__25;
lean_inc(x_31);
x_49 = lean_array_push(x_48, x_31);
x_50 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__18;
lean_inc(x_17);
x_51 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_51, 0, x_17);
lean_ctor_set(x_51, 1, x_50);
lean_ctor_set(x_51, 2, x_49);
x_52 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__23;
x_53 = lean_array_push(x_52, x_47);
x_54 = lean_array_push(x_53, x_51);
x_55 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__26;
lean_inc(x_17);
x_56 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_56, 0, x_17);
lean_ctor_set(x_56, 1, x_55);
lean_ctor_set(x_56, 2, x_54);
x_57 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__26;
lean_inc(x_17);
x_58 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_58, 0, x_17);
lean_ctor_set(x_58, 1, x_57);
x_59 = lean_array_push(x_48, x_58);
lean_inc(x_17);
x_60 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_60, 0, x_17);
lean_ctor_set(x_60, 1, x_50);
lean_ctor_set(x_60, 2, x_59);
x_61 = lean_array_push(x_52, x_56);
lean_inc(x_60);
x_62 = lean_array_push(x_61, x_60);
x_63 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__24;
lean_inc(x_17);
x_64 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_64, 0, x_17);
lean_ctor_set(x_64, 1, x_63);
lean_ctor_set(x_64, 2, x_62);
x_65 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__27;
lean_inc(x_17);
x_66 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_66, 0, x_17);
lean_ctor_set(x_66, 1, x_65);
x_67 = lean_array_push(x_52, x_66);
x_68 = lean_array_push(x_67, x_14);
x_69 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__28;
lean_inc(x_17);
x_70 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_70, 0, x_17);
lean_ctor_set(x_70, 1, x_69);
lean_ctor_set(x_70, 2, x_68);
x_71 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__19;
lean_inc(x_17);
x_72 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_72, 0, x_17);
lean_ctor_set(x_72, 1, x_50);
lean_ctor_set(x_72, 2, x_71);
x_73 = lean_array_push(x_52, x_70);
lean_inc(x_72);
x_74 = lean_array_push(x_73, x_72);
lean_inc(x_17);
x_75 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_75, 0, x_17);
lean_ctor_set(x_75, 1, x_63);
lean_ctor_set(x_75, 2, x_74);
x_76 = lean_array_push(x_52, x_64);
x_77 = lean_array_push(x_76, x_75);
lean_inc(x_17);
x_78 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_78, 0, x_17);
lean_ctor_set(x_78, 1, x_50);
lean_ctor_set(x_78, 2, x_77);
x_79 = lean_array_push(x_48, x_78);
x_80 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__22;
lean_inc(x_17);
x_81 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_81, 0, x_17);
lean_ctor_set(x_81, 1, x_80);
lean_ctor_set(x_81, 2, x_79);
x_82 = lean_array_push(x_48, x_81);
x_83 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__20;
lean_inc(x_17);
x_84 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_84, 0, x_17);
lean_ctor_set(x_84, 1, x_83);
lean_ctor_set(x_84, 2, x_82);
x_85 = lean_array_push(x_52, x_45);
lean_inc(x_85);
x_86 = lean_array_push(x_85, x_84);
x_87 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__15;
lean_inc(x_17);
x_88 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_88, 0, x_17);
lean_ctor_set(x_88, 1, x_87);
lean_ctor_set(x_88, 2, x_86);
x_89 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__29;
lean_inc(x_17);
x_90 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_90, 0, x_17);
lean_ctor_set(x_90, 1, x_89);
x_91 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__33;
lean_inc(x_19);
lean_inc(x_24);
x_92 = l_Lean_addMacroScope(x_24, x_91, x_19);
x_93 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__32;
x_94 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__38;
lean_inc(x_17);
x_95 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_95, 0, x_17);
lean_ctor_set(x_95, 1, x_93);
lean_ctor_set(x_95, 2, x_92);
lean_ctor_set(x_95, 3, x_94);
x_96 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__41;
lean_inc(x_17);
x_97 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_97, 0, x_17);
lean_ctor_set(x_97, 1, x_96);
x_98 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__42;
lean_inc(x_17);
x_99 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_99, 0, x_17);
lean_ctor_set(x_99, 1, x_98);
x_100 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__47;
x_101 = l_Lean_addMacroScope(x_24, x_100, x_19);
x_102 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__46;
lean_inc(x_17);
x_103 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_103, 0, x_17);
lean_ctor_set(x_103, 1, x_102);
lean_ctor_set(x_103, 2, x_101);
lean_ctor_set(x_103, 3, x_29);
lean_inc(x_103);
x_104 = lean_array_push(x_48, x_103);
lean_inc(x_17);
x_105 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_105, 0, x_17);
lean_ctor_set(x_105, 1, x_50);
lean_ctor_set(x_105, 2, x_104);
x_106 = lean_array_push(x_52, x_99);
x_107 = lean_array_push(x_106, x_105);
x_108 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__43;
lean_inc(x_17);
x_109 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_109, 0, x_17);
lean_ctor_set(x_109, 1, x_108);
lean_ctor_set(x_109, 2, x_107);
x_110 = lean_array_push(x_52, x_109);
lean_inc(x_60);
x_111 = lean_array_push(x_110, x_60);
lean_inc(x_17);
x_112 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_112, 0, x_17);
lean_ctor_set(x_112, 1, x_63);
lean_ctor_set(x_112, 2, x_111);
x_113 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__48;
lean_inc(x_17);
x_114 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_114, 0, x_17);
lean_ctor_set(x_114, 1, x_113);
x_115 = lean_array_push(x_36, x_114);
x_116 = lean_array_push(x_115, x_103);
lean_inc(x_72);
x_117 = lean_array_push(x_116, x_72);
x_118 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__49;
lean_inc(x_17);
x_119 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_119, 0, x_17);
lean_ctor_set(x_119, 1, x_118);
lean_ctor_set(x_119, 2, x_117);
x_120 = lean_array_push(x_52, x_119);
lean_inc(x_60);
x_121 = lean_array_push(x_120, x_60);
lean_inc(x_17);
x_122 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_122, 0, x_17);
lean_ctor_set(x_122, 1, x_63);
lean_ctor_set(x_122, 2, x_121);
x_123 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__50;
lean_inc(x_17);
x_124 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_124, 0, x_17);
lean_ctor_set(x_124, 1, x_123);
x_125 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__54;
lean_inc(x_17);
x_126 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_126, 0, x_17);
lean_ctor_set(x_126, 1, x_125);
x_127 = lean_array_push(x_48, x_126);
x_128 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__53;
lean_inc(x_17);
x_129 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_129, 0, x_17);
lean_ctor_set(x_129, 1, x_128);
lean_ctor_set(x_129, 2, x_127);
x_130 = lean_array_push(x_48, x_129);
lean_inc(x_17);
x_131 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_131, 0, x_17);
lean_ctor_set(x_131, 1, x_50);
lean_ctor_set(x_131, 2, x_130);
lean_inc(x_31);
x_132 = lean_array_push(x_52, x_31);
x_133 = lean_array_push(x_132, x_131);
x_134 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__22;
lean_inc(x_17);
x_135 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_135, 0, x_17);
lean_ctor_set(x_135, 1, x_134);
lean_ctor_set(x_135, 2, x_133);
x_136 = lean_array_push(x_52, x_124);
x_137 = lean_array_push(x_136, x_135);
x_138 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__51;
lean_inc(x_17);
x_139 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_139, 0, x_17);
lean_ctor_set(x_139, 1, x_138);
lean_ctor_set(x_139, 2, x_137);
x_140 = lean_array_push(x_52, x_139);
x_141 = lean_array_push(x_140, x_60);
lean_inc(x_17);
x_142 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_142, 0, x_17);
lean_ctor_set(x_142, 1, x_63);
lean_ctor_set(x_142, 2, x_141);
x_143 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__55;
lean_inc(x_17);
x_144 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_144, 0, x_17);
lean_ctor_set(x_144, 1, x_143);
x_145 = lean_array_push(x_48, x_144);
x_146 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__56;
lean_inc(x_17);
x_147 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_147, 0, x_17);
lean_ctor_set(x_147, 1, x_146);
lean_ctor_set(x_147, 2, x_145);
x_148 = lean_array_push(x_52, x_147);
lean_inc(x_72);
x_149 = lean_array_push(x_148, x_72);
lean_inc(x_17);
x_150 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_150, 0, x_17);
lean_ctor_set(x_150, 1, x_63);
lean_ctor_set(x_150, 2, x_149);
x_151 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__27;
x_152 = lean_array_push(x_151, x_112);
x_153 = lean_array_push(x_152, x_122);
x_154 = lean_array_push(x_153, x_142);
x_155 = lean_array_push(x_154, x_150);
lean_inc(x_17);
x_156 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_156, 0, x_17);
lean_ctor_set(x_156, 1, x_50);
lean_ctor_set(x_156, 2, x_155);
x_157 = lean_array_push(x_48, x_156);
lean_inc(x_17);
x_158 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_158, 0, x_17);
lean_ctor_set(x_158, 1, x_80);
lean_ctor_set(x_158, 2, x_157);
x_159 = lean_array_push(x_48, x_158);
lean_inc(x_17);
x_160 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_160, 0, x_17);
lean_ctor_set(x_160, 1, x_83);
lean_ctor_set(x_160, 2, x_159);
x_161 = lean_array_push(x_85, x_160);
lean_inc(x_17);
x_162 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_162, 0, x_17);
lean_ctor_set(x_162, 1, x_87);
lean_ctor_set(x_162, 2, x_161);
x_163 = lean_array_push(x_52, x_162);
x_164 = lean_array_push(x_163, x_72);
lean_inc(x_17);
x_165 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_165, 0, x_17);
lean_ctor_set(x_165, 1, x_50);
lean_ctor_set(x_165, 2, x_164);
x_166 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__57;
lean_inc(x_17);
x_167 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_167, 0, x_17);
lean_ctor_set(x_167, 1, x_166);
x_168 = lean_array_push(x_36, x_97);
x_169 = lean_array_push(x_168, x_165);
x_170 = lean_array_push(x_169, x_167);
x_171 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__40;
lean_inc(x_17);
x_172 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_172, 0, x_17);
lean_ctor_set(x_172, 1, x_171);
lean_ctor_set(x_172, 2, x_170);
x_173 = lean_array_push(x_48, x_172);
lean_inc(x_17);
x_174 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_174, 0, x_17);
lean_ctor_set(x_174, 1, x_50);
lean_ctor_set(x_174, 2, x_173);
x_175 = lean_array_push(x_52, x_95);
x_176 = lean_array_push(x_175, x_174);
lean_inc(x_17);
x_177 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_177, 0, x_17);
lean_ctor_set(x_177, 1, x_134);
lean_ctor_set(x_177, 2, x_176);
x_178 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__58;
x_179 = lean_array_push(x_178, x_26);
x_180 = lean_array_push(x_179, x_31);
x_181 = lean_array_push(x_180, x_33);
x_182 = lean_array_push(x_181, x_41);
x_183 = lean_array_push(x_182, x_43);
x_184 = lean_array_push(x_183, x_88);
x_185 = lean_array_push(x_184, x_90);
x_186 = lean_array_push(x_185, x_177);
x_187 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__2;
x_188 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_188, 0, x_17);
lean_ctor_set(x_188, 1, x_187);
lean_ctor_set(x_188, 2, x_186);
x_189 = lean_apply_8(x_9, x_188, x_3, x_4, x_5, x_6, x_10, x_11, x_22);
return x_189;
}
else
{
uint8_t x_190; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_190 = !lean_is_exclusive(x_13);
if (x_190 == 0)
{
return x_13;
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_191 = lean_ctor_get(x_13, 0);
x_192 = lean_ctor_get(x_13, 1);
lean_inc(x_192);
lean_inc(x_191);
lean_dec(x_13);
x_193 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_193, 0, x_191);
lean_ctor_set(x_193, 1, x_192);
return x_193;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("have", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__6;
x_2 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__3___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("haveDecl", 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__6;
x_2 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__3___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__3___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("haveIdDecl", 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__3___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__6;
x_2 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__3___closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__3___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("typeSpec", 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__3___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__6;
x_2 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__3___closed__7;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__3___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("rfl", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__3___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__3___closed__9;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__3___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__3___closed__9;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__3___closed__10;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__3___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__3___closed__9;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__3___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__3___closed__12;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__3___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__3___closed__13;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_13 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs(x_1, x_2, x_3, x_4, x_5, x_6, x_10, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_10);
x_16 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_exprToSyntax___spec__1___rarg(x_10, x_11, x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_10, 10);
lean_inc(x_19);
x_20 = lean_st_ref_get(x_11, x_18);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_environment_main_module(x_23);
x_25 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__3___closed__1;
lean_inc(x_17);
x_26 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_26, 0, x_17);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__7;
lean_inc(x_19);
lean_inc(x_24);
x_28 = l_Lean_addMacroScope(x_24, x_27, x_19);
x_29 = lean_box(0);
x_30 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__6;
lean_inc(x_17);
x_31 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_31, 0, x_17);
lean_ctor_set(x_31, 1, x_30);
lean_ctor_set(x_31, 2, x_28);
lean_ctor_set(x_31, 3, x_29);
x_32 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__18;
x_33 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__19;
lean_inc(x_17);
x_34 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_34, 0, x_17);
lean_ctor_set(x_34, 1, x_32);
lean_ctor_set(x_34, 2, x_33);
x_35 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__23;
lean_inc(x_31);
x_36 = lean_array_push(x_35, x_31);
lean_inc(x_34);
x_37 = lean_array_push(x_36, x_34);
lean_inc(x_17);
x_38 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_38, 0, x_17);
lean_ctor_set(x_38, 1, x_32);
lean_ctor_set(x_38, 2, x_37);
x_39 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__8;
lean_inc(x_17);
x_40 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_40, 0, x_17);
lean_ctor_set(x_40, 1, x_39);
x_41 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__11;
lean_inc(x_17);
x_42 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_42, 0, x_17);
lean_ctor_set(x_42, 1, x_41);
x_43 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__12;
x_44 = lean_array_push(x_43, x_7);
x_45 = lean_array_push(x_44, x_42);
x_46 = lean_array_push(x_45, x_8);
x_47 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__10;
lean_inc(x_17);
x_48 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_48, 0, x_17);
lean_ctor_set(x_48, 1, x_47);
lean_ctor_set(x_48, 2, x_46);
x_49 = lean_array_push(x_35, x_40);
x_50 = lean_array_push(x_49, x_48);
x_51 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__3___closed__8;
lean_inc(x_17);
x_52 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_52, 0, x_17);
lean_ctor_set(x_52, 1, x_51);
lean_ctor_set(x_52, 2, x_50);
x_53 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__25;
x_54 = lean_array_push(x_53, x_52);
lean_inc(x_17);
x_55 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_55, 0, x_17);
lean_ctor_set(x_55, 1, x_32);
lean_ctor_set(x_55, 2, x_54);
x_56 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__20;
lean_inc(x_17);
x_57 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_57, 0, x_17);
lean_ctor_set(x_57, 1, x_56);
x_58 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__3___closed__12;
x_59 = l_Lean_addMacroScope(x_24, x_58, x_19);
x_60 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__3___closed__11;
x_61 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__3___closed__14;
lean_inc(x_17);
x_62 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_62, 0, x_17);
lean_ctor_set(x_62, 1, x_60);
lean_ctor_set(x_62, 2, x_59);
lean_ctor_set(x_62, 3, x_61);
x_63 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__27;
x_64 = lean_array_push(x_63, x_38);
x_65 = lean_array_push(x_64, x_55);
x_66 = lean_array_push(x_65, x_57);
x_67 = lean_array_push(x_66, x_62);
x_68 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__3___closed__6;
lean_inc(x_17);
x_69 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_69, 0, x_17);
lean_ctor_set(x_69, 1, x_68);
lean_ctor_set(x_69, 2, x_67);
x_70 = lean_array_push(x_53, x_69);
x_71 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__3___closed__4;
lean_inc(x_17);
x_72 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_72, 0, x_17);
lean_ctor_set(x_72, 1, x_71);
lean_ctor_set(x_72, 2, x_70);
x_73 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__26;
lean_inc(x_17);
x_74 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_74, 0, x_17);
lean_ctor_set(x_74, 1, x_73);
x_75 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__16;
lean_inc(x_17);
x_76 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_76, 0, x_17);
lean_ctor_set(x_76, 1, x_75);
x_77 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__25;
lean_inc(x_17);
x_78 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_78, 0, x_17);
lean_ctor_set(x_78, 1, x_77);
x_79 = lean_array_push(x_53, x_31);
lean_inc(x_17);
x_80 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_80, 0, x_17);
lean_ctor_set(x_80, 1, x_32);
lean_ctor_set(x_80, 2, x_79);
x_81 = lean_array_push(x_35, x_78);
x_82 = lean_array_push(x_81, x_80);
x_83 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__26;
lean_inc(x_17);
x_84 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_84, 0, x_17);
lean_ctor_set(x_84, 1, x_83);
lean_ctor_set(x_84, 2, x_82);
lean_inc(x_74);
x_85 = lean_array_push(x_53, x_74);
lean_inc(x_17);
x_86 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_86, 0, x_17);
lean_ctor_set(x_86, 1, x_32);
lean_ctor_set(x_86, 2, x_85);
x_87 = lean_array_push(x_35, x_84);
x_88 = lean_array_push(x_87, x_86);
x_89 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__24;
lean_inc(x_17);
x_90 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_90, 0, x_17);
lean_ctor_set(x_90, 1, x_89);
lean_ctor_set(x_90, 2, x_88);
x_91 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__27;
lean_inc(x_17);
x_92 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_92, 0, x_17);
lean_ctor_set(x_92, 1, x_91);
x_93 = lean_array_push(x_35, x_92);
x_94 = lean_array_push(x_93, x_14);
x_95 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__28;
lean_inc(x_17);
x_96 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_96, 0, x_17);
lean_ctor_set(x_96, 1, x_95);
lean_ctor_set(x_96, 2, x_94);
x_97 = lean_array_push(x_35, x_96);
x_98 = lean_array_push(x_97, x_34);
lean_inc(x_17);
x_99 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_99, 0, x_17);
lean_ctor_set(x_99, 1, x_89);
lean_ctor_set(x_99, 2, x_98);
x_100 = lean_array_push(x_35, x_90);
x_101 = lean_array_push(x_100, x_99);
lean_inc(x_17);
x_102 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_102, 0, x_17);
lean_ctor_set(x_102, 1, x_32);
lean_ctor_set(x_102, 2, x_101);
x_103 = lean_array_push(x_53, x_102);
x_104 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__22;
lean_inc(x_17);
x_105 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_105, 0, x_17);
lean_ctor_set(x_105, 1, x_104);
lean_ctor_set(x_105, 2, x_103);
x_106 = lean_array_push(x_53, x_105);
x_107 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__20;
lean_inc(x_17);
x_108 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_108, 0, x_17);
lean_ctor_set(x_108, 1, x_107);
lean_ctor_set(x_108, 2, x_106);
x_109 = lean_array_push(x_35, x_76);
x_110 = lean_array_push(x_109, x_108);
x_111 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__15;
lean_inc(x_17);
x_112 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_112, 0, x_17);
lean_ctor_set(x_112, 1, x_111);
lean_ctor_set(x_112, 2, x_110);
x_113 = lean_array_push(x_63, x_26);
x_114 = lean_array_push(x_113, x_72);
x_115 = lean_array_push(x_114, x_74);
x_116 = lean_array_push(x_115, x_112);
x_117 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__3___closed__2;
x_118 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_118, 0, x_17);
lean_ctor_set(x_118, 1, x_117);
lean_ctor_set(x_118, 2, x_116);
x_119 = lean_apply_8(x_9, x_118, x_3, x_4, x_5, x_6, x_10, x_11, x_22);
return x_119;
}
else
{
uint8_t x_120; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_120 = !lean_is_exclusive(x_13);
if (x_120 == 0)
{
return x_13;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_13, 0);
x_122 = lean_ctor_get(x_13, 1);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_13);
x_123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_122);
return x_123;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("isTrue", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__1;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__2;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__35;
x_2 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__5;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__6;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
lean_inc(x_7);
x_10 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_exprToSyntax___spec__1___rarg(x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_7, 10);
lean_inc(x_13);
lean_dec(x_7);
x_14 = lean_st_ref_get(x_8, x_12);
lean_dec(x_8);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_environment_main_module(x_17);
x_19 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__4;
lean_inc(x_13);
lean_inc(x_18);
x_20 = l_Lean_addMacroScope(x_18, x_19, x_13);
x_21 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__3;
x_22 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__7;
lean_inc(x_11);
x_23 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_23, 0, x_11);
lean_ctor_set(x_23, 1, x_21);
lean_ctor_set(x_23, 2, x_20);
lean_ctor_set(x_23, 3, x_22);
x_24 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__3___closed__12;
x_25 = l_Lean_addMacroScope(x_18, x_24, x_13);
x_26 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__3___closed__11;
x_27 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__3___closed__14;
lean_inc(x_11);
x_28 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_28, 0, x_11);
lean_ctor_set(x_28, 1, x_26);
lean_ctor_set(x_28, 2, x_25);
lean_ctor_set(x_28, 3, x_27);
x_29 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__25;
x_30 = lean_array_push(x_29, x_28);
x_31 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__18;
lean_inc(x_11);
x_32 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_32, 0, x_11);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set(x_32, 2, x_30);
x_33 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__23;
x_34 = lean_array_push(x_33, x_23);
x_35 = lean_array_push(x_34, x_32);
x_36 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__22;
x_37 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_37, 0, x_11);
lean_ctor_set(x_37, 1, x_36);
lean_ctor_set(x_37, 2, x_35);
lean_ctor_set(x_14, 0, x_37);
return x_14;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_38 = lean_ctor_get(x_14, 0);
x_39 = lean_ctor_get(x_14, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_14);
x_40 = lean_ctor_get(x_38, 0);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_environment_main_module(x_40);
x_42 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__4;
lean_inc(x_13);
lean_inc(x_41);
x_43 = l_Lean_addMacroScope(x_41, x_42, x_13);
x_44 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__3;
x_45 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__7;
lean_inc(x_11);
x_46 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_46, 0, x_11);
lean_ctor_set(x_46, 1, x_44);
lean_ctor_set(x_46, 2, x_43);
lean_ctor_set(x_46, 3, x_45);
x_47 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__3___closed__12;
x_48 = l_Lean_addMacroScope(x_41, x_47, x_13);
x_49 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__3___closed__11;
x_50 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__3___closed__14;
lean_inc(x_11);
x_51 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_51, 0, x_11);
lean_ctor_set(x_51, 1, x_49);
lean_ctor_set(x_51, 2, x_48);
lean_ctor_set(x_51, 3, x_50);
x_52 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__25;
x_53 = lean_array_push(x_52, x_51);
x_54 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__18;
lean_inc(x_11);
x_55 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_55, 0, x_11);
lean_ctor_set(x_55, 1, x_54);
lean_ctor_set(x_55, 2, x_53);
x_56 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__23;
x_57 = lean_array_push(x_56, x_46);
x_58 = lean_array_push(x_57, x_55);
x_59 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__22;
x_60 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_60, 0, x_11);
lean_ctor_set(x_60, 1, x_59);
lean_ctor_set(x_60, 2, x_58);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_39);
return x_61;
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; uint8_t x_77; 
x_62 = lean_ctor_get(x_2, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
x_65 = lean_ctor_get(x_2, 1);
lean_inc(x_65);
lean_dec(x_2);
x_66 = lean_ctor_get(x_62, 0);
lean_inc(x_66);
lean_dec(x_62);
x_67 = lean_ctor_get(x_63, 0);
lean_inc(x_67);
lean_dec(x_63);
x_68 = lean_ctor_get(x_64, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_64, 1);
lean_inc(x_69);
lean_dec(x_64);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_1);
x_70 = lean_alloc_closure((void*)(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___boxed), 12, 4);
lean_closure_set(x_70, 0, x_68);
lean_closure_set(x_70, 1, x_1);
lean_closure_set(x_70, 2, x_66);
lean_closure_set(x_70, 3, x_67);
x_77 = lean_unbox(x_69);
lean_dec(x_69);
if (x_77 == 0)
{
uint8_t x_78; 
x_78 = 0;
x_71 = x_78;
goto block_76;
}
else
{
uint8_t x_79; 
x_79 = 1;
x_71 = x_79;
goto block_76;
}
block_76:
{
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_alloc_closure((void*)(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2), 12, 9);
lean_closure_set(x_72, 0, x_1);
lean_closure_set(x_72, 1, x_65);
lean_closure_set(x_72, 2, x_3);
lean_closure_set(x_72, 3, x_4);
lean_closure_set(x_72, 4, x_5);
lean_closure_set(x_72, 5, x_6);
lean_closure_set(x_72, 6, x_66);
lean_closure_set(x_72, 7, x_67);
lean_closure_set(x_72, 8, x_70);
x_73 = l_Lean_Core_withFreshMacroScope___rarg(x_72, x_7, x_8, x_9);
return x_73;
}
else
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_alloc_closure((void*)(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__3), 12, 9);
lean_closure_set(x_74, 0, x_1);
lean_closure_set(x_74, 1, x_65);
lean_closure_set(x_74, 2, x_3);
lean_closure_set(x_74, 3, x_4);
lean_closure_set(x_74, 4, x_5);
lean_closure_set(x_74, 5, x_6);
lean_closure_set(x_74, 6, x_66);
lean_closure_set(x_74, 7, x_67);
lean_closure_set(x_74, 8, x_70);
x_75 = l_Lean_Core_withFreshMacroScope___rarg(x_74, x_7, x_8, x_9);
return x_75;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_1);
lean_dec(x_1);
x_14 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
static lean_object* _init_l_Lean_getConstInfoCtor___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("'", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_getConstInfoCtor___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("' is not a constructor", 22);
return x_1;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_getConstInfoCtor___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__1___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
x_21 = l_Lean_getConstInfoCtor___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__1___closed__2;
x_22 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
x_23 = l_Lean_getConstInfoCtor___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__1___closed__4;
x_24 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Lean_throwError___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__2(x_24, x_2, x_3, x_4, x_5, x_6, x_7, x_17);
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
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
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
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
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
x_23 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__54;
lean_inc(x_19);
x_24 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_24, 0, x_19);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__25;
x_26 = lean_array_push(x_25, x_24);
x_27 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__53;
x_28 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_28, 0, x_19);
lean_ctor_set(x_28, 1, x_27);
lean_ctor_set(x_28, 2, x_26);
x_29 = lean_array_push(x_5, x_28);
x_30 = lean_nat_add(x_2, x_4);
lean_dec(x_2);
x_1 = x_17;
x_2 = x_30;
x_5 = x_29;
x_12 = x_22;
goto _start;
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
else
{
lean_object* x_33; 
lean_dec(x_10);
lean_dec(x_2);
lean_dec(x_1);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_5);
lean_ctor_set(x_33, 1, x_12);
return x_33;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
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
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
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
x_25 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__54;
lean_inc(x_21);
x_26 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_26, 0, x_21);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__25;
x_28 = lean_array_push(x_27, x_26);
x_29 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__53;
x_30 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_30, 0, x_21);
lean_ctor_set(x_30, 1, x_29);
lean_ctor_set(x_30, 2, x_28);
x_31 = lean_array_push(x_18, x_30);
lean_inc(x_10);
x_32 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_exprToSyntax___spec__1___rarg(x_10, x_11, x_24);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_st_ref_get(x_11, x_34);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
lean_inc(x_33);
x_37 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_37, 0, x_33);
lean_ctor_set(x_37, 1, x_25);
x_38 = lean_array_push(x_27, x_37);
x_39 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_39, 0, x_33);
lean_ctor_set(x_39, 1, x_29);
lean_ctor_set(x_39, 2, x_38);
x_40 = lean_array_push(x_19, x_39);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_31);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_nat_add(x_2, x_4);
lean_dec(x_2);
x_1 = x_17;
x_2 = x_42;
x_5 = x_41;
x_12 = x_36;
goto _start;
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
else
{
lean_object* x_45; 
lean_dec(x_10);
lean_dec(x_2);
lean_dec(x_1);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_5);
lean_ctor_set(x_45, 1, x_12);
return x_45;
}
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("a", 1);
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__5___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__5___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__5___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("b", 1);
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__5___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__5___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__5___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Init.Util", 9);
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__5___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("getElem!", 8);
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__5___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("index out of bounds", 19);
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__5___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__5___closed__5;
x_2 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__5___closed__6;
x_3 = lean_unsigned_to_nat(73u);
x_4 = lean_unsigned_to_nat(36u);
x_5 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__5___closed__7;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; 
x_17 = lean_nat_dec_le(x_7, x_6);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_nat_dec_eq(x_5, x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_107; lean_object* x_108; uint8_t x_109; 
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_sub(x_5, x_20);
lean_dec(x_5);
x_28 = lean_ctor_get(x_9, 1);
lean_inc(x_28);
x_29 = lean_ctor_get(x_9, 0);
lean_inc(x_29);
lean_dec(x_9);
x_30 = lean_ctor_get(x_28, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_32 = x_28;
} else {
 lean_dec_ref(x_28);
 x_32 = lean_box(0);
}
x_107 = lean_nat_add(x_4, x_6);
x_108 = lean_array_get_size(x_2);
x_109 = lean_nat_dec_lt(x_107, x_108);
lean_dec(x_108);
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; 
lean_dec(x_107);
x_110 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__5___closed__8;
x_111 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_110);
x_33 = x_111;
goto block_106;
}
else
{
lean_object* x_112; 
x_112 = lean_array_fget(x_2, x_107);
lean_dec(x_107);
x_33 = x_112;
goto block_106;
}
block_27:
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_nat_add(x_6, x_8);
lean_dec(x_6);
x_5 = x_21;
x_6 = x_25;
x_9 = x_24;
x_16 = x_23;
goto _start;
}
block_106:
{
lean_object* x_34; uint8_t x_35; 
lean_inc(x_33);
x_34 = l_Lean_Expr_fvarId_x21(x_33);
x_35 = l_Lean_Expr_hasAnyFVar_visit___at_Lean_Expr_containsFVar___spec__1(x_34, x_3);
lean_dec(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_36 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__5___closed__2;
x_37 = l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(x_36, x_14, x_15, x_16);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_mk_syntax_ident(x_38);
x_41 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__5___closed__4;
x_42 = l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(x_41, x_14, x_15, x_39);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_mk_syntax_ident(x_43);
lean_inc(x_40);
x_46 = lean_array_push(x_29, x_40);
lean_inc(x_45);
x_47 = lean_array_push(x_30, x_45);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_33);
x_48 = lean_infer_type(x_33, x_12, x_13, x_14, x_15, x_44);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = lean_ctor_get(x_1, 0);
x_52 = lean_ctor_get(x_51, 0);
x_53 = l_Lean_Expr_isAppOf(x_49, x_52);
lean_dec(x_49);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_54 = lean_infer_type(x_33, x_12, x_13, x_14, x_15, x_50);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_57 = lean_infer_type(x_55, x_12, x_13, x_14, x_15, x_56);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = l_Lean_Expr_isProp(x_58);
lean_dec(x_58);
x_61 = lean_box(x_53);
x_62 = lean_box(x_60);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_45);
lean_ctor_set(x_64, 1, x_63);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_40);
lean_ctor_set(x_65, 1, x_64);
x_66 = lean_array_push(x_31, x_65);
if (lean_is_scalar(x_32)) {
 x_67 = lean_alloc_ctor(0, 2, 0);
} else {
 x_67 = x_32;
}
lean_ctor_set(x_67, 0, x_47);
lean_ctor_set(x_67, 1, x_66);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_46);
lean_ctor_set(x_68, 1, x_67);
x_69 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_69, 0, x_68);
x_22 = x_69;
x_23 = x_59;
goto block_27;
}
else
{
uint8_t x_70; 
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_40);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_21);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_6);
x_70 = !lean_is_exclusive(x_57);
if (x_70 == 0)
{
return x_57;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_57, 0);
x_72 = lean_ctor_get(x_57, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_57);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
else
{
uint8_t x_74; 
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_40);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_21);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_6);
x_74 = !lean_is_exclusive(x_54);
if (x_74 == 0)
{
return x_54;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_54, 0);
x_76 = lean_ctor_get(x_54, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_54);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
else
{
uint8_t x_78; 
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_40);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_21);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_6);
x_78 = !lean_is_exclusive(x_48);
if (x_78 == 0)
{
return x_48;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_48, 0);
x_80 = lean_ctor_get(x_48, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_48);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_dec(x_33);
lean_inc(x_14);
x_82 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_exprToSyntax___spec__1___rarg(x_14, x_15, x_16);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
x_85 = lean_st_ref_get(x_15, x_84);
x_86 = lean_ctor_get(x_85, 1);
lean_inc(x_86);
lean_dec(x_85);
x_87 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__54;
lean_inc(x_83);
x_88 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_88, 0, x_83);
lean_ctor_set(x_88, 1, x_87);
x_89 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__25;
x_90 = lean_array_push(x_89, x_88);
x_91 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__53;
x_92 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_92, 0, x_83);
lean_ctor_set(x_92, 1, x_91);
lean_ctor_set(x_92, 2, x_90);
x_93 = lean_array_push(x_29, x_92);
lean_inc(x_14);
x_94 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_exprToSyntax___spec__1___rarg(x_14, x_15, x_86);
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
lean_dec(x_94);
x_97 = lean_st_ref_get(x_15, x_96);
x_98 = lean_ctor_get(x_97, 1);
lean_inc(x_98);
lean_dec(x_97);
lean_inc(x_95);
x_99 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_99, 0, x_95);
lean_ctor_set(x_99, 1, x_87);
x_100 = lean_array_push(x_89, x_99);
x_101 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_101, 0, x_95);
lean_ctor_set(x_101, 1, x_91);
lean_ctor_set(x_101, 2, x_100);
x_102 = lean_array_push(x_30, x_101);
if (lean_is_scalar(x_32)) {
 x_103 = lean_alloc_ctor(0, 2, 0);
} else {
 x_103 = x_32;
}
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_31);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_93);
lean_ctor_set(x_104, 1, x_103);
x_105 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_105, 0, x_104);
x_22 = x_105;
x_23 = x_98;
goto block_27;
}
}
}
else
{
lean_object* x_113; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_9);
lean_ctor_set(x_113, 1, x_16);
return x_113;
}
}
else
{
lean_object* x_114; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_9);
lean_ctor_set(x_114, 1, x_16);
return x_114;
}
}
}
static lean_object* _init_l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_betaReduce___lambda__1___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_betaReduce___lambda__2___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("explicit", 8);
return x_1;
}
}
static lean_object* _init_l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__6;
x_2 = l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("@", 1);
return x_1;
}
}
static lean_object* _init_l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("matchAlt", 8);
return x_1;
}
}
static lean_object* _init_l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__6;
x_2 = l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1___closed__6;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("|", 1);
return x_1;
}
}
static lean_object* _init_l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(",", 1);
return x_1;
}
}
static lean_object* _init_l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(2);
x_2 = l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1___closed__9;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("=>", 2);
return x_1;
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1___closed__1;
x_17 = l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1___closed__2;
lean_inc(x_14);
lean_inc(x_13);
x_18 = l_Lean_Core_transform___at_Lean_Core_betaReduce___spec__1(x_8, x_16, x_17, x_13, x_14, x_15);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
lean_inc_n(x_2, 2);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_2);
lean_ctor_set(x_22, 1, x_2);
x_23 = lean_unsigned_to_nat(0u);
x_24 = lean_unsigned_to_nat(1u);
lean_inc(x_13);
lean_inc(x_21);
x_25 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__4(x_21, x_23, x_21, x_24, x_22, x_9, x_10, x_11, x_12, x_13, x_14, x_20);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = !lean_is_exclusive(x_26);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_26, 0);
x_30 = lean_ctor_get(x_26, 1);
x_31 = lean_ctor_get(x_3, 4);
lean_inc(x_31);
lean_dec(x_3);
lean_inc(x_2);
lean_ctor_set(x_26, 1, x_2);
lean_ctor_set(x_26, 0, x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_29);
lean_ctor_set(x_32, 1, x_26);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_31);
x_33 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__5(x_1, x_7, x_19, x_21, x_31, x_23, x_31, x_24, x_32, x_9, x_10, x_11, x_12, x_13, x_14, x_27);
lean_dec(x_31);
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_1);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
x_37 = lean_ctor_get(x_34, 0);
lean_inc(x_37);
lean_dec(x_34);
x_38 = lean_ctor_get(x_35, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_35, 1);
lean_inc(x_39);
lean_dec(x_35);
lean_inc(x_13);
x_40 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_exprToSyntax___spec__1___rarg(x_13, x_14, x_36);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_st_ref_get(x_14, x_42);
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
lean_dec(x_43);
x_45 = l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1___closed__5;
lean_inc(x_41);
x_46 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_46, 0, x_41);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_mk_syntax_ident(x_4);
x_48 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__23;
x_49 = lean_array_push(x_48, x_46);
lean_inc(x_47);
x_50 = lean_array_push(x_49, x_47);
x_51 = l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1___closed__4;
lean_inc(x_41);
x_52 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_52, 0, x_41);
lean_ctor_set(x_52, 1, x_51);
lean_ctor_set(x_52, 2, x_50);
lean_inc(x_2);
x_53 = l_Array_append___rarg(x_2, x_37);
x_54 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__18;
lean_inc(x_41);
x_55 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_55, 0, x_41);
lean_ctor_set(x_55, 1, x_54);
lean_ctor_set(x_55, 2, x_53);
x_56 = lean_array_push(x_48, x_52);
x_57 = lean_array_push(x_56, x_55);
x_58 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__22;
x_59 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_59, 0, x_41);
lean_ctor_set(x_59, 1, x_58);
lean_ctor_set(x_59, 2, x_57);
x_60 = lean_array_push(x_5, x_59);
lean_inc(x_13);
x_61 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_exprToSyntax___spec__1___rarg(x_13, x_14, x_44);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_64 = lean_st_ref_get(x_14, x_63);
x_65 = lean_ctor_get(x_64, 1);
lean_inc(x_65);
lean_dec(x_64);
lean_inc(x_62);
x_66 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_66, 0, x_62);
lean_ctor_set(x_66, 1, x_45);
x_67 = lean_array_push(x_48, x_66);
x_68 = lean_array_push(x_67, x_47);
lean_inc(x_62);
x_69 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_69, 0, x_62);
lean_ctor_set(x_69, 1, x_51);
lean_ctor_set(x_69, 2, x_68);
lean_inc(x_2);
x_70 = l_Array_append___rarg(x_2, x_38);
lean_inc(x_62);
x_71 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_71, 0, x_62);
lean_ctor_set(x_71, 1, x_54);
lean_ctor_set(x_71, 2, x_70);
x_72 = lean_array_push(x_48, x_69);
x_73 = lean_array_push(x_72, x_71);
x_74 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_74, 0, x_62);
lean_ctor_set(x_74, 1, x_58);
lean_ctor_set(x_74, 2, x_73);
x_75 = lean_array_push(x_60, x_74);
x_76 = lean_array_to_list(lean_box(0), x_39);
lean_inc(x_14);
lean_inc(x_13);
x_77 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs(x_6, x_76, x_9, x_10, x_11, x_12, x_13, x_14, x_65);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
x_80 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_exprToSyntax___spec__1___rarg(x_13, x_14, x_79);
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec(x_80);
x_83 = lean_st_ref_get(x_14, x_82);
lean_dec(x_14);
x_84 = !lean_is_exclusive(x_83);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; size_t x_89; size_t x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_85 = lean_ctor_get(x_83, 0);
lean_dec(x_85);
x_86 = l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1___closed__8;
lean_inc(x_81);
x_87 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_87, 0, x_81);
lean_ctor_set(x_87, 1, x_86);
x_88 = lean_array_get_size(x_75);
x_89 = lean_usize_of_nat(x_88);
lean_dec(x_88);
x_90 = 0;
x_91 = l_Array_mapMUnsafe_map___at___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___spec__3(x_89, x_90, x_75);
x_92 = l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1___closed__10;
x_93 = l_Lean_mkSepArray(x_91, x_92);
lean_dec(x_91);
x_94 = l_Array_append___rarg(x_2, x_93);
lean_inc(x_81);
x_95 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_95, 0, x_81);
lean_ctor_set(x_95, 1, x_54);
lean_ctor_set(x_95, 2, x_94);
x_96 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__25;
x_97 = lean_array_push(x_96, x_95);
lean_inc(x_81);
x_98 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_98, 0, x_81);
lean_ctor_set(x_98, 1, x_54);
lean_ctor_set(x_98, 2, x_97);
x_99 = l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1___closed__11;
lean_inc(x_81);
x_100 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_100, 0, x_81);
lean_ctor_set(x_100, 1, x_99);
x_101 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__27;
x_102 = lean_array_push(x_101, x_87);
x_103 = lean_array_push(x_102, x_98);
x_104 = lean_array_push(x_103, x_100);
x_105 = lean_array_push(x_104, x_78);
x_106 = l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1___closed__7;
x_107 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_107, 0, x_81);
lean_ctor_set(x_107, 1, x_106);
lean_ctor_set(x_107, 2, x_105);
lean_ctor_set(x_83, 0, x_107);
return x_83;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; size_t x_112; size_t x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_108 = lean_ctor_get(x_83, 1);
lean_inc(x_108);
lean_dec(x_83);
x_109 = l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1___closed__8;
lean_inc(x_81);
x_110 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_110, 0, x_81);
lean_ctor_set(x_110, 1, x_109);
x_111 = lean_array_get_size(x_75);
x_112 = lean_usize_of_nat(x_111);
lean_dec(x_111);
x_113 = 0;
x_114 = l_Array_mapMUnsafe_map___at___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___spec__3(x_112, x_113, x_75);
x_115 = l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1___closed__10;
x_116 = l_Lean_mkSepArray(x_114, x_115);
lean_dec(x_114);
x_117 = l_Array_append___rarg(x_2, x_116);
lean_inc(x_81);
x_118 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_118, 0, x_81);
lean_ctor_set(x_118, 1, x_54);
lean_ctor_set(x_118, 2, x_117);
x_119 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__25;
x_120 = lean_array_push(x_119, x_118);
lean_inc(x_81);
x_121 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_121, 0, x_81);
lean_ctor_set(x_121, 1, x_54);
lean_ctor_set(x_121, 2, x_120);
x_122 = l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1___closed__11;
lean_inc(x_81);
x_123 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_123, 0, x_81);
lean_ctor_set(x_123, 1, x_122);
x_124 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__27;
x_125 = lean_array_push(x_124, x_110);
x_126 = lean_array_push(x_125, x_121);
x_127 = lean_array_push(x_126, x_123);
x_128 = lean_array_push(x_127, x_78);
x_129 = l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1___closed__7;
x_130 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_130, 0, x_81);
lean_ctor_set(x_130, 1, x_129);
lean_ctor_set(x_130, 2, x_128);
x_131 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_108);
return x_131;
}
}
else
{
uint8_t x_132; 
lean_dec(x_75);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_2);
x_132 = !lean_is_exclusive(x_77);
if (x_132 == 0)
{
return x_77;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_133 = lean_ctor_get(x_77, 0);
x_134 = lean_ctor_get(x_77, 1);
lean_inc(x_134);
lean_inc(x_133);
lean_dec(x_77);
x_135 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_135, 0, x_133);
lean_ctor_set(x_135, 1, x_134);
return x_135;
}
}
}
else
{
uint8_t x_136; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_136 = !lean_is_exclusive(x_33);
if (x_136 == 0)
{
return x_33;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_137 = lean_ctor_get(x_33, 0);
x_138 = lean_ctor_get(x_33, 1);
lean_inc(x_138);
lean_inc(x_137);
lean_dec(x_33);
x_139 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_139, 0, x_137);
lean_ctor_set(x_139, 1, x_138);
return x_139;
}
}
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_140 = lean_ctor_get(x_26, 0);
x_141 = lean_ctor_get(x_26, 1);
lean_inc(x_141);
lean_inc(x_140);
lean_dec(x_26);
x_142 = lean_ctor_get(x_3, 4);
lean_inc(x_142);
lean_dec(x_3);
lean_inc(x_2);
x_143 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_143, 0, x_141);
lean_ctor_set(x_143, 1, x_2);
x_144 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_144, 0, x_140);
lean_ctor_set(x_144, 1, x_143);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_142);
x_145 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__5(x_1, x_7, x_19, x_21, x_142, x_23, x_142, x_24, x_144, x_9, x_10, x_11, x_12, x_13, x_14, x_27);
lean_dec(x_142);
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_1);
if (lean_obj_tag(x_145) == 0)
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_146, 1);
lean_inc(x_147);
x_148 = lean_ctor_get(x_145, 1);
lean_inc(x_148);
lean_dec(x_145);
x_149 = lean_ctor_get(x_146, 0);
lean_inc(x_149);
lean_dec(x_146);
x_150 = lean_ctor_get(x_147, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_147, 1);
lean_inc(x_151);
lean_dec(x_147);
lean_inc(x_13);
x_152 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_exprToSyntax___spec__1___rarg(x_13, x_14, x_148);
x_153 = lean_ctor_get(x_152, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_152, 1);
lean_inc(x_154);
lean_dec(x_152);
x_155 = lean_st_ref_get(x_14, x_154);
x_156 = lean_ctor_get(x_155, 1);
lean_inc(x_156);
lean_dec(x_155);
x_157 = l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1___closed__5;
lean_inc(x_153);
x_158 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_158, 0, x_153);
lean_ctor_set(x_158, 1, x_157);
x_159 = lean_mk_syntax_ident(x_4);
x_160 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__23;
x_161 = lean_array_push(x_160, x_158);
lean_inc(x_159);
x_162 = lean_array_push(x_161, x_159);
x_163 = l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1___closed__4;
lean_inc(x_153);
x_164 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_164, 0, x_153);
lean_ctor_set(x_164, 1, x_163);
lean_ctor_set(x_164, 2, x_162);
lean_inc(x_2);
x_165 = l_Array_append___rarg(x_2, x_149);
x_166 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__18;
lean_inc(x_153);
x_167 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_167, 0, x_153);
lean_ctor_set(x_167, 1, x_166);
lean_ctor_set(x_167, 2, x_165);
x_168 = lean_array_push(x_160, x_164);
x_169 = lean_array_push(x_168, x_167);
x_170 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__22;
x_171 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_171, 0, x_153);
lean_ctor_set(x_171, 1, x_170);
lean_ctor_set(x_171, 2, x_169);
x_172 = lean_array_push(x_5, x_171);
lean_inc(x_13);
x_173 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_exprToSyntax___spec__1___rarg(x_13, x_14, x_156);
x_174 = lean_ctor_get(x_173, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_173, 1);
lean_inc(x_175);
lean_dec(x_173);
x_176 = lean_st_ref_get(x_14, x_175);
x_177 = lean_ctor_get(x_176, 1);
lean_inc(x_177);
lean_dec(x_176);
lean_inc(x_174);
x_178 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_178, 0, x_174);
lean_ctor_set(x_178, 1, x_157);
x_179 = lean_array_push(x_160, x_178);
x_180 = lean_array_push(x_179, x_159);
lean_inc(x_174);
x_181 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_181, 0, x_174);
lean_ctor_set(x_181, 1, x_163);
lean_ctor_set(x_181, 2, x_180);
lean_inc(x_2);
x_182 = l_Array_append___rarg(x_2, x_150);
lean_inc(x_174);
x_183 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_183, 0, x_174);
lean_ctor_set(x_183, 1, x_166);
lean_ctor_set(x_183, 2, x_182);
x_184 = lean_array_push(x_160, x_181);
x_185 = lean_array_push(x_184, x_183);
x_186 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_186, 0, x_174);
lean_ctor_set(x_186, 1, x_170);
lean_ctor_set(x_186, 2, x_185);
x_187 = lean_array_push(x_172, x_186);
x_188 = lean_array_to_list(lean_box(0), x_151);
lean_inc(x_14);
lean_inc(x_13);
x_189 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs(x_6, x_188, x_9, x_10, x_11, x_12, x_13, x_14, x_177);
if (lean_obj_tag(x_189) == 0)
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; size_t x_201; size_t x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_190 = lean_ctor_get(x_189, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_189, 1);
lean_inc(x_191);
lean_dec(x_189);
x_192 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_exprToSyntax___spec__1___rarg(x_13, x_14, x_191);
x_193 = lean_ctor_get(x_192, 0);
lean_inc(x_193);
x_194 = lean_ctor_get(x_192, 1);
lean_inc(x_194);
lean_dec(x_192);
x_195 = lean_st_ref_get(x_14, x_194);
lean_dec(x_14);
x_196 = lean_ctor_get(x_195, 1);
lean_inc(x_196);
if (lean_is_exclusive(x_195)) {
 lean_ctor_release(x_195, 0);
 lean_ctor_release(x_195, 1);
 x_197 = x_195;
} else {
 lean_dec_ref(x_195);
 x_197 = lean_box(0);
}
x_198 = l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1___closed__8;
lean_inc(x_193);
x_199 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_199, 0, x_193);
lean_ctor_set(x_199, 1, x_198);
x_200 = lean_array_get_size(x_187);
x_201 = lean_usize_of_nat(x_200);
lean_dec(x_200);
x_202 = 0;
x_203 = l_Array_mapMUnsafe_map___at___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___spec__3(x_201, x_202, x_187);
x_204 = l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1___closed__10;
x_205 = l_Lean_mkSepArray(x_203, x_204);
lean_dec(x_203);
x_206 = l_Array_append___rarg(x_2, x_205);
lean_inc(x_193);
x_207 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_207, 0, x_193);
lean_ctor_set(x_207, 1, x_166);
lean_ctor_set(x_207, 2, x_206);
x_208 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__25;
x_209 = lean_array_push(x_208, x_207);
lean_inc(x_193);
x_210 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_210, 0, x_193);
lean_ctor_set(x_210, 1, x_166);
lean_ctor_set(x_210, 2, x_209);
x_211 = l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1___closed__11;
lean_inc(x_193);
x_212 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_212, 0, x_193);
lean_ctor_set(x_212, 1, x_211);
x_213 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__27;
x_214 = lean_array_push(x_213, x_199);
x_215 = lean_array_push(x_214, x_210);
x_216 = lean_array_push(x_215, x_212);
x_217 = lean_array_push(x_216, x_190);
x_218 = l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1___closed__7;
x_219 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_219, 0, x_193);
lean_ctor_set(x_219, 1, x_218);
lean_ctor_set(x_219, 2, x_217);
if (lean_is_scalar(x_197)) {
 x_220 = lean_alloc_ctor(0, 2, 0);
} else {
 x_220 = x_197;
}
lean_ctor_set(x_220, 0, x_219);
lean_ctor_set(x_220, 1, x_196);
return x_220;
}
else
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; 
lean_dec(x_187);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_2);
x_221 = lean_ctor_get(x_189, 0);
lean_inc(x_221);
x_222 = lean_ctor_get(x_189, 1);
lean_inc(x_222);
if (lean_is_exclusive(x_189)) {
 lean_ctor_release(x_189, 0);
 lean_ctor_release(x_189, 1);
 x_223 = x_189;
} else {
 lean_dec_ref(x_189);
 x_223 = lean_box(0);
}
if (lean_is_scalar(x_223)) {
 x_224 = lean_alloc_ctor(1, 2, 0);
} else {
 x_224 = x_223;
}
lean_ctor_set(x_224, 0, x_221);
lean_ctor_set(x_224, 1, x_222);
return x_224;
}
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_225 = lean_ctor_get(x_145, 0);
lean_inc(x_225);
x_226 = lean_ctor_get(x_145, 1);
lean_inc(x_226);
if (lean_is_exclusive(x_145)) {
 lean_ctor_release(x_145, 0);
 lean_ctor_release(x_145, 1);
 x_227 = x_145;
} else {
 lean_dec_ref(x_145);
 x_227 = lean_box(0);
}
if (lean_is_scalar(x_227)) {
 x_228 = lean_alloc_ctor(1, 2, 0);
} else {
 x_228 = x_227;
}
lean_ctor_set(x_228, 0, x_225);
lean_ctor_set(x_228, 1, x_226);
return x_228;
}
}
}
else
{
uint8_t x_229; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_229 = !lean_is_exclusive(x_18);
if (x_229 == 0)
{
return x_18;
}
else
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; 
x_230 = lean_ctor_get(x_18, 0);
x_231 = lean_ctor_get(x_18, 1);
lean_inc(x_231);
lean_inc(x_230);
lean_dec(x_18);
x_232 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_232, 0, x_230);
lean_ctor_set(x_232, 1, x_231);
return x_232;
}
}
}
}
static lean_object* _init_l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("ellipsis", 8);
return x_1;
}
}
static lean_object* _init_l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__6;
x_2 = l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("..", 2);
return x_1;
}
}
static lean_object* _init_l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__36;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___closed__4;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_14; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_6);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_15 = lean_ctor_get(x_5, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_5, 1);
lean_inc(x_16);
lean_dec(x_5);
x_22 = lean_ctor_get(x_1, 2);
lean_inc(x_22);
x_23 = lean_unsigned_to_nat(0u);
x_24 = lean_unsigned_to_nat(1u);
x_25 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__19;
lean_inc(x_11);
lean_inc(x_22);
x_26 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__3(x_22, x_23, x_22, x_24, x_25, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_22);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_name_eq(x_3, x_15);
if (x_29 == 0)
{
lean_object* x_30; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_15);
lean_inc(x_3);
x_30 = l_Lean_Meta_compatibleCtors(x_3, x_15, x_9, x_10, x_11, x_12, x_28);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_unbox(x_31);
lean_dec(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_27);
lean_dec(x_15);
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
lean_dec(x_30);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_6);
x_17 = x_34;
x_18 = x_33;
goto block_21;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; size_t x_160; size_t x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_35 = lean_ctor_get(x_30, 1);
lean_inc(x_35);
lean_dec(x_30);
lean_inc(x_11);
x_36 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_exprToSyntax___spec__1___rarg(x_11, x_12, x_35);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_st_ref_get(x_12, x_38);
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec(x_39);
lean_inc(x_3);
x_41 = lean_mk_syntax_ident(x_3);
x_42 = l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___closed__3;
lean_inc(x_37);
x_43 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_43, 0, x_37);
lean_ctor_set(x_43, 1, x_42);
x_44 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__25;
x_45 = lean_array_push(x_44, x_43);
x_46 = l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___closed__2;
lean_inc(x_37);
x_47 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_47, 0, x_37);
lean_ctor_set(x_47, 1, x_46);
lean_ctor_set(x_47, 2, x_45);
x_48 = lean_array_push(x_44, x_47);
x_49 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__18;
lean_inc(x_37);
x_50 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_50, 0, x_37);
lean_ctor_set(x_50, 1, x_49);
lean_ctor_set(x_50, 2, x_48);
x_51 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__23;
x_52 = lean_array_push(x_51, x_41);
x_53 = lean_array_push(x_52, x_50);
x_54 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__22;
x_55 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_55, 0, x_37);
lean_ctor_set(x_55, 1, x_54);
lean_ctor_set(x_55, 2, x_53);
lean_inc(x_11);
x_56 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_exprToSyntax___spec__1___rarg(x_11, x_12, x_40);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = lean_st_ref_get(x_12, x_58);
x_60 = lean_ctor_get(x_59, 1);
lean_inc(x_60);
lean_dec(x_59);
x_61 = lean_mk_syntax_ident(x_15);
lean_inc(x_57);
x_62 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_62, 0, x_57);
lean_ctor_set(x_62, 1, x_42);
x_63 = lean_array_push(x_44, x_62);
lean_inc(x_57);
x_64 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_64, 0, x_57);
lean_ctor_set(x_64, 1, x_46);
lean_ctor_set(x_64, 2, x_63);
x_65 = lean_array_push(x_44, x_64);
lean_inc(x_57);
x_66 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_66, 0, x_57);
lean_ctor_set(x_66, 1, x_49);
lean_ctor_set(x_66, 2, x_65);
x_67 = lean_array_push(x_51, x_61);
x_68 = lean_array_push(x_67, x_66);
x_69 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_69, 0, x_57);
lean_ctor_set(x_69, 1, x_54);
lean_ctor_set(x_69, 2, x_68);
x_70 = lean_array_push(x_51, x_55);
x_71 = lean_array_push(x_70, x_69);
x_72 = l_Array_append___rarg(x_27, x_71);
lean_inc(x_11);
x_73 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_exprToSyntax___spec__1___rarg(x_11, x_12, x_60);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec(x_73);
x_76 = lean_ctor_get(x_11, 10);
lean_inc(x_76);
x_77 = lean_st_ref_get(x_12, x_75);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
x_80 = lean_ctor_get(x_78, 0);
lean_inc(x_80);
lean_dec(x_78);
x_81 = lean_environment_main_module(x_80);
x_82 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__33;
lean_inc(x_76);
lean_inc(x_81);
x_83 = l_Lean_addMacroScope(x_81, x_82, x_76);
x_84 = lean_box(0);
x_85 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__32;
x_86 = l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___closed__5;
lean_inc(x_74);
x_87 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_87, 0, x_74);
lean_ctor_set(x_87, 1, x_85);
lean_ctor_set(x_87, 2, x_83);
lean_ctor_set(x_87, 3, x_86);
x_88 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__41;
lean_inc(x_74);
x_89 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_89, 0, x_74);
lean_ctor_set(x_89, 1, x_88);
x_90 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__16;
lean_inc(x_74);
x_91 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_91, 0, x_74);
lean_ctor_set(x_91, 1, x_90);
x_92 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__42;
lean_inc(x_74);
x_93 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_93, 0, x_74);
lean_ctor_set(x_93, 1, x_92);
x_94 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__7;
x_95 = l_Lean_addMacroScope(x_81, x_94, x_76);
x_96 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__6;
lean_inc(x_74);
x_97 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_97, 0, x_74);
lean_ctor_set(x_97, 1, x_96);
lean_ctor_set(x_97, 2, x_95);
lean_ctor_set(x_97, 3, x_84);
lean_inc(x_97);
x_98 = lean_array_push(x_44, x_97);
lean_inc(x_74);
x_99 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_99, 0, x_74);
lean_ctor_set(x_99, 1, x_49);
lean_ctor_set(x_99, 2, x_98);
x_100 = lean_array_push(x_51, x_93);
x_101 = lean_array_push(x_100, x_99);
x_102 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__43;
lean_inc(x_74);
x_103 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_103, 0, x_74);
lean_ctor_set(x_103, 1, x_102);
lean_ctor_set(x_103, 2, x_101);
x_104 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__26;
lean_inc(x_74);
x_105 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_105, 0, x_74);
lean_ctor_set(x_105, 1, x_104);
x_106 = lean_array_push(x_44, x_105);
lean_inc(x_74);
x_107 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_107, 0, x_74);
lean_ctor_set(x_107, 1, x_49);
lean_ctor_set(x_107, 2, x_106);
x_108 = lean_array_push(x_51, x_103);
x_109 = lean_array_push(x_108, x_107);
x_110 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__24;
lean_inc(x_74);
x_111 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_111, 0, x_74);
lean_ctor_set(x_111, 1, x_110);
lean_ctor_set(x_111, 2, x_109);
x_112 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__48;
lean_inc(x_74);
x_113 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_113, 0, x_74);
lean_ctor_set(x_113, 1, x_112);
lean_inc(x_74);
x_114 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_114, 0, x_74);
lean_ctor_set(x_114, 1, x_49);
lean_ctor_set(x_114, 2, x_25);
x_115 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__12;
x_116 = lean_array_push(x_115, x_113);
x_117 = lean_array_push(x_116, x_97);
lean_inc(x_114);
x_118 = lean_array_push(x_117, x_114);
x_119 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__49;
lean_inc(x_74);
x_120 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_120, 0, x_74);
lean_ctor_set(x_120, 1, x_119);
lean_ctor_set(x_120, 2, x_118);
x_121 = lean_array_push(x_51, x_120);
lean_inc(x_114);
x_122 = lean_array_push(x_121, x_114);
lean_inc(x_74);
x_123 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_123, 0, x_74);
lean_ctor_set(x_123, 1, x_110);
lean_ctor_set(x_123, 2, x_122);
x_124 = lean_array_push(x_51, x_111);
x_125 = lean_array_push(x_124, x_123);
lean_inc(x_74);
x_126 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_126, 0, x_74);
lean_ctor_set(x_126, 1, x_49);
lean_ctor_set(x_126, 2, x_125);
x_127 = lean_array_push(x_44, x_126);
x_128 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__22;
lean_inc(x_74);
x_129 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_129, 0, x_74);
lean_ctor_set(x_129, 1, x_128);
lean_ctor_set(x_129, 2, x_127);
x_130 = lean_array_push(x_44, x_129);
x_131 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__20;
lean_inc(x_74);
x_132 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_132, 0, x_74);
lean_ctor_set(x_132, 1, x_131);
lean_ctor_set(x_132, 2, x_130);
x_133 = lean_array_push(x_51, x_91);
x_134 = lean_array_push(x_133, x_132);
x_135 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__15;
lean_inc(x_74);
x_136 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_136, 0, x_74);
lean_ctor_set(x_136, 1, x_135);
lean_ctor_set(x_136, 2, x_134);
x_137 = lean_array_push(x_51, x_136);
x_138 = lean_array_push(x_137, x_114);
lean_inc(x_74);
x_139 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_139, 0, x_74);
lean_ctor_set(x_139, 1, x_49);
lean_ctor_set(x_139, 2, x_138);
x_140 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__57;
lean_inc(x_74);
x_141 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_141, 0, x_74);
lean_ctor_set(x_141, 1, x_140);
x_142 = lean_array_push(x_115, x_89);
x_143 = lean_array_push(x_142, x_139);
x_144 = lean_array_push(x_143, x_141);
x_145 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__40;
lean_inc(x_74);
x_146 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_146, 0, x_74);
lean_ctor_set(x_146, 1, x_145);
lean_ctor_set(x_146, 2, x_144);
x_147 = lean_array_push(x_44, x_146);
lean_inc(x_74);
x_148 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_148, 0, x_74);
lean_ctor_set(x_148, 1, x_49);
lean_ctor_set(x_148, 2, x_147);
x_149 = lean_array_push(x_51, x_87);
x_150 = lean_array_push(x_149, x_148);
x_151 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_151, 0, x_74);
lean_ctor_set(x_151, 1, x_54);
lean_ctor_set(x_151, 2, x_150);
lean_inc(x_11);
x_152 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_exprToSyntax___spec__1___rarg(x_11, x_12, x_79);
x_153 = lean_ctor_get(x_152, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_152, 1);
lean_inc(x_154);
lean_dec(x_152);
x_155 = lean_st_ref_get(x_12, x_154);
x_156 = lean_ctor_get(x_155, 1);
lean_inc(x_156);
lean_dec(x_155);
x_157 = l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1___closed__8;
lean_inc(x_153);
x_158 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_158, 0, x_153);
lean_ctor_set(x_158, 1, x_157);
x_159 = lean_array_get_size(x_72);
x_160 = lean_usize_of_nat(x_159);
lean_dec(x_159);
x_161 = 0;
x_162 = l_Array_mapMUnsafe_map___at___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___spec__3(x_160, x_161, x_72);
x_163 = l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1___closed__10;
x_164 = l_Lean_mkSepArray(x_162, x_163);
lean_dec(x_162);
x_165 = l_Array_append___rarg(x_25, x_164);
lean_inc(x_153);
x_166 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_166, 0, x_153);
lean_ctor_set(x_166, 1, x_49);
lean_ctor_set(x_166, 2, x_165);
x_167 = lean_array_push(x_44, x_166);
lean_inc(x_153);
x_168 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_168, 0, x_153);
lean_ctor_set(x_168, 1, x_49);
lean_ctor_set(x_168, 2, x_167);
x_169 = l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1___closed__11;
lean_inc(x_153);
x_170 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_170, 0, x_153);
lean_ctor_set(x_170, 1, x_169);
x_171 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__27;
x_172 = lean_array_push(x_171, x_158);
x_173 = lean_array_push(x_172, x_168);
x_174 = lean_array_push(x_173, x_170);
x_175 = lean_array_push(x_174, x_151);
x_176 = l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1___closed__7;
x_177 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_177, 0, x_153);
lean_ctor_set(x_177, 1, x_176);
lean_ctor_set(x_177, 2, x_175);
x_178 = lean_array_push(x_6, x_177);
x_179 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_179, 0, x_178);
x_17 = x_179;
x_18 = x_156;
goto block_21;
}
}
else
{
uint8_t x_180; 
lean_dec(x_27);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_180 = !lean_is_exclusive(x_30);
if (x_180 == 0)
{
return x_30;
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_181 = lean_ctor_get(x_30, 0);
x_182 = lean_ctor_get(x_30, 1);
lean_inc(x_182);
lean_inc(x_181);
lean_dec(x_30);
x_183 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_183, 0, x_181);
lean_ctor_set(x_183, 1, x_182);
return x_183;
}
}
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
lean_dec(x_15);
x_184 = lean_ctor_get(x_4, 0);
lean_inc(x_184);
x_185 = lean_ctor_get(x_184, 2);
lean_inc(x_185);
lean_dec(x_184);
lean_inc(x_2);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_1);
x_186 = lean_alloc_closure((void*)(l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1___boxed), 15, 6);
lean_closure_set(x_186, 0, x_1);
lean_closure_set(x_186, 1, x_25);
lean_closure_set(x_186, 2, x_4);
lean_closure_set(x_186, 3, x_3);
lean_closure_set(x_186, 4, x_27);
lean_closure_set(x_186, 5, x_2);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_187 = l_Lean_Meta_forallTelescopeReducing___at_Lean_Elab_Deriving_mkInductArgNames___spec__2___rarg(x_185, x_186, x_7, x_8, x_9, x_10, x_11, x_12, x_28);
if (lean_obj_tag(x_187) == 0)
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_188 = lean_ctor_get(x_187, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_187, 1);
lean_inc(x_189);
lean_dec(x_187);
x_190 = lean_array_push(x_6, x_188);
x_191 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_191, 0, x_190);
x_17 = x_191;
x_18 = x_189;
goto block_21;
}
else
{
uint8_t x_192; 
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_192 = !lean_is_exclusive(x_187);
if (x_192 == 0)
{
return x_187;
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_193 = lean_ctor_get(x_187, 0);
x_194 = lean_ctor_get(x_187, 1);
lean_inc(x_194);
lean_inc(x_193);
lean_dec(x_187);
x_195 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_195, 0, x_193);
lean_ctor_set(x_195, 1, x_194);
return x_195;
}
}
}
block_21:
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
x_5 = x_16;
x_6 = x_19;
x_13 = x_18;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_13; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_5);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_4, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_4, 1);
lean_inc(x_15);
lean_dec(x_4);
lean_inc(x_6);
lean_inc(x_14);
x_16 = l_Lean_getConstInfoCtor___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__1(x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_19 = l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6(x_1, x_2, x_14, x_17, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_4 = x_15;
x_5 = x_20;
x_12 = x_21;
goto _start;
}
else
{
uint8_t x_23; 
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_19);
if (x_23 == 0)
{
return x_19;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_19, 0);
x_25 = lean_ctor_get(x_19, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_19);
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
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_16);
if (x_27 == 0)
{
return x_16;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_16, 0);
x_29 = lean_ctor_get(x_16, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_16);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__8(size_t x_1, size_t x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_1, 4);
lean_inc(x_10);
x_11 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__19;
lean_inc(x_10);
x_12 = l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__7(x_1, x_2, x_10, x_10, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_array_get_size(x_14);
x_16 = lean_usize_of_nat(x_15);
lean_dec(x_15);
x_17 = 0;
x_18 = l_Array_mapMUnsafe_map___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__8(x_16, x_17, x_14);
lean_ctor_set(x_12, 0, x_18);
return x_12;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; size_t x_22; size_t x_23; lean_object* x_24; lean_object* x_25; 
x_19 = lean_ctor_get(x_12, 0);
x_20 = lean_ctor_get(x_12, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_12);
x_21 = lean_array_get_size(x_19);
x_22 = lean_usize_of_nat(x_21);
lean_dec(x_21);
x_23 = 0;
x_24 = l_Array_mapMUnsafe_map___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__8(x_22, x_23, x_19);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_20);
return x_25;
}
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_12);
if (x_26 == 0)
{
return x_12;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_12, 0);
x_28 = lean_ctor_get(x_12, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_12);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwError___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_getConstInfoCtor___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
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
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
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
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_17;
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_7);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__8(x_4, x_5, x_3);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("match", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__6;
x_2 = l_Lean_Elab_Deriving_DecEq_mkMatch___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("with", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("matchAlts", 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__6;
x_2 = l_Lean_Elab_Deriving_DecEq_mkMatch___closed__4;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(6u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_inc(x_8);
lean_inc(x_2);
x_11 = l_Lean_Elab_Deriving_mkDiscrs(x_1, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_9);
lean_inc(x_8);
x_14 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_exprToSyntax___spec__1___rarg(x_8, x_9, x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_st_ref_get(x_9, x_19);
lean_dec(x_9);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; size_t x_29; size_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_22 = lean_ctor_get(x_20, 0);
lean_dec(x_22);
x_23 = l_Lean_Elab_Deriving_DecEq_mkMatch___closed__1;
lean_inc(x_18);
x_24 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_24, 0, x_18);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__18;
x_26 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__19;
lean_inc(x_18);
x_27 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_27, 0, x_18);
lean_ctor_set(x_27, 1, x_25);
lean_ctor_set(x_27, 2, x_26);
x_28 = lean_array_get_size(x_12);
x_29 = lean_usize_of_nat(x_28);
lean_dec(x_28);
x_30 = 0;
x_31 = l_Array_mapMUnsafe_map___at_Lean_PrettyPrinter_Delaborator_delabAppMatch___spec__9(x_29, x_30, x_12);
x_32 = l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1___closed__10;
x_33 = l_Lean_mkSepArray(x_31, x_32);
lean_dec(x_31);
x_34 = l_Array_append___rarg(x_26, x_33);
lean_inc(x_18);
x_35 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_35, 0, x_18);
lean_ctor_set(x_35, 1, x_25);
lean_ctor_set(x_35, 2, x_34);
x_36 = l_Lean_Elab_Deriving_DecEq_mkMatch___closed__3;
lean_inc(x_18);
x_37 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_37, 0, x_18);
lean_ctor_set(x_37, 1, x_36);
x_38 = l_Array_append___rarg(x_26, x_15);
lean_inc(x_18);
x_39 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_39, 0, x_18);
lean_ctor_set(x_39, 1, x_25);
lean_ctor_set(x_39, 2, x_38);
x_40 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__25;
x_41 = lean_array_push(x_40, x_39);
x_42 = l_Lean_Elab_Deriving_DecEq_mkMatch___closed__5;
lean_inc(x_18);
x_43 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_43, 0, x_18);
lean_ctor_set(x_43, 1, x_42);
lean_ctor_set(x_43, 2, x_41);
x_44 = l_Lean_Elab_Deriving_DecEq_mkMatch___closed__6;
x_45 = lean_array_push(x_44, x_24);
lean_inc(x_27);
x_46 = lean_array_push(x_45, x_27);
x_47 = lean_array_push(x_46, x_27);
x_48 = lean_array_push(x_47, x_35);
x_49 = lean_array_push(x_48, x_37);
x_50 = lean_array_push(x_49, x_43);
x_51 = l_Lean_Elab_Deriving_DecEq_mkMatch___closed__2;
x_52 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_52, 0, x_18);
lean_ctor_set(x_52, 1, x_51);
lean_ctor_set(x_52, 2, x_50);
lean_ctor_set(x_20, 0, x_52);
return x_20;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; size_t x_60; size_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_53 = lean_ctor_get(x_20, 1);
lean_inc(x_53);
lean_dec(x_20);
x_54 = l_Lean_Elab_Deriving_DecEq_mkMatch___closed__1;
lean_inc(x_18);
x_55 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_55, 0, x_18);
lean_ctor_set(x_55, 1, x_54);
x_56 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__18;
x_57 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__19;
lean_inc(x_18);
x_58 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_58, 0, x_18);
lean_ctor_set(x_58, 1, x_56);
lean_ctor_set(x_58, 2, x_57);
x_59 = lean_array_get_size(x_12);
x_60 = lean_usize_of_nat(x_59);
lean_dec(x_59);
x_61 = 0;
x_62 = l_Array_mapMUnsafe_map___at_Lean_PrettyPrinter_Delaborator_delabAppMatch___spec__9(x_60, x_61, x_12);
x_63 = l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1___closed__10;
x_64 = l_Lean_mkSepArray(x_62, x_63);
lean_dec(x_62);
x_65 = l_Array_append___rarg(x_57, x_64);
lean_inc(x_18);
x_66 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_66, 0, x_18);
lean_ctor_set(x_66, 1, x_56);
lean_ctor_set(x_66, 2, x_65);
x_67 = l_Lean_Elab_Deriving_DecEq_mkMatch___closed__3;
lean_inc(x_18);
x_68 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_68, 0, x_18);
lean_ctor_set(x_68, 1, x_67);
x_69 = l_Array_append___rarg(x_57, x_15);
lean_inc(x_18);
x_70 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_70, 0, x_18);
lean_ctor_set(x_70, 1, x_56);
lean_ctor_set(x_70, 2, x_69);
x_71 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__25;
x_72 = lean_array_push(x_71, x_70);
x_73 = l_Lean_Elab_Deriving_DecEq_mkMatch___closed__5;
lean_inc(x_18);
x_74 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_74, 0, x_18);
lean_ctor_set(x_74, 1, x_73);
lean_ctor_set(x_74, 2, x_72);
x_75 = l_Lean_Elab_Deriving_DecEq_mkMatch___closed__6;
x_76 = lean_array_push(x_75, x_55);
lean_inc(x_58);
x_77 = lean_array_push(x_76, x_58);
x_78 = lean_array_push(x_77, x_58);
x_79 = lean_array_push(x_78, x_66);
x_80 = lean_array_push(x_79, x_68);
x_81 = lean_array_push(x_80, x_74);
x_82 = l_Lean_Elab_Deriving_DecEq_mkMatch___closed__2;
x_83 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_83, 0, x_18);
lean_ctor_set(x_83, 1, x_82);
lean_ctor_set(x_83, 2, x_81);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_53);
return x_84;
}
}
else
{
uint8_t x_85; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
x_85 = !lean_is_exclusive(x_14);
if (x_85 == 0)
{
return x_14;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_14, 0);
x_87 = lean_ctor_get(x_14, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_14);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Command", 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__4;
x_2 = l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("declaration", 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__2;
x_2 = l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("declModifiers", 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__2;
x_2 = l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("private", 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__2;
x_2 = l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__7;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("def", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__2;
x_2 = l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__9;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("declId", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__2;
x_2 = l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__11;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("optDeclSig", 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__2;
x_2 = l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__13;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("declValSimple", 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__2;
x_2 = l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__15;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(7u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__34;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__34;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__18;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__35;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__20;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_DecEq_mkAuxFunction(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_9 = lean_ctor_get(x_1, 1);
x_10 = lean_array_get_size(x_9);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_nat_dec_lt(x_11, x_10);
lean_dec(x_10);
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_array_get_size(x_13);
x_15 = lean_nat_dec_lt(x_11, x_14);
lean_dec(x_14);
if (x_12 == 0)
{
lean_object* x_254; lean_object* x_255; 
x_254 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__5___closed__8;
x_255 = l_panic___at___private_Init_Prelude_0__Lean_assembleParts___spec__1(x_254);
x_16 = x_255;
goto block_253;
}
else
{
lean_object* x_256; 
x_256 = lean_array_fget(x_9, x_11);
x_16 = x_256;
goto block_253;
}
block_253:
{
lean_object* x_17; 
if (x_15 == 0)
{
lean_object* x_250; lean_object* x_251; 
x_250 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__5___closed__8;
x_251 = l_panic___at_Lean_Elab_Deriving_mkLocalInstanceLetDecls___spec__1(x_250);
x_17 = x_251;
goto block_249;
}
else
{
lean_object* x_252; 
x_252 = lean_array_fget(x_13, x_11);
x_17 = x_252;
goto block_249;
}
block_249:
{
lean_object* x_18; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_17);
x_18 = l_Lean_Elab_Deriving_DecEq_mkDecEqHeader(x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_16);
lean_inc(x_19);
x_21 = l_Lean_Elab_Deriving_DecEq_mkMatch(x_19, x_17, x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; uint8_t x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; uint8_t x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_ctor_get(x_19, 0);
lean_inc(x_24);
lean_inc(x_6);
x_164 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_exprToSyntax___spec__1___rarg(x_6, x_7, x_23);
x_165 = lean_ctor_get(x_164, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_164, 1);
lean_inc(x_166);
lean_dec(x_164);
x_167 = lean_ctor_get(x_6, 10);
lean_inc(x_167);
x_168 = lean_st_ref_get(x_7, x_166);
x_169 = lean_ctor_get(x_168, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_168, 1);
lean_inc(x_170);
lean_dec(x_168);
x_171 = lean_ctor_get(x_169, 0);
lean_inc(x_171);
lean_dec(x_169);
x_172 = lean_environment_main_module(x_171);
x_173 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__35;
x_174 = l_Lean_addMacroScope(x_172, x_173, x_167);
x_175 = l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__19;
x_176 = l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__21;
lean_inc(x_165);
x_177 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_177, 0, x_165);
lean_ctor_set(x_177, 1, x_175);
lean_ctor_set(x_177, 2, x_174);
lean_ctor_set(x_177, 3, x_176);
x_178 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__41;
lean_inc(x_165);
x_179 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_179, 0, x_165);
lean_ctor_set(x_179, 1, x_178);
x_180 = lean_ctor_get(x_19, 2);
lean_inc(x_180);
lean_dec(x_19);
x_181 = lean_array_get_size(x_180);
x_182 = lean_nat_dec_lt(x_11, x_181);
x_183 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__11;
lean_inc(x_165);
x_184 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_184, 0, x_165);
lean_ctor_set(x_184, 1, x_183);
x_185 = lean_unsigned_to_nat(1u);
x_186 = lean_nat_dec_lt(x_185, x_181);
lean_dec(x_181);
x_187 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__18;
x_188 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__19;
lean_inc(x_165);
x_189 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_189, 0, x_165);
lean_ctor_set(x_189, 1, x_187);
lean_ctor_set(x_189, 2, x_188);
x_190 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__57;
lean_inc(x_165);
x_191 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_191, 0, x_165);
lean_ctor_set(x_191, 1, x_190);
x_192 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__12;
x_193 = lean_array_push(x_192, x_179);
x_194 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__23;
x_195 = lean_array_push(x_194, x_177);
if (x_182 == 0)
{
lean_object* x_238; lean_object* x_239; 
x_238 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__5___closed__8;
x_239 = l_panic___at___private_Init_Prelude_0__Lean_assembleParts___spec__1(x_238);
x_196 = x_239;
goto block_237;
}
else
{
lean_object* x_240; 
x_240 = lean_array_fget(x_180, x_11);
x_196 = x_240;
goto block_237;
}
block_163:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_27 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_exprToSyntax___spec__1___rarg(x_6, x_7, x_26);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_st_ref_get(x_7, x_29);
lean_dec(x_7);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_32 = lean_ctor_get(x_30, 0);
lean_dec(x_32);
x_33 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__18;
x_34 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__19;
lean_inc(x_28);
x_35 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_35, 0, x_28);
lean_ctor_set(x_35, 1, x_33);
lean_ctor_set(x_35, 2, x_34);
x_36 = l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__7;
lean_inc(x_28);
x_37 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_37, 0, x_28);
lean_ctor_set(x_37, 1, x_36);
x_38 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__25;
x_39 = lean_array_push(x_38, x_37);
x_40 = l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__8;
lean_inc(x_28);
x_41 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_41, 0, x_28);
lean_ctor_set(x_41, 1, x_40);
lean_ctor_set(x_41, 2, x_39);
x_42 = lean_array_push(x_38, x_41);
lean_inc(x_28);
x_43 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_43, 0, x_28);
lean_ctor_set(x_43, 1, x_33);
lean_ctor_set(x_43, 2, x_42);
x_44 = l_Lean_Elab_Deriving_DecEq_mkMatch___closed__6;
lean_inc(x_35);
x_45 = lean_array_push(x_44, x_35);
lean_inc(x_35);
x_46 = lean_array_push(x_45, x_35);
x_47 = lean_array_push(x_46, x_43);
lean_inc(x_35);
x_48 = lean_array_push(x_47, x_35);
lean_inc(x_35);
x_49 = lean_array_push(x_48, x_35);
lean_inc(x_35);
x_50 = lean_array_push(x_49, x_35);
x_51 = l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__6;
lean_inc(x_28);
x_52 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_52, 0, x_28);
lean_ctor_set(x_52, 1, x_51);
lean_ctor_set(x_52, 2, x_50);
x_53 = l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__9;
lean_inc(x_28);
x_54 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_54, 0, x_28);
lean_ctor_set(x_54, 1, x_53);
x_55 = lean_mk_syntax_ident(x_16);
x_56 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__23;
x_57 = lean_array_push(x_56, x_55);
lean_inc(x_35);
x_58 = lean_array_push(x_57, x_35);
x_59 = l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__12;
lean_inc(x_28);
x_60 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_60, 0, x_28);
lean_ctor_set(x_60, 1, x_59);
lean_ctor_set(x_60, 2, x_58);
x_61 = l_Array_append___rarg(x_34, x_24);
lean_inc(x_28);
x_62 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_62, 0, x_28);
lean_ctor_set(x_62, 1, x_33);
lean_ctor_set(x_62, 2, x_61);
x_63 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__8;
lean_inc(x_28);
x_64 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_64, 0, x_28);
lean_ctor_set(x_64, 1, x_63);
x_65 = lean_array_push(x_56, x_64);
x_66 = lean_array_push(x_65, x_25);
x_67 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__3___closed__8;
lean_inc(x_28);
x_68 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_68, 0, x_28);
lean_ctor_set(x_68, 1, x_67);
lean_ctor_set(x_68, 2, x_66);
x_69 = lean_array_push(x_38, x_68);
lean_inc(x_28);
x_70 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_70, 0, x_28);
lean_ctor_set(x_70, 1, x_33);
lean_ctor_set(x_70, 2, x_69);
x_71 = lean_array_push(x_56, x_62);
x_72 = lean_array_push(x_71, x_70);
x_73 = l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__14;
lean_inc(x_28);
x_74 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_74, 0, x_28);
lean_ctor_set(x_74, 1, x_73);
lean_ctor_set(x_74, 2, x_72);
x_75 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__20;
lean_inc(x_28);
x_76 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_76, 0, x_28);
lean_ctor_set(x_76, 1, x_75);
x_77 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__12;
x_78 = lean_array_push(x_77, x_76);
x_79 = lean_array_push(x_78, x_22);
lean_inc(x_35);
x_80 = lean_array_push(x_79, x_35);
x_81 = l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__16;
lean_inc(x_28);
x_82 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_82, 0, x_28);
lean_ctor_set(x_82, 1, x_81);
lean_ctor_set(x_82, 2, x_80);
x_83 = l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__17;
x_84 = lean_array_push(x_83, x_54);
x_85 = lean_array_push(x_84, x_60);
x_86 = lean_array_push(x_85, x_74);
x_87 = lean_array_push(x_86, x_82);
lean_inc(x_35);
x_88 = lean_array_push(x_87, x_35);
lean_inc(x_35);
x_89 = lean_array_push(x_88, x_35);
x_90 = lean_array_push(x_89, x_35);
x_91 = l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__10;
lean_inc(x_28);
x_92 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_92, 0, x_28);
lean_ctor_set(x_92, 1, x_91);
lean_ctor_set(x_92, 2, x_90);
x_93 = lean_array_push(x_56, x_52);
x_94 = lean_array_push(x_93, x_92);
x_95 = l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__4;
x_96 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_96, 0, x_28);
lean_ctor_set(x_96, 1, x_95);
lean_ctor_set(x_96, 2, x_94);
lean_ctor_set(x_30, 0, x_96);
return x_30;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_97 = lean_ctor_get(x_30, 1);
lean_inc(x_97);
lean_dec(x_30);
x_98 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__18;
x_99 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__19;
lean_inc(x_28);
x_100 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_100, 0, x_28);
lean_ctor_set(x_100, 1, x_98);
lean_ctor_set(x_100, 2, x_99);
x_101 = l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__7;
lean_inc(x_28);
x_102 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_102, 0, x_28);
lean_ctor_set(x_102, 1, x_101);
x_103 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__25;
x_104 = lean_array_push(x_103, x_102);
x_105 = l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__8;
lean_inc(x_28);
x_106 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_106, 0, x_28);
lean_ctor_set(x_106, 1, x_105);
lean_ctor_set(x_106, 2, x_104);
x_107 = lean_array_push(x_103, x_106);
lean_inc(x_28);
x_108 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_108, 0, x_28);
lean_ctor_set(x_108, 1, x_98);
lean_ctor_set(x_108, 2, x_107);
x_109 = l_Lean_Elab_Deriving_DecEq_mkMatch___closed__6;
lean_inc(x_100);
x_110 = lean_array_push(x_109, x_100);
lean_inc(x_100);
x_111 = lean_array_push(x_110, x_100);
x_112 = lean_array_push(x_111, x_108);
lean_inc(x_100);
x_113 = lean_array_push(x_112, x_100);
lean_inc(x_100);
x_114 = lean_array_push(x_113, x_100);
lean_inc(x_100);
x_115 = lean_array_push(x_114, x_100);
x_116 = l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__6;
lean_inc(x_28);
x_117 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_117, 0, x_28);
lean_ctor_set(x_117, 1, x_116);
lean_ctor_set(x_117, 2, x_115);
x_118 = l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__9;
lean_inc(x_28);
x_119 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_119, 0, x_28);
lean_ctor_set(x_119, 1, x_118);
x_120 = lean_mk_syntax_ident(x_16);
x_121 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__23;
x_122 = lean_array_push(x_121, x_120);
lean_inc(x_100);
x_123 = lean_array_push(x_122, x_100);
x_124 = l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__12;
lean_inc(x_28);
x_125 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_125, 0, x_28);
lean_ctor_set(x_125, 1, x_124);
lean_ctor_set(x_125, 2, x_123);
x_126 = l_Array_append___rarg(x_99, x_24);
lean_inc(x_28);
x_127 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_127, 0, x_28);
lean_ctor_set(x_127, 1, x_98);
lean_ctor_set(x_127, 2, x_126);
x_128 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__8;
lean_inc(x_28);
x_129 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_129, 0, x_28);
lean_ctor_set(x_129, 1, x_128);
x_130 = lean_array_push(x_121, x_129);
x_131 = lean_array_push(x_130, x_25);
x_132 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__3___closed__8;
lean_inc(x_28);
x_133 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_133, 0, x_28);
lean_ctor_set(x_133, 1, x_132);
lean_ctor_set(x_133, 2, x_131);
x_134 = lean_array_push(x_103, x_133);
lean_inc(x_28);
x_135 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_135, 0, x_28);
lean_ctor_set(x_135, 1, x_98);
lean_ctor_set(x_135, 2, x_134);
x_136 = lean_array_push(x_121, x_127);
x_137 = lean_array_push(x_136, x_135);
x_138 = l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__14;
lean_inc(x_28);
x_139 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_139, 0, x_28);
lean_ctor_set(x_139, 1, x_138);
lean_ctor_set(x_139, 2, x_137);
x_140 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__20;
lean_inc(x_28);
x_141 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_141, 0, x_28);
lean_ctor_set(x_141, 1, x_140);
x_142 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__12;
x_143 = lean_array_push(x_142, x_141);
x_144 = lean_array_push(x_143, x_22);
lean_inc(x_100);
x_145 = lean_array_push(x_144, x_100);
x_146 = l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__16;
lean_inc(x_28);
x_147 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_147, 0, x_28);
lean_ctor_set(x_147, 1, x_146);
lean_ctor_set(x_147, 2, x_145);
x_148 = l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__17;
x_149 = lean_array_push(x_148, x_119);
x_150 = lean_array_push(x_149, x_125);
x_151 = lean_array_push(x_150, x_139);
x_152 = lean_array_push(x_151, x_147);
lean_inc(x_100);
x_153 = lean_array_push(x_152, x_100);
lean_inc(x_100);
x_154 = lean_array_push(x_153, x_100);
x_155 = lean_array_push(x_154, x_100);
x_156 = l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__10;
lean_inc(x_28);
x_157 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_157, 0, x_28);
lean_ctor_set(x_157, 1, x_156);
lean_ctor_set(x_157, 2, x_155);
x_158 = lean_array_push(x_121, x_117);
x_159 = lean_array_push(x_158, x_157);
x_160 = l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__4;
x_161 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_161, 0, x_28);
lean_ctor_set(x_161, 1, x_160);
lean_ctor_set(x_161, 2, x_159);
x_162 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_162, 0, x_161);
lean_ctor_set(x_162, 1, x_97);
return x_162;
}
}
block_237:
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_197 = lean_mk_syntax_ident(x_196);
x_198 = lean_array_push(x_192, x_197);
x_199 = lean_array_push(x_198, x_184);
if (x_186 == 0)
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; 
lean_dec(x_180);
x_200 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__5___closed__8;
x_201 = l_panic___at___private_Init_Prelude_0__Lean_assembleParts___spec__1(x_200);
x_202 = lean_mk_syntax_ident(x_201);
x_203 = lean_array_push(x_199, x_202);
x_204 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__10;
lean_inc(x_165);
x_205 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_205, 0, x_165);
lean_ctor_set(x_205, 1, x_204);
lean_ctor_set(x_205, 2, x_203);
x_206 = lean_array_push(x_194, x_205);
x_207 = lean_array_push(x_206, x_189);
lean_inc(x_165);
x_208 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_208, 0, x_165);
lean_ctor_set(x_208, 1, x_187);
lean_ctor_set(x_208, 2, x_207);
x_209 = lean_array_push(x_193, x_208);
x_210 = lean_array_push(x_209, x_191);
x_211 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__40;
lean_inc(x_165);
x_212 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_212, 0, x_165);
lean_ctor_set(x_212, 1, x_211);
lean_ctor_set(x_212, 2, x_210);
x_213 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__25;
x_214 = lean_array_push(x_213, x_212);
lean_inc(x_165);
x_215 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_215, 0, x_165);
lean_ctor_set(x_215, 1, x_187);
lean_ctor_set(x_215, 2, x_214);
x_216 = lean_array_push(x_195, x_215);
x_217 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__22;
x_218 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_218, 0, x_165);
lean_ctor_set(x_218, 1, x_217);
lean_ctor_set(x_218, 2, x_216);
x_25 = x_218;
x_26 = x_170;
goto block_163;
}
else
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; 
x_219 = lean_array_fget(x_180, x_185);
lean_dec(x_180);
x_220 = lean_mk_syntax_ident(x_219);
x_221 = lean_array_push(x_199, x_220);
x_222 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__10;
lean_inc(x_165);
x_223 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_223, 0, x_165);
lean_ctor_set(x_223, 1, x_222);
lean_ctor_set(x_223, 2, x_221);
x_224 = lean_array_push(x_194, x_223);
x_225 = lean_array_push(x_224, x_189);
lean_inc(x_165);
x_226 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_226, 0, x_165);
lean_ctor_set(x_226, 1, x_187);
lean_ctor_set(x_226, 2, x_225);
x_227 = lean_array_push(x_193, x_226);
x_228 = lean_array_push(x_227, x_191);
x_229 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__40;
lean_inc(x_165);
x_230 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_230, 0, x_165);
lean_ctor_set(x_230, 1, x_229);
lean_ctor_set(x_230, 2, x_228);
x_231 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__25;
x_232 = lean_array_push(x_231, x_230);
lean_inc(x_165);
x_233 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_233, 0, x_165);
lean_ctor_set(x_233, 1, x_187);
lean_ctor_set(x_233, 2, x_232);
x_234 = lean_array_push(x_195, x_233);
x_235 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__22;
x_236 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_236, 0, x_165);
lean_ctor_set(x_236, 1, x_235);
lean_ctor_set(x_236, 2, x_234);
x_25 = x_236;
x_26 = x_170;
goto block_163;
}
}
}
else
{
uint8_t x_241; 
lean_dec(x_19);
lean_dec(x_16);
lean_dec(x_7);
lean_dec(x_6);
x_241 = !lean_is_exclusive(x_21);
if (x_241 == 0)
{
return x_21;
}
else
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; 
x_242 = lean_ctor_get(x_21, 0);
x_243 = lean_ctor_get(x_21, 1);
lean_inc(x_243);
lean_inc(x_242);
lean_dec(x_21);
x_244 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_244, 0, x_242);
lean_ctor_set(x_244, 1, x_243);
return x_244;
}
}
}
else
{
uint8_t x_245; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_245 = !lean_is_exclusive(x_18);
if (x_245 == 0)
{
return x_18;
}
else
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; 
x_246 = lean_ctor_get(x_18, 0);
x_247 = lean_ctor_get(x_18, 1);
lean_inc(x_247);
lean_inc(x_246);
lean_dec(x_18);
x_248 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_248, 0, x_246);
lean_ctor_set(x_248, 1, x_247);
return x_248;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_DecEq_mkAuxFunction___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Deriving_DecEq_mkAuxFunction(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_List_mapTRAux___at_Lean_Elab_Deriving_DecEq_mkDecEqCmds___spec__1(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_DecEq_mkDecEqCmds___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkDecEqCmds___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("decEq", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkDecEqCmds___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Elab", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkDecEqCmds___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Deriving_DecEq_mkDecEqCmds___closed__2;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkDecEqCmds___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Deriving", 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkDecEqCmds___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkDecEqCmds___closed__3;
x_2 = l_Lean_Elab_Deriving_DecEq_mkDecEqCmds___closed__4;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkDecEqCmds___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkDecEqCmds___closed__5;
x_2 = l_Lean_Elab_Deriving_DecEq_mkDecEqCmds___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkDecEqCmds___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("\n", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkDecEqCmds___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkDecEqCmds___closed__7;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkDecEqCmds___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("", 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkDecEqCmds___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkDecEqCmds___closed__9;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_DecEq_mkDecEqCmds(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = l_Lean_Elab_Deriving_DecEq_mkDecEqCmds___closed__1;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_10);
x_12 = l_Lean_Elab_Deriving_mkContext(x_11, x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_15 = l_Lean_Elab_Deriving_DecEq_mkAuxFunction(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__25;
x_19 = lean_array_push(x_18, x_10);
x_20 = l_Lean_Elab_Deriving_DecEq_mkDecEqHeader___closed__2;
x_21 = 0;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_22 = l_Lean_Elab_Deriving_mkInstanceCmds(x_13, x_20, x_19, x_21, x_2, x_3, x_4, x_5, x_6, x_7, x_17);
lean_dec(x_19);
lean_dec(x_13);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_25 = x_22;
} else {
 lean_dec_ref(x_22);
 x_25 = lean_box(0);
}
x_26 = lean_array_push(x_18, x_16);
x_27 = l_Array_append___rarg(x_26, x_23);
x_28 = l_Lean_Elab_Deriving_DecEq_mkDecEqCmds___closed__6;
x_46 = lean_st_ref_get(x_7, x_24);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_47, 3);
lean_inc(x_48);
lean_dec(x_47);
x_49 = lean_ctor_get_uint8(x_48, sizeof(void*)*1);
lean_dec(x_48);
if (x_49 == 0)
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_46, 1);
lean_inc(x_50);
lean_dec(x_46);
x_29 = x_21;
x_30 = x_50;
goto block_45;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_51 = lean_ctor_get(x_46, 1);
lean_inc(x_51);
lean_dec(x_46);
x_52 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_tryCoe___spec__2(x_28, x_2, x_3, x_4, x_5, x_6, x_7, x_51);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = lean_unbox(x_53);
lean_dec(x_53);
x_29 = x_55;
x_30 = x_54;
goto block_45;
}
block_45:
{
if (x_29 == 0)
{
lean_object* x_31; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
if (lean_is_scalar(x_25)) {
 x_31 = lean_alloc_ctor(0, 2, 0);
} else {
 x_31 = x_25;
}
lean_ctor_set(x_31, 0, x_27);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
lean_dec(x_25);
lean_inc(x_27);
x_32 = lean_array_to_list(lean_box(0), x_27);
x_33 = lean_box(0);
x_34 = l_List_mapTRAux___at_Lean_Elab_Deriving_DecEq_mkDecEqCmds___spec__1(x_32, x_33);
x_35 = l_Lean_MessageData_ofList(x_34);
lean_dec(x_34);
x_36 = l_Lean_Elab_Deriving_DecEq_mkDecEqCmds___closed__8;
x_37 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
x_38 = l_Lean_Elab_Deriving_DecEq_mkDecEqCmds___closed__10;
x_39 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = l_Lean_addTrace___at___private_Lean_Elab_Term_0__Lean_Elab_Term_tryCoe___spec__1(x_28, x_39, x_2, x_3, x_4, x_5, x_6, x_7, x_30);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_40, 0);
lean_dec(x_42);
lean_ctor_set(x_40, 0, x_27);
return x_40;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
lean_dec(x_40);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_27);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
}
else
{
uint8_t x_56; 
lean_dec(x_16);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_56 = !lean_is_exclusive(x_22);
if (x_56 == 0)
{
return x_22;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_22, 0);
x_58 = lean_ctor_get(x_22, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_22);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
else
{
uint8_t x_60; 
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_60 = !lean_is_exclusive(x_15);
if (x_60 == 0)
{
return x_15;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_15, 0);
x_62 = lean_ctor_get(x_15, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_15);
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
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_64 = !lean_is_exclusive(x_12);
if (x_64 == 0)
{
return x_12;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_12, 0);
x_66 = lean_ctor_get(x_12, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_12);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_DecEq_mkDecEqCmds___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Deriving_DecEq_mkDecEqCmds___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Deriving_DecEq_mkDecEq___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_5 = l_Lean_Elab_Command_getRef(x_2, x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_2, 4);
lean_inc(x_8);
lean_inc(x_8);
x_9 = l_Lean_Elab_getBetterRef(x_6, x_8);
lean_dec(x_6);
x_10 = l_Lean_addMessageContextPartial___at_Lean_Elab_Command_instAddMessageContextCommandElabM___spec__1(x_1, x_2, x_3, x_7);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Elab_addMacroStack___at_Lean_Elab_Command_instAddErrorMessageContextCommandElabM___spec__1(x_11, x_8, x_2, x_3, x_12);
lean_dec(x_2);
lean_dec(x_8);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_9);
lean_ctor_set(x_16, 1, x_15);
lean_ctor_set_tag(x_13, 1);
lean_ctor_set(x_13, 0, x_16);
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_13, 0);
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_13);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_9);
lean_ctor_set(x_19, 1, x_17);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
}
static lean_object* _init_l_Lean_getConstInfoInduct___at_Lean_Elab_Deriving_DecEq_mkDecEq___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("' is not a inductive type", 25);
return x_1;
}
}
static lean_object* _init_l_Lean_getConstInfoInduct___at_Lean_Elab_Deriving_DecEq_mkDecEq___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_getConstInfoInduct___at_Lean_Elab_Deriving_DecEq_mkDecEq___spec__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at_Lean_Elab_Deriving_DecEq_mkDecEq___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_2);
lean_inc(x_1);
x_5 = l_Lean_getConstInfo___at_Lean_Elab_elabDeriving___spec__17(x_1, x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 5)
{
uint8_t x_7; 
lean_dec(x_2);
lean_dec(x_1);
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_5, 0);
lean_dec(x_8);
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
lean_dec(x_6);
lean_ctor_set(x_5, 0, x_9);
return x_5;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
lean_dec(x_5);
x_11 = lean_ctor_get(x_6, 0);
lean_inc(x_11);
lean_dec(x_6);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_6);
x_13 = lean_ctor_get(x_5, 1);
lean_inc(x_13);
lean_dec(x_5);
x_14 = lean_box(0);
x_15 = l_Lean_Expr_const___override(x_1, x_14);
x_16 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = l_Lean_getConstInfoCtor___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__1___closed__2;
x_18 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = l_Lean_getConstInfoInduct___at_Lean_Elab_Deriving_DecEq_mkDecEq___spec__1___closed__2;
x_20 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_throwError___at_Lean_Elab_Deriving_DecEq_mkDecEq___spec__2(x_20, x_2, x_3, x_13);
return x_21;
}
}
else
{
uint8_t x_22; 
lean_dec(x_2);
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_5);
if (x_22 == 0)
{
return x_5;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_5, 0);
x_24 = lean_ctor_get(x_5, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_5);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_DecEq_mkDecEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_2);
x_5 = l_Lean_getConstInfoInduct___at_Lean_Elab_Deriving_DecEq_mkDecEq___spec__1(x_1, x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get_uint8(x_6, sizeof(void*)*5 + 3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec(x_5);
x_9 = lean_alloc_closure((void*)(l_Lean_Elab_Deriving_DecEq_mkDecEqCmds), 8, 1);
lean_closure_set(x_9, 0, x_6);
lean_inc(x_2);
x_10 = l_Lean_Elab_Command_liftTermElabM___rarg(x_9, x_2, x_3, x_8);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
x_14 = lean_array_get_size(x_12);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_nat_dec_lt(x_15, x_14);
if (x_16 == 0)
{
uint8_t x_17; lean_object* x_18; 
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_2);
x_17 = 1;
x_18 = lean_box(x_17);
lean_ctor_set(x_10, 0, x_18);
return x_10;
}
else
{
uint8_t x_19; 
x_19 = lean_nat_dec_le(x_14, x_14);
if (x_19 == 0)
{
uint8_t x_20; lean_object* x_21; 
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_2);
x_20 = 1;
x_21 = lean_box(x_20);
lean_ctor_set(x_10, 0, x_21);
return x_10;
}
else
{
size_t x_22; size_t x_23; lean_object* x_24; lean_object* x_25; 
lean_free_object(x_10);
x_22 = 0;
x_23 = lean_usize_of_nat(x_14);
lean_dec(x_14);
x_24 = lean_box(0);
x_25 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabCommand___spec__20(x_12, x_22, x_23, x_24, x_2, x_3, x_13);
lean_dec(x_12);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_25, 0);
lean_dec(x_27);
x_28 = 1;
x_29 = lean_box(x_28);
lean_ctor_set(x_25, 0, x_29);
return x_25;
}
else
{
lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_25, 1);
lean_inc(x_30);
lean_dec(x_25);
x_31 = 1;
x_32 = lean_box(x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_30);
return x_33;
}
}
else
{
uint8_t x_34; 
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
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_38 = lean_ctor_get(x_10, 0);
x_39 = lean_ctor_get(x_10, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_10);
x_40 = lean_array_get_size(x_38);
x_41 = lean_unsigned_to_nat(0u);
x_42 = lean_nat_dec_lt(x_41, x_40);
if (x_42 == 0)
{
uint8_t x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_40);
lean_dec(x_38);
lean_dec(x_3);
lean_dec(x_2);
x_43 = 1;
x_44 = lean_box(x_43);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_39);
return x_45;
}
else
{
uint8_t x_46; 
x_46 = lean_nat_dec_le(x_40, x_40);
if (x_46 == 0)
{
uint8_t x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_40);
lean_dec(x_38);
lean_dec(x_3);
lean_dec(x_2);
x_47 = 1;
x_48 = lean_box(x_47);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_39);
return x_49;
}
else
{
size_t x_50; size_t x_51; lean_object* x_52; lean_object* x_53; 
x_50 = 0;
x_51 = lean_usize_of_nat(x_40);
lean_dec(x_40);
x_52 = lean_box(0);
x_53 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabCommand___spec__20(x_38, x_50, x_51, x_52, x_2, x_3, x_39);
lean_dec(x_38);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; 
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
x_56 = 1;
x_57 = lean_box(x_56);
if (lean_is_scalar(x_55)) {
 x_58 = lean_alloc_ctor(0, 2, 0);
} else {
 x_58 = x_55;
}
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_54);
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
}
}
else
{
uint8_t x_63; 
lean_dec(x_3);
lean_dec(x_2);
x_63 = !lean_is_exclusive(x_10);
if (x_63 == 0)
{
return x_10;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_10, 0);
x_65 = lean_ctor_get(x_10, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_10);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
else
{
uint8_t x_67; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_67 = !lean_is_exclusive(x_5);
if (x_67 == 0)
{
lean_object* x_68; uint8_t x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_5, 0);
lean_dec(x_68);
x_69 = 0;
x_70 = lean_box(x_69);
lean_ctor_set(x_5, 0, x_70);
return x_5;
}
else
{
lean_object* x_71; uint8_t x_72; lean_object* x_73; lean_object* x_74; 
x_71 = lean_ctor_get(x_5, 1);
lean_inc(x_71);
lean_dec(x_5);
x_72 = 0;
x_73 = lean_box(x_72);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_71);
return x_74;
}
}
}
else
{
uint8_t x_75; 
lean_dec(x_3);
lean_dec(x_2);
x_75 = !lean_is_exclusive(x_5);
if (x_75 == 0)
{
return x_5;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_5, 0);
x_77 = lean_ctor_get(x_5, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_5);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Deriving_DecEq_mkDecEq___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_throwError___at_Lean_Elab_Deriving_DecEq_mkDecEq___spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at_Lean_Elab_Deriving_DecEq_mkDecEq___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_getConstInfoInduct___at_Lean_Elab_Deriving_DecEq_mkDecEq___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkEnumOfNat_mkDecTree___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Nat", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkEnumOfNat_mkDecTree___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Deriving_DecEq_mkEnumOfNat_mkDecTree___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkEnumOfNat_mkDecTree___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("ble", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkEnumOfNat_mkDecTree___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkEnumOfNat_mkDecTree___closed__2;
x_2 = l_Lean_Elab_Deriving_DecEq_mkEnumOfNat_mkDecTree___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkEnumOfNat_mkDecTree___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Deriving_DecEq_mkEnumOfNat_mkDecTree___closed__4;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkEnumOfNat_mkDecTree___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("beq", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkEnumOfNat_mkDecTree___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkEnumOfNat_mkDecTree___closed__2;
x_2 = l_Lean_Elab_Deriving_DecEq_mkEnumOfNat_mkDecTree___closed__6;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkEnumOfNat_mkDecTree___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Deriving_DecEq_mkEnumOfNat_mkDecTree___closed__7;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_DecEq_mkEnumOfNat_mkDecTree(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_add(x_5, x_7);
x_9 = lean_nat_dec_eq(x_8, x_6);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_unsigned_to_nat(2u);
x_11 = lean_nat_add(x_5, x_10);
x_12 = lean_nat_dec_eq(x_11, x_6);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_8);
x_13 = lean_nat_add(x_5, x_6);
x_14 = lean_nat_div(x_13, x_10);
lean_dec(x_13);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_15 = l_Lean_Elab_Deriving_DecEq_mkEnumOfNat_mkDecTree(x_1, x_2, x_3, x_4, x_5, x_14);
lean_inc(x_14);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_16 = l_Lean_Elab_Deriving_DecEq_mkEnumOfNat_mkDecTree(x_1, x_2, x_3, x_4, x_14, x_6);
x_17 = l_Lean_mkRawNatLit(x_14);
x_18 = l_Lean_Elab_Deriving_DecEq_mkEnumOfNat_mkDecTree___closed__5;
x_19 = l_Lean_mkAppB(x_18, x_17, x_3);
x_20 = l_Lean_mkApp4(x_4, x_1, x_19, x_16, x_15);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_27; 
x_21 = lean_box(0);
lean_inc(x_5);
x_22 = l_Lean_mkRawNatLit(x_5);
x_23 = l_Lean_Elab_Deriving_DecEq_mkEnumOfNat_mkDecTree___closed__8;
x_24 = l_Lean_mkAppB(x_23, x_3, x_22);
x_25 = lean_array_get_size(x_2);
x_26 = lean_nat_dec_lt(x_5, x_25);
x_27 = lean_nat_dec_lt(x_8, x_25);
lean_dec(x_25);
if (x_26 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_5);
x_28 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__5___closed__8;
x_29 = l_panic___at___private_Init_Prelude_0__Lean_assembleParts___spec__1(x_28);
x_30 = l_Lean_Expr_const___override(x_29, x_21);
if (x_27 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_8);
x_31 = l_panic___at___private_Init_Prelude_0__Lean_assembleParts___spec__1(x_28);
x_32 = l_Lean_Expr_const___override(x_31, x_21);
x_33 = l_Lean_mkApp4(x_4, x_1, x_24, x_30, x_32);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_array_fget(x_2, x_8);
lean_dec(x_8);
x_35 = l_Lean_Expr_const___override(x_34, x_21);
x_36 = l_Lean_mkApp4(x_4, x_1, x_24, x_30, x_35);
return x_36;
}
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_array_fget(x_2, x_5);
lean_dec(x_5);
x_38 = l_Lean_Expr_const___override(x_37, x_21);
if (x_27 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_8);
x_39 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__5___closed__8;
x_40 = l_panic___at___private_Init_Prelude_0__Lean_assembleParts___spec__1(x_39);
x_41 = l_Lean_Expr_const___override(x_40, x_21);
x_42 = l_Lean_mkApp4(x_4, x_1, x_24, x_38, x_41);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_array_fget(x_2, x_8);
lean_dec(x_8);
x_44 = l_Lean_Expr_const___override(x_43, x_21);
x_45 = l_Lean_mkApp4(x_4, x_1, x_24, x_38, x_44);
return x_45;
}
}
}
}
else
{
lean_object* x_46; uint8_t x_47; lean_object* x_48; 
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_46 = lean_array_get_size(x_2);
x_47 = lean_nat_dec_lt(x_5, x_46);
lean_dec(x_46);
x_48 = lean_box(0);
if (x_47 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_5);
x_49 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__5___closed__8;
x_50 = l_panic___at___private_Init_Prelude_0__Lean_assembleParts___spec__1(x_49);
x_51 = l_Lean_Expr_const___override(x_50, x_48);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_array_fget(x_2, x_5);
lean_dec(x_5);
x_53 = l_Lean_Expr_const___override(x_52, x_48);
return x_53;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_DecEq_mkEnumOfNat_mkDecTree___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_Deriving_DecEq_mkEnumOfNat_mkDecTree(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_2);
return x_7;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkEnumOfNat___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("cond", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkEnumOfNat___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Deriving_DecEq_mkEnumOfNat___lambda__1___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkEnumOfNat___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("ofNat", 5);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_DecEq_mkEnumOfNat___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; lean_object* x_24; 
x_12 = l_Lean_levelZero;
lean_inc(x_1);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_1);
x_14 = l_Lean_Elab_Deriving_DecEq_mkEnumOfNat___lambda__1___closed__2;
x_15 = l_Lean_Expr_const___override(x_14, x_13);
x_16 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__25;
lean_inc(x_6);
x_17 = lean_array_push(x_16, x_6);
x_18 = lean_array_get_size(x_2);
x_19 = lean_unsigned_to_nat(0u);
lean_inc(x_3);
x_20 = l_Lean_Elab_Deriving_DecEq_mkEnumOfNat_mkDecTree(x_3, x_2, x_6, x_15, x_19, x_18);
lean_dec(x_18);
x_21 = 0;
x_22 = 1;
x_23 = 1;
x_24 = l_Lean_Meta_mkLambdaFVars(x_17, x_20, x_21, x_22, x_23, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_Lean_mkArrow(x_4, x_3, x_9, x_10, x_26);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Lean_Elab_Deriving_DecEq_mkEnumOfNat___lambda__1___closed__3;
x_31 = l_Lean_Name_str___override(x_5, x_30);
lean_inc(x_1);
lean_inc(x_31);
x_32 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_1);
lean_ctor_set(x_32, 2, x_28);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_1);
x_34 = lean_box(1);
x_35 = 1;
x_36 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_36, 0, x_32);
lean_ctor_set(x_36, 1, x_25);
lean_ctor_set(x_36, 2, x_34);
lean_ctor_set(x_36, 3, x_33);
lean_ctor_set_uint8(x_36, sizeof(void*)*4, x_35);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_36);
x_38 = l_Lean_addAndCompile___at_Lean_Meta_evalExprCore___spec__1(x_37, x_7, x_8, x_9, x_10, x_29);
return x_38;
}
else
{
uint8_t x_39; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_24);
if (x_39 == 0)
{
return x_24;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_24, 0);
x_41 = lean_ctor_get(x_24, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_24);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkEnumOfNat___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Deriving_DecEq_mkEnumOfNat_mkDecTree___closed__2;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_DecEq_mkEnumOfNat(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_1);
x_7 = l_Lean_getConstInfoInduct___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoForKernelRec___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_box(0);
lean_inc(x_1);
x_11 = l_Lean_Expr_const___override(x_1, x_10);
x_12 = lean_ctor_get(x_8, 4);
lean_inc(x_12);
lean_dec(x_8);
x_13 = l_List_redLength___rarg(x_12);
x_14 = lean_mk_empty_array_with_capacity(x_13);
lean_dec(x_13);
x_15 = l_List_toArrayAux___rarg(x_12, x_14);
x_16 = l_Lean_Elab_Deriving_DecEq_mkEnumOfNat___closed__1;
x_17 = lean_alloc_closure((void*)(l_Lean_Elab_Deriving_DecEq_mkEnumOfNat___lambda__1___boxed), 11, 5);
lean_closure_set(x_17, 0, x_10);
lean_closure_set(x_17, 1, x_15);
lean_closure_set(x_17, 2, x_11);
lean_closure_set(x_17, 3, x_16);
lean_closure_set(x_17, 4, x_1);
x_18 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__47;
x_19 = 0;
x_20 = l_Lean_Meta_withLocalDecl___at_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___spec__1___rarg(x_18, x_19, x_16, x_17, x_2, x_3, x_4, x_5, x_9);
return x_20;
}
else
{
uint8_t x_21; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_7);
if (x_21 == 0)
{
return x_7;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_7, 0);
x_23 = lean_ctor_get(x_7, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_7);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_DecEq_mkEnumOfNat___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Deriving_DecEq_mkEnumOfNat___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkEnumOfNatThm___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_10; 
lean_dec(x_2);
lean_dec(x_1);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_4);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_3, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
lean_dec(x_3);
lean_inc(x_1);
x_13 = l_Lean_Expr_const___override(x_11, x_1);
lean_inc(x_2);
x_14 = l_Lean_Expr_app___override(x_2, x_13);
x_15 = l_Lean_Expr_app___override(x_4, x_14);
x_3 = x_12;
x_4 = x_15;
goto _start;
}
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkEnumOfNatThm___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("ofNat_toCtorIdx", 15);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_DecEq_mkEnumOfNatThm___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; lean_object* x_22; 
lean_inc(x_8);
x_14 = l_Lean_Expr_app___override(x_1, x_8);
x_15 = l_Lean_Expr_app___override(x_2, x_14);
lean_inc(x_8);
x_16 = l_Lean_mkAppB(x_3, x_15, x_8);
x_17 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__25;
lean_inc(x_8);
x_18 = lean_array_push(x_17, x_8);
x_19 = 0;
x_20 = 1;
x_21 = 1;
lean_inc(x_16);
lean_inc(x_18);
x_22 = l_Lean_Meta_mkLambdaFVars(x_18, x_16, x_19, x_20, x_21, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_casesOnSuffix;
lean_inc(x_4);
x_26 = l_Lean_Name_str___override(x_4, x_25);
x_27 = l_Lean_levelZero;
lean_inc(x_5);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_5);
x_29 = l_Lean_Expr_const___override(x_26, x_28);
x_30 = l_Lean_mkAppB(x_29, x_23, x_8);
lean_inc(x_5);
x_31 = l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkEnumOfNatThm___spec__1(x_5, x_6, x_7, x_30, x_9, x_10, x_11, x_12, x_24);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
lean_inc(x_18);
x_34 = l_Lean_Meta_mkLambdaFVars(x_18, x_32, x_19, x_20, x_21, x_9, x_10, x_11, x_12, x_33);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = l_Lean_Meta_mkForallFVars(x_18, x_16, x_19, x_20, x_21, x_9, x_10, x_11, x_12, x_36);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = l_Lean_Elab_Deriving_DecEq_mkEnumOfNatThm___lambda__1___closed__1;
x_41 = l_Lean_Name_str___override(x_4, x_40);
lean_inc(x_5);
lean_inc(x_41);
x_42 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_5);
lean_ctor_set(x_42, 2, x_38);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_5);
x_44 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_35);
lean_ctor_set(x_44, 2, x_43);
x_45 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_45, 0, x_44);
x_46 = l_Lean_addAndCompile___at_Lean_Meta_evalExprCore___spec__1(x_45, x_9, x_10, x_11, x_12, x_39);
return x_46;
}
else
{
uint8_t x_47; 
lean_dec(x_35);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
x_47 = !lean_is_exclusive(x_37);
if (x_47 == 0)
{
return x_37;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_37, 0);
x_49 = lean_ctor_get(x_37, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_37);
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
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
x_51 = !lean_is_exclusive(x_34);
if (x_51 == 0)
{
return x_34;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_34, 0);
x_53 = lean_ctor_get(x_34, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_34);
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
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_55 = !lean_is_exclusive(x_22);
if (x_55 == 0)
{
return x_22;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_22, 0);
x_57 = lean_ctor_get(x_22, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_22);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkEnumOfNatThm___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("toCtorIdx", 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkEnumOfNatThm___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Eq", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkEnumOfNatThm___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Deriving_DecEq_mkEnumOfNatThm___closed__2;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkEnumOfNatThm___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_levelOne;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkEnumOfNatThm___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkEnumOfNatThm___closed__3;
x_2 = l_Lean_Elab_Deriving_DecEq_mkEnumOfNatThm___closed__4;
x_3 = l_Lean_Expr_const___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkEnumOfNatThm___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("refl", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkEnumOfNatThm___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkEnumOfNatThm___closed__3;
x_2 = l_Lean_Elab_Deriving_DecEq_mkEnumOfNatThm___closed__6;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkEnumOfNatThm___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkEnumOfNatThm___closed__7;
x_2 = l_Lean_Elab_Deriving_DecEq_mkEnumOfNatThm___closed__4;
x_3 = l_Lean_Expr_const___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkEnumOfNatThm___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("x", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkEnumOfNatThm___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Deriving_DecEq_mkEnumOfNatThm___closed__9;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_DecEq_mkEnumOfNatThm(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_1);
x_7 = l_Lean_getConstInfoInduct___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoForKernelRec___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_Elab_Deriving_DecEq_mkEnumOfNatThm___closed__1;
lean_inc(x_1);
x_11 = l_Lean_Name_str___override(x_1, x_10);
x_12 = lean_box(0);
x_13 = l_Lean_Expr_const___override(x_11, x_12);
x_14 = l_Lean_Elab_Deriving_DecEq_mkEnumOfNat___lambda__1___closed__3;
lean_inc(x_1);
x_15 = l_Lean_Name_str___override(x_1, x_14);
x_16 = l_Lean_Expr_const___override(x_15, x_12);
lean_inc(x_1);
x_17 = l_Lean_Expr_const___override(x_1, x_12);
x_18 = l_Lean_Elab_Deriving_DecEq_mkEnumOfNatThm___closed__5;
lean_inc(x_17);
x_19 = l_Lean_Expr_app___override(x_18, x_17);
x_20 = l_Lean_Elab_Deriving_DecEq_mkEnumOfNatThm___closed__8;
lean_inc(x_17);
x_21 = l_Lean_Expr_app___override(x_20, x_17);
x_22 = lean_ctor_get(x_8, 4);
lean_inc(x_22);
lean_dec(x_8);
x_23 = lean_alloc_closure((void*)(l_Lean_Elab_Deriving_DecEq_mkEnumOfNatThm___lambda__1), 13, 7);
lean_closure_set(x_23, 0, x_13);
lean_closure_set(x_23, 1, x_16);
lean_closure_set(x_23, 2, x_19);
lean_closure_set(x_23, 3, x_1);
lean_closure_set(x_23, 4, x_12);
lean_closure_set(x_23, 5, x_21);
lean_closure_set(x_23, 6, x_22);
x_24 = l_Lean_Elab_Deriving_DecEq_mkEnumOfNatThm___closed__10;
x_25 = 0;
x_26 = l_Lean_Meta_withLocalDecl___at_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___spec__1___rarg(x_24, x_25, x_17, x_23, x_2, x_3, x_4, x_5, x_9);
return x_26;
}
else
{
uint8_t x_27; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_7);
if (x_27 == 0)
{
return x_7;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_7, 0);
x_29 = lean_ctor_get(x_7, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_7);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkEnumOfNatThm___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkEnumOfNatThm___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Deriving_DecEq_mkEnumOfNat(x_1, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Deriving_DecEq_mkEnumOfNatThm(x_1, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Command_elabCommand(x_1, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("instance", 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__2;
x_2 = l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("attrKind", 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__6;
x_2 = l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("declSig", 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__2;
x_2 = l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkDecEqHeader___closed__1;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkDecEqHeader___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__7;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Deriving_DecEq_mkDecEqHeader___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__9;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("fun", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__6;
x_2 = l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__11;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("basicFun", 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__6;
x_2 = l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__13;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkEnumOfNatThm___closed__9;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkEnumOfNatThm___closed__9;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__15;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("y", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__17;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__17;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__18;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__17;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__21() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("x.toCtorIdx", 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__21;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__21;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__22;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkEnumOfNatThm___closed__10;
x_2 = l_Lean_Elab_Deriving_DecEq_mkEnumOfNatThm___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__25() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("y.toCtorIdx", 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__25;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__25;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__26;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__28() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__20;
x_2 = l_Lean_Elab_Deriving_DecEq_mkEnumOfNatThm___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__29() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__5;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__30() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__29;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__31() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("first", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__32() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__18;
x_2 = l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__31;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__33() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("tacticHave_", 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__34() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__18;
x_2 = l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__33;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__35() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("aux", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__36() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__35;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__37() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__35;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__36;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__38() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__35;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__39() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("congrArg", 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__40() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__39;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__41() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__39;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__40;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__42() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__39;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__43() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__42;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__44() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__43;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__45() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("rwSeq", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__46() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__18;
x_2 = l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__45;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__47() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("rw", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__48() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("rwRuleSeq", 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__49() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__18;
x_2 = l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__48;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__50() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("[", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__51() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("rwRule", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__52() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__18;
x_2 = l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__51;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__53() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("]", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__54() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("location", 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__55() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__18;
x_2 = l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__54;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__56() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("at", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__57() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("locationHyp", 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__58() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__18;
x_2 = l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__57;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__59() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("tacticRfl", 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__60() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__18;
x_2 = l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__59;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__61() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("contradiction", 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__62() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__18;
x_2 = l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__61;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_DecEq_mkDecEqEnum(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
lean_inc(x_1);
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___lambda__1___boxed), 8, 1);
lean_closure_set(x_5, 0, x_1);
lean_inc(x_2);
x_6 = l_Lean_Elab_Command_liftTermElabM___rarg(x_5, x_2, x_3, x_4);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___lambda__2___boxed), 8, 1);
lean_closure_set(x_8, 0, x_1);
lean_inc(x_2);
x_9 = l_Lean_Elab_Command_liftTermElabM___rarg(x_8, x_2, x_3, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; uint8_t x_367; lean_object* x_368; lean_object* x_379; lean_object* x_380; lean_object* x_381; uint8_t x_382; 
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = l_Lean_Elab_Deriving_DecEq_mkEnumOfNat___lambda__1___closed__3;
lean_inc(x_1);
x_12 = l_Lean_Name_str___override(x_1, x_11);
x_13 = lean_mk_syntax_ident(x_12);
x_14 = l_Lean_Elab_Deriving_DecEq_mkEnumOfNatThm___lambda__1___closed__1;
lean_inc(x_1);
x_15 = l_Lean_Name_str___override(x_1, x_14);
x_16 = lean_mk_syntax_ident(x_15);
x_17 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Command_mkDefViewOfInstance___spec__11(x_2, x_3, x_10);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_Elab_Command_getCurrMacroScope(x_2, x_3, x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_Elab_Command_getMainModule___rarg(x_3, x_22);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__18;
x_27 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__19;
lean_inc(x_18);
x_28 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_28, 0, x_18);
lean_ctor_set(x_28, 1, x_26);
lean_ctor_set(x_28, 2, x_27);
x_29 = l_Lean_Elab_Deriving_DecEq_mkMatch___closed__6;
lean_inc(x_28);
x_30 = lean_array_push(x_29, x_28);
lean_inc(x_28);
x_31 = lean_array_push(x_30, x_28);
lean_inc(x_28);
x_32 = lean_array_push(x_31, x_28);
lean_inc(x_28);
x_33 = lean_array_push(x_32, x_28);
lean_inc(x_28);
x_34 = lean_array_push(x_33, x_28);
lean_inc(x_28);
x_35 = lean_array_push(x_34, x_28);
x_36 = l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__6;
lean_inc(x_18);
x_37 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_37, 0, x_18);
lean_ctor_set(x_37, 1, x_36);
lean_ctor_set(x_37, 2, x_35);
x_38 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__25;
lean_inc(x_28);
x_39 = lean_array_push(x_38, x_28);
x_40 = l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__4;
lean_inc(x_18);
x_41 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_41, 0, x_18);
lean_ctor_set(x_41, 1, x_40);
lean_ctor_set(x_41, 2, x_39);
x_42 = l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__1;
lean_inc(x_18);
x_43 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_43, 0, x_18);
lean_ctor_set(x_43, 1, x_42);
x_44 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__8;
lean_inc(x_18);
x_45 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_45, 0, x_18);
lean_ctor_set(x_45, 1, x_44);
x_46 = l_Lean_Elab_Deriving_DecEq_mkDecEqHeader___closed__2;
lean_inc(x_21);
lean_inc(x_24);
x_47 = l_Lean_addMacroScope(x_24, x_46, x_21);
x_48 = lean_box(0);
x_49 = l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__8;
x_50 = l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__10;
lean_inc(x_18);
x_51 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_51, 0, x_18);
lean_ctor_set(x_51, 1, x_49);
lean_ctor_set(x_51, 2, x_47);
lean_ctor_set(x_51, 3, x_50);
x_52 = lean_mk_syntax_ident(x_1);
x_53 = lean_array_push(x_38, x_52);
lean_inc(x_18);
x_54 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_54, 0, x_18);
lean_ctor_set(x_54, 1, x_26);
lean_ctor_set(x_54, 2, x_53);
x_55 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__23;
x_56 = lean_array_push(x_55, x_51);
x_57 = lean_array_push(x_56, x_54);
x_58 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__22;
lean_inc(x_18);
x_59 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_59, 0, x_18);
lean_ctor_set(x_59, 1, x_58);
lean_ctor_set(x_59, 2, x_57);
lean_inc(x_45);
x_60 = lean_array_push(x_55, x_45);
x_61 = lean_array_push(x_60, x_59);
x_62 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__3___closed__8;
lean_inc(x_18);
x_63 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_63, 0, x_18);
lean_ctor_set(x_63, 1, x_62);
lean_ctor_set(x_63, 2, x_61);
lean_inc(x_28);
x_64 = lean_array_push(x_55, x_28);
lean_inc(x_64);
x_65 = lean_array_push(x_64, x_63);
x_66 = l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__6;
lean_inc(x_18);
x_67 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_67, 0, x_18);
lean_ctor_set(x_67, 1, x_66);
lean_ctor_set(x_67, 2, x_65);
x_68 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__20;
lean_inc(x_18);
x_69 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_69, 0, x_18);
lean_ctor_set(x_69, 1, x_68);
x_70 = l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__11;
lean_inc(x_18);
x_71 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_71, 0, x_18);
lean_ctor_set(x_71, 1, x_70);
x_72 = l_Lean_Elab_Deriving_DecEq_mkEnumOfNatThm___closed__10;
lean_inc(x_21);
lean_inc(x_24);
x_73 = l_Lean_addMacroScope(x_24, x_72, x_21);
x_74 = l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__16;
lean_inc(x_18);
x_75 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_75, 0, x_18);
lean_ctor_set(x_75, 1, x_74);
lean_ctor_set(x_75, 2, x_73);
lean_ctor_set(x_75, 3, x_48);
x_76 = l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__20;
lean_inc(x_21);
lean_inc(x_24);
x_77 = l_Lean_addMacroScope(x_24, x_76, x_21);
x_78 = l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__19;
lean_inc(x_18);
x_79 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_79, 0, x_18);
lean_ctor_set(x_79, 1, x_78);
lean_ctor_set(x_79, 2, x_77);
lean_ctor_set(x_79, 3, x_48);
x_80 = lean_array_push(x_55, x_75);
x_81 = lean_array_push(x_80, x_79);
lean_inc(x_18);
x_82 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_82, 0, x_18);
lean_ctor_set(x_82, 1, x_26);
lean_ctor_set(x_82, 2, x_81);
x_83 = l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1___closed__11;
lean_inc(x_18);
x_84 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_84, 0, x_18);
lean_ctor_set(x_84, 1, x_83);
x_85 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__3;
lean_inc(x_18);
x_86 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_86, 0, x_18);
lean_ctor_set(x_86, 1, x_85);
x_87 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__7;
lean_inc(x_21);
lean_inc(x_24);
x_88 = l_Lean_addMacroScope(x_24, x_87, x_21);
x_89 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__6;
lean_inc(x_18);
x_90 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_90, 0, x_18);
lean_ctor_set(x_90, 1, x_89);
lean_ctor_set(x_90, 2, x_88);
lean_ctor_set(x_90, 3, x_48);
x_91 = l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__24;
lean_inc(x_21);
lean_inc(x_24);
x_92 = l_Lean_addMacroScope(x_24, x_91, x_21);
x_93 = l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__23;
lean_inc(x_18);
x_94 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_94, 0, x_18);
lean_ctor_set(x_94, 1, x_93);
lean_ctor_set(x_94, 2, x_92);
lean_ctor_set(x_94, 3, x_48);
x_95 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__11;
lean_inc(x_18);
x_96 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_96, 0, x_18);
lean_ctor_set(x_96, 1, x_95);
x_97 = l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__28;
lean_inc(x_21);
lean_inc(x_24);
x_98 = l_Lean_addMacroScope(x_24, x_97, x_21);
x_99 = l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__27;
lean_inc(x_18);
x_100 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_100, 0, x_18);
lean_ctor_set(x_100, 1, x_99);
lean_ctor_set(x_100, 2, x_98);
lean_ctor_set(x_100, 3, x_48);
x_101 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__12;
x_102 = lean_array_push(x_101, x_94);
x_103 = lean_array_push(x_102, x_96);
x_104 = lean_array_push(x_103, x_100);
x_105 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__10;
lean_inc(x_18);
x_106 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_106, 0, x_18);
lean_ctor_set(x_106, 1, x_105);
lean_ctor_set(x_106, 2, x_104);
x_107 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__13;
lean_inc(x_18);
x_108 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_108, 0, x_18);
lean_ctor_set(x_108, 1, x_107);
x_109 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__4;
lean_inc(x_21);
lean_inc(x_24);
x_110 = l_Lean_addMacroScope(x_24, x_109, x_21);
x_111 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__3;
x_112 = l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__30;
lean_inc(x_18);
x_113 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_113, 0, x_18);
lean_ctor_set(x_113, 1, x_111);
lean_ctor_set(x_113, 2, x_110);
lean_ctor_set(x_113, 3, x_112);
x_114 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__41;
lean_inc(x_18);
x_115 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_115, 0, x_18);
lean_ctor_set(x_115, 1, x_114);
x_116 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__16;
lean_inc(x_18);
x_117 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_117, 0, x_18);
lean_ctor_set(x_117, 1, x_116);
x_118 = l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__31;
lean_inc(x_18);
x_119 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_119, 0, x_18);
lean_ctor_set(x_119, 1, x_118);
x_120 = l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1___closed__8;
lean_inc(x_18);
x_121 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_121, 0, x_18);
lean_ctor_set(x_121, 1, x_120);
x_122 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__3___closed__1;
lean_inc(x_18);
x_123 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_123, 0, x_18);
lean_ctor_set(x_123, 1, x_122);
x_124 = l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__38;
lean_inc(x_21);
lean_inc(x_24);
x_125 = l_Lean_addMacroScope(x_24, x_124, x_21);
x_126 = l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__37;
lean_inc(x_18);
x_127 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_127, 0, x_18);
lean_ctor_set(x_127, 1, x_126);
lean_ctor_set(x_127, 2, x_125);
lean_ctor_set(x_127, 3, x_48);
lean_inc(x_127);
x_128 = lean_array_push(x_55, x_127);
lean_inc(x_28);
x_129 = lean_array_push(x_128, x_28);
lean_inc(x_18);
x_130 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_130, 0, x_18);
lean_ctor_set(x_130, 1, x_26);
lean_ctor_set(x_130, 2, x_129);
x_131 = l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__42;
lean_inc(x_21);
lean_inc(x_24);
x_132 = l_Lean_addMacroScope(x_24, x_131, x_21);
x_133 = l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__41;
x_134 = l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__44;
lean_inc(x_18);
x_135 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_135, 0, x_18);
lean_ctor_set(x_135, 1, x_133);
lean_ctor_set(x_135, 2, x_132);
lean_ctor_set(x_135, 3, x_134);
x_136 = lean_array_push(x_55, x_13);
lean_inc(x_90);
x_137 = lean_array_push(x_136, x_90);
lean_inc(x_18);
x_138 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_138, 0, x_18);
lean_ctor_set(x_138, 1, x_26);
lean_ctor_set(x_138, 2, x_137);
x_139 = lean_array_push(x_55, x_135);
x_140 = lean_array_push(x_139, x_138);
lean_inc(x_18);
x_141 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_141, 0, x_18);
lean_ctor_set(x_141, 1, x_58);
lean_ctor_set(x_141, 2, x_140);
x_142 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__27;
x_143 = lean_array_push(x_142, x_130);
lean_inc(x_28);
x_144 = lean_array_push(x_143, x_28);
lean_inc(x_69);
x_145 = lean_array_push(x_144, x_69);
x_146 = lean_array_push(x_145, x_141);
x_147 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__3___closed__6;
lean_inc(x_18);
x_148 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_148, 0, x_18);
lean_ctor_set(x_148, 1, x_147);
lean_ctor_set(x_148, 2, x_146);
x_149 = lean_array_push(x_38, x_148);
x_150 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__3___closed__4;
lean_inc(x_18);
x_151 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_151, 0, x_18);
lean_ctor_set(x_151, 1, x_150);
lean_ctor_set(x_151, 2, x_149);
x_152 = lean_array_push(x_55, x_123);
x_153 = lean_array_push(x_152, x_151);
x_154 = l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__34;
lean_inc(x_18);
x_155 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_155, 0, x_18);
lean_ctor_set(x_155, 1, x_154);
lean_ctor_set(x_155, 2, x_153);
x_156 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__26;
lean_inc(x_18);
x_157 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_157, 0, x_18);
lean_ctor_set(x_157, 1, x_156);
x_158 = lean_array_push(x_38, x_157);
lean_inc(x_18);
x_159 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_159, 0, x_18);
lean_ctor_set(x_159, 1, x_26);
lean_ctor_set(x_159, 2, x_158);
x_160 = lean_array_push(x_55, x_155);
lean_inc(x_159);
x_161 = lean_array_push(x_160, x_159);
x_162 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__24;
lean_inc(x_18);
x_163 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_163, 0, x_18);
lean_ctor_set(x_163, 1, x_162);
lean_ctor_set(x_163, 2, x_161);
x_164 = l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__47;
lean_inc(x_18);
x_165 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_165, 0, x_18);
lean_ctor_set(x_165, 1, x_164);
x_166 = l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__50;
lean_inc(x_18);
x_167 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_167, 0, x_18);
lean_ctor_set(x_167, 1, x_166);
x_168 = lean_array_push(x_64, x_16);
x_169 = l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__52;
lean_inc(x_18);
x_170 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_170, 0, x_18);
lean_ctor_set(x_170, 1, x_169);
lean_ctor_set(x_170, 2, x_168);
x_171 = l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1___closed__9;
lean_inc(x_18);
x_172 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_172, 0, x_18);
lean_ctor_set(x_172, 1, x_171);
lean_inc(x_170);
x_173 = lean_array_push(x_101, x_170);
x_174 = lean_array_push(x_173, x_172);
x_175 = lean_array_push(x_174, x_170);
lean_inc(x_18);
x_176 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_176, 0, x_18);
lean_ctor_set(x_176, 1, x_26);
lean_ctor_set(x_176, 2, x_175);
x_177 = l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__53;
lean_inc(x_18);
x_178 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_178, 0, x_18);
lean_ctor_set(x_178, 1, x_177);
x_179 = lean_array_push(x_101, x_167);
x_180 = lean_array_push(x_179, x_176);
x_181 = lean_array_push(x_180, x_178);
x_182 = l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__49;
lean_inc(x_18);
x_183 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_183, 0, x_18);
lean_ctor_set(x_183, 1, x_182);
lean_ctor_set(x_183, 2, x_181);
x_184 = l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__56;
lean_inc(x_18);
x_185 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_185, 0, x_18);
lean_ctor_set(x_185, 1, x_184);
x_186 = lean_array_push(x_38, x_127);
lean_inc(x_18);
x_187 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_187, 0, x_18);
lean_ctor_set(x_187, 1, x_26);
lean_ctor_set(x_187, 2, x_186);
x_188 = lean_array_push(x_55, x_187);
lean_inc(x_28);
x_189 = lean_array_push(x_188, x_28);
x_190 = l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__58;
lean_inc(x_18);
x_191 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_191, 0, x_18);
lean_ctor_set(x_191, 1, x_190);
lean_ctor_set(x_191, 2, x_189);
x_192 = lean_array_push(x_55, x_185);
x_193 = lean_array_push(x_192, x_191);
x_194 = l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__55;
lean_inc(x_18);
x_195 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_195, 0, x_18);
lean_ctor_set(x_195, 1, x_194);
lean_ctor_set(x_195, 2, x_193);
x_196 = lean_array_push(x_38, x_195);
lean_inc(x_18);
x_197 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_197, 0, x_18);
lean_ctor_set(x_197, 1, x_26);
lean_ctor_set(x_197, 2, x_196);
x_198 = lean_array_push(x_142, x_165);
lean_inc(x_28);
x_199 = lean_array_push(x_198, x_28);
x_200 = lean_array_push(x_199, x_183);
x_201 = lean_array_push(x_200, x_197);
x_202 = l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__46;
lean_inc(x_18);
x_203 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_203, 0, x_18);
lean_ctor_set(x_203, 1, x_202);
lean_ctor_set(x_203, 2, x_201);
x_204 = lean_array_push(x_55, x_203);
lean_inc(x_159);
x_205 = lean_array_push(x_204, x_159);
lean_inc(x_18);
x_206 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_206, 0, x_18);
lean_ctor_set(x_206, 1, x_162);
lean_ctor_set(x_206, 2, x_205);
x_207 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__55;
lean_inc(x_18);
x_208 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_208, 0, x_18);
lean_ctor_set(x_208, 1, x_207);
x_209 = lean_array_push(x_38, x_208);
x_210 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__56;
lean_inc(x_18);
x_211 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_211, 0, x_18);
lean_ctor_set(x_211, 1, x_210);
lean_ctor_set(x_211, 2, x_209);
x_212 = lean_array_push(x_55, x_211);
lean_inc(x_28);
x_213 = lean_array_push(x_212, x_28);
lean_inc(x_18);
x_214 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_214, 0, x_18);
lean_ctor_set(x_214, 1, x_162);
lean_ctor_set(x_214, 2, x_213);
x_215 = lean_array_push(x_101, x_163);
x_216 = lean_array_push(x_215, x_206);
x_217 = lean_array_push(x_216, x_214);
lean_inc(x_18);
x_218 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_218, 0, x_18);
lean_ctor_set(x_218, 1, x_26);
lean_ctor_set(x_218, 2, x_217);
x_219 = lean_array_push(x_38, x_218);
x_220 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__22;
lean_inc(x_18);
x_221 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_221, 0, x_18);
lean_ctor_set(x_221, 1, x_220);
lean_ctor_set(x_221, 2, x_219);
x_222 = lean_array_push(x_38, x_221);
x_223 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__20;
lean_inc(x_18);
x_224 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_224, 0, x_18);
lean_ctor_set(x_224, 1, x_223);
lean_ctor_set(x_224, 2, x_222);
x_225 = lean_array_push(x_55, x_121);
lean_inc(x_225);
x_226 = lean_array_push(x_225, x_224);
lean_inc(x_18);
x_227 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_227, 0, x_18);
lean_ctor_set(x_227, 1, x_162);
lean_ctor_set(x_227, 2, x_226);
x_228 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__3___closed__9;
lean_inc(x_18);
x_229 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_229, 0, x_18);
lean_ctor_set(x_229, 1, x_228);
x_230 = lean_array_push(x_38, x_229);
x_231 = l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__60;
lean_inc(x_18);
x_232 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_232, 0, x_18);
lean_ctor_set(x_232, 1, x_231);
lean_ctor_set(x_232, 2, x_230);
x_233 = lean_array_push(x_55, x_232);
lean_inc(x_28);
x_234 = lean_array_push(x_233, x_28);
lean_inc(x_18);
x_235 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_235, 0, x_18);
lean_ctor_set(x_235, 1, x_162);
lean_ctor_set(x_235, 2, x_234);
x_236 = lean_array_push(x_38, x_235);
lean_inc(x_18);
x_237 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_237, 0, x_18);
lean_ctor_set(x_237, 1, x_26);
lean_ctor_set(x_237, 2, x_236);
x_238 = lean_array_push(x_38, x_237);
lean_inc(x_18);
x_239 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_239, 0, x_18);
lean_ctor_set(x_239, 1, x_220);
lean_ctor_set(x_239, 2, x_238);
x_240 = lean_array_push(x_38, x_239);
lean_inc(x_18);
x_241 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_241, 0, x_18);
lean_ctor_set(x_241, 1, x_223);
lean_ctor_set(x_241, 2, x_240);
x_242 = lean_array_push(x_225, x_241);
lean_inc(x_18);
x_243 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_243, 0, x_18);
lean_ctor_set(x_243, 1, x_162);
lean_ctor_set(x_243, 2, x_242);
x_244 = lean_array_push(x_55, x_227);
x_245 = lean_array_push(x_244, x_243);
lean_inc(x_18);
x_246 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_246, 0, x_18);
lean_ctor_set(x_246, 1, x_26);
lean_ctor_set(x_246, 2, x_245);
x_247 = lean_array_push(x_55, x_119);
x_248 = lean_array_push(x_247, x_246);
x_249 = l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__32;
lean_inc(x_18);
x_250 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_250, 0, x_18);
lean_ctor_set(x_250, 1, x_249);
lean_ctor_set(x_250, 2, x_248);
x_251 = lean_array_push(x_55, x_250);
lean_inc(x_28);
x_252 = lean_array_push(x_251, x_28);
lean_inc(x_18);
x_253 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_253, 0, x_18);
lean_ctor_set(x_253, 1, x_162);
lean_ctor_set(x_253, 2, x_252);
x_254 = lean_array_push(x_38, x_253);
lean_inc(x_18);
x_255 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_255, 0, x_18);
lean_ctor_set(x_255, 1, x_26);
lean_ctor_set(x_255, 2, x_254);
x_256 = lean_array_push(x_38, x_255);
lean_inc(x_18);
x_257 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_257, 0, x_18);
lean_ctor_set(x_257, 1, x_220);
lean_ctor_set(x_257, 2, x_256);
x_258 = lean_array_push(x_38, x_257);
lean_inc(x_18);
x_259 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_259, 0, x_18);
lean_ctor_set(x_259, 1, x_223);
lean_ctor_set(x_259, 2, x_258);
x_260 = lean_array_push(x_55, x_117);
lean_inc(x_260);
x_261 = lean_array_push(x_260, x_259);
x_262 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__15;
lean_inc(x_18);
x_263 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_263, 0, x_18);
lean_ctor_set(x_263, 1, x_262);
lean_ctor_set(x_263, 2, x_261);
x_264 = lean_array_push(x_55, x_263);
lean_inc(x_28);
x_265 = lean_array_push(x_264, x_28);
lean_inc(x_18);
x_266 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_266, 0, x_18);
lean_ctor_set(x_266, 1, x_26);
lean_ctor_set(x_266, 2, x_265);
x_267 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__57;
lean_inc(x_18);
x_268 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_268, 0, x_18);
lean_ctor_set(x_268, 1, x_267);
x_269 = lean_array_push(x_101, x_115);
x_270 = lean_array_push(x_269, x_266);
x_271 = lean_array_push(x_270, x_268);
x_272 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__40;
lean_inc(x_18);
x_273 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_273, 0, x_18);
lean_ctor_set(x_273, 1, x_272);
lean_ctor_set(x_273, 2, x_271);
x_274 = lean_array_push(x_38, x_273);
lean_inc(x_18);
x_275 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_275, 0, x_18);
lean_ctor_set(x_275, 1, x_26);
lean_ctor_set(x_275, 2, x_274);
x_276 = lean_array_push(x_55, x_113);
x_277 = lean_array_push(x_276, x_275);
lean_inc(x_18);
x_278 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_278, 0, x_18);
lean_ctor_set(x_278, 1, x_58);
lean_ctor_set(x_278, 2, x_277);
x_279 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__29;
lean_inc(x_18);
x_280 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_280, 0, x_18);
lean_ctor_set(x_280, 1, x_279);
x_281 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__33;
x_282 = l_Lean_addMacroScope(x_24, x_281, x_21);
x_283 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__32;
x_284 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__38;
lean_inc(x_18);
x_285 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_285, 0, x_18);
lean_ctor_set(x_285, 1, x_283);
lean_ctor_set(x_285, 2, x_282);
lean_ctor_set(x_285, 3, x_284);
lean_inc(x_90);
x_286 = lean_array_push(x_38, x_90);
lean_inc(x_18);
x_287 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_287, 0, x_18);
lean_ctor_set(x_287, 1, x_26);
lean_ctor_set(x_287, 2, x_286);
x_288 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__25;
lean_inc(x_18);
x_289 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_289, 0, x_18);
lean_ctor_set(x_289, 1, x_288);
x_290 = lean_array_push(x_55, x_289);
lean_inc(x_287);
x_291 = lean_array_push(x_290, x_287);
x_292 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__26;
lean_inc(x_18);
x_293 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_293, 0, x_18);
lean_ctor_set(x_293, 1, x_292);
lean_ctor_set(x_293, 2, x_291);
x_294 = lean_array_push(x_55, x_293);
x_295 = lean_array_push(x_294, x_159);
lean_inc(x_18);
x_296 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_296, 0, x_18);
lean_ctor_set(x_296, 1, x_162);
lean_ctor_set(x_296, 2, x_295);
x_297 = l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__61;
lean_inc(x_18);
x_298 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_298, 0, x_18);
lean_ctor_set(x_298, 1, x_297);
x_299 = lean_array_push(x_38, x_298);
x_300 = l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__62;
lean_inc(x_18);
x_301 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_301, 0, x_18);
lean_ctor_set(x_301, 1, x_300);
lean_ctor_set(x_301, 2, x_299);
x_302 = lean_array_push(x_55, x_301);
lean_inc(x_28);
x_303 = lean_array_push(x_302, x_28);
lean_inc(x_18);
x_304 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_304, 0, x_18);
lean_ctor_set(x_304, 1, x_162);
lean_ctor_set(x_304, 2, x_303);
x_305 = lean_array_push(x_55, x_296);
x_306 = lean_array_push(x_305, x_304);
lean_inc(x_18);
x_307 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_307, 0, x_18);
lean_ctor_set(x_307, 1, x_26);
lean_ctor_set(x_307, 2, x_306);
x_308 = lean_array_push(x_38, x_307);
lean_inc(x_18);
x_309 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_309, 0, x_18);
lean_ctor_set(x_309, 1, x_220);
lean_ctor_set(x_309, 2, x_308);
x_310 = lean_array_push(x_38, x_309);
lean_inc(x_18);
x_311 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_311, 0, x_18);
lean_ctor_set(x_311, 1, x_223);
lean_ctor_set(x_311, 2, x_310);
x_312 = lean_array_push(x_260, x_311);
lean_inc(x_18);
x_313 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_313, 0, x_18);
lean_ctor_set(x_313, 1, x_262);
lean_ctor_set(x_313, 2, x_312);
x_314 = lean_array_push(x_142, x_287);
lean_inc(x_28);
x_315 = lean_array_push(x_314, x_28);
lean_inc(x_84);
x_316 = lean_array_push(x_315, x_84);
x_317 = lean_array_push(x_316, x_313);
x_318 = l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__14;
lean_inc(x_18);
x_319 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_319, 0, x_18);
lean_ctor_set(x_319, 1, x_318);
lean_ctor_set(x_319, 2, x_317);
x_320 = lean_array_push(x_55, x_71);
lean_inc(x_320);
x_321 = lean_array_push(x_320, x_319);
x_322 = l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__12;
lean_inc(x_18);
x_323 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_323, 0, x_18);
lean_ctor_set(x_323, 1, x_322);
lean_ctor_set(x_323, 2, x_321);
x_324 = lean_array_push(x_38, x_323);
lean_inc(x_18);
x_325 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_325, 0, x_18);
lean_ctor_set(x_325, 1, x_26);
lean_ctor_set(x_325, 2, x_324);
x_326 = lean_array_push(x_55, x_285);
x_327 = lean_array_push(x_326, x_325);
lean_inc(x_18);
x_328 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_328, 0, x_18);
lean_ctor_set(x_328, 1, x_58);
lean_ctor_set(x_328, 2, x_327);
x_329 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__58;
x_330 = lean_array_push(x_329, x_86);
x_331 = lean_array_push(x_330, x_90);
x_332 = lean_array_push(x_331, x_45);
x_333 = lean_array_push(x_332, x_106);
x_334 = lean_array_push(x_333, x_108);
x_335 = lean_array_push(x_334, x_278);
x_336 = lean_array_push(x_335, x_280);
x_337 = lean_array_push(x_336, x_328);
x_338 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__2;
lean_inc(x_18);
x_339 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_339, 0, x_18);
lean_ctor_set(x_339, 1, x_338);
lean_ctor_set(x_339, 2, x_337);
x_340 = lean_array_push(x_142, x_82);
lean_inc(x_28);
x_341 = lean_array_push(x_340, x_28);
x_342 = lean_array_push(x_341, x_84);
x_343 = lean_array_push(x_342, x_339);
lean_inc(x_18);
x_344 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_344, 0, x_18);
lean_ctor_set(x_344, 1, x_318);
lean_ctor_set(x_344, 2, x_343);
x_345 = lean_array_push(x_320, x_344);
lean_inc(x_18);
x_346 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_346, 0, x_18);
lean_ctor_set(x_346, 1, x_322);
lean_ctor_set(x_346, 2, x_345);
x_347 = lean_array_push(x_101, x_69);
x_348 = lean_array_push(x_347, x_346);
lean_inc(x_28);
x_349 = lean_array_push(x_348, x_28);
x_350 = l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__16;
lean_inc(x_18);
x_351 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_351, 0, x_18);
lean_ctor_set(x_351, 1, x_350);
lean_ctor_set(x_351, 2, x_349);
x_352 = lean_array_push(x_329, x_41);
x_353 = lean_array_push(x_352, x_43);
lean_inc(x_28);
x_354 = lean_array_push(x_353, x_28);
lean_inc(x_28);
x_355 = lean_array_push(x_354, x_28);
x_356 = lean_array_push(x_355, x_67);
x_357 = lean_array_push(x_356, x_351);
lean_inc(x_28);
x_358 = lean_array_push(x_357, x_28);
x_359 = lean_array_push(x_358, x_28);
x_360 = l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__2;
lean_inc(x_18);
x_361 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_361, 0, x_18);
lean_ctor_set(x_361, 1, x_360);
lean_ctor_set(x_361, 2, x_359);
x_362 = lean_array_push(x_55, x_37);
x_363 = lean_array_push(x_362, x_361);
x_364 = l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__4;
x_365 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_365, 0, x_18);
lean_ctor_set(x_365, 1, x_364);
lean_ctor_set(x_365, 2, x_363);
x_366 = l_Lean_Elab_Deriving_DecEq_mkDecEqCmds___closed__6;
x_379 = lean_st_ref_get(x_3, x_25);
x_380 = lean_ctor_get(x_379, 0);
lean_inc(x_380);
x_381 = lean_ctor_get(x_380, 8);
lean_inc(x_381);
lean_dec(x_380);
x_382 = lean_ctor_get_uint8(x_381, sizeof(void*)*1);
lean_dec(x_381);
if (x_382 == 0)
{
lean_object* x_383; uint8_t x_384; 
x_383 = lean_ctor_get(x_379, 1);
lean_inc(x_383);
lean_dec(x_379);
x_384 = 0;
x_367 = x_384;
x_368 = x_383;
goto block_378;
}
else
{
lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; uint8_t x_389; 
x_385 = lean_ctor_get(x_379, 1);
lean_inc(x_385);
lean_dec(x_379);
x_386 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Elab_Command_elabCommand___spec__7(x_366, x_2, x_3, x_385);
x_387 = lean_ctor_get(x_386, 0);
lean_inc(x_387);
x_388 = lean_ctor_get(x_386, 1);
lean_inc(x_388);
lean_dec(x_386);
x_389 = lean_unbox(x_387);
lean_dec(x_387);
x_367 = x_389;
x_368 = x_388;
goto block_378;
}
block_378:
{
if (x_367 == 0)
{
lean_object* x_369; 
x_369 = l_Lean_Elab_Command_elabCommand(x_365, x_2, x_3, x_368);
return x_369;
}
else
{
lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; 
lean_inc(x_365);
x_370 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_370, 0, x_365);
x_371 = l_Lean_Elab_Deriving_DecEq_mkDecEqCmds___closed__8;
x_372 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_372, 0, x_371);
lean_ctor_set(x_372, 1, x_370);
x_373 = l_Lean_Elab_Deriving_DecEq_mkDecEqCmds___closed__10;
x_374 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_374, 0, x_372);
lean_ctor_set(x_374, 1, x_373);
x_375 = l_Lean_addTrace___at_Lean_Elab_Command_elabCommand___spec__8(x_366, x_374, x_2, x_3, x_368);
x_376 = lean_ctor_get(x_375, 1);
lean_inc(x_376);
lean_dec(x_375);
x_377 = l_Lean_Elab_Command_elabCommand(x_365, x_2, x_3, x_376);
return x_377;
}
}
}
else
{
uint8_t x_390; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_390 = !lean_is_exclusive(x_9);
if (x_390 == 0)
{
return x_9;
}
else
{
lean_object* x_391; lean_object* x_392; lean_object* x_393; 
x_391 = lean_ctor_get(x_9, 0);
x_392 = lean_ctor_get(x_9, 1);
lean_inc(x_392);
lean_inc(x_391);
lean_dec(x_9);
x_393 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_393, 0, x_391);
lean_ctor_set(x_393, 1, x_392);
return x_393;
}
}
}
else
{
uint8_t x_394; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_394 = !lean_is_exclusive(x_6);
if (x_394 == 0)
{
return x_6;
}
else
{
lean_object* x_395; lean_object* x_396; lean_object* x_397; 
x_395 = lean_ctor_get(x_6, 0);
x_396 = lean_ctor_get(x_6, 1);
lean_inc(x_396);
lean_inc(x_395);
lean_dec(x_6);
x_397 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_397, 0, x_395);
lean_ctor_set(x_397, 1, x_396);
return x_397;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___lambda__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_List_allM___at_Lean_Elab_Deriving_DecEq_mkDecEqInstanceHandler___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_5 = 1;
x_6 = lean_box(x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_17; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_dec(x_1);
lean_inc(x_2);
x_17 = l_Lean_getConstInfo___at_Lean_Elab_elabDeriving___spec__17(x_8, x_2, x_3, x_4);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 6)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_ctor_get(x_20, 4);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_nat_dec_eq(x_21, x_22);
lean_dec(x_21);
x_10 = x_23;
x_11 = x_19;
goto block_16;
}
else
{
lean_object* x_24; uint8_t x_25; 
lean_dec(x_18);
x_24 = lean_ctor_get(x_17, 1);
lean_inc(x_24);
lean_dec(x_17);
x_25 = 0;
x_10 = x_25;
x_11 = x_24;
goto block_16;
}
}
else
{
uint8_t x_26; 
lean_dec(x_9);
lean_dec(x_2);
x_26 = !lean_is_exclusive(x_17);
if (x_26 == 0)
{
return x_17;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_17, 0);
x_28 = lean_ctor_get(x_17, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_17);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
block_16:
{
if (x_10 == 0)
{
uint8_t x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_9);
lean_dec(x_2);
x_12 = 0;
x_13 = lean_box(x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
else
{
x_1 = x_9;
x_4 = x_11;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isEnumType___at_Lean_Elab_Deriving_DecEq_mkDecEqInstanceHandler___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_2);
x_5 = l_Lean_getConstInfo___at_Lean_Elab_elabDeriving___spec__17(x_1, x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 5)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_8 = lean_ctor_get(x_5, 1);
x_9 = lean_ctor_get(x_5, 0);
lean_dec(x_9);
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_10);
lean_dec(x_6);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_11, 2);
lean_inc(x_12);
lean_dec(x_11);
x_13 = l_Lean_Expr_isProp(x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_14 = lean_ctor_get(x_10, 3);
lean_inc(x_14);
x_15 = lean_unsigned_to_nat(0u);
x_16 = l_List_lengthTRAux___rarg(x_14, x_15);
lean_dec(x_14);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_dec_eq(x_16, x_17);
lean_dec(x_16);
if (x_18 == 0)
{
uint8_t x_19; lean_object* x_20; 
lean_dec(x_10);
lean_dec(x_2);
x_19 = 0;
x_20 = lean_box(x_19);
lean_ctor_set(x_5, 0, x_20);
return x_5;
}
else
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_10, 2);
lean_inc(x_21);
x_22 = lean_nat_dec_eq(x_21, x_15);
lean_dec(x_21);
if (x_22 == 0)
{
uint8_t x_23; lean_object* x_24; 
lean_dec(x_10);
lean_dec(x_2);
x_23 = 0;
x_24 = lean_box(x_23);
lean_ctor_set(x_5, 0, x_24);
return x_5;
}
else
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_10, 1);
lean_inc(x_25);
x_26 = lean_nat_dec_eq(x_25, x_15);
lean_dec(x_25);
if (x_26 == 0)
{
uint8_t x_27; lean_object* x_28; 
lean_dec(x_10);
lean_dec(x_2);
x_27 = 0;
x_28 = lean_box(x_27);
lean_ctor_set(x_5, 0, x_28);
return x_5;
}
else
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_10, 4);
lean_inc(x_29);
x_30 = l_List_isEmpty___rarg(x_29);
if (x_30 == 0)
{
uint8_t x_31; 
x_31 = lean_ctor_get_uint8(x_10, sizeof(void*)*5);
if (x_31 == 0)
{
uint8_t x_32; 
x_32 = lean_ctor_get_uint8(x_10, sizeof(void*)*5 + 3);
if (x_32 == 0)
{
uint8_t x_33; 
x_33 = lean_ctor_get_uint8(x_10, sizeof(void*)*5 + 1);
lean_dec(x_10);
if (x_33 == 0)
{
lean_object* x_34; 
lean_free_object(x_5);
x_34 = l_List_allM___at_Lean_Elab_Deriving_DecEq_mkDecEqInstanceHandler___spec__2(x_29, x_2, x_3, x_8);
return x_34;
}
else
{
uint8_t x_35; lean_object* x_36; 
lean_dec(x_29);
lean_dec(x_2);
x_35 = 0;
x_36 = lean_box(x_35);
lean_ctor_set(x_5, 0, x_36);
return x_5;
}
}
else
{
uint8_t x_37; lean_object* x_38; 
lean_dec(x_29);
lean_dec(x_10);
lean_dec(x_2);
x_37 = 0;
x_38 = lean_box(x_37);
lean_ctor_set(x_5, 0, x_38);
return x_5;
}
}
else
{
uint8_t x_39; lean_object* x_40; 
lean_dec(x_29);
lean_dec(x_10);
lean_dec(x_2);
x_39 = 0;
x_40 = lean_box(x_39);
lean_ctor_set(x_5, 0, x_40);
return x_5;
}
}
else
{
uint8_t x_41; lean_object* x_42; 
lean_dec(x_29);
lean_dec(x_10);
lean_dec(x_2);
x_41 = 0;
x_42 = lean_box(x_41);
lean_ctor_set(x_5, 0, x_42);
return x_5;
}
}
}
}
}
else
{
uint8_t x_43; lean_object* x_44; 
lean_dec(x_10);
lean_dec(x_2);
x_43 = 0;
x_44 = lean_box(x_43);
lean_ctor_set(x_5, 0, x_44);
return x_5;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_45 = lean_ctor_get(x_5, 1);
lean_inc(x_45);
lean_dec(x_5);
x_46 = lean_ctor_get(x_6, 0);
lean_inc(x_46);
lean_dec(x_6);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_47, 2);
lean_inc(x_48);
lean_dec(x_47);
x_49 = l_Lean_Expr_isProp(x_48);
lean_dec(x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_50 = lean_ctor_get(x_46, 3);
lean_inc(x_50);
x_51 = lean_unsigned_to_nat(0u);
x_52 = l_List_lengthTRAux___rarg(x_50, x_51);
lean_dec(x_50);
x_53 = lean_unsigned_to_nat(1u);
x_54 = lean_nat_dec_eq(x_52, x_53);
lean_dec(x_52);
if (x_54 == 0)
{
uint8_t x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_46);
lean_dec(x_2);
x_55 = 0;
x_56 = lean_box(x_55);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_45);
return x_57;
}
else
{
lean_object* x_58; uint8_t x_59; 
x_58 = lean_ctor_get(x_46, 2);
lean_inc(x_58);
x_59 = lean_nat_dec_eq(x_58, x_51);
lean_dec(x_58);
if (x_59 == 0)
{
uint8_t x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_46);
lean_dec(x_2);
x_60 = 0;
x_61 = lean_box(x_60);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_45);
return x_62;
}
else
{
lean_object* x_63; uint8_t x_64; 
x_63 = lean_ctor_get(x_46, 1);
lean_inc(x_63);
x_64 = lean_nat_dec_eq(x_63, x_51);
lean_dec(x_63);
if (x_64 == 0)
{
uint8_t x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_46);
lean_dec(x_2);
x_65 = 0;
x_66 = lean_box(x_65);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_45);
return x_67;
}
else
{
lean_object* x_68; uint8_t x_69; 
x_68 = lean_ctor_get(x_46, 4);
lean_inc(x_68);
x_69 = l_List_isEmpty___rarg(x_68);
if (x_69 == 0)
{
uint8_t x_70; 
x_70 = lean_ctor_get_uint8(x_46, sizeof(void*)*5);
if (x_70 == 0)
{
uint8_t x_71; 
x_71 = lean_ctor_get_uint8(x_46, sizeof(void*)*5 + 3);
if (x_71 == 0)
{
uint8_t x_72; 
x_72 = lean_ctor_get_uint8(x_46, sizeof(void*)*5 + 1);
lean_dec(x_46);
if (x_72 == 0)
{
lean_object* x_73; 
x_73 = l_List_allM___at_Lean_Elab_Deriving_DecEq_mkDecEqInstanceHandler___spec__2(x_68, x_2, x_3, x_45);
return x_73;
}
else
{
uint8_t x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_68);
lean_dec(x_2);
x_74 = 0;
x_75 = lean_box(x_74);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_45);
return x_76;
}
}
else
{
uint8_t x_77; lean_object* x_78; lean_object* x_79; 
lean_dec(x_68);
lean_dec(x_46);
lean_dec(x_2);
x_77 = 0;
x_78 = lean_box(x_77);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_45);
return x_79;
}
}
else
{
uint8_t x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_68);
lean_dec(x_46);
lean_dec(x_2);
x_80 = 0;
x_81 = lean_box(x_80);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_45);
return x_82;
}
}
else
{
uint8_t x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_68);
lean_dec(x_46);
lean_dec(x_2);
x_83 = 0;
x_84 = lean_box(x_83);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_45);
return x_85;
}
}
}
}
}
else
{
uint8_t x_86; lean_object* x_87; lean_object* x_88; 
lean_dec(x_46);
lean_dec(x_2);
x_86 = 0;
x_87 = lean_box(x_86);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_45);
return x_88;
}
}
}
else
{
uint8_t x_89; 
lean_dec(x_6);
lean_dec(x_2);
x_89 = !lean_is_exclusive(x_5);
if (x_89 == 0)
{
lean_object* x_90; uint8_t x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_5, 0);
lean_dec(x_90);
x_91 = 0;
x_92 = lean_box(x_91);
lean_ctor_set(x_5, 0, x_92);
return x_5;
}
else
{
lean_object* x_93; uint8_t x_94; lean_object* x_95; lean_object* x_96; 
x_93 = lean_ctor_get(x_5, 1);
lean_inc(x_93);
lean_dec(x_5);
x_94 = 0;
x_95 = lean_box(x_94);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_93);
return x_96;
}
}
}
else
{
uint8_t x_97; 
lean_dec(x_2);
x_97 = !lean_is_exclusive(x_5);
if (x_97 == 0)
{
return x_5;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_5, 0);
x_99 = lean_ctor_get(x_5, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_5);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
return x_100;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_DecEq_mkDecEqInstanceHandler(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_array_get_size(x_1);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_dec_eq(x_5, x_6);
if (x_7 == 0)
{
uint8_t x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_8 = 0;
x_9 = lean_box(x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_4);
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
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__5___closed__8;
x_14 = l_panic___at___private_Init_Prelude_0__Lean_assembleParts___spec__1(x_13);
lean_inc(x_2);
lean_inc(x_14);
x_15 = l_Lean_isEnumType___at_Lean_Elab_Deriving_DecEq_mkDecEqInstanceHandler___spec__1(x_14, x_2, x_3, x_4);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_unbox(x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = l_Lean_Elab_Deriving_DecEq_mkDecEq(x_14, x_2, x_3, x_18);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_dec(x_15);
x_21 = l_Lean_Elab_Deriving_DecEq_mkDecEqEnum(x_14, x_2, x_3, x_20);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_21, 0);
lean_dec(x_23);
x_24 = 1;
x_25 = lean_box(x_24);
lean_ctor_set(x_21, 0, x_25);
return x_21;
}
else
{
lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_21, 1);
lean_inc(x_26);
lean_dec(x_21);
x_27 = 1;
x_28 = lean_box(x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_26);
return x_29;
}
}
else
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_21);
if (x_30 == 0)
{
return x_21;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_21, 0);
x_32 = lean_ctor_get(x_21, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_21);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
else
{
uint8_t x_34; 
lean_dec(x_14);
lean_dec(x_3);
lean_dec(x_2);
x_34 = !lean_is_exclusive(x_15);
if (x_34 == 0)
{
return x_15;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_15, 0);
x_36 = lean_ctor_get(x_15, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_15);
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
x_38 = lean_array_fget(x_1, x_11);
lean_inc(x_2);
lean_inc(x_38);
x_39 = l_Lean_isEnumType___at_Lean_Elab_Deriving_DecEq_mkDecEqInstanceHandler___spec__1(x_38, x_2, x_3, x_4);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_unbox(x_40);
lean_dec(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_39, 1);
lean_inc(x_42);
lean_dec(x_39);
x_43 = l_Lean_Elab_Deriving_DecEq_mkDecEq(x_38, x_2, x_3, x_42);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_39, 1);
lean_inc(x_44);
lean_dec(x_39);
x_45 = l_Lean_Elab_Deriving_DecEq_mkDecEqEnum(x_38, x_2, x_3, x_44);
if (lean_obj_tag(x_45) == 0)
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; uint8_t x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_45, 0);
lean_dec(x_47);
x_48 = 1;
x_49 = lean_box(x_48);
lean_ctor_set(x_45, 0, x_49);
return x_45;
}
else
{
lean_object* x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; 
x_50 = lean_ctor_get(x_45, 1);
lean_inc(x_50);
lean_dec(x_45);
x_51 = 1;
x_52 = lean_box(x_51);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_50);
return x_53;
}
}
else
{
uint8_t x_54; 
x_54 = !lean_is_exclusive(x_45);
if (x_54 == 0)
{
return x_45;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_45, 0);
x_56 = lean_ctor_get(x_45, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_45);
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
uint8_t x_58; 
lean_dec(x_38);
lean_dec(x_3);
lean_dec(x_2);
x_58 = !lean_is_exclusive(x_39);
if (x_58 == 0)
{
return x_39;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_39, 0);
x_60 = lean_ctor_get(x_39, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_39);
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
LEAN_EXPORT lean_object* l_List_allM___at_Lean_Elab_Deriving_DecEq_mkDecEqInstanceHandler___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_allM___at_Lean_Elab_Deriving_DecEq_mkDecEqInstanceHandler___spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_isEnumType___at_Lean_Elab_Deriving_DecEq_mkDecEqInstanceHandler___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_isEnumType___at_Lean_Elab_Deriving_DecEq_mkDecEqInstanceHandler___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_DecEq_mkDecEqInstanceHandler___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Deriving_DecEq_mkDecEqInstanceHandler(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_initFn____x40_Lean_Elab_Deriving_DecEq___hyg_5366____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Deriving_DecEq_mkDecEqInstanceHandler___boxed), 4, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_DecEq_initFn____x40_Lean_Elab_Deriving_DecEq___hyg_5366_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Elab_Deriving_DecEq_mkDecEqHeader___closed__2;
x_3 = l_Lean_Elab_Deriving_DecEq_initFn____x40_Lean_Elab_Deriving_DecEq___hyg_5366____closed__1;
x_4 = l_Lean_Elab_registerDerivingHandler(x_2, x_3, x_1);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = l_Lean_Elab_Deriving_DecEq_mkDecEqCmds___closed__6;
x_7 = l_Lean_registerTraceClass(x_6, x_5);
return x_7;
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_4);
if (x_8 == 0)
{
return x_4;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_4);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Transform(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Inductive(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Deriving_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Deriving_Util(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Deriving_DecEq(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Transform(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Inductive(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Deriving_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Deriving_Util(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Deriving_DecEq_mkDecEqHeader___closed__1 = _init_l_Lean_Elab_Deriving_DecEq_mkDecEqHeader___closed__1();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkDecEqHeader___closed__1);
l_Lean_Elab_Deriving_DecEq_mkDecEqHeader___closed__2 = _init_l_Lean_Elab_Deriving_DecEq_mkDecEqHeader___closed__2();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkDecEqHeader___closed__2);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__1 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__1);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__2 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__2);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__3 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__3);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__4 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__4);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__5 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__5();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__5);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__6 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__6();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__6);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__7 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__7();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__7);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__8 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__8();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__8);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__9 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__9();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__9);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__10 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__10();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__10);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__11 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__11();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__11);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__12 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__12();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__12);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__13 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__13();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__13);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__14 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__14();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__14);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__15 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__15();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__15);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__16 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__16();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__16);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__17 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__17();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__17);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__18 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__18();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__18);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__19 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__19();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__19);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__20 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__20();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__20);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__21 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__21();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__21);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__22 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__22();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__22);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__23 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__23();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__23);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__24 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__24();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__24);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__25 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__25();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__25);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__26 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__26();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__26);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__27 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__27();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__1___closed__27);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__1 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__1);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__2 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__2);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__3 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__3();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__3);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__4 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__4();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__4);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__5 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__5();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__5);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__6 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__6();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__6);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__7 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__7();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__7);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__8 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__8();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__8);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__9 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__9();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__9);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__10 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__10();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__10);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__11 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__11();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__11);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__12 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__12();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__12);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__13 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__13();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__13);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__14 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__14();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__14);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__15 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__15();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__15);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__16 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__16();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__16);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__17 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__17();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__17);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__18 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__18();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__18);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__19 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__19();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__19);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__20 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__20();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__20);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__21 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__21();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__21);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__22 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__22();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__22);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__23 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__23();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__23);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__24 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__24();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__24);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__25 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__25();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__25);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__26 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__26();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__26);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__27 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__27();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__27);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__28 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__28();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__28);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__29 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__29();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__29);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__30 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__30();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__30);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__31 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__31();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__31);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__32 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__32();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__32);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__33 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__33();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__33);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__34 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__34();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__34);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__35 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__35();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__35);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__36 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__36();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__36);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__37 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__37();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__37);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__38 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__38();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__38);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__39 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__39();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__39);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__40 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__40();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__40);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__41 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__41();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__41);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__42 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__42();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__42);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__43 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__43();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__43);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__44 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__44();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__44);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__45 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__45();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__45);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__46 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__46();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__46);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__47 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__47();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__47);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__48 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__48();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__48);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__49 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__49();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__49);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__50 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__50();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__50);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__51 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__51();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__51);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__52 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__52();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__52);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__53 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__53();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__53);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__54 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__54();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__54);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__55 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__55();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__55);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__56 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__56();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__56);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__57 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__57();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__57);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__58 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__58();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__2___closed__58);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__3___closed__1 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__3___closed__1);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__3___closed__2 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__3___closed__2();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__3___closed__2);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__3___closed__3 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__3___closed__3();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__3___closed__3);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__3___closed__4 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__3___closed__4();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__3___closed__4);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__3___closed__5 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__3___closed__5();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__3___closed__5);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__3___closed__6 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__3___closed__6();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__3___closed__6);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__3___closed__7 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__3___closed__7();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__3___closed__7);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__3___closed__8 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__3___closed__8();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__3___closed__8);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__3___closed__9 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__3___closed__9();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__3___closed__9);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__3___closed__10 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__3___closed__10();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__3___closed__10);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__3___closed__11 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__3___closed__11();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__3___closed__11);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__3___closed__12 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__3___closed__12();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__3___closed__12);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__3___closed__13 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__3___closed__13();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__3___closed__13);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__3___closed__14 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__3___closed__14();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___lambda__3___closed__14);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__1 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__1();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__1);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__2 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__2();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__2);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__3 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__3();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__3);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__4 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__4();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__4);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__5 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__5();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__5);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__6 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__6();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__6);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__7 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__7();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__7);
l_Lean_getConstInfoCtor___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__1___closed__1 = _init_l_Lean_getConstInfoCtor___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__1___closed__1();
lean_mark_persistent(l_Lean_getConstInfoCtor___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__1___closed__1);
l_Lean_getConstInfoCtor___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__1___closed__2 = _init_l_Lean_getConstInfoCtor___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__1___closed__2();
lean_mark_persistent(l_Lean_getConstInfoCtor___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__1___closed__2);
l_Lean_getConstInfoCtor___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__1___closed__3 = _init_l_Lean_getConstInfoCtor___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__1___closed__3();
lean_mark_persistent(l_Lean_getConstInfoCtor___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__1___closed__3);
l_Lean_getConstInfoCtor___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__1___closed__4 = _init_l_Lean_getConstInfoCtor___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__1___closed__4();
lean_mark_persistent(l_Lean_getConstInfoCtor___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__1___closed__4);
l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__5___closed__1 = _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__5___closed__1();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__5___closed__1);
l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__5___closed__2 = _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__5___closed__2();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__5___closed__2);
l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__5___closed__3 = _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__5___closed__3();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__5___closed__3);
l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__5___closed__4 = _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__5___closed__4();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__5___closed__4);
l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__5___closed__5 = _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__5___closed__5();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__5___closed__5);
l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__5___closed__6 = _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__5___closed__6();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__5___closed__6);
l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__5___closed__7 = _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__5___closed__7();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__5___closed__7);
l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__5___closed__8 = _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__5___closed__8();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__5___closed__8);
l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1___closed__1 = _init_l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1___closed__1();
lean_mark_persistent(l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1___closed__1);
l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1___closed__2 = _init_l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1___closed__2();
lean_mark_persistent(l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1___closed__2);
l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1___closed__3 = _init_l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1___closed__3();
lean_mark_persistent(l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1___closed__3);
l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1___closed__4 = _init_l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1___closed__4();
lean_mark_persistent(l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1___closed__4);
l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1___closed__5 = _init_l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1___closed__5();
lean_mark_persistent(l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1___closed__5);
l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1___closed__6 = _init_l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1___closed__6();
lean_mark_persistent(l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1___closed__6);
l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1___closed__7 = _init_l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1___closed__7();
lean_mark_persistent(l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1___closed__7);
l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1___closed__8 = _init_l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1___closed__8();
lean_mark_persistent(l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1___closed__8);
l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1___closed__9 = _init_l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1___closed__9();
lean_mark_persistent(l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1___closed__9);
l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1___closed__10 = _init_l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1___closed__10();
lean_mark_persistent(l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1___closed__10);
l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1___closed__11 = _init_l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1___closed__11();
lean_mark_persistent(l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1___closed__11);
l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___closed__1 = _init_l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___closed__1();
lean_mark_persistent(l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___closed__1);
l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___closed__2 = _init_l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___closed__2();
lean_mark_persistent(l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___closed__2);
l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___closed__3 = _init_l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___closed__3();
lean_mark_persistent(l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___closed__3);
l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___closed__4 = _init_l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___closed__4();
lean_mark_persistent(l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___closed__4);
l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___closed__5 = _init_l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___closed__5();
lean_mark_persistent(l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___closed__5);
l_Lean_Elab_Deriving_DecEq_mkMatch___closed__1 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch___closed__1();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch___closed__1);
l_Lean_Elab_Deriving_DecEq_mkMatch___closed__2 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch___closed__2();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch___closed__2);
l_Lean_Elab_Deriving_DecEq_mkMatch___closed__3 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch___closed__3();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch___closed__3);
l_Lean_Elab_Deriving_DecEq_mkMatch___closed__4 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch___closed__4();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch___closed__4);
l_Lean_Elab_Deriving_DecEq_mkMatch___closed__5 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch___closed__5();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch___closed__5);
l_Lean_Elab_Deriving_DecEq_mkMatch___closed__6 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch___closed__6();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch___closed__6);
l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__1 = _init_l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__1();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__1);
l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__2 = _init_l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__2();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__2);
l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__3 = _init_l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__3();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__3);
l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__4 = _init_l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__4();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__4);
l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__5 = _init_l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__5();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__5);
l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__6 = _init_l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__6();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__6);
l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__7 = _init_l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__7();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__7);
l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__8 = _init_l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__8();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__8);
l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__9 = _init_l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__9();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__9);
l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__10 = _init_l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__10();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__10);
l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__11 = _init_l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__11();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__11);
l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__12 = _init_l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__12();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__12);
l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__13 = _init_l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__13();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__13);
l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__14 = _init_l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__14();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__14);
l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__15 = _init_l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__15();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__15);
l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__16 = _init_l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__16();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__16);
l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__17 = _init_l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__17();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__17);
l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__18 = _init_l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__18();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__18);
l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__19 = _init_l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__19();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__19);
l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__20 = _init_l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__20();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__20);
l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__21 = _init_l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__21();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__21);
l_Lean_Elab_Deriving_DecEq_mkDecEqCmds___closed__1 = _init_l_Lean_Elab_Deriving_DecEq_mkDecEqCmds___closed__1();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkDecEqCmds___closed__1);
l_Lean_Elab_Deriving_DecEq_mkDecEqCmds___closed__2 = _init_l_Lean_Elab_Deriving_DecEq_mkDecEqCmds___closed__2();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkDecEqCmds___closed__2);
l_Lean_Elab_Deriving_DecEq_mkDecEqCmds___closed__3 = _init_l_Lean_Elab_Deriving_DecEq_mkDecEqCmds___closed__3();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkDecEqCmds___closed__3);
l_Lean_Elab_Deriving_DecEq_mkDecEqCmds___closed__4 = _init_l_Lean_Elab_Deriving_DecEq_mkDecEqCmds___closed__4();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkDecEqCmds___closed__4);
l_Lean_Elab_Deriving_DecEq_mkDecEqCmds___closed__5 = _init_l_Lean_Elab_Deriving_DecEq_mkDecEqCmds___closed__5();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkDecEqCmds___closed__5);
l_Lean_Elab_Deriving_DecEq_mkDecEqCmds___closed__6 = _init_l_Lean_Elab_Deriving_DecEq_mkDecEqCmds___closed__6();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkDecEqCmds___closed__6);
l_Lean_Elab_Deriving_DecEq_mkDecEqCmds___closed__7 = _init_l_Lean_Elab_Deriving_DecEq_mkDecEqCmds___closed__7();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkDecEqCmds___closed__7);
l_Lean_Elab_Deriving_DecEq_mkDecEqCmds___closed__8 = _init_l_Lean_Elab_Deriving_DecEq_mkDecEqCmds___closed__8();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkDecEqCmds___closed__8);
l_Lean_Elab_Deriving_DecEq_mkDecEqCmds___closed__9 = _init_l_Lean_Elab_Deriving_DecEq_mkDecEqCmds___closed__9();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkDecEqCmds___closed__9);
l_Lean_Elab_Deriving_DecEq_mkDecEqCmds___closed__10 = _init_l_Lean_Elab_Deriving_DecEq_mkDecEqCmds___closed__10();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkDecEqCmds___closed__10);
l_Lean_getConstInfoInduct___at_Lean_Elab_Deriving_DecEq_mkDecEq___spec__1___closed__1 = _init_l_Lean_getConstInfoInduct___at_Lean_Elab_Deriving_DecEq_mkDecEq___spec__1___closed__1();
lean_mark_persistent(l_Lean_getConstInfoInduct___at_Lean_Elab_Deriving_DecEq_mkDecEq___spec__1___closed__1);
l_Lean_getConstInfoInduct___at_Lean_Elab_Deriving_DecEq_mkDecEq___spec__1___closed__2 = _init_l_Lean_getConstInfoInduct___at_Lean_Elab_Deriving_DecEq_mkDecEq___spec__1___closed__2();
lean_mark_persistent(l_Lean_getConstInfoInduct___at_Lean_Elab_Deriving_DecEq_mkDecEq___spec__1___closed__2);
l_Lean_Elab_Deriving_DecEq_mkEnumOfNat_mkDecTree___closed__1 = _init_l_Lean_Elab_Deriving_DecEq_mkEnumOfNat_mkDecTree___closed__1();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkEnumOfNat_mkDecTree___closed__1);
l_Lean_Elab_Deriving_DecEq_mkEnumOfNat_mkDecTree___closed__2 = _init_l_Lean_Elab_Deriving_DecEq_mkEnumOfNat_mkDecTree___closed__2();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkEnumOfNat_mkDecTree___closed__2);
l_Lean_Elab_Deriving_DecEq_mkEnumOfNat_mkDecTree___closed__3 = _init_l_Lean_Elab_Deriving_DecEq_mkEnumOfNat_mkDecTree___closed__3();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkEnumOfNat_mkDecTree___closed__3);
l_Lean_Elab_Deriving_DecEq_mkEnumOfNat_mkDecTree___closed__4 = _init_l_Lean_Elab_Deriving_DecEq_mkEnumOfNat_mkDecTree___closed__4();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkEnumOfNat_mkDecTree___closed__4);
l_Lean_Elab_Deriving_DecEq_mkEnumOfNat_mkDecTree___closed__5 = _init_l_Lean_Elab_Deriving_DecEq_mkEnumOfNat_mkDecTree___closed__5();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkEnumOfNat_mkDecTree___closed__5);
l_Lean_Elab_Deriving_DecEq_mkEnumOfNat_mkDecTree___closed__6 = _init_l_Lean_Elab_Deriving_DecEq_mkEnumOfNat_mkDecTree___closed__6();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkEnumOfNat_mkDecTree___closed__6);
l_Lean_Elab_Deriving_DecEq_mkEnumOfNat_mkDecTree___closed__7 = _init_l_Lean_Elab_Deriving_DecEq_mkEnumOfNat_mkDecTree___closed__7();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkEnumOfNat_mkDecTree___closed__7);
l_Lean_Elab_Deriving_DecEq_mkEnumOfNat_mkDecTree___closed__8 = _init_l_Lean_Elab_Deriving_DecEq_mkEnumOfNat_mkDecTree___closed__8();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkEnumOfNat_mkDecTree___closed__8);
l_Lean_Elab_Deriving_DecEq_mkEnumOfNat___lambda__1___closed__1 = _init_l_Lean_Elab_Deriving_DecEq_mkEnumOfNat___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkEnumOfNat___lambda__1___closed__1);
l_Lean_Elab_Deriving_DecEq_mkEnumOfNat___lambda__1___closed__2 = _init_l_Lean_Elab_Deriving_DecEq_mkEnumOfNat___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkEnumOfNat___lambda__1___closed__2);
l_Lean_Elab_Deriving_DecEq_mkEnumOfNat___lambda__1___closed__3 = _init_l_Lean_Elab_Deriving_DecEq_mkEnumOfNat___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkEnumOfNat___lambda__1___closed__3);
l_Lean_Elab_Deriving_DecEq_mkEnumOfNat___closed__1 = _init_l_Lean_Elab_Deriving_DecEq_mkEnumOfNat___closed__1();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkEnumOfNat___closed__1);
l_Lean_Elab_Deriving_DecEq_mkEnumOfNatThm___lambda__1___closed__1 = _init_l_Lean_Elab_Deriving_DecEq_mkEnumOfNatThm___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkEnumOfNatThm___lambda__1___closed__1);
l_Lean_Elab_Deriving_DecEq_mkEnumOfNatThm___closed__1 = _init_l_Lean_Elab_Deriving_DecEq_mkEnumOfNatThm___closed__1();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkEnumOfNatThm___closed__1);
l_Lean_Elab_Deriving_DecEq_mkEnumOfNatThm___closed__2 = _init_l_Lean_Elab_Deriving_DecEq_mkEnumOfNatThm___closed__2();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkEnumOfNatThm___closed__2);
l_Lean_Elab_Deriving_DecEq_mkEnumOfNatThm___closed__3 = _init_l_Lean_Elab_Deriving_DecEq_mkEnumOfNatThm___closed__3();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkEnumOfNatThm___closed__3);
l_Lean_Elab_Deriving_DecEq_mkEnumOfNatThm___closed__4 = _init_l_Lean_Elab_Deriving_DecEq_mkEnumOfNatThm___closed__4();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkEnumOfNatThm___closed__4);
l_Lean_Elab_Deriving_DecEq_mkEnumOfNatThm___closed__5 = _init_l_Lean_Elab_Deriving_DecEq_mkEnumOfNatThm___closed__5();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkEnumOfNatThm___closed__5);
l_Lean_Elab_Deriving_DecEq_mkEnumOfNatThm___closed__6 = _init_l_Lean_Elab_Deriving_DecEq_mkEnumOfNatThm___closed__6();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkEnumOfNatThm___closed__6);
l_Lean_Elab_Deriving_DecEq_mkEnumOfNatThm___closed__7 = _init_l_Lean_Elab_Deriving_DecEq_mkEnumOfNatThm___closed__7();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkEnumOfNatThm___closed__7);
l_Lean_Elab_Deriving_DecEq_mkEnumOfNatThm___closed__8 = _init_l_Lean_Elab_Deriving_DecEq_mkEnumOfNatThm___closed__8();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkEnumOfNatThm___closed__8);
l_Lean_Elab_Deriving_DecEq_mkEnumOfNatThm___closed__9 = _init_l_Lean_Elab_Deriving_DecEq_mkEnumOfNatThm___closed__9();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkEnumOfNatThm___closed__9);
l_Lean_Elab_Deriving_DecEq_mkEnumOfNatThm___closed__10 = _init_l_Lean_Elab_Deriving_DecEq_mkEnumOfNatThm___closed__10();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkEnumOfNatThm___closed__10);
l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__1 = _init_l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__1();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__1);
l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__2 = _init_l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__2();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__2);
l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__3 = _init_l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__3();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__3);
l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__4 = _init_l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__4();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__4);
l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__5 = _init_l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__5();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__5);
l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__6 = _init_l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__6();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__6);
l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__7 = _init_l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__7();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__7);
l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__8 = _init_l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__8();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__8);
l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__9 = _init_l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__9();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__9);
l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__10 = _init_l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__10();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__10);
l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__11 = _init_l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__11();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__11);
l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__12 = _init_l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__12();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__12);
l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__13 = _init_l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__13();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__13);
l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__14 = _init_l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__14();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__14);
l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__15 = _init_l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__15();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__15);
l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__16 = _init_l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__16();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__16);
l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__17 = _init_l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__17();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__17);
l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__18 = _init_l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__18();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__18);
l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__19 = _init_l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__19();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__19);
l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__20 = _init_l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__20();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__20);
l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__21 = _init_l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__21();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__21);
l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__22 = _init_l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__22();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__22);
l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__23 = _init_l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__23();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__23);
l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__24 = _init_l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__24();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__24);
l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__25 = _init_l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__25();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__25);
l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__26 = _init_l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__26();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__26);
l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__27 = _init_l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__27();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__27);
l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__28 = _init_l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__28();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__28);
l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__29 = _init_l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__29();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__29);
l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__30 = _init_l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__30();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__30);
l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__31 = _init_l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__31();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__31);
l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__32 = _init_l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__32();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__32);
l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__33 = _init_l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__33();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__33);
l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__34 = _init_l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__34();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__34);
l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__35 = _init_l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__35();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__35);
l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__36 = _init_l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__36();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__36);
l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__37 = _init_l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__37();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__37);
l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__38 = _init_l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__38();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__38);
l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__39 = _init_l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__39();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__39);
l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__40 = _init_l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__40();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__40);
l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__41 = _init_l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__41();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__41);
l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__42 = _init_l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__42();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__42);
l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__43 = _init_l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__43();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__43);
l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__44 = _init_l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__44();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__44);
l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__45 = _init_l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__45();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__45);
l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__46 = _init_l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__46();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__46);
l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__47 = _init_l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__47();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__47);
l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__48 = _init_l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__48();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__48);
l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__49 = _init_l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__49();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__49);
l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__50 = _init_l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__50();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__50);
l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__51 = _init_l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__51();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__51);
l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__52 = _init_l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__52();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__52);
l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__53 = _init_l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__53();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__53);
l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__54 = _init_l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__54();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__54);
l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__55 = _init_l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__55();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__55);
l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__56 = _init_l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__56();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__56);
l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__57 = _init_l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__57();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__57);
l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__58 = _init_l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__58();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__58);
l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__59 = _init_l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__59();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__59);
l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__60 = _init_l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__60();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__60);
l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__61 = _init_l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__61();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__61);
l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__62 = _init_l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__62();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkDecEqEnum___closed__62);
l_Lean_Elab_Deriving_DecEq_initFn____x40_Lean_Elab_Deriving_DecEq___hyg_5366____closed__1 = _init_l_Lean_Elab_Deriving_DecEq_initFn____x40_Lean_Elab_Deriving_DecEq___hyg_5366____closed__1();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_initFn____x40_Lean_Elab_Deriving_DecEq___hyg_5366____closed__1);
res = l_Lean_Elab_Deriving_DecEq_initFn____x40_Lean_Elab_Deriving_DecEq___hyg_5366_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
