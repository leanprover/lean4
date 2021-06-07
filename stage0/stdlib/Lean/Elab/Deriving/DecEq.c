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
lean_object* l_Lean_getConstInfo___at_Lean_Elab_Term_mkConst___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__2;
uint8_t l_Lean_Expr_hasAnyFVar_visit___at_Lean_Expr_containsFVar___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkDecEqCmds___closed__5;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__88;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__41;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__96;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__13;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__72;
lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch___rarg___closed__3;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__23;
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkDecEqHeader___rarg___closed__2;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1___closed__3;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkDecEqCmds___closed__2;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__38;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__21;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__1;
lean_object* l_Lean_Elab_Command_liftTermElabM___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__97;
lean_object* lean_name_mk_string(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__64;
static lean_object* l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___closed__2;
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__2;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__60;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__89;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__47;
static lean_object* l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1___closed__6;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkDecEqCmds___closed__3;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__44;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__9;
lean_object* l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__74;
lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkDecEqHeader___rarg___closed__1;
lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch___boxed(lean_object*);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__4;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch___rarg___closed__6;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__25;
lean_object* l_Lean_Meta_compatibleCtors(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__23;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__6;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__80;
static lean_object* l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___closed__1;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__29;
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__46;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__86;
static lean_object* l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___closed__4;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch___rarg___closed__5;
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_betaReduce___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__19;
lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts_match__1(lean_object*);
lean_object* l_Lean_Elab_Deriving_DecEq_mkDecEqHeader___boxed(lean_object*);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__50;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__99;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__48;
lean_object* lean_string_utf8_byte_size(lean_object*);
static lean_object* l_Lean_getConstInfoInduct___at_Lean_Elab_Deriving_DecEq_mkDecEqInstanceHandler___spec__1___closed__1;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__34;
lean_object* l_Lean_getConstInfoInduct___at_Lean_Elab_Deriving_DecEq_mkDecEqInstanceHandler___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getMainModule___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__21;
lean_object* l_Lean_Elab_Deriving_DecEq_mkDecEqInstanceHandler___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__6;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__19;
lean_object* l_Lean_getConstInfoCtor___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___at_Lean_Elab_Deriving_DecEq_mkDecEqCmds___spec__1(lean_object*);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__51;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__82;
lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__11;
lean_object* l_Lean_Elab_Deriving_mkDiscrs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_getConstInfoCtor___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__1___closed__2;
static lean_object* l_Lean_getConstInfoCtor___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__1___closed__1;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__69;
static lean_object* l_Lean_getConstInfoInduct___at_Lean_Elab_Deriving_DecEq_mkDecEqInstanceHandler___spec__1___closed__2;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__31;
lean_object* l_Lean_Elab_Deriving_DecEq_mkDecEqHeader___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getConstInfoInduct___at_Lean_Elab_Deriving_DecEq_mkDecEqInstanceHandler___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1___closed__7;
static lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__5___closed__1;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__59;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
static lean_object* l_Lean_getConstInfoCtor___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__1___closed__3;
lean_object* l_Lean_Elab_Deriving_mkInstanceCmds(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
static lean_object* l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1___closed__10;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__61;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkDecEqCmds___closed__7;
lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch(lean_object*);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__4;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__3;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__1;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__57;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__17;
static lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__5___closed__2;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__14;
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__8;
lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__94;
lean_object* l_Lean_Elab_Deriving_DecEq_mkDecEqCmds(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__40;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__67;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__45;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__9;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__36;
lean_object* l_Lean_Elab_Deriving_DecEq_mkAuxFunction___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__27;
static lean_object* l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1___closed__5;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__8;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__13;
lean_object* l_Lean_Elab_addMacroStack___at_Lean_Elab_Term_instAddErrorMessageContextTermElabM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getConstInfo___at_Lean_Elab_elabDeriving___spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__70;
static lean_object* l_Lean_getConstInfoCtor___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__1___closed__4;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__5;
static lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__5___closed__4;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__65;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__39;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__83;
lean_object* l_Lean_addMessageContextPartial___at_Lean_Elab_Command_instAddMessageContextCommandElabM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getCurrMacroScope(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__18;
lean_object* l_Lean_throwError___at_Lean_Elab_Deriving_DecEq_mkDecEqInstanceHandler___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__15;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__35;
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs_match__1___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__7;
lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts_match__1___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__79;
lean_object* l_Lean_mkSepArray(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__24;
lean_object* l_Lean_Core_transform___at_Lean_Core_betaReduce___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__95;
lean_object* l_Lean_Elab_Deriving_mkHeader___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__10;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkDecEqCmds___closed__10;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__43;
lean_object* l_Lean_Elab_Deriving_mkContext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__81;
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__98;
lean_object* l_Lean_addTrace___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__20;
lean_object* l_Lean_getConstInfoCtor___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__10;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__32;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__73;
lean_object* l_Lean_throwError___at_Lean_Elab_Deriving_DecEq_mkDecEqInstanceHandler___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__66;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch___rarg___closed__4;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__85;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__56;
lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts_match__2(lean_object*);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__16;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__77;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__26;
lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_myMacro____x40_Init_NotationExtra___hyg_4440____spec__3(size_t, size_t, lean_object*);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__58;
lean_object* l_Lean_Elab_Deriving_DecEq_mkDecEqHeader(lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__75;
lean_object* l_Lean_Elab_addMacroStack___at_Lean_Elab_Command_instAddErrorMessageContextCommandElabM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs_match__1(lean_object*);
lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__90;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__12;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__22;
lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__87;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__68;
lean_object* l_Lean_Elab_Deriving_DecEq_initFn____x40_Lean_Elab_Deriving_DecEq___hyg_2438_(lean_object*);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__92;
lean_object* l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__3;
lean_object* l_Lean_Elab_Command_getRef(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__15;
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__55;
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedName;
lean_object* l_Lean_Meta_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_registerBuiltinDerivingHandler(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__5;
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabCommand___spec__13(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__28;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__30;
static lean_object* l_Lean_Elab_Deriving_DecEq_initFn____x40_Lean_Elab_Deriving_DecEq___hyg_2438____closed__1;
lean_object* l_Lean_Elab_Deriving_DecEq_mkAuxFunction(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1___closed__1;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__14;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__93;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__17;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__33;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__18;
static lean_object* l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1___closed__9;
static lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__5___closed__3;
lean_object* l_Lean_Meta_forallTelescopeReducing___at_Lean_Elab_Deriving_mkInductArgNames___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__76;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__78;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__91;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__22;
lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts_match__2___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__52;
lean_object* lean_mk_syntax_ident(lean_object*);
static lean_object* l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1___closed__2;
extern lean_object* l_Lean_instInhabitedInductiveVal;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__62;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__84;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__54;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__12;
static lean_object* l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___closed__3;
lean_object* l_Lean_Elab_Deriving_DecEq_mkDecEqInstanceHandler(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_betaReduce___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkDecEqCmds___closed__9;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__16;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__11;
static lean_object* l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1___closed__8;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__71;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__7;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__63;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch___rarg___closed__2;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__49;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__24;
static lean_object* l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1___closed__4;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkDecEqCmds___closed__6;
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__20;
lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkDecEqCmds___closed__1;
static lean_object* l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1___closed__11;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch___rarg___closed__1;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkDecEqCmds___closed__4;
lean_object* l_Lean_throwError___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Deriving_mkInductiveApp___spec__2___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__42;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__53;
static lean_object* l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___closed__5;
static lean_object* l_Lean_Elab_Deriving_DecEq_mkDecEqCmds___closed__8;
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__37;
lean_object* l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkDecEqHeader___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("DecidableEq");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkDecEqHeader___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Deriving_DecEq_mkDecEqHeader___rarg___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Deriving_DecEq_mkDecEqHeader___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = l_Lean_Elab_Deriving_DecEq_mkDecEqHeader___rarg___closed__2;
x_10 = lean_unsigned_to_nat(2u);
x_11 = l_Lean_Elab_Deriving_mkHeader___rarg(x_9, x_10, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
lean_object* l_Lean_Elab_Deriving_DecEq_mkDecEqHeader(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Deriving_DecEq_mkDecEqHeader___rarg), 8, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Deriving_DecEq_mkDecEqHeader___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Deriving_DecEq_mkDecEqHeader(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
lean_dec(x_6);
x_10 = lean_ctor_get(x_7, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_7, 1);
lean_inc(x_11);
lean_dec(x_7);
x_12 = lean_apply_4(x_3, x_9, x_10, x_11, x_8);
return x_12;
}
}
}
lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec(x_3);
x_7 = lean_apply_3(x_2, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts_match__2___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts_match__2___rarg), 2, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Parser");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__2;
x_2 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Term");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__4;
x_2 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("app");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__6;
x_2 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__7;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("isTrue");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__9;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__9;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__10;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__9;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Decidable");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__13;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__14;
x_2 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__9;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__15;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__16;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__18() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("null");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__18;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__20() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("rfl");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__20;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__20;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__21;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__20;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__23;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__24;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__28() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("termDepIfThenElse");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__29() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__28;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__30() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("if");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__31() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("h");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__32() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__31;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__33() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__31;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__32;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__34() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__31;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__35() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(":");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__36() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("term_=_");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__37() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__36;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__38() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("=");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__39() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__40() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("then");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__41() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("byTactic");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__42() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__6;
x_2 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__41;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__43() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("by");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__44() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Tactic");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__45() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__4;
x_2 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__44;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__46() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("tacticSeq");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__47() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__45;
x_2 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__46;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__48() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("tacticSeq1Indented");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__49() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__45;
x_2 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__48;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__50() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("group");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__51() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__50;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__52() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("subst");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__53() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__45;
x_2 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__52;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__54() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(";");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__55() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("exact");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__56() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__45;
x_2 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__55;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__57() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__58() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__19;
x_2 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__57;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__59() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("else");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__60() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("isFalse");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__61() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__60;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__62() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__60;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__61;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__63() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__60;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__64() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__14;
x_2 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__60;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__65() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__64;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__66() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__65;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__67() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("paren");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__68() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__6;
x_2 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__67;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__69() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("(");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__70() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("intro");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__71() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__45;
x_2 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__70;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__72() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("n");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__73() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__72;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__74() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__72;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__73;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__75() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__72;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__76() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("injection");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__77() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__45;
x_2 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__76;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__78() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("apply");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__79() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__45;
x_2 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__78;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__80() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("hole");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__81() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__6;
x_2 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__80;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__82() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__83() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("assumption");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__84() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__45;
x_2 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__83;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__85() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__86() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(")");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__87() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__88() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("let");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__89() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__6;
x_2 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__88;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__90() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("letDecl");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__91() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__6;
x_2 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__90;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__92() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("letIdDecl");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__93() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__6;
x_2 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__92;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__94() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("inst");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__95() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__94;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__96() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__94;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__95;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__97() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__94;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__98() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(":=");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__99() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(5u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
lean_dec(x_1);
x_10 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Deriving_mkInductiveApp___spec__2___rarg(x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4, x_5, x_6, x_7, x_8, x_12);
lean_dec(x_3);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Elab_Term_getMainModule___rarg(x_8, x_15);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__12;
lean_inc(x_14);
lean_inc(x_18);
x_20 = l_Lean_addMacroScope(x_18, x_19, x_14);
x_21 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__11;
x_22 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__17;
lean_inc(x_11);
x_23 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_23, 0, x_11);
lean_ctor_set(x_23, 1, x_21);
lean_ctor_set(x_23, 2, x_20);
lean_ctor_set(x_23, 3, x_22);
x_24 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__23;
x_25 = l_Lean_addMacroScope(x_18, x_24, x_14);
x_26 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__22;
x_27 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__25;
x_28 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_28, 0, x_11);
lean_ctor_set(x_28, 1, x_26);
lean_ctor_set(x_28, 2, x_25);
lean_ctor_set(x_28, 3, x_27);
x_29 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__26;
x_30 = lean_array_push(x_29, x_28);
x_31 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__19;
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
x_33 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__27;
x_34 = lean_array_push(x_33, x_23);
x_35 = lean_array_push(x_34, x_32);
x_36 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__8;
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
lean_ctor_set(x_16, 0, x_37);
return x_16;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_38 = lean_ctor_get(x_16, 0);
x_39 = lean_ctor_get(x_16, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_16);
x_40 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__12;
lean_inc(x_14);
lean_inc(x_38);
x_41 = l_Lean_addMacroScope(x_38, x_40, x_14);
x_42 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__11;
x_43 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__17;
lean_inc(x_11);
x_44 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_44, 0, x_11);
lean_ctor_set(x_44, 1, x_42);
lean_ctor_set(x_44, 2, x_41);
lean_ctor_set(x_44, 3, x_43);
x_45 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__23;
x_46 = l_Lean_addMacroScope(x_38, x_45, x_14);
x_47 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__22;
x_48 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__25;
x_49 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_49, 0, x_11);
lean_ctor_set(x_49, 1, x_47);
lean_ctor_set(x_49, 2, x_46);
lean_ctor_set(x_49, 3, x_48);
x_50 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__26;
x_51 = lean_array_push(x_50, x_49);
x_52 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__19;
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_51);
x_54 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__27;
x_55 = lean_array_push(x_54, x_44);
x_56 = lean_array_push(x_55, x_53);
x_57 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__8;
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_56);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_39);
return x_59;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_60 = lean_ctor_get(x_2, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_60, 1);
lean_inc(x_61);
x_62 = lean_ctor_get(x_2, 1);
lean_inc(x_62);
lean_dec(x_2);
x_63 = lean_ctor_get(x_60, 0);
lean_inc(x_63);
lean_dec(x_60);
x_64 = lean_ctor_get(x_61, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_61, 1);
lean_inc(x_65);
lean_dec(x_61);
x_66 = lean_st_ref_take(x_8, x_9);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = !lean_is_exclusive(x_67);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_70 = lean_ctor_get(x_67, 1);
x_71 = lean_unsigned_to_nat(1u);
x_72 = lean_nat_add(x_70, x_71);
lean_ctor_set(x_67, 1, x_72);
x_73 = lean_st_ref_set(x_8, x_67, x_68);
x_74 = lean_ctor_get(x_73, 1);
lean_inc(x_74);
lean_dec(x_73);
x_75 = !lean_is_exclusive(x_3);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_76 = lean_ctor_get(x_3, 4);
lean_dec(x_76);
lean_ctor_set(x_3, 4, x_70);
lean_inc(x_3);
lean_inc(x_1);
x_77 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs(x_1, x_62, x_3, x_4, x_5, x_6, x_7, x_8, x_74);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
x_80 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Deriving_mkInductiveApp___spec__2___rarg(x_7, x_8, x_79);
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec(x_80);
x_83 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4, x_5, x_6, x_7, x_8, x_82);
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec(x_83);
x_86 = l_Lean_Elab_Term_getMainModule___rarg(x_8, x_85);
x_87 = !lean_is_exclusive(x_86);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; uint8_t x_253; 
x_88 = lean_ctor_get(x_86, 0);
x_89 = lean_ctor_get(x_86, 1);
x_90 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__30;
lean_inc(x_81);
x_91 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_91, 0, x_81);
lean_ctor_set(x_91, 1, x_90);
x_92 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__34;
lean_inc(x_84);
lean_inc(x_88);
x_93 = l_Lean_addMacroScope(x_88, x_92, x_84);
x_94 = lean_box(0);
x_95 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__33;
lean_inc(x_81);
x_96 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_96, 0, x_81);
lean_ctor_set(x_96, 1, x_95);
lean_ctor_set(x_96, 2, x_93);
lean_ctor_set(x_96, 3, x_94);
x_97 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__35;
lean_inc(x_81);
x_98 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_98, 0, x_81);
lean_ctor_set(x_98, 1, x_97);
x_99 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__38;
lean_inc(x_81);
x_100 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_100, 0, x_81);
lean_ctor_set(x_100, 1, x_99);
x_101 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__39;
lean_inc(x_63);
x_102 = lean_array_push(x_101, x_63);
x_103 = lean_array_push(x_102, x_100);
lean_inc(x_64);
x_104 = lean_array_push(x_103, x_64);
x_105 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__37;
x_106 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_104);
x_107 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__40;
lean_inc(x_81);
x_108 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_108, 0, x_81);
lean_ctor_set(x_108, 1, x_107);
x_109 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__43;
lean_inc(x_81);
x_110 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_110, 0, x_81);
lean_ctor_set(x_110, 1, x_109);
x_111 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__52;
lean_inc(x_81);
x_112 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_112, 0, x_81);
lean_ctor_set(x_112, 1, x_111);
x_113 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__26;
lean_inc(x_96);
x_114 = lean_array_push(x_113, x_96);
x_115 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__19;
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_114);
x_117 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__27;
x_118 = lean_array_push(x_117, x_112);
x_119 = lean_array_push(x_118, x_116);
x_120 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__53;
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_119);
x_122 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__54;
lean_inc(x_81);
x_123 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_123, 0, x_81);
lean_ctor_set(x_123, 1, x_122);
x_124 = lean_array_push(x_113, x_123);
x_125 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_125, 0, x_115);
lean_ctor_set(x_125, 1, x_124);
x_126 = lean_array_push(x_117, x_121);
lean_inc(x_125);
x_127 = lean_array_push(x_126, x_125);
x_128 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__51;
x_129 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_127);
x_130 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__55;
lean_inc(x_81);
x_131 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_131, 0, x_81);
lean_ctor_set(x_131, 1, x_130);
x_132 = lean_array_push(x_117, x_131);
x_133 = lean_array_push(x_132, x_78);
x_134 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__56;
x_135 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_133);
x_136 = lean_array_push(x_117, x_135);
x_137 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__58;
x_138 = lean_array_push(x_136, x_137);
x_139 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_139, 0, x_128);
lean_ctor_set(x_139, 1, x_138);
x_140 = lean_array_push(x_117, x_129);
x_141 = lean_array_push(x_140, x_139);
x_142 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_142, 0, x_115);
lean_ctor_set(x_142, 1, x_141);
x_143 = lean_array_push(x_113, x_142);
x_144 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__49;
x_145 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_145, 0, x_144);
lean_ctor_set(x_145, 1, x_143);
x_146 = lean_array_push(x_113, x_145);
x_147 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__47;
x_148 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_148, 0, x_147);
lean_ctor_set(x_148, 1, x_146);
x_149 = lean_array_push(x_117, x_110);
lean_inc(x_149);
x_150 = lean_array_push(x_149, x_148);
x_151 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__42;
x_152 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_152, 0, x_151);
lean_ctor_set(x_152, 1, x_150);
x_153 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__59;
lean_inc(x_81);
x_154 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_154, 0, x_81);
lean_ctor_set(x_154, 1, x_153);
x_155 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__63;
lean_inc(x_84);
lean_inc(x_88);
x_156 = l_Lean_addMacroScope(x_88, x_155, x_84);
x_157 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__62;
x_158 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__66;
lean_inc(x_81);
x_159 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_159, 0, x_81);
lean_ctor_set(x_159, 1, x_157);
lean_ctor_set(x_159, 2, x_156);
lean_ctor_set(x_159, 3, x_158);
x_160 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__69;
lean_inc(x_81);
x_161 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_161, 0, x_81);
lean_ctor_set(x_161, 1, x_160);
x_162 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__70;
lean_inc(x_81);
x_163 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_163, 0, x_81);
lean_ctor_set(x_163, 1, x_162);
x_164 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__75;
x_165 = l_Lean_addMacroScope(x_88, x_164, x_84);
x_166 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__74;
lean_inc(x_81);
x_167 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_167, 0, x_81);
lean_ctor_set(x_167, 1, x_166);
lean_ctor_set(x_167, 2, x_165);
lean_ctor_set(x_167, 3, x_94);
lean_inc(x_167);
x_168 = lean_array_push(x_113, x_167);
x_169 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_169, 0, x_115);
lean_ctor_set(x_169, 1, x_168);
x_170 = lean_array_push(x_117, x_163);
x_171 = lean_array_push(x_170, x_169);
x_172 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__71;
x_173 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_173, 0, x_172);
lean_ctor_set(x_173, 1, x_171);
x_174 = lean_array_push(x_117, x_173);
lean_inc(x_125);
x_175 = lean_array_push(x_174, x_125);
x_176 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_176, 0, x_128);
lean_ctor_set(x_176, 1, x_175);
x_177 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__76;
lean_inc(x_81);
x_178 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_178, 0, x_81);
lean_ctor_set(x_178, 1, x_177);
x_179 = lean_array_push(x_101, x_178);
x_180 = lean_array_push(x_179, x_167);
x_181 = lean_array_push(x_180, x_137);
x_182 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__77;
x_183 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_183, 0, x_182);
lean_ctor_set(x_183, 1, x_181);
x_184 = lean_array_push(x_117, x_183);
lean_inc(x_125);
x_185 = lean_array_push(x_184, x_125);
x_186 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_186, 0, x_128);
lean_ctor_set(x_186, 1, x_185);
x_187 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__78;
lean_inc(x_81);
x_188 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_188, 0, x_81);
lean_ctor_set(x_188, 1, x_187);
x_189 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__82;
lean_inc(x_81);
x_190 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_190, 0, x_81);
lean_ctor_set(x_190, 1, x_189);
x_191 = lean_array_push(x_113, x_190);
x_192 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__81;
x_193 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_193, 0, x_192);
lean_ctor_set(x_193, 1, x_191);
x_194 = lean_array_push(x_113, x_193);
x_195 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_195, 0, x_115);
lean_ctor_set(x_195, 1, x_194);
lean_inc(x_96);
x_196 = lean_array_push(x_117, x_96);
x_197 = lean_array_push(x_196, x_195);
x_198 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__8;
x_199 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_199, 0, x_198);
lean_ctor_set(x_199, 1, x_197);
x_200 = lean_array_push(x_117, x_188);
x_201 = lean_array_push(x_200, x_199);
x_202 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__79;
x_203 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_203, 0, x_202);
lean_ctor_set(x_203, 1, x_201);
x_204 = lean_array_push(x_117, x_203);
x_205 = lean_array_push(x_204, x_125);
x_206 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_206, 0, x_128);
lean_ctor_set(x_206, 1, x_205);
x_207 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__83;
lean_inc(x_81);
x_208 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_208, 0, x_81);
lean_ctor_set(x_208, 1, x_207);
x_209 = lean_array_push(x_113, x_208);
x_210 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__84;
x_211 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_211, 0, x_210);
lean_ctor_set(x_211, 1, x_209);
x_212 = lean_array_push(x_117, x_211);
x_213 = lean_array_push(x_212, x_137);
x_214 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_214, 0, x_128);
lean_ctor_set(x_214, 1, x_213);
x_215 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__85;
x_216 = lean_array_push(x_215, x_176);
x_217 = lean_array_push(x_216, x_186);
x_218 = lean_array_push(x_217, x_206);
x_219 = lean_array_push(x_218, x_214);
x_220 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_220, 0, x_115);
lean_ctor_set(x_220, 1, x_219);
x_221 = lean_array_push(x_113, x_220);
x_222 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_222, 0, x_144);
lean_ctor_set(x_222, 1, x_221);
x_223 = lean_array_push(x_113, x_222);
x_224 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_224, 0, x_147);
lean_ctor_set(x_224, 1, x_223);
x_225 = lean_array_push(x_149, x_224);
x_226 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_226, 0, x_151);
lean_ctor_set(x_226, 1, x_225);
x_227 = lean_array_push(x_117, x_226);
x_228 = lean_array_push(x_227, x_137);
x_229 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_229, 0, x_115);
lean_ctor_set(x_229, 1, x_228);
x_230 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__86;
x_231 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_231, 0, x_81);
lean_ctor_set(x_231, 1, x_230);
x_232 = lean_array_push(x_101, x_161);
x_233 = lean_array_push(x_232, x_229);
x_234 = lean_array_push(x_233, x_231);
x_235 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__68;
x_236 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_236, 0, x_235);
lean_ctor_set(x_236, 1, x_234);
x_237 = lean_array_push(x_113, x_236);
x_238 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_238, 0, x_115);
lean_ctor_set(x_238, 1, x_237);
x_239 = lean_array_push(x_117, x_159);
x_240 = lean_array_push(x_239, x_238);
x_241 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_241, 0, x_198);
lean_ctor_set(x_241, 1, x_240);
x_242 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__87;
x_243 = lean_array_push(x_242, x_91);
x_244 = lean_array_push(x_243, x_96);
x_245 = lean_array_push(x_244, x_98);
x_246 = lean_array_push(x_245, x_106);
x_247 = lean_array_push(x_246, x_108);
x_248 = lean_array_push(x_247, x_152);
x_249 = lean_array_push(x_248, x_154);
x_250 = lean_array_push(x_249, x_241);
x_251 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__29;
x_252 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_252, 0, x_251);
lean_ctor_set(x_252, 1, x_250);
x_253 = lean_unbox(x_65);
lean_dec(x_65);
if (x_253 == 0)
{
lean_dec(x_3);
lean_dec(x_64);
lean_dec(x_63);
lean_dec(x_1);
lean_ctor_set(x_86, 0, x_252);
return x_86;
}
else
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; uint8_t x_261; 
lean_free_object(x_86);
x_254 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Deriving_mkInductiveApp___spec__2___rarg(x_7, x_8, x_89);
x_255 = lean_ctor_get(x_254, 0);
lean_inc(x_255);
x_256 = lean_ctor_get(x_254, 1);
lean_inc(x_256);
lean_dec(x_254);
x_257 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4, x_5, x_6, x_7, x_8, x_256);
lean_dec(x_3);
x_258 = lean_ctor_get(x_257, 0);
lean_inc(x_258);
x_259 = lean_ctor_get(x_257, 1);
lean_inc(x_259);
lean_dec(x_257);
x_260 = l_Lean_Elab_Term_getMainModule___rarg(x_8, x_259);
x_261 = !lean_is_exclusive(x_260);
if (x_261 == 0)
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; 
x_262 = lean_ctor_get(x_260, 0);
x_263 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__88;
lean_inc(x_255);
x_264 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_264, 0, x_255);
lean_ctor_set(x_264, 1, x_263);
x_265 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__97;
x_266 = l_Lean_addMacroScope(x_262, x_265, x_258);
x_267 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__96;
lean_inc(x_255);
x_268 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_268, 0, x_255);
lean_ctor_set(x_268, 1, x_267);
lean_ctor_set(x_268, 2, x_266);
lean_ctor_set(x_268, 3, x_94);
x_269 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__98;
lean_inc(x_255);
x_270 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_270, 0, x_255);
lean_ctor_set(x_270, 1, x_269);
x_271 = lean_mk_syntax_ident(x_1);
x_272 = lean_array_push(x_117, x_63);
x_273 = lean_array_push(x_272, x_64);
x_274 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_274, 0, x_115);
lean_ctor_set(x_274, 1, x_273);
x_275 = lean_array_push(x_117, x_271);
x_276 = lean_array_push(x_275, x_274);
x_277 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_277, 0, x_198);
lean_ctor_set(x_277, 1, x_276);
x_278 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__99;
x_279 = lean_array_push(x_278, x_268);
x_280 = lean_array_push(x_279, x_137);
x_281 = lean_array_push(x_280, x_137);
x_282 = lean_array_push(x_281, x_270);
x_283 = lean_array_push(x_282, x_277);
x_284 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__93;
x_285 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_285, 0, x_284);
lean_ctor_set(x_285, 1, x_283);
x_286 = lean_array_push(x_113, x_285);
x_287 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__91;
x_288 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_288, 0, x_287);
lean_ctor_set(x_288, 1, x_286);
x_289 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_289, 0, x_255);
lean_ctor_set(x_289, 1, x_122);
x_290 = lean_array_push(x_113, x_289);
x_291 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_291, 0, x_115);
lean_ctor_set(x_291, 1, x_290);
x_292 = lean_array_push(x_215, x_264);
x_293 = lean_array_push(x_292, x_288);
x_294 = lean_array_push(x_293, x_291);
x_295 = lean_array_push(x_294, x_252);
x_296 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__89;
x_297 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_297, 0, x_296);
lean_ctor_set(x_297, 1, x_295);
lean_ctor_set(x_260, 0, x_297);
return x_260;
}
else
{
lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; 
x_298 = lean_ctor_get(x_260, 0);
x_299 = lean_ctor_get(x_260, 1);
lean_inc(x_299);
lean_inc(x_298);
lean_dec(x_260);
x_300 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__88;
lean_inc(x_255);
x_301 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_301, 0, x_255);
lean_ctor_set(x_301, 1, x_300);
x_302 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__97;
x_303 = l_Lean_addMacroScope(x_298, x_302, x_258);
x_304 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__96;
lean_inc(x_255);
x_305 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_305, 0, x_255);
lean_ctor_set(x_305, 1, x_304);
lean_ctor_set(x_305, 2, x_303);
lean_ctor_set(x_305, 3, x_94);
x_306 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__98;
lean_inc(x_255);
x_307 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_307, 0, x_255);
lean_ctor_set(x_307, 1, x_306);
x_308 = lean_mk_syntax_ident(x_1);
x_309 = lean_array_push(x_117, x_63);
x_310 = lean_array_push(x_309, x_64);
x_311 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_311, 0, x_115);
lean_ctor_set(x_311, 1, x_310);
x_312 = lean_array_push(x_117, x_308);
x_313 = lean_array_push(x_312, x_311);
x_314 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_314, 0, x_198);
lean_ctor_set(x_314, 1, x_313);
x_315 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__99;
x_316 = lean_array_push(x_315, x_305);
x_317 = lean_array_push(x_316, x_137);
x_318 = lean_array_push(x_317, x_137);
x_319 = lean_array_push(x_318, x_307);
x_320 = lean_array_push(x_319, x_314);
x_321 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__93;
x_322 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_322, 0, x_321);
lean_ctor_set(x_322, 1, x_320);
x_323 = lean_array_push(x_113, x_322);
x_324 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__91;
x_325 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_325, 0, x_324);
lean_ctor_set(x_325, 1, x_323);
x_326 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_326, 0, x_255);
lean_ctor_set(x_326, 1, x_122);
x_327 = lean_array_push(x_113, x_326);
x_328 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_328, 0, x_115);
lean_ctor_set(x_328, 1, x_327);
x_329 = lean_array_push(x_215, x_301);
x_330 = lean_array_push(x_329, x_325);
x_331 = lean_array_push(x_330, x_328);
x_332 = lean_array_push(x_331, x_252);
x_333 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__89;
x_334 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_334, 0, x_333);
lean_ctor_set(x_334, 1, x_332);
x_335 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_335, 0, x_334);
lean_ctor_set(x_335, 1, x_299);
return x_335;
}
}
}
else
{
lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; uint8_t x_501; 
x_336 = lean_ctor_get(x_86, 0);
x_337 = lean_ctor_get(x_86, 1);
lean_inc(x_337);
lean_inc(x_336);
lean_dec(x_86);
x_338 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__30;
lean_inc(x_81);
x_339 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_339, 0, x_81);
lean_ctor_set(x_339, 1, x_338);
x_340 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__34;
lean_inc(x_84);
lean_inc(x_336);
x_341 = l_Lean_addMacroScope(x_336, x_340, x_84);
x_342 = lean_box(0);
x_343 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__33;
lean_inc(x_81);
x_344 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_344, 0, x_81);
lean_ctor_set(x_344, 1, x_343);
lean_ctor_set(x_344, 2, x_341);
lean_ctor_set(x_344, 3, x_342);
x_345 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__35;
lean_inc(x_81);
x_346 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_346, 0, x_81);
lean_ctor_set(x_346, 1, x_345);
x_347 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__38;
lean_inc(x_81);
x_348 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_348, 0, x_81);
lean_ctor_set(x_348, 1, x_347);
x_349 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__39;
lean_inc(x_63);
x_350 = lean_array_push(x_349, x_63);
x_351 = lean_array_push(x_350, x_348);
lean_inc(x_64);
x_352 = lean_array_push(x_351, x_64);
x_353 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__37;
x_354 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_354, 0, x_353);
lean_ctor_set(x_354, 1, x_352);
x_355 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__40;
lean_inc(x_81);
x_356 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_356, 0, x_81);
lean_ctor_set(x_356, 1, x_355);
x_357 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__43;
lean_inc(x_81);
x_358 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_358, 0, x_81);
lean_ctor_set(x_358, 1, x_357);
x_359 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__52;
lean_inc(x_81);
x_360 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_360, 0, x_81);
lean_ctor_set(x_360, 1, x_359);
x_361 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__26;
lean_inc(x_344);
x_362 = lean_array_push(x_361, x_344);
x_363 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__19;
x_364 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_364, 0, x_363);
lean_ctor_set(x_364, 1, x_362);
x_365 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__27;
x_366 = lean_array_push(x_365, x_360);
x_367 = lean_array_push(x_366, x_364);
x_368 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__53;
x_369 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_369, 0, x_368);
lean_ctor_set(x_369, 1, x_367);
x_370 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__54;
lean_inc(x_81);
x_371 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_371, 0, x_81);
lean_ctor_set(x_371, 1, x_370);
x_372 = lean_array_push(x_361, x_371);
x_373 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_373, 0, x_363);
lean_ctor_set(x_373, 1, x_372);
x_374 = lean_array_push(x_365, x_369);
lean_inc(x_373);
x_375 = lean_array_push(x_374, x_373);
x_376 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__51;
x_377 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_377, 0, x_376);
lean_ctor_set(x_377, 1, x_375);
x_378 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__55;
lean_inc(x_81);
x_379 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_379, 0, x_81);
lean_ctor_set(x_379, 1, x_378);
x_380 = lean_array_push(x_365, x_379);
x_381 = lean_array_push(x_380, x_78);
x_382 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__56;
x_383 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_383, 0, x_382);
lean_ctor_set(x_383, 1, x_381);
x_384 = lean_array_push(x_365, x_383);
x_385 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__58;
x_386 = lean_array_push(x_384, x_385);
x_387 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_387, 0, x_376);
lean_ctor_set(x_387, 1, x_386);
x_388 = lean_array_push(x_365, x_377);
x_389 = lean_array_push(x_388, x_387);
x_390 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_390, 0, x_363);
lean_ctor_set(x_390, 1, x_389);
x_391 = lean_array_push(x_361, x_390);
x_392 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__49;
x_393 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_393, 0, x_392);
lean_ctor_set(x_393, 1, x_391);
x_394 = lean_array_push(x_361, x_393);
x_395 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__47;
x_396 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_396, 0, x_395);
lean_ctor_set(x_396, 1, x_394);
x_397 = lean_array_push(x_365, x_358);
lean_inc(x_397);
x_398 = lean_array_push(x_397, x_396);
x_399 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__42;
x_400 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_400, 0, x_399);
lean_ctor_set(x_400, 1, x_398);
x_401 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__59;
lean_inc(x_81);
x_402 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_402, 0, x_81);
lean_ctor_set(x_402, 1, x_401);
x_403 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__63;
lean_inc(x_84);
lean_inc(x_336);
x_404 = l_Lean_addMacroScope(x_336, x_403, x_84);
x_405 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__62;
x_406 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__66;
lean_inc(x_81);
x_407 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_407, 0, x_81);
lean_ctor_set(x_407, 1, x_405);
lean_ctor_set(x_407, 2, x_404);
lean_ctor_set(x_407, 3, x_406);
x_408 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__69;
lean_inc(x_81);
x_409 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_409, 0, x_81);
lean_ctor_set(x_409, 1, x_408);
x_410 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__70;
lean_inc(x_81);
x_411 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_411, 0, x_81);
lean_ctor_set(x_411, 1, x_410);
x_412 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__75;
x_413 = l_Lean_addMacroScope(x_336, x_412, x_84);
x_414 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__74;
lean_inc(x_81);
x_415 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_415, 0, x_81);
lean_ctor_set(x_415, 1, x_414);
lean_ctor_set(x_415, 2, x_413);
lean_ctor_set(x_415, 3, x_342);
lean_inc(x_415);
x_416 = lean_array_push(x_361, x_415);
x_417 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_417, 0, x_363);
lean_ctor_set(x_417, 1, x_416);
x_418 = lean_array_push(x_365, x_411);
x_419 = lean_array_push(x_418, x_417);
x_420 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__71;
x_421 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_421, 0, x_420);
lean_ctor_set(x_421, 1, x_419);
x_422 = lean_array_push(x_365, x_421);
lean_inc(x_373);
x_423 = lean_array_push(x_422, x_373);
x_424 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_424, 0, x_376);
lean_ctor_set(x_424, 1, x_423);
x_425 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__76;
lean_inc(x_81);
x_426 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_426, 0, x_81);
lean_ctor_set(x_426, 1, x_425);
x_427 = lean_array_push(x_349, x_426);
x_428 = lean_array_push(x_427, x_415);
x_429 = lean_array_push(x_428, x_385);
x_430 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__77;
x_431 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_431, 0, x_430);
lean_ctor_set(x_431, 1, x_429);
x_432 = lean_array_push(x_365, x_431);
lean_inc(x_373);
x_433 = lean_array_push(x_432, x_373);
x_434 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_434, 0, x_376);
lean_ctor_set(x_434, 1, x_433);
x_435 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__78;
lean_inc(x_81);
x_436 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_436, 0, x_81);
lean_ctor_set(x_436, 1, x_435);
x_437 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__82;
lean_inc(x_81);
x_438 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_438, 0, x_81);
lean_ctor_set(x_438, 1, x_437);
x_439 = lean_array_push(x_361, x_438);
x_440 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__81;
x_441 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_441, 0, x_440);
lean_ctor_set(x_441, 1, x_439);
x_442 = lean_array_push(x_361, x_441);
x_443 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_443, 0, x_363);
lean_ctor_set(x_443, 1, x_442);
lean_inc(x_344);
x_444 = lean_array_push(x_365, x_344);
x_445 = lean_array_push(x_444, x_443);
x_446 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__8;
x_447 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_447, 0, x_446);
lean_ctor_set(x_447, 1, x_445);
x_448 = lean_array_push(x_365, x_436);
x_449 = lean_array_push(x_448, x_447);
x_450 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__79;
x_451 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_451, 0, x_450);
lean_ctor_set(x_451, 1, x_449);
x_452 = lean_array_push(x_365, x_451);
x_453 = lean_array_push(x_452, x_373);
x_454 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_454, 0, x_376);
lean_ctor_set(x_454, 1, x_453);
x_455 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__83;
lean_inc(x_81);
x_456 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_456, 0, x_81);
lean_ctor_set(x_456, 1, x_455);
x_457 = lean_array_push(x_361, x_456);
x_458 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__84;
x_459 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_459, 0, x_458);
lean_ctor_set(x_459, 1, x_457);
x_460 = lean_array_push(x_365, x_459);
x_461 = lean_array_push(x_460, x_385);
x_462 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_462, 0, x_376);
lean_ctor_set(x_462, 1, x_461);
x_463 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__85;
x_464 = lean_array_push(x_463, x_424);
x_465 = lean_array_push(x_464, x_434);
x_466 = lean_array_push(x_465, x_454);
x_467 = lean_array_push(x_466, x_462);
x_468 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_468, 0, x_363);
lean_ctor_set(x_468, 1, x_467);
x_469 = lean_array_push(x_361, x_468);
x_470 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_470, 0, x_392);
lean_ctor_set(x_470, 1, x_469);
x_471 = lean_array_push(x_361, x_470);
x_472 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_472, 0, x_395);
lean_ctor_set(x_472, 1, x_471);
x_473 = lean_array_push(x_397, x_472);
x_474 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_474, 0, x_399);
lean_ctor_set(x_474, 1, x_473);
x_475 = lean_array_push(x_365, x_474);
x_476 = lean_array_push(x_475, x_385);
x_477 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_477, 0, x_363);
lean_ctor_set(x_477, 1, x_476);
x_478 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__86;
x_479 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_479, 0, x_81);
lean_ctor_set(x_479, 1, x_478);
x_480 = lean_array_push(x_349, x_409);
x_481 = lean_array_push(x_480, x_477);
x_482 = lean_array_push(x_481, x_479);
x_483 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__68;
x_484 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_484, 0, x_483);
lean_ctor_set(x_484, 1, x_482);
x_485 = lean_array_push(x_361, x_484);
x_486 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_486, 0, x_363);
lean_ctor_set(x_486, 1, x_485);
x_487 = lean_array_push(x_365, x_407);
x_488 = lean_array_push(x_487, x_486);
x_489 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_489, 0, x_446);
lean_ctor_set(x_489, 1, x_488);
x_490 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__87;
x_491 = lean_array_push(x_490, x_339);
x_492 = lean_array_push(x_491, x_344);
x_493 = lean_array_push(x_492, x_346);
x_494 = lean_array_push(x_493, x_354);
x_495 = lean_array_push(x_494, x_356);
x_496 = lean_array_push(x_495, x_400);
x_497 = lean_array_push(x_496, x_402);
x_498 = lean_array_push(x_497, x_489);
x_499 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__29;
x_500 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_500, 0, x_499);
lean_ctor_set(x_500, 1, x_498);
x_501 = lean_unbox(x_65);
lean_dec(x_65);
if (x_501 == 0)
{
lean_object* x_502; 
lean_dec(x_3);
lean_dec(x_64);
lean_dec(x_63);
lean_dec(x_1);
x_502 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_502, 0, x_500);
lean_ctor_set(x_502, 1, x_337);
return x_502;
}
else
{
lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; 
x_503 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Deriving_mkInductiveApp___spec__2___rarg(x_7, x_8, x_337);
x_504 = lean_ctor_get(x_503, 0);
lean_inc(x_504);
x_505 = lean_ctor_get(x_503, 1);
lean_inc(x_505);
lean_dec(x_503);
x_506 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4, x_5, x_6, x_7, x_8, x_505);
lean_dec(x_3);
x_507 = lean_ctor_get(x_506, 0);
lean_inc(x_507);
x_508 = lean_ctor_get(x_506, 1);
lean_inc(x_508);
lean_dec(x_506);
x_509 = l_Lean_Elab_Term_getMainModule___rarg(x_8, x_508);
x_510 = lean_ctor_get(x_509, 0);
lean_inc(x_510);
x_511 = lean_ctor_get(x_509, 1);
lean_inc(x_511);
if (lean_is_exclusive(x_509)) {
 lean_ctor_release(x_509, 0);
 lean_ctor_release(x_509, 1);
 x_512 = x_509;
} else {
 lean_dec_ref(x_509);
 x_512 = lean_box(0);
}
x_513 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__88;
lean_inc(x_504);
x_514 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_514, 0, x_504);
lean_ctor_set(x_514, 1, x_513);
x_515 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__97;
x_516 = l_Lean_addMacroScope(x_510, x_515, x_507);
x_517 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__96;
lean_inc(x_504);
x_518 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_518, 0, x_504);
lean_ctor_set(x_518, 1, x_517);
lean_ctor_set(x_518, 2, x_516);
lean_ctor_set(x_518, 3, x_342);
x_519 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__98;
lean_inc(x_504);
x_520 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_520, 0, x_504);
lean_ctor_set(x_520, 1, x_519);
x_521 = lean_mk_syntax_ident(x_1);
x_522 = lean_array_push(x_365, x_63);
x_523 = lean_array_push(x_522, x_64);
x_524 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_524, 0, x_363);
lean_ctor_set(x_524, 1, x_523);
x_525 = lean_array_push(x_365, x_521);
x_526 = lean_array_push(x_525, x_524);
x_527 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_527, 0, x_446);
lean_ctor_set(x_527, 1, x_526);
x_528 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__99;
x_529 = lean_array_push(x_528, x_518);
x_530 = lean_array_push(x_529, x_385);
x_531 = lean_array_push(x_530, x_385);
x_532 = lean_array_push(x_531, x_520);
x_533 = lean_array_push(x_532, x_527);
x_534 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__93;
x_535 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_535, 0, x_534);
lean_ctor_set(x_535, 1, x_533);
x_536 = lean_array_push(x_361, x_535);
x_537 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__91;
x_538 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_538, 0, x_537);
lean_ctor_set(x_538, 1, x_536);
x_539 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_539, 0, x_504);
lean_ctor_set(x_539, 1, x_370);
x_540 = lean_array_push(x_361, x_539);
x_541 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_541, 0, x_363);
lean_ctor_set(x_541, 1, x_540);
x_542 = lean_array_push(x_463, x_514);
x_543 = lean_array_push(x_542, x_538);
x_544 = lean_array_push(x_543, x_541);
x_545 = lean_array_push(x_544, x_500);
x_546 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__89;
x_547 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_547, 0, x_546);
lean_ctor_set(x_547, 1, x_545);
if (lean_is_scalar(x_512)) {
 x_548 = lean_alloc_ctor(0, 2, 0);
} else {
 x_548 = x_512;
}
lean_ctor_set(x_548, 0, x_547);
lean_ctor_set(x_548, 1, x_511);
return x_548;
}
}
}
else
{
lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; uint8_t x_553; uint8_t x_554; uint8_t x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; uint8_t x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; lean_object* x_665; lean_object* x_666; lean_object* x_667; lean_object* x_668; lean_object* x_669; lean_object* x_670; lean_object* x_671; lean_object* x_672; lean_object* x_673; lean_object* x_674; lean_object* x_675; lean_object* x_676; lean_object* x_677; lean_object* x_678; lean_object* x_679; lean_object* x_680; lean_object* x_681; lean_object* x_682; lean_object* x_683; lean_object* x_684; lean_object* x_685; lean_object* x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; lean_object* x_691; lean_object* x_692; lean_object* x_693; lean_object* x_694; lean_object* x_695; lean_object* x_696; lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; lean_object* x_701; lean_object* x_702; lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; lean_object* x_707; lean_object* x_708; lean_object* x_709; lean_object* x_710; lean_object* x_711; lean_object* x_712; lean_object* x_713; lean_object* x_714; lean_object* x_715; lean_object* x_716; lean_object* x_717; lean_object* x_718; lean_object* x_719; lean_object* x_720; lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; lean_object* x_727; lean_object* x_728; lean_object* x_729; lean_object* x_730; lean_object* x_731; lean_object* x_732; lean_object* x_733; lean_object* x_734; lean_object* x_735; lean_object* x_736; uint8_t x_737; 
x_549 = lean_ctor_get(x_3, 0);
x_550 = lean_ctor_get(x_3, 1);
x_551 = lean_ctor_get(x_3, 2);
x_552 = lean_ctor_get(x_3, 3);
x_553 = lean_ctor_get_uint8(x_3, sizeof(void*)*8);
x_554 = lean_ctor_get_uint8(x_3, sizeof(void*)*8 + 1);
x_555 = lean_ctor_get_uint8(x_3, sizeof(void*)*8 + 2);
x_556 = lean_ctor_get(x_3, 5);
x_557 = lean_ctor_get(x_3, 6);
x_558 = lean_ctor_get(x_3, 7);
x_559 = lean_ctor_get_uint8(x_3, sizeof(void*)*8 + 3);
lean_inc(x_558);
lean_inc(x_557);
lean_inc(x_556);
lean_inc(x_552);
lean_inc(x_551);
lean_inc(x_550);
lean_inc(x_549);
lean_dec(x_3);
x_560 = lean_alloc_ctor(0, 8, 4);
lean_ctor_set(x_560, 0, x_549);
lean_ctor_set(x_560, 1, x_550);
lean_ctor_set(x_560, 2, x_551);
lean_ctor_set(x_560, 3, x_552);
lean_ctor_set(x_560, 4, x_70);
lean_ctor_set(x_560, 5, x_556);
lean_ctor_set(x_560, 6, x_557);
lean_ctor_set(x_560, 7, x_558);
lean_ctor_set_uint8(x_560, sizeof(void*)*8, x_553);
lean_ctor_set_uint8(x_560, sizeof(void*)*8 + 1, x_554);
lean_ctor_set_uint8(x_560, sizeof(void*)*8 + 2, x_555);
lean_ctor_set_uint8(x_560, sizeof(void*)*8 + 3, x_559);
lean_inc(x_560);
lean_inc(x_1);
x_561 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs(x_1, x_62, x_560, x_4, x_5, x_6, x_7, x_8, x_74);
x_562 = lean_ctor_get(x_561, 0);
lean_inc(x_562);
x_563 = lean_ctor_get(x_561, 1);
lean_inc(x_563);
lean_dec(x_561);
x_564 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Deriving_mkInductiveApp___spec__2___rarg(x_7, x_8, x_563);
x_565 = lean_ctor_get(x_564, 0);
lean_inc(x_565);
x_566 = lean_ctor_get(x_564, 1);
lean_inc(x_566);
lean_dec(x_564);
x_567 = l_Lean_Elab_Term_getCurrMacroScope(x_560, x_4, x_5, x_6, x_7, x_8, x_566);
x_568 = lean_ctor_get(x_567, 0);
lean_inc(x_568);
x_569 = lean_ctor_get(x_567, 1);
lean_inc(x_569);
lean_dec(x_567);
x_570 = l_Lean_Elab_Term_getMainModule___rarg(x_8, x_569);
x_571 = lean_ctor_get(x_570, 0);
lean_inc(x_571);
x_572 = lean_ctor_get(x_570, 1);
lean_inc(x_572);
if (lean_is_exclusive(x_570)) {
 lean_ctor_release(x_570, 0);
 lean_ctor_release(x_570, 1);
 x_573 = x_570;
} else {
 lean_dec_ref(x_570);
 x_573 = lean_box(0);
}
x_574 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__30;
lean_inc(x_565);
x_575 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_575, 0, x_565);
lean_ctor_set(x_575, 1, x_574);
x_576 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__34;
lean_inc(x_568);
lean_inc(x_571);
x_577 = l_Lean_addMacroScope(x_571, x_576, x_568);
x_578 = lean_box(0);
x_579 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__33;
lean_inc(x_565);
x_580 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_580, 0, x_565);
lean_ctor_set(x_580, 1, x_579);
lean_ctor_set(x_580, 2, x_577);
lean_ctor_set(x_580, 3, x_578);
x_581 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__35;
lean_inc(x_565);
x_582 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_582, 0, x_565);
lean_ctor_set(x_582, 1, x_581);
x_583 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__38;
lean_inc(x_565);
x_584 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_584, 0, x_565);
lean_ctor_set(x_584, 1, x_583);
x_585 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__39;
lean_inc(x_63);
x_586 = lean_array_push(x_585, x_63);
x_587 = lean_array_push(x_586, x_584);
lean_inc(x_64);
x_588 = lean_array_push(x_587, x_64);
x_589 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__37;
x_590 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_590, 0, x_589);
lean_ctor_set(x_590, 1, x_588);
x_591 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__40;
lean_inc(x_565);
x_592 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_592, 0, x_565);
lean_ctor_set(x_592, 1, x_591);
x_593 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__43;
lean_inc(x_565);
x_594 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_594, 0, x_565);
lean_ctor_set(x_594, 1, x_593);
x_595 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__52;
lean_inc(x_565);
x_596 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_596, 0, x_565);
lean_ctor_set(x_596, 1, x_595);
x_597 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__26;
lean_inc(x_580);
x_598 = lean_array_push(x_597, x_580);
x_599 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__19;
x_600 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_600, 0, x_599);
lean_ctor_set(x_600, 1, x_598);
x_601 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__27;
x_602 = lean_array_push(x_601, x_596);
x_603 = lean_array_push(x_602, x_600);
x_604 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__53;
x_605 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_605, 0, x_604);
lean_ctor_set(x_605, 1, x_603);
x_606 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__54;
lean_inc(x_565);
x_607 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_607, 0, x_565);
lean_ctor_set(x_607, 1, x_606);
x_608 = lean_array_push(x_597, x_607);
x_609 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_609, 0, x_599);
lean_ctor_set(x_609, 1, x_608);
x_610 = lean_array_push(x_601, x_605);
lean_inc(x_609);
x_611 = lean_array_push(x_610, x_609);
x_612 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__51;
x_613 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_613, 0, x_612);
lean_ctor_set(x_613, 1, x_611);
x_614 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__55;
lean_inc(x_565);
x_615 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_615, 0, x_565);
lean_ctor_set(x_615, 1, x_614);
x_616 = lean_array_push(x_601, x_615);
x_617 = lean_array_push(x_616, x_562);
x_618 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__56;
x_619 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_619, 0, x_618);
lean_ctor_set(x_619, 1, x_617);
x_620 = lean_array_push(x_601, x_619);
x_621 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__58;
x_622 = lean_array_push(x_620, x_621);
x_623 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_623, 0, x_612);
lean_ctor_set(x_623, 1, x_622);
x_624 = lean_array_push(x_601, x_613);
x_625 = lean_array_push(x_624, x_623);
x_626 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_626, 0, x_599);
lean_ctor_set(x_626, 1, x_625);
x_627 = lean_array_push(x_597, x_626);
x_628 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__49;
x_629 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_629, 0, x_628);
lean_ctor_set(x_629, 1, x_627);
x_630 = lean_array_push(x_597, x_629);
x_631 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__47;
x_632 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_632, 0, x_631);
lean_ctor_set(x_632, 1, x_630);
x_633 = lean_array_push(x_601, x_594);
lean_inc(x_633);
x_634 = lean_array_push(x_633, x_632);
x_635 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__42;
x_636 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_636, 0, x_635);
lean_ctor_set(x_636, 1, x_634);
x_637 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__59;
lean_inc(x_565);
x_638 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_638, 0, x_565);
lean_ctor_set(x_638, 1, x_637);
x_639 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__63;
lean_inc(x_568);
lean_inc(x_571);
x_640 = l_Lean_addMacroScope(x_571, x_639, x_568);
x_641 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__62;
x_642 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__66;
lean_inc(x_565);
x_643 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_643, 0, x_565);
lean_ctor_set(x_643, 1, x_641);
lean_ctor_set(x_643, 2, x_640);
lean_ctor_set(x_643, 3, x_642);
x_644 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__69;
lean_inc(x_565);
x_645 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_645, 0, x_565);
lean_ctor_set(x_645, 1, x_644);
x_646 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__70;
lean_inc(x_565);
x_647 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_647, 0, x_565);
lean_ctor_set(x_647, 1, x_646);
x_648 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__75;
x_649 = l_Lean_addMacroScope(x_571, x_648, x_568);
x_650 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__74;
lean_inc(x_565);
x_651 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_651, 0, x_565);
lean_ctor_set(x_651, 1, x_650);
lean_ctor_set(x_651, 2, x_649);
lean_ctor_set(x_651, 3, x_578);
lean_inc(x_651);
x_652 = lean_array_push(x_597, x_651);
x_653 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_653, 0, x_599);
lean_ctor_set(x_653, 1, x_652);
x_654 = lean_array_push(x_601, x_647);
x_655 = lean_array_push(x_654, x_653);
x_656 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__71;
x_657 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_657, 0, x_656);
lean_ctor_set(x_657, 1, x_655);
x_658 = lean_array_push(x_601, x_657);
lean_inc(x_609);
x_659 = lean_array_push(x_658, x_609);
x_660 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_660, 0, x_612);
lean_ctor_set(x_660, 1, x_659);
x_661 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__76;
lean_inc(x_565);
x_662 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_662, 0, x_565);
lean_ctor_set(x_662, 1, x_661);
x_663 = lean_array_push(x_585, x_662);
x_664 = lean_array_push(x_663, x_651);
x_665 = lean_array_push(x_664, x_621);
x_666 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__77;
x_667 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_667, 0, x_666);
lean_ctor_set(x_667, 1, x_665);
x_668 = lean_array_push(x_601, x_667);
lean_inc(x_609);
x_669 = lean_array_push(x_668, x_609);
x_670 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_670, 0, x_612);
lean_ctor_set(x_670, 1, x_669);
x_671 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__78;
lean_inc(x_565);
x_672 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_672, 0, x_565);
lean_ctor_set(x_672, 1, x_671);
x_673 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__82;
lean_inc(x_565);
x_674 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_674, 0, x_565);
lean_ctor_set(x_674, 1, x_673);
x_675 = lean_array_push(x_597, x_674);
x_676 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__81;
x_677 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_677, 0, x_676);
lean_ctor_set(x_677, 1, x_675);
x_678 = lean_array_push(x_597, x_677);
x_679 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_679, 0, x_599);
lean_ctor_set(x_679, 1, x_678);
lean_inc(x_580);
x_680 = lean_array_push(x_601, x_580);
x_681 = lean_array_push(x_680, x_679);
x_682 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__8;
x_683 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_683, 0, x_682);
lean_ctor_set(x_683, 1, x_681);
x_684 = lean_array_push(x_601, x_672);
x_685 = lean_array_push(x_684, x_683);
x_686 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__79;
x_687 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_687, 0, x_686);
lean_ctor_set(x_687, 1, x_685);
x_688 = lean_array_push(x_601, x_687);
x_689 = lean_array_push(x_688, x_609);
x_690 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_690, 0, x_612);
lean_ctor_set(x_690, 1, x_689);
x_691 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__83;
lean_inc(x_565);
x_692 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_692, 0, x_565);
lean_ctor_set(x_692, 1, x_691);
x_693 = lean_array_push(x_597, x_692);
x_694 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__84;
x_695 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_695, 0, x_694);
lean_ctor_set(x_695, 1, x_693);
x_696 = lean_array_push(x_601, x_695);
x_697 = lean_array_push(x_696, x_621);
x_698 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_698, 0, x_612);
lean_ctor_set(x_698, 1, x_697);
x_699 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__85;
x_700 = lean_array_push(x_699, x_660);
x_701 = lean_array_push(x_700, x_670);
x_702 = lean_array_push(x_701, x_690);
x_703 = lean_array_push(x_702, x_698);
x_704 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_704, 0, x_599);
lean_ctor_set(x_704, 1, x_703);
x_705 = lean_array_push(x_597, x_704);
x_706 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_706, 0, x_628);
lean_ctor_set(x_706, 1, x_705);
x_707 = lean_array_push(x_597, x_706);
x_708 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_708, 0, x_631);
lean_ctor_set(x_708, 1, x_707);
x_709 = lean_array_push(x_633, x_708);
x_710 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_710, 0, x_635);
lean_ctor_set(x_710, 1, x_709);
x_711 = lean_array_push(x_601, x_710);
x_712 = lean_array_push(x_711, x_621);
x_713 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_713, 0, x_599);
lean_ctor_set(x_713, 1, x_712);
x_714 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__86;
x_715 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_715, 0, x_565);
lean_ctor_set(x_715, 1, x_714);
x_716 = lean_array_push(x_585, x_645);
x_717 = lean_array_push(x_716, x_713);
x_718 = lean_array_push(x_717, x_715);
x_719 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__68;
x_720 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_720, 0, x_719);
lean_ctor_set(x_720, 1, x_718);
x_721 = lean_array_push(x_597, x_720);
x_722 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_722, 0, x_599);
lean_ctor_set(x_722, 1, x_721);
x_723 = lean_array_push(x_601, x_643);
x_724 = lean_array_push(x_723, x_722);
x_725 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_725, 0, x_682);
lean_ctor_set(x_725, 1, x_724);
x_726 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__87;
x_727 = lean_array_push(x_726, x_575);
x_728 = lean_array_push(x_727, x_580);
x_729 = lean_array_push(x_728, x_582);
x_730 = lean_array_push(x_729, x_590);
x_731 = lean_array_push(x_730, x_592);
x_732 = lean_array_push(x_731, x_636);
x_733 = lean_array_push(x_732, x_638);
x_734 = lean_array_push(x_733, x_725);
x_735 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__29;
x_736 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_736, 0, x_735);
lean_ctor_set(x_736, 1, x_734);
x_737 = lean_unbox(x_65);
lean_dec(x_65);
if (x_737 == 0)
{
lean_object* x_738; 
lean_dec(x_560);
lean_dec(x_64);
lean_dec(x_63);
lean_dec(x_1);
if (lean_is_scalar(x_573)) {
 x_738 = lean_alloc_ctor(0, 2, 0);
} else {
 x_738 = x_573;
}
lean_ctor_set(x_738, 0, x_736);
lean_ctor_set(x_738, 1, x_572);
return x_738;
}
else
{
lean_object* x_739; lean_object* x_740; lean_object* x_741; lean_object* x_742; lean_object* x_743; lean_object* x_744; lean_object* x_745; lean_object* x_746; lean_object* x_747; lean_object* x_748; lean_object* x_749; lean_object* x_750; lean_object* x_751; lean_object* x_752; lean_object* x_753; lean_object* x_754; lean_object* x_755; lean_object* x_756; lean_object* x_757; lean_object* x_758; lean_object* x_759; lean_object* x_760; lean_object* x_761; lean_object* x_762; lean_object* x_763; lean_object* x_764; lean_object* x_765; lean_object* x_766; lean_object* x_767; lean_object* x_768; lean_object* x_769; lean_object* x_770; lean_object* x_771; lean_object* x_772; lean_object* x_773; lean_object* x_774; lean_object* x_775; lean_object* x_776; lean_object* x_777; lean_object* x_778; lean_object* x_779; lean_object* x_780; lean_object* x_781; lean_object* x_782; lean_object* x_783; lean_object* x_784; 
lean_dec(x_573);
x_739 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Deriving_mkInductiveApp___spec__2___rarg(x_7, x_8, x_572);
x_740 = lean_ctor_get(x_739, 0);
lean_inc(x_740);
x_741 = lean_ctor_get(x_739, 1);
lean_inc(x_741);
lean_dec(x_739);
x_742 = l_Lean_Elab_Term_getCurrMacroScope(x_560, x_4, x_5, x_6, x_7, x_8, x_741);
lean_dec(x_560);
x_743 = lean_ctor_get(x_742, 0);
lean_inc(x_743);
x_744 = lean_ctor_get(x_742, 1);
lean_inc(x_744);
lean_dec(x_742);
x_745 = l_Lean_Elab_Term_getMainModule___rarg(x_8, x_744);
x_746 = lean_ctor_get(x_745, 0);
lean_inc(x_746);
x_747 = lean_ctor_get(x_745, 1);
lean_inc(x_747);
if (lean_is_exclusive(x_745)) {
 lean_ctor_release(x_745, 0);
 lean_ctor_release(x_745, 1);
 x_748 = x_745;
} else {
 lean_dec_ref(x_745);
 x_748 = lean_box(0);
}
x_749 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__88;
lean_inc(x_740);
x_750 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_750, 0, x_740);
lean_ctor_set(x_750, 1, x_749);
x_751 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__97;
x_752 = l_Lean_addMacroScope(x_746, x_751, x_743);
x_753 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__96;
lean_inc(x_740);
x_754 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_754, 0, x_740);
lean_ctor_set(x_754, 1, x_753);
lean_ctor_set(x_754, 2, x_752);
lean_ctor_set(x_754, 3, x_578);
x_755 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__98;
lean_inc(x_740);
x_756 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_756, 0, x_740);
lean_ctor_set(x_756, 1, x_755);
x_757 = lean_mk_syntax_ident(x_1);
x_758 = lean_array_push(x_601, x_63);
x_759 = lean_array_push(x_758, x_64);
x_760 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_760, 0, x_599);
lean_ctor_set(x_760, 1, x_759);
x_761 = lean_array_push(x_601, x_757);
x_762 = lean_array_push(x_761, x_760);
x_763 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_763, 0, x_682);
lean_ctor_set(x_763, 1, x_762);
x_764 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__99;
x_765 = lean_array_push(x_764, x_754);
x_766 = lean_array_push(x_765, x_621);
x_767 = lean_array_push(x_766, x_621);
x_768 = lean_array_push(x_767, x_756);
x_769 = lean_array_push(x_768, x_763);
x_770 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__93;
x_771 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_771, 0, x_770);
lean_ctor_set(x_771, 1, x_769);
x_772 = lean_array_push(x_597, x_771);
x_773 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__91;
x_774 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_774, 0, x_773);
lean_ctor_set(x_774, 1, x_772);
x_775 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_775, 0, x_740);
lean_ctor_set(x_775, 1, x_606);
x_776 = lean_array_push(x_597, x_775);
x_777 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_777, 0, x_599);
lean_ctor_set(x_777, 1, x_776);
x_778 = lean_array_push(x_699, x_750);
x_779 = lean_array_push(x_778, x_774);
x_780 = lean_array_push(x_779, x_777);
x_781 = lean_array_push(x_780, x_736);
x_782 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__89;
x_783 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_783, 0, x_782);
lean_ctor_set(x_783, 1, x_781);
if (lean_is_scalar(x_748)) {
 x_784 = lean_alloc_ctor(0, 2, 0);
} else {
 x_784 = x_748;
}
lean_ctor_set(x_784, 0, x_783);
lean_ctor_set(x_784, 1, x_747);
return x_784;
}
}
}
else
{
lean_object* x_785; lean_object* x_786; lean_object* x_787; lean_object* x_788; lean_object* x_789; lean_object* x_790; lean_object* x_791; lean_object* x_792; lean_object* x_793; lean_object* x_794; lean_object* x_795; lean_object* x_796; lean_object* x_797; uint8_t x_798; uint8_t x_799; uint8_t x_800; lean_object* x_801; lean_object* x_802; lean_object* x_803; uint8_t x_804; lean_object* x_805; lean_object* x_806; lean_object* x_807; lean_object* x_808; lean_object* x_809; lean_object* x_810; lean_object* x_811; lean_object* x_812; lean_object* x_813; lean_object* x_814; lean_object* x_815; lean_object* x_816; lean_object* x_817; lean_object* x_818; lean_object* x_819; lean_object* x_820; lean_object* x_821; lean_object* x_822; lean_object* x_823; lean_object* x_824; lean_object* x_825; lean_object* x_826; lean_object* x_827; lean_object* x_828; lean_object* x_829; lean_object* x_830; lean_object* x_831; lean_object* x_832; lean_object* x_833; lean_object* x_834; lean_object* x_835; lean_object* x_836; lean_object* x_837; lean_object* x_838; lean_object* x_839; lean_object* x_840; lean_object* x_841; lean_object* x_842; lean_object* x_843; lean_object* x_844; lean_object* x_845; lean_object* x_846; lean_object* x_847; lean_object* x_848; lean_object* x_849; lean_object* x_850; lean_object* x_851; lean_object* x_852; lean_object* x_853; lean_object* x_854; lean_object* x_855; lean_object* x_856; lean_object* x_857; lean_object* x_858; lean_object* x_859; lean_object* x_860; lean_object* x_861; lean_object* x_862; lean_object* x_863; lean_object* x_864; lean_object* x_865; lean_object* x_866; lean_object* x_867; lean_object* x_868; lean_object* x_869; lean_object* x_870; lean_object* x_871; lean_object* x_872; lean_object* x_873; lean_object* x_874; lean_object* x_875; lean_object* x_876; lean_object* x_877; lean_object* x_878; lean_object* x_879; lean_object* x_880; lean_object* x_881; lean_object* x_882; lean_object* x_883; lean_object* x_884; lean_object* x_885; lean_object* x_886; lean_object* x_887; lean_object* x_888; lean_object* x_889; lean_object* x_890; lean_object* x_891; lean_object* x_892; lean_object* x_893; lean_object* x_894; lean_object* x_895; lean_object* x_896; lean_object* x_897; lean_object* x_898; lean_object* x_899; lean_object* x_900; lean_object* x_901; lean_object* x_902; lean_object* x_903; lean_object* x_904; lean_object* x_905; lean_object* x_906; lean_object* x_907; lean_object* x_908; lean_object* x_909; lean_object* x_910; lean_object* x_911; lean_object* x_912; lean_object* x_913; lean_object* x_914; lean_object* x_915; lean_object* x_916; lean_object* x_917; lean_object* x_918; lean_object* x_919; lean_object* x_920; lean_object* x_921; lean_object* x_922; lean_object* x_923; lean_object* x_924; lean_object* x_925; lean_object* x_926; lean_object* x_927; lean_object* x_928; lean_object* x_929; lean_object* x_930; lean_object* x_931; lean_object* x_932; lean_object* x_933; lean_object* x_934; lean_object* x_935; lean_object* x_936; lean_object* x_937; lean_object* x_938; lean_object* x_939; lean_object* x_940; lean_object* x_941; lean_object* x_942; lean_object* x_943; lean_object* x_944; lean_object* x_945; lean_object* x_946; lean_object* x_947; lean_object* x_948; lean_object* x_949; lean_object* x_950; lean_object* x_951; lean_object* x_952; lean_object* x_953; lean_object* x_954; lean_object* x_955; lean_object* x_956; lean_object* x_957; lean_object* x_958; lean_object* x_959; lean_object* x_960; lean_object* x_961; lean_object* x_962; lean_object* x_963; lean_object* x_964; lean_object* x_965; lean_object* x_966; lean_object* x_967; lean_object* x_968; lean_object* x_969; lean_object* x_970; lean_object* x_971; lean_object* x_972; lean_object* x_973; lean_object* x_974; lean_object* x_975; lean_object* x_976; lean_object* x_977; lean_object* x_978; lean_object* x_979; lean_object* x_980; lean_object* x_981; lean_object* x_982; uint8_t x_983; 
x_785 = lean_ctor_get(x_67, 0);
x_786 = lean_ctor_get(x_67, 1);
x_787 = lean_ctor_get(x_67, 2);
x_788 = lean_ctor_get(x_67, 3);
lean_inc(x_788);
lean_inc(x_787);
lean_inc(x_786);
lean_inc(x_785);
lean_dec(x_67);
x_789 = lean_unsigned_to_nat(1u);
x_790 = lean_nat_add(x_786, x_789);
x_791 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_791, 0, x_785);
lean_ctor_set(x_791, 1, x_790);
lean_ctor_set(x_791, 2, x_787);
lean_ctor_set(x_791, 3, x_788);
x_792 = lean_st_ref_set(x_8, x_791, x_68);
x_793 = lean_ctor_get(x_792, 1);
lean_inc(x_793);
lean_dec(x_792);
x_794 = lean_ctor_get(x_3, 0);
lean_inc(x_794);
x_795 = lean_ctor_get(x_3, 1);
lean_inc(x_795);
x_796 = lean_ctor_get(x_3, 2);
lean_inc(x_796);
x_797 = lean_ctor_get(x_3, 3);
lean_inc(x_797);
x_798 = lean_ctor_get_uint8(x_3, sizeof(void*)*8);
x_799 = lean_ctor_get_uint8(x_3, sizeof(void*)*8 + 1);
x_800 = lean_ctor_get_uint8(x_3, sizeof(void*)*8 + 2);
x_801 = lean_ctor_get(x_3, 5);
lean_inc(x_801);
x_802 = lean_ctor_get(x_3, 6);
lean_inc(x_802);
x_803 = lean_ctor_get(x_3, 7);
lean_inc(x_803);
x_804 = lean_ctor_get_uint8(x_3, sizeof(void*)*8 + 3);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 lean_ctor_release(x_3, 3);
 lean_ctor_release(x_3, 4);
 lean_ctor_release(x_3, 5);
 lean_ctor_release(x_3, 6);
 lean_ctor_release(x_3, 7);
 x_805 = x_3;
} else {
 lean_dec_ref(x_3);
 x_805 = lean_box(0);
}
if (lean_is_scalar(x_805)) {
 x_806 = lean_alloc_ctor(0, 8, 4);
} else {
 x_806 = x_805;
}
lean_ctor_set(x_806, 0, x_794);
lean_ctor_set(x_806, 1, x_795);
lean_ctor_set(x_806, 2, x_796);
lean_ctor_set(x_806, 3, x_797);
lean_ctor_set(x_806, 4, x_786);
lean_ctor_set(x_806, 5, x_801);
lean_ctor_set(x_806, 6, x_802);
lean_ctor_set(x_806, 7, x_803);
lean_ctor_set_uint8(x_806, sizeof(void*)*8, x_798);
lean_ctor_set_uint8(x_806, sizeof(void*)*8 + 1, x_799);
lean_ctor_set_uint8(x_806, sizeof(void*)*8 + 2, x_800);
lean_ctor_set_uint8(x_806, sizeof(void*)*8 + 3, x_804);
lean_inc(x_806);
lean_inc(x_1);
x_807 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs(x_1, x_62, x_806, x_4, x_5, x_6, x_7, x_8, x_793);
x_808 = lean_ctor_get(x_807, 0);
lean_inc(x_808);
x_809 = lean_ctor_get(x_807, 1);
lean_inc(x_809);
lean_dec(x_807);
x_810 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Deriving_mkInductiveApp___spec__2___rarg(x_7, x_8, x_809);
x_811 = lean_ctor_get(x_810, 0);
lean_inc(x_811);
x_812 = lean_ctor_get(x_810, 1);
lean_inc(x_812);
lean_dec(x_810);
x_813 = l_Lean_Elab_Term_getCurrMacroScope(x_806, x_4, x_5, x_6, x_7, x_8, x_812);
x_814 = lean_ctor_get(x_813, 0);
lean_inc(x_814);
x_815 = lean_ctor_get(x_813, 1);
lean_inc(x_815);
lean_dec(x_813);
x_816 = l_Lean_Elab_Term_getMainModule___rarg(x_8, x_815);
x_817 = lean_ctor_get(x_816, 0);
lean_inc(x_817);
x_818 = lean_ctor_get(x_816, 1);
lean_inc(x_818);
if (lean_is_exclusive(x_816)) {
 lean_ctor_release(x_816, 0);
 lean_ctor_release(x_816, 1);
 x_819 = x_816;
} else {
 lean_dec_ref(x_816);
 x_819 = lean_box(0);
}
x_820 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__30;
lean_inc(x_811);
x_821 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_821, 0, x_811);
lean_ctor_set(x_821, 1, x_820);
x_822 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__34;
lean_inc(x_814);
lean_inc(x_817);
x_823 = l_Lean_addMacroScope(x_817, x_822, x_814);
x_824 = lean_box(0);
x_825 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__33;
lean_inc(x_811);
x_826 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_826, 0, x_811);
lean_ctor_set(x_826, 1, x_825);
lean_ctor_set(x_826, 2, x_823);
lean_ctor_set(x_826, 3, x_824);
x_827 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__35;
lean_inc(x_811);
x_828 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_828, 0, x_811);
lean_ctor_set(x_828, 1, x_827);
x_829 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__38;
lean_inc(x_811);
x_830 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_830, 0, x_811);
lean_ctor_set(x_830, 1, x_829);
x_831 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__39;
lean_inc(x_63);
x_832 = lean_array_push(x_831, x_63);
x_833 = lean_array_push(x_832, x_830);
lean_inc(x_64);
x_834 = lean_array_push(x_833, x_64);
x_835 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__37;
x_836 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_836, 0, x_835);
lean_ctor_set(x_836, 1, x_834);
x_837 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__40;
lean_inc(x_811);
x_838 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_838, 0, x_811);
lean_ctor_set(x_838, 1, x_837);
x_839 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__43;
lean_inc(x_811);
x_840 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_840, 0, x_811);
lean_ctor_set(x_840, 1, x_839);
x_841 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__52;
lean_inc(x_811);
x_842 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_842, 0, x_811);
lean_ctor_set(x_842, 1, x_841);
x_843 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__26;
lean_inc(x_826);
x_844 = lean_array_push(x_843, x_826);
x_845 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__19;
x_846 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_846, 0, x_845);
lean_ctor_set(x_846, 1, x_844);
x_847 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__27;
x_848 = lean_array_push(x_847, x_842);
x_849 = lean_array_push(x_848, x_846);
x_850 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__53;
x_851 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_851, 0, x_850);
lean_ctor_set(x_851, 1, x_849);
x_852 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__54;
lean_inc(x_811);
x_853 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_853, 0, x_811);
lean_ctor_set(x_853, 1, x_852);
x_854 = lean_array_push(x_843, x_853);
x_855 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_855, 0, x_845);
lean_ctor_set(x_855, 1, x_854);
x_856 = lean_array_push(x_847, x_851);
lean_inc(x_855);
x_857 = lean_array_push(x_856, x_855);
x_858 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__51;
x_859 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_859, 0, x_858);
lean_ctor_set(x_859, 1, x_857);
x_860 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__55;
lean_inc(x_811);
x_861 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_861, 0, x_811);
lean_ctor_set(x_861, 1, x_860);
x_862 = lean_array_push(x_847, x_861);
x_863 = lean_array_push(x_862, x_808);
x_864 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__56;
x_865 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_865, 0, x_864);
lean_ctor_set(x_865, 1, x_863);
x_866 = lean_array_push(x_847, x_865);
x_867 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__58;
x_868 = lean_array_push(x_866, x_867);
x_869 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_869, 0, x_858);
lean_ctor_set(x_869, 1, x_868);
x_870 = lean_array_push(x_847, x_859);
x_871 = lean_array_push(x_870, x_869);
x_872 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_872, 0, x_845);
lean_ctor_set(x_872, 1, x_871);
x_873 = lean_array_push(x_843, x_872);
x_874 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__49;
x_875 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_875, 0, x_874);
lean_ctor_set(x_875, 1, x_873);
x_876 = lean_array_push(x_843, x_875);
x_877 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__47;
x_878 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_878, 0, x_877);
lean_ctor_set(x_878, 1, x_876);
x_879 = lean_array_push(x_847, x_840);
lean_inc(x_879);
x_880 = lean_array_push(x_879, x_878);
x_881 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__42;
x_882 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_882, 0, x_881);
lean_ctor_set(x_882, 1, x_880);
x_883 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__59;
lean_inc(x_811);
x_884 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_884, 0, x_811);
lean_ctor_set(x_884, 1, x_883);
x_885 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__63;
lean_inc(x_814);
lean_inc(x_817);
x_886 = l_Lean_addMacroScope(x_817, x_885, x_814);
x_887 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__62;
x_888 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__66;
lean_inc(x_811);
x_889 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_889, 0, x_811);
lean_ctor_set(x_889, 1, x_887);
lean_ctor_set(x_889, 2, x_886);
lean_ctor_set(x_889, 3, x_888);
x_890 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__69;
lean_inc(x_811);
x_891 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_891, 0, x_811);
lean_ctor_set(x_891, 1, x_890);
x_892 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__70;
lean_inc(x_811);
x_893 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_893, 0, x_811);
lean_ctor_set(x_893, 1, x_892);
x_894 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__75;
x_895 = l_Lean_addMacroScope(x_817, x_894, x_814);
x_896 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__74;
lean_inc(x_811);
x_897 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_897, 0, x_811);
lean_ctor_set(x_897, 1, x_896);
lean_ctor_set(x_897, 2, x_895);
lean_ctor_set(x_897, 3, x_824);
lean_inc(x_897);
x_898 = lean_array_push(x_843, x_897);
x_899 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_899, 0, x_845);
lean_ctor_set(x_899, 1, x_898);
x_900 = lean_array_push(x_847, x_893);
x_901 = lean_array_push(x_900, x_899);
x_902 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__71;
x_903 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_903, 0, x_902);
lean_ctor_set(x_903, 1, x_901);
x_904 = lean_array_push(x_847, x_903);
lean_inc(x_855);
x_905 = lean_array_push(x_904, x_855);
x_906 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_906, 0, x_858);
lean_ctor_set(x_906, 1, x_905);
x_907 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__76;
lean_inc(x_811);
x_908 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_908, 0, x_811);
lean_ctor_set(x_908, 1, x_907);
x_909 = lean_array_push(x_831, x_908);
x_910 = lean_array_push(x_909, x_897);
x_911 = lean_array_push(x_910, x_867);
x_912 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__77;
x_913 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_913, 0, x_912);
lean_ctor_set(x_913, 1, x_911);
x_914 = lean_array_push(x_847, x_913);
lean_inc(x_855);
x_915 = lean_array_push(x_914, x_855);
x_916 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_916, 0, x_858);
lean_ctor_set(x_916, 1, x_915);
x_917 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__78;
lean_inc(x_811);
x_918 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_918, 0, x_811);
lean_ctor_set(x_918, 1, x_917);
x_919 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__82;
lean_inc(x_811);
x_920 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_920, 0, x_811);
lean_ctor_set(x_920, 1, x_919);
x_921 = lean_array_push(x_843, x_920);
x_922 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__81;
x_923 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_923, 0, x_922);
lean_ctor_set(x_923, 1, x_921);
x_924 = lean_array_push(x_843, x_923);
x_925 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_925, 0, x_845);
lean_ctor_set(x_925, 1, x_924);
lean_inc(x_826);
x_926 = lean_array_push(x_847, x_826);
x_927 = lean_array_push(x_926, x_925);
x_928 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__8;
x_929 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_929, 0, x_928);
lean_ctor_set(x_929, 1, x_927);
x_930 = lean_array_push(x_847, x_918);
x_931 = lean_array_push(x_930, x_929);
x_932 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__79;
x_933 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_933, 0, x_932);
lean_ctor_set(x_933, 1, x_931);
x_934 = lean_array_push(x_847, x_933);
x_935 = lean_array_push(x_934, x_855);
x_936 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_936, 0, x_858);
lean_ctor_set(x_936, 1, x_935);
x_937 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__83;
lean_inc(x_811);
x_938 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_938, 0, x_811);
lean_ctor_set(x_938, 1, x_937);
x_939 = lean_array_push(x_843, x_938);
x_940 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__84;
x_941 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_941, 0, x_940);
lean_ctor_set(x_941, 1, x_939);
x_942 = lean_array_push(x_847, x_941);
x_943 = lean_array_push(x_942, x_867);
x_944 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_944, 0, x_858);
lean_ctor_set(x_944, 1, x_943);
x_945 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__85;
x_946 = lean_array_push(x_945, x_906);
x_947 = lean_array_push(x_946, x_916);
x_948 = lean_array_push(x_947, x_936);
x_949 = lean_array_push(x_948, x_944);
x_950 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_950, 0, x_845);
lean_ctor_set(x_950, 1, x_949);
x_951 = lean_array_push(x_843, x_950);
x_952 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_952, 0, x_874);
lean_ctor_set(x_952, 1, x_951);
x_953 = lean_array_push(x_843, x_952);
x_954 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_954, 0, x_877);
lean_ctor_set(x_954, 1, x_953);
x_955 = lean_array_push(x_879, x_954);
x_956 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_956, 0, x_881);
lean_ctor_set(x_956, 1, x_955);
x_957 = lean_array_push(x_847, x_956);
x_958 = lean_array_push(x_957, x_867);
x_959 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_959, 0, x_845);
lean_ctor_set(x_959, 1, x_958);
x_960 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__86;
x_961 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_961, 0, x_811);
lean_ctor_set(x_961, 1, x_960);
x_962 = lean_array_push(x_831, x_891);
x_963 = lean_array_push(x_962, x_959);
x_964 = lean_array_push(x_963, x_961);
x_965 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__68;
x_966 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_966, 0, x_965);
lean_ctor_set(x_966, 1, x_964);
x_967 = lean_array_push(x_843, x_966);
x_968 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_968, 0, x_845);
lean_ctor_set(x_968, 1, x_967);
x_969 = lean_array_push(x_847, x_889);
x_970 = lean_array_push(x_969, x_968);
x_971 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_971, 0, x_928);
lean_ctor_set(x_971, 1, x_970);
x_972 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__87;
x_973 = lean_array_push(x_972, x_821);
x_974 = lean_array_push(x_973, x_826);
x_975 = lean_array_push(x_974, x_828);
x_976 = lean_array_push(x_975, x_836);
x_977 = lean_array_push(x_976, x_838);
x_978 = lean_array_push(x_977, x_882);
x_979 = lean_array_push(x_978, x_884);
x_980 = lean_array_push(x_979, x_971);
x_981 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__29;
x_982 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_982, 0, x_981);
lean_ctor_set(x_982, 1, x_980);
x_983 = lean_unbox(x_65);
lean_dec(x_65);
if (x_983 == 0)
{
lean_object* x_984; 
lean_dec(x_806);
lean_dec(x_64);
lean_dec(x_63);
lean_dec(x_1);
if (lean_is_scalar(x_819)) {
 x_984 = lean_alloc_ctor(0, 2, 0);
} else {
 x_984 = x_819;
}
lean_ctor_set(x_984, 0, x_982);
lean_ctor_set(x_984, 1, x_818);
return x_984;
}
else
{
lean_object* x_985; lean_object* x_986; lean_object* x_987; lean_object* x_988; lean_object* x_989; lean_object* x_990; lean_object* x_991; lean_object* x_992; lean_object* x_993; lean_object* x_994; lean_object* x_995; lean_object* x_996; lean_object* x_997; lean_object* x_998; lean_object* x_999; lean_object* x_1000; lean_object* x_1001; lean_object* x_1002; lean_object* x_1003; lean_object* x_1004; lean_object* x_1005; lean_object* x_1006; lean_object* x_1007; lean_object* x_1008; lean_object* x_1009; lean_object* x_1010; lean_object* x_1011; lean_object* x_1012; lean_object* x_1013; lean_object* x_1014; lean_object* x_1015; lean_object* x_1016; lean_object* x_1017; lean_object* x_1018; lean_object* x_1019; lean_object* x_1020; lean_object* x_1021; lean_object* x_1022; lean_object* x_1023; lean_object* x_1024; lean_object* x_1025; lean_object* x_1026; lean_object* x_1027; lean_object* x_1028; lean_object* x_1029; lean_object* x_1030; 
lean_dec(x_819);
x_985 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Deriving_mkInductiveApp___spec__2___rarg(x_7, x_8, x_818);
x_986 = lean_ctor_get(x_985, 0);
lean_inc(x_986);
x_987 = lean_ctor_get(x_985, 1);
lean_inc(x_987);
lean_dec(x_985);
x_988 = l_Lean_Elab_Term_getCurrMacroScope(x_806, x_4, x_5, x_6, x_7, x_8, x_987);
lean_dec(x_806);
x_989 = lean_ctor_get(x_988, 0);
lean_inc(x_989);
x_990 = lean_ctor_get(x_988, 1);
lean_inc(x_990);
lean_dec(x_988);
x_991 = l_Lean_Elab_Term_getMainModule___rarg(x_8, x_990);
x_992 = lean_ctor_get(x_991, 0);
lean_inc(x_992);
x_993 = lean_ctor_get(x_991, 1);
lean_inc(x_993);
if (lean_is_exclusive(x_991)) {
 lean_ctor_release(x_991, 0);
 lean_ctor_release(x_991, 1);
 x_994 = x_991;
} else {
 lean_dec_ref(x_991);
 x_994 = lean_box(0);
}
x_995 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__88;
lean_inc(x_986);
x_996 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_996, 0, x_986);
lean_ctor_set(x_996, 1, x_995);
x_997 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__97;
x_998 = l_Lean_addMacroScope(x_992, x_997, x_989);
x_999 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__96;
lean_inc(x_986);
x_1000 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_1000, 0, x_986);
lean_ctor_set(x_1000, 1, x_999);
lean_ctor_set(x_1000, 2, x_998);
lean_ctor_set(x_1000, 3, x_824);
x_1001 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__98;
lean_inc(x_986);
x_1002 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1002, 0, x_986);
lean_ctor_set(x_1002, 1, x_1001);
x_1003 = lean_mk_syntax_ident(x_1);
x_1004 = lean_array_push(x_847, x_63);
x_1005 = lean_array_push(x_1004, x_64);
x_1006 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1006, 0, x_845);
lean_ctor_set(x_1006, 1, x_1005);
x_1007 = lean_array_push(x_847, x_1003);
x_1008 = lean_array_push(x_1007, x_1006);
x_1009 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1009, 0, x_928);
lean_ctor_set(x_1009, 1, x_1008);
x_1010 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__99;
x_1011 = lean_array_push(x_1010, x_1000);
x_1012 = lean_array_push(x_1011, x_867);
x_1013 = lean_array_push(x_1012, x_867);
x_1014 = lean_array_push(x_1013, x_1002);
x_1015 = lean_array_push(x_1014, x_1009);
x_1016 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__93;
x_1017 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1017, 0, x_1016);
lean_ctor_set(x_1017, 1, x_1015);
x_1018 = lean_array_push(x_843, x_1017);
x_1019 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__91;
x_1020 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1020, 0, x_1019);
lean_ctor_set(x_1020, 1, x_1018);
x_1021 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1021, 0, x_986);
lean_ctor_set(x_1021, 1, x_852);
x_1022 = lean_array_push(x_843, x_1021);
x_1023 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1023, 0, x_845);
lean_ctor_set(x_1023, 1, x_1022);
x_1024 = lean_array_push(x_945, x_996);
x_1025 = lean_array_push(x_1024, x_1020);
x_1026 = lean_array_push(x_1025, x_1023);
x_1027 = lean_array_push(x_1026, x_982);
x_1028 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__89;
x_1029 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1029, 0, x_1028);
lean_ctor_set(x_1029, 1, x_1027);
if (lean_is_scalar(x_994)) {
 x_1030 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1030 = x_994;
}
lean_ctor_set(x_1030, 0, x_1029);
lean_ctor_set(x_1030, 1, x_993);
return x_1030;
}
}
}
}
}
lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_10;
}
}
lean_object* l_Lean_throwError___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_9 = lean_ctor_get(x_6, 3);
x_10 = lean_ctor_get(x_2, 3);
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
x_1 = lean_mk_string("'");
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
x_1 = lean_mk_string("' is not a constructor");
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
lean_object* l_Lean_getConstInfoCtor___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
x_19 = l_Lean_mkConst(x_1, x_18);
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
lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_1, 1);
x_13 = lean_nat_dec_le(x_12, x_3);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_eq(x_2, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_sub(x_2, x_16);
lean_dec(x_2);
x_18 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Deriving_mkInductiveApp___spec__2___rarg(x_9, x_10, x_11);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_6, x_7, x_8, x_9, x_10, x_20);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = l_Lean_Elab_Term_getMainModule___rarg(x_10, x_22);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__82;
x_26 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_26, 0, x_19);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__26;
x_28 = lean_array_push(x_27, x_26);
x_29 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__81;
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
x_31 = lean_array_push(x_4, x_30);
x_32 = lean_ctor_get(x_1, 2);
x_33 = lean_nat_add(x_3, x_32);
lean_dec(x_3);
x_2 = x_17;
x_3 = x_33;
x_4 = x_31;
x_11 = x_24;
goto _start;
}
else
{
lean_object* x_35; 
lean_dec(x_3);
lean_dec(x_2);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_4);
lean_ctor_set(x_35, 1, x_11);
return x_35;
}
}
else
{
lean_object* x_36; 
lean_dec(x_3);
lean_dec(x_2);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_4);
lean_ctor_set(x_36, 1, x_11);
return x_36;
}
}
}
lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_1, 1);
x_13 = lean_nat_dec_le(x_12, x_3);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_eq(x_2, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_sub(x_2, x_16);
lean_dec(x_2);
x_18 = lean_ctor_get(x_4, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_4, 1);
lean_inc(x_19);
lean_dec(x_4);
x_20 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Deriving_mkInductiveApp___spec__2___rarg(x_9, x_10, x_11);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_6, x_7, x_8, x_9, x_10, x_22);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = l_Lean_Elab_Term_getMainModule___rarg(x_10, x_24);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__82;
x_28 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_28, 0, x_21);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__26;
x_30 = lean_array_push(x_29, x_28);
x_31 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__81;
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
x_33 = lean_array_push(x_18, x_32);
x_34 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Deriving_mkInductiveApp___spec__2___rarg(x_9, x_10, x_26);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_6, x_7, x_8, x_9, x_10, x_36);
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
lean_dec(x_37);
x_39 = l_Lean_Elab_Term_getMainModule___rarg(x_10, x_38);
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec(x_39);
x_41 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_41, 0, x_35);
lean_ctor_set(x_41, 1, x_27);
x_42 = lean_array_push(x_29, x_41);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_31);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_array_push(x_19, x_43);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_33);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_ctor_get(x_1, 2);
x_47 = lean_nat_add(x_3, x_46);
lean_dec(x_3);
x_2 = x_17;
x_3 = x_47;
x_4 = x_45;
x_11 = x_40;
goto _start;
}
else
{
lean_object* x_49; 
lean_dec(x_3);
lean_dec(x_2);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_4);
lean_ctor_set(x_49, 1, x_11);
return x_49;
}
}
else
{
lean_object* x_50; 
lean_dec(x_3);
lean_dec(x_2);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_4);
lean_ctor_set(x_50, 1, x_11);
return x_50;
}
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("a");
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__5___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__5___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__5___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("b");
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__5___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__5___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_5, 1);
x_17 = lean_nat_dec_le(x_16, x_7);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_nat_dec_eq(x_6, x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_sub(x_6, x_20);
lean_dec(x_6);
x_29 = lean_ctor_get(x_8, 1);
lean_inc(x_29);
x_30 = lean_ctor_get(x_8, 0);
lean_inc(x_30);
lean_dec(x_8);
x_31 = !lean_is_exclusive(x_29);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_32 = lean_ctor_get(x_29, 0);
x_33 = lean_ctor_get(x_29, 1);
x_34 = lean_nat_add(x_4, x_7);
x_35 = l_Lean_instInhabitedExpr;
x_36 = lean_array_get(x_35, x_2, x_34);
lean_dec(x_34);
x_37 = l_Lean_Expr_fvarId_x21(x_36);
x_38 = l_Lean_Expr_hasAnyFVar_visit___at_Lean_Expr_containsFVar___spec__1(x_37, x_3);
lean_dec(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_39 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__5___closed__2;
x_40 = l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(x_39, x_13, x_14, x_15);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_mk_syntax_ident(x_41);
x_44 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__5___closed__4;
x_45 = l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(x_44, x_13, x_14, x_42);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = lean_mk_syntax_ident(x_46);
lean_inc(x_43);
x_49 = lean_array_push(x_30, x_43);
lean_inc(x_48);
x_50 = lean_array_push(x_32, x_48);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_51 = l_Lean_Meta_inferType(x_36, x_11, x_12, x_13, x_14, x_47);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = lean_ctor_get(x_1, 0);
x_55 = lean_ctor_get(x_54, 0);
x_56 = l_Lean_Expr_isAppOf(x_52, x_55);
lean_dec(x_52);
x_57 = lean_box(x_56);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_48);
lean_ctor_set(x_58, 1, x_57);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_43);
lean_ctor_set(x_59, 1, x_58);
x_60 = lean_array_push(x_33, x_59);
lean_ctor_set(x_29, 1, x_60);
lean_ctor_set(x_29, 0, x_50);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_49);
lean_ctor_set(x_61, 1, x_29);
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_61);
x_22 = x_62;
x_23 = x_53;
goto block_28;
}
else
{
uint8_t x_63; 
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_43);
lean_free_object(x_29);
lean_dec(x_33);
lean_dec(x_21);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_7);
x_63 = !lean_is_exclusive(x_51);
if (x_63 == 0)
{
return x_51;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_51, 0);
x_65 = lean_ctor_get(x_51, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_51);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec(x_36);
x_67 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Deriving_mkInductiveApp___spec__2___rarg(x_13, x_14, x_15);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_70 = l_Lean_Elab_Term_getCurrMacroScope(x_9, x_10, x_11, x_12, x_13, x_14, x_69);
x_71 = lean_ctor_get(x_70, 1);
lean_inc(x_71);
lean_dec(x_70);
x_72 = l_Lean_Elab_Term_getMainModule___rarg(x_14, x_71);
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
lean_dec(x_72);
x_74 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__82;
x_75 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_75, 0, x_68);
lean_ctor_set(x_75, 1, x_74);
x_76 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__26;
x_77 = lean_array_push(x_76, x_75);
x_78 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__81;
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_77);
x_80 = lean_array_push(x_30, x_79);
x_81 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Deriving_mkInductiveApp___spec__2___rarg(x_13, x_14, x_73);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
x_84 = l_Lean_Elab_Term_getCurrMacroScope(x_9, x_10, x_11, x_12, x_13, x_14, x_83);
x_85 = lean_ctor_get(x_84, 1);
lean_inc(x_85);
lean_dec(x_84);
x_86 = l_Lean_Elab_Term_getMainModule___rarg(x_14, x_85);
x_87 = lean_ctor_get(x_86, 1);
lean_inc(x_87);
lean_dec(x_86);
x_88 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_88, 0, x_82);
lean_ctor_set(x_88, 1, x_74);
x_89 = lean_array_push(x_76, x_88);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_78);
lean_ctor_set(x_90, 1, x_89);
x_91 = lean_array_push(x_32, x_90);
lean_ctor_set(x_29, 0, x_91);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_80);
lean_ctor_set(x_92, 1, x_29);
x_93 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_93, 0, x_92);
x_22 = x_93;
x_23 = x_87;
goto block_28;
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; 
x_94 = lean_ctor_get(x_29, 0);
x_95 = lean_ctor_get(x_29, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_29);
x_96 = lean_nat_add(x_4, x_7);
x_97 = l_Lean_instInhabitedExpr;
x_98 = lean_array_get(x_97, x_2, x_96);
lean_dec(x_96);
x_99 = l_Lean_Expr_fvarId_x21(x_98);
x_100 = l_Lean_Expr_hasAnyFVar_visit___at_Lean_Expr_containsFVar___spec__1(x_99, x_3);
lean_dec(x_99);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_101 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__5___closed__2;
x_102 = l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(x_101, x_13, x_14, x_15);
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_102, 1);
lean_inc(x_104);
lean_dec(x_102);
x_105 = lean_mk_syntax_ident(x_103);
x_106 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__5___closed__4;
x_107 = l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(x_106, x_13, x_14, x_104);
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
lean_dec(x_107);
x_110 = lean_mk_syntax_ident(x_108);
lean_inc(x_105);
x_111 = lean_array_push(x_30, x_105);
lean_inc(x_110);
x_112 = lean_array_push(x_94, x_110);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_113 = l_Lean_Meta_inferType(x_98, x_11, x_12, x_13, x_14, x_109);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; uint8_t x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_113, 1);
lean_inc(x_115);
lean_dec(x_113);
x_116 = lean_ctor_get(x_1, 0);
x_117 = lean_ctor_get(x_116, 0);
x_118 = l_Lean_Expr_isAppOf(x_114, x_117);
lean_dec(x_114);
x_119 = lean_box(x_118);
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_110);
lean_ctor_set(x_120, 1, x_119);
x_121 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_121, 0, x_105);
lean_ctor_set(x_121, 1, x_120);
x_122 = lean_array_push(x_95, x_121);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_112);
lean_ctor_set(x_123, 1, x_122);
x_124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_124, 0, x_111);
lean_ctor_set(x_124, 1, x_123);
x_125 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_125, 0, x_124);
x_22 = x_125;
x_23 = x_115;
goto block_28;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
lean_dec(x_112);
lean_dec(x_111);
lean_dec(x_110);
lean_dec(x_105);
lean_dec(x_95);
lean_dec(x_21);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_7);
x_126 = lean_ctor_get(x_113, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_113, 1);
lean_inc(x_127);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 lean_ctor_release(x_113, 1);
 x_128 = x_113;
} else {
 lean_dec_ref(x_113);
 x_128 = lean_box(0);
}
if (lean_is_scalar(x_128)) {
 x_129 = lean_alloc_ctor(1, 2, 0);
} else {
 x_129 = x_128;
}
lean_ctor_set(x_129, 0, x_126);
lean_ctor_set(x_129, 1, x_127);
return x_129;
}
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
lean_dec(x_98);
x_130 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Deriving_mkInductiveApp___spec__2___rarg(x_13, x_14, x_15);
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_130, 1);
lean_inc(x_132);
lean_dec(x_130);
x_133 = l_Lean_Elab_Term_getCurrMacroScope(x_9, x_10, x_11, x_12, x_13, x_14, x_132);
x_134 = lean_ctor_get(x_133, 1);
lean_inc(x_134);
lean_dec(x_133);
x_135 = l_Lean_Elab_Term_getMainModule___rarg(x_14, x_134);
x_136 = lean_ctor_get(x_135, 1);
lean_inc(x_136);
lean_dec(x_135);
x_137 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__82;
x_138 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_138, 0, x_131);
lean_ctor_set(x_138, 1, x_137);
x_139 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__26;
x_140 = lean_array_push(x_139, x_138);
x_141 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__81;
x_142 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_140);
x_143 = lean_array_push(x_30, x_142);
x_144 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Deriving_mkInductiveApp___spec__2___rarg(x_13, x_14, x_136);
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_144, 1);
lean_inc(x_146);
lean_dec(x_144);
x_147 = l_Lean_Elab_Term_getCurrMacroScope(x_9, x_10, x_11, x_12, x_13, x_14, x_146);
x_148 = lean_ctor_get(x_147, 1);
lean_inc(x_148);
lean_dec(x_147);
x_149 = l_Lean_Elab_Term_getMainModule___rarg(x_14, x_148);
x_150 = lean_ctor_get(x_149, 1);
lean_inc(x_150);
lean_dec(x_149);
x_151 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_151, 0, x_145);
lean_ctor_set(x_151, 1, x_137);
x_152 = lean_array_push(x_139, x_151);
x_153 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_153, 0, x_141);
lean_ctor_set(x_153, 1, x_152);
x_154 = lean_array_push(x_94, x_153);
x_155 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_155, 0, x_154);
lean_ctor_set(x_155, 1, x_95);
x_156 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_156, 0, x_143);
lean_ctor_set(x_156, 1, x_155);
x_157 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_157, 0, x_156);
x_22 = x_157;
x_23 = x_150;
goto block_28;
}
}
block_28:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_ctor_get(x_5, 2);
x_26 = lean_nat_add(x_7, x_25);
lean_dec(x_7);
x_6 = x_21;
x_7 = x_26;
x_8 = x_24;
x_15 = x_23;
goto _start;
}
}
else
{
lean_object* x_158; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
x_158 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_158, 0, x_8);
lean_ctor_set(x_158, 1, x_15);
return x_158;
}
}
else
{
lean_object* x_159; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
x_159 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_159, 0, x_8);
lean_ctor_set(x_159, 1, x_15);
return x_159;
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
x_1 = lean_mk_string("explicit");
return x_1;
}
}
static lean_object* _init_l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__6;
x_2 = l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("@");
return x_1;
}
}
static lean_object* _init_l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("matchAlt");
return x_1;
}
}
static lean_object* _init_l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__6;
x_2 = l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1___closed__6;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("|");
return x_1;
}
}
static lean_object* _init_l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(",");
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
x_1 = lean_mk_string("=>");
return x_1;
}
}
lean_object* l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1___closed__1;
x_18 = l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1___closed__2;
lean_inc(x_15);
lean_inc(x_14);
x_19 = l_Lean_Core_transform___at_Lean_Core_betaReduce___spec__1(x_9, x_17, x_18, x_14, x_15, x_16);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_unsigned_to_nat(1u);
lean_inc(x_1);
x_24 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_1);
lean_ctor_set(x_24, 2, x_23);
lean_inc_n(x_2, 2);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_2);
lean_ctor_set(x_25, 1, x_2);
lean_inc(x_1);
x_26 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__4(x_24, x_1, x_22, x_25, x_10, x_11, x_12, x_13, x_14, x_15, x_21);
lean_dec(x_24);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = !lean_is_exclusive(x_27);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_30 = lean_ctor_get(x_27, 0);
x_31 = lean_ctor_get(x_27, 1);
x_32 = lean_ctor_get(x_3, 4);
lean_inc(x_32);
lean_dec(x_3);
lean_inc(x_32);
x_33 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_33, 0, x_22);
lean_ctor_set(x_33, 1, x_32);
lean_ctor_set(x_33, 2, x_23);
x_34 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__57;
lean_ctor_set(x_27, 1, x_34);
lean_ctor_set(x_27, 0, x_31);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_30);
lean_ctor_set(x_35, 1, x_27);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_36 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__5(x_4, x_8, x_20, x_1, x_33, x_32, x_22, x_35, x_10, x_11, x_12, x_13, x_14, x_15, x_28);
lean_dec(x_33);
lean_dec(x_1);
lean_dec(x_20);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; 
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
x_43 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Deriving_mkInductiveApp___spec__2___rarg(x_14, x_15, x_39);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = l_Lean_Elab_Term_getCurrMacroScope(x_10, x_11, x_12, x_13, x_14, x_15, x_45);
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
lean_dec(x_46);
x_48 = l_Lean_Elab_Term_getMainModule___rarg(x_15, x_47);
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
lean_dec(x_48);
x_50 = l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1___closed__5;
x_51 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_51, 0, x_44);
lean_ctor_set(x_51, 1, x_50);
x_52 = lean_mk_syntax_ident(x_5);
x_53 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__27;
x_54 = lean_array_push(x_53, x_51);
lean_inc(x_52);
x_55 = lean_array_push(x_54, x_52);
x_56 = l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1___closed__4;
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_55);
lean_inc(x_2);
x_58 = l_Array_append___rarg(x_2, x_40);
lean_dec(x_40);
x_59 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__19;
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_58);
x_61 = lean_array_push(x_53, x_57);
x_62 = lean_array_push(x_61, x_60);
x_63 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__8;
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_62);
x_65 = lean_array_push(x_6, x_64);
x_66 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Deriving_mkInductiveApp___spec__2___rarg(x_14, x_15, x_49);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = l_Lean_Elab_Term_getCurrMacroScope(x_10, x_11, x_12, x_13, x_14, x_15, x_68);
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
lean_dec(x_69);
x_71 = l_Lean_Elab_Term_getMainModule___rarg(x_15, x_70);
x_72 = lean_ctor_get(x_71, 1);
lean_inc(x_72);
lean_dec(x_71);
x_73 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_73, 0, x_67);
lean_ctor_set(x_73, 1, x_50);
x_74 = lean_array_push(x_53, x_73);
x_75 = lean_array_push(x_74, x_52);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_56);
lean_ctor_set(x_76, 1, x_75);
lean_inc(x_2);
x_77 = l_Array_append___rarg(x_2, x_41);
lean_dec(x_41);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_59);
lean_ctor_set(x_78, 1, x_77);
x_79 = lean_array_push(x_53, x_76);
x_80 = lean_array_push(x_79, x_78);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_63);
lean_ctor_set(x_81, 1, x_80);
x_82 = lean_array_push(x_65, x_81);
x_83 = lean_array_to_list(lean_box(0), x_42);
lean_inc(x_10);
x_84 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs(x_7, x_83, x_10, x_11, x_12, x_13, x_14, x_15, x_72);
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
x_87 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Deriving_mkInductiveApp___spec__2___rarg(x_14, x_15, x_86);
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
lean_dec(x_87);
x_90 = l_Lean_Elab_Term_getCurrMacroScope(x_10, x_11, x_12, x_13, x_14, x_15, x_89);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
x_91 = lean_ctor_get(x_90, 1);
lean_inc(x_91);
lean_dec(x_90);
x_92 = l_Lean_Elab_Term_getMainModule___rarg(x_15, x_91);
lean_dec(x_15);
x_93 = !lean_is_exclusive(x_92);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; size_t x_98; size_t x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_94 = lean_ctor_get(x_92, 0);
lean_dec(x_94);
x_95 = l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1___closed__8;
lean_inc(x_88);
x_96 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_96, 0, x_88);
lean_ctor_set(x_96, 1, x_95);
x_97 = lean_array_get_size(x_82);
x_98 = lean_usize_of_nat(x_97);
lean_dec(x_97);
x_99 = 0;
x_100 = x_82;
x_101 = l_Array_mapMUnsafe_map___at_myMacro____x40_Init_NotationExtra___hyg_4440____spec__3(x_98, x_99, x_100);
x_102 = x_101;
x_103 = l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1___closed__10;
x_104 = l_Lean_mkSepArray(x_102, x_103);
lean_dec(x_102);
x_105 = l_Array_append___rarg(x_2, x_104);
lean_dec(x_104);
x_106 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_106, 0, x_59);
lean_ctor_set(x_106, 1, x_105);
x_107 = l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1___closed__11;
x_108 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_108, 0, x_88);
lean_ctor_set(x_108, 1, x_107);
x_109 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__85;
x_110 = lean_array_push(x_109, x_96);
x_111 = lean_array_push(x_110, x_106);
x_112 = lean_array_push(x_111, x_108);
x_113 = lean_array_push(x_112, x_85);
x_114 = l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1___closed__7;
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_113);
lean_ctor_set(x_92, 0, x_115);
return x_92;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; size_t x_120; size_t x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_116 = lean_ctor_get(x_92, 1);
lean_inc(x_116);
lean_dec(x_92);
x_117 = l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1___closed__8;
lean_inc(x_88);
x_118 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_118, 0, x_88);
lean_ctor_set(x_118, 1, x_117);
x_119 = lean_array_get_size(x_82);
x_120 = lean_usize_of_nat(x_119);
lean_dec(x_119);
x_121 = 0;
x_122 = x_82;
x_123 = l_Array_mapMUnsafe_map___at_myMacro____x40_Init_NotationExtra___hyg_4440____spec__3(x_120, x_121, x_122);
x_124 = x_123;
x_125 = l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1___closed__10;
x_126 = l_Lean_mkSepArray(x_124, x_125);
lean_dec(x_124);
x_127 = l_Array_append___rarg(x_2, x_126);
lean_dec(x_126);
x_128 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_128, 0, x_59);
lean_ctor_set(x_128, 1, x_127);
x_129 = l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1___closed__11;
x_130 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_130, 0, x_88);
lean_ctor_set(x_130, 1, x_129);
x_131 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__85;
x_132 = lean_array_push(x_131, x_118);
x_133 = lean_array_push(x_132, x_128);
x_134 = lean_array_push(x_133, x_130);
x_135 = lean_array_push(x_134, x_85);
x_136 = l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1___closed__7;
x_137 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_135);
x_138 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_138, 0, x_137);
lean_ctor_set(x_138, 1, x_116);
return x_138;
}
}
else
{
uint8_t x_139; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_139 = !lean_is_exclusive(x_36);
if (x_139 == 0)
{
return x_36;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_140 = lean_ctor_get(x_36, 0);
x_141 = lean_ctor_get(x_36, 1);
lean_inc(x_141);
lean_inc(x_140);
lean_dec(x_36);
x_142 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_142, 0, x_140);
lean_ctor_set(x_142, 1, x_141);
return x_142;
}
}
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_143 = lean_ctor_get(x_27, 0);
x_144 = lean_ctor_get(x_27, 1);
lean_inc(x_144);
lean_inc(x_143);
lean_dec(x_27);
x_145 = lean_ctor_get(x_3, 4);
lean_inc(x_145);
lean_dec(x_3);
lean_inc(x_145);
x_146 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_146, 0, x_22);
lean_ctor_set(x_146, 1, x_145);
lean_ctor_set(x_146, 2, x_23);
x_147 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__57;
x_148 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_148, 0, x_144);
lean_ctor_set(x_148, 1, x_147);
x_149 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_149, 0, x_143);
lean_ctor_set(x_149, 1, x_148);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_150 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__5(x_4, x_8, x_20, x_1, x_146, x_145, x_22, x_149, x_10, x_11, x_12, x_13, x_14, x_15, x_28);
lean_dec(x_146);
lean_dec(x_1);
lean_dec(x_20);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; size_t x_212; size_t x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; 
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_151, 1);
lean_inc(x_152);
x_153 = lean_ctor_get(x_150, 1);
lean_inc(x_153);
lean_dec(x_150);
x_154 = lean_ctor_get(x_151, 0);
lean_inc(x_154);
lean_dec(x_151);
x_155 = lean_ctor_get(x_152, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_152, 1);
lean_inc(x_156);
lean_dec(x_152);
x_157 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Deriving_mkInductiveApp___spec__2___rarg(x_14, x_15, x_153);
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_157, 1);
lean_inc(x_159);
lean_dec(x_157);
x_160 = l_Lean_Elab_Term_getCurrMacroScope(x_10, x_11, x_12, x_13, x_14, x_15, x_159);
x_161 = lean_ctor_get(x_160, 1);
lean_inc(x_161);
lean_dec(x_160);
x_162 = l_Lean_Elab_Term_getMainModule___rarg(x_15, x_161);
x_163 = lean_ctor_get(x_162, 1);
lean_inc(x_163);
lean_dec(x_162);
x_164 = l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1___closed__5;
x_165 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_165, 0, x_158);
lean_ctor_set(x_165, 1, x_164);
x_166 = lean_mk_syntax_ident(x_5);
x_167 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__27;
x_168 = lean_array_push(x_167, x_165);
lean_inc(x_166);
x_169 = lean_array_push(x_168, x_166);
x_170 = l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1___closed__4;
x_171 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_171, 1, x_169);
lean_inc(x_2);
x_172 = l_Array_append___rarg(x_2, x_154);
lean_dec(x_154);
x_173 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__19;
x_174 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_174, 0, x_173);
lean_ctor_set(x_174, 1, x_172);
x_175 = lean_array_push(x_167, x_171);
x_176 = lean_array_push(x_175, x_174);
x_177 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__8;
x_178 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_178, 0, x_177);
lean_ctor_set(x_178, 1, x_176);
x_179 = lean_array_push(x_6, x_178);
x_180 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Deriving_mkInductiveApp___spec__2___rarg(x_14, x_15, x_163);
x_181 = lean_ctor_get(x_180, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_180, 1);
lean_inc(x_182);
lean_dec(x_180);
x_183 = l_Lean_Elab_Term_getCurrMacroScope(x_10, x_11, x_12, x_13, x_14, x_15, x_182);
x_184 = lean_ctor_get(x_183, 1);
lean_inc(x_184);
lean_dec(x_183);
x_185 = l_Lean_Elab_Term_getMainModule___rarg(x_15, x_184);
x_186 = lean_ctor_get(x_185, 1);
lean_inc(x_186);
lean_dec(x_185);
x_187 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_187, 0, x_181);
lean_ctor_set(x_187, 1, x_164);
x_188 = lean_array_push(x_167, x_187);
x_189 = lean_array_push(x_188, x_166);
x_190 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_190, 0, x_170);
lean_ctor_set(x_190, 1, x_189);
lean_inc(x_2);
x_191 = l_Array_append___rarg(x_2, x_155);
lean_dec(x_155);
x_192 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_192, 0, x_173);
lean_ctor_set(x_192, 1, x_191);
x_193 = lean_array_push(x_167, x_190);
x_194 = lean_array_push(x_193, x_192);
x_195 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_195, 0, x_177);
lean_ctor_set(x_195, 1, x_194);
x_196 = lean_array_push(x_179, x_195);
x_197 = lean_array_to_list(lean_box(0), x_156);
lean_inc(x_10);
x_198 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs(x_7, x_197, x_10, x_11, x_12, x_13, x_14, x_15, x_186);
x_199 = lean_ctor_get(x_198, 0);
lean_inc(x_199);
x_200 = lean_ctor_get(x_198, 1);
lean_inc(x_200);
lean_dec(x_198);
x_201 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Deriving_mkInductiveApp___spec__2___rarg(x_14, x_15, x_200);
x_202 = lean_ctor_get(x_201, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_201, 1);
lean_inc(x_203);
lean_dec(x_201);
x_204 = l_Lean_Elab_Term_getCurrMacroScope(x_10, x_11, x_12, x_13, x_14, x_15, x_203);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
x_205 = lean_ctor_get(x_204, 1);
lean_inc(x_205);
lean_dec(x_204);
x_206 = l_Lean_Elab_Term_getMainModule___rarg(x_15, x_205);
lean_dec(x_15);
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
x_209 = l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1___closed__8;
lean_inc(x_202);
x_210 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_210, 0, x_202);
lean_ctor_set(x_210, 1, x_209);
x_211 = lean_array_get_size(x_196);
x_212 = lean_usize_of_nat(x_211);
lean_dec(x_211);
x_213 = 0;
x_214 = x_196;
x_215 = l_Array_mapMUnsafe_map___at_myMacro____x40_Init_NotationExtra___hyg_4440____spec__3(x_212, x_213, x_214);
x_216 = x_215;
x_217 = l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1___closed__10;
x_218 = l_Lean_mkSepArray(x_216, x_217);
lean_dec(x_216);
x_219 = l_Array_append___rarg(x_2, x_218);
lean_dec(x_218);
x_220 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_220, 0, x_173);
lean_ctor_set(x_220, 1, x_219);
x_221 = l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1___closed__11;
x_222 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_222, 0, x_202);
lean_ctor_set(x_222, 1, x_221);
x_223 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__85;
x_224 = lean_array_push(x_223, x_210);
x_225 = lean_array_push(x_224, x_220);
x_226 = lean_array_push(x_225, x_222);
x_227 = lean_array_push(x_226, x_199);
x_228 = l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1___closed__7;
x_229 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_229, 0, x_228);
lean_ctor_set(x_229, 1, x_227);
if (lean_is_scalar(x_208)) {
 x_230 = lean_alloc_ctor(0, 2, 0);
} else {
 x_230 = x_208;
}
lean_ctor_set(x_230, 0, x_229);
lean_ctor_set(x_230, 1, x_207);
return x_230;
}
else
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_231 = lean_ctor_get(x_150, 0);
lean_inc(x_231);
x_232 = lean_ctor_get(x_150, 1);
lean_inc(x_232);
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 lean_ctor_release(x_150, 1);
 x_233 = x_150;
} else {
 lean_dec_ref(x_150);
 x_233 = lean_box(0);
}
if (lean_is_scalar(x_233)) {
 x_234 = lean_alloc_ctor(1, 2, 0);
} else {
 x_234 = x_233;
}
lean_ctor_set(x_234, 0, x_231);
lean_ctor_set(x_234, 1, x_232);
return x_234;
}
}
}
else
{
uint8_t x_235; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_235 = !lean_is_exclusive(x_19);
if (x_235 == 0)
{
return x_19;
}
else
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; 
x_236 = lean_ctor_get(x_19, 0);
x_237 = lean_ctor_get(x_19, 1);
lean_inc(x_237);
lean_inc(x_236);
lean_dec(x_19);
x_238 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_238, 0, x_236);
lean_ctor_set(x_238, 1, x_237);
return x_238;
}
}
}
}
static lean_object* _init_l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ellipsis");
return x_1;
}
}
static lean_object* _init_l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__6;
x_2 = l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("..");
return x_1;
}
}
static lean_object* _init_l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__64;
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
lean_object* l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_15; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_16 = lean_ctor_get(x_6, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_6, 1);
lean_inc(x_17);
lean_dec(x_6);
x_23 = lean_ctor_get(x_1, 1);
lean_inc(x_23);
x_24 = lean_ctor_get(x_1, 2);
lean_inc(x_24);
x_25 = lean_unsigned_to_nat(0u);
x_26 = lean_unsigned_to_nat(1u);
lean_inc(x_24);
x_27 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_24);
lean_ctor_set(x_27, 2, x_26);
lean_inc(x_3);
x_28 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__3(x_27, x_24, x_25, x_3, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_27);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_name_eq(x_4, x_16);
if (x_31 == 0)
{
lean_object* x_32; 
lean_dec(x_23);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_16);
lean_inc(x_4);
x_32 = l_Lean_Meta_compatibleCtors(x_4, x_16, x_10, x_11, x_12, x_13, x_30);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_unbox(x_33);
lean_dec(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_29);
lean_dec(x_16);
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
lean_dec(x_32);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_7);
x_18 = x_36;
x_19 = x_35;
goto block_22;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; size_t x_168; size_t x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_37 = lean_ctor_get(x_32, 1);
lean_inc(x_37);
lean_dec(x_32);
x_38 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Deriving_mkInductiveApp___spec__2___rarg(x_12, x_13, x_37);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = l_Lean_Elab_Term_getCurrMacroScope(x_8, x_9, x_10, x_11, x_12, x_13, x_40);
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
lean_dec(x_41);
x_43 = l_Lean_Elab_Term_getMainModule___rarg(x_13, x_42);
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
lean_dec(x_43);
lean_inc(x_4);
x_45 = lean_mk_syntax_ident(x_4);
x_46 = l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___closed__3;
x_47 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_47, 0, x_39);
lean_ctor_set(x_47, 1, x_46);
x_48 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__26;
x_49 = lean_array_push(x_48, x_47);
x_50 = l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___closed__2;
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_49);
x_52 = lean_array_push(x_48, x_51);
x_53 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__19;
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_52);
x_55 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__27;
x_56 = lean_array_push(x_55, x_45);
x_57 = lean_array_push(x_56, x_54);
x_58 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__8;
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_57);
x_60 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Deriving_mkInductiveApp___spec__2___rarg(x_12, x_13, x_44);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_63 = l_Lean_Elab_Term_getCurrMacroScope(x_8, x_9, x_10, x_11, x_12, x_13, x_62);
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
lean_dec(x_63);
x_65 = l_Lean_Elab_Term_getMainModule___rarg(x_13, x_64);
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
lean_dec(x_65);
x_67 = lean_mk_syntax_ident(x_16);
x_68 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_68, 0, x_61);
lean_ctor_set(x_68, 1, x_46);
x_69 = lean_array_push(x_48, x_68);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_50);
lean_ctor_set(x_70, 1, x_69);
x_71 = lean_array_push(x_48, x_70);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_53);
lean_ctor_set(x_72, 1, x_71);
x_73 = lean_array_push(x_55, x_67);
x_74 = lean_array_push(x_73, x_72);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_58);
lean_ctor_set(x_75, 1, x_74);
x_76 = lean_array_push(x_55, x_59);
x_77 = lean_array_push(x_76, x_75);
x_78 = l_Array_append___rarg(x_29, x_77);
lean_dec(x_77);
x_79 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Deriving_mkInductiveApp___spec__2___rarg(x_12, x_13, x_66);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec(x_79);
x_82 = l_Lean_Elab_Term_getCurrMacroScope(x_8, x_9, x_10, x_11, x_12, x_13, x_81);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
x_85 = l_Lean_Elab_Term_getMainModule___rarg(x_13, x_84);
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
lean_dec(x_85);
x_88 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__63;
lean_inc(x_83);
lean_inc(x_86);
x_89 = l_Lean_addMacroScope(x_86, x_88, x_83);
x_90 = lean_box(0);
x_91 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__62;
x_92 = l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___closed__5;
lean_inc(x_80);
x_93 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_93, 0, x_80);
lean_ctor_set(x_93, 1, x_91);
lean_ctor_set(x_93, 2, x_89);
lean_ctor_set(x_93, 3, x_92);
x_94 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__69;
lean_inc(x_80);
x_95 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_95, 0, x_80);
lean_ctor_set(x_95, 1, x_94);
x_96 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__43;
lean_inc(x_80);
x_97 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_97, 0, x_80);
lean_ctor_set(x_97, 1, x_96);
x_98 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__70;
lean_inc(x_80);
x_99 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_99, 0, x_80);
lean_ctor_set(x_99, 1, x_98);
x_100 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__34;
x_101 = l_Lean_addMacroScope(x_86, x_100, x_83);
x_102 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__33;
lean_inc(x_80);
x_103 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_103, 0, x_80);
lean_ctor_set(x_103, 1, x_102);
lean_ctor_set(x_103, 2, x_101);
lean_ctor_set(x_103, 3, x_90);
lean_inc(x_103);
x_104 = lean_array_push(x_48, x_103);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_53);
lean_ctor_set(x_105, 1, x_104);
x_106 = lean_array_push(x_55, x_99);
x_107 = lean_array_push(x_106, x_105);
x_108 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__71;
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_107);
x_110 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__54;
lean_inc(x_80);
x_111 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_111, 0, x_80);
lean_ctor_set(x_111, 1, x_110);
x_112 = lean_array_push(x_48, x_111);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_53);
lean_ctor_set(x_113, 1, x_112);
x_114 = lean_array_push(x_55, x_109);
x_115 = lean_array_push(x_114, x_113);
x_116 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__51;
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_115);
x_118 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__76;
lean_inc(x_80);
x_119 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_119, 0, x_80);
lean_ctor_set(x_119, 1, x_118);
lean_inc(x_3);
x_120 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_120, 0, x_53);
lean_ctor_set(x_120, 1, x_3);
x_121 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__39;
x_122 = lean_array_push(x_121, x_119);
x_123 = lean_array_push(x_122, x_103);
lean_inc(x_120);
x_124 = lean_array_push(x_123, x_120);
x_125 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__77;
x_126 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set(x_126, 1, x_124);
x_127 = lean_array_push(x_55, x_126);
lean_inc(x_120);
x_128 = lean_array_push(x_127, x_120);
x_129 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_129, 0, x_116);
lean_ctor_set(x_129, 1, x_128);
x_130 = lean_array_push(x_55, x_117);
x_131 = lean_array_push(x_130, x_129);
x_132 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_132, 0, x_53);
lean_ctor_set(x_132, 1, x_131);
x_133 = lean_array_push(x_48, x_132);
x_134 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__49;
x_135 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_133);
x_136 = lean_array_push(x_48, x_135);
x_137 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__47;
x_138 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_138, 0, x_137);
lean_ctor_set(x_138, 1, x_136);
x_139 = lean_array_push(x_55, x_97);
x_140 = lean_array_push(x_139, x_138);
x_141 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__42;
x_142 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_140);
x_143 = lean_array_push(x_55, x_142);
x_144 = lean_array_push(x_143, x_120);
x_145 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_145, 0, x_53);
lean_ctor_set(x_145, 1, x_144);
x_146 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__86;
x_147 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_147, 0, x_80);
lean_ctor_set(x_147, 1, x_146);
x_148 = lean_array_push(x_121, x_95);
x_149 = lean_array_push(x_148, x_145);
x_150 = lean_array_push(x_149, x_147);
x_151 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__68;
x_152 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_152, 0, x_151);
lean_ctor_set(x_152, 1, x_150);
x_153 = lean_array_push(x_48, x_152);
x_154 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_154, 0, x_53);
lean_ctor_set(x_154, 1, x_153);
x_155 = lean_array_push(x_55, x_93);
x_156 = lean_array_push(x_155, x_154);
x_157 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_157, 0, x_58);
lean_ctor_set(x_157, 1, x_156);
x_158 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Deriving_mkInductiveApp___spec__2___rarg(x_12, x_13, x_87);
x_159 = lean_ctor_get(x_158, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_158, 1);
lean_inc(x_160);
lean_dec(x_158);
x_161 = l_Lean_Elab_Term_getCurrMacroScope(x_8, x_9, x_10, x_11, x_12, x_13, x_160);
x_162 = lean_ctor_get(x_161, 1);
lean_inc(x_162);
lean_dec(x_161);
x_163 = l_Lean_Elab_Term_getMainModule___rarg(x_13, x_162);
x_164 = lean_ctor_get(x_163, 1);
lean_inc(x_164);
lean_dec(x_163);
x_165 = l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1___closed__8;
lean_inc(x_159);
x_166 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_166, 0, x_159);
lean_ctor_set(x_166, 1, x_165);
x_167 = lean_array_get_size(x_78);
x_168 = lean_usize_of_nat(x_167);
lean_dec(x_167);
x_169 = 0;
x_170 = x_78;
x_171 = l_Array_mapMUnsafe_map___at_myMacro____x40_Init_NotationExtra___hyg_4440____spec__3(x_168, x_169, x_170);
x_172 = x_171;
x_173 = l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1___closed__10;
x_174 = l_Lean_mkSepArray(x_172, x_173);
lean_dec(x_172);
lean_inc(x_3);
x_175 = l_Array_append___rarg(x_3, x_174);
lean_dec(x_174);
x_176 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_176, 0, x_53);
lean_ctor_set(x_176, 1, x_175);
x_177 = l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1___closed__11;
x_178 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_178, 0, x_159);
lean_ctor_set(x_178, 1, x_177);
x_179 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__85;
x_180 = lean_array_push(x_179, x_166);
x_181 = lean_array_push(x_180, x_176);
x_182 = lean_array_push(x_181, x_178);
x_183 = lean_array_push(x_182, x_157);
x_184 = l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1___closed__7;
x_185 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_185, 0, x_184);
lean_ctor_set(x_185, 1, x_183);
x_186 = lean_array_push(x_7, x_185);
x_187 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_187, 0, x_186);
x_18 = x_187;
x_19 = x_164;
goto block_22;
}
}
else
{
uint8_t x_188; 
lean_dec(x_29);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_188 = !lean_is_exclusive(x_32);
if (x_188 == 0)
{
return x_32;
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_189 = lean_ctor_get(x_32, 0);
x_190 = lean_ctor_get(x_32, 1);
lean_inc(x_190);
lean_inc(x_189);
lean_dec(x_32);
x_191 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_191, 0, x_189);
lean_ctor_set(x_191, 1, x_190);
return x_191;
}
}
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
lean_dec(x_16);
x_192 = lean_ctor_get(x_5, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_192, 2);
lean_inc(x_193);
lean_dec(x_192);
lean_inc(x_2);
lean_inc(x_4);
lean_inc(x_1);
lean_inc(x_5);
lean_inc(x_3);
x_194 = lean_alloc_closure((void*)(l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1___boxed), 16, 7);
lean_closure_set(x_194, 0, x_23);
lean_closure_set(x_194, 1, x_3);
lean_closure_set(x_194, 2, x_5);
lean_closure_set(x_194, 3, x_1);
lean_closure_set(x_194, 4, x_4);
lean_closure_set(x_194, 5, x_29);
lean_closure_set(x_194, 6, x_2);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_195 = l_Lean_Meta_forallTelescopeReducing___at_Lean_Elab_Deriving_mkInductArgNames___spec__2___rarg(x_193, x_194, x_8, x_9, x_10, x_11, x_12, x_13, x_30);
if (lean_obj_tag(x_195) == 0)
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_196 = lean_ctor_get(x_195, 0);
lean_inc(x_196);
x_197 = lean_ctor_get(x_195, 1);
lean_inc(x_197);
lean_dec(x_195);
x_198 = lean_array_push(x_7, x_196);
x_199 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_199, 0, x_198);
x_18 = x_199;
x_19 = x_197;
goto block_22;
}
else
{
uint8_t x_200; 
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_200 = !lean_is_exclusive(x_195);
if (x_200 == 0)
{
return x_195;
}
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_201 = lean_ctor_get(x_195, 0);
x_202 = lean_ctor_get(x_195, 1);
lean_inc(x_202);
lean_inc(x_201);
lean_dec(x_195);
x_203 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_203, 0, x_201);
lean_ctor_set(x_203, 1, x_202);
return x_203;
}
}
}
block_22:
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec(x_18);
x_6 = x_17;
x_7 = x_20;
x_14 = x_19;
goto _start;
}
}
}
}
lean_object* l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
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
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_5, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_5, 1);
lean_inc(x_16);
lean_dec(x_5);
lean_inc(x_7);
lean_inc(x_15);
x_17 = l_Lean_getConstInfoCtor___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__1(x_15, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_20 = l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6(x_1, x_2, x_3, x_15, x_18, x_4, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_5 = x_16;
x_6 = x_21;
x_13 = x_22;
goto _start;
}
else
{
uint8_t x_24; 
lean_dec(x_16);
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
x_24 = !lean_is_exclusive(x_20);
if (x_24 == 0)
{
return x_20;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_20, 0);
x_26 = lean_ctor_get(x_20, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_20);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
uint8_t x_28; 
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
x_28 = !lean_is_exclusive(x_17);
if (x_28 == 0)
{
return x_17;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_17, 0);
x_30 = lean_ctor_get(x_17, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_17);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
}
lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_1, 4);
lean_inc(x_10);
x_11 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__57;
lean_inc(x_10);
x_12 = l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__7(x_1, x_2, x_11, x_10, x_10, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
return x_12;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_12);
if (x_17 == 0)
{
return x_12;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_12, 0);
x_19 = lean_ctor_get(x_12, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_12);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
lean_object* l_Lean_throwError___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
lean_object* l_Lean_getConstInfoCtor___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_12;
}
}
lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_12;
}
}
lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_16;
}
}
lean_object* l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_4);
return x_17;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("match");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__6;
x_2 = l_Lean_Elab_Deriving_DecEq_mkMatch___rarg___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch___rarg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("with");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch___rarg___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("matchAlts");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch___rarg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__6;
x_2 = l_Lean_Elab_Deriving_DecEq_mkMatch___rarg___closed__4;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkMatch___rarg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(6u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_2);
x_12 = l_Lean_Elab_Deriving_mkDiscrs(x_1, x_2, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_15 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts(x_2, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Deriving_mkInductiveApp___spec__2___rarg(x_9, x_10, x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_6, x_7, x_8, x_9, x_10, x_20);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = l_Lean_Elab_Term_getMainModule___rarg(x_10, x_22);
lean_dec(x_10);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; size_t x_29; size_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_25 = lean_ctor_get(x_23, 0);
lean_dec(x_25);
x_26 = l_Lean_Elab_Deriving_DecEq_mkMatch___rarg___closed__1;
lean_inc(x_19);
x_27 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_27, 0, x_19);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_array_get_size(x_13);
x_29 = lean_usize_of_nat(x_28);
lean_dec(x_28);
x_30 = 0;
x_31 = x_13;
x_32 = l_Array_mapMUnsafe_map___at_myMacro____x40_Init_NotationExtra___hyg_4440____spec__3(x_29, x_30, x_31);
x_33 = x_32;
x_34 = l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1___closed__10;
x_35 = l_Lean_mkSepArray(x_33, x_34);
lean_dec(x_33);
x_36 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__57;
x_37 = l_Array_append___rarg(x_36, x_35);
lean_dec(x_35);
x_38 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__19;
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
x_40 = l_Lean_Elab_Deriving_DecEq_mkMatch___rarg___closed__3;
x_41 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_41, 0, x_19);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_Array_append___rarg(x_36, x_16);
lean_dec(x_16);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_38);
lean_ctor_set(x_43, 1, x_42);
x_44 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__26;
x_45 = lean_array_push(x_44, x_43);
x_46 = l_Lean_Elab_Deriving_DecEq_mkMatch___rarg___closed__5;
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
x_48 = l_Lean_Elab_Deriving_DecEq_mkMatch___rarg___closed__6;
x_49 = lean_array_push(x_48, x_27);
x_50 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__58;
x_51 = lean_array_push(x_49, x_50);
x_52 = lean_array_push(x_51, x_39);
x_53 = lean_array_push(x_52, x_50);
x_54 = lean_array_push(x_53, x_41);
x_55 = lean_array_push(x_54, x_47);
x_56 = l_Lean_Elab_Deriving_DecEq_mkMatch___rarg___closed__2;
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_55);
lean_ctor_set(x_23, 0, x_57);
return x_23;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; size_t x_62; size_t x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_58 = lean_ctor_get(x_23, 1);
lean_inc(x_58);
lean_dec(x_23);
x_59 = l_Lean_Elab_Deriving_DecEq_mkMatch___rarg___closed__1;
lean_inc(x_19);
x_60 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_60, 0, x_19);
lean_ctor_set(x_60, 1, x_59);
x_61 = lean_array_get_size(x_13);
x_62 = lean_usize_of_nat(x_61);
lean_dec(x_61);
x_63 = 0;
x_64 = x_13;
x_65 = l_Array_mapMUnsafe_map___at_myMacro____x40_Init_NotationExtra___hyg_4440____spec__3(x_62, x_63, x_64);
x_66 = x_65;
x_67 = l_List_forIn_loop___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__6___lambda__1___closed__10;
x_68 = l_Lean_mkSepArray(x_66, x_67);
lean_dec(x_66);
x_69 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__57;
x_70 = l_Array_append___rarg(x_69, x_68);
lean_dec(x_68);
x_71 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__19;
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_70);
x_73 = l_Lean_Elab_Deriving_DecEq_mkMatch___rarg___closed__3;
x_74 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_74, 0, x_19);
lean_ctor_set(x_74, 1, x_73);
x_75 = l_Array_append___rarg(x_69, x_16);
lean_dec(x_16);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_71);
lean_ctor_set(x_76, 1, x_75);
x_77 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__26;
x_78 = lean_array_push(x_77, x_76);
x_79 = l_Lean_Elab_Deriving_DecEq_mkMatch___rarg___closed__5;
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_78);
x_81 = l_Lean_Elab_Deriving_DecEq_mkMatch___rarg___closed__6;
x_82 = lean_array_push(x_81, x_60);
x_83 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__58;
x_84 = lean_array_push(x_82, x_83);
x_85 = lean_array_push(x_84, x_72);
x_86 = lean_array_push(x_85, x_83);
x_87 = lean_array_push(x_86, x_74);
x_88 = lean_array_push(x_87, x_80);
x_89 = l_Lean_Elab_Deriving_DecEq_mkMatch___rarg___closed__2;
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_88);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_58);
return x_91;
}
}
else
{
uint8_t x_92; 
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_92 = !lean_is_exclusive(x_15);
if (x_92 == 0)
{
return x_15;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_15, 0);
x_94 = lean_ctor_get(x_15, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_15);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
else
{
uint8_t x_96; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_96 = !lean_is_exclusive(x_12);
if (x_96 == 0)
{
return x_12;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_12, 0);
x_98 = lean_ctor_get(x_12, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_12);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
}
}
}
lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Deriving_DecEq_mkMatch___rarg___boxed), 11, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Deriving_DecEq_mkMatch___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_4);
return x_12;
}
}
lean_object* l_Lean_Elab_Deriving_DecEq_mkMatch___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Deriving_DecEq_mkMatch(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__13;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__13;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__1;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__14;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__3;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Command");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__4;
x_2 = l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("declaration");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__6;
x_2 = l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__7;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("declModifiers");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__6;
x_2 = l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__9;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("private");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__6;
x_2 = l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__11;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkMatch___rarg___closed__6;
x_2 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__58;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__13;
x_2 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__58;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("def");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__6;
x_2 = l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__15;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("declId");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__6;
x_2 = l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__17;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("optDeclSig");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__6;
x_2 = l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__19;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__21() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("typeSpec");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__6;
x_2 = l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__21;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__23() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("declValSimple");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__6;
x_2 = l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__23;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Deriving_DecEq_mkAuxFunction(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_9 = lean_ctor_get(x_1, 1);
x_10 = l_Lean_instInhabitedName;
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_array_get(x_10, x_9, x_11);
x_13 = lean_ctor_get(x_1, 0);
x_14 = l_Lean_instInhabitedInductiveVal;
x_15 = lean_array_get(x_14, x_13, x_11);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_15);
x_16 = l_Lean_Elab_Deriving_DecEq_mkDecEqHeader___rarg(x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_12);
lean_inc(x_17);
x_20 = l_Lean_Elab_Deriving_DecEq_mkMatch___rarg(x_17, x_15, x_12, x_19, x_2, x_3, x_4, x_5, x_6, x_7, x_18);
lean_dec(x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_ctor_get(x_17, 0);
lean_inc(x_23);
x_24 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Deriving_mkInductiveApp___spec__2___rarg(x_6, x_7, x_22);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_Lean_Elab_Term_getCurrMacroScope(x_2, x_3, x_4, x_5, x_6, x_7, x_26);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Lean_Elab_Term_getMainModule___rarg(x_7, x_29);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__14;
x_34 = l_Lean_addMacroScope(x_31, x_33, x_28);
x_35 = l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__2;
x_36 = l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__4;
lean_inc(x_25);
x_37 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_37, 0, x_25);
lean_ctor_set(x_37, 1, x_35);
lean_ctor_set(x_37, 2, x_34);
lean_ctor_set(x_37, 3, x_36);
x_38 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__69;
lean_inc(x_25);
x_39 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_39, 0, x_25);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_ctor_get(x_17, 2);
lean_inc(x_40);
lean_dec(x_17);
x_41 = lean_array_get(x_10, x_40, x_11);
x_42 = lean_mk_syntax_ident(x_41);
x_43 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__38;
lean_inc(x_25);
x_44 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_44, 0, x_25);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_unsigned_to_nat(1u);
x_46 = lean_array_get(x_10, x_40, x_45);
lean_dec(x_40);
x_47 = lean_mk_syntax_ident(x_46);
x_48 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__39;
x_49 = lean_array_push(x_48, x_42);
x_50 = lean_array_push(x_49, x_44);
x_51 = lean_array_push(x_50, x_47);
x_52 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__37;
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_51);
x_54 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__27;
x_55 = lean_array_push(x_54, x_53);
x_56 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__58;
x_57 = lean_array_push(x_55, x_56);
x_58 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__19;
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_57);
x_60 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__86;
x_61 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_61, 0, x_25);
lean_ctor_set(x_61, 1, x_60);
x_62 = lean_array_push(x_48, x_39);
x_63 = lean_array_push(x_62, x_59);
x_64 = lean_array_push(x_63, x_61);
x_65 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__68;
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_64);
x_67 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__26;
x_68 = lean_array_push(x_67, x_66);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_58);
lean_ctor_set(x_69, 1, x_68);
x_70 = lean_array_push(x_54, x_37);
x_71 = lean_array_push(x_70, x_69);
x_72 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__8;
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_71);
x_74 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Deriving_mkInductiveApp___spec__2___rarg(x_6, x_7, x_32);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
x_77 = l_Lean_Elab_Term_getCurrMacroScope(x_2, x_3, x_4, x_5, x_6, x_7, x_76);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_78 = lean_ctor_get(x_77, 1);
lean_inc(x_78);
lean_dec(x_77);
x_79 = l_Lean_Elab_Term_getMainModule___rarg(x_7, x_78);
lean_dec(x_7);
x_80 = !lean_is_exclusive(x_79);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_81 = lean_ctor_get(x_79, 0);
lean_dec(x_81);
x_82 = l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__11;
lean_inc(x_75);
x_83 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_83, 0, x_75);
lean_ctor_set(x_83, 1, x_82);
x_84 = lean_array_push(x_67, x_83);
x_85 = l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__12;
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_84);
x_87 = lean_array_push(x_67, x_86);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_58);
lean_ctor_set(x_88, 1, x_87);
x_89 = l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__14;
x_90 = lean_array_push(x_89, x_88);
x_91 = lean_array_push(x_90, x_56);
x_92 = lean_array_push(x_91, x_56);
x_93 = lean_array_push(x_92, x_56);
x_94 = l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__10;
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_93);
x_96 = l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__15;
lean_inc(x_75);
x_97 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_97, 0, x_75);
lean_ctor_set(x_97, 1, x_96);
x_98 = lean_mk_syntax_ident(x_12);
x_99 = lean_array_push(x_54, x_98);
x_100 = lean_array_push(x_99, x_56);
x_101 = l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__18;
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_100);
x_103 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__57;
x_104 = l_Array_append___rarg(x_103, x_23);
lean_dec(x_23);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_58);
lean_ctor_set(x_105, 1, x_104);
x_106 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__35;
lean_inc(x_75);
x_107 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_107, 0, x_75);
lean_ctor_set(x_107, 1, x_106);
x_108 = lean_array_push(x_54, x_107);
x_109 = lean_array_push(x_108, x_73);
x_110 = l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__22;
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_109);
x_112 = lean_array_push(x_67, x_111);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_58);
lean_ctor_set(x_113, 1, x_112);
x_114 = lean_array_push(x_54, x_105);
x_115 = lean_array_push(x_114, x_113);
x_116 = l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__20;
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_115);
x_118 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__98;
x_119 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_119, 0, x_75);
lean_ctor_set(x_119, 1, x_118);
x_120 = lean_array_push(x_48, x_119);
x_121 = lean_array_push(x_120, x_21);
x_122 = lean_array_push(x_121, x_56);
x_123 = l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__24;
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_122);
x_125 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__85;
x_126 = lean_array_push(x_125, x_97);
x_127 = lean_array_push(x_126, x_102);
x_128 = lean_array_push(x_127, x_117);
x_129 = lean_array_push(x_128, x_124);
x_130 = l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__16;
x_131 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_129);
x_132 = lean_array_push(x_54, x_95);
x_133 = lean_array_push(x_132, x_131);
x_134 = l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__8;
x_135 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_133);
lean_ctor_set(x_79, 0, x_135);
return x_79;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_136 = lean_ctor_get(x_79, 1);
lean_inc(x_136);
lean_dec(x_79);
x_137 = l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__11;
lean_inc(x_75);
x_138 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_138, 0, x_75);
lean_ctor_set(x_138, 1, x_137);
x_139 = lean_array_push(x_67, x_138);
x_140 = l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__12;
x_141 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_139);
x_142 = lean_array_push(x_67, x_141);
x_143 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_143, 0, x_58);
lean_ctor_set(x_143, 1, x_142);
x_144 = l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__14;
x_145 = lean_array_push(x_144, x_143);
x_146 = lean_array_push(x_145, x_56);
x_147 = lean_array_push(x_146, x_56);
x_148 = lean_array_push(x_147, x_56);
x_149 = l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__10;
x_150 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_150, 0, x_149);
lean_ctor_set(x_150, 1, x_148);
x_151 = l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__15;
lean_inc(x_75);
x_152 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_152, 0, x_75);
lean_ctor_set(x_152, 1, x_151);
x_153 = lean_mk_syntax_ident(x_12);
x_154 = lean_array_push(x_54, x_153);
x_155 = lean_array_push(x_154, x_56);
x_156 = l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__18;
x_157 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_155);
x_158 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__57;
x_159 = l_Array_append___rarg(x_158, x_23);
lean_dec(x_23);
x_160 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_160, 0, x_58);
lean_ctor_set(x_160, 1, x_159);
x_161 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__35;
lean_inc(x_75);
x_162 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_162, 0, x_75);
lean_ctor_set(x_162, 1, x_161);
x_163 = lean_array_push(x_54, x_162);
x_164 = lean_array_push(x_163, x_73);
x_165 = l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__22;
x_166 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_166, 0, x_165);
lean_ctor_set(x_166, 1, x_164);
x_167 = lean_array_push(x_67, x_166);
x_168 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_168, 0, x_58);
lean_ctor_set(x_168, 1, x_167);
x_169 = lean_array_push(x_54, x_160);
x_170 = lean_array_push(x_169, x_168);
x_171 = l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__20;
x_172 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_172, 0, x_171);
lean_ctor_set(x_172, 1, x_170);
x_173 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__98;
x_174 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_174, 0, x_75);
lean_ctor_set(x_174, 1, x_173);
x_175 = lean_array_push(x_48, x_174);
x_176 = lean_array_push(x_175, x_21);
x_177 = lean_array_push(x_176, x_56);
x_178 = l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__24;
x_179 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_179, 0, x_178);
lean_ctor_set(x_179, 1, x_177);
x_180 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__85;
x_181 = lean_array_push(x_180, x_152);
x_182 = lean_array_push(x_181, x_157);
x_183 = lean_array_push(x_182, x_172);
x_184 = lean_array_push(x_183, x_179);
x_185 = l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__16;
x_186 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_186, 0, x_185);
lean_ctor_set(x_186, 1, x_184);
x_187 = lean_array_push(x_54, x_150);
x_188 = lean_array_push(x_187, x_186);
x_189 = l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__8;
x_190 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_190, 0, x_189);
lean_ctor_set(x_190, 1, x_188);
x_191 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_191, 0, x_190);
lean_ctor_set(x_191, 1, x_136);
return x_191;
}
}
else
{
uint8_t x_192; 
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_192 = !lean_is_exclusive(x_20);
if (x_192 == 0)
{
return x_20;
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_193 = lean_ctor_get(x_20, 0);
x_194 = lean_ctor_get(x_20, 1);
lean_inc(x_194);
lean_inc(x_193);
lean_dec(x_20);
x_195 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_195, 0, x_193);
lean_ctor_set(x_195, 1, x_194);
return x_195;
}
}
}
else
{
uint8_t x_196; 
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_196 = !lean_is_exclusive(x_16);
if (x_196 == 0)
{
return x_16;
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_197 = lean_ctor_get(x_16, 0);
x_198 = lean_ctor_get(x_16, 1);
lean_inc(x_198);
lean_inc(x_197);
lean_dec(x_16);
x_199 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_199, 0, x_197);
lean_ctor_set(x_199, 1, x_198);
return x_199;
}
}
}
}
lean_object* l_Lean_Elab_Deriving_DecEq_mkAuxFunction___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Deriving_DecEq_mkAuxFunction(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
return x_9;
}
}
lean_object* l_List_map___at_Lean_Elab_Deriving_DecEq_mkDecEqCmds___spec__1(lean_object* x_1) {
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
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_4);
x_7 = l_List_map___at_Lean_Elab_Deriving_DecEq_mkDecEqCmds___spec__1(x_5);
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
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_8);
x_11 = l_List_map___at_Lean_Elab_Deriving_DecEq_mkDecEqCmds___spec__1(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkDecEqCmds___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("decEq");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkDecEqCmds___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Elab");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkDecEqCmds___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Deriving_DecEq_mkDecEqCmds___closed__2;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkDecEqCmds___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Deriving");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkDecEqCmds___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkDecEqCmds___closed__3;
x_2 = l_Lean_Elab_Deriving_DecEq_mkDecEqCmds___closed__4;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkDecEqCmds___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Deriving_DecEq_mkDecEqCmds___closed__5;
x_2 = l_Lean_Elab_Deriving_DecEq_mkDecEqCmds___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_mkDecEqCmds___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("\n");
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
x_1 = lean_mk_string("");
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
lean_object* l_Lean_Elab_Deriving_DecEq_mkDecEqCmds(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
x_18 = l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__26;
x_19 = lean_array_push(x_18, x_10);
x_20 = l_Lean_Elab_Deriving_DecEq_mkDecEqHeader___rarg___closed__2;
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
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
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
lean_dec(x_23);
x_45 = lean_st_ref_get(x_7, x_24);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_46, 3);
lean_inc(x_47);
lean_dec(x_46);
x_48 = lean_ctor_get_uint8(x_47, sizeof(void*)*1);
lean_dec(x_47);
if (x_48 == 0)
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_45, 1);
lean_inc(x_49);
lean_dec(x_45);
x_28 = x_21;
x_29 = x_49;
goto block_44;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_50 = lean_ctor_get(x_45, 1);
lean_inc(x_50);
lean_dec(x_45);
x_51 = l_Lean_Elab_Deriving_DecEq_mkDecEqCmds___closed__6;
x_52 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__2(x_51, x_2, x_3, x_4, x_5, x_6, x_7, x_50);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = lean_unbox(x_53);
lean_dec(x_53);
x_28 = x_55;
x_29 = x_54;
goto block_44;
}
block_44:
{
if (x_28 == 0)
{
lean_object* x_30; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
if (lean_is_scalar(x_25)) {
 x_30 = lean_alloc_ctor(0, 2, 0);
} else {
 x_30 = x_25;
}
lean_ctor_set(x_30, 0, x_27);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
lean_dec(x_25);
lean_inc(x_27);
x_31 = lean_array_to_list(lean_box(0), x_27);
x_32 = l_List_map___at_Lean_Elab_Deriving_DecEq_mkDecEqCmds___spec__1(x_31);
x_33 = l_Lean_MessageData_ofList(x_32);
lean_dec(x_32);
x_34 = l_Lean_Elab_Deriving_DecEq_mkDecEqCmds___closed__8;
x_35 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
x_36 = l_Lean_Elab_Deriving_DecEq_mkDecEqCmds___closed__10;
x_37 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = l_Lean_Elab_Deriving_DecEq_mkDecEqCmds___closed__6;
x_39 = l_Lean_addTrace___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__1(x_38, x_37, x_2, x_3, x_4, x_5, x_6, x_7, x_29);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_39, 0);
lean_dec(x_41);
lean_ctor_set(x_39, 0, x_27);
return x_39;
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_39, 1);
lean_inc(x_42);
lean_dec(x_39);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_27);
lean_ctor_set(x_43, 1, x_42);
return x_43;
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
lean_object* l_Lean_throwError___at_Lean_Elab_Deriving_DecEq_mkDecEqInstanceHandler___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
static lean_object* _init_l_Lean_getConstInfoInduct___at_Lean_Elab_Deriving_DecEq_mkDecEqInstanceHandler___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' is not a inductive type");
return x_1;
}
}
static lean_object* _init_l_Lean_getConstInfoInduct___at_Lean_Elab_Deriving_DecEq_mkDecEqInstanceHandler___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_getConstInfoInduct___at_Lean_Elab_Deriving_DecEq_mkDecEqInstanceHandler___spec__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Lean_getConstInfoInduct___at_Lean_Elab_Deriving_DecEq_mkDecEqInstanceHandler___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_2);
lean_inc(x_1);
x_5 = l_Lean_getConstInfo___at_Lean_Elab_elabDeriving___spec__7(x_1, x_2, x_3, x_4);
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
x_15 = l_Lean_mkConst(x_1, x_14);
x_16 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = l_Lean_getConstInfoCtor___at_Lean_Elab_Deriving_DecEq_mkMatch_mkAlts___spec__1___closed__2;
x_18 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = l_Lean_getConstInfoInduct___at_Lean_Elab_Deriving_DecEq_mkDecEqInstanceHandler___spec__1___closed__2;
x_20 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_throwError___at_Lean_Elab_Deriving_DecEq_mkDecEqInstanceHandler___spec__2(x_20, x_2, x_3, x_13);
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
lean_object* l_Lean_Elab_Deriving_DecEq_mkDecEqInstanceHandler(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_array_get_size(x_1);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_dec_eq(x_5, x_6);
lean_dec(x_5);
if (x_7 == 0)
{
uint8_t x_8; lean_object* x_9; lean_object* x_10; 
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
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = l_Lean_instInhabitedName;
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_array_get(x_11, x_1, x_12);
lean_inc(x_2);
x_14 = l_Lean_getConstInfoInduct___at_Lean_Elab_Deriving_DecEq_mkDecEqInstanceHandler___spec__1(x_13, x_2, x_3, x_4);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get_uint8(x_15, sizeof(void*)*5 + 3);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_box(0);
x_19 = lean_alloc_closure((void*)(l_Lean_Elab_Deriving_DecEq_mkDecEqCmds), 8, 1);
lean_closure_set(x_19, 0, x_15);
lean_inc(x_2);
x_20 = l_Lean_Elab_Command_liftTermElabM___rarg(x_18, x_19, x_2, x_3, x_17);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_20, 1);
x_24 = lean_array_get_size(x_22);
x_25 = lean_nat_dec_lt(x_12, x_24);
if (x_25 == 0)
{
uint8_t x_26; lean_object* x_27; 
lean_dec(x_24);
lean_dec(x_22);
lean_dec(x_3);
lean_dec(x_2);
x_26 = 1;
x_27 = lean_box(x_26);
lean_ctor_set(x_20, 0, x_27);
return x_20;
}
else
{
uint8_t x_28; 
x_28 = lean_nat_dec_le(x_24, x_24);
if (x_28 == 0)
{
uint8_t x_29; lean_object* x_30; 
lean_dec(x_24);
lean_dec(x_22);
lean_dec(x_3);
lean_dec(x_2);
x_29 = 1;
x_30 = lean_box(x_29);
lean_ctor_set(x_20, 0, x_30);
return x_20;
}
else
{
size_t x_31; size_t x_32; lean_object* x_33; lean_object* x_34; 
lean_free_object(x_20);
x_31 = 0;
x_32 = lean_usize_of_nat(x_24);
lean_dec(x_24);
x_33 = lean_box(0);
x_34 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabCommand___spec__13(x_22, x_31, x_32, x_33, x_2, x_3, x_23);
lean_dec(x_2);
lean_dec(x_22);
if (lean_obj_tag(x_34) == 0)
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; uint8_t x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_34, 0);
lean_dec(x_36);
x_37 = 1;
x_38 = lean_box(x_37);
lean_ctor_set(x_34, 0, x_38);
return x_34;
}
else
{
lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; 
x_39 = lean_ctor_get(x_34, 1);
lean_inc(x_39);
lean_dec(x_34);
x_40 = 1;
x_41 = lean_box(x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_39);
return x_42;
}
}
else
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_34);
if (x_43 == 0)
{
return x_34;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_34, 0);
x_45 = lean_ctor_get(x_34, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_34);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_47 = lean_ctor_get(x_20, 0);
x_48 = lean_ctor_get(x_20, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_20);
x_49 = lean_array_get_size(x_47);
x_50 = lean_nat_dec_lt(x_12, x_49);
if (x_50 == 0)
{
uint8_t x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_49);
lean_dec(x_47);
lean_dec(x_3);
lean_dec(x_2);
x_51 = 1;
x_52 = lean_box(x_51);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_48);
return x_53;
}
else
{
uint8_t x_54; 
x_54 = lean_nat_dec_le(x_49, x_49);
if (x_54 == 0)
{
uint8_t x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_49);
lean_dec(x_47);
lean_dec(x_3);
lean_dec(x_2);
x_55 = 1;
x_56 = lean_box(x_55);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_48);
return x_57;
}
else
{
size_t x_58; size_t x_59; lean_object* x_60; lean_object* x_61; 
x_58 = 0;
x_59 = lean_usize_of_nat(x_49);
lean_dec(x_49);
x_60 = lean_box(0);
x_61 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabCommand___spec__13(x_47, x_58, x_59, x_60, x_2, x_3, x_48);
lean_dec(x_2);
lean_dec(x_47);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; uint8_t x_64; lean_object* x_65; lean_object* x_66; 
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
x_64 = 1;
x_65 = lean_box(x_64);
if (lean_is_scalar(x_63)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_63;
}
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_62);
return x_66;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_67 = lean_ctor_get(x_61, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_61, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_69 = x_61;
} else {
 lean_dec_ref(x_61);
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
}
}
else
{
uint8_t x_71; 
lean_dec(x_3);
lean_dec(x_2);
x_71 = !lean_is_exclusive(x_20);
if (x_71 == 0)
{
return x_20;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_20, 0);
x_73 = lean_ctor_get(x_20, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_20);
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
lean_dec(x_15);
lean_dec(x_3);
lean_dec(x_2);
x_75 = !lean_is_exclusive(x_14);
if (x_75 == 0)
{
lean_object* x_76; uint8_t x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_14, 0);
lean_dec(x_76);
x_77 = 0;
x_78 = lean_box(x_77);
lean_ctor_set(x_14, 0, x_78);
return x_14;
}
else
{
lean_object* x_79; uint8_t x_80; lean_object* x_81; lean_object* x_82; 
x_79 = lean_ctor_get(x_14, 1);
lean_inc(x_79);
lean_dec(x_14);
x_80 = 0;
x_81 = lean_box(x_80);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_79);
return x_82;
}
}
}
else
{
uint8_t x_83; 
lean_dec(x_3);
lean_dec(x_2);
x_83 = !lean_is_exclusive(x_14);
if (x_83 == 0)
{
return x_14;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_14, 0);
x_85 = lean_ctor_get(x_14, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_14);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
}
}
}
lean_object* l_Lean_throwError___at_Lean_Elab_Deriving_DecEq_mkDecEqInstanceHandler___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_throwError___at_Lean_Elab_Deriving_DecEq_mkDecEqInstanceHandler___spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Lean_getConstInfoInduct___at_Lean_Elab_Deriving_DecEq_mkDecEqInstanceHandler___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_getConstInfoInduct___at_Lean_Elab_Deriving_DecEq_mkDecEqInstanceHandler___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Lean_Elab_Deriving_DecEq_mkDecEqInstanceHandler___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Deriving_DecEq_mkDecEqInstanceHandler(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_DecEq_initFn____x40_Lean_Elab_Deriving_DecEq___hyg_2438____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Deriving_DecEq_mkDecEqInstanceHandler___boxed), 4, 0);
return x_1;
}
}
lean_object* l_Lean_Elab_Deriving_DecEq_initFn____x40_Lean_Elab_Deriving_DecEq___hyg_2438_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Elab_Deriving_DecEq_mkDecEqHeader___rarg___closed__2;
x_3 = l_Lean_Elab_Deriving_DecEq_initFn____x40_Lean_Elab_Deriving_DecEq___hyg_2438____closed__1;
x_4 = l_Lean_Elab_registerBuiltinDerivingHandler(x_2, x_3, x_1);
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
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Meta_Transform(lean_object*);
lean_object* initialize_Lean_Meta_Inductive(lean_object*);
lean_object* initialize_Lean_Elab_Deriving_Basic(lean_object*);
lean_object* initialize_Lean_Elab_Deriving_Util(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Elab_Deriving_DecEq(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Transform(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Inductive(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Deriving_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Deriving_Util(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Deriving_DecEq_mkDecEqHeader___rarg___closed__1 = _init_l_Lean_Elab_Deriving_DecEq_mkDecEqHeader___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkDecEqHeader___rarg___closed__1);
l_Lean_Elab_Deriving_DecEq_mkDecEqHeader___rarg___closed__2 = _init_l_Lean_Elab_Deriving_DecEq_mkDecEqHeader___rarg___closed__2();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkDecEqHeader___rarg___closed__2);
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
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__8 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__8();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__8);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__9 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__9();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__9);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__10 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__10();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__10);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__11 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__11();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__11);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__12 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__12();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__12);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__13 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__13();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__13);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__14 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__14();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__14);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__15 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__15();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__15);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__16 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__16();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__16);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__17 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__17();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__17);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__18 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__18();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__18);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__19 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__19();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__19);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__20 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__20();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__20);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__21 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__21();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__21);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__22 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__22();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__22);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__23 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__23();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__23);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__24 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__24();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__24);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__25 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__25();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__25);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__26 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__26();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__26);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__27 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__27();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__27);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__28 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__28();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__28);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__29 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__29();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__29);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__30 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__30();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__30);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__31 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__31();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__31);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__32 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__32();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__32);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__33 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__33();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__33);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__34 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__34();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__34);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__35 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__35();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__35);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__36 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__36();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__36);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__37 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__37();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__37);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__38 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__38();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__38);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__39 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__39();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__39);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__40 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__40();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__40);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__41 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__41();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__41);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__42 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__42();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__42);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__43 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__43();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__43);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__44 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__44();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__44);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__45 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__45();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__45);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__46 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__46();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__46);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__47 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__47();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__47);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__48 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__48();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__48);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__49 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__49();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__49);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__50 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__50();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__50);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__51 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__51();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__51);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__52 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__52();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__52);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__53 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__53();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__53);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__54 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__54();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__54);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__55 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__55();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__55);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__56 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__56();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__56);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__57 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__57();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__57);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__58 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__58();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__58);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__59 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__59();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__59);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__60 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__60();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__60);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__61 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__61();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__61);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__62 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__62();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__62);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__63 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__63();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__63);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__64 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__64();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__64);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__65 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__65();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__65);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__66 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__66();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__66);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__67 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__67();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__67);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__68 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__68();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__68);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__69 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__69();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__69);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__70 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__70();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__70);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__71 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__71();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__71);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__72 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__72();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__72);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__73 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__73();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__73);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__74 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__74();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__74);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__75 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__75();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__75);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__76 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__76();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__76);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__77 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__77();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__77);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__78 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__78();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__78);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__79 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__79();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__79);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__80 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__80();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__80);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__81 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__81();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__81);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__82 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__82();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__82);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__83 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__83();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__83);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__84 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__84();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__84);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__85 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__85();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__85);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__86 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__86();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__86);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__87 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__87();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__87);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__88 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__88();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__88);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__89 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__89();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__89);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__90 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__90();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__90);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__91 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__91();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__91);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__92 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__92();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__92);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__93 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__93();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__93);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__94 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__94();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__94);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__95 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__95();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__95);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__96 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__96();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__96);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__97 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__97();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__97);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__98 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__98();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__98);
l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__99 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__99();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch_mkSameCtorRhs___closed__99);
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
l_Lean_Elab_Deriving_DecEq_mkMatch___rarg___closed__1 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch___rarg___closed__1);
l_Lean_Elab_Deriving_DecEq_mkMatch___rarg___closed__2 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch___rarg___closed__2();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch___rarg___closed__2);
l_Lean_Elab_Deriving_DecEq_mkMatch___rarg___closed__3 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch___rarg___closed__3();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch___rarg___closed__3);
l_Lean_Elab_Deriving_DecEq_mkMatch___rarg___closed__4 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch___rarg___closed__4();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch___rarg___closed__4);
l_Lean_Elab_Deriving_DecEq_mkMatch___rarg___closed__5 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch___rarg___closed__5();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch___rarg___closed__5);
l_Lean_Elab_Deriving_DecEq_mkMatch___rarg___closed__6 = _init_l_Lean_Elab_Deriving_DecEq_mkMatch___rarg___closed__6();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkMatch___rarg___closed__6);
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
l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__22 = _init_l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__22();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__22);
l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__23 = _init_l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__23();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__23);
l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__24 = _init_l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__24();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_mkAuxFunction___closed__24);
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
l_Lean_getConstInfoInduct___at_Lean_Elab_Deriving_DecEq_mkDecEqInstanceHandler___spec__1___closed__1 = _init_l_Lean_getConstInfoInduct___at_Lean_Elab_Deriving_DecEq_mkDecEqInstanceHandler___spec__1___closed__1();
lean_mark_persistent(l_Lean_getConstInfoInduct___at_Lean_Elab_Deriving_DecEq_mkDecEqInstanceHandler___spec__1___closed__1);
l_Lean_getConstInfoInduct___at_Lean_Elab_Deriving_DecEq_mkDecEqInstanceHandler___spec__1___closed__2 = _init_l_Lean_getConstInfoInduct___at_Lean_Elab_Deriving_DecEq_mkDecEqInstanceHandler___spec__1___closed__2();
lean_mark_persistent(l_Lean_getConstInfoInduct___at_Lean_Elab_Deriving_DecEq_mkDecEqInstanceHandler___spec__1___closed__2);
l_Lean_Elab_Deriving_DecEq_initFn____x40_Lean_Elab_Deriving_DecEq___hyg_2438____closed__1 = _init_l_Lean_Elab_Deriving_DecEq_initFn____x40_Lean_Elab_Deriving_DecEq___hyg_2438____closed__1();
lean_mark_persistent(l_Lean_Elab_Deriving_DecEq_initFn____x40_Lean_Elab_Deriving_DecEq___hyg_2438____closed__1);
res = l_Lean_Elab_Deriving_DecEq_initFn____x40_Lean_Elab_Deriving_DecEq___hyg_2438_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
