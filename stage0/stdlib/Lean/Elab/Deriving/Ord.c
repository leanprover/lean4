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
static lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__52;
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__9;
static lean_object* l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__13;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_List_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__7___lambda__2___closed__11;
static lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__33;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__6(size_t, size_t, lean_object*);
static lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__3;
static lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__22;
lean_object* l_Lean_Elab_Command_liftTermElabM___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__43;
static lean_object* l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__12;
static lean_object* l_Lean_Elab_Deriving_Ord_mkMutualBlock___closed__2;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
static lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__2;
static lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__35;
lean_object* lean_environment_find(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Deriving_Ord_initFn____x40_Lean_Elab_Deriving_Ord___hyg_2936____closed__1;
static lean_object* l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__16;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__39;
static lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__5;
static lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__36;
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Ord_mkOrdHeader(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* lean_string_utf8_byte_size(lean_object*);
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
static lean_object* l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__24;
lean_object* l_Lean_Elab_Deriving_mkDiscrs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_getConstInfoCtor___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__1___closed__1;
static lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__10;
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__19;
lean_object* l_Array_mapMUnsafe_map___at___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___spec__3(size_t, size_t, lean_object*);
static lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__8;
static lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__32;
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__9;
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
static lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__51;
static lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__34;
lean_object* l_Lean_Elab_Deriving_mkLet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Ord_mkOrdInstanceHandler(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__48;
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
static lean_object* l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__28;
static lean_object* l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__5;
static lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__50;
static lean_object* l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__29;
static lean_object* l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__25;
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Ord_mkMutualBlock(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__22;
static lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__49;
LEAN_EXPORT lean_object* l_Lean_isInductive___at_Lean_Elab_Deriving_Ord_mkOrdInstanceHandler___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_addMacroStack___at_Lean_Elab_Term_instAddErrorMessageContextTermElabM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__7;
static lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__24;
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__7___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__13;
static lean_object* l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__14;
lean_object* lean_array_to_list(lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__16;
extern lean_object* l_Lean_instInhabitedExpr;
static lean_object* l_List_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__7___lambda__2___closed__5;
static lean_object* l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__6;
lean_object* l_Lean_mkSepArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_transform___at_Lean_Core_betaReduce___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__31;
lean_object* l_Lean_Elab_Deriving_mkContext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__7___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__21;
lean_object* l_Lean_addTrace___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__38;
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
static lean_object* l_List_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__7___lambda__2___closed__3;
static lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__6;
static lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__20;
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabCommand___spec__16(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__41;
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Ord_initFn____x40_Lean_Elab_Deriving_Ord___hyg_2936_(lean_object*);
lean_object* l_Lean_Elab_Deriving_mkHeader(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__23;
static lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__37;
static lean_object* l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__4;
static lean_object* l_Lean_getConstInfoCtor___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__7___lambda__2___closed__9;
static lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__10;
static lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__42;
static lean_object* l_List_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__7___lambda__2___closed__4;
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMutualBlock___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__7___lambda__2___closed__8;
lean_object* lean_environment_main_module(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__6___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__17;
static lean_object* l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__8;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__12;
static lean_object* l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__1;
lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_exprToSyntax___spec__1___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Deriving_Ord_mkOrdHeader___closed__1;
static lean_object* l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__2;
static lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__26;
static lean_object* l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__3;
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__1;
static lean_object* l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__15;
static lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__10;
static lean_object* l_Lean_Elab_Deriving_Ord_mkMutualBlock___closed__4;
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__44;
extern lean_object* l_Lean_instInhabitedName;
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__2;
lean_object* l_Lean_Elab_registerBuiltinDerivingHandler(lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_forallTelescopeReducing___at_Lean_Elab_Deriving_mkInductArgNames___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__14;
static lean_object* l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__9;
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__7___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__27;
static lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__28;
lean_object* lean_mk_syntax_ident(lean_object*);
extern lean_object* l_Lean_instInhabitedInductiveVal;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__1;
static lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__4;
static lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__7;
static lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__15;
static lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__3;
static lean_object* l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__26;
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__7___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Deriving_Ord_mkMutualBlock___closed__5;
lean_object* l_Lean_Core_betaReduce___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__7___lambda__2___closed__10;
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Ord_mkMatch_mkAlts(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Deriving_Ord_mkMatch___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
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
x_3 = lean_name_mk_string(x_1, x_2);
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
x_10 = lean_ctor_get(x_2, 1);
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
x_19 = l_Lean_mkConst(x_1, x_18);
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Parser", 6);
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__2;
x_2 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Term", 4);
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__4;
x_2 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("hole", 4);
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__6;
x_2 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__7;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_", 1);
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
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
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
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
x_23 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__9;
x_24 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_24, 0, x_19);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__10;
x_26 = lean_array_push(x_25, x_24);
x_27 = lean_box(2);
x_28 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__8;
x_29 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
lean_ctor_set(x_29, 2, x_26);
x_30 = lean_array_push(x_5, x_29);
x_31 = lean_nat_add(x_2, x_4);
lean_dec(x_2);
x_1 = x_17;
x_2 = x_31;
x_5 = x_30;
x_12 = x_22;
goto _start;
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
else
{
lean_object* x_34; 
lean_dec(x_10);
lean_dec(x_2);
lean_dec(x_1);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_5);
lean_ctor_set(x_34, 1, x_12);
return x_34;
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
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
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
x_25 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__9;
x_26 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_26, 0, x_21);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__10;
x_28 = lean_array_push(x_27, x_26);
x_29 = lean_box(2);
x_30 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__8;
x_31 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
lean_ctor_set(x_31, 2, x_28);
x_32 = lean_array_push(x_18, x_31);
lean_inc(x_10);
x_33 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_exprToSyntax___spec__1___rarg(x_10, x_11, x_24);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_st_ref_get(x_11, x_35);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
x_38 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_38, 0, x_34);
lean_ctor_set(x_38, 1, x_25);
x_39 = lean_array_push(x_27, x_38);
x_40 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_40, 0, x_29);
lean_ctor_set(x_40, 1, x_30);
lean_ctor_set(x_40, 2, x_39);
x_41 = lean_array_push(x_19, x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_32);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_nat_add(x_2, x_4);
lean_dec(x_2);
x_1 = x_17;
x_2 = x_43;
x_5 = x_42;
x_12 = x_37;
goto _start;
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
else
{
lean_object* x_46; 
lean_dec(x_10);
lean_dec(x_2);
lean_dec(x_1);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_5);
lean_ctor_set(x_46, 1, x_12);
return x_46;
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__6;
x_2 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
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
x_3 = lean_name_mk_string(x_1, x_2);
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(2);
x_2 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__4;
x_3 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__5;
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("matchDiscr", 10);
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__6;
x_2 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__7;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("app", 3);
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__6;
x_2 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__9;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("compare", 7);
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__11;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__11;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__12;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__11;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Deriving_Ord_mkOrdHeader___closed__2;
x_2 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__11;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__15;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__16;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__18;
x_2 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__6;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__20() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("with", 4);
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__21() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("matchAlts", 9);
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__6;
x_2 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__21;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__23() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("matchAlt", 8);
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__6;
x_2 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__23;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__25() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("|", 1);
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__26() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Ordering.lt", 11);
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__26;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__28() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__26;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__27;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__29() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Ordering", 8);
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__30() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__29;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__31() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("lt", 2);
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__32() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__30;
x_2 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__31;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__33() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__32;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__34() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__33;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__35() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("=>", 2);
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__36() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__37() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Ordering.gt", 11);
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__38() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__37;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__39() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__37;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__38;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__40() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("gt", 2);
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__41() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__30;
x_2 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__40;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__42() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__41;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__43() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__42;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__44() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Ordering.eq", 11);
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__45() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__44;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__46() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__44;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__45;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__47() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("eq", 2);
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__48() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__30;
x_2 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__47;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__49() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__48;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__50() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__49;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__51() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__52() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(6u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
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
x_23 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__14;
lean_inc(x_15);
lean_inc(x_20);
x_24 = l_Lean_addMacroScope(x_20, x_23, x_15);
x_25 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__13;
x_26 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__17;
lean_inc(x_13);
x_27 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_27, 0, x_13);
lean_ctor_set(x_27, 1, x_25);
lean_ctor_set(x_27, 2, x_24);
lean_ctor_set(x_27, 3, x_26);
x_28 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__18;
x_29 = lean_array_push(x_28, x_1);
x_30 = lean_array_push(x_29, x_2);
x_31 = lean_box(2);
x_32 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__4;
x_33 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
lean_ctor_set(x_33, 2, x_30);
x_34 = lean_array_push(x_28, x_27);
x_35 = lean_array_push(x_34, x_33);
x_36 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__10;
x_37 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_37, 0, x_31);
lean_ctor_set(x_37, 1, x_36);
lean_ctor_set(x_37, 2, x_35);
x_38 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__19;
x_39 = lean_array_push(x_38, x_37);
x_40 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__8;
x_41 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_41, 0, x_31);
lean_ctor_set(x_41, 1, x_40);
lean_ctor_set(x_41, 2, x_39);
x_42 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__10;
x_43 = lean_array_push(x_42, x_41);
x_44 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_44, 0, x_31);
lean_ctor_set(x_44, 1, x_32);
lean_ctor_set(x_44, 2, x_43);
x_45 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__20;
lean_inc(x_13);
x_46 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_46, 0, x_13);
lean_ctor_set(x_46, 1, x_45);
x_47 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__25;
lean_inc(x_13);
x_48 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_48, 0, x_13);
lean_ctor_set(x_48, 1, x_47);
x_49 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__32;
lean_inc(x_15);
lean_inc(x_20);
x_50 = l_Lean_addMacroScope(x_20, x_49, x_15);
x_51 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__28;
x_52 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__34;
lean_inc(x_13);
x_53 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_53, 0, x_13);
lean_ctor_set(x_53, 1, x_51);
lean_ctor_set(x_53, 2, x_50);
lean_ctor_set(x_53, 3, x_52);
lean_inc(x_53);
x_54 = lean_array_push(x_42, x_53);
x_55 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_55, 0, x_31);
lean_ctor_set(x_55, 1, x_32);
lean_ctor_set(x_55, 2, x_54);
x_56 = lean_array_push(x_42, x_55);
x_57 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_57, 0, x_31);
lean_ctor_set(x_57, 1, x_32);
lean_ctor_set(x_57, 2, x_56);
x_58 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__35;
lean_inc(x_13);
x_59 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_59, 0, x_13);
lean_ctor_set(x_59, 1, x_58);
x_60 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__36;
x_61 = lean_array_push(x_60, x_48);
lean_inc(x_61);
x_62 = lean_array_push(x_61, x_57);
lean_inc(x_59);
x_63 = lean_array_push(x_62, x_59);
x_64 = lean_array_push(x_63, x_53);
x_65 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__24;
x_66 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_66, 0, x_31);
lean_ctor_set(x_66, 1, x_65);
lean_ctor_set(x_66, 2, x_64);
x_67 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__41;
lean_inc(x_15);
lean_inc(x_20);
x_68 = l_Lean_addMacroScope(x_20, x_67, x_15);
x_69 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__39;
x_70 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__43;
lean_inc(x_13);
x_71 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_71, 0, x_13);
lean_ctor_set(x_71, 1, x_69);
lean_ctor_set(x_71, 2, x_68);
lean_ctor_set(x_71, 3, x_70);
lean_inc(x_71);
x_72 = lean_array_push(x_42, x_71);
x_73 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_73, 0, x_31);
lean_ctor_set(x_73, 1, x_32);
lean_ctor_set(x_73, 2, x_72);
x_74 = lean_array_push(x_42, x_73);
x_75 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_75, 0, x_31);
lean_ctor_set(x_75, 1, x_32);
lean_ctor_set(x_75, 2, x_74);
lean_inc(x_61);
x_76 = lean_array_push(x_61, x_75);
lean_inc(x_59);
x_77 = lean_array_push(x_76, x_59);
x_78 = lean_array_push(x_77, x_71);
x_79 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_79, 0, x_31);
lean_ctor_set(x_79, 1, x_65);
lean_ctor_set(x_79, 2, x_78);
x_80 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__48;
x_81 = l_Lean_addMacroScope(x_20, x_80, x_15);
x_82 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__46;
x_83 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__50;
x_84 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_84, 0, x_13);
lean_ctor_set(x_84, 1, x_82);
lean_ctor_set(x_84, 2, x_81);
lean_ctor_set(x_84, 3, x_83);
x_85 = lean_array_push(x_42, x_84);
x_86 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_86, 0, x_31);
lean_ctor_set(x_86, 1, x_32);
lean_ctor_set(x_86, 2, x_85);
x_87 = lean_array_push(x_42, x_86);
x_88 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_88, 0, x_31);
lean_ctor_set(x_88, 1, x_32);
lean_ctor_set(x_88, 2, x_87);
x_89 = lean_array_push(x_61, x_88);
x_90 = lean_array_push(x_89, x_59);
x_91 = lean_array_push(x_90, x_4);
x_92 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_92, 0, x_31);
lean_ctor_set(x_92, 1, x_65);
lean_ctor_set(x_92, 2, x_91);
x_93 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__51;
x_94 = lean_array_push(x_93, x_66);
x_95 = lean_array_push(x_94, x_79);
x_96 = lean_array_push(x_95, x_92);
x_97 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_97, 0, x_31);
lean_ctor_set(x_97, 1, x_32);
lean_ctor_set(x_97, 2, x_96);
x_98 = lean_array_push(x_42, x_97);
x_99 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__22;
x_100 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_100, 0, x_31);
lean_ctor_set(x_100, 1, x_99);
lean_ctor_set(x_100, 2, x_98);
x_101 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__52;
x_102 = lean_array_push(x_101, x_22);
x_103 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__6;
x_104 = lean_array_push(x_102, x_103);
x_105 = lean_array_push(x_104, x_103);
x_106 = lean_array_push(x_105, x_44);
x_107 = lean_array_push(x_106, x_46);
x_108 = lean_array_push(x_107, x_100);
x_109 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__2;
x_110 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_110, 0, x_31);
lean_ctor_set(x_110, 1, x_109);
lean_ctor_set(x_110, 2, x_108);
x_111 = lean_apply_8(x_3, x_110, x_5, x_6, x_7, x_8, x_9, x_10, x_18);
return x_111;
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
x_3 = lean_name_mk_string(x_1, x_2);
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
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
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
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
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
x_32 = lean_nat_add(x_3, x_5);
x_33 = l_Lean_instInhabitedExpr;
x_34 = lean_array_get(x_33, x_1, x_32);
lean_dec(x_32);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_34);
x_35 = lean_infer_type(x_34, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_38 = l_Lean_Meta_isProp(x_36, x_11, x_12, x_13, x_14, x_37);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_68; uint8_t x_69; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_68 = l_Lean_Expr_fvarId_x21(x_34);
x_69 = l_Lean_Expr_hasAnyFVar_visit___at_Lean_Expr_containsFVar___spec__1(x_68, x_2);
lean_dec(x_68);
if (x_69 == 0)
{
uint8_t x_70; 
x_70 = lean_unbox(x_39);
lean_dec(x_39);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_31);
x_71 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___closed__2;
x_72 = l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(x_71, x_13, x_14, x_40);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
x_75 = lean_mk_syntax_ident(x_73);
x_76 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___closed__4;
x_77 = l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(x_76, x_13, x_14, x_74);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
x_80 = lean_mk_syntax_ident(x_78);
lean_inc(x_75);
x_81 = lean_array_push(x_28, x_75);
lean_inc(x_80);
x_82 = lean_array_push(x_29, x_80);
x_83 = lean_alloc_closure((void*)(l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1), 11, 3);
lean_closure_set(x_83, 0, x_75);
lean_closure_set(x_83, 1, x_80);
lean_closure_set(x_83, 2, x_30);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_81);
lean_ctor_set(x_85, 1, x_84);
x_86 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_86, 0, x_85);
x_21 = x_86;
x_22 = x_79;
goto block_26;
}
else
{
lean_object* x_87; 
x_87 = lean_box(0);
x_41 = x_87;
goto block_67;
}
}
else
{
lean_object* x_88; 
lean_dec(x_39);
x_88 = lean_box(0);
x_41 = x_88;
goto block_67;
}
block_67:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_41);
lean_inc(x_13);
x_42 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_exprToSyntax___spec__1___rarg(x_13, x_14, x_40);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_st_ref_get(x_14, x_44);
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
lean_dec(x_45);
x_47 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__9;
x_48 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_48, 0, x_43);
lean_ctor_set(x_48, 1, x_47);
x_49 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__10;
x_50 = lean_array_push(x_49, x_48);
x_51 = lean_box(2);
x_52 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__8;
x_53 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
lean_ctor_set(x_53, 2, x_50);
x_54 = lean_array_push(x_28, x_53);
lean_inc(x_13);
x_55 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_exprToSyntax___spec__1___rarg(x_13, x_14, x_46);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_58 = lean_st_ref_get(x_14, x_57);
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec(x_58);
x_60 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_60, 0, x_56);
lean_ctor_set(x_60, 1, x_47);
x_61 = lean_array_push(x_49, x_60);
x_62 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_62, 0, x_51);
lean_ctor_set(x_62, 1, x_52);
lean_ctor_set(x_62, 2, x_61);
x_63 = lean_array_push(x_29, x_62);
if (lean_is_scalar(x_31)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_31;
}
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_30);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_54);
lean_ctor_set(x_65, 1, x_64);
x_66 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_66, 0, x_65);
x_21 = x_66;
x_22 = x_59;
goto block_26;
}
}
else
{
uint8_t x_89; 
lean_dec(x_34);
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
x_89 = !lean_is_exclusive(x_38);
if (x_89 == 0)
{
return x_38;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_38, 0);
x_91 = lean_ctor_get(x_38, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_38);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
}
}
else
{
uint8_t x_93; 
lean_dec(x_34);
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
x_93 = !lean_is_exclusive(x_35);
if (x_93 == 0)
{
return x_35;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_35, 0);
x_95 = lean_ctor_get(x_35, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_35);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
return x_96;
}
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
}
else
{
lean_object* x_97; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_8);
lean_ctor_set(x_97, 1, x_15);
return x_97;
}
}
else
{
lean_object* x_98; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_8);
lean_ctor_set(x_98, 1, x_15);
return x_98;
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__6;
x_2 = l_List_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__7___lambda__2___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__48;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_List_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__7___lambda__2___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_List_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__7___lambda__2___closed__8;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_List_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__7___lambda__2___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(",", 1);
return x_1;
}
}
static lean_object* _init_l_List_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__7___lambda__2___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(2);
x_2 = l_List_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__7___lambda__2___closed__10;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
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
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
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
x_49 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_49, 0, x_44);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_mk_syntax_ident(x_3);
x_51 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__18;
x_52 = lean_array_push(x_51, x_49);
lean_inc(x_50);
x_53 = lean_array_push(x_52, x_50);
x_54 = lean_box(2);
x_55 = l_List_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__7___lambda__2___closed__6;
x_56 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
lean_ctor_set(x_56, 2, x_53);
x_57 = l_Array_append___rarg(x_21, x_40);
x_58 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__4;
x_59 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_59, 0, x_54);
lean_ctor_set(x_59, 1, x_58);
lean_ctor_set(x_59, 2, x_57);
x_60 = lean_array_push(x_51, x_56);
x_61 = lean_array_push(x_60, x_59);
x_62 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__10;
x_63 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_63, 0, x_54);
lean_ctor_set(x_63, 1, x_62);
lean_ctor_set(x_63, 2, x_61);
lean_inc(x_10);
x_64 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_exprToSyntax___spec__1___rarg(x_10, x_11, x_47);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_67 = lean_st_ref_get(x_11, x_66);
x_68 = lean_ctor_get(x_67, 1);
lean_inc(x_68);
lean_dec(x_67);
x_69 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_69, 0, x_65);
lean_ctor_set(x_69, 1, x_48);
x_70 = lean_array_push(x_51, x_69);
x_71 = lean_array_push(x_70, x_50);
x_72 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_72, 0, x_54);
lean_ctor_set(x_72, 1, x_55);
lean_ctor_set(x_72, 2, x_71);
x_73 = l_Array_append___rarg(x_21, x_41);
x_74 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_74, 0, x_54);
lean_ctor_set(x_74, 1, x_58);
lean_ctor_set(x_74, 2, x_73);
x_75 = lean_array_push(x_51, x_72);
x_76 = lean_array_push(x_75, x_74);
x_77 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_77, 0, x_54);
lean_ctor_set(x_77, 1, x_62);
lean_ctor_set(x_77, 2, x_76);
x_78 = lean_array_push(x_51, x_63);
lean_inc(x_77);
lean_inc(x_78);
x_79 = lean_array_push(x_78, x_77);
lean_inc(x_23);
x_80 = l_Array_append___rarg(x_23, x_79);
lean_inc(x_10);
x_81 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_exprToSyntax___spec__1___rarg(x_10, x_11, x_68);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
x_84 = lean_st_ref_get(x_11, x_83);
x_85 = lean_ctor_get(x_84, 1);
lean_inc(x_85);
lean_dec(x_84);
x_86 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__9;
x_87 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_87, 0, x_82);
lean_ctor_set(x_87, 1, x_86);
x_88 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__10;
x_89 = lean_array_push(x_88, x_87);
x_90 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__8;
x_91 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_91, 0, x_54);
lean_ctor_set(x_91, 1, x_90);
lean_ctor_set(x_91, 2, x_89);
x_92 = lean_array_push(x_78, x_91);
lean_inc(x_23);
x_93 = l_Array_append___rarg(x_23, x_92);
lean_inc(x_10);
x_94 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_exprToSyntax___spec__1___rarg(x_10, x_11, x_85);
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
lean_dec(x_94);
x_97 = lean_st_ref_get(x_11, x_96);
x_98 = lean_ctor_get(x_97, 1);
lean_inc(x_98);
lean_dec(x_97);
x_99 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_99, 0, x_95);
lean_ctor_set(x_99, 1, x_86);
x_100 = lean_array_push(x_88, x_99);
x_101 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_101, 0, x_54);
lean_ctor_set(x_101, 1, x_90);
lean_ctor_set(x_101, 2, x_100);
x_102 = lean_array_push(x_51, x_101);
x_103 = lean_array_push(x_102, x_77);
x_104 = l_Array_append___rarg(x_23, x_103);
lean_inc(x_10);
x_105 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_exprToSyntax___spec__1___rarg(x_10, x_11, x_98);
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
lean_dec(x_105);
x_108 = lean_ctor_get(x_10, 10);
lean_inc(x_108);
x_109 = lean_st_ref_get(x_11, x_107);
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_109, 1);
lean_inc(x_111);
lean_dec(x_109);
x_112 = lean_ctor_get(x_110, 0);
lean_inc(x_112);
lean_dec(x_110);
x_113 = lean_environment_main_module(x_112);
x_114 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__48;
lean_inc(x_108);
x_115 = l_Lean_addMacroScope(x_113, x_114, x_108);
x_116 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__46;
x_117 = l_List_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__7___lambda__2___closed__9;
x_118 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_118, 0, x_106);
lean_ctor_set(x_118, 1, x_116);
lean_ctor_set(x_118, 2, x_115);
lean_ctor_set(x_118, 3, x_117);
lean_inc(x_11);
lean_inc(x_10);
x_119 = lean_apply_8(x_42, x_118, x_6, x_7, x_8, x_9, x_10, x_11, x_111);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; size_t x_130; size_t x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; size_t x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; uint8_t x_180; 
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_119, 1);
lean_inc(x_121);
lean_dec(x_119);
lean_inc(x_10);
x_122 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_exprToSyntax___spec__1___rarg(x_10, x_11, x_121);
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_122, 1);
lean_inc(x_124);
lean_dec(x_122);
x_125 = lean_st_ref_get(x_11, x_124);
x_126 = lean_ctor_get(x_125, 1);
lean_inc(x_126);
lean_dec(x_125);
x_127 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__25;
lean_inc(x_123);
x_128 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_128, 0, x_123);
lean_ctor_set(x_128, 1, x_127);
x_129 = lean_array_get_size(x_80);
x_130 = lean_usize_of_nat(x_129);
lean_dec(x_129);
x_131 = 0;
x_132 = l_Array_mapMUnsafe_map___at___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___spec__3(x_130, x_131, x_80);
x_133 = l_List_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__7___lambda__2___closed__11;
x_134 = l_Lean_mkSepArray(x_132, x_133);
lean_dec(x_132);
x_135 = l_Array_append___rarg(x_21, x_134);
x_136 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_136, 0, x_54);
lean_ctor_set(x_136, 1, x_58);
lean_ctor_set(x_136, 2, x_135);
x_137 = lean_array_push(x_88, x_136);
x_138 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_138, 0, x_54);
lean_ctor_set(x_138, 1, x_58);
lean_ctor_set(x_138, 2, x_137);
x_139 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__35;
x_140 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_140, 0, x_123);
lean_ctor_set(x_140, 1, x_139);
x_141 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__36;
x_142 = lean_array_push(x_141, x_128);
x_143 = lean_array_push(x_142, x_138);
x_144 = lean_array_push(x_143, x_140);
x_145 = lean_array_push(x_144, x_120);
x_146 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__24;
x_147 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_147, 0, x_54);
lean_ctor_set(x_147, 1, x_146);
lean_ctor_set(x_147, 2, x_145);
lean_inc(x_10);
x_148 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_exprToSyntax___spec__1___rarg(x_10, x_11, x_126);
x_149 = lean_ctor_get(x_148, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_148, 1);
lean_inc(x_150);
lean_dec(x_148);
x_151 = lean_st_ref_get(x_11, x_150);
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_151, 1);
lean_inc(x_153);
lean_dec(x_151);
x_154 = lean_ctor_get(x_152, 0);
lean_inc(x_154);
lean_dec(x_152);
x_155 = lean_environment_main_module(x_154);
lean_inc(x_149);
x_156 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_156, 0, x_149);
lean_ctor_set(x_156, 1, x_127);
x_157 = lean_array_get_size(x_93);
x_158 = lean_usize_of_nat(x_157);
lean_dec(x_157);
x_159 = l_Array_mapMUnsafe_map___at___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___spec__3(x_158, x_131, x_93);
x_160 = l_Lean_mkSepArray(x_159, x_133);
lean_dec(x_159);
x_161 = l_Array_append___rarg(x_21, x_160);
x_162 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_162, 0, x_54);
lean_ctor_set(x_162, 1, x_58);
lean_ctor_set(x_162, 2, x_161);
x_163 = lean_array_push(x_88, x_162);
x_164 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_164, 0, x_54);
lean_ctor_set(x_164, 1, x_58);
lean_ctor_set(x_164, 2, x_163);
lean_inc(x_149);
x_165 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_165, 0, x_149);
lean_ctor_set(x_165, 1, x_139);
x_166 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__32;
lean_inc(x_108);
x_167 = l_Lean_addMacroScope(x_155, x_166, x_108);
x_168 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__28;
x_169 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__34;
x_170 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_170, 0, x_149);
lean_ctor_set(x_170, 1, x_168);
lean_ctor_set(x_170, 2, x_167);
lean_ctor_set(x_170, 3, x_169);
x_171 = lean_array_push(x_141, x_156);
x_172 = lean_array_push(x_171, x_164);
x_173 = lean_array_push(x_172, x_165);
x_174 = lean_array_push(x_173, x_170);
x_175 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_175, 0, x_54);
lean_ctor_set(x_175, 1, x_146);
lean_ctor_set(x_175, 2, x_174);
x_176 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_exprToSyntax___spec__1___rarg(x_10, x_11, x_153);
x_177 = lean_ctor_get(x_176, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_176, 1);
lean_inc(x_178);
lean_dec(x_176);
x_179 = lean_st_ref_get(x_11, x_178);
lean_dec(x_11);
x_180 = !lean_is_exclusive(x_179);
if (x_180 == 0)
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; size_t x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_181 = lean_ctor_get(x_179, 0);
x_182 = lean_ctor_get(x_181, 0);
lean_inc(x_182);
lean_dec(x_181);
x_183 = lean_environment_main_module(x_182);
lean_inc(x_177);
x_184 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_184, 0, x_177);
lean_ctor_set(x_184, 1, x_127);
x_185 = lean_array_get_size(x_104);
x_186 = lean_usize_of_nat(x_185);
lean_dec(x_185);
x_187 = l_Array_mapMUnsafe_map___at___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___spec__3(x_186, x_131, x_104);
x_188 = l_Lean_mkSepArray(x_187, x_133);
lean_dec(x_187);
x_189 = l_Array_append___rarg(x_21, x_188);
x_190 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_190, 0, x_54);
lean_ctor_set(x_190, 1, x_58);
lean_ctor_set(x_190, 2, x_189);
x_191 = lean_array_push(x_88, x_190);
x_192 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_192, 0, x_54);
lean_ctor_set(x_192, 1, x_58);
lean_ctor_set(x_192, 2, x_191);
lean_inc(x_177);
x_193 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_193, 0, x_177);
lean_ctor_set(x_193, 1, x_139);
x_194 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__41;
x_195 = l_Lean_addMacroScope(x_183, x_194, x_108);
x_196 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__39;
x_197 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__43;
x_198 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_198, 0, x_177);
lean_ctor_set(x_198, 1, x_196);
lean_ctor_set(x_198, 2, x_195);
lean_ctor_set(x_198, 3, x_197);
x_199 = lean_array_push(x_141, x_184);
x_200 = lean_array_push(x_199, x_192);
x_201 = lean_array_push(x_200, x_193);
x_202 = lean_array_push(x_201, x_198);
x_203 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_203, 0, x_54);
lean_ctor_set(x_203, 1, x_146);
lean_ctor_set(x_203, 2, x_202);
x_204 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__51;
x_205 = lean_array_push(x_204, x_147);
x_206 = lean_array_push(x_205, x_175);
x_207 = lean_array_push(x_206, x_203);
lean_ctor_set(x_179, 0, x_207);
return x_179;
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; size_t x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; 
x_208 = lean_ctor_get(x_179, 0);
x_209 = lean_ctor_get(x_179, 1);
lean_inc(x_209);
lean_inc(x_208);
lean_dec(x_179);
x_210 = lean_ctor_get(x_208, 0);
lean_inc(x_210);
lean_dec(x_208);
x_211 = lean_environment_main_module(x_210);
lean_inc(x_177);
x_212 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_212, 0, x_177);
lean_ctor_set(x_212, 1, x_127);
x_213 = lean_array_get_size(x_104);
x_214 = lean_usize_of_nat(x_213);
lean_dec(x_213);
x_215 = l_Array_mapMUnsafe_map___at___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___spec__3(x_214, x_131, x_104);
x_216 = l_Lean_mkSepArray(x_215, x_133);
lean_dec(x_215);
x_217 = l_Array_append___rarg(x_21, x_216);
x_218 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_218, 0, x_54);
lean_ctor_set(x_218, 1, x_58);
lean_ctor_set(x_218, 2, x_217);
x_219 = lean_array_push(x_88, x_218);
x_220 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_220, 0, x_54);
lean_ctor_set(x_220, 1, x_58);
lean_ctor_set(x_220, 2, x_219);
lean_inc(x_177);
x_221 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_221, 0, x_177);
lean_ctor_set(x_221, 1, x_139);
x_222 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__41;
x_223 = l_Lean_addMacroScope(x_211, x_222, x_108);
x_224 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__39;
x_225 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__43;
x_226 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_226, 0, x_177);
lean_ctor_set(x_226, 1, x_224);
lean_ctor_set(x_226, 2, x_223);
lean_ctor_set(x_226, 3, x_225);
x_227 = lean_array_push(x_141, x_212);
x_228 = lean_array_push(x_227, x_220);
x_229 = lean_array_push(x_228, x_221);
x_230 = lean_array_push(x_229, x_226);
x_231 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_231, 0, x_54);
lean_ctor_set(x_231, 1, x_146);
lean_ctor_set(x_231, 2, x_230);
x_232 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__51;
x_233 = lean_array_push(x_232, x_147);
x_234 = lean_array_push(x_233, x_175);
x_235 = lean_array_push(x_234, x_231);
x_236 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_236, 0, x_235);
lean_ctor_set(x_236, 1, x_209);
return x_236;
}
}
else
{
uint8_t x_237; 
lean_dec(x_108);
lean_dec(x_104);
lean_dec(x_93);
lean_dec(x_80);
lean_dec(x_11);
lean_dec(x_10);
x_237 = !lean_is_exclusive(x_119);
if (x_237 == 0)
{
return x_119;
}
else
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; 
x_238 = lean_ctor_get(x_119, 0);
x_239 = lean_ctor_get(x_119, 1);
lean_inc(x_239);
lean_inc(x_238);
lean_dec(x_119);
x_240 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_240, 0, x_238);
lean_ctor_set(x_240, 1, x_239);
return x_240;
}
}
}
else
{
uint8_t x_241; 
lean_dec(x_23);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
x_241 = !lean_is_exclusive(x_36);
if (x_241 == 0)
{
return x_36;
}
else
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; 
x_242 = lean_ctor_get(x_36, 0);
x_243 = lean_ctor_get(x_36, 1);
lean_inc(x_243);
lean_inc(x_242);
lean_dec(x_36);
x_244 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_244, 0, x_242);
lean_ctor_set(x_244, 1, x_243);
return x_244;
}
}
}
else
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; 
x_245 = lean_ctor_get(x_28, 0);
x_246 = lean_ctor_get(x_28, 1);
lean_inc(x_246);
lean_inc(x_245);
lean_dec(x_28);
x_247 = lean_ctor_get(x_2, 4);
lean_inc(x_247);
lean_dec(x_2);
x_248 = l_List_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__7___lambda__2___closed__4;
x_249 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_249, 0, x_246);
lean_ctor_set(x_249, 1, x_248);
x_250 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_250, 0, x_245);
lean_ctor_set(x_250, 1, x_249);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_247);
x_251 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5(x_4, x_16, x_25, x_247, x_19, x_247, x_20, x_250, x_6, x_7, x_8, x_9, x_10, x_11, x_29);
lean_dec(x_247);
lean_dec(x_25);
lean_dec(x_16);
if (lean_obj_tag(x_251) == 0)
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; 
x_252 = lean_ctor_get(x_251, 0);
lean_inc(x_252);
x_253 = lean_ctor_get(x_252, 1);
lean_inc(x_253);
x_254 = lean_ctor_get(x_251, 1);
lean_inc(x_254);
lean_dec(x_251);
x_255 = lean_ctor_get(x_252, 0);
lean_inc(x_255);
lean_dec(x_252);
x_256 = lean_ctor_get(x_253, 0);
lean_inc(x_256);
x_257 = lean_ctor_get(x_253, 1);
lean_inc(x_257);
lean_dec(x_253);
lean_inc(x_10);
x_258 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_exprToSyntax___spec__1___rarg(x_10, x_11, x_254);
x_259 = lean_ctor_get(x_258, 0);
lean_inc(x_259);
x_260 = lean_ctor_get(x_258, 1);
lean_inc(x_260);
lean_dec(x_258);
x_261 = lean_st_ref_get(x_11, x_260);
x_262 = lean_ctor_get(x_261, 1);
lean_inc(x_262);
lean_dec(x_261);
x_263 = l_List_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__7___lambda__2___closed__7;
x_264 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_264, 0, x_259);
lean_ctor_set(x_264, 1, x_263);
x_265 = lean_mk_syntax_ident(x_3);
x_266 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__18;
x_267 = lean_array_push(x_266, x_264);
lean_inc(x_265);
x_268 = lean_array_push(x_267, x_265);
x_269 = lean_box(2);
x_270 = l_List_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__7___lambda__2___closed__6;
x_271 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_271, 0, x_269);
lean_ctor_set(x_271, 1, x_270);
lean_ctor_set(x_271, 2, x_268);
x_272 = l_Array_append___rarg(x_21, x_255);
x_273 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__4;
x_274 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_274, 0, x_269);
lean_ctor_set(x_274, 1, x_273);
lean_ctor_set(x_274, 2, x_272);
x_275 = lean_array_push(x_266, x_271);
x_276 = lean_array_push(x_275, x_274);
x_277 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__10;
x_278 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_278, 0, x_269);
lean_ctor_set(x_278, 1, x_277);
lean_ctor_set(x_278, 2, x_276);
lean_inc(x_10);
x_279 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_exprToSyntax___spec__1___rarg(x_10, x_11, x_262);
x_280 = lean_ctor_get(x_279, 0);
lean_inc(x_280);
x_281 = lean_ctor_get(x_279, 1);
lean_inc(x_281);
lean_dec(x_279);
x_282 = lean_st_ref_get(x_11, x_281);
x_283 = lean_ctor_get(x_282, 1);
lean_inc(x_283);
lean_dec(x_282);
x_284 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_284, 0, x_280);
lean_ctor_set(x_284, 1, x_263);
x_285 = lean_array_push(x_266, x_284);
x_286 = lean_array_push(x_285, x_265);
x_287 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_287, 0, x_269);
lean_ctor_set(x_287, 1, x_270);
lean_ctor_set(x_287, 2, x_286);
x_288 = l_Array_append___rarg(x_21, x_256);
x_289 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_289, 0, x_269);
lean_ctor_set(x_289, 1, x_273);
lean_ctor_set(x_289, 2, x_288);
x_290 = lean_array_push(x_266, x_287);
x_291 = lean_array_push(x_290, x_289);
x_292 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_292, 0, x_269);
lean_ctor_set(x_292, 1, x_277);
lean_ctor_set(x_292, 2, x_291);
x_293 = lean_array_push(x_266, x_278);
lean_inc(x_292);
lean_inc(x_293);
x_294 = lean_array_push(x_293, x_292);
lean_inc(x_23);
x_295 = l_Array_append___rarg(x_23, x_294);
lean_inc(x_10);
x_296 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_exprToSyntax___spec__1___rarg(x_10, x_11, x_283);
x_297 = lean_ctor_get(x_296, 0);
lean_inc(x_297);
x_298 = lean_ctor_get(x_296, 1);
lean_inc(x_298);
lean_dec(x_296);
x_299 = lean_st_ref_get(x_11, x_298);
x_300 = lean_ctor_get(x_299, 1);
lean_inc(x_300);
lean_dec(x_299);
x_301 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__9;
x_302 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_302, 0, x_297);
lean_ctor_set(x_302, 1, x_301);
x_303 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__10;
x_304 = lean_array_push(x_303, x_302);
x_305 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__8;
x_306 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_306, 0, x_269);
lean_ctor_set(x_306, 1, x_305);
lean_ctor_set(x_306, 2, x_304);
x_307 = lean_array_push(x_293, x_306);
lean_inc(x_23);
x_308 = l_Array_append___rarg(x_23, x_307);
lean_inc(x_10);
x_309 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_exprToSyntax___spec__1___rarg(x_10, x_11, x_300);
x_310 = lean_ctor_get(x_309, 0);
lean_inc(x_310);
x_311 = lean_ctor_get(x_309, 1);
lean_inc(x_311);
lean_dec(x_309);
x_312 = lean_st_ref_get(x_11, x_311);
x_313 = lean_ctor_get(x_312, 1);
lean_inc(x_313);
lean_dec(x_312);
x_314 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_314, 0, x_310);
lean_ctor_set(x_314, 1, x_301);
x_315 = lean_array_push(x_303, x_314);
x_316 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_316, 0, x_269);
lean_ctor_set(x_316, 1, x_305);
lean_ctor_set(x_316, 2, x_315);
x_317 = lean_array_push(x_266, x_316);
x_318 = lean_array_push(x_317, x_292);
x_319 = l_Array_append___rarg(x_23, x_318);
lean_inc(x_10);
x_320 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_exprToSyntax___spec__1___rarg(x_10, x_11, x_313);
x_321 = lean_ctor_get(x_320, 0);
lean_inc(x_321);
x_322 = lean_ctor_get(x_320, 1);
lean_inc(x_322);
lean_dec(x_320);
x_323 = lean_ctor_get(x_10, 10);
lean_inc(x_323);
x_324 = lean_st_ref_get(x_11, x_322);
x_325 = lean_ctor_get(x_324, 0);
lean_inc(x_325);
x_326 = lean_ctor_get(x_324, 1);
lean_inc(x_326);
lean_dec(x_324);
x_327 = lean_ctor_get(x_325, 0);
lean_inc(x_327);
lean_dec(x_325);
x_328 = lean_environment_main_module(x_327);
x_329 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__48;
lean_inc(x_323);
x_330 = l_Lean_addMacroScope(x_328, x_329, x_323);
x_331 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__46;
x_332 = l_List_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__7___lambda__2___closed__9;
x_333 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_333, 0, x_321);
lean_ctor_set(x_333, 1, x_331);
lean_ctor_set(x_333, 2, x_330);
lean_ctor_set(x_333, 3, x_332);
lean_inc(x_11);
lean_inc(x_10);
x_334 = lean_apply_8(x_257, x_333, x_6, x_7, x_8, x_9, x_10, x_11, x_326);
if (lean_obj_tag(x_334) == 0)
{
lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; size_t x_345; size_t x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; size_t x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; size_t x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; 
x_335 = lean_ctor_get(x_334, 0);
lean_inc(x_335);
x_336 = lean_ctor_get(x_334, 1);
lean_inc(x_336);
lean_dec(x_334);
lean_inc(x_10);
x_337 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_exprToSyntax___spec__1___rarg(x_10, x_11, x_336);
x_338 = lean_ctor_get(x_337, 0);
lean_inc(x_338);
x_339 = lean_ctor_get(x_337, 1);
lean_inc(x_339);
lean_dec(x_337);
x_340 = lean_st_ref_get(x_11, x_339);
x_341 = lean_ctor_get(x_340, 1);
lean_inc(x_341);
lean_dec(x_340);
x_342 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__25;
lean_inc(x_338);
x_343 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_343, 0, x_338);
lean_ctor_set(x_343, 1, x_342);
x_344 = lean_array_get_size(x_295);
x_345 = lean_usize_of_nat(x_344);
lean_dec(x_344);
x_346 = 0;
x_347 = l_Array_mapMUnsafe_map___at___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___spec__3(x_345, x_346, x_295);
x_348 = l_List_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__7___lambda__2___closed__11;
x_349 = l_Lean_mkSepArray(x_347, x_348);
lean_dec(x_347);
x_350 = l_Array_append___rarg(x_21, x_349);
x_351 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_351, 0, x_269);
lean_ctor_set(x_351, 1, x_273);
lean_ctor_set(x_351, 2, x_350);
x_352 = lean_array_push(x_303, x_351);
x_353 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_353, 0, x_269);
lean_ctor_set(x_353, 1, x_273);
lean_ctor_set(x_353, 2, x_352);
x_354 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__35;
x_355 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_355, 0, x_338);
lean_ctor_set(x_355, 1, x_354);
x_356 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__36;
x_357 = lean_array_push(x_356, x_343);
x_358 = lean_array_push(x_357, x_353);
x_359 = lean_array_push(x_358, x_355);
x_360 = lean_array_push(x_359, x_335);
x_361 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__24;
x_362 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_362, 0, x_269);
lean_ctor_set(x_362, 1, x_361);
lean_ctor_set(x_362, 2, x_360);
lean_inc(x_10);
x_363 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_exprToSyntax___spec__1___rarg(x_10, x_11, x_341);
x_364 = lean_ctor_get(x_363, 0);
lean_inc(x_364);
x_365 = lean_ctor_get(x_363, 1);
lean_inc(x_365);
lean_dec(x_363);
x_366 = lean_st_ref_get(x_11, x_365);
x_367 = lean_ctor_get(x_366, 0);
lean_inc(x_367);
x_368 = lean_ctor_get(x_366, 1);
lean_inc(x_368);
lean_dec(x_366);
x_369 = lean_ctor_get(x_367, 0);
lean_inc(x_369);
lean_dec(x_367);
x_370 = lean_environment_main_module(x_369);
lean_inc(x_364);
x_371 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_371, 0, x_364);
lean_ctor_set(x_371, 1, x_342);
x_372 = lean_array_get_size(x_308);
x_373 = lean_usize_of_nat(x_372);
lean_dec(x_372);
x_374 = l_Array_mapMUnsafe_map___at___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___spec__3(x_373, x_346, x_308);
x_375 = l_Lean_mkSepArray(x_374, x_348);
lean_dec(x_374);
x_376 = l_Array_append___rarg(x_21, x_375);
x_377 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_377, 0, x_269);
lean_ctor_set(x_377, 1, x_273);
lean_ctor_set(x_377, 2, x_376);
x_378 = lean_array_push(x_303, x_377);
x_379 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_379, 0, x_269);
lean_ctor_set(x_379, 1, x_273);
lean_ctor_set(x_379, 2, x_378);
lean_inc(x_364);
x_380 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_380, 0, x_364);
lean_ctor_set(x_380, 1, x_354);
x_381 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__32;
lean_inc(x_323);
x_382 = l_Lean_addMacroScope(x_370, x_381, x_323);
x_383 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__28;
x_384 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__34;
x_385 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_385, 0, x_364);
lean_ctor_set(x_385, 1, x_383);
lean_ctor_set(x_385, 2, x_382);
lean_ctor_set(x_385, 3, x_384);
x_386 = lean_array_push(x_356, x_371);
x_387 = lean_array_push(x_386, x_379);
x_388 = lean_array_push(x_387, x_380);
x_389 = lean_array_push(x_388, x_385);
x_390 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_390, 0, x_269);
lean_ctor_set(x_390, 1, x_361);
lean_ctor_set(x_390, 2, x_389);
x_391 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_exprToSyntax___spec__1___rarg(x_10, x_11, x_368);
x_392 = lean_ctor_get(x_391, 0);
lean_inc(x_392);
x_393 = lean_ctor_get(x_391, 1);
lean_inc(x_393);
lean_dec(x_391);
x_394 = lean_st_ref_get(x_11, x_393);
lean_dec(x_11);
x_395 = lean_ctor_get(x_394, 0);
lean_inc(x_395);
x_396 = lean_ctor_get(x_394, 1);
lean_inc(x_396);
if (lean_is_exclusive(x_394)) {
 lean_ctor_release(x_394, 0);
 lean_ctor_release(x_394, 1);
 x_397 = x_394;
} else {
 lean_dec_ref(x_394);
 x_397 = lean_box(0);
}
x_398 = lean_ctor_get(x_395, 0);
lean_inc(x_398);
lean_dec(x_395);
x_399 = lean_environment_main_module(x_398);
lean_inc(x_392);
x_400 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_400, 0, x_392);
lean_ctor_set(x_400, 1, x_342);
x_401 = lean_array_get_size(x_319);
x_402 = lean_usize_of_nat(x_401);
lean_dec(x_401);
x_403 = l_Array_mapMUnsafe_map___at___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___spec__3(x_402, x_346, x_319);
x_404 = l_Lean_mkSepArray(x_403, x_348);
lean_dec(x_403);
x_405 = l_Array_append___rarg(x_21, x_404);
x_406 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_406, 0, x_269);
lean_ctor_set(x_406, 1, x_273);
lean_ctor_set(x_406, 2, x_405);
x_407 = lean_array_push(x_303, x_406);
x_408 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_408, 0, x_269);
lean_ctor_set(x_408, 1, x_273);
lean_ctor_set(x_408, 2, x_407);
lean_inc(x_392);
x_409 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_409, 0, x_392);
lean_ctor_set(x_409, 1, x_354);
x_410 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__41;
x_411 = l_Lean_addMacroScope(x_399, x_410, x_323);
x_412 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__39;
x_413 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__43;
x_414 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_414, 0, x_392);
lean_ctor_set(x_414, 1, x_412);
lean_ctor_set(x_414, 2, x_411);
lean_ctor_set(x_414, 3, x_413);
x_415 = lean_array_push(x_356, x_400);
x_416 = lean_array_push(x_415, x_408);
x_417 = lean_array_push(x_416, x_409);
x_418 = lean_array_push(x_417, x_414);
x_419 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_419, 0, x_269);
lean_ctor_set(x_419, 1, x_361);
lean_ctor_set(x_419, 2, x_418);
x_420 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__51;
x_421 = lean_array_push(x_420, x_362);
x_422 = lean_array_push(x_421, x_390);
x_423 = lean_array_push(x_422, x_419);
if (lean_is_scalar(x_397)) {
 x_424 = lean_alloc_ctor(0, 2, 0);
} else {
 x_424 = x_397;
}
lean_ctor_set(x_424, 0, x_423);
lean_ctor_set(x_424, 1, x_396);
return x_424;
}
else
{
lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; 
lean_dec(x_323);
lean_dec(x_319);
lean_dec(x_308);
lean_dec(x_295);
lean_dec(x_11);
lean_dec(x_10);
x_425 = lean_ctor_get(x_334, 0);
lean_inc(x_425);
x_426 = lean_ctor_get(x_334, 1);
lean_inc(x_426);
if (lean_is_exclusive(x_334)) {
 lean_ctor_release(x_334, 0);
 lean_ctor_release(x_334, 1);
 x_427 = x_334;
} else {
 lean_dec_ref(x_334);
 x_427 = lean_box(0);
}
if (lean_is_scalar(x_427)) {
 x_428 = lean_alloc_ctor(1, 2, 0);
} else {
 x_428 = x_427;
}
lean_ctor_set(x_428, 0, x_425);
lean_ctor_set(x_428, 1, x_426);
return x_428;
}
}
else
{
lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; 
lean_dec(x_23);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
x_429 = lean_ctor_get(x_251, 0);
lean_inc(x_429);
x_430 = lean_ctor_get(x_251, 1);
lean_inc(x_430);
if (lean_is_exclusive(x_251)) {
 lean_ctor_release(x_251, 0);
 lean_ctor_release(x_251, 1);
 x_431 = x_251;
} else {
 lean_dec_ref(x_251);
 x_431 = lean_box(0);
}
if (lean_is_scalar(x_431)) {
 x_432 = lean_alloc_ctor(1, 2, 0);
} else {
 x_432 = x_431;
}
lean_ctor_set(x_432, 0, x_429);
lean_ctor_set(x_432, 1, x_430);
return x_432;
}
}
}
else
{
uint8_t x_433; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_433 = !lean_is_exclusive(x_15);
if (x_433 == 0)
{
return x_15;
}
else
{
lean_object* x_434; lean_object* x_435; lean_object* x_436; 
x_434 = lean_ctor_get(x_15, 0);
x_435 = lean_ctor_get(x_15, 1);
lean_inc(x_435);
lean_inc(x_434);
lean_dec(x_15);
x_436 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_436, 0, x_434);
lean_ctor_set(x_436, 1, x_435);
return x_436;
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
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; size_t x_25; size_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_21 = lean_ctor_get(x_19, 0);
lean_dec(x_21);
x_22 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__1;
lean_inc(x_17);
x_23 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_23, 0, x_17);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_array_get_size(x_11);
x_25 = lean_usize_of_nat(x_24);
lean_dec(x_24);
x_26 = 0;
x_27 = l_Array_mapMUnsafe_map___at_Lean_Elab_Deriving_Ord_mkMatch___spec__1(x_25, x_26, x_11);
x_28 = l_List_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__7___lambda__2___closed__11;
x_29 = l_Lean_mkSepArray(x_27, x_28);
lean_dec(x_27);
x_30 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__5;
x_31 = l_Array_append___rarg(x_30, x_29);
x_32 = lean_box(2);
x_33 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__4;
x_34 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
lean_ctor_set(x_34, 2, x_31);
x_35 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__20;
x_36 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_36, 0, x_17);
lean_ctor_set(x_36, 1, x_35);
x_37 = l_Array_append___rarg(x_30, x_14);
x_38 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_38, 0, x_32);
lean_ctor_set(x_38, 1, x_33);
lean_ctor_set(x_38, 2, x_37);
x_39 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__10;
x_40 = lean_array_push(x_39, x_38);
x_41 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__22;
x_42 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_42, 0, x_32);
lean_ctor_set(x_42, 1, x_41);
lean_ctor_set(x_42, 2, x_40);
x_43 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__52;
x_44 = lean_array_push(x_43, x_23);
x_45 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__6;
x_46 = lean_array_push(x_44, x_45);
x_47 = lean_array_push(x_46, x_45);
x_48 = lean_array_push(x_47, x_34);
x_49 = lean_array_push(x_48, x_36);
x_50 = lean_array_push(x_49, x_42);
x_51 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__2;
x_52 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_52, 0, x_32);
lean_ctor_set(x_52, 1, x_51);
lean_ctor_set(x_52, 2, x_50);
lean_ctor_set(x_19, 0, x_52);
return x_19;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; size_t x_57; size_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_53 = lean_ctor_get(x_19, 1);
lean_inc(x_53);
lean_dec(x_19);
x_54 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__1;
lean_inc(x_17);
x_55 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_55, 0, x_17);
lean_ctor_set(x_55, 1, x_54);
x_56 = lean_array_get_size(x_11);
x_57 = lean_usize_of_nat(x_56);
lean_dec(x_56);
x_58 = 0;
x_59 = l_Array_mapMUnsafe_map___at_Lean_Elab_Deriving_Ord_mkMatch___spec__1(x_57, x_58, x_11);
x_60 = l_List_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__7___lambda__2___closed__11;
x_61 = l_Lean_mkSepArray(x_59, x_60);
lean_dec(x_59);
x_62 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__5;
x_63 = l_Array_append___rarg(x_62, x_61);
x_64 = lean_box(2);
x_65 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__4;
x_66 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
lean_ctor_set(x_66, 2, x_63);
x_67 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__20;
x_68 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_68, 0, x_17);
lean_ctor_set(x_68, 1, x_67);
x_69 = l_Array_append___rarg(x_62, x_14);
x_70 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_70, 0, x_64);
lean_ctor_set(x_70, 1, x_65);
lean_ctor_set(x_70, 2, x_69);
x_71 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__10;
x_72 = lean_array_push(x_71, x_70);
x_73 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__22;
x_74 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_74, 0, x_64);
lean_ctor_set(x_74, 1, x_73);
lean_ctor_set(x_74, 2, x_72);
x_75 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__52;
x_76 = lean_array_push(x_75, x_55);
x_77 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__6;
x_78 = lean_array_push(x_76, x_77);
x_79 = lean_array_push(x_78, x_77);
x_80 = lean_array_push(x_79, x_66);
x_81 = lean_array_push(x_80, x_68);
x_82 = lean_array_push(x_81, x_74);
x_83 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__2;
x_84 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_84, 0, x_64);
lean_ctor_set(x_84, 1, x_83);
lean_ctor_set(x_84, 2, x_82);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_53);
return x_85;
}
}
else
{
uint8_t x_86; 
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
x_86 = !lean_is_exclusive(x_13);
if (x_86 == 0)
{
return x_13;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_13, 0);
x_88 = lean_ctor_get(x_13, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_13);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
return x_89;
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__4;
x_2 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("declaration", 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__2;
x_2 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("declModifiers", 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__2;
x_2 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("private", 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__2;
x_2 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__7;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("partial", 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__2;
x_2 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__9;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__52;
x_2 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__6;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__11;
x_2 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__6;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("def", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__2;
x_2 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__13;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("declId", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__2;
x_2 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__15;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("optDeclSig", 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__2;
x_2 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__17;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("typeSpec", 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__6;
x_2 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__19;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__21() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(":", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__29;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__29;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__22;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__30;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__24;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__26() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("declValSimple", 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__2;
x_2 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__26;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__28() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(":=", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__29() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(7u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; uint8_t x_181; 
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
lean_dec(x_1);
x_181 = lean_ctor_get_uint8(x_3, sizeof(void*)*2);
if (x_181 == 0)
{
uint8_t x_182; 
x_182 = lean_ctor_get_uint8(x_4, sizeof(void*)*5);
if (x_182 == 0)
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; uint8_t x_188; 
lean_inc(x_11);
x_183 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_exprToSyntax___spec__1___rarg(x_11, x_12, x_13);
x_184 = lean_ctor_get(x_183, 0);
lean_inc(x_184);
x_185 = lean_ctor_get(x_183, 1);
lean_inc(x_185);
lean_dec(x_183);
x_186 = lean_ctor_get(x_11, 10);
lean_inc(x_186);
lean_dec(x_11);
x_187 = lean_st_ref_get(x_12, x_185);
x_188 = !lean_is_exclusive(x_187);
if (x_188 == 0)
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; 
x_189 = lean_ctor_get(x_187, 0);
x_190 = lean_ctor_get(x_189, 0);
lean_inc(x_190);
lean_dec(x_189);
x_191 = lean_environment_main_module(x_190);
x_192 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__7;
lean_inc(x_184);
x_193 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_193, 0, x_184);
lean_ctor_set(x_193, 1, x_192);
x_194 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__10;
x_195 = lean_array_push(x_194, x_193);
x_196 = lean_box(2);
x_197 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__8;
x_198 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_198, 0, x_196);
lean_ctor_set(x_198, 1, x_197);
lean_ctor_set(x_198, 2, x_195);
x_199 = lean_array_push(x_194, x_198);
x_200 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__4;
x_201 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_201, 0, x_196);
lean_ctor_set(x_201, 1, x_200);
lean_ctor_set(x_201, 2, x_199);
x_202 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__12;
x_203 = lean_array_push(x_202, x_201);
x_204 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__6;
x_205 = lean_array_push(x_203, x_204);
x_206 = lean_array_push(x_205, x_204);
x_207 = lean_array_push(x_206, x_204);
x_208 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__6;
x_209 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_209, 0, x_196);
lean_ctor_set(x_209, 1, x_208);
lean_ctor_set(x_209, 2, x_207);
x_210 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__13;
lean_inc(x_184);
x_211 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_211, 0, x_184);
lean_ctor_set(x_211, 1, x_210);
x_212 = lean_mk_syntax_ident(x_2);
x_213 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__18;
x_214 = lean_array_push(x_213, x_212);
x_215 = lean_array_push(x_214, x_204);
x_216 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__16;
x_217 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_217, 0, x_196);
lean_ctor_set(x_217, 1, x_216);
lean_ctor_set(x_217, 2, x_215);
x_218 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__5;
x_219 = l_Array_append___rarg(x_218, x_14);
x_220 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_220, 0, x_196);
lean_ctor_set(x_220, 1, x_200);
lean_ctor_set(x_220, 2, x_219);
x_221 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__21;
lean_inc(x_184);
x_222 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_222, 0, x_184);
lean_ctor_set(x_222, 1, x_221);
x_223 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__30;
x_224 = l_Lean_addMacroScope(x_191, x_223, x_186);
x_225 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__23;
x_226 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__25;
lean_inc(x_184);
x_227 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_227, 0, x_184);
lean_ctor_set(x_227, 1, x_225);
lean_ctor_set(x_227, 2, x_224);
lean_ctor_set(x_227, 3, x_226);
x_228 = lean_array_push(x_213, x_222);
x_229 = lean_array_push(x_228, x_227);
x_230 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__20;
x_231 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_231, 0, x_196);
lean_ctor_set(x_231, 1, x_230);
lean_ctor_set(x_231, 2, x_229);
x_232 = lean_array_push(x_194, x_231);
x_233 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_233, 0, x_196);
lean_ctor_set(x_233, 1, x_200);
lean_ctor_set(x_233, 2, x_232);
x_234 = lean_array_push(x_213, x_220);
x_235 = lean_array_push(x_234, x_233);
x_236 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__18;
x_237 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_237, 0, x_196);
lean_ctor_set(x_237, 1, x_236);
lean_ctor_set(x_237, 2, x_235);
x_238 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__28;
x_239 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_239, 0, x_184);
lean_ctor_set(x_239, 1, x_238);
x_240 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__51;
x_241 = lean_array_push(x_240, x_239);
x_242 = lean_array_push(x_241, x_5);
x_243 = lean_array_push(x_242, x_204);
x_244 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__27;
x_245 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_245, 0, x_196);
lean_ctor_set(x_245, 1, x_244);
lean_ctor_set(x_245, 2, x_243);
x_246 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__29;
x_247 = lean_array_push(x_246, x_211);
x_248 = lean_array_push(x_247, x_217);
x_249 = lean_array_push(x_248, x_237);
x_250 = lean_array_push(x_249, x_245);
x_251 = lean_array_push(x_250, x_204);
x_252 = lean_array_push(x_251, x_204);
x_253 = lean_array_push(x_252, x_204);
x_254 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__14;
x_255 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_255, 0, x_196);
lean_ctor_set(x_255, 1, x_254);
lean_ctor_set(x_255, 2, x_253);
x_256 = lean_array_push(x_213, x_209);
x_257 = lean_array_push(x_256, x_255);
x_258 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__4;
x_259 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_259, 0, x_196);
lean_ctor_set(x_259, 1, x_258);
lean_ctor_set(x_259, 2, x_257);
lean_ctor_set(x_187, 0, x_259);
return x_187;
}
else
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; 
x_260 = lean_ctor_get(x_187, 0);
x_261 = lean_ctor_get(x_187, 1);
lean_inc(x_261);
lean_inc(x_260);
lean_dec(x_187);
x_262 = lean_ctor_get(x_260, 0);
lean_inc(x_262);
lean_dec(x_260);
x_263 = lean_environment_main_module(x_262);
x_264 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__7;
lean_inc(x_184);
x_265 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_265, 0, x_184);
lean_ctor_set(x_265, 1, x_264);
x_266 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__10;
x_267 = lean_array_push(x_266, x_265);
x_268 = lean_box(2);
x_269 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__8;
x_270 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_270, 0, x_268);
lean_ctor_set(x_270, 1, x_269);
lean_ctor_set(x_270, 2, x_267);
x_271 = lean_array_push(x_266, x_270);
x_272 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__4;
x_273 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_273, 0, x_268);
lean_ctor_set(x_273, 1, x_272);
lean_ctor_set(x_273, 2, x_271);
x_274 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__12;
x_275 = lean_array_push(x_274, x_273);
x_276 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__6;
x_277 = lean_array_push(x_275, x_276);
x_278 = lean_array_push(x_277, x_276);
x_279 = lean_array_push(x_278, x_276);
x_280 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__6;
x_281 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_281, 0, x_268);
lean_ctor_set(x_281, 1, x_280);
lean_ctor_set(x_281, 2, x_279);
x_282 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__13;
lean_inc(x_184);
x_283 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_283, 0, x_184);
lean_ctor_set(x_283, 1, x_282);
x_284 = lean_mk_syntax_ident(x_2);
x_285 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__18;
x_286 = lean_array_push(x_285, x_284);
x_287 = lean_array_push(x_286, x_276);
x_288 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__16;
x_289 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_289, 0, x_268);
lean_ctor_set(x_289, 1, x_288);
lean_ctor_set(x_289, 2, x_287);
x_290 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__5;
x_291 = l_Array_append___rarg(x_290, x_14);
x_292 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_292, 0, x_268);
lean_ctor_set(x_292, 1, x_272);
lean_ctor_set(x_292, 2, x_291);
x_293 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__21;
lean_inc(x_184);
x_294 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_294, 0, x_184);
lean_ctor_set(x_294, 1, x_293);
x_295 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__30;
x_296 = l_Lean_addMacroScope(x_263, x_295, x_186);
x_297 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__23;
x_298 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__25;
lean_inc(x_184);
x_299 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_299, 0, x_184);
lean_ctor_set(x_299, 1, x_297);
lean_ctor_set(x_299, 2, x_296);
lean_ctor_set(x_299, 3, x_298);
x_300 = lean_array_push(x_285, x_294);
x_301 = lean_array_push(x_300, x_299);
x_302 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__20;
x_303 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_303, 0, x_268);
lean_ctor_set(x_303, 1, x_302);
lean_ctor_set(x_303, 2, x_301);
x_304 = lean_array_push(x_266, x_303);
x_305 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_305, 0, x_268);
lean_ctor_set(x_305, 1, x_272);
lean_ctor_set(x_305, 2, x_304);
x_306 = lean_array_push(x_285, x_292);
x_307 = lean_array_push(x_306, x_305);
x_308 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__18;
x_309 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_309, 0, x_268);
lean_ctor_set(x_309, 1, x_308);
lean_ctor_set(x_309, 2, x_307);
x_310 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__28;
x_311 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_311, 0, x_184);
lean_ctor_set(x_311, 1, x_310);
x_312 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__51;
x_313 = lean_array_push(x_312, x_311);
x_314 = lean_array_push(x_313, x_5);
x_315 = lean_array_push(x_314, x_276);
x_316 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__27;
x_317 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_317, 0, x_268);
lean_ctor_set(x_317, 1, x_316);
lean_ctor_set(x_317, 2, x_315);
x_318 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__29;
x_319 = lean_array_push(x_318, x_283);
x_320 = lean_array_push(x_319, x_289);
x_321 = lean_array_push(x_320, x_309);
x_322 = lean_array_push(x_321, x_317);
x_323 = lean_array_push(x_322, x_276);
x_324 = lean_array_push(x_323, x_276);
x_325 = lean_array_push(x_324, x_276);
x_326 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__14;
x_327 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_327, 0, x_268);
lean_ctor_set(x_327, 1, x_326);
lean_ctor_set(x_327, 2, x_325);
x_328 = lean_array_push(x_285, x_281);
x_329 = lean_array_push(x_328, x_327);
x_330 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__4;
x_331 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_331, 0, x_268);
lean_ctor_set(x_331, 1, x_330);
lean_ctor_set(x_331, 2, x_329);
x_332 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_332, 0, x_331);
lean_ctor_set(x_332, 1, x_261);
return x_332;
}
}
else
{
lean_object* x_333; 
x_333 = lean_box(0);
x_15 = x_333;
goto block_180;
}
}
else
{
lean_object* x_334; 
x_334 = lean_box(0);
x_15 = x_334;
goto block_180;
}
block_180:
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
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_environment_main_module(x_23);
x_25 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__7;
lean_inc(x_17);
x_26 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_26, 0, x_17);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__10;
x_28 = lean_array_push(x_27, x_26);
x_29 = lean_box(2);
x_30 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__8;
x_31 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
lean_ctor_set(x_31, 2, x_28);
x_32 = lean_array_push(x_27, x_31);
x_33 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__4;
x_34 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_34, 0, x_29);
lean_ctor_set(x_34, 1, x_33);
lean_ctor_set(x_34, 2, x_32);
x_35 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__9;
lean_inc(x_17);
x_36 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_36, 0, x_17);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_array_push(x_27, x_36);
x_38 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__10;
x_39 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_39, 0, x_29);
lean_ctor_set(x_39, 1, x_38);
lean_ctor_set(x_39, 2, x_37);
x_40 = lean_array_push(x_27, x_39);
x_41 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_41, 0, x_29);
lean_ctor_set(x_41, 1, x_33);
lean_ctor_set(x_41, 2, x_40);
x_42 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__12;
x_43 = lean_array_push(x_42, x_34);
x_44 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__6;
x_45 = lean_array_push(x_43, x_44);
x_46 = lean_array_push(x_45, x_44);
x_47 = lean_array_push(x_46, x_41);
x_48 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__6;
x_49 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_49, 0, x_29);
lean_ctor_set(x_49, 1, x_48);
lean_ctor_set(x_49, 2, x_47);
x_50 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__13;
lean_inc(x_17);
x_51 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_51, 0, x_17);
lean_ctor_set(x_51, 1, x_50);
x_52 = lean_mk_syntax_ident(x_2);
x_53 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__18;
x_54 = lean_array_push(x_53, x_52);
x_55 = lean_array_push(x_54, x_44);
x_56 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__16;
x_57 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_57, 0, x_29);
lean_ctor_set(x_57, 1, x_56);
lean_ctor_set(x_57, 2, x_55);
x_58 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__5;
x_59 = l_Array_append___rarg(x_58, x_14);
x_60 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_60, 0, x_29);
lean_ctor_set(x_60, 1, x_33);
lean_ctor_set(x_60, 2, x_59);
x_61 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__21;
lean_inc(x_17);
x_62 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_62, 0, x_17);
lean_ctor_set(x_62, 1, x_61);
x_63 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__30;
x_64 = l_Lean_addMacroScope(x_24, x_63, x_19);
x_65 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__23;
x_66 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__25;
lean_inc(x_17);
x_67 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_67, 0, x_17);
lean_ctor_set(x_67, 1, x_65);
lean_ctor_set(x_67, 2, x_64);
lean_ctor_set(x_67, 3, x_66);
x_68 = lean_array_push(x_53, x_62);
x_69 = lean_array_push(x_68, x_67);
x_70 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__20;
x_71 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_71, 0, x_29);
lean_ctor_set(x_71, 1, x_70);
lean_ctor_set(x_71, 2, x_69);
x_72 = lean_array_push(x_27, x_71);
x_73 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_73, 0, x_29);
lean_ctor_set(x_73, 1, x_33);
lean_ctor_set(x_73, 2, x_72);
x_74 = lean_array_push(x_53, x_60);
x_75 = lean_array_push(x_74, x_73);
x_76 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__18;
x_77 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_77, 0, x_29);
lean_ctor_set(x_77, 1, x_76);
lean_ctor_set(x_77, 2, x_75);
x_78 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__28;
x_79 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_79, 0, x_17);
lean_ctor_set(x_79, 1, x_78);
x_80 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__51;
x_81 = lean_array_push(x_80, x_79);
x_82 = lean_array_push(x_81, x_5);
x_83 = lean_array_push(x_82, x_44);
x_84 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__27;
x_85 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_85, 0, x_29);
lean_ctor_set(x_85, 1, x_84);
lean_ctor_set(x_85, 2, x_83);
x_86 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__29;
x_87 = lean_array_push(x_86, x_51);
x_88 = lean_array_push(x_87, x_57);
x_89 = lean_array_push(x_88, x_77);
x_90 = lean_array_push(x_89, x_85);
x_91 = lean_array_push(x_90, x_44);
x_92 = lean_array_push(x_91, x_44);
x_93 = lean_array_push(x_92, x_44);
x_94 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__14;
x_95 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_95, 0, x_29);
lean_ctor_set(x_95, 1, x_94);
lean_ctor_set(x_95, 2, x_93);
x_96 = lean_array_push(x_53, x_49);
x_97 = lean_array_push(x_96, x_95);
x_98 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__4;
x_99 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_99, 0, x_29);
lean_ctor_set(x_99, 1, x_98);
lean_ctor_set(x_99, 2, x_97);
lean_ctor_set(x_20, 0, x_99);
return x_20;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_100 = lean_ctor_get(x_20, 0);
x_101 = lean_ctor_get(x_20, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_20);
x_102 = lean_ctor_get(x_100, 0);
lean_inc(x_102);
lean_dec(x_100);
x_103 = lean_environment_main_module(x_102);
x_104 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__7;
lean_inc(x_17);
x_105 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_105, 0, x_17);
lean_ctor_set(x_105, 1, x_104);
x_106 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__10;
x_107 = lean_array_push(x_106, x_105);
x_108 = lean_box(2);
x_109 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__8;
x_110 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
lean_ctor_set(x_110, 2, x_107);
x_111 = lean_array_push(x_106, x_110);
x_112 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__4;
x_113 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_113, 0, x_108);
lean_ctor_set(x_113, 1, x_112);
lean_ctor_set(x_113, 2, x_111);
x_114 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__9;
lean_inc(x_17);
x_115 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_115, 0, x_17);
lean_ctor_set(x_115, 1, x_114);
x_116 = lean_array_push(x_106, x_115);
x_117 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__10;
x_118 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_118, 0, x_108);
lean_ctor_set(x_118, 1, x_117);
lean_ctor_set(x_118, 2, x_116);
x_119 = lean_array_push(x_106, x_118);
x_120 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_120, 0, x_108);
lean_ctor_set(x_120, 1, x_112);
lean_ctor_set(x_120, 2, x_119);
x_121 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__12;
x_122 = lean_array_push(x_121, x_113);
x_123 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__6;
x_124 = lean_array_push(x_122, x_123);
x_125 = lean_array_push(x_124, x_123);
x_126 = lean_array_push(x_125, x_120);
x_127 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__6;
x_128 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_128, 0, x_108);
lean_ctor_set(x_128, 1, x_127);
lean_ctor_set(x_128, 2, x_126);
x_129 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__13;
lean_inc(x_17);
x_130 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_130, 0, x_17);
lean_ctor_set(x_130, 1, x_129);
x_131 = lean_mk_syntax_ident(x_2);
x_132 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__18;
x_133 = lean_array_push(x_132, x_131);
x_134 = lean_array_push(x_133, x_123);
x_135 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__16;
x_136 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_136, 0, x_108);
lean_ctor_set(x_136, 1, x_135);
lean_ctor_set(x_136, 2, x_134);
x_137 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__5;
x_138 = l_Array_append___rarg(x_137, x_14);
x_139 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_139, 0, x_108);
lean_ctor_set(x_139, 1, x_112);
lean_ctor_set(x_139, 2, x_138);
x_140 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__21;
lean_inc(x_17);
x_141 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_141, 0, x_17);
lean_ctor_set(x_141, 1, x_140);
x_142 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__30;
x_143 = l_Lean_addMacroScope(x_103, x_142, x_19);
x_144 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__23;
x_145 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__25;
lean_inc(x_17);
x_146 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_146, 0, x_17);
lean_ctor_set(x_146, 1, x_144);
lean_ctor_set(x_146, 2, x_143);
lean_ctor_set(x_146, 3, x_145);
x_147 = lean_array_push(x_132, x_141);
x_148 = lean_array_push(x_147, x_146);
x_149 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__20;
x_150 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_150, 0, x_108);
lean_ctor_set(x_150, 1, x_149);
lean_ctor_set(x_150, 2, x_148);
x_151 = lean_array_push(x_106, x_150);
x_152 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_152, 0, x_108);
lean_ctor_set(x_152, 1, x_112);
lean_ctor_set(x_152, 2, x_151);
x_153 = lean_array_push(x_132, x_139);
x_154 = lean_array_push(x_153, x_152);
x_155 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__18;
x_156 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_156, 0, x_108);
lean_ctor_set(x_156, 1, x_155);
lean_ctor_set(x_156, 2, x_154);
x_157 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__28;
x_158 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_158, 0, x_17);
lean_ctor_set(x_158, 1, x_157);
x_159 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__51;
x_160 = lean_array_push(x_159, x_158);
x_161 = lean_array_push(x_160, x_5);
x_162 = lean_array_push(x_161, x_123);
x_163 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__27;
x_164 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_164, 0, x_108);
lean_ctor_set(x_164, 1, x_163);
lean_ctor_set(x_164, 2, x_162);
x_165 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__29;
x_166 = lean_array_push(x_165, x_130);
x_167 = lean_array_push(x_166, x_136);
x_168 = lean_array_push(x_167, x_156);
x_169 = lean_array_push(x_168, x_164);
x_170 = lean_array_push(x_169, x_123);
x_171 = lean_array_push(x_170, x_123);
x_172 = lean_array_push(x_171, x_123);
x_173 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__14;
x_174 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_174, 0, x_108);
lean_ctor_set(x_174, 1, x_173);
lean_ctor_set(x_174, 2, x_172);
x_175 = lean_array_push(x_132, x_128);
x_176 = lean_array_push(x_175, x_174);
x_177 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__4;
x_178 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_178, 0, x_108);
lean_ctor_set(x_178, 1, x_177);
lean_ctor_set(x_178, 2, x_176);
x_179 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_179, 0, x_178);
lean_ctor_set(x_179, 1, x_101);
return x_179;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Ord_mkAuxFunction(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
x_11 = l_Lean_instInhabitedName;
x_12 = lean_array_get(x_11, x_10, x_2);
lean_dec(x_10);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
x_14 = l_Lean_instInhabitedInductiveVal;
x_15 = lean_array_get(x_14, x_13, x_2);
lean_dec(x_2);
lean_dec(x_13);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_15);
x_16 = l_Lean_Elab_Deriving_Ord_mkOrdHeader(x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_15);
lean_inc(x_17);
x_19 = l_Lean_Elab_Deriving_Ord_mkMatch(x_17, x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_18);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
if (x_20 == 0)
{
uint8_t x_21; 
x_21 = lean_ctor_get_uint8(x_15, sizeof(void*)*5);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_19, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_19, 1);
lean_inc(x_23);
lean_dec(x_19);
x_24 = lean_box(0);
x_25 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1(x_17, x_12, x_1, x_15, x_22, x_24, x_3, x_4, x_5, x_6, x_7, x_8, x_23);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_15);
lean_dec(x_1);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_19, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_19, 1);
lean_inc(x_27);
lean_dec(x_19);
x_28 = lean_ctor_get(x_17, 1);
lean_inc(x_28);
x_29 = l_Lean_Elab_Deriving_Ord_mkOrdHeader___closed__2;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_30 = l_Lean_Elab_Deriving_mkLocalInstanceLetDecls(x_1, x_29, x_28, x_3, x_4, x_5, x_6, x_7, x_8, x_27);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_33 = l_Lean_Elab_Deriving_mkLet(x_31, x_26, x_3, x_4, x_5, x_6, x_7, x_8, x_32);
lean_dec(x_31);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_box(0);
x_37 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1(x_17, x_12, x_1, x_15, x_34, x_36, x_3, x_4, x_5, x_6, x_7, x_8, x_35);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_15);
lean_dec(x_1);
return x_37;
}
else
{
uint8_t x_38; 
lean_dec(x_26);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_30);
if (x_38 == 0)
{
return x_30;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_30, 0);
x_40 = lean_ctor_get(x_30, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_30);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_42 = lean_ctor_get(x_19, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_19, 1);
lean_inc(x_43);
lean_dec(x_19);
x_44 = lean_ctor_get(x_17, 1);
lean_inc(x_44);
x_45 = l_Lean_Elab_Deriving_Ord_mkOrdHeader___closed__2;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_46 = l_Lean_Elab_Deriving_mkLocalInstanceLetDecls(x_1, x_45, x_44, x_3, x_4, x_5, x_6, x_7, x_8, x_43);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_49 = l_Lean_Elab_Deriving_mkLet(x_47, x_42, x_3, x_4, x_5, x_6, x_7, x_8, x_48);
lean_dec(x_47);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = lean_box(0);
x_53 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1(x_17, x_12, x_1, x_15, x_50, x_52, x_3, x_4, x_5, x_6, x_7, x_8, x_51);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_15);
lean_dec(x_1);
return x_53;
}
else
{
uint8_t x_54; 
lean_dec(x_42);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_54 = !lean_is_exclusive(x_46);
if (x_54 == 0)
{
return x_46;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_46, 0);
x_56 = lean_ctor_get(x_46, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_46);
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
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_58 = !lean_is_exclusive(x_19);
if (x_58 == 0)
{
return x_19;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_19, 0);
x_60 = lean_ctor_get(x_19, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_19);
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
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_62 = !lean_is_exclusive(x_16);
if (x_62 == 0)
{
return x_16;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_16, 0);
x_64 = lean_ctor_get(x_16, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_16);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__2;
x_2 = l_Lean_Elab_Deriving_Ord_mkMutualBlock___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
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
static lean_object* _init_l_Lean_Elab_Deriving_Ord_mkMutualBlock___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(2);
x_2 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__4;
x_3 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__5;
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_Ord_mkMutualBlock___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(5u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
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
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_22 = lean_ctor_get(x_20, 0);
lean_dec(x_22);
x_23 = l_Lean_Elab_Deriving_Ord_mkMutualBlock___closed__1;
lean_inc(x_18);
x_24 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_24, 0, x_18);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Array_append___rarg(x_13, x_15);
x_26 = lean_box(2);
x_27 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__4;
x_28 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
lean_ctor_set(x_28, 2, x_25);
x_29 = l_Lean_Elab_Deriving_Ord_mkMutualBlock___closed__3;
x_30 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_30, 0, x_18);
lean_ctor_set(x_30, 1, x_29);
x_31 = l_Lean_Elab_Deriving_Ord_mkMutualBlock___closed__5;
x_32 = lean_array_push(x_31, x_24);
x_33 = lean_array_push(x_32, x_28);
x_34 = lean_array_push(x_33, x_30);
x_35 = l_Lean_Elab_Deriving_Ord_mkMutualBlock___closed__4;
x_36 = lean_array_push(x_34, x_35);
x_37 = lean_array_push(x_36, x_35);
x_38 = l_Lean_Elab_Deriving_Ord_mkMutualBlock___closed__2;
x_39 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_39, 0, x_26);
lean_ctor_set(x_39, 1, x_38);
lean_ctor_set(x_39, 2, x_37);
lean_ctor_set(x_20, 0, x_39);
return x_20;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_40 = lean_ctor_get(x_20, 1);
lean_inc(x_40);
lean_dec(x_20);
x_41 = l_Lean_Elab_Deriving_Ord_mkMutualBlock___closed__1;
lean_inc(x_18);
x_42 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_42, 0, x_18);
lean_ctor_set(x_42, 1, x_41);
x_43 = l_Array_append___rarg(x_13, x_15);
x_44 = lean_box(2);
x_45 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__4;
x_46 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
lean_ctor_set(x_46, 2, x_43);
x_47 = l_Lean_Elab_Deriving_Ord_mkMutualBlock___closed__3;
x_48 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_48, 0, x_18);
lean_ctor_set(x_48, 1, x_47);
x_49 = l_Lean_Elab_Deriving_Ord_mkMutualBlock___closed__5;
x_50 = lean_array_push(x_49, x_42);
x_51 = lean_array_push(x_50, x_46);
x_52 = lean_array_push(x_51, x_48);
x_53 = l_Lean_Elab_Deriving_Ord_mkMutualBlock___closed__4;
x_54 = lean_array_push(x_52, x_53);
x_55 = lean_array_push(x_54, x_53);
x_56 = l_Lean_Elab_Deriving_Ord_mkMutualBlock___closed__2;
x_57 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_57, 0, x_44);
lean_ctor_set(x_57, 1, x_56);
lean_ctor_set(x_57, 2, x_55);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_40);
return x_58;
}
}
else
{
uint8_t x_59; 
lean_dec(x_7);
lean_dec(x_6);
x_59 = !lean_is_exclusive(x_14);
if (x_59 == 0)
{
return x_14;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_14, 0);
x_61 = lean_ctor_get(x_14, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_14);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
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
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Elab", 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__2;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__3;
x_2 = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__4;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__5;
x_2 = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("\n", 1);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__7;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("", 0);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__9;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = l_Lean_instInhabitedName;
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_array_get(x_9, x_1, x_10);
x_12 = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__1;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_13 = l_Lean_Elab_Deriving_mkContext(x_12, x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_14);
x_16 = l_Lean_Elab_Deriving_Ord_mkMutualBlock(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_Elab_Deriving_Ord_mkOrdHeader___closed__2;
x_20 = 1;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_21 = l_Lean_Elab_Deriving_mkInstanceCmds(x_14, x_19, x_1, x_20, x_2, x_3, x_4, x_5, x_6, x_7, x_18);
lean_dec(x_14);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_24 = x_21;
} else {
 lean_dec_ref(x_21);
 x_24 = lean_box(0);
}
x_25 = l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__10;
x_26 = lean_array_push(x_25, x_17);
x_27 = l_Array_append___rarg(x_26, x_22);
x_28 = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__6;
x_46 = lean_st_ref_get(x_7, x_23);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_47, 3);
lean_inc(x_48);
lean_dec(x_47);
x_49 = lean_ctor_get_uint8(x_48, sizeof(void*)*1);
lean_dec(x_48);
if (x_49 == 0)
{
lean_object* x_50; uint8_t x_51; 
x_50 = lean_ctor_get(x_46, 1);
lean_inc(x_50);
lean_dec(x_46);
x_51 = 0;
x_29 = x_51;
x_30 = x_50;
goto block_45;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_52 = lean_ctor_get(x_46, 1);
lean_inc(x_52);
lean_dec(x_46);
x_53 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__2(x_28, x_2, x_3, x_4, x_5, x_6, x_7, x_52);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = lean_unbox(x_54);
lean_dec(x_54);
x_29 = x_56;
x_30 = x_55;
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
if (lean_is_scalar(x_24)) {
 x_31 = lean_alloc_ctor(0, 2, 0);
} else {
 x_31 = x_24;
}
lean_ctor_set(x_31, 0, x_27);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
lean_dec(x_24);
lean_inc(x_27);
x_32 = lean_array_to_list(lean_box(0), x_27);
x_33 = lean_box(0);
x_34 = l_List_mapTRAux___at___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___spec__1(x_32, x_33);
x_35 = l_Lean_MessageData_ofList(x_34);
lean_dec(x_34);
x_36 = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__8;
x_37 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
x_38 = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__10;
x_39 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = l_Lean_addTrace___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__1(x_28, x_39, x_2, x_3, x_4, x_5, x_6, x_7, x_30);
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
uint8_t x_57; 
lean_dec(x_17);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_57 = !lean_is_exclusive(x_21);
if (x_57 == 0)
{
return x_21;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_21, 0);
x_59 = lean_ctor_get(x_21, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_21);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
else
{
uint8_t x_61; 
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_61 = !lean_is_exclusive(x_16);
if (x_61 == 0)
{
return x_16;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_16, 0);
x_63 = lean_ctor_get(x_16, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_16);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
else
{
uint8_t x_65; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_65 = !lean_is_exclusive(x_13);
if (x_65 == 0)
{
return x_13;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_13, 0);
x_67 = lean_ctor_get(x_13, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_13);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
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
lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_74; uint8_t x_75; 
x_5 = lean_array_get_size(x_1);
x_74 = lean_unsigned_to_nat(0u);
x_75 = lean_nat_dec_lt(x_74, x_5);
if (x_75 == 0)
{
uint8_t x_76; 
x_76 = 1;
x_6 = x_76;
x_7 = x_4;
goto block_73;
}
else
{
uint8_t x_77; 
x_77 = lean_nat_dec_le(x_5, x_5);
if (x_77 == 0)
{
uint8_t x_78; 
x_78 = 1;
x_6 = x_78;
x_7 = x_4;
goto block_73;
}
else
{
size_t x_79; size_t x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; 
x_79 = 0;
x_80 = lean_usize_of_nat(x_5);
x_81 = l_Array_anyMUnsafe_any___at_Lean_Elab_Deriving_Ord_mkOrdInstanceHandler___spec__2(x_1, x_79, x_80, x_2, x_3, x_4);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_unbox(x_82);
lean_dec(x_82);
if (x_83 == 0)
{
lean_object* x_84; uint8_t x_85; 
x_84 = lean_ctor_get(x_81, 1);
lean_inc(x_84);
lean_dec(x_81);
x_85 = 1;
x_6 = x_85;
x_7 = x_84;
goto block_73;
}
else
{
lean_object* x_86; uint8_t x_87; 
x_86 = lean_ctor_get(x_81, 1);
lean_inc(x_86);
lean_dec(x_81);
x_87 = 0;
x_6 = x_87;
x_7 = x_86;
goto block_73;
}
}
}
block_73:
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
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_box(0);
x_17 = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___boxed), 8, 1);
lean_closure_set(x_17, 0, x_1);
lean_inc(x_2);
x_18 = l_Lean_Elab_Command_liftTermElabM___rarg(x_16, x_17, x_2, x_3, x_7);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_18, 1);
x_22 = lean_array_get_size(x_20);
x_23 = lean_nat_dec_lt(x_11, x_22);
if (x_23 == 0)
{
uint8_t x_24; lean_object* x_25; 
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_3);
lean_dec(x_2);
x_24 = 1;
x_25 = lean_box(x_24);
lean_ctor_set(x_18, 0, x_25);
return x_18;
}
else
{
uint8_t x_26; 
x_26 = lean_nat_dec_le(x_22, x_22);
if (x_26 == 0)
{
uint8_t x_27; lean_object* x_28; 
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_3);
lean_dec(x_2);
x_27 = 1;
x_28 = lean_box(x_27);
lean_ctor_set(x_18, 0, x_28);
return x_18;
}
else
{
size_t x_29; size_t x_30; lean_object* x_31; lean_object* x_32; 
lean_free_object(x_18);
x_29 = 0;
x_30 = lean_usize_of_nat(x_22);
lean_dec(x_22);
x_31 = lean_box(0);
x_32 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabCommand___spec__16(x_20, x_29, x_30, x_31, x_2, x_3, x_21);
lean_dec(x_20);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; uint8_t x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_32, 0);
lean_dec(x_34);
x_35 = 1;
x_36 = lean_box(x_35);
lean_ctor_set(x_32, 0, x_36);
return x_32;
}
else
{
lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_32, 1);
lean_inc(x_37);
lean_dec(x_32);
x_38 = 1;
x_39 = lean_box(x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_37);
return x_40;
}
}
else
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_32);
if (x_41 == 0)
{
return x_32;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_32, 0);
x_43 = lean_ctor_get(x_32, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_32);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_45 = lean_ctor_get(x_18, 0);
x_46 = lean_ctor_get(x_18, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_18);
x_47 = lean_array_get_size(x_45);
x_48 = lean_nat_dec_lt(x_11, x_47);
if (x_48 == 0)
{
uint8_t x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_47);
lean_dec(x_45);
lean_dec(x_3);
lean_dec(x_2);
x_49 = 1;
x_50 = lean_box(x_49);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_46);
return x_51;
}
else
{
uint8_t x_52; 
x_52 = lean_nat_dec_le(x_47, x_47);
if (x_52 == 0)
{
uint8_t x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_47);
lean_dec(x_45);
lean_dec(x_3);
lean_dec(x_2);
x_53 = 1;
x_54 = lean_box(x_53);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_46);
return x_55;
}
else
{
size_t x_56; size_t x_57; lean_object* x_58; lean_object* x_59; 
x_56 = 0;
x_57 = lean_usize_of_nat(x_47);
lean_dec(x_47);
x_58 = lean_box(0);
x_59 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabCommand___spec__16(x_45, x_56, x_57, x_58, x_2, x_3, x_46);
lean_dec(x_45);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; uint8_t x_62; lean_object* x_63; lean_object* x_64; 
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
x_62 = 1;
x_63 = lean_box(x_62);
if (lean_is_scalar(x_61)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_61;
}
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_60);
return x_64;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_65 = lean_ctor_get(x_59, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_59, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_67 = x_59;
} else {
 lean_dec_ref(x_59);
 x_67 = lean_box(0);
}
if (lean_is_scalar(x_67)) {
 x_68 = lean_alloc_ctor(1, 2, 0);
} else {
 x_68 = x_67;
}
lean_ctor_set(x_68, 0, x_65);
lean_ctor_set(x_68, 1, x_66);
return x_68;
}
}
}
}
}
else
{
uint8_t x_69; 
lean_dec(x_3);
lean_dec(x_2);
x_69 = !lean_is_exclusive(x_18);
if (x_69 == 0)
{
return x_18;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_18, 0);
x_71 = lean_ctor_get(x_18, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_18);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
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
static lean_object* _init_l_Lean_Elab_Deriving_Ord_initFn____x40_Lean_Elab_Deriving_Ord___hyg_2936____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Deriving_Ord_mkOrdInstanceHandler), 4, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Ord_initFn____x40_Lean_Elab_Deriving_Ord___hyg_2936_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Elab_Deriving_Ord_mkOrdHeader___closed__2;
x_3 = l_Lean_Elab_Deriving_Ord_initFn____x40_Lean_Elab_Deriving_Ord___hyg_2936____closed__1;
x_4 = l_Lean_Elab_registerBuiltinDerivingHandler(x_2, x_3, x_1);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__6;
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
l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__7 = _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__7();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__7);
l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__8 = _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__8();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__8);
l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__9 = _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__9();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__9);
l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__10 = _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__10();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__3___closed__10);
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
l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__48 = _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__48();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__48);
l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__49 = _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__49();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__49);
l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__50 = _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__50();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__50);
l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__51 = _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__51();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__51);
l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__52 = _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__52();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___lambda__1___closed__52);
l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___closed__1 = _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___closed__1();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___closed__1);
l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___closed__2 = _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___closed__2();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___closed__2);
l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___closed__3 = _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___closed__3();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___closed__3);
l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___closed__4 = _init_l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___closed__4();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Elab_Deriving_Ord_mkMatch_mkAlts___spec__5___closed__4);
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
l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__28 = _init_l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__28();
lean_mark_persistent(l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__28);
l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__29 = _init_l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__29();
lean_mark_persistent(l_Lean_Elab_Deriving_Ord_mkAuxFunction___lambda__1___closed__29);
l_Lean_Elab_Deriving_Ord_mkMutualBlock___closed__1 = _init_l_Lean_Elab_Deriving_Ord_mkMutualBlock___closed__1();
lean_mark_persistent(l_Lean_Elab_Deriving_Ord_mkMutualBlock___closed__1);
l_Lean_Elab_Deriving_Ord_mkMutualBlock___closed__2 = _init_l_Lean_Elab_Deriving_Ord_mkMutualBlock___closed__2();
lean_mark_persistent(l_Lean_Elab_Deriving_Ord_mkMutualBlock___closed__2);
l_Lean_Elab_Deriving_Ord_mkMutualBlock___closed__3 = _init_l_Lean_Elab_Deriving_Ord_mkMutualBlock___closed__3();
lean_mark_persistent(l_Lean_Elab_Deriving_Ord_mkMutualBlock___closed__3);
l_Lean_Elab_Deriving_Ord_mkMutualBlock___closed__4 = _init_l_Lean_Elab_Deriving_Ord_mkMutualBlock___closed__4();
lean_mark_persistent(l_Lean_Elab_Deriving_Ord_mkMutualBlock___closed__4);
l_Lean_Elab_Deriving_Ord_mkMutualBlock___closed__5 = _init_l_Lean_Elab_Deriving_Ord_mkMutualBlock___closed__5();
lean_mark_persistent(l_Lean_Elab_Deriving_Ord_mkMutualBlock___closed__5);
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
l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__10 = _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__10();
lean_mark_persistent(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__10);
l_Lean_Elab_Deriving_Ord_initFn____x40_Lean_Elab_Deriving_Ord___hyg_2936____closed__1 = _init_l_Lean_Elab_Deriving_Ord_initFn____x40_Lean_Elab_Deriving_Ord___hyg_2936____closed__1();
lean_mark_persistent(l_Lean_Elab_Deriving_Ord_initFn____x40_Lean_Elab_Deriving_Ord___hyg_2936____closed__1);
res = l_Lean_Elab_Deriving_Ord_initFn____x40_Lean_Elab_Deriving_Ord___hyg_2936_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
