// Lean compiler output
// Module: Init.Lean.Elaborator.PreTerm
// Imports: Init.Lean.Elaborator.Basic
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
lean_object* l___regBuiltinTermElab_Lean_Elab_convertId(lean_object*);
lean_object* l_Lean_mkPreTypeAscription___closed__3;
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Elaborator_PreTerm_4__processBinder___spec__1___closed__2;
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinPreTermElab(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_convertSorry___closed__1;
lean_object* l_Lean_registerBuiltinPreTermElabAttr___closed__2;
lean_object* l___regBuiltinTermElab_Lean_Elab_convertSorry(lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Elaborator_PreTerm_4__processBinder___spec__1___closed__4;
lean_object* l_Lean_registerBuiltinPreTermElabAttr___closed__3;
uint8_t l_Lean_Name_beq___main(lean_object*, lean_object*);
lean_object* l_Lean_registerBuiltinPreTermElabAttr___closed__5;
lean_object* lean_local_ctx_find_from_user_name(lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Elaborator_PreTerm_4__processBinder___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getKind___rarg(lean_object*);
lean_object* l_HashMapImp_find___at_Lean_Elab_toPreTerm___spec__1(lean_object*, lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* l_Lean_mkAsPattern___closed__1;
lean_object* l_Lean_Format_pretty(lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_convertHole(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkLevelMax(lean_object*, lean_object*);
lean_object* l_Lean_Elab_runIOUnsafe___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_IO_println___at_HasRepr_HasEval___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_builtinPreTermElabTable;
lean_object* l_Lean_Elab_convertType___rarg(lean_object*);
lean_object* l___private_Init_Lean_Elaborator_PreTerm_3__mkLocalAux___boxed(lean_object*);
lean_object* l___private_Init_Lean_Elaborator_PreTerm_1__setPos___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_mkForall(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_convertId___closed__1;
lean_object* l_Lean_Elab_convertSorry___rarg___closed__3;
lean_object* l_Lean_registerBuiltinPreTermElabAttr___lambda__1___closed__4;
lean_object* l_Lean_Elab_convertHole___rarg(lean_object*);
extern lean_object* l_Lean_AttributeImpl_inhabited___closed__5;
lean_object* l___private_Init_Lean_Elaborator_PreTerm_4__processBinder___closed__1;
lean_object* l___regBuiltinTermElab_Lean_Elab_convertHole___closed__3;
lean_object* l_Lean_mkApp(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Level_addLit___elambda__1___closed__1;
lean_object* l_HashMapImp_insert___at_Lean_addBuiltinPreTermElab___spec__3(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_addBuiltinTermElab___closed__2;
extern lean_object* l_Lean_Parser_Term_binderDefault___elambda__1___rarg___closed__1;
lean_object* l_Lean_mkBuiltinPreTermElabTable___closed__1;
lean_object* l_Lean_Elab_mkLocalDecl(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Elab_convertProp___rarg(lean_object*);
lean_object* l___private_Init_Lean_Elaborator_PreTerm_2__mkHoleFor(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_formatStx___main___rarg(lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_convertSort___closed__3;
lean_object* l_Lean_registerAttribute(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Level_paren___elambda__1___rarg___closed__1;
lean_object* l_Lean_Elab_logError___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Elaborator_PreTerm_4__processBinder___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_convertSortApp___closed__2;
lean_object* l___regBuiltinTermElab_Lean_Elab_convertSortApp___closed__1;
lean_object* l_Lean_registerBuiltinPreTermElabAttr___closed__7;
lean_object* l___regBuiltinTermElab_Lean_Elab_convertId___closed__3;
lean_object* l_Lean_Elab_convertSort___boxed(lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_convertType___closed__5;
lean_object* l_Lean_mkPreTypeAscriptionIfSome(lean_object*, lean_object*);
lean_object* l_Lean_Elab_convertId(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_toLevel___main___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_nameToExprAux___main___closed__1;
lean_object* l_Lean_KVMap_setNat(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_toLevel___main___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_convertType(lean_object*, lean_object*);
lean_object* l_Lean_Elab_convertForall(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Name_toStringWithSep___main(lean_object*, lean_object*);
lean_object* l_Lean_mkPreTypeAscription___closed__1;
extern lean_object* l_Lean_mkInitAttr___lambda__1___closed__1;
lean_object* l___private_Init_Lean_Elaborator_PreTerm_1__setPos___closed__2;
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_toLevel___main___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_Elaborator_PreTerm_5__processBinders___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_AssocList_contains___main___at_Lean_addBuiltinPreTermElab___spec__2(lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_convertProp___closed__1;
lean_object* l_Lean_mkMVar(lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_convertForall___closed__1;
extern lean_object* l_Lean_Parser_Term_sorry___elambda__1___rarg___closed__2;
lean_object* lean_io_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_registerBuiltinPreTermElabAttr___closed__4;
lean_object* l___regBuiltinTermElab_Lean_Elab_convertSortApp___closed__3;
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_mkPreTypeAscription___closed__2;
lean_object* l_Lean_Elab_toLevel___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_toPreTerm___closed__2;
lean_object* l_Lean_Elab_toLevel___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_declareBuiltinPreTermElab___closed__2;
lean_object* l___regBuiltinTermElab_Lean_Elab_convertType___closed__1;
lean_object* l_Lean_Level_ofNat___main(lean_object*);
lean_object* l_AssocList_find___main___at_Lean_Elab_toPreTerm___spec__2(lean_object*, lean_object*);
lean_object* l_IO_Prim_Ref_get___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_convertType___closed__3;
lean_object* l___regBuiltinTermElab_Lean_Elab_convertSort___closed__2;
lean_object* l_Lean_registerBuiltinPreTermElabAttr___lambda__1___closed__3;
lean_object* l_Lean_declareBuiltinPreTermElab___closed__1;
lean_object* l_mkHashMap___at_Lean_mkBuiltinPreTermElabTable___spec__1(lean_object*);
lean_object* l_Lean_mkAsPattern___closed__2;
lean_object* l_Lean_Elab_convertHole(lean_object*, lean_object*);
extern lean_object* l_Lean_AttributeImpl_inhabited___closed__4;
lean_object* l_Lean_oldElaborateAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTagAttribute___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_convertId___closed__2;
lean_object* l___private_Init_Lean_Elaborator_PreTerm_1__setPos___closed__1;
lean_object* l_Lean_registerBuiltinPreTermElabAttr___closed__1;
lean_object* l_HashMapImp_find___at_Lean_Elab_toPreTerm___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_registerBuiltinPreTermElabAttr(lean_object*);
lean_object* l_Lean_Elab_convertSort(lean_object*, lean_object*);
lean_object* l_Lean_mkAsPattern(lean_object*, lean_object*);
size_t lean_name_hash_usize(lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_Elab_toPreTerm___closed__1;
lean_object* l___private_Init_Lean_Elaborator_PreTerm_1__setPos___closed__3;
lean_object* l_Lean_Elab_localContext___rarg(lean_object*);
lean_object* lean_old_elaborate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg___rarg(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Level_num___elambda__1___rarg___closed__1;
lean_object* l_Lean_Elab_toLevel___main___closed__2;
extern lean_object* l_Lean_Parser_Term_prop___elambda__1___rarg___closed__2;
lean_object* l_Lean_mkSort(lean_object*);
lean_object* l_Lean_Elab_convertSortApp(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_hole___elambda__1___rarg___closed__1;
lean_object* l_Lean_registerBuiltinPreTermElabAttr___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* l_Lean_KVMap_setName(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_sort___elambda__1___rarg___closed__2;
uint8_t l_Lean_Syntax_isOfKind___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_convertHole___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_Inhabited;
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Elaborator_PreTerm_4__processBinder___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_type___elambda__1___rarg___closed__2;
extern lean_object* l_Lean_Level_LevelToFormat_Result_format___main___closed__5;
lean_object* l_Lean_registerBuiltinPreTermElabAttr___lambda__1___closed__1;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_HashMapImp_contains___at_Lean_addBuiltinPreTermElab___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs___rarg(lean_object*);
extern lean_object* l_Char_HasRepr___closed__1;
lean_object* l_Lean_mkPreTypeAscription(lean_object*, lean_object*);
extern lean_object* l_Lean_addBuiltinTermElab___closed__1;
lean_object* l___regBuiltinTermElab_Lean_Elab_convertType___closed__4;
lean_object* l_Lean_Syntax_getId___rarg(lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l_Lean_Elab_getUniverses___rarg(lean_object*);
lean_object* l___private_Init_Lean_Elaborator_PreTerm_5__processBinders(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerBuiltinPreTermElabAttr___lambda__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_convertProp(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_convertSorry___closed__2;
uint8_t l_HashMapImp_contains___at_Lean_addBuiltinPreTermElab___spec__1(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elaborator_PreTerm_3__mkLocalAux___closed__2;
extern lean_object* l_Lean_Parser_Term_sortApp___elambda__1___closed__2;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_explicitUniv___elambda__1___closed__2;
lean_object* l_Lean_Elab_convertSort___rarg(lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_toLevel___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_head_x21___at_Lean_Elab_getScope___spec__1(lean_object*);
lean_object* l_Lean_addBuiltinPreTermElab___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elaborator_PreTerm_2__mkHoleFor___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Level_paren___elambda__1___rarg___closed__3;
lean_object* l_AssocList_find___main___at_Lean_Elab_toPreTerm___spec__2___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Level_hole___elambda__1___rarg___closed__1;
lean_object* l_Lean_syntaxNodeKindOfAttrParam(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elaborator_PreTerm_1__setPos(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_convertSorry___closed__3;
lean_object* l_Lean_registerBuiltinPreTermElabAttr___closed__6;
lean_object* l___regBuiltinTermElab_Lean_Elab_convertForall___closed__2;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l___private_Init_Util_1__mkPanicMessage(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_mk_ref(lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_convertForall(lean_object*);
extern lean_object* l_Lean_Parser_Term_explicitBinder___elambda__1___closed__1;
lean_object* l___private_Init_Lean_Elaborator_PreTerm_1__setPos___closed__4;
extern lean_object* l_Lean_Parser_Term_instBinder___elambda__1___rarg___closed__1;
lean_object* l_Lean_Elab_convertId___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_List_elem___main___at_Lean_Parser_addBuiltinLeadingParser___spec__4(lean_object*, lean_object*);
lean_object* l_HashMapImp_expand___at_Lean_addBuiltinPreTermElab___spec__4(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_convertType(lean_object*);
lean_object* l_AssocList_foldlM___main___at_Lean_addBuiltinPreTermElab___spec__6(lean_object*, lean_object*);
lean_object* l_Lean_mkAsIs___closed__2;
lean_object* l_HashMapImp_moveEntries___main___at_Lean_addBuiltinPreTermElab___spec__5(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elaborator_PreTerm_3__mkLocalAux___closed__1;
lean_object* l_Lean_Elab_convertSorry___rarg___closed__2;
lean_object* l_Lean_Elab_toPreTerm___closed__3;
extern lean_object* l_Lean_Level_LevelToFormat_Result_format___main___closed__3;
extern lean_object* l_Lean_Parser_Term_app___elambda__1___closed__2;
lean_object* l___private_Init_Lean_Elaborator_PreTerm_2__mkHoleFor___closed__1;
lean_object* l_Lean_mkAsIs___closed__1;
extern lean_object* l_System_FilePath_dirName___closed__1;
lean_object* l_panic(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_id___elambda__1___closed__2;
lean_object* l_Lean_Elab_toLevel___main___closed__1;
lean_object* lean_io_ref_get(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elaborator_PreTerm_4__processBinder(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mkAnnotation___closed__1;
extern lean_object* l_Lean_levelOne;
lean_object* l_Lean_mkMData(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_simpleBinder___elambda__1___closed__1;
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Elaborator_PreTerm_4__processBinder___spec__1___closed__1;
size_t lean_usize_modn(size_t, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_convertId___closed__1;
lean_object* l_Lean_Syntax_getIdAt___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_convertSorry___boxed(lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* l_Lean_Expr_mkAnnotation(lean_object*, lean_object*);
lean_object* l_Lean_mkBuiltinPreTermElabTable(lean_object*);
lean_object* lean_environment_find(lean_object*, lean_object*);
lean_object* l_Lean_Elab_convertSorry___rarg___closed__4;
lean_object* l___regBuiltinTermElab_Lean_Elab_convertSort___closed__1;
lean_object* l_Lean_Elab_toPreTerm(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_addOffsetAux___main(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Elab_convertSorry___rarg(lean_object*);
lean_object* l_Lean_Elab_toLevel(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkLevelSucc(lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_convertHole___closed__1;
lean_object* l___private_Init_Lean_Elaborator_PreTerm_4__processBinder___closed__3;
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Elab_convertType___boxed(lean_object*, lean_object*);
lean_object* l_mkHashMapImp___rarg(lean_object*);
extern lean_object* l_Lean_Parser_Term_binderTactic___elambda__1___rarg___closed__1;
extern lean_object* l_Lean_Expr_getAppArgs___closed__1;
lean_object* l___regBuiltinTermElab_Lean_Elab_convertSortApp(lean_object*);
extern lean_object* l_Lean_Syntax_formatStx___main___rarg___closed__5;
lean_object* l_Lean_registerBuiltinPreTermElabAttr___lambda__1___closed__2;
extern lean_object* l_Lean_nameToExprAux___main___closed__4;
lean_object* l___private_Init_Lean_Elaborator_PreTerm_4__processBinder___closed__2;
extern lean_object* l_Lean_Parser_Term_forall___elambda__1___closed__2;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_convertSort(lean_object*);
extern lean_object* l_Lean_Parser_symbolOrIdentInfo___closed__1;
lean_object* l___regBuiltinTermElab_Lean_Elab_convertForall___closed__3;
extern lean_object* l_Lean_Parser_Term_explicitUniv___elambda__1___closed__1;
extern lean_object* l_Lean_Parser_Term_implicitBinder___elambda__1___closed__1;
lean_object* l_Lean_Syntax_toNat___rarg(lean_object*);
lean_object* l_Lean_Syntax_getPos___rarg(lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_convertHole___closed__2;
lean_object* l___private_Init_Lean_Elaborator_PreTerm_3__mkLocalAux(lean_object*);
lean_object* l_Lean_Elab_convertProp(lean_object*, lean_object*);
lean_object* l_Lean_Elab_getScope___rarg(lean_object*);
lean_object* l_Lean_mkLevelIMax(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_AssocList_replace___main___at_Lean_addBuiltinPreTermElab___spec__7(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_convertProp___boxed(lean_object*, lean_object*);
lean_object* l_Lean_mkLevelMVar(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
lean_object* l_Lean_declareBuiltinElab(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_tail_x21___rarg(lean_object*);
lean_object* l_Lean_Elab_logErrorAndThrow___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getNumArgs___rarg(lean_object*);
lean_object* l_Lean_Elab_convertSorry(lean_object*, lean_object*);
lean_object* l_Lean_Elab_convertSortApp___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Elaborator_PreTerm_4__processBinder___spec__1___closed__3;
lean_object* l___regBuiltinTermElab_Lean_Elab_convertProp___closed__2;
lean_object* l_Lean_Elab_logMessage(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_toLevel___main___closed__3;
lean_object* l_Lean_Elab_toLevel___main___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_oldElaborate(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Elaborator_PreTerm_4__processBinder___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_AssocList_contains___main___at_Lean_addBuiltinPreTermElab___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_mkAnnotation___closed__2;
lean_object* l_Lean_Elab_convertSorry___rarg___closed__1;
lean_object* l___regBuiltinTermElab_Lean_Elab_convertType___closed__2;
lean_object* lean_io_ref_reset(lean_object*, lean_object*);
lean_object* l_Lean_mkAsIs(lean_object*);
lean_object* l_Lean_Elab_convertType___rarg___closed__1;
lean_object* l_Lean_Elab_convertForall___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elaborator_PreTerm_4__processBinder___closed__4;
lean_object* l___private_Init_Lean_Elaborator_PreTerm_3__mkLocalAux___closed__3;
lean_object* l___regBuiltinTermElab_Lean_Elab_convertProp___closed__3;
lean_object* l_Lean_declareBuiltinPreTermElab(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTagAttribute___lambda__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_Elaborator_PreTerm_5__processBinders___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_String_splitAux___main___closed__1;
lean_object* l___private_Init_Lean_Elaborator_PreTerm_5__processBinders___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_toPreTerm___closed__4;
lean_object* l_Lean_oldElaborateAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_old_elaborate(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_mkHashMap___at_Lean_mkBuiltinPreTermElabTable___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_mkHashMapImp___rarg(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_mkBuiltinPreTermElabTable___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_mkHashMapImp___rarg(x_1);
return x_2;
}
}
lean_object* l_Lean_mkBuiltinPreTermElabTable(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_mkBuiltinPreTermElabTable___closed__1;
x_3 = lean_io_mk_ref(x_2, x_1);
return x_3;
}
}
uint8_t l_AssocList_contains___main___at_Lean_addBuiltinPreTermElab___spec__2(lean_object* x_1, lean_object* x_2) {
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
x_6 = l_Lean_Name_beq___main(x_4, x_1);
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
uint8_t l_HashMapImp_contains___at_Lean_addBuiltinPreTermElab___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; size_t x_5; size_t x_6; lean_object* x_7; uint8_t x_8; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = lean_name_hash_usize(x_2);
x_6 = lean_usize_modn(x_5, x_4);
lean_dec(x_4);
x_7 = lean_array_uget(x_3, x_6);
x_8 = l_AssocList_contains___main___at_Lean_addBuiltinPreTermElab___spec__2(x_2, x_7);
lean_dec(x_7);
return x_8;
}
}
lean_object* l_AssocList_foldlM___main___at_Lean_addBuiltinPreTermElab___spec__6(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
x_7 = lean_name_hash_usize(x_4);
x_8 = lean_usize_modn(x_7, x_6);
lean_dec(x_6);
x_9 = lean_array_uget(x_1, x_8);
lean_ctor_set(x_2, 2, x_9);
x_10 = lean_array_uset(x_1, x_8, x_2);
x_1 = x_10;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_ctor_get(x_2, 1);
x_14 = lean_ctor_get(x_2, 2);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_2);
x_15 = lean_array_get_size(x_1);
x_16 = lean_name_hash_usize(x_12);
x_17 = lean_usize_modn(x_16, x_15);
lean_dec(x_15);
x_18 = lean_array_uget(x_1, x_17);
x_19 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_19, 0, x_12);
lean_ctor_set(x_19, 1, x_13);
lean_ctor_set(x_19, 2, x_18);
x_20 = lean_array_uset(x_1, x_17, x_19);
x_1 = x_20;
x_2 = x_14;
goto _start;
}
}
}
}
lean_object* l_HashMapImp_moveEntries___main___at_Lean_addBuiltinPreTermElab___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_AssocList_foldlM___main___at_Lean_addBuiltinPreTermElab___spec__6(x_3, x_6);
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
lean_object* l_HashMapImp_expand___at_Lean_addBuiltinPreTermElab___spec__4(lean_object* x_1, lean_object* x_2) {
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
x_9 = l_HashMapImp_moveEntries___main___at_Lean_addBuiltinPreTermElab___spec__5(x_8, x_2, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
lean_object* l_AssocList_replace___main___at_Lean_addBuiltinPreTermElab___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_8 = l_Lean_Name_beq___main(x_5, x_1);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = l_AssocList_replace___main___at_Lean_addBuiltinPreTermElab___spec__7(x_1, x_2, x_7);
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
x_13 = l_Lean_Name_beq___main(x_10, x_1);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_AssocList_replace___main___at_Lean_addBuiltinPreTermElab___spec__7(x_1, x_2, x_12);
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
lean_object* l_HashMapImp_insert___at_Lean_addBuiltinPreTermElab___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; lean_object* x_10; uint8_t x_11; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_array_get_size(x_6);
x_8 = lean_name_hash_usize(x_2);
x_9 = lean_usize_modn(x_8, x_7);
x_10 = lean_array_uget(x_6, x_9);
x_11 = l_AssocList_contains___main___at_Lean_addBuiltinPreTermElab___spec__2(x_2, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_5, x_12);
lean_dec(x_5);
x_14 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_14, 0, x_2);
lean_ctor_set(x_14, 1, x_3);
lean_ctor_set(x_14, 2, x_10);
x_15 = lean_array_uset(x_6, x_9, x_14);
x_16 = lean_nat_dec_le(x_13, x_7);
lean_dec(x_7);
if (x_16 == 0)
{
lean_object* x_17; 
lean_free_object(x_1);
x_17 = l_HashMapImp_expand___at_Lean_addBuiltinPreTermElab___spec__4(x_13, x_15);
return x_17;
}
else
{
lean_ctor_set(x_1, 1, x_15);
lean_ctor_set(x_1, 0, x_13);
return x_1;
}
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_7);
x_18 = l_AssocList_replace___main___at_Lean_addBuiltinPreTermElab___spec__7(x_2, x_3, x_10);
x_19 = lean_array_uset(x_6, x_9, x_18);
lean_ctor_set(x_1, 1, x_19);
return x_1;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; lean_object* x_25; uint8_t x_26; 
x_20 = lean_ctor_get(x_1, 0);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_1);
x_22 = lean_array_get_size(x_21);
x_23 = lean_name_hash_usize(x_2);
x_24 = lean_usize_modn(x_23, x_22);
x_25 = lean_array_uget(x_21, x_24);
x_26 = l_AssocList_contains___main___at_Lean_addBuiltinPreTermElab___spec__2(x_2, x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_add(x_20, x_27);
lean_dec(x_20);
x_29 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_29, 0, x_2);
lean_ctor_set(x_29, 1, x_3);
lean_ctor_set(x_29, 2, x_25);
x_30 = lean_array_uset(x_21, x_24, x_29);
x_31 = lean_nat_dec_le(x_28, x_22);
lean_dec(x_22);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = l_HashMapImp_expand___at_Lean_addBuiltinPreTermElab___spec__4(x_28, x_30);
return x_32;
}
else
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_28);
lean_ctor_set(x_33, 1, x_30);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_22);
x_34 = l_AssocList_replace___main___at_Lean_addBuiltinPreTermElab___spec__7(x_2, x_3, x_25);
x_35 = lean_array_uset(x_21, x_24, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_20);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
lean_object* l_Lean_addBuiltinPreTermElab(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_builtinPreTermElabTable;
x_6 = lean_io_ref_get(x_5, x_4);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
x_10 = l_HashMapImp_contains___at_Lean_addBuiltinPreTermElab___spec__1(x_8, x_1);
lean_dec(x_8);
if (x_10 == 0)
{
lean_object* x_11; 
lean_free_object(x_6);
x_11 = lean_io_ref_get(x_5, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_io_ref_reset(x_5, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = l_HashMapImp_insert___at_Lean_addBuiltinPreTermElab___spec__3(x_12, x_1, x_3);
x_17 = lean_io_ref_set(x_5, x_16, x_15);
return x_17;
}
else
{
uint8_t x_18; 
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_14);
if (x_18 == 0)
{
return x_14;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_14, 0);
x_20 = lean_ctor_get(x_14, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_14);
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
lean_dec(x_3);
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_11);
if (x_22 == 0)
{
return x_11;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_11, 0);
x_24 = lean_ctor_get(x_11, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_11);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_3);
x_26 = l_System_FilePath_dirName___closed__1;
x_27 = l_Lean_Name_toStringWithSep___main(x_26, x_1);
x_28 = l_Lean_addBuiltinTermElab___closed__1;
x_29 = lean_string_append(x_28, x_27);
lean_dec(x_27);
x_30 = l_Lean_addBuiltinTermElab___closed__2;
x_31 = lean_string_append(x_29, x_30);
lean_ctor_set_tag(x_6, 1);
lean_ctor_set(x_6, 0, x_31);
return x_6;
}
}
else
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_32 = lean_ctor_get(x_6, 0);
x_33 = lean_ctor_get(x_6, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_6);
x_34 = l_HashMapImp_contains___at_Lean_addBuiltinPreTermElab___spec__1(x_32, x_1);
lean_dec(x_32);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = lean_io_ref_get(x_5, x_33);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_io_ref_reset(x_5, x_37);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
lean_dec(x_38);
x_40 = l_HashMapImp_insert___at_Lean_addBuiltinPreTermElab___spec__3(x_36, x_1, x_3);
x_41 = lean_io_ref_set(x_5, x_40, x_39);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_36);
lean_dec(x_3);
lean_dec(x_1);
x_42 = lean_ctor_get(x_38, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_38, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_44 = x_38;
} else {
 lean_dec_ref(x_38);
 x_44 = lean_box(0);
}
if (lean_is_scalar(x_44)) {
 x_45 = lean_alloc_ctor(1, 2, 0);
} else {
 x_45 = x_44;
}
lean_ctor_set(x_45, 0, x_42);
lean_ctor_set(x_45, 1, x_43);
return x_45;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_3);
lean_dec(x_1);
x_46 = lean_ctor_get(x_35, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_35, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_48 = x_35;
} else {
 lean_dec_ref(x_35);
 x_48 = lean_box(0);
}
if (lean_is_scalar(x_48)) {
 x_49 = lean_alloc_ctor(1, 2, 0);
} else {
 x_49 = x_48;
}
lean_ctor_set(x_49, 0, x_46);
lean_ctor_set(x_49, 1, x_47);
return x_49;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_3);
x_50 = l_System_FilePath_dirName___closed__1;
x_51 = l_Lean_Name_toStringWithSep___main(x_50, x_1);
x_52 = l_Lean_addBuiltinTermElab___closed__1;
x_53 = lean_string_append(x_52, x_51);
lean_dec(x_51);
x_54 = l_Lean_addBuiltinTermElab___closed__2;
x_55 = lean_string_append(x_53, x_54);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_33);
return x_56;
}
}
}
else
{
uint8_t x_57; 
lean_dec(x_3);
lean_dec(x_1);
x_57 = !lean_is_exclusive(x_6);
if (x_57 == 0)
{
return x_6;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_6, 0);
x_59 = lean_ctor_get(x_6, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_6);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
}
lean_object* l_AssocList_contains___main___at_Lean_addBuiltinPreTermElab___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_AssocList_contains___main___at_Lean_addBuiltinPreTermElab___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_HashMapImp_contains___at_Lean_addBuiltinPreTermElab___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_HashMapImp_contains___at_Lean_addBuiltinPreTermElab___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_addBuiltinPreTermElab___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_addBuiltinPreTermElab(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* _init_l_Lean_declareBuiltinPreTermElab___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("addBuiltinPreTermElab");
return x_1;
}
}
lean_object* _init_l_Lean_declareBuiltinPreTermElab___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_nameToExprAux___main___closed__4;
x_2 = l_Lean_declareBuiltinPreTermElab___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_declareBuiltinPreTermElab(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_declareBuiltinPreTermElab___closed__2;
x_6 = l_Lean_declareBuiltinElab(x_1, x_5, x_2, x_3, x_4);
return x_6;
}
}
lean_object* _init_l_Lean_registerBuiltinPreTermElabAttr___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid attribute 'builtinPreTermElab', must be persistent");
return x_1;
}
}
lean_object* _init_l_Lean_registerBuiltinPreTermElabAttr___lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected preterm elaborator type at '");
return x_1;
}
}
lean_object* _init_l_Lean_registerBuiltinPreTermElabAttr___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' `PreTermElab` expected");
return x_1;
}
}
lean_object* _init_l_Lean_registerBuiltinPreTermElabAttr___lambda__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("PreTermElab");
return x_1;
}
}
lean_object* l_Lean_registerBuiltinPreTermElabAttr___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5) {
_start:
{
if (x_4 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
lean_dec(x_1);
x_6 = l_Lean_registerBuiltinPreTermElabAttr___lambda__1___closed__1;
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_Parser_Term_explicitUniv___elambda__1___closed__2;
lean_inc(x_1);
x_9 = l_Lean_syntaxNodeKindOfAttrParam(x_1, x_8, x_3, x_5);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_22; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_12 = x_9;
} else {
 lean_dec_ref(x_9);
 x_12 = lean_box(0);
}
lean_inc(x_2);
lean_inc(x_1);
x_22 = lean_environment_find(x_1, x_2);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_2);
lean_dec(x_1);
x_23 = l_Lean_mkInitAttr___lambda__1___closed__1;
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_11);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_22, 0);
lean_inc(x_25);
lean_dec(x_22);
x_26 = l_Lean_ConstantInfo_type(x_25);
lean_dec(x_25);
if (lean_obj_tag(x_26) == 4)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec(x_26);
if (lean_obj_tag(x_27) == 1)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
if (lean_obj_tag(x_28) == 1)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_dec(x_27);
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = l_Lean_nameToExprAux___main___closed__1;
x_33 = lean_string_dec_eq(x_31, x_32);
lean_dec(x_31);
if (x_33 == 0)
{
lean_object* x_34; 
lean_dec(x_30);
lean_dec(x_10);
lean_dec(x_1);
x_34 = lean_box(0);
x_13 = x_34;
goto block_21;
}
else
{
lean_object* x_35; uint8_t x_36; 
x_35 = l_Lean_registerBuiltinPreTermElabAttr___lambda__1___closed__4;
x_36 = lean_string_dec_eq(x_30, x_35);
lean_dec(x_30);
if (x_36 == 0)
{
lean_object* x_37; 
lean_dec(x_10);
lean_dec(x_1);
x_37 = lean_box(0);
x_13 = x_37;
goto block_21;
}
else
{
lean_object* x_38; 
lean_dec(x_12);
x_38 = l_Lean_declareBuiltinPreTermElab(x_1, x_10, x_2, x_11);
return x_38;
}
}
}
else
{
lean_object* x_39; 
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_10);
lean_dec(x_1);
x_39 = lean_box(0);
x_13 = x_39;
goto block_21;
}
}
else
{
lean_object* x_40; 
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_10);
lean_dec(x_1);
x_40 = lean_box(0);
x_13 = x_40;
goto block_21;
}
}
else
{
lean_object* x_41; 
lean_dec(x_27);
lean_dec(x_10);
lean_dec(x_1);
x_41 = lean_box(0);
x_13 = x_41;
goto block_21;
}
}
else
{
lean_object* x_42; 
lean_dec(x_26);
lean_dec(x_10);
lean_dec(x_1);
x_42 = lean_box(0);
x_13 = x_42;
goto block_21;
}
}
block_21:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_13);
x_14 = l_System_FilePath_dirName___closed__1;
x_15 = l_Lean_Name_toStringWithSep___main(x_14, x_2);
x_16 = l_Lean_registerBuiltinPreTermElabAttr___lambda__1___closed__2;
x_17 = lean_string_append(x_16, x_15);
lean_dec(x_15);
x_18 = l_Lean_registerBuiltinPreTermElabAttr___lambda__1___closed__3;
x_19 = lean_string_append(x_17, x_18);
if (lean_is_scalar(x_12)) {
 x_20 = lean_alloc_ctor(1, 2, 0);
} else {
 x_20 = x_12;
 lean_ctor_set_tag(x_20, 1);
}
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_11);
return x_20;
}
}
else
{
uint8_t x_43; 
lean_dec(x_2);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_9);
if (x_43 == 0)
{
return x_9;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_9, 0);
x_45 = lean_ctor_get(x_9, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_9);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
}
}
lean_object* _init_l_Lean_registerBuiltinPreTermElabAttr___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("builtinPreTermElab");
return x_1;
}
}
lean_object* _init_l_Lean_registerBuiltinPreTermElabAttr___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_registerBuiltinPreTermElabAttr___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_registerBuiltinPreTermElabAttr___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_registerBuiltinPreTermElabAttr___closed__2;
x_2 = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lambda__5___boxed), 5, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_registerBuiltinPreTermElabAttr___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_registerBuiltinPreTermElabAttr___closed__2;
x_2 = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lambda__6___boxed), 5, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_registerBuiltinPreTermElabAttr___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Builtin preterm conversion elaborator, we use it to interface with the Lean3 elaborator");
return x_1;
}
}
lean_object* _init_l_Lean_registerBuiltinPreTermElabAttr___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_registerBuiltinPreTermElabAttr___lambda__1___boxed), 5, 0);
return x_1;
}
}
lean_object* _init_l_Lean_registerBuiltinPreTermElabAttr___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_1 = l_Lean_registerBuiltinPreTermElabAttr___closed__2;
x_2 = l_Lean_registerBuiltinPreTermElabAttr___closed__5;
x_3 = l_Lean_registerBuiltinPreTermElabAttr___closed__6;
x_4 = l_Lean_registerBuiltinPreTermElabAttr___closed__3;
x_5 = l_Lean_registerBuiltinPreTermElabAttr___closed__4;
x_6 = l_Lean_AttributeImpl_inhabited___closed__4;
x_7 = l_Lean_AttributeImpl_inhabited___closed__5;
x_8 = 1;
x_9 = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_2);
lean_ctor_set(x_9, 2, x_3);
lean_ctor_set(x_9, 3, x_4);
lean_ctor_set(x_9, 4, x_5);
lean_ctor_set(x_9, 5, x_6);
lean_ctor_set(x_9, 6, x_7);
lean_ctor_set(x_9, 7, x_7);
lean_ctor_set_uint8(x_9, sizeof(void*)*8, x_8);
return x_9;
}
}
lean_object* l_Lean_registerBuiltinPreTermElabAttr(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_registerBuiltinPreTermElabAttr___closed__7;
x_3 = l_Lean_registerAttribute(x_2, x_1);
return x_3;
}
}
lean_object* l_Lean_registerBuiltinPreTermElabAttr___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_4);
lean_dec(x_4);
x_7 = l_Lean_registerBuiltinPreTermElabAttr___lambda__1(x_1, x_2, x_3, x_6, x_5);
lean_dec(x_3);
return x_7;
}
}
lean_object* _init_l_Lean_Expr_mkAnnotation___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("annotation");
return x_1;
}
}
lean_object* _init_l_Lean_Expr_mkAnnotation___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Expr_mkAnnotation___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Expr_mkAnnotation(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_box(0);
x_4 = l_Lean_Expr_mkAnnotation___closed__2;
x_5 = l_Lean_KVMap_setName(x_3, x_4, x_1);
x_6 = l_Lean_mkMData(x_5, x_2);
return x_6;
}
}
lean_object* _init_l_Lean_mkAsIs___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("as_is");
return x_1;
}
}
lean_object* _init_l_Lean_mkAsIs___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_mkAsIs___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_mkAsIs(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_mkAsIs___closed__2;
x_3 = l_Lean_Expr_mkAnnotation(x_2, x_1);
return x_3;
}
}
lean_object* _init_l_Lean_mkAsPattern___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("as_pattern");
return x_1;
}
}
lean_object* _init_l_Lean_mkAsPattern___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_mkAsPattern___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_mkAsPattern(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = l_Lean_mkFVar(x_1);
x_4 = l_Lean_mkApp(x_3, x_2);
x_5 = l_Lean_mkAsPattern___closed__2;
x_6 = l_Lean_Expr_mkAnnotation(x_5, x_4);
return x_6;
}
}
lean_object* _init_l_Lean_mkPreTypeAscription___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("typedExpr");
return x_1;
}
}
lean_object* _init_l_Lean_mkPreTypeAscription___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_mkPreTypeAscription___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_mkPreTypeAscription___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_mkPreTypeAscription___closed__2;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
lean_object* l_Lean_mkPreTypeAscription(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Lean_mkPreTypeAscription___closed__3;
x_4 = l_Lean_mkApp(x_3, x_2);
x_5 = l_Lean_mkApp(x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_mkPreTypeAscriptionIfSome(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = l_Lean_mkPreTypeAscription(x_1, x_3);
return x_4;
}
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_toLevel___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_2);
x_8 = lean_nat_dec_lt(x_3, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_3);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_array_fget(x_2, x_3);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_3, x_11);
lean_dec(x_3);
x_13 = l_Lean_Elab_toLevel___main(x_10, x_5, x_6);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_mkLevelIMax(x_4, x_14);
x_3 = x_12;
x_4 = x_16;
x_6 = x_15;
goto _start;
}
else
{
uint8_t x_18; 
lean_dec(x_12);
lean_dec(x_4);
x_18 = !lean_is_exclusive(x_13);
if (x_18 == 0)
{
return x_13;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_13, 0);
x_20 = lean_ctor_get(x_13, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_13);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_toLevel___main___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_2);
x_8 = lean_nat_dec_lt(x_3, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_3);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_array_fget(x_2, x_3);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_3, x_11);
lean_dec(x_3);
x_13 = l_Lean_Elab_toLevel___main(x_10, x_5, x_6);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_mkLevelMax(x_4, x_14);
x_3 = x_12;
x_4 = x_16;
x_6 = x_15;
goto _start;
}
else
{
uint8_t x_18; 
lean_dec(x_12);
lean_dec(x_4);
x_18 = !lean_is_exclusive(x_13);
if (x_18 == 0)
{
return x_13;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_13, 0);
x_20 = lean_ctor_get(x_13, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_13);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
}
lean_object* _init_l_Lean_Elab_toLevel___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected universe level syntax");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_toLevel___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_toLevel___main___closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_toLevel___main___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unknown universe variable '");
return x_1;
}
}
lean_object* l_Lean_Elab_toLevel___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Syntax_getKind___rarg(x_1);
if (lean_obj_tag(x_4) == 1)
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 1)
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 1)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 1)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_9 = lean_ctor_get(x_4, 1);
lean_inc(x_9);
lean_dec(x_4);
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
lean_dec(x_5);
x_11 = lean_ctor_get(x_6, 1);
lean_inc(x_11);
lean_dec(x_6);
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_12);
lean_dec(x_7);
x_13 = l_Lean_nameToExprAux___main___closed__1;
x_14 = lean_string_dec_eq(x_12, x_13);
lean_dec(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_15 = l_Lean_Elab_toLevel___main___closed__2;
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_3);
return x_16;
}
else
{
lean_object* x_17; uint8_t x_18; 
x_17 = l_Lean_Syntax_formatStx___main___rarg___closed__5;
x_18 = lean_string_dec_eq(x_11, x_17);
lean_dec(x_11);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_19 = l_Lean_Elab_toLevel___main___closed__2;
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_3);
return x_20;
}
else
{
lean_object* x_21; uint8_t x_22; 
x_21 = l_Lean_Parser_Level_paren___elambda__1___rarg___closed__1;
x_22 = lean_string_dec_eq(x_10, x_21);
lean_dec(x_10);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_9);
lean_dec(x_1);
x_23 = l_Lean_Elab_toLevel___main___closed__2;
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_3);
return x_24;
}
else
{
lean_object* x_25; uint8_t x_26; 
x_25 = l_Lean_Parser_Level_paren___elambda__1___rarg___closed__3;
x_26 = lean_string_dec_eq(x_9, x_25);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; 
x_27 = l_Lean_Level_LevelToFormat_Result_format___main___closed__3;
x_28 = lean_string_dec_eq(x_9, x_27);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = l_Lean_Level_LevelToFormat_Result_format___main___closed__5;
x_30 = lean_string_dec_eq(x_9, x_29);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; 
x_31 = l_Lean_Parser_Level_hole___elambda__1___rarg___closed__1;
x_32 = lean_string_dec_eq(x_9, x_31);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = l_Lean_Parser_Level_num___elambda__1___rarg___closed__1;
x_34 = lean_string_dec_eq(x_9, x_33);
if (x_34 == 0)
{
lean_object* x_35; uint8_t x_36; 
x_35 = l_Lean_Parser_symbolOrIdentInfo___closed__1;
x_36 = lean_string_dec_eq(x_9, x_35);
if (x_36 == 0)
{
lean_object* x_37; uint8_t x_38; 
x_37 = l_Lean_Parser_Level_addLit___elambda__1___closed__1;
x_38 = lean_string_dec_eq(x_9, x_37);
lean_dec(x_9);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
lean_dec(x_1);
x_39 = l_Lean_Elab_toLevel___main___closed__2;
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_3);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_unsigned_to_nat(0u);
x_42 = l_Lean_Syntax_getArg___rarg(x_1, x_41);
x_43 = l_Lean_Elab_toLevel___main(x_42, x_2, x_3);
if (lean_obj_tag(x_43) == 0)
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_45 = lean_ctor_get(x_43, 0);
x_46 = lean_unsigned_to_nat(2u);
x_47 = l_Lean_Syntax_getArg___rarg(x_1, x_46);
lean_dec(x_1);
x_48 = l_Lean_Syntax_toNat___rarg(x_47);
lean_dec(x_47);
x_49 = l_Lean_Level_addOffsetAux___main(x_48, x_45);
lean_ctor_set(x_43, 0, x_49);
return x_43;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_50 = lean_ctor_get(x_43, 0);
x_51 = lean_ctor_get(x_43, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_43);
x_52 = lean_unsigned_to_nat(2u);
x_53 = l_Lean_Syntax_getArg___rarg(x_1, x_52);
lean_dec(x_1);
x_54 = l_Lean_Syntax_toNat___rarg(x_53);
lean_dec(x_53);
x_55 = l_Lean_Level_addOffsetAux___main(x_54, x_50);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_51);
return x_56;
}
}
else
{
uint8_t x_57; 
lean_dec(x_1);
x_57 = !lean_is_exclusive(x_43);
if (x_57 == 0)
{
return x_43;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_43, 0);
x_59 = lean_ctor_get(x_43, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_43);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
lean_dec(x_9);
x_61 = lean_unsigned_to_nat(0u);
x_62 = l_Lean_Syntax_getIdAt___rarg(x_1, x_61);
x_63 = l_Lean_Elab_getUniverses___rarg(x_3);
x_64 = !lean_is_exclusive(x_63);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_65 = lean_ctor_get(x_63, 0);
x_66 = lean_ctor_get(x_63, 1);
x_67 = l_List_elem___main___at_Lean_Parser_addBuiltinLeadingParser___spec__4(x_62, x_65);
lean_dec(x_65);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
lean_free_object(x_63);
x_68 = l_System_FilePath_dirName___closed__1;
x_69 = l_Lean_Name_toStringWithSep___main(x_68, x_62);
x_70 = l_Lean_Elab_toLevel___main___closed__3;
x_71 = lean_string_append(x_70, x_69);
lean_dec(x_69);
x_72 = l_Char_HasRepr___closed__1;
x_73 = lean_string_append(x_71, x_72);
x_74 = l_Lean_Elab_logError___rarg(x_1, x_73, x_2, x_66);
lean_dec(x_1);
x_75 = !lean_is_exclusive(x_74);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_ctor_get(x_74, 0);
lean_dec(x_76);
x_77 = l_Lean_mkLevelMVar(x_8);
lean_ctor_set(x_74, 0, x_77);
return x_74;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_74, 1);
lean_inc(x_78);
lean_dec(x_74);
x_79 = l_Lean_mkLevelMVar(x_8);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_78);
return x_80;
}
}
else
{
lean_object* x_81; 
lean_dec(x_1);
x_81 = l_Lean_mkLevelParam(x_62);
lean_ctor_set(x_63, 0, x_81);
return x_63;
}
}
else
{
lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_82 = lean_ctor_get(x_63, 0);
x_83 = lean_ctor_get(x_63, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_63);
x_84 = l_List_elem___main___at_Lean_Parser_addBuiltinLeadingParser___spec__4(x_62, x_82);
lean_dec(x_82);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_85 = l_System_FilePath_dirName___closed__1;
x_86 = l_Lean_Name_toStringWithSep___main(x_85, x_62);
x_87 = l_Lean_Elab_toLevel___main___closed__3;
x_88 = lean_string_append(x_87, x_86);
lean_dec(x_86);
x_89 = l_Char_HasRepr___closed__1;
x_90 = lean_string_append(x_88, x_89);
x_91 = l_Lean_Elab_logError___rarg(x_1, x_90, x_2, x_83);
lean_dec(x_1);
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
x_94 = l_Lean_mkLevelMVar(x_8);
if (lean_is_scalar(x_93)) {
 x_95 = lean_alloc_ctor(0, 2, 0);
} else {
 x_95 = x_93;
}
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_92);
return x_95;
}
else
{
lean_object* x_96; lean_object* x_97; 
lean_dec(x_1);
x_96 = l_Lean_mkLevelParam(x_62);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_83);
return x_97;
}
}
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
lean_dec(x_9);
x_98 = lean_unsigned_to_nat(0u);
x_99 = l_Lean_Syntax_getArg___rarg(x_1, x_98);
lean_dec(x_1);
x_100 = l_Lean_Syntax_toNat___rarg(x_99);
lean_dec(x_99);
x_101 = l_Lean_Level_ofNat___main(x_100);
lean_dec(x_100);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_3);
return x_102;
}
}
else
{
lean_object* x_103; lean_object* x_104; 
lean_dec(x_9);
lean_dec(x_1);
x_103 = l_Lean_mkLevelMVar(x_8);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_3);
return x_104;
}
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
lean_dec(x_9);
x_105 = lean_unsigned_to_nat(1u);
x_106 = l_Lean_Syntax_getArg___rarg(x_1, x_105);
x_107 = l_Lean_Syntax_getArgs___rarg(x_106);
lean_dec(x_106);
x_108 = lean_box(0);
x_109 = lean_unsigned_to_nat(0u);
x_110 = lean_array_get(x_108, x_107, x_109);
x_111 = l_Lean_Elab_toLevel___main(x_110, x_2, x_3);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_111, 1);
lean_inc(x_113);
lean_dec(x_111);
x_114 = l_Array_iterateMAux___main___at_Lean_Elab_toLevel___main___spec__1(x_1, x_107, x_105, x_112, x_2, x_113);
lean_dec(x_107);
lean_dec(x_1);
return x_114;
}
else
{
uint8_t x_115; 
lean_dec(x_107);
lean_dec(x_1);
x_115 = !lean_is_exclusive(x_111);
if (x_115 == 0)
{
return x_111;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_116 = lean_ctor_get(x_111, 0);
x_117 = lean_ctor_get(x_111, 1);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_111);
x_118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
return x_118;
}
}
}
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
lean_dec(x_9);
x_119 = lean_unsigned_to_nat(1u);
x_120 = l_Lean_Syntax_getArg___rarg(x_1, x_119);
x_121 = l_Lean_Syntax_getArgs___rarg(x_120);
lean_dec(x_120);
x_122 = lean_box(0);
x_123 = lean_unsigned_to_nat(0u);
x_124 = lean_array_get(x_122, x_121, x_123);
x_125 = l_Lean_Elab_toLevel___main(x_124, x_2, x_3);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_125, 1);
lean_inc(x_127);
lean_dec(x_125);
x_128 = l_Array_iterateMAux___main___at_Lean_Elab_toLevel___main___spec__2(x_1, x_121, x_119, x_126, x_2, x_127);
lean_dec(x_121);
lean_dec(x_1);
return x_128;
}
else
{
uint8_t x_129; 
lean_dec(x_121);
lean_dec(x_1);
x_129 = !lean_is_exclusive(x_125);
if (x_129 == 0)
{
return x_125;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_130 = lean_ctor_get(x_125, 0);
x_131 = lean_ctor_get(x_125, 1);
lean_inc(x_131);
lean_inc(x_130);
lean_dec(x_125);
x_132 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set(x_132, 1, x_131);
return x_132;
}
}
}
}
else
{
lean_object* x_133; lean_object* x_134; 
lean_dec(x_9);
x_133 = lean_unsigned_to_nat(1u);
x_134 = l_Lean_Syntax_getArg___rarg(x_1, x_133);
lean_dec(x_1);
x_1 = x_134;
goto _start;
}
}
}
}
}
else
{
lean_object* x_136; lean_object* x_137; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_136 = l_Lean_Elab_toLevel___main___closed__2;
x_137 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_3);
return x_137;
}
}
else
{
lean_object* x_138; lean_object* x_139; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_138 = l_Lean_Elab_toLevel___main___closed__2;
x_139 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set(x_139, 1, x_3);
return x_139;
}
}
else
{
lean_object* x_140; lean_object* x_141; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_140 = l_Lean_Elab_toLevel___main___closed__2;
x_141 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_3);
return x_141;
}
}
else
{
lean_object* x_142; lean_object* x_143; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_142 = l_Lean_Elab_toLevel___main___closed__2;
x_143 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_143, 0, x_142);
lean_ctor_set(x_143, 1, x_3);
return x_143;
}
}
else
{
lean_object* x_144; lean_object* x_145; 
lean_dec(x_4);
lean_dec(x_1);
x_144 = l_Lean_Elab_toLevel___main___closed__2;
x_145 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_145, 0, x_144);
lean_ctor_set(x_145, 1, x_3);
return x_145;
}
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_toLevel___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_iterateMAux___main___at_Lean_Elab_toLevel___main___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_toLevel___main___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_iterateMAux___main___at_Lean_Elab_toLevel___main___spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_Elab_toLevel___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_toLevel___main(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Elab_toLevel(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_toLevel___main(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_Elab_toLevel___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_toLevel(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* _init_l___private_Init_Lean_Elaborator_PreTerm_1__setPos___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("column");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Elaborator_PreTerm_1__setPos___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Init_Lean_Elaborator_PreTerm_1__setPos___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Elaborator_PreTerm_1__setPos___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("row");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Elaborator_PreTerm_1__setPos___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Init_Lean_Elaborator_PreTerm_1__setPos___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Init_Lean_Elaborator_PreTerm_1__setPos(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_Parser_Term_app___elambda__1___closed__2;
x_6 = l_Lean_Syntax_isOfKind___rarg(x_1, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = l_Lean_Syntax_getPos___rarg(x_1);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_2);
lean_ctor_set(x_8, 1, x_4);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_ctor_get(x_3, 1);
x_11 = l_Lean_FileMap_toPosition(x_10, x_9);
lean_dec(x_9);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
x_13 = lean_box(0);
x_14 = l___private_Init_Lean_Elaborator_PreTerm_1__setPos___closed__2;
x_15 = l_Lean_KVMap_setNat(x_13, x_14, x_12);
x_16 = lean_ctor_get(x_11, 0);
lean_inc(x_16);
lean_dec(x_11);
x_17 = l___private_Init_Lean_Elaborator_PreTerm_1__setPos___closed__4;
x_18 = l_Lean_KVMap_setNat(x_15, x_17, x_16);
x_19 = l_Lean_mkMData(x_18, x_2);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_4);
return x_20;
}
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_2);
lean_ctor_set(x_21, 1, x_4);
return x_21;
}
}
}
lean_object* l___private_Init_Lean_Elaborator_PreTerm_1__setPos___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Lean_Elaborator_PreTerm_1__setPos(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_AssocList_find___main___at_Lean_Elab_toPreTerm___spec__2(lean_object* x_1, lean_object* x_2) {
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
x_7 = l_Lean_Name_beq___main(x_4, x_1);
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
lean_object* l_HashMapImp_find___at_Lean_Elab_toPreTerm___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; size_t x_5; size_t x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = lean_name_hash_usize(x_2);
x_6 = lean_usize_modn(x_5, x_4);
lean_dec(x_4);
x_7 = lean_array_uget(x_3, x_6);
x_8 = l_AssocList_find___main___at_Lean_Elab_toPreTerm___spec__2(x_2, x_7);
lean_dec(x_7);
return x_8;
}
}
lean_object* _init_l_Lean_Elab_toPreTerm___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("`toPreTerm` failed, unexpected syntax");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_toPreTerm___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_toPreTerm___closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_toPreTerm___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_builtinPreTermElabTable;
x_2 = lean_alloc_closure((void*)(l_IO_Prim_Ref_get___boxed), 3, 2);
lean_closure_set(x_2, 0, lean_box(0));
lean_closure_set(x_2, 1, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_toPreTerm___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("`toPreTerm` failed, no support for syntax '");
return x_1;
}
}
lean_object* l_Lean_Elab_toPreTerm(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = l_Lean_Elab_toPreTerm___closed__3;
x_6 = l_Lean_Elab_runIOUnsafe___rarg(x_5, x_2, x_3);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_HashMapImp_find___at_Lean_Elab_toPreTerm___spec__1(x_7, x_4);
lean_dec(x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = l_System_FilePath_dirName___closed__1;
x_11 = l_Lean_Name_toStringWithSep___main(x_10, x_4);
x_12 = l_Lean_Elab_toPreTerm___closed__4;
x_13 = lean_string_append(x_12, x_11);
lean_dec(x_11);
x_14 = l_Char_HasRepr___closed__1;
x_15 = lean_string_append(x_13, x_14);
x_16 = l_Lean_Elab_logErrorAndThrow___rarg(x_1, x_15, x_2, x_8);
lean_dec(x_2);
lean_dec(x_1);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_4);
x_17 = lean_ctor_get(x_9, 0);
lean_inc(x_17);
lean_dec(x_9);
lean_inc(x_2);
lean_inc(x_1);
x_18 = lean_apply_3(x_17, x_1, x_2, x_8);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l___private_Init_Lean_Elaborator_PreTerm_1__setPos(x_1, x_19, x_2, x_20);
lean_dec(x_2);
lean_dec(x_1);
return x_21;
}
else
{
uint8_t x_22; 
lean_dec(x_2);
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_18);
if (x_22 == 0)
{
return x_18;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_18, 0);
x_24 = lean_ctor_get(x_18, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_18);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
else
{
uint8_t x_26; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_6);
if (x_26 == 0)
{
return x_6;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_6, 0);
x_28 = lean_ctor_get(x_6, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_6);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
else
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_2);
lean_dec(x_1);
x_30 = l_Lean_Elab_toPreTerm___closed__2;
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_3);
return x_31;
}
}
}
lean_object* l_AssocList_find___main___at_Lean_Elab_toPreTerm___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_AssocList_find___main___at_Lean_Elab_toPreTerm___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_HashMapImp_find___at_Lean_Elab_toPreTerm___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_HashMapImp_find___at_Lean_Elab_toPreTerm___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Elaborator_PreTerm_2__mkHoleFor___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = l_Lean_mkMVar(x_1);
return x_2;
}
}
lean_object* l___private_Init_Lean_Elaborator_PreTerm_2__mkHoleFor(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l___private_Init_Lean_Elaborator_PreTerm_2__mkHoleFor___closed__1;
x_5 = l___private_Init_Lean_Elaborator_PreTerm_1__setPos(x_1, x_4, x_2, x_3);
return x_5;
}
}
lean_object* l___private_Init_Lean_Elaborator_PreTerm_2__mkHoleFor___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Elaborator_PreTerm_2__mkHoleFor(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* _init_l_Lean_Elab_convertType___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_levelOne;
x_2 = l_Lean_mkSort(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_convertType___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_convertType___rarg___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_convertType(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Elab_convertType___rarg), 1, 0);
return x_3;
}
}
lean_object* l_Lean_Elab_convertType___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_convertType(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_convertType___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Elab");
return x_1;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_convertType___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_nameToExprAux___main___closed__4;
x_2 = l___regBuiltinTermElab_Lean_Elab_convertType___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_convertType___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("convertType");
return x_1;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_convertType___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltinTermElab_Lean_Elab_convertType___closed__2;
x_2 = l___regBuiltinTermElab_Lean_Elab_convertType___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_convertType___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_convertType___boxed), 2, 0);
return x_1;
}
}
lean_object* l___regBuiltinTermElab_Lean_Elab_convertType(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Parser_Term_type___elambda__1___rarg___closed__2;
x_3 = l___regBuiltinTermElab_Lean_Elab_convertType___closed__4;
x_4 = l___regBuiltinTermElab_Lean_Elab_convertType___closed__5;
x_5 = l_Lean_addBuiltinPreTermElab(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_convertSort___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_getAppArgs___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_convertSort(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Elab_convertSort___rarg), 1, 0);
return x_3;
}
}
lean_object* l_Lean_Elab_convertSort___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_convertSort(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_convertSort___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("convertSort");
return x_1;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_convertSort___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltinTermElab_Lean_Elab_convertType___closed__2;
x_2 = l___regBuiltinTermElab_Lean_Elab_convertSort___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_convertSort___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_convertSort___boxed), 2, 0);
return x_1;
}
}
lean_object* l___regBuiltinTermElab_Lean_Elab_convertSort(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Parser_Term_sort___elambda__1___rarg___closed__2;
x_3 = l___regBuiltinTermElab_Lean_Elab_convertSort___closed__2;
x_4 = l___regBuiltinTermElab_Lean_Elab_convertSort___closed__3;
x_5 = l_Lean_addBuiltinPreTermElab(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_convertProp___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_getAppArgs___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_convertProp(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Elab_convertProp___rarg), 1, 0);
return x_3;
}
}
lean_object* l_Lean_Elab_convertProp___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_convertProp(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_convertProp___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("convertProp");
return x_1;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_convertProp___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltinTermElab_Lean_Elab_convertType___closed__2;
x_2 = l___regBuiltinTermElab_Lean_Elab_convertProp___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_convertProp___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_convertProp___boxed), 2, 0);
return x_1;
}
}
lean_object* l___regBuiltinTermElab_Lean_Elab_convertProp(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Parser_Term_prop___elambda__1___rarg___closed__2;
x_3 = l___regBuiltinTermElab_Lean_Elab_convertProp___closed__2;
x_4 = l___regBuiltinTermElab_Lean_Elab_convertProp___closed__3;
x_5 = l_Lean_addBuiltinPreTermElab(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_convertSortApp(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_box(0);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_get(x_5, x_4, x_6);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_array_get(x_5, x_4, x_8);
x_10 = l_Lean_Elab_toLevel___main(x_9, x_2, x_3);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = l_Lean_Parser_Term_type___elambda__1___rarg___closed__2;
x_14 = l_Lean_Syntax_isOfKind___rarg(x_7, x_13);
lean_dec(x_7);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = l_Lean_mkSort(x_12);
lean_ctor_set(x_10, 0, x_15);
return x_10;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = l_Lean_mkLevelSucc(x_12);
x_17 = l_Lean_mkSort(x_16);
lean_ctor_set(x_10, 0, x_17);
return x_10;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_10, 0);
x_19 = lean_ctor_get(x_10, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_10);
x_20 = l_Lean_Parser_Term_type___elambda__1___rarg___closed__2;
x_21 = l_Lean_Syntax_isOfKind___rarg(x_7, x_20);
lean_dec(x_7);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = l_Lean_mkSort(x_18);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_19);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = l_Lean_mkLevelSucc(x_18);
x_25 = l_Lean_mkSort(x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_19);
return x_26;
}
}
}
else
{
uint8_t x_27; 
lean_dec(x_7);
x_27 = !lean_is_exclusive(x_10);
if (x_27 == 0)
{
return x_10;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_10, 0);
x_29 = lean_ctor_get(x_10, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_10);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
lean_object* l_Lean_Elab_convertSortApp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_convertSortApp(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_convertSortApp___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("convertSortApp");
return x_1;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_convertSortApp___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltinTermElab_Lean_Elab_convertType___closed__2;
x_2 = l___regBuiltinTermElab_Lean_Elab_convertSortApp___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_convertSortApp___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_convertSortApp___boxed), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltinTermElab_Lean_Elab_convertSortApp(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Parser_Term_sortApp___elambda__1___closed__2;
x_3 = l___regBuiltinTermElab_Lean_Elab_convertSortApp___closed__2;
x_4 = l___regBuiltinTermElab_Lean_Elab_convertSortApp___closed__3;
x_5 = l_Lean_addBuiltinPreTermElab(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* _init_l___private_Init_Lean_Elaborator_PreTerm_3__mkLocalAux___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Init.Lean.Elaborator.PreTerm");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Elaborator_PreTerm_3__mkLocalAux___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("to be deleted");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Elaborator_PreTerm_3__mkLocalAux___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Init_Lean_Elaborator_PreTerm_3__mkLocalAux___closed__1;
x_2 = lean_unsigned_to_nat(141u);
x_3 = lean_unsigned_to_nat(0u);
x_4 = l___private_Init_Lean_Elaborator_PreTerm_3__mkLocalAux___closed__2;
x_5 = l___private_Init_Util_1__mkPanicMessage(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l___private_Init_Lean_Elaborator_PreTerm_3__mkLocalAux(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Expr_Inhabited;
x_3 = l___private_Init_Lean_Elaborator_PreTerm_3__mkLocalAux___closed__3;
x_4 = lean_panic_fn(x_3);
return x_4;
}
}
lean_object* l___private_Init_Lean_Elaborator_PreTerm_3__mkLocalAux___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Init_Lean_Elaborator_PreTerm_3__mkLocalAux(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* _init_l_Array_umapMAux___main___at___private_Init_Lean_Elaborator_PreTerm_4__processBinder___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unknown binder default value annotation");
return x_1;
}
}
lean_object* _init_l_Array_umapMAux___main___at___private_Init_Lean_Elaborator_PreTerm_4__processBinder___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_umapMAux___main___at___private_Init_Lean_Elaborator_PreTerm_4__processBinder___spec__1___closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Array_umapMAux___main___at___private_Init_Lean_Elaborator_PreTerm_4__processBinder___spec__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("old elaborator does not support tactics in parameters");
return x_1;
}
}
lean_object* _init_l_Array_umapMAux___main___at___private_Init_Lean_Elaborator_PreTerm_4__processBinder___spec__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("optParam");
return x_1;
}
}
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Elaborator_PreTerm_4__processBinder___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_4);
x_8 = lean_nat_dec_lt(x_3, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
lean_dec(x_3);
x_9 = l_Array_empty___closed__1;
x_10 = x_4;
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_6);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_98; lean_object* x_99; uint8_t x_100; 
x_12 = lean_array_fget(x_4, x_3);
x_13 = lean_box(0);
lean_inc(x_12);
x_14 = x_13;
x_15 = lean_array_fset(x_4, x_3, x_14);
x_24 = l_Lean_Syntax_getId___rarg(x_12);
x_98 = l_Lean_Syntax_getNumArgs___rarg(x_1);
x_99 = lean_unsigned_to_nat(0u);
x_100 = lean_nat_dec_eq(x_98, x_99);
lean_dec(x_98);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_unsigned_to_nat(1u);
x_102 = l_Lean_Syntax_getArg___rarg(x_1, x_101);
lean_inc(x_5);
x_103 = l_Lean_Elab_toPreTerm(x_102, x_5, x_6);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; 
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
lean_dec(x_103);
x_25 = x_104;
x_26 = x_105;
goto block_97;
}
else
{
uint8_t x_106; 
lean_dec(x_24);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_3);
x_106 = !lean_is_exclusive(x_103);
if (x_106 == 0)
{
return x_103;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_103, 0);
x_108 = lean_ctor_get(x_103, 1);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_103);
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set(x_109, 1, x_108);
return x_109;
}
}
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = l___private_Init_Lean_Elaborator_PreTerm_2__mkHoleFor(x_12, x_5, x_6);
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_110, 1);
lean_inc(x_112);
lean_dec(x_110);
x_25 = x_111;
x_26 = x_112;
goto block_97;
}
block_23:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_3, x_18);
x_20 = x_16;
x_21 = lean_array_fset(x_15, x_3, x_20);
lean_dec(x_3);
x_3 = x_19;
x_4 = x_21;
x_6 = x_17;
goto _start;
}
block_97:
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = l_Lean_Syntax_getNumArgs___rarg(x_2);
x_28 = lean_unsigned_to_nat(0u);
x_29 = lean_nat_dec_eq(x_27, x_28);
lean_dec(x_27);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = l_Lean_Syntax_getArg___rarg(x_2, x_28);
x_31 = l_Lean_Syntax_getKind___rarg(x_30);
if (lean_obj_tag(x_31) == 1)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
if (lean_obj_tag(x_32) == 1)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
if (lean_obj_tag(x_33) == 1)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
if (lean_obj_tag(x_34) == 1)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_36 = lean_ctor_get(x_31, 1);
lean_inc(x_36);
lean_dec(x_31);
x_37 = lean_ctor_get(x_32, 1);
lean_inc(x_37);
lean_dec(x_32);
x_38 = lean_ctor_get(x_33, 1);
lean_inc(x_38);
lean_dec(x_33);
x_39 = lean_ctor_get(x_34, 1);
lean_inc(x_39);
lean_dec(x_34);
x_40 = l_Lean_nameToExprAux___main___closed__1;
x_41 = lean_string_dec_eq(x_39, x_40);
lean_dec(x_39);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_30);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_3);
x_42 = l_Array_umapMAux___main___at___private_Init_Lean_Elaborator_PreTerm_4__processBinder___spec__1___closed__2;
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_26);
return x_43;
}
else
{
lean_object* x_44; uint8_t x_45; 
x_44 = l_Lean_Syntax_formatStx___main___rarg___closed__5;
x_45 = lean_string_dec_eq(x_38, x_44);
lean_dec(x_38);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_30);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_3);
x_46 = l_Array_umapMAux___main___at___private_Init_Lean_Elaborator_PreTerm_4__processBinder___spec__1___closed__2;
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_26);
return x_47;
}
else
{
lean_object* x_48; uint8_t x_49; 
x_48 = l_Lean_Parser_Term_explicitUniv___elambda__1___closed__1;
x_49 = lean_string_dec_eq(x_37, x_48);
lean_dec(x_37);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
lean_dec(x_36);
lean_dec(x_30);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_3);
x_50 = l_Array_umapMAux___main___at___private_Init_Lean_Elaborator_PreTerm_4__processBinder___spec__1___closed__2;
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_26);
return x_51;
}
else
{
lean_object* x_52; uint8_t x_53; 
x_52 = l_Lean_Parser_Term_binderDefault___elambda__1___rarg___closed__1;
x_53 = lean_string_dec_eq(x_36, x_52);
if (x_53 == 0)
{
lean_object* x_54; uint8_t x_55; 
lean_dec(x_30);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_3);
x_54 = l_Lean_Parser_Term_binderTactic___elambda__1___rarg___closed__1;
x_55 = lean_string_dec_eq(x_36, x_54);
lean_dec(x_36);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; 
lean_dec(x_5);
x_56 = l_Array_umapMAux___main___at___private_Init_Lean_Elaborator_PreTerm_4__processBinder___spec__1___closed__2;
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_26);
return x_57;
}
else
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_58 = l_Array_umapMAux___main___at___private_Init_Lean_Elaborator_PreTerm_4__processBinder___spec__1___closed__3;
x_59 = l_Lean_Elab_logErrorAndThrow___rarg(x_2, x_58, x_5, x_26);
lean_dec(x_5);
x_60 = !lean_is_exclusive(x_59);
if (x_60 == 0)
{
return x_59;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_59, 0);
x_62 = lean_ctor_get(x_59, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_59);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_36);
x_64 = lean_unsigned_to_nat(1u);
x_65 = l_Lean_Syntax_getArg___rarg(x_30, x_64);
lean_dec(x_30);
lean_inc(x_5);
x_66 = l_Lean_Elab_toPreTerm(x_65, x_5, x_26);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = l_Array_umapMAux___main___at___private_Init_Lean_Elaborator_PreTerm_4__processBinder___spec__1___closed__4;
x_70 = lean_name_mk_string(x_35, x_69);
x_71 = lean_box(0);
x_72 = l_Lean_mkConst(x_70, x_71);
x_73 = l_Lean_mkApp(x_72, x_25);
x_74 = l_Lean_mkApp(x_73, x_67);
x_75 = 0;
x_76 = l_Lean_Elab_mkLocalDecl(x_24, x_74, x_75, x_5, x_68);
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_16 = x_77;
x_17 = x_78;
goto block_23;
}
else
{
uint8_t x_79; 
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_3);
x_79 = !lean_is_exclusive(x_66);
if (x_79 == 0)
{
return x_66;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_66, 0);
x_81 = lean_ctor_get(x_66, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_66);
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
}
else
{
lean_object* x_83; lean_object* x_84; 
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_3);
x_83 = l_Array_umapMAux___main___at___private_Init_Lean_Elaborator_PreTerm_4__processBinder___spec__1___closed__2;
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_26);
return x_84;
}
}
else
{
lean_object* x_85; lean_object* x_86; 
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_3);
x_85 = l_Array_umapMAux___main___at___private_Init_Lean_Elaborator_PreTerm_4__processBinder___spec__1___closed__2;
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_26);
return x_86;
}
}
else
{
lean_object* x_87; lean_object* x_88; 
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_3);
x_87 = l_Array_umapMAux___main___at___private_Init_Lean_Elaborator_PreTerm_4__processBinder___spec__1___closed__2;
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_26);
return x_88;
}
}
else
{
lean_object* x_89; lean_object* x_90; 
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_3);
x_89 = l_Array_umapMAux___main___at___private_Init_Lean_Elaborator_PreTerm_4__processBinder___spec__1___closed__2;
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_26);
return x_90;
}
}
else
{
lean_object* x_91; lean_object* x_92; 
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_3);
x_91 = l_Array_umapMAux___main___at___private_Init_Lean_Elaborator_PreTerm_4__processBinder___spec__1___closed__2;
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_26);
return x_92;
}
}
else
{
uint8_t x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_93 = 0;
x_94 = l_Lean_Elab_mkLocalDecl(x_24, x_25, x_93, x_5, x_26);
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
lean_dec(x_94);
x_16 = x_95;
x_17 = x_96;
goto block_23;
}
}
}
}
}
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Elaborator_PreTerm_4__processBinder___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_2);
x_6 = lean_nat_dec_lt(x_1, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_1);
x_7 = l_Array_empty___closed__1;
x_8 = x_2;
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_4);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_10 = lean_array_fget(x_2, x_1);
x_11 = lean_box(0);
lean_inc(x_10);
x_12 = x_11;
x_13 = lean_array_fset(x_2, x_1, x_12);
x_14 = l_Lean_Syntax_getId___rarg(x_10);
x_15 = l___private_Init_Lean_Elaborator_PreTerm_2__mkHoleFor(x_10, x_3, x_4);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = 0;
x_19 = l_Lean_Elab_mkLocalDecl(x_14, x_16, x_18, x_3, x_17);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_add(x_1, x_22);
x_24 = x_20;
x_25 = lean_array_fset(x_13, x_1, x_24);
lean_dec(x_1);
x_1 = x_23;
x_2 = x_25;
x_4 = x_21;
goto _start;
}
}
}
lean_object* _init_l___private_Init_Lean_Elaborator_PreTerm_4__processBinder___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unknown binder kind");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Elaborator_PreTerm_4__processBinder___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elaborator_PreTerm_4__processBinder___closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elaborator_PreTerm_4__processBinder___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(">> inst ");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Elaborator_PreTerm_4__processBinder___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(">> implict ");
return x_1;
}
}
lean_object* l___private_Init_Lean_Elaborator_PreTerm_4__processBinder(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Syntax_getKind___rarg(x_1);
if (lean_obj_tag(x_4) == 1)
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 1)
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 1)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 1)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_9 = lean_ctor_get(x_4, 1);
lean_inc(x_9);
lean_dec(x_4);
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
lean_dec(x_5);
x_11 = lean_ctor_get(x_6, 1);
lean_inc(x_11);
lean_dec(x_6);
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_12);
lean_dec(x_7);
x_13 = l_Lean_nameToExprAux___main___closed__1;
x_14 = lean_string_dec_eq(x_12, x_13);
lean_dec(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_2);
lean_dec(x_1);
x_15 = l___private_Init_Lean_Elaborator_PreTerm_4__processBinder___closed__2;
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_3);
return x_16;
}
else
{
lean_object* x_17; uint8_t x_18; 
x_17 = l_Lean_Syntax_formatStx___main___rarg___closed__5;
x_18 = lean_string_dec_eq(x_11, x_17);
lean_dec(x_11);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_2);
lean_dec(x_1);
x_19 = l___private_Init_Lean_Elaborator_PreTerm_4__processBinder___closed__2;
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_3);
return x_20;
}
else
{
lean_object* x_21; uint8_t x_22; 
x_21 = l_Lean_Parser_Term_explicitUniv___elambda__1___closed__1;
x_22 = lean_string_dec_eq(x_10, x_21);
lean_dec(x_10);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_9);
lean_dec(x_2);
lean_dec(x_1);
x_23 = l___private_Init_Lean_Elaborator_PreTerm_4__processBinder___closed__2;
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_3);
return x_24;
}
else
{
lean_object* x_25; uint8_t x_26; 
x_25 = l_Lean_Parser_Term_simpleBinder___elambda__1___closed__1;
x_26 = lean_string_dec_eq(x_9, x_25);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; 
x_27 = l_Lean_Parser_Term_explicitBinder___elambda__1___closed__1;
x_28 = lean_string_dec_eq(x_9, x_27);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = l_Lean_Parser_Term_implicitBinder___elambda__1___closed__1;
x_30 = lean_string_dec_eq(x_9, x_29);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; 
x_31 = l_Lean_Parser_Term_instBinder___elambda__1___rarg___closed__1;
x_32 = lean_string_dec_eq(x_9, x_31);
lean_dec(x_9);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_2);
lean_dec(x_1);
x_33 = l___private_Init_Lean_Elaborator_PreTerm_4__processBinder___closed__2;
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_3);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_35 = l_Lean_Syntax_formatStx___main___rarg(x_1);
x_36 = l_Lean_Options_empty;
x_37 = l_Lean_Format_pretty(x_35, x_36);
x_38 = l___private_Init_Lean_Elaborator_PreTerm_4__processBinder___closed__3;
x_39 = lean_string_append(x_38, x_37);
lean_dec(x_37);
x_40 = lean_alloc_closure((void*)(l_IO_println___at_HasRepr_HasEval___spec__1___boxed), 2, 1);
lean_closure_set(x_40, 0, x_39);
x_41 = l_Lean_Elab_runIOUnsafe___rarg(x_40, x_2, x_3);
lean_dec(x_2);
if (lean_obj_tag(x_41) == 0)
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_41, 0);
lean_dec(x_43);
x_44 = l_Array_empty___closed__1;
lean_ctor_set(x_41, 0, x_44);
return x_41;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_41, 1);
lean_inc(x_45);
lean_dec(x_41);
x_46 = l_Array_empty___closed__1;
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
return x_47;
}
}
else
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_41);
if (x_48 == 0)
{
return x_41;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_41, 0);
x_50 = lean_ctor_get(x_41, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_41);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_9);
x_52 = l_Lean_Syntax_formatStx___main___rarg(x_1);
x_53 = l_Lean_Options_empty;
x_54 = l_Lean_Format_pretty(x_52, x_53);
x_55 = l___private_Init_Lean_Elaborator_PreTerm_4__processBinder___closed__4;
x_56 = lean_string_append(x_55, x_54);
lean_dec(x_54);
x_57 = lean_alloc_closure((void*)(l_IO_println___at_HasRepr_HasEval___spec__1___boxed), 2, 1);
lean_closure_set(x_57, 0, x_56);
x_58 = l_Lean_Elab_runIOUnsafe___rarg(x_57, x_2, x_3);
lean_dec(x_2);
if (lean_obj_tag(x_58) == 0)
{
uint8_t x_59; 
x_59 = !lean_is_exclusive(x_58);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_58, 0);
lean_dec(x_60);
x_61 = l_Array_empty___closed__1;
lean_ctor_set(x_58, 0, x_61);
return x_58;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_58, 1);
lean_inc(x_62);
lean_dec(x_58);
x_63 = l_Array_empty___closed__1;
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_62);
return x_64;
}
}
else
{
uint8_t x_65; 
x_65 = !lean_is_exclusive(x_58);
if (x_65 == 0)
{
return x_58;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_58, 0);
x_67 = lean_ctor_get(x_58, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_58);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_9);
x_69 = lean_unsigned_to_nat(1u);
x_70 = l_Lean_Syntax_getArg___rarg(x_1, x_69);
x_71 = l_Lean_Syntax_getArgs___rarg(x_70);
lean_dec(x_70);
x_72 = lean_unsigned_to_nat(2u);
x_73 = l_Lean_Syntax_getArg___rarg(x_1, x_72);
x_74 = lean_unsigned_to_nat(3u);
x_75 = l_Lean_Syntax_getArg___rarg(x_1, x_74);
lean_dec(x_1);
x_76 = lean_unsigned_to_nat(0u);
x_77 = l_Array_umapMAux___main___at___private_Init_Lean_Elaborator_PreTerm_4__processBinder___spec__1(x_73, x_75, x_76, x_71, x_2, x_3);
lean_dec(x_75);
lean_dec(x_73);
return x_77;
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_9);
x_78 = lean_unsigned_to_nat(0u);
x_79 = l_Lean_Syntax_getArg___rarg(x_1, x_78);
lean_dec(x_1);
x_80 = l_Lean_Syntax_getArgs___rarg(x_79);
lean_dec(x_79);
x_81 = l_Array_umapMAux___main___at___private_Init_Lean_Elaborator_PreTerm_4__processBinder___spec__2(x_78, x_80, x_2, x_3);
lean_dec(x_2);
return x_81;
}
}
}
}
}
else
{
lean_object* x_82; lean_object* x_83; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_82 = l___private_Init_Lean_Elaborator_PreTerm_4__processBinder___closed__2;
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_3);
return x_83;
}
}
else
{
lean_object* x_84; lean_object* x_85; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_84 = l___private_Init_Lean_Elaborator_PreTerm_4__processBinder___closed__2;
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_3);
return x_85;
}
}
else
{
lean_object* x_86; lean_object* x_87; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_86 = l___private_Init_Lean_Elaborator_PreTerm_4__processBinder___closed__2;
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_3);
return x_87;
}
}
else
{
lean_object* x_88; lean_object* x_89; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_88 = l___private_Init_Lean_Elaborator_PreTerm_4__processBinder___closed__2;
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_3);
return x_89;
}
}
else
{
lean_object* x_90; lean_object* x_91; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_90 = l___private_Init_Lean_Elaborator_PreTerm_4__processBinder___closed__2;
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_3);
return x_91;
}
}
}
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Elaborator_PreTerm_4__processBinder___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_umapMAux___main___at___private_Init_Lean_Elaborator_PreTerm_4__processBinder___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Elaborator_PreTerm_4__processBinder___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_umapMAux___main___at___private_Init_Lean_Elaborator_PreTerm_4__processBinder___spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_Elaborator_PreTerm_5__processBinders___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_2);
x_8 = lean_nat_dec_lt(x_3, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_5);
lean_dec(x_3);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_array_fget(x_2, x_3);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_3, x_11);
lean_dec(x_3);
lean_inc(x_5);
x_13 = l___private_Init_Lean_Elaborator_PreTerm_4__processBinder(x_10, x_5, x_6);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_unsigned_to_nat(0u);
x_17 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_14, x_14, x_16, x_4);
lean_dec(x_14);
x_3 = x_12;
x_4 = x_17;
x_6 = x_15;
goto _start;
}
else
{
uint8_t x_19; 
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
x_19 = !lean_is_exclusive(x_13);
if (x_19 == 0)
{
return x_13;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_13, 0);
x_21 = lean_ctor_get(x_13, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_13);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
}
lean_object* l___private_Init_Lean_Elaborator_PreTerm_5__processBinders(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Array_empty___closed__1;
x_6 = l_Array_iterateMAux___main___at___private_Init_Lean_Elaborator_PreTerm_5__processBinders___spec__1(x_1, x_1, x_4, x_5, x_2, x_3);
return x_6;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_Elaborator_PreTerm_5__processBinders___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_iterateMAux___main___at___private_Init_Lean_Elaborator_PreTerm_5__processBinders___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l___private_Init_Lean_Elaborator_PreTerm_5__processBinders___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Elaborator_PreTerm_5__processBinders(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Elab_convertForall(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_5 = lean_ctor_get(x_3, 5);
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_List_head_x21___at_Lean_Elab_getScope___spec__1(x_5);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_5);
lean_ctor_set(x_3, 5, x_8);
x_9 = lean_box(0);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_array_get(x_9, x_6, x_10);
x_12 = l_Lean_Syntax_getArgs___rarg(x_11);
lean_dec(x_11);
lean_inc(x_2);
x_13 = l___private_Init_Lean_Elaborator_PreTerm_5__processBinders(x_12, x_2, x_3);
lean_dec(x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_unsigned_to_nat(3u);
x_17 = lean_array_get(x_9, x_6, x_16);
lean_inc(x_2);
x_18 = l_Lean_Elab_toPreTerm(x_17, x_2, x_15);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_Elab_mkForall(x_14, x_19, x_2, x_20);
lean_dec(x_2);
lean_dec(x_19);
lean_dec(x_14);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_21, 1);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_23, 5);
x_26 = l_List_tail_x21___rarg(x_25);
lean_dec(x_25);
lean_ctor_set(x_23, 5, x_26);
return x_21;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_27 = lean_ctor_get(x_23, 0);
x_28 = lean_ctor_get(x_23, 1);
x_29 = lean_ctor_get(x_23, 2);
x_30 = lean_ctor_get(x_23, 3);
x_31 = lean_ctor_get(x_23, 4);
x_32 = lean_ctor_get(x_23, 5);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_23);
x_33 = l_List_tail_x21___rarg(x_32);
lean_dec(x_32);
x_34 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_34, 0, x_27);
lean_ctor_set(x_34, 1, x_28);
lean_ctor_set(x_34, 2, x_29);
lean_ctor_set(x_34, 3, x_30);
lean_ctor_set(x_34, 4, x_31);
lean_ctor_set(x_34, 5, x_33);
lean_ctor_set(x_21, 1, x_34);
return x_21;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_35 = lean_ctor_get(x_21, 1);
x_36 = lean_ctor_get(x_21, 0);
lean_inc(x_35);
lean_inc(x_36);
lean_dec(x_21);
x_37 = lean_ctor_get(x_35, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
x_39 = lean_ctor_get(x_35, 2);
lean_inc(x_39);
x_40 = lean_ctor_get(x_35, 3);
lean_inc(x_40);
x_41 = lean_ctor_get(x_35, 4);
lean_inc(x_41);
x_42 = lean_ctor_get(x_35, 5);
lean_inc(x_42);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 lean_ctor_release(x_35, 2);
 lean_ctor_release(x_35, 3);
 lean_ctor_release(x_35, 4);
 lean_ctor_release(x_35, 5);
 x_43 = x_35;
} else {
 lean_dec_ref(x_35);
 x_43 = lean_box(0);
}
x_44 = l_List_tail_x21___rarg(x_42);
lean_dec(x_42);
if (lean_is_scalar(x_43)) {
 x_45 = lean_alloc_ctor(0, 6, 0);
} else {
 x_45 = x_43;
}
lean_ctor_set(x_45, 0, x_37);
lean_ctor_set(x_45, 1, x_38);
lean_ctor_set(x_45, 2, x_39);
lean_ctor_set(x_45, 3, x_40);
lean_ctor_set(x_45, 4, x_41);
lean_ctor_set(x_45, 5, x_44);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_36);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
else
{
uint8_t x_47; 
lean_dec(x_14);
lean_dec(x_2);
x_47 = !lean_is_exclusive(x_18);
if (x_47 == 0)
{
return x_18;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_18, 0);
x_49 = lean_ctor_get(x_18, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_18);
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
lean_dec(x_2);
x_51 = !lean_is_exclusive(x_13);
if (x_51 == 0)
{
return x_13;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_13, 0);
x_53 = lean_ctor_get(x_13, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_13);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_55 = lean_ctor_get(x_3, 0);
x_56 = lean_ctor_get(x_3, 1);
x_57 = lean_ctor_get(x_3, 2);
x_58 = lean_ctor_get(x_3, 3);
x_59 = lean_ctor_get(x_3, 4);
x_60 = lean_ctor_get(x_3, 5);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_3);
x_61 = lean_ctor_get(x_1, 1);
x_62 = l_List_head_x21___at_Lean_Elab_getScope___spec__1(x_60);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_60);
x_64 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_64, 0, x_55);
lean_ctor_set(x_64, 1, x_56);
lean_ctor_set(x_64, 2, x_57);
lean_ctor_set(x_64, 3, x_58);
lean_ctor_set(x_64, 4, x_59);
lean_ctor_set(x_64, 5, x_63);
x_65 = lean_box(0);
x_66 = lean_unsigned_to_nat(1u);
x_67 = lean_array_get(x_65, x_61, x_66);
x_68 = l_Lean_Syntax_getArgs___rarg(x_67);
lean_dec(x_67);
lean_inc(x_2);
x_69 = l___private_Init_Lean_Elaborator_PreTerm_5__processBinders(x_68, x_2, x_64);
lean_dec(x_68);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_72 = lean_unsigned_to_nat(3u);
x_73 = lean_array_get(x_65, x_61, x_72);
lean_inc(x_2);
x_74 = l_Lean_Elab_toPreTerm(x_73, x_2, x_71);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
x_77 = l_Lean_Elab_mkForall(x_70, x_75, x_2, x_76);
lean_dec(x_2);
lean_dec(x_75);
lean_dec(x_70);
x_78 = lean_ctor_get(x_77, 1);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 0);
lean_inc(x_79);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 x_80 = x_77;
} else {
 lean_dec_ref(x_77);
 x_80 = lean_box(0);
}
x_81 = lean_ctor_get(x_78, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_78, 1);
lean_inc(x_82);
x_83 = lean_ctor_get(x_78, 2);
lean_inc(x_83);
x_84 = lean_ctor_get(x_78, 3);
lean_inc(x_84);
x_85 = lean_ctor_get(x_78, 4);
lean_inc(x_85);
x_86 = lean_ctor_get(x_78, 5);
lean_inc(x_86);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 lean_ctor_release(x_78, 2);
 lean_ctor_release(x_78, 3);
 lean_ctor_release(x_78, 4);
 lean_ctor_release(x_78, 5);
 x_87 = x_78;
} else {
 lean_dec_ref(x_78);
 x_87 = lean_box(0);
}
x_88 = l_List_tail_x21___rarg(x_86);
lean_dec(x_86);
if (lean_is_scalar(x_87)) {
 x_89 = lean_alloc_ctor(0, 6, 0);
} else {
 x_89 = x_87;
}
lean_ctor_set(x_89, 0, x_81);
lean_ctor_set(x_89, 1, x_82);
lean_ctor_set(x_89, 2, x_83);
lean_ctor_set(x_89, 3, x_84);
lean_ctor_set(x_89, 4, x_85);
lean_ctor_set(x_89, 5, x_88);
if (lean_is_scalar(x_80)) {
 x_90 = lean_alloc_ctor(0, 2, 0);
} else {
 x_90 = x_80;
}
lean_ctor_set(x_90, 0, x_79);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_dec(x_70);
lean_dec(x_2);
x_91 = lean_ctor_get(x_74, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_74, 1);
lean_inc(x_92);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_93 = x_74;
} else {
 lean_dec_ref(x_74);
 x_93 = lean_box(0);
}
if (lean_is_scalar(x_93)) {
 x_94 = lean_alloc_ctor(1, 2, 0);
} else {
 x_94 = x_93;
}
lean_ctor_set(x_94, 0, x_91);
lean_ctor_set(x_94, 1, x_92);
return x_94;
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
lean_dec(x_2);
x_95 = lean_ctor_get(x_69, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_69, 1);
lean_inc(x_96);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_97 = x_69;
} else {
 lean_dec_ref(x_69);
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
}
}
lean_object* l_Lean_Elab_convertForall___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_convertForall(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_convertForall___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("convertForall");
return x_1;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_convertForall___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltinTermElab_Lean_Elab_convertType___closed__2;
x_2 = l___regBuiltinTermElab_Lean_Elab_convertForall___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_convertForall___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_convertForall___boxed), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltinTermElab_Lean_Elab_convertForall(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Parser_Term_forall___elambda__1___closed__2;
x_3 = l___regBuiltinTermElab_Lean_Elab_convertForall___closed__2;
x_4 = l___regBuiltinTermElab_Lean_Elab_convertForall___closed__3;
x_5 = l_Lean_addBuiltinPreTermElab(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_convertHole___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l___private_Init_Lean_Elaborator_PreTerm_2__mkHoleFor___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_convertHole(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Elab_convertHole___rarg), 1, 0);
return x_3;
}
}
lean_object* l_Lean_Elab_convertHole___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_convertHole(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_convertHole___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("convertHole");
return x_1;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_convertHole___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltinTermElab_Lean_Elab_convertType___closed__2;
x_2 = l___regBuiltinTermElab_Lean_Elab_convertHole___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_convertHole___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_convertHole___boxed), 2, 0);
return x_1;
}
}
lean_object* l___regBuiltinTermElab_Lean_Elab_convertHole(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Parser_Term_hole___elambda__1___rarg___closed__1;
x_3 = l___regBuiltinTermElab_Lean_Elab_convertHole___closed__2;
x_4 = l___regBuiltinTermElab_Lean_Elab_convertHole___closed__3;
x_5 = l_Lean_addBuiltinPreTermElab(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* _init_l_Lean_Elab_convertSorry___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("sorryAx");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_convertSorry___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_convertSorry___rarg___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_convertSorry___rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_convertSorry___rarg___closed__2;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_convertSorry___rarg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_convertSorry___rarg___closed__3;
x_2 = l___private_Init_Lean_Elaborator_PreTerm_2__mkHoleFor___closed__1;
x_3 = l_Lean_mkApp(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_convertSorry___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_convertSorry___rarg___closed__4;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_convertSorry(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Elab_convertSorry___rarg), 1, 0);
return x_3;
}
}
lean_object* l_Lean_Elab_convertSorry___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_convertSorry(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_convertSorry___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("convertSorry");
return x_1;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_convertSorry___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltinTermElab_Lean_Elab_convertType___closed__2;
x_2 = l___regBuiltinTermElab_Lean_Elab_convertSorry___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_convertSorry___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_convertSorry___boxed), 2, 0);
return x_1;
}
}
lean_object* l___regBuiltinTermElab_Lean_Elab_convertSorry(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Parser_Term_sorry___elambda__1___rarg___closed__2;
x_3 = l___regBuiltinTermElab_Lean_Elab_convertSorry___closed__2;
x_4 = l___regBuiltinTermElab_Lean_Elab_convertSorry___closed__3;
x_5 = l_Lean_addBuiltinPreTermElab(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* _init_l_Lean_Elab_convertId___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unknown identifier '");
return x_1;
}
}
lean_object* l_Lean_Elab_convertId(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = l_Lean_Elab_localContext___rarg(x_3);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
x_9 = lean_box(0);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_array_get(x_9, x_4, x_10);
x_12 = l_Lean_Syntax_getId___rarg(x_11);
lean_dec(x_11);
lean_inc(x_12);
x_13 = lean_local_ctx_find_from_user_name(x_7, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_free_object(x_5);
x_14 = l_System_FilePath_dirName___closed__1;
x_15 = l_Lean_Name_toStringWithSep___main(x_14, x_12);
x_16 = l_Lean_Elab_convertId___closed__1;
x_17 = lean_string_append(x_16, x_15);
lean_dec(x_15);
x_18 = l_Char_HasRepr___closed__1;
x_19 = lean_string_append(x_17, x_18);
x_20 = l_Lean_Elab_logErrorAndThrow___rarg(x_1, x_19, x_2, x_8);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_12);
x_21 = lean_ctor_get(x_13, 0);
lean_inc(x_21);
lean_dec(x_13);
x_22 = l___private_Init_Lean_Elaborator_PreTerm_3__mkLocalAux(x_21);
lean_dec(x_21);
lean_ctor_set(x_5, 0, x_22);
return x_5;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_23 = lean_ctor_get(x_5, 0);
x_24 = lean_ctor_get(x_5, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_5);
x_25 = lean_box(0);
x_26 = lean_unsigned_to_nat(0u);
x_27 = lean_array_get(x_25, x_4, x_26);
x_28 = l_Lean_Syntax_getId___rarg(x_27);
lean_dec(x_27);
lean_inc(x_28);
x_29 = lean_local_ctx_find_from_user_name(x_23, x_28);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_30 = l_System_FilePath_dirName___closed__1;
x_31 = l_Lean_Name_toStringWithSep___main(x_30, x_28);
x_32 = l_Lean_Elab_convertId___closed__1;
x_33 = lean_string_append(x_32, x_31);
lean_dec(x_31);
x_34 = l_Char_HasRepr___closed__1;
x_35 = lean_string_append(x_33, x_34);
x_36 = l_Lean_Elab_logErrorAndThrow___rarg(x_1, x_35, x_2, x_24);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_28);
x_37 = lean_ctor_get(x_29, 0);
lean_inc(x_37);
lean_dec(x_29);
x_38 = l___private_Init_Lean_Elaborator_PreTerm_3__mkLocalAux(x_37);
lean_dec(x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_24);
return x_39;
}
}
}
}
lean_object* l_Lean_Elab_convertId___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_convertId(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_convertId___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("convertId");
return x_1;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_convertId___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltinTermElab_Lean_Elab_convertType___closed__2;
x_2 = l___regBuiltinTermElab_Lean_Elab_convertId___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_convertId___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_convertId___boxed), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltinTermElab_Lean_Elab_convertId(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Parser_Term_id___elambda__1___closed__2;
x_3 = l___regBuiltinTermElab_Lean_Elab_convertId___closed__2;
x_4 = l___regBuiltinTermElab_Lean_Elab_convertId___closed__3;
x_5 = l_Lean_addBuiltinPreTermElab(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_oldElaborate(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_3);
lean_inc(x_1);
x_5 = l_Lean_Elab_toPreTerm(x_1, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l_Lean_Elab_getScope___rarg(x_7);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_10 = lean_ctor_get(x_8, 1);
x_11 = lean_ctor_get(x_8, 0);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_10, 2);
lean_inc(x_14);
x_15 = lean_ctor_get(x_10, 3);
lean_inc(x_15);
x_16 = lean_ctor_get(x_10, 4);
lean_inc(x_16);
x_17 = lean_ctor_get(x_10, 5);
lean_inc(x_17);
x_18 = lean_ctor_get(x_11, 2);
lean_inc(x_18);
x_19 = lean_ctor_get(x_11, 6);
lean_inc(x_19);
lean_dec(x_11);
x_20 = l_Lean_mkPreTypeAscriptionIfSome(x_6, x_2);
lean_inc(x_18);
x_21 = lean_old_elaborate(x_12, x_18, x_16, x_19, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_free_object(x_8);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_Format_pretty(x_24, x_18);
lean_dec(x_18);
x_26 = l_Lean_Elab_logErrorAndThrow___rarg(x_1, x_25, x_3, x_10);
lean_dec(x_3);
lean_dec(x_1);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
lean_dec(x_18);
lean_dec(x_1);
x_27 = lean_ctor_get(x_22, 1);
lean_inc(x_27);
lean_dec(x_22);
x_28 = lean_ctor_get(x_23, 0);
lean_inc(x_28);
lean_dec(x_23);
x_29 = lean_ctor_get(x_3, 0);
lean_inc(x_29);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_27);
x_32 = 2;
x_33 = l_String_splitAux___main___closed__1;
x_34 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_34, 0, x_29);
lean_ctor_set(x_34, 1, x_28);
lean_ctor_set(x_34, 2, x_30);
lean_ctor_set(x_34, 3, x_33);
lean_ctor_set(x_34, 4, x_31);
lean_ctor_set_uint8(x_34, sizeof(void*)*5, x_32);
x_35 = l_Lean_Elab_logMessage(x_34, x_3, x_10);
lean_dec(x_3);
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_35, 0);
lean_dec(x_37);
x_38 = lean_box(4);
lean_ctor_set_tag(x_35, 1);
lean_ctor_set(x_35, 0, x_38);
return x_35;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_35, 1);
lean_inc(x_39);
lean_dec(x_35);
x_40 = lean_box(4);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
return x_41;
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_18);
lean_dec(x_3);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_10);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_43 = lean_ctor_get(x_10, 5);
lean_dec(x_43);
x_44 = lean_ctor_get(x_10, 4);
lean_dec(x_44);
x_45 = lean_ctor_get(x_10, 3);
lean_dec(x_45);
x_46 = lean_ctor_get(x_10, 2);
lean_dec(x_46);
x_47 = lean_ctor_get(x_10, 1);
lean_dec(x_47);
x_48 = lean_ctor_get(x_10, 0);
lean_dec(x_48);
x_49 = lean_ctor_get(x_21, 0);
lean_inc(x_49);
lean_dec(x_21);
x_50 = lean_ctor_get(x_49, 1);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 0);
lean_inc(x_51);
lean_dec(x_49);
x_52 = lean_ctor_get(x_50, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_50, 1);
lean_inc(x_53);
lean_dec(x_50);
lean_ctor_set(x_10, 4, x_52);
lean_ctor_set(x_10, 0, x_51);
lean_ctor_set(x_8, 0, x_53);
return x_8;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_10);
x_54 = lean_ctor_get(x_21, 0);
lean_inc(x_54);
lean_dec(x_21);
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 0);
lean_inc(x_56);
lean_dec(x_54);
x_57 = lean_ctor_get(x_55, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_55, 1);
lean_inc(x_58);
lean_dec(x_55);
x_59 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_59, 0, x_56);
lean_ctor_set(x_59, 1, x_13);
lean_ctor_set(x_59, 2, x_14);
lean_ctor_set(x_59, 3, x_15);
lean_ctor_set(x_59, 4, x_57);
lean_ctor_set(x_59, 5, x_17);
lean_ctor_set(x_8, 1, x_59);
lean_ctor_set(x_8, 0, x_58);
return x_8;
}
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_60 = lean_ctor_get(x_8, 1);
x_61 = lean_ctor_get(x_8, 0);
lean_inc(x_60);
lean_inc(x_61);
lean_dec(x_8);
x_62 = lean_ctor_get(x_60, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_60, 1);
lean_inc(x_63);
x_64 = lean_ctor_get(x_60, 2);
lean_inc(x_64);
x_65 = lean_ctor_get(x_60, 3);
lean_inc(x_65);
x_66 = lean_ctor_get(x_60, 4);
lean_inc(x_66);
x_67 = lean_ctor_get(x_60, 5);
lean_inc(x_67);
x_68 = lean_ctor_get(x_61, 2);
lean_inc(x_68);
x_69 = lean_ctor_get(x_61, 6);
lean_inc(x_69);
lean_dec(x_61);
x_70 = l_Lean_mkPreTypeAscriptionIfSome(x_6, x_2);
lean_inc(x_68);
x_71 = lean_old_elaborate(x_62, x_68, x_66, x_69, x_70);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; 
lean_dec(x_67);
lean_dec(x_65);
lean_dec(x_64);
lean_dec(x_63);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
lean_dec(x_71);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
x_75 = l_Lean_Format_pretty(x_74, x_68);
lean_dec(x_68);
x_76 = l_Lean_Elab_logErrorAndThrow___rarg(x_1, x_75, x_3, x_60);
lean_dec(x_3);
lean_dec(x_1);
return x_76;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_dec(x_68);
lean_dec(x_1);
x_77 = lean_ctor_get(x_72, 1);
lean_inc(x_77);
lean_dec(x_72);
x_78 = lean_ctor_get(x_73, 0);
lean_inc(x_78);
lean_dec(x_73);
x_79 = lean_ctor_get(x_3, 0);
lean_inc(x_79);
x_80 = lean_box(0);
x_81 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_81, 0, x_77);
x_82 = 2;
x_83 = l_String_splitAux___main___closed__1;
x_84 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_84, 0, x_79);
lean_ctor_set(x_84, 1, x_78);
lean_ctor_set(x_84, 2, x_80);
lean_ctor_set(x_84, 3, x_83);
lean_ctor_set(x_84, 4, x_81);
lean_ctor_set_uint8(x_84, sizeof(void*)*5, x_82);
x_85 = l_Lean_Elab_logMessage(x_84, x_3, x_60);
lean_dec(x_3);
x_86 = lean_ctor_get(x_85, 1);
lean_inc(x_86);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 lean_ctor_release(x_85, 1);
 x_87 = x_85;
} else {
 lean_dec_ref(x_85);
 x_87 = lean_box(0);
}
x_88 = lean_box(4);
if (lean_is_scalar(x_87)) {
 x_89 = lean_alloc_ctor(1, 2, 0);
} else {
 x_89 = x_87;
 lean_ctor_set_tag(x_89, 1);
}
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_86);
return x_89;
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_68);
lean_dec(x_3);
lean_dec(x_1);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 lean_ctor_release(x_60, 2);
 lean_ctor_release(x_60, 3);
 lean_ctor_release(x_60, 4);
 lean_ctor_release(x_60, 5);
 x_90 = x_60;
} else {
 lean_dec_ref(x_60);
 x_90 = lean_box(0);
}
x_91 = lean_ctor_get(x_71, 0);
lean_inc(x_91);
lean_dec(x_71);
x_92 = lean_ctor_get(x_91, 1);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 0);
lean_inc(x_93);
lean_dec(x_91);
x_94 = lean_ctor_get(x_92, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_92, 1);
lean_inc(x_95);
lean_dec(x_92);
if (lean_is_scalar(x_90)) {
 x_96 = lean_alloc_ctor(0, 6, 0);
} else {
 x_96 = x_90;
}
lean_ctor_set(x_96, 0, x_93);
lean_ctor_set(x_96, 1, x_63);
lean_ctor_set(x_96, 2, x_64);
lean_ctor_set(x_96, 3, x_65);
lean_ctor_set(x_96, 4, x_94);
lean_ctor_set(x_96, 5, x_67);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
}
else
{
uint8_t x_98; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_98 = !lean_is_exclusive(x_5);
if (x_98 == 0)
{
return x_5;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_5, 0);
x_100 = lean_ctor_get(x_5, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_5);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
return x_101;
}
}
}
}
lean_object* initialize_Init_Lean_Elaborator_Basic(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Elaborator_PreTerm(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Lean_Elaborator_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_mkBuiltinPreTermElabTable___closed__1 = _init_l_Lean_mkBuiltinPreTermElabTable___closed__1();
lean_mark_persistent(l_Lean_mkBuiltinPreTermElabTable___closed__1);
res = l_Lean_mkBuiltinPreTermElabTable(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_builtinPreTermElabTable = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_builtinPreTermElabTable);
lean_dec_ref(res);
l_Lean_declareBuiltinPreTermElab___closed__1 = _init_l_Lean_declareBuiltinPreTermElab___closed__1();
lean_mark_persistent(l_Lean_declareBuiltinPreTermElab___closed__1);
l_Lean_declareBuiltinPreTermElab___closed__2 = _init_l_Lean_declareBuiltinPreTermElab___closed__2();
lean_mark_persistent(l_Lean_declareBuiltinPreTermElab___closed__2);
l_Lean_registerBuiltinPreTermElabAttr___lambda__1___closed__1 = _init_l_Lean_registerBuiltinPreTermElabAttr___lambda__1___closed__1();
lean_mark_persistent(l_Lean_registerBuiltinPreTermElabAttr___lambda__1___closed__1);
l_Lean_registerBuiltinPreTermElabAttr___lambda__1___closed__2 = _init_l_Lean_registerBuiltinPreTermElabAttr___lambda__1___closed__2();
lean_mark_persistent(l_Lean_registerBuiltinPreTermElabAttr___lambda__1___closed__2);
l_Lean_registerBuiltinPreTermElabAttr___lambda__1___closed__3 = _init_l_Lean_registerBuiltinPreTermElabAttr___lambda__1___closed__3();
lean_mark_persistent(l_Lean_registerBuiltinPreTermElabAttr___lambda__1___closed__3);
l_Lean_registerBuiltinPreTermElabAttr___lambda__1___closed__4 = _init_l_Lean_registerBuiltinPreTermElabAttr___lambda__1___closed__4();
lean_mark_persistent(l_Lean_registerBuiltinPreTermElabAttr___lambda__1___closed__4);
l_Lean_registerBuiltinPreTermElabAttr___closed__1 = _init_l_Lean_registerBuiltinPreTermElabAttr___closed__1();
lean_mark_persistent(l_Lean_registerBuiltinPreTermElabAttr___closed__1);
l_Lean_registerBuiltinPreTermElabAttr___closed__2 = _init_l_Lean_registerBuiltinPreTermElabAttr___closed__2();
lean_mark_persistent(l_Lean_registerBuiltinPreTermElabAttr___closed__2);
l_Lean_registerBuiltinPreTermElabAttr___closed__3 = _init_l_Lean_registerBuiltinPreTermElabAttr___closed__3();
lean_mark_persistent(l_Lean_registerBuiltinPreTermElabAttr___closed__3);
l_Lean_registerBuiltinPreTermElabAttr___closed__4 = _init_l_Lean_registerBuiltinPreTermElabAttr___closed__4();
lean_mark_persistent(l_Lean_registerBuiltinPreTermElabAttr___closed__4);
l_Lean_registerBuiltinPreTermElabAttr___closed__5 = _init_l_Lean_registerBuiltinPreTermElabAttr___closed__5();
lean_mark_persistent(l_Lean_registerBuiltinPreTermElabAttr___closed__5);
l_Lean_registerBuiltinPreTermElabAttr___closed__6 = _init_l_Lean_registerBuiltinPreTermElabAttr___closed__6();
lean_mark_persistent(l_Lean_registerBuiltinPreTermElabAttr___closed__6);
l_Lean_registerBuiltinPreTermElabAttr___closed__7 = _init_l_Lean_registerBuiltinPreTermElabAttr___closed__7();
lean_mark_persistent(l_Lean_registerBuiltinPreTermElabAttr___closed__7);
res = l_Lean_registerBuiltinPreTermElabAttr(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Expr_mkAnnotation___closed__1 = _init_l_Lean_Expr_mkAnnotation___closed__1();
lean_mark_persistent(l_Lean_Expr_mkAnnotation___closed__1);
l_Lean_Expr_mkAnnotation___closed__2 = _init_l_Lean_Expr_mkAnnotation___closed__2();
lean_mark_persistent(l_Lean_Expr_mkAnnotation___closed__2);
l_Lean_mkAsIs___closed__1 = _init_l_Lean_mkAsIs___closed__1();
lean_mark_persistent(l_Lean_mkAsIs___closed__1);
l_Lean_mkAsIs___closed__2 = _init_l_Lean_mkAsIs___closed__2();
lean_mark_persistent(l_Lean_mkAsIs___closed__2);
l_Lean_mkAsPattern___closed__1 = _init_l_Lean_mkAsPattern___closed__1();
lean_mark_persistent(l_Lean_mkAsPattern___closed__1);
l_Lean_mkAsPattern___closed__2 = _init_l_Lean_mkAsPattern___closed__2();
lean_mark_persistent(l_Lean_mkAsPattern___closed__2);
l_Lean_mkPreTypeAscription___closed__1 = _init_l_Lean_mkPreTypeAscription___closed__1();
lean_mark_persistent(l_Lean_mkPreTypeAscription___closed__1);
l_Lean_mkPreTypeAscription___closed__2 = _init_l_Lean_mkPreTypeAscription___closed__2();
lean_mark_persistent(l_Lean_mkPreTypeAscription___closed__2);
l_Lean_mkPreTypeAscription___closed__3 = _init_l_Lean_mkPreTypeAscription___closed__3();
lean_mark_persistent(l_Lean_mkPreTypeAscription___closed__3);
l_Lean_Elab_toLevel___main___closed__1 = _init_l_Lean_Elab_toLevel___main___closed__1();
lean_mark_persistent(l_Lean_Elab_toLevel___main___closed__1);
l_Lean_Elab_toLevel___main___closed__2 = _init_l_Lean_Elab_toLevel___main___closed__2();
lean_mark_persistent(l_Lean_Elab_toLevel___main___closed__2);
l_Lean_Elab_toLevel___main___closed__3 = _init_l_Lean_Elab_toLevel___main___closed__3();
lean_mark_persistent(l_Lean_Elab_toLevel___main___closed__3);
l___private_Init_Lean_Elaborator_PreTerm_1__setPos___closed__1 = _init_l___private_Init_Lean_Elaborator_PreTerm_1__setPos___closed__1();
lean_mark_persistent(l___private_Init_Lean_Elaborator_PreTerm_1__setPos___closed__1);
l___private_Init_Lean_Elaborator_PreTerm_1__setPos___closed__2 = _init_l___private_Init_Lean_Elaborator_PreTerm_1__setPos___closed__2();
lean_mark_persistent(l___private_Init_Lean_Elaborator_PreTerm_1__setPos___closed__2);
l___private_Init_Lean_Elaborator_PreTerm_1__setPos___closed__3 = _init_l___private_Init_Lean_Elaborator_PreTerm_1__setPos___closed__3();
lean_mark_persistent(l___private_Init_Lean_Elaborator_PreTerm_1__setPos___closed__3);
l___private_Init_Lean_Elaborator_PreTerm_1__setPos___closed__4 = _init_l___private_Init_Lean_Elaborator_PreTerm_1__setPos___closed__4();
lean_mark_persistent(l___private_Init_Lean_Elaborator_PreTerm_1__setPos___closed__4);
l_Lean_Elab_toPreTerm___closed__1 = _init_l_Lean_Elab_toPreTerm___closed__1();
lean_mark_persistent(l_Lean_Elab_toPreTerm___closed__1);
l_Lean_Elab_toPreTerm___closed__2 = _init_l_Lean_Elab_toPreTerm___closed__2();
lean_mark_persistent(l_Lean_Elab_toPreTerm___closed__2);
l_Lean_Elab_toPreTerm___closed__3 = _init_l_Lean_Elab_toPreTerm___closed__3();
lean_mark_persistent(l_Lean_Elab_toPreTerm___closed__3);
l_Lean_Elab_toPreTerm___closed__4 = _init_l_Lean_Elab_toPreTerm___closed__4();
lean_mark_persistent(l_Lean_Elab_toPreTerm___closed__4);
l___private_Init_Lean_Elaborator_PreTerm_2__mkHoleFor___closed__1 = _init_l___private_Init_Lean_Elaborator_PreTerm_2__mkHoleFor___closed__1();
lean_mark_persistent(l___private_Init_Lean_Elaborator_PreTerm_2__mkHoleFor___closed__1);
l_Lean_Elab_convertType___rarg___closed__1 = _init_l_Lean_Elab_convertType___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_convertType___rarg___closed__1);
l___regBuiltinTermElab_Lean_Elab_convertType___closed__1 = _init_l___regBuiltinTermElab_Lean_Elab_convertType___closed__1();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_convertType___closed__1);
l___regBuiltinTermElab_Lean_Elab_convertType___closed__2 = _init_l___regBuiltinTermElab_Lean_Elab_convertType___closed__2();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_convertType___closed__2);
l___regBuiltinTermElab_Lean_Elab_convertType___closed__3 = _init_l___regBuiltinTermElab_Lean_Elab_convertType___closed__3();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_convertType___closed__3);
l___regBuiltinTermElab_Lean_Elab_convertType___closed__4 = _init_l___regBuiltinTermElab_Lean_Elab_convertType___closed__4();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_convertType___closed__4);
l___regBuiltinTermElab_Lean_Elab_convertType___closed__5 = _init_l___regBuiltinTermElab_Lean_Elab_convertType___closed__5();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_convertType___closed__5);
res = l___regBuiltinTermElab_Lean_Elab_convertType(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltinTermElab_Lean_Elab_convertSort___closed__1 = _init_l___regBuiltinTermElab_Lean_Elab_convertSort___closed__1();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_convertSort___closed__1);
l___regBuiltinTermElab_Lean_Elab_convertSort___closed__2 = _init_l___regBuiltinTermElab_Lean_Elab_convertSort___closed__2();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_convertSort___closed__2);
l___regBuiltinTermElab_Lean_Elab_convertSort___closed__3 = _init_l___regBuiltinTermElab_Lean_Elab_convertSort___closed__3();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_convertSort___closed__3);
res = l___regBuiltinTermElab_Lean_Elab_convertSort(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltinTermElab_Lean_Elab_convertProp___closed__1 = _init_l___regBuiltinTermElab_Lean_Elab_convertProp___closed__1();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_convertProp___closed__1);
l___regBuiltinTermElab_Lean_Elab_convertProp___closed__2 = _init_l___regBuiltinTermElab_Lean_Elab_convertProp___closed__2();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_convertProp___closed__2);
l___regBuiltinTermElab_Lean_Elab_convertProp___closed__3 = _init_l___regBuiltinTermElab_Lean_Elab_convertProp___closed__3();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_convertProp___closed__3);
res = l___regBuiltinTermElab_Lean_Elab_convertProp(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltinTermElab_Lean_Elab_convertSortApp___closed__1 = _init_l___regBuiltinTermElab_Lean_Elab_convertSortApp___closed__1();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_convertSortApp___closed__1);
l___regBuiltinTermElab_Lean_Elab_convertSortApp___closed__2 = _init_l___regBuiltinTermElab_Lean_Elab_convertSortApp___closed__2();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_convertSortApp___closed__2);
l___regBuiltinTermElab_Lean_Elab_convertSortApp___closed__3 = _init_l___regBuiltinTermElab_Lean_Elab_convertSortApp___closed__3();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_convertSortApp___closed__3);
res = l___regBuiltinTermElab_Lean_Elab_convertSortApp(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Init_Lean_Elaborator_PreTerm_3__mkLocalAux___closed__1 = _init_l___private_Init_Lean_Elaborator_PreTerm_3__mkLocalAux___closed__1();
lean_mark_persistent(l___private_Init_Lean_Elaborator_PreTerm_3__mkLocalAux___closed__1);
l___private_Init_Lean_Elaborator_PreTerm_3__mkLocalAux___closed__2 = _init_l___private_Init_Lean_Elaborator_PreTerm_3__mkLocalAux___closed__2();
lean_mark_persistent(l___private_Init_Lean_Elaborator_PreTerm_3__mkLocalAux___closed__2);
l___private_Init_Lean_Elaborator_PreTerm_3__mkLocalAux___closed__3 = _init_l___private_Init_Lean_Elaborator_PreTerm_3__mkLocalAux___closed__3();
lean_mark_persistent(l___private_Init_Lean_Elaborator_PreTerm_3__mkLocalAux___closed__3);
l_Array_umapMAux___main___at___private_Init_Lean_Elaborator_PreTerm_4__processBinder___spec__1___closed__1 = _init_l_Array_umapMAux___main___at___private_Init_Lean_Elaborator_PreTerm_4__processBinder___spec__1___closed__1();
lean_mark_persistent(l_Array_umapMAux___main___at___private_Init_Lean_Elaborator_PreTerm_4__processBinder___spec__1___closed__1);
l_Array_umapMAux___main___at___private_Init_Lean_Elaborator_PreTerm_4__processBinder___spec__1___closed__2 = _init_l_Array_umapMAux___main___at___private_Init_Lean_Elaborator_PreTerm_4__processBinder___spec__1___closed__2();
lean_mark_persistent(l_Array_umapMAux___main___at___private_Init_Lean_Elaborator_PreTerm_4__processBinder___spec__1___closed__2);
l_Array_umapMAux___main___at___private_Init_Lean_Elaborator_PreTerm_4__processBinder___spec__1___closed__3 = _init_l_Array_umapMAux___main___at___private_Init_Lean_Elaborator_PreTerm_4__processBinder___spec__1___closed__3();
lean_mark_persistent(l_Array_umapMAux___main___at___private_Init_Lean_Elaborator_PreTerm_4__processBinder___spec__1___closed__3);
l_Array_umapMAux___main___at___private_Init_Lean_Elaborator_PreTerm_4__processBinder___spec__1___closed__4 = _init_l_Array_umapMAux___main___at___private_Init_Lean_Elaborator_PreTerm_4__processBinder___spec__1___closed__4();
lean_mark_persistent(l_Array_umapMAux___main___at___private_Init_Lean_Elaborator_PreTerm_4__processBinder___spec__1___closed__4);
l___private_Init_Lean_Elaborator_PreTerm_4__processBinder___closed__1 = _init_l___private_Init_Lean_Elaborator_PreTerm_4__processBinder___closed__1();
lean_mark_persistent(l___private_Init_Lean_Elaborator_PreTerm_4__processBinder___closed__1);
l___private_Init_Lean_Elaborator_PreTerm_4__processBinder___closed__2 = _init_l___private_Init_Lean_Elaborator_PreTerm_4__processBinder___closed__2();
lean_mark_persistent(l___private_Init_Lean_Elaborator_PreTerm_4__processBinder___closed__2);
l___private_Init_Lean_Elaborator_PreTerm_4__processBinder___closed__3 = _init_l___private_Init_Lean_Elaborator_PreTerm_4__processBinder___closed__3();
lean_mark_persistent(l___private_Init_Lean_Elaborator_PreTerm_4__processBinder___closed__3);
l___private_Init_Lean_Elaborator_PreTerm_4__processBinder___closed__4 = _init_l___private_Init_Lean_Elaborator_PreTerm_4__processBinder___closed__4();
lean_mark_persistent(l___private_Init_Lean_Elaborator_PreTerm_4__processBinder___closed__4);
l___regBuiltinTermElab_Lean_Elab_convertForall___closed__1 = _init_l___regBuiltinTermElab_Lean_Elab_convertForall___closed__1();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_convertForall___closed__1);
l___regBuiltinTermElab_Lean_Elab_convertForall___closed__2 = _init_l___regBuiltinTermElab_Lean_Elab_convertForall___closed__2();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_convertForall___closed__2);
l___regBuiltinTermElab_Lean_Elab_convertForall___closed__3 = _init_l___regBuiltinTermElab_Lean_Elab_convertForall___closed__3();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_convertForall___closed__3);
res = l___regBuiltinTermElab_Lean_Elab_convertForall(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltinTermElab_Lean_Elab_convertHole___closed__1 = _init_l___regBuiltinTermElab_Lean_Elab_convertHole___closed__1();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_convertHole___closed__1);
l___regBuiltinTermElab_Lean_Elab_convertHole___closed__2 = _init_l___regBuiltinTermElab_Lean_Elab_convertHole___closed__2();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_convertHole___closed__2);
l___regBuiltinTermElab_Lean_Elab_convertHole___closed__3 = _init_l___regBuiltinTermElab_Lean_Elab_convertHole___closed__3();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_convertHole___closed__3);
res = l___regBuiltinTermElab_Lean_Elab_convertHole(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_convertSorry___rarg___closed__1 = _init_l_Lean_Elab_convertSorry___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_convertSorry___rarg___closed__1);
l_Lean_Elab_convertSorry___rarg___closed__2 = _init_l_Lean_Elab_convertSorry___rarg___closed__2();
lean_mark_persistent(l_Lean_Elab_convertSorry___rarg___closed__2);
l_Lean_Elab_convertSorry___rarg___closed__3 = _init_l_Lean_Elab_convertSorry___rarg___closed__3();
lean_mark_persistent(l_Lean_Elab_convertSorry___rarg___closed__3);
l_Lean_Elab_convertSorry___rarg___closed__4 = _init_l_Lean_Elab_convertSorry___rarg___closed__4();
lean_mark_persistent(l_Lean_Elab_convertSorry___rarg___closed__4);
l___regBuiltinTermElab_Lean_Elab_convertSorry___closed__1 = _init_l___regBuiltinTermElab_Lean_Elab_convertSorry___closed__1();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_convertSorry___closed__1);
l___regBuiltinTermElab_Lean_Elab_convertSorry___closed__2 = _init_l___regBuiltinTermElab_Lean_Elab_convertSorry___closed__2();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_convertSorry___closed__2);
l___regBuiltinTermElab_Lean_Elab_convertSorry___closed__3 = _init_l___regBuiltinTermElab_Lean_Elab_convertSorry___closed__3();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_convertSorry___closed__3);
res = l___regBuiltinTermElab_Lean_Elab_convertSorry(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_convertId___closed__1 = _init_l_Lean_Elab_convertId___closed__1();
lean_mark_persistent(l_Lean_Elab_convertId___closed__1);
l___regBuiltinTermElab_Lean_Elab_convertId___closed__1 = _init_l___regBuiltinTermElab_Lean_Elab_convertId___closed__1();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_convertId___closed__1);
l___regBuiltinTermElab_Lean_Elab_convertId___closed__2 = _init_l___regBuiltinTermElab_Lean_Elab_convertId___closed__2();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_convertId___closed__2);
l___regBuiltinTermElab_Lean_Elab_convertId___closed__3 = _init_l___regBuiltinTermElab_Lean_Elab_convertId___closed__3();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_convertId___closed__3);
res = l___regBuiltinTermElab_Lean_Elab_convertId(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
