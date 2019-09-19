// Lean compiler output
// Module: init.lean.elaborator.preterm
// Imports: init.lean.elaborator.basic
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
extern lean_object* l_Lean_Parser_Level_num___elambda__1___rarg___closed__2;
lean_object* l_Lean_mkPreTypeAscription___closed__3;
lean_object* lean_expr_mk_mdata(lean_object*, lean_object*);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinPreTermElab(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_convertSorry___closed__1;
lean_object* l_Lean_registerBuiltinPreTermElabAttr___closed__2;
lean_object* l___regBuiltinTermElab_Lean_Elab_convertSorry(lean_object*);
lean_object* l_Lean_registerBuiltinPreTermElabAttr___closed__3;
lean_object* l_Lean_registerBuiltinPreTermElabAttr___closed__5;
uint8_t lean_name_dec_eq(lean_object*, lean_object*);
lean_object* l_Array_miterateAux___main___at___private_init_lean_elaborator_preterm_6__processBinders___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_local_ctx_find_from_user_name(lean_object*, lean_object*);
lean_object* lean_expr_mk_sort(lean_object*);
lean_object* l_Array_ummapAux___main___at___private_init_lean_elaborator_preterm_5__processBinder___spec__1___closed__5;
lean_object* l_Lean_Syntax_getKind___rarg(lean_object*);
lean_object* l_HashMapImp_find___at_Lean_Elab_toPreTerm___spec__1(lean_object*, lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* l_Lean_mkAsPattern___closed__1;
lean_object* l_Lean_Format_pretty(lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_convertHole(lean_object*);
lean_object* l_Array_ummapAux___main___at___private_init_lean_elaborator_preterm_5__processBinder___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_runIOUnsafe___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_tail___rarg(lean_object*);
lean_object* l_Array_mkArray(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_println___at_HasRepr_HasEval___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_builtinPreTermElabTable;
lean_object* l_Lean_Elab_convertType___rarg(lean_object*);
lean_object* l_Lean_Elab_toLevel___main___closed__4;
lean_object* l_Lean_Elab_mkForall(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_convertId___closed__1;
lean_object* l___private_init_lean_elaborator_preterm_2__setPos___closed__4;
lean_object* l_Lean_Elab_convertSorry___rarg___closed__3;
lean_object* l_Lean_registerBuiltinPreTermElabAttr___lambda__1___closed__4;
lean_object* l_Lean_Elab_convertHole___rarg(lean_object*);
extern lean_object* l_Lean_AttributeImpl_inhabited___closed__5;
lean_object* l___regBuiltinTermElab_Lean_Elab_convertHole___closed__3;
extern lean_object* l_Lean_Parser_Level_max___elambda__1___closed__1;
lean_object* l___private_init_lean_elaborator_preterm_2__setPos___closed__2;
lean_object* l_HashMapImp_insert___at_Lean_addBuiltinPreTermElab___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_miterateAux___main___at___private_init_lean_elaborator_preterm_6__processBinders___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_addBuiltinTermElab___closed__2;
extern lean_object* l_Lean_Parser_Term_binderDefault___elambda__1___rarg___closed__1;
lean_object* l_Lean_mkBuiltinPreTermElabTable___closed__1;
lean_object* l_Lean_Elab_mkLocalDecl(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Elab_convertProp___rarg(lean_object*);
lean_object* l_Lean_Syntax_formatStx___main___rarg(lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_convertSort___closed__3;
lean_object* l_Lean_registerAttribute(lean_object*, lean_object*);
lean_object* l___private_init_lean_elaborator_preterm_2__setPos___closed__1;
lean_object* l___private_init_lean_elaborator_preterm_5__processBinder___closed__2;
lean_object* l_Lean_Elab_logError___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_convertSortApp___closed__2;
lean_object* level_mk_mvar(lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_convertSortApp___closed__1;
lean_object* l_Lean_registerBuiltinPreTermElabAttr___closed__7;
lean_object* lean_expr_local(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l___regBuiltinTermElab_Lean_Elab_convertId___closed__3;
lean_object* lean_expr_mk_app(lean_object*, lean_object*);
lean_object* l_Lean_Elab_convertSort___boxed(lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_convertType___closed__5;
lean_object* l_Lean_mkPreTypeAscriptionIfSome(lean_object*, lean_object*);
lean_object* l_Lean_Elab_convertId(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KVMap_setNat(lean_object*, lean_object*, lean_object*);
lean_object* l_List_head___at_Lean_Elab_getScope___spec__1(lean_object*);
lean_object* l_Lean_Elab_convertType(lean_object*, lean_object*);
lean_object* l_Array_ummapAux___main___at___private_init_lean_elaborator_preterm_5__processBinder___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_convertForall(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_uget(lean_object*, lean_object*, size_t, lean_object*);
lean_object* l_Lean_Name_toStringWithSep___main(lean_object*, lean_object*);
lean_object* l_Lean_mkPreTypeAscription___closed__1;
extern lean_object* l_Lean_mkInitAttr___lambda__1___closed__1;
extern lean_object* l_Lean_Parser_Level_hole___elambda__1___rarg___closed__2;
lean_object* l_Array_uset(lean_object*, lean_object*, size_t, lean_object*, lean_object*);
uint8_t l_AssocList_contains___main___at_Lean_addBuiltinPreTermElab___spec__2(lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_convertProp___closed__1;
lean_object* l___regBuiltinTermElab_Lean_Elab_convertForall___closed__1;
extern lean_object* l_Lean_Parser_Term_sorry___elambda__1___rarg___closed__2;
lean_object* l_IO_Prim_Ref_set(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerBuiltinPreTermElabAttr___closed__4;
lean_object* l___regBuiltinTermElab_Lean_Elab_convertSortApp___closed__3;
lean_object* l___private_init_lean_elaborator_preterm_3__mkHoleFor(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_miterateAux___main___at_Lean_Elab_toLevel___main___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_mkPreTypeAscription___closed__2;
extern lean_object* l_Lean_Parser_Term_explicitBinder___elambda__1___closed__2;
lean_object* l_Lean_Elab_toLevel___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_toPreTerm___closed__2;
lean_object* l_Lean_Elab_toLevel___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_declareBuiltinPreTermElab___closed__2;
lean_object* l_Array_ummapAux___main___at___private_init_lean_elaborator_preterm_5__processBinder___spec__1___closed__6;
lean_object* l___regBuiltinTermElab_Lean_Elab_convertType___closed__1;
lean_object* l_Lean_Level_ofNat___main(lean_object*);
lean_object* l_AssocList_find___main___at_Lean_Elab_toPreTerm___spec__2(lean_object*, lean_object*);
lean_object* lean_expr_mk_fvar(lean_object*);
lean_object* l___private_init_lean_elaborator_preterm_1__dummy___closed__1;
lean_object* l_IO_Prim_Ref_get___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_convertType___closed__3;
lean_object* l___regBuiltinTermElab_Lean_Elab_convertSort___closed__2;
lean_object* l_Lean_registerBuiltinPreTermElabAttr___lambda__1___closed__3;
lean_object* l_Lean_declareBuiltinPreTermElab___closed__1;
lean_object* l_mkHashMap___at_Lean_mkBuiltinPreTermElabTable___spec__1(lean_object*);
lean_object* l_Lean_mkAsPattern___closed__2;
lean_object* l_Lean_Elab_convertHole(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_implicitBinder___elambda__1___closed__2;
extern lean_object* l_Lean_AttributeImpl_inhabited___closed__4;
lean_object* l_Lean_oldElaborateAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTagAttribute___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_convertId___closed__2;
lean_object* l___private_init_lean_elaborator_preterm_1__dummy;
lean_object* l_Lean_registerBuiltinPreTermElabAttr___closed__1;
lean_object* l___private_init_lean_elaborator_preterm_3__mkHoleFor___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_HashMapImp_find___at_Lean_Elab_toPreTerm___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_registerBuiltinPreTermElabAttr(lean_object*);
lean_object* lean_expr_mk_const(lean_object*, lean_object*);
lean_object* l_Lean_Elab_convertSort(lean_object*, lean_object*);
lean_object* l_Lean_mkAsPattern(lean_object*, lean_object*);
size_t lean_name_hash_usize(lean_object*);
lean_object* l_Lean_Elab_toPreTerm___closed__1;
lean_object* l_Lean_Elab_localContext___rarg(lean_object*);
lean_object* l___private_init_lean_elaborator_preterm_5__processBinder___closed__1;
lean_object* lean_old_elaborate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_userName(lean_object*);
lean_object* l_Array_ummapAux___main___at___private_init_lean_elaborator_preterm_5__processBinder___spec__1___closed__4;
lean_object* l_Lean_Syntax_getArg___rarg(lean_object*, lean_object*);
lean_object* l_Array_miterateAux___main___at_Lean_Elab_toLevel___main___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_toLevel___main___closed__2;
extern lean_object* l_Lean_Parser_Term_prop___elambda__1___rarg___closed__2;
extern lean_object* l_Lean_Parser_Term_prop___elambda__1___rarg___closed__3;
lean_object* l_Lean_Elab_convertSortApp(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_hole___elambda__1___rarg___closed__1;
lean_object* l_Lean_registerBuiltinPreTermElabAttr___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_init_lean_elaborator_preterm_5__processBinder(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KVMap_setName(lean_object*, lean_object*, lean_object*);
lean_object* l___private_init_lean_elaborator_preterm_6__processBinders(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_sort___elambda__1___rarg___closed__2;
uint8_t l_Lean_Syntax_isOfKind___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_convertHole___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Level_addLit___elambda__1___closed__2;
extern lean_object* l_Lean_Parser_Term_type___elambda__1___rarg___closed__2;
lean_object* l_Lean_registerBuiltinPreTermElabAttr___lambda__1___closed__1;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_HashMapImp_contains___at_Lean_addBuiltinPreTermElab___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs___rarg(lean_object*);
extern lean_object* l_Char_HasRepr___closed__1;
lean_object* l_Lean_mkPreTypeAscription(lean_object*, lean_object*);
extern lean_object* l_Lean_addBuiltinTermElab___closed__1;
lean_object* l___regBuiltinTermElab_Lean_Elab_convertType___closed__4;
lean_object* l_Lean_Syntax_getId___rarg(lean_object*);
lean_object* l___private_init_lean_elaborator_preterm_1__dummy___closed__2;
lean_object* l_Lean_Elab_getUniverses___rarg(lean_object*);
lean_object* l_Array_fget(lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_binderInfo(lean_object*);
lean_object* l_Lean_registerBuiltinPreTermElabAttr___lambda__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_convertProp(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_convertSorry___closed__2;
uint8_t l_HashMapImp_contains___at_Lean_addBuiltinPreTermElab___spec__1(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_sortApp___elambda__1___closed__2;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_explicitUniv___elambda__1___closed__2;
lean_object* l_Lean_Elab_convertSort___rarg(lean_object*);
extern lean_object* l_Lean_Parser_Term_instBinder___elambda__1___rarg___closed__2;
lean_object* l_Lean_addBuiltinPreTermElab___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_AssocList_find___main___at_Lean_Elab_toPreTerm___spec__2___boxed(lean_object*, lean_object*);
lean_object* level_mk_imax(lean_object*, lean_object*);
lean_object* l_Lean_syntaxNodeKindOfAttrParam(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_ummapAux___main___at___private_init_lean_elaborator_preterm_5__processBinder___spec__1___closed__2;
lean_object* l___regBuiltinTermElab_Lean_Elab_convertSorry___closed__3;
lean_object* l_Lean_registerBuiltinPreTermElabAttr___closed__6;
lean_object* l___regBuiltinTermElab_Lean_Elab_convertForall___closed__2;
lean_object* l_IO_Prim_mkRef(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_convertForall(lean_object*);
lean_object* l_Array_ummapAux___main___at___private_init_lean_elaborator_preterm_5__processBinder___spec__1___closed__3;
extern lean_object* l_Lean_Parser_Level_paren___elambda__1___rarg___closed__4;
lean_object* l_Lean_Elab_convertId___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_List_elem___main___at_Lean_Parser_addBuiltinLeadingParser___spec__4(lean_object*, lean_object*);
lean_object* l___private_init_lean_elaborator_preterm_2__setPos(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_HashMapImp_expand___at_Lean_addBuiltinPreTermElab___spec__4(lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_convertType(lean_object*);
extern lean_object* l_Lean_Level_one___closed__1;
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_mkAsIs___closed__2;
lean_object* l_HashMapImp_moveEntries___main___at_Lean_addBuiltinPreTermElab___spec__5(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_convertSorry___rarg___closed__2;
lean_object* lean_expr_mk_mvar(lean_object*);
lean_object* l_Lean_Elab_toPreTerm___closed__3;
lean_object* l___private_init_lean_elaborator_preterm_4__mkLocal___boxed(lean_object*);
lean_object* level_mk_param(lean_object*);
extern lean_object* l_Lean_Parser_Term_app___elambda__1___closed__2;
lean_object* l_Array_ummapAux___main___at___private_init_lean_elaborator_preterm_5__processBinder___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* level_mk_succ(lean_object*);
lean_object* l_Lean_mkAsIs___closed__1;
extern lean_object* l_System_FilePath_dirName___closed__1;
extern lean_object* l_Lean_Parser_Term_id___elambda__1___closed__2;
lean_object* l_Lean_Elab_toLevel___main___closed__1;
lean_object* l_IO_Prim_Ref_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mkAnnotation___closed__1;
size_t lean_usize_modn(size_t, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_convertId___closed__1;
lean_object* l_Lean_Syntax_getIdAt___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_convertSorry___boxed(lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* l_Array_ummapAux___main___at___private_init_lean_elaborator_preterm_5__processBinder___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mkAnnotation(lean_object*, lean_object*);
lean_object* l_Lean_mkBuiltinPreTermElabTable(lean_object*);
lean_object* lean_environment_find(lean_object*, lean_object*);
lean_object* l_Lean_Elab_convertSorry___rarg___closed__4;
lean_object* l___regBuiltinTermElab_Lean_Elab_convertSort___closed__1;
lean_object* l_Lean_Elab_toPreTerm(lean_object*, lean_object*, lean_object*);
lean_object* l_AssocList_mfoldl___main___at_Lean_addBuiltinPreTermElab___spec__6(lean_object*, lean_object*);
lean_object* l_Lean_Level_addOffsetAux___main(lean_object*, lean_object*);
lean_object* l_Array_size(lean_object*, lean_object*);
lean_object* l_Lean_Elab_convertSorry___rarg(lean_object*);
lean_object* l_Lean_Elab_toLevel(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_fset(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_convertHole___closed__1;
lean_object* l_Array_get(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_convertType___boxed(lean_object*, lean_object*);
lean_object* l_mkHashMapImp___rarg(lean_object*);
lean_object* l_Array_miterateAux___main___at_Lean_Elab_toLevel___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_binderTactic___elambda__1___rarg___closed__1;
lean_object* l___regBuiltinTermElab_Lean_Elab_convertSortApp(lean_object*);
extern lean_object* l_Lean_Parser_Level_ident___elambda__1___rarg___closed__1;
lean_object* l_Lean_registerBuiltinPreTermElabAttr___lambda__1___closed__2;
lean_object* l_Array_miterateAux___main___at_Lean_Elab_toLevel___main___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_nameToExprAux___main___closed__4;
extern lean_object* l_Lean_Parser_Term_forall___elambda__1___closed__2;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_convertSort(lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_convertForall___closed__3;
lean_object* l_Lean_Syntax_toNat___rarg(lean_object*);
lean_object* l_Array_ummapAux___main___at___private_init_lean_elaborator_preterm_5__processBinder___spec__1___closed__1;
lean_object* l_Lean_Syntax_getPos___rarg(lean_object*);
extern lean_object* l_Lean_Parser_Level_imax___elambda__1___closed__1;
lean_object* l___regBuiltinTermElab_Lean_Elab_convertHole___closed__2;
lean_object* l_Lean_Elab_convertProp(lean_object*, lean_object*);
lean_object* l_Lean_Elab_getScope___rarg(lean_object*);
lean_object* l___private_init_lean_elaborator_preterm_4__mkLocal(lean_object*);
lean_object* l_AssocList_replace___main___at_Lean_addBuiltinPreTermElab___spec__7(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_convertProp___boxed(lean_object*, lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
lean_object* l_Lean_declareBuiltinElab(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_logErrorAndThrow___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getNumArgs___rarg(lean_object*);
lean_object* l_Lean_Elab_convertSorry(lean_object*, lean_object*);
lean_object* l_Lean_Elab_convertSortApp___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_convertProp___closed__2;
lean_object* l_Lean_Elab_logMessage(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_toLevel___main___closed__3;
lean_object* l_Lean_Elab_toLevel___main___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_miterateAux___main___at_Array_append___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_oldElaborate(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_init_lean_elaborator_preterm_2__setPos___closed__3;
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_AssocList_contains___main___at_Lean_addBuiltinPreTermElab___spec__2___boxed(lean_object*, lean_object*);
lean_object* l___private_init_lean_elaborator_preterm_6__processBinders___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_init_lean_elaborator_preterm_3__mkHoleFor___closed__1;
lean_object* l_Lean_Expr_mkAnnotation___closed__2;
lean_object* l_Lean_Elab_convertSorry___rarg___closed__1;
extern lean_object* l_Lean_Parser_Term_simpleBinder___elambda__1___closed__2;
lean_object* l___regBuiltinTermElab_Lean_Elab_convertType___closed__2;
lean_object* l___private_init_lean_elaborator_preterm_5__processBinder___closed__4;
lean_object* l_IO_Prim_Ref_reset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAsIs(lean_object*);
lean_object* l_Lean_Elab_convertType___rarg___closed__1;
extern lean_object* l_Lean_exprIsInhabited___closed__1;
lean_object* l_Lean_Elab_convertForall___boxed(lean_object*, lean_object*, lean_object*);
lean_object* level_mk_max(lean_object*, lean_object*);
lean_object* l___private_init_lean_elaborator_preterm_5__processBinder___closed__3;
lean_object* l_Lean_registerBuiltinPreTermElabAttr___lambda__1___closed__5;
lean_object* l___private_init_lean_elaborator_preterm_2__setPos___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_convertProp___closed__3;
lean_object* l_Lean_declareBuiltinPreTermElab(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTagAttribute___lambda__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_String_splitAux___main___closed__1;
lean_object* l_Lean_LocalDecl_name(lean_object*);
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
x_6 = lean_name_dec_eq(x_4, x_1);
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
lean_object* l_AssocList_mfoldl___main___at_Lean_addBuiltinPreTermElab___spec__6(lean_object* x_1, lean_object* x_2) {
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
x_9 = l_AssocList_mfoldl___main___at_Lean_addBuiltinPreTermElab___spec__6(x_3, x_6);
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
x_8 = lean_name_dec_eq(x_5, x_1);
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
x_13 = lean_name_dec_eq(x_10, x_1);
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
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = l_HashMapImp_contains___at_Lean_addBuiltinPreTermElab___spec__1(x_8, x_1);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_box(0);
lean_ctor_set(x_6, 0, x_10);
x_11 = lean_io_ref_get(x_5, x_6);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
lean_ctor_set(x_11, 0, x_10);
x_14 = lean_io_ref_reset(x_5, x_11);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 0);
lean_dec(x_16);
lean_ctor_set(x_14, 0, x_10);
x_17 = l_HashMapImp_insert___at_Lean_addBuiltinPreTermElab___spec__3(x_13, x_1, x_3);
x_18 = lean_io_ref_set(x_5, x_17, x_14);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
lean_dec(x_14);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_10);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_HashMapImp_insert___at_Lean_addBuiltinPreTermElab___spec__3(x_13, x_1, x_3);
x_22 = lean_io_ref_set(x_5, x_21, x_20);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_dec(x_13);
lean_dec(x_3);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_14);
if (x_23 == 0)
{
return x_14;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_14, 0);
x_25 = lean_ctor_get(x_14, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_14);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_11, 0);
x_28 = lean_ctor_get(x_11, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_11);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_10);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_io_ref_reset(x_5, x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_32 = x_30;
} else {
 lean_dec_ref(x_30);
 x_32 = lean_box(0);
}
if (lean_is_scalar(x_32)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_32;
}
lean_ctor_set(x_33, 0, x_10);
lean_ctor_set(x_33, 1, x_31);
x_34 = l_HashMapImp_insert___at_Lean_addBuiltinPreTermElab___spec__3(x_27, x_1, x_3);
x_35 = lean_io_ref_set(x_5, x_34, x_33);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_27);
lean_dec(x_3);
lean_dec(x_1);
x_36 = lean_ctor_get(x_30, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_30, 1);
lean_inc(x_37);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_38 = x_30;
} else {
 lean_dec_ref(x_30);
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
}
else
{
uint8_t x_40; 
lean_dec(x_3);
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_11);
if (x_40 == 0)
{
return x_11;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_11, 0);
x_42 = lean_ctor_get(x_11, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_11);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_3);
x_44 = l_System_FilePath_dirName___closed__1;
x_45 = l_Lean_Name_toStringWithSep___main(x_44, x_1);
x_46 = l_Lean_addBuiltinTermElab___closed__1;
x_47 = lean_string_append(x_46, x_45);
lean_dec(x_45);
x_48 = l_Lean_addBuiltinTermElab___closed__2;
x_49 = lean_string_append(x_47, x_48);
lean_ctor_set_tag(x_6, 1);
lean_ctor_set(x_6, 0, x_49);
return x_6;
}
}
else
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_50 = lean_ctor_get(x_6, 0);
x_51 = lean_ctor_get(x_6, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_6);
x_52 = l_HashMapImp_contains___at_Lean_addBuiltinPreTermElab___spec__1(x_50, x_1);
lean_dec(x_50);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_box(0);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_51);
x_55 = lean_io_ref_get(x_5, x_54);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_58 = x_55;
} else {
 lean_dec_ref(x_55);
 x_58 = lean_box(0);
}
if (lean_is_scalar(x_58)) {
 x_59 = lean_alloc_ctor(0, 2, 0);
} else {
 x_59 = x_58;
}
lean_ctor_set(x_59, 0, x_53);
lean_ctor_set(x_59, 1, x_57);
x_60 = lean_io_ref_reset(x_5, x_59);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
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
if (lean_is_scalar(x_62)) {
 x_63 = lean_alloc_ctor(0, 2, 0);
} else {
 x_63 = x_62;
}
lean_ctor_set(x_63, 0, x_53);
lean_ctor_set(x_63, 1, x_61);
x_64 = l_HashMapImp_insert___at_Lean_addBuiltinPreTermElab___spec__3(x_56, x_1, x_3);
x_65 = lean_io_ref_set(x_5, x_64, x_63);
return x_65;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_56);
lean_dec(x_3);
lean_dec(x_1);
x_66 = lean_ctor_get(x_60, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_60, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_68 = x_60;
} else {
 lean_dec_ref(x_60);
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
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_3);
lean_dec(x_1);
x_70 = lean_ctor_get(x_55, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_55, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_72 = x_55;
} else {
 lean_dec_ref(x_55);
 x_72 = lean_box(0);
}
if (lean_is_scalar(x_72)) {
 x_73 = lean_alloc_ctor(1, 2, 0);
} else {
 x_73 = x_72;
}
lean_ctor_set(x_73, 0, x_70);
lean_ctor_set(x_73, 1, x_71);
return x_73;
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_3);
x_74 = l_System_FilePath_dirName___closed__1;
x_75 = l_Lean_Name_toStringWithSep___main(x_74, x_1);
x_76 = l_Lean_addBuiltinTermElab___closed__1;
x_77 = lean_string_append(x_76, x_75);
lean_dec(x_75);
x_78 = l_Lean_addBuiltinTermElab___closed__2;
x_79 = lean_string_append(x_77, x_78);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_51);
return x_80;
}
}
}
else
{
uint8_t x_81; 
lean_dec(x_3);
lean_dec(x_1);
x_81 = !lean_is_exclusive(x_6);
if (x_81 == 0)
{
return x_6;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_6, 0);
x_83 = lean_ctor_get(x_6, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_6);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
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
lean_object* _init_l_Lean_registerBuiltinPreTermElabAttr___lambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_nameToExprAux___main___closed__4;
x_2 = l_Lean_registerBuiltinPreTermElabAttr___lambda__1___closed__4;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_registerBuiltinPreTermElabAttr___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5) {
_start:
{
if (x_4 == 0)
{
uint8_t x_6; 
lean_dec(x_2);
lean_dec(x_1);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_5, 0);
lean_dec(x_7);
x_8 = l_Lean_registerBuiltinPreTermElabAttr___lambda__1___closed__1;
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 0, x_8);
return x_5;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_5, 1);
lean_inc(x_9);
lean_dec(x_5);
x_10 = l_Lean_registerBuiltinPreTermElabAttr___lambda__1___closed__1;
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_5);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_5, 0);
lean_dec(x_13);
x_14 = lean_box(0);
lean_ctor_set(x_5, 0, x_14);
x_15 = l_Lean_Parser_Term_explicitUniv___elambda__1___closed__2;
lean_inc(x_1);
x_16 = l_Lean_syntaxNodeKindOfAttrParam(x_1, x_15, x_3, x_5);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_29; lean_object* x_30; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_19 = x_16;
} else {
 lean_dec_ref(x_16);
 x_19 = lean_box(0);
}
lean_inc(x_18);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_14);
lean_ctor_set(x_29, 1, x_18);
lean_inc(x_2);
lean_inc(x_1);
x_30 = lean_environment_find(x_1, x_2);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_29);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_2);
lean_dec(x_1);
x_31 = l_Lean_mkInitAttr___lambda__1___closed__1;
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_18);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_30, 0);
lean_inc(x_33);
lean_dec(x_30);
x_34 = l_Lean_ConstantInfo_type(x_33);
lean_dec(x_33);
if (lean_obj_tag(x_34) == 4)
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
lean_dec(x_34);
x_36 = l_Lean_registerBuiltinPreTermElabAttr___lambda__1___closed__5;
x_37 = lean_name_dec_eq(x_35, x_36);
lean_dec(x_35);
if (x_37 == 0)
{
lean_dec(x_29);
lean_dec(x_17);
lean_dec(x_1);
x_20 = x_14;
goto block_28;
}
else
{
lean_object* x_38; 
lean_dec(x_19);
lean_dec(x_18);
x_38 = l_Lean_declareBuiltinPreTermElab(x_1, x_17, x_2, x_29);
return x_38;
}
}
else
{
lean_dec(x_34);
lean_dec(x_29);
lean_dec(x_17);
lean_dec(x_1);
x_20 = x_14;
goto block_28;
}
}
block_28:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_20);
x_21 = l_System_FilePath_dirName___closed__1;
x_22 = l_Lean_Name_toStringWithSep___main(x_21, x_2);
x_23 = l_Lean_registerBuiltinPreTermElabAttr___lambda__1___closed__2;
x_24 = lean_string_append(x_23, x_22);
lean_dec(x_22);
x_25 = l_Lean_registerBuiltinPreTermElabAttr___lambda__1___closed__3;
x_26 = lean_string_append(x_24, x_25);
if (lean_is_scalar(x_19)) {
 x_27 = lean_alloc_ctor(1, 2, 0);
} else {
 x_27 = x_19;
 lean_ctor_set_tag(x_27, 1);
}
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_18);
return x_27;
}
}
else
{
uint8_t x_39; 
lean_dec(x_2);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_16);
if (x_39 == 0)
{
return x_16;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_16, 0);
x_41 = lean_ctor_get(x_16, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_16);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_43 = lean_ctor_get(x_5, 1);
lean_inc(x_43);
lean_dec(x_5);
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
x_46 = l_Lean_Parser_Term_explicitUniv___elambda__1___closed__2;
lean_inc(x_1);
x_47 = l_Lean_syntaxNodeKindOfAttrParam(x_1, x_46, x_3, x_45);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_60; lean_object* x_61; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_50 = x_47;
} else {
 lean_dec_ref(x_47);
 x_50 = lean_box(0);
}
lean_inc(x_49);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_44);
lean_ctor_set(x_60, 1, x_49);
lean_inc(x_2);
lean_inc(x_1);
x_61 = lean_environment_find(x_1, x_2);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; 
lean_dec(x_60);
lean_dec(x_50);
lean_dec(x_48);
lean_dec(x_2);
lean_dec(x_1);
x_62 = l_Lean_mkInitAttr___lambda__1___closed__1;
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_49);
return x_63;
}
else
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_61, 0);
lean_inc(x_64);
lean_dec(x_61);
x_65 = l_Lean_ConstantInfo_type(x_64);
lean_dec(x_64);
if (lean_obj_tag(x_65) == 4)
{
lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
lean_dec(x_65);
x_67 = l_Lean_registerBuiltinPreTermElabAttr___lambda__1___closed__5;
x_68 = lean_name_dec_eq(x_66, x_67);
lean_dec(x_66);
if (x_68 == 0)
{
lean_dec(x_60);
lean_dec(x_48);
lean_dec(x_1);
x_51 = x_44;
goto block_59;
}
else
{
lean_object* x_69; 
lean_dec(x_50);
lean_dec(x_49);
x_69 = l_Lean_declareBuiltinPreTermElab(x_1, x_48, x_2, x_60);
return x_69;
}
}
else
{
lean_dec(x_65);
lean_dec(x_60);
lean_dec(x_48);
lean_dec(x_1);
x_51 = x_44;
goto block_59;
}
}
block_59:
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_51);
x_52 = l_System_FilePath_dirName___closed__1;
x_53 = l_Lean_Name_toStringWithSep___main(x_52, x_2);
x_54 = l_Lean_registerBuiltinPreTermElabAttr___lambda__1___closed__2;
x_55 = lean_string_append(x_54, x_53);
lean_dec(x_53);
x_56 = l_Lean_registerBuiltinPreTermElabAttr___lambda__1___closed__3;
x_57 = lean_string_append(x_55, x_56);
if (lean_is_scalar(x_50)) {
 x_58 = lean_alloc_ctor(1, 2, 0);
} else {
 x_58 = x_50;
 lean_ctor_set_tag(x_58, 1);
}
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_49);
return x_58;
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_2);
lean_dec(x_1);
x_70 = lean_ctor_get(x_47, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_47, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_72 = x_47;
} else {
 lean_dec_ref(x_47);
 x_72 = lean_box(0);
}
if (lean_is_scalar(x_72)) {
 x_73 = lean_alloc_ctor(1, 2, 0);
} else {
 x_73 = x_72;
}
lean_ctor_set(x_73, 0, x_70);
lean_ctor_set(x_73, 1, x_71);
return x_73;
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
x_6 = lean_expr_mk_mdata(x_5, x_2);
return x_6;
}
}
lean_object* _init_l___private_init_lean_elaborator_preterm_1__dummy___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_Term_prop___elambda__1___rarg___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_init_lean_elaborator_preterm_1__dummy___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_init_lean_elaborator_preterm_1__dummy___closed__1;
x_3 = lean_expr_mk_const(x_2, x_1);
return x_3;
}
}
lean_object* _init_l___private_init_lean_elaborator_preterm_1__dummy() {
_start:
{
lean_object* x_1; 
x_1 = l___private_init_lean_elaborator_preterm_1__dummy___closed__2;
return x_1;
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
x_3 = lean_expr_mk_fvar(x_1);
x_4 = lean_expr_mk_app(x_3, x_2);
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
x_3 = lean_expr_mk_const(x_2, x_1);
return x_3;
}
}
lean_object* l_Lean_mkPreTypeAscription(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Lean_mkPreTypeAscription___closed__3;
x_4 = lean_expr_mk_app(x_3, x_2);
x_5 = lean_expr_mk_app(x_4, x_1);
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
lean_object* l_Array_miterateAux___main___at_Lean_Elab_toLevel___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_2);
x_8 = lean_nat_dec_lt(x_3, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_3);
x_9 = !lean_is_exclusive(x_6);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_6, 0);
lean_dec(x_10);
lean_ctor_set(x_6, 0, x_4);
return x_6;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_6, 1);
lean_inc(x_11);
lean_dec(x_6);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_4);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_array_fget(x_2, x_3);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_3, x_14);
lean_dec(x_3);
x_16 = l_Lean_Elab_toLevel___main(x_13, x_5, x_6);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = level_mk_imax(x_4, x_18);
x_20 = lean_box(0);
lean_ctor_set(x_16, 0, x_20);
x_3 = x_15;
x_4 = x_19;
x_6 = x_16;
goto _start;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_16, 0);
x_23 = lean_ctor_get(x_16, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_16);
x_24 = level_mk_imax(x_4, x_22);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_23);
x_3 = x_15;
x_4 = x_24;
x_6 = x_26;
goto _start;
}
}
else
{
uint8_t x_28; 
lean_dec(x_15);
lean_dec(x_4);
x_28 = !lean_is_exclusive(x_16);
if (x_28 == 0)
{
return x_16;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_16, 0);
x_30 = lean_ctor_get(x_16, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_16);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
}
lean_object* l_Array_miterateAux___main___at_Lean_Elab_toLevel___main___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_2);
x_8 = lean_nat_dec_lt(x_3, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_3);
x_9 = !lean_is_exclusive(x_6);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_6, 0);
lean_dec(x_10);
lean_ctor_set(x_6, 0, x_4);
return x_6;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_6, 1);
lean_inc(x_11);
lean_dec(x_6);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_4);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_array_fget(x_2, x_3);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_3, x_14);
lean_dec(x_3);
x_16 = l_Lean_Elab_toLevel___main(x_13, x_5, x_6);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = level_mk_max(x_4, x_18);
x_20 = lean_box(0);
lean_ctor_set(x_16, 0, x_20);
x_3 = x_15;
x_4 = x_19;
x_6 = x_16;
goto _start;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_16, 0);
x_23 = lean_ctor_get(x_16, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_16);
x_24 = level_mk_max(x_4, x_22);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_23);
x_3 = x_15;
x_4 = x_24;
x_6 = x_26;
goto _start;
}
}
else
{
uint8_t x_28; 
lean_dec(x_15);
lean_dec(x_4);
x_28 = !lean_is_exclusive(x_16);
if (x_28 == 0)
{
return x_16;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_16, 0);
x_30 = lean_ctor_get(x_16, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_16);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
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
lean_object* _init_l_Lean_Elab_toLevel___main___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = level_mk_mvar(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_toLevel___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = l_Lean_Syntax_getKind___rarg(x_1);
x_5 = l_Lean_Parser_Level_paren___elambda__1___rarg___closed__4;
x_6 = lean_name_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = l_Lean_Parser_Level_max___elambda__1___closed__1;
x_8 = lean_name_dec_eq(x_4, x_7);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = l_Lean_Parser_Level_imax___elambda__1___closed__1;
x_10 = lean_name_dec_eq(x_4, x_9);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Lean_Parser_Level_hole___elambda__1___rarg___closed__2;
x_12 = lean_name_dec_eq(x_4, x_11);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = l_Lean_Parser_Level_num___elambda__1___rarg___closed__2;
x_14 = lean_name_dec_eq(x_4, x_13);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = l_Lean_Parser_Level_ident___elambda__1___rarg___closed__1;
x_16 = lean_name_dec_eq(x_4, x_15);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = l_Lean_Parser_Level_addLit___elambda__1___closed__2;
x_18 = lean_name_dec_eq(x_4, x_17);
lean_dec(x_4);
if (x_18 == 0)
{
uint8_t x_19; 
lean_dec(x_1);
x_19 = !lean_is_exclusive(x_3);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_3, 0);
lean_dec(x_20);
x_21 = l_Lean_Elab_toLevel___main___closed__2;
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 0, x_21);
return x_3;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_3, 1);
lean_inc(x_22);
lean_dec(x_3);
x_23 = l_Lean_Elab_toLevel___main___closed__2;
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_unsigned_to_nat(0u);
x_26 = l_Lean_Syntax_getArg___rarg(x_1, x_25);
x_27 = l_Lean_Elab_toLevel___main(x_26, x_2, x_3);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_unsigned_to_nat(2u);
x_31 = l_Lean_Syntax_getArg___rarg(x_1, x_30);
lean_dec(x_1);
x_32 = l_Lean_Syntax_toNat___rarg(x_31);
lean_dec(x_31);
x_33 = l_Lean_Level_addOffsetAux___main(x_32, x_29);
lean_ctor_set(x_27, 0, x_33);
return x_27;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_34 = lean_ctor_get(x_27, 0);
x_35 = lean_ctor_get(x_27, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_27);
x_36 = lean_unsigned_to_nat(2u);
x_37 = l_Lean_Syntax_getArg___rarg(x_1, x_36);
lean_dec(x_1);
x_38 = l_Lean_Syntax_toNat___rarg(x_37);
lean_dec(x_37);
x_39 = l_Lean_Level_addOffsetAux___main(x_38, x_34);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_35);
return x_40;
}
}
else
{
uint8_t x_41; 
lean_dec(x_1);
x_41 = !lean_is_exclusive(x_27);
if (x_41 == 0)
{
return x_27;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_27, 0);
x_43 = lean_ctor_get(x_27, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_27);
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
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_4);
x_45 = lean_unsigned_to_nat(0u);
x_46 = l_Lean_Syntax_getIdAt___rarg(x_1, x_45);
x_47 = l_Lean_Elab_getUniverses___rarg(x_3);
if (lean_obj_tag(x_47) == 0)
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_49 = lean_ctor_get(x_47, 0);
x_50 = lean_ctor_get(x_47, 1);
x_51 = lean_box(0);
lean_inc(x_50);
lean_ctor_set(x_47, 0, x_51);
x_52 = l_List_elem___main___at_Lean_Parser_addBuiltinLeadingParser___spec__4(x_46, x_49);
lean_dec(x_49);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_50);
x_53 = l_System_FilePath_dirName___closed__1;
x_54 = l_Lean_Name_toStringWithSep___main(x_53, x_46);
x_55 = l_Lean_Elab_toLevel___main___closed__3;
x_56 = lean_string_append(x_55, x_54);
lean_dec(x_54);
x_57 = l_Char_HasRepr___closed__1;
x_58 = lean_string_append(x_56, x_57);
x_59 = l_Lean_Elab_logError___rarg(x_1, x_58, x_2, x_47);
lean_dec(x_1);
if (lean_obj_tag(x_59) == 0)
{
uint8_t x_60; 
x_60 = !lean_is_exclusive(x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_59, 0);
lean_dec(x_61);
x_62 = l_Lean_Elab_toLevel___main___closed__4;
lean_ctor_set(x_59, 0, x_62);
return x_59;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_59, 1);
lean_inc(x_63);
lean_dec(x_59);
x_64 = l_Lean_Elab_toLevel___main___closed__4;
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_63);
return x_65;
}
}
else
{
uint8_t x_66; 
x_66 = !lean_is_exclusive(x_59);
if (x_66 == 0)
{
return x_59;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_59, 0);
x_68 = lean_ctor_get(x_59, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_59);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
else
{
lean_object* x_70; lean_object* x_71; 
lean_dec(x_47);
lean_dec(x_1);
x_70 = level_mk_param(x_46);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_50);
return x_71;
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_72 = lean_ctor_get(x_47, 0);
x_73 = lean_ctor_get(x_47, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_47);
x_74 = lean_box(0);
lean_inc(x_73);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_73);
x_76 = l_List_elem___main___at_Lean_Parser_addBuiltinLeadingParser___spec__4(x_46, x_72);
lean_dec(x_72);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_dec(x_73);
x_77 = l_System_FilePath_dirName___closed__1;
x_78 = l_Lean_Name_toStringWithSep___main(x_77, x_46);
x_79 = l_Lean_Elab_toLevel___main___closed__3;
x_80 = lean_string_append(x_79, x_78);
lean_dec(x_78);
x_81 = l_Char_HasRepr___closed__1;
x_82 = lean_string_append(x_80, x_81);
x_83 = l_Lean_Elab_logError___rarg(x_1, x_82, x_2, x_75);
lean_dec(x_1);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_84 = lean_ctor_get(x_83, 1);
lean_inc(x_84);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_85 = x_83;
} else {
 lean_dec_ref(x_83);
 x_85 = lean_box(0);
}
x_86 = l_Lean_Elab_toLevel___main___closed__4;
if (lean_is_scalar(x_85)) {
 x_87 = lean_alloc_ctor(0, 2, 0);
} else {
 x_87 = x_85;
}
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_84);
return x_87;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_88 = lean_ctor_get(x_83, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_83, 1);
lean_inc(x_89);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_90 = x_83;
} else {
 lean_dec_ref(x_83);
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
else
{
lean_object* x_92; lean_object* x_93; 
lean_dec(x_75);
lean_dec(x_1);
x_92 = level_mk_param(x_46);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_73);
return x_93;
}
}
}
else
{
uint8_t x_94; 
lean_dec(x_46);
lean_dec(x_1);
x_94 = !lean_is_exclusive(x_47);
if (x_94 == 0)
{
return x_47;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_47, 0);
x_96 = lean_ctor_get(x_47, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_47);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
}
}
else
{
uint8_t x_98; 
lean_dec(x_4);
x_98 = !lean_is_exclusive(x_3);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_99 = lean_ctor_get(x_3, 0);
lean_dec(x_99);
x_100 = lean_unsigned_to_nat(0u);
x_101 = l_Lean_Syntax_getArg___rarg(x_1, x_100);
lean_dec(x_1);
x_102 = l_Lean_Syntax_toNat___rarg(x_101);
lean_dec(x_101);
x_103 = l_Lean_Level_ofNat___main(x_102);
lean_dec(x_102);
lean_ctor_set(x_3, 0, x_103);
return x_3;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_104 = lean_ctor_get(x_3, 1);
lean_inc(x_104);
lean_dec(x_3);
x_105 = lean_unsigned_to_nat(0u);
x_106 = l_Lean_Syntax_getArg___rarg(x_1, x_105);
lean_dec(x_1);
x_107 = l_Lean_Syntax_toNat___rarg(x_106);
lean_dec(x_106);
x_108 = l_Lean_Level_ofNat___main(x_107);
lean_dec(x_107);
x_109 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_104);
return x_109;
}
}
}
else
{
uint8_t x_110; 
lean_dec(x_4);
lean_dec(x_1);
x_110 = !lean_is_exclusive(x_3);
if (x_110 == 0)
{
lean_object* x_111; lean_object* x_112; 
x_111 = lean_ctor_get(x_3, 0);
lean_dec(x_111);
x_112 = l_Lean_Elab_toLevel___main___closed__4;
lean_ctor_set(x_3, 0, x_112);
return x_3;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_3, 1);
lean_inc(x_113);
lean_dec(x_3);
x_114 = l_Lean_Elab_toLevel___main___closed__4;
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_113);
return x_115;
}
}
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
lean_dec(x_4);
x_116 = lean_unsigned_to_nat(1u);
x_117 = l_Lean_Syntax_getArg___rarg(x_1, x_116);
x_118 = l_Lean_Syntax_getArgs___rarg(x_117);
lean_dec(x_117);
x_119 = lean_box(0);
x_120 = lean_unsigned_to_nat(0u);
x_121 = lean_array_get(x_119, x_118, x_120);
x_122 = l_Lean_Elab_toLevel___main(x_121, x_2, x_3);
if (lean_obj_tag(x_122) == 0)
{
uint8_t x_123; 
x_123 = !lean_is_exclusive(x_122);
if (x_123 == 0)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_122, 0);
x_125 = lean_box(0);
lean_ctor_set(x_122, 0, x_125);
x_126 = l_Array_miterateAux___main___at_Lean_Elab_toLevel___main___spec__1(x_1, x_118, x_116, x_124, x_2, x_122);
lean_dec(x_118);
lean_dec(x_1);
return x_126;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_127 = lean_ctor_get(x_122, 0);
x_128 = lean_ctor_get(x_122, 1);
lean_inc(x_128);
lean_inc(x_127);
lean_dec(x_122);
x_129 = lean_box(0);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_128);
x_131 = l_Array_miterateAux___main___at_Lean_Elab_toLevel___main___spec__1(x_1, x_118, x_116, x_127, x_2, x_130);
lean_dec(x_118);
lean_dec(x_1);
return x_131;
}
}
else
{
uint8_t x_132; 
lean_dec(x_118);
lean_dec(x_1);
x_132 = !lean_is_exclusive(x_122);
if (x_132 == 0)
{
return x_122;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_133 = lean_ctor_get(x_122, 0);
x_134 = lean_ctor_get(x_122, 1);
lean_inc(x_134);
lean_inc(x_133);
lean_dec(x_122);
x_135 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_135, 0, x_133);
lean_ctor_set(x_135, 1, x_134);
return x_135;
}
}
}
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
lean_dec(x_4);
x_136 = lean_unsigned_to_nat(1u);
x_137 = l_Lean_Syntax_getArg___rarg(x_1, x_136);
x_138 = l_Lean_Syntax_getArgs___rarg(x_137);
lean_dec(x_137);
x_139 = lean_box(0);
x_140 = lean_unsigned_to_nat(0u);
x_141 = lean_array_get(x_139, x_138, x_140);
x_142 = l_Lean_Elab_toLevel___main(x_141, x_2, x_3);
if (lean_obj_tag(x_142) == 0)
{
uint8_t x_143; 
x_143 = !lean_is_exclusive(x_142);
if (x_143 == 0)
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_144 = lean_ctor_get(x_142, 0);
x_145 = lean_box(0);
lean_ctor_set(x_142, 0, x_145);
x_146 = l_Array_miterateAux___main___at_Lean_Elab_toLevel___main___spec__2(x_1, x_138, x_136, x_144, x_2, x_142);
lean_dec(x_138);
lean_dec(x_1);
return x_146;
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_147 = lean_ctor_get(x_142, 0);
x_148 = lean_ctor_get(x_142, 1);
lean_inc(x_148);
lean_inc(x_147);
lean_dec(x_142);
x_149 = lean_box(0);
x_150 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_150, 0, x_149);
lean_ctor_set(x_150, 1, x_148);
x_151 = l_Array_miterateAux___main___at_Lean_Elab_toLevel___main___spec__2(x_1, x_138, x_136, x_147, x_2, x_150);
lean_dec(x_138);
lean_dec(x_1);
return x_151;
}
}
else
{
uint8_t x_152; 
lean_dec(x_138);
lean_dec(x_1);
x_152 = !lean_is_exclusive(x_142);
if (x_152 == 0)
{
return x_142;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_153 = lean_ctor_get(x_142, 0);
x_154 = lean_ctor_get(x_142, 1);
lean_inc(x_154);
lean_inc(x_153);
lean_dec(x_142);
x_155 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_155, 0, x_153);
lean_ctor_set(x_155, 1, x_154);
return x_155;
}
}
}
}
else
{
lean_object* x_156; lean_object* x_157; 
lean_dec(x_4);
x_156 = lean_unsigned_to_nat(1u);
x_157 = l_Lean_Syntax_getArg___rarg(x_1, x_156);
lean_dec(x_1);
x_1 = x_157;
goto _start;
}
}
}
lean_object* l_Array_miterateAux___main___at_Lean_Elab_toLevel___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_miterateAux___main___at_Lean_Elab_toLevel___main___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Array_miterateAux___main___at_Lean_Elab_toLevel___main___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_miterateAux___main___at_Lean_Elab_toLevel___main___spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
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
lean_object* _init_l___private_init_lean_elaborator_preterm_2__setPos___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("column");
return x_1;
}
}
lean_object* _init_l___private_init_lean_elaborator_preterm_2__setPos___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_init_lean_elaborator_preterm_2__setPos___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_init_lean_elaborator_preterm_2__setPos___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("row");
return x_1;
}
}
lean_object* _init_l___private_init_lean_elaborator_preterm_2__setPos___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_init_lean_elaborator_preterm_2__setPos___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l___private_init_lean_elaborator_preterm_2__setPos(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_Parser_Term_app___elambda__1___closed__2;
x_6 = l_Lean_Syntax_isOfKind___rarg(x_1, x_5);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_4, 0);
lean_dec(x_8);
x_9 = l_Lean_Syntax_getPos___rarg(x_1);
if (lean_obj_tag(x_9) == 0)
{
lean_ctor_set(x_4, 0, x_2);
return x_4;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_ctor_get(x_3, 1);
x_12 = l_Lean_FileMap_toPosition(x_11, x_10);
lean_dec(x_10);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
x_14 = lean_box(0);
x_15 = l___private_init_lean_elaborator_preterm_2__setPos___closed__2;
x_16 = l_Lean_KVMap_setNat(x_14, x_15, x_13);
x_17 = lean_ctor_get(x_12, 0);
lean_inc(x_17);
lean_dec(x_12);
x_18 = l___private_init_lean_elaborator_preterm_2__setPos___closed__4;
x_19 = l_Lean_KVMap_setNat(x_16, x_18, x_17);
x_20 = lean_expr_mk_mdata(x_19, x_2);
lean_ctor_set(x_4, 0, x_20);
return x_4;
}
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_4, 1);
lean_inc(x_21);
lean_dec(x_4);
x_22 = l_Lean_Syntax_getPos___rarg(x_1);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_2);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_ctor_get(x_3, 1);
x_26 = l_Lean_FileMap_toPosition(x_25, x_24);
lean_dec(x_24);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
x_28 = lean_box(0);
x_29 = l___private_init_lean_elaborator_preterm_2__setPos___closed__2;
x_30 = l_Lean_KVMap_setNat(x_28, x_29, x_27);
x_31 = lean_ctor_get(x_26, 0);
lean_inc(x_31);
lean_dec(x_26);
x_32 = l___private_init_lean_elaborator_preterm_2__setPos___closed__4;
x_33 = l_Lean_KVMap_setNat(x_30, x_32, x_31);
x_34 = lean_expr_mk_mdata(x_33, x_2);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_21);
return x_35;
}
}
}
else
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_4);
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_4, 0);
lean_dec(x_37);
lean_ctor_set(x_4, 0, x_2);
return x_4;
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_4, 1);
lean_inc(x_38);
lean_dec(x_4);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_2);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
lean_object* l___private_init_lean_elaborator_preterm_2__setPos___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_init_lean_elaborator_preterm_2__setPos(x_1, x_2, x_3, x_4);
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
x_7 = lean_name_dec_eq(x_4, x_1);
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
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_3, 0);
lean_dec(x_6);
x_7 = lean_box(0);
lean_ctor_set(x_3, 0, x_7);
x_8 = l_Lean_Elab_toPreTerm___closed__3;
x_9 = l_Lean_Elab_runIOUnsafe___rarg(x_8, x_2, x_3);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
lean_ctor_set(x_9, 0, x_7);
x_12 = l_HashMapImp_find___at_Lean_Elab_toPreTerm___spec__1(x_11, x_4);
lean_dec(x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = l_System_FilePath_dirName___closed__1;
x_14 = l_Lean_Name_toStringWithSep___main(x_13, x_4);
x_15 = l_Lean_Elab_toPreTerm___closed__4;
x_16 = lean_string_append(x_15, x_14);
lean_dec(x_14);
x_17 = l_Char_HasRepr___closed__1;
x_18 = lean_string_append(x_16, x_17);
x_19 = l_Lean_Elab_logErrorAndThrow___rarg(x_1, x_18, x_2, x_9);
lean_dec(x_2);
lean_dec(x_1);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_4);
x_20 = lean_ctor_get(x_12, 0);
lean_inc(x_20);
lean_dec(x_12);
lean_inc(x_2);
lean_inc(x_1);
x_21 = lean_apply_3(x_20, x_1, x_2, x_9);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_21, 0);
lean_ctor_set(x_21, 0, x_7);
x_24 = l___private_init_lean_elaborator_preterm_2__setPos(x_1, x_23, x_2, x_21);
lean_dec(x_2);
lean_dec(x_1);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_21, 0);
x_26 = lean_ctor_get(x_21, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_21);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_7);
lean_ctor_set(x_27, 1, x_26);
x_28 = l___private_init_lean_elaborator_preterm_2__setPos(x_1, x_25, x_2, x_27);
lean_dec(x_2);
lean_dec(x_1);
return x_28;
}
}
else
{
uint8_t x_29; 
lean_dec(x_2);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_21);
if (x_29 == 0)
{
return x_21;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_21, 0);
x_31 = lean_ctor_get(x_21, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_21);
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
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_9, 0);
x_34 = lean_ctor_get(x_9, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_9);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_7);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_HashMapImp_find___at_Lean_Elab_toPreTerm___spec__1(x_33, x_4);
lean_dec(x_33);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_37 = l_System_FilePath_dirName___closed__1;
x_38 = l_Lean_Name_toStringWithSep___main(x_37, x_4);
x_39 = l_Lean_Elab_toPreTerm___closed__4;
x_40 = lean_string_append(x_39, x_38);
lean_dec(x_38);
x_41 = l_Char_HasRepr___closed__1;
x_42 = lean_string_append(x_40, x_41);
x_43 = l_Lean_Elab_logErrorAndThrow___rarg(x_1, x_42, x_2, x_35);
lean_dec(x_2);
lean_dec(x_1);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; 
lean_dec(x_4);
x_44 = lean_ctor_get(x_36, 0);
lean_inc(x_44);
lean_dec(x_36);
lean_inc(x_2);
lean_inc(x_1);
x_45 = lean_apply_3(x_44, x_1, x_2, x_35);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_48 = x_45;
} else {
 lean_dec_ref(x_45);
 x_48 = lean_box(0);
}
if (lean_is_scalar(x_48)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_48;
}
lean_ctor_set(x_49, 0, x_7);
lean_ctor_set(x_49, 1, x_47);
x_50 = l___private_init_lean_elaborator_preterm_2__setPos(x_1, x_46, x_2, x_49);
lean_dec(x_2);
lean_dec(x_1);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_2);
lean_dec(x_1);
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
}
}
else
{
uint8_t x_55; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_55 = !lean_is_exclusive(x_9);
if (x_55 == 0)
{
return x_9;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_9, 0);
x_57 = lean_ctor_get(x_9, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_9);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_59 = lean_ctor_get(x_3, 1);
lean_inc(x_59);
lean_dec(x_3);
x_60 = lean_box(0);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_59);
x_62 = l_Lean_Elab_toPreTerm___closed__3;
x_63 = l_Lean_Elab_runIOUnsafe___rarg(x_62, x_2, x_61);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_66 = x_63;
} else {
 lean_dec_ref(x_63);
 x_66 = lean_box(0);
}
if (lean_is_scalar(x_66)) {
 x_67 = lean_alloc_ctor(0, 2, 0);
} else {
 x_67 = x_66;
}
lean_ctor_set(x_67, 0, x_60);
lean_ctor_set(x_67, 1, x_65);
x_68 = l_HashMapImp_find___at_Lean_Elab_toPreTerm___spec__1(x_64, x_4);
lean_dec(x_64);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_69 = l_System_FilePath_dirName___closed__1;
x_70 = l_Lean_Name_toStringWithSep___main(x_69, x_4);
x_71 = l_Lean_Elab_toPreTerm___closed__4;
x_72 = lean_string_append(x_71, x_70);
lean_dec(x_70);
x_73 = l_Char_HasRepr___closed__1;
x_74 = lean_string_append(x_72, x_73);
x_75 = l_Lean_Elab_logErrorAndThrow___rarg(x_1, x_74, x_2, x_67);
lean_dec(x_2);
lean_dec(x_1);
return x_75;
}
else
{
lean_object* x_76; lean_object* x_77; 
lean_dec(x_4);
x_76 = lean_ctor_get(x_68, 0);
lean_inc(x_76);
lean_dec(x_68);
lean_inc(x_2);
lean_inc(x_1);
x_77 = lean_apply_3(x_76, x_1, x_2, x_67);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 x_80 = x_77;
} else {
 lean_dec_ref(x_77);
 x_80 = lean_box(0);
}
if (lean_is_scalar(x_80)) {
 x_81 = lean_alloc_ctor(0, 2, 0);
} else {
 x_81 = x_80;
}
lean_ctor_set(x_81, 0, x_60);
lean_ctor_set(x_81, 1, x_79);
x_82 = l___private_init_lean_elaborator_preterm_2__setPos(x_1, x_78, x_2, x_81);
lean_dec(x_2);
lean_dec(x_1);
return x_82;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_2);
lean_dec(x_1);
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
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_87 = lean_ctor_get(x_63, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_63, 1);
lean_inc(x_88);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_89 = x_63;
} else {
 lean_dec_ref(x_63);
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
lean_dec(x_2);
lean_dec(x_1);
x_91 = !lean_is_exclusive(x_3);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; 
x_92 = lean_ctor_get(x_3, 0);
lean_dec(x_92);
x_93 = l_Lean_Elab_toPreTerm___closed__2;
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 0, x_93);
return x_3;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_3, 1);
lean_inc(x_94);
lean_dec(x_3);
x_95 = l_Lean_Elab_toPreTerm___closed__2;
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_94);
return x_96;
}
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
lean_object* _init_l___private_init_lean_elaborator_preterm_3__mkHoleFor___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_expr_mk_mvar(x_1);
return x_2;
}
}
lean_object* l___private_init_lean_elaborator_preterm_3__mkHoleFor(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l___private_init_lean_elaborator_preterm_3__mkHoleFor___closed__1;
x_5 = l___private_init_lean_elaborator_preterm_2__setPos(x_1, x_4, x_2, x_3);
return x_5;
}
}
lean_object* l___private_init_lean_elaborator_preterm_3__mkHoleFor___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_init_lean_elaborator_preterm_3__mkHoleFor(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* _init_l_Lean_Elab_convertType___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Level_one___closed__1;
x_2 = lean_expr_mk_sort(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_convertType___rarg(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_dec(x_3);
x_4 = l_Lean_Elab_convertType___rarg___closed__1;
lean_ctor_set(x_1, 0, x_4);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = l_Lean_Elab_convertType___rarg___closed__1;
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
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
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_dec(x_3);
x_4 = l_Lean_exprIsInhabited___closed__1;
lean_ctor_set(x_1, 0, x_4);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = l_Lean_exprIsInhabited___closed__1;
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
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
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_dec(x_3);
x_4 = l_Lean_exprIsInhabited___closed__1;
lean_ctor_set(x_1, 0, x_4);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = l_Lean_exprIsInhabited___closed__1;
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
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
x_15 = lean_expr_mk_sort(x_12);
lean_ctor_set(x_10, 0, x_15);
return x_10;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = level_mk_succ(x_12);
x_17 = lean_expr_mk_sort(x_16);
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
x_22 = lean_expr_mk_sort(x_18);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_19);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = level_mk_succ(x_18);
x_25 = lean_expr_mk_sort(x_24);
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
lean_object* l___private_init_lean_elaborator_preterm_4__mkLocal(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_2 = l_Lean_LocalDecl_name(x_1);
x_3 = l_Lean_LocalDecl_userName(x_1);
x_4 = l_Lean_LocalDecl_type(x_1);
x_5 = l_Lean_LocalDecl_binderInfo(x_1);
x_6 = lean_expr_local(x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l___private_init_lean_elaborator_preterm_4__mkLocal___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_init_lean_elaborator_preterm_4__mkLocal(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* _init_l_Array_ummapAux___main___at___private_init_lean_elaborator_preterm_5__processBinder___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unknown binder default value annotation");
return x_1;
}
}
lean_object* _init_l_Array_ummapAux___main___at___private_init_lean_elaborator_preterm_5__processBinder___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_ummapAux___main___at___private_init_lean_elaborator_preterm_5__processBinder___spec__1___closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Array_ummapAux___main___at___private_init_lean_elaborator_preterm_5__processBinder___spec__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("old elaborator does not support tactics in parameters");
return x_1;
}
}
lean_object* _init_l_Array_ummapAux___main___at___private_init_lean_elaborator_preterm_5__processBinder___spec__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("optParam");
return x_1;
}
}
lean_object* _init_l_Array_ummapAux___main___at___private_init_lean_elaborator_preterm_5__processBinder___spec__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Array_ummapAux___main___at___private_init_lean_elaborator_preterm_5__processBinder___spec__1___closed__4;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Array_ummapAux___main___at___private_init_lean_elaborator_preterm_5__processBinder___spec__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Array_ummapAux___main___at___private_init_lean_elaborator_preterm_5__processBinder___spec__1___closed__5;
x_3 = lean_expr_mk_const(x_2, x_1);
return x_3;
}
}
lean_object* l_Array_ummapAux___main___at___private_init_lean_elaborator_preterm_5__processBinder___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_get_size(x_5);
x_9 = lean_nat_dec_lt(x_4, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
uint8_t x_10; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_7, 0);
lean_dec(x_11);
x_12 = l_Array_empty___closed__1;
x_13 = x_5;
lean_ctor_set(x_7, 0, x_13);
return x_7;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_7, 1);
lean_inc(x_14);
lean_dec(x_7);
x_15 = l_Array_empty___closed__1;
x_16 = x_5;
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_14);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_50; lean_object* x_51; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_18 = lean_array_fget(x_5, x_4);
x_19 = lean_box(0);
lean_inc(x_18);
x_20 = x_19;
x_21 = lean_array_fset(x_5, x_4, x_20);
x_22 = l_Lean_Syntax_getId___rarg(x_18);
x_87 = l_Lean_Syntax_getNumArgs___rarg(x_2);
x_88 = lean_unsigned_to_nat(0u);
x_89 = lean_nat_dec_eq(x_87, x_88);
lean_dec(x_87);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_unsigned_to_nat(1u);
x_91 = l_Lean_Syntax_getArg___rarg(x_2, x_90);
lean_inc(x_6);
x_92 = l_Lean_Elab_toPreTerm(x_91, x_6, x_7);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; 
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
lean_dec(x_92);
x_50 = x_93;
x_51 = x_94;
goto block_86;
}
else
{
uint8_t x_95; 
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_18);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_95 = !lean_is_exclusive(x_92);
if (x_95 == 0)
{
return x_92;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_92, 0);
x_97 = lean_ctor_get(x_92, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_92);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
}
}
else
{
lean_object* x_99; 
x_99 = l___private_init_lean_elaborator_preterm_3__mkHoleFor(x_18, x_6, x_7);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; 
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_99, 1);
lean_inc(x_101);
lean_dec(x_99);
x_50 = x_100;
x_51 = x_101;
goto block_86;
}
else
{
uint8_t x_102; 
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_18);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_102 = !lean_is_exclusive(x_99);
if (x_102 == 0)
{
return x_99;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_99, 0);
x_104 = lean_ctor_get(x_99, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_99);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
return x_105;
}
}
}
block_49:
{
lean_object* x_25; uint8_t x_26; lean_object* x_27; 
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_19);
lean_ctor_set(x_25, 1, x_24);
x_26 = 0;
x_27 = l_Lean_Elab_mkLocalDecl(x_22, x_23, x_26, x_6, x_25);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = l___private_init_lean_elaborator_preterm_4__mkLocal(x_29);
lean_dec(x_29);
lean_ctor_set(x_27, 0, x_19);
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_nat_add(x_4, x_31);
x_33 = x_30;
x_34 = lean_array_fset(x_21, x_4, x_33);
lean_dec(x_4);
x_4 = x_32;
x_5 = x_34;
x_7 = x_27;
goto _start;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_36 = lean_ctor_get(x_27, 0);
x_37 = lean_ctor_get(x_27, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_27);
x_38 = l___private_init_lean_elaborator_preterm_4__mkLocal(x_36);
lean_dec(x_36);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_19);
lean_ctor_set(x_39, 1, x_37);
x_40 = lean_unsigned_to_nat(1u);
x_41 = lean_nat_add(x_4, x_40);
x_42 = x_38;
x_43 = lean_array_fset(x_21, x_4, x_42);
lean_dec(x_4);
x_4 = x_41;
x_5 = x_43;
x_7 = x_39;
goto _start;
}
}
else
{
uint8_t x_45; 
lean_dec(x_21);
lean_dec(x_18);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
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
block_86:
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
lean_inc(x_51);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_19);
lean_ctor_set(x_52, 1, x_51);
x_53 = l_Lean_Syntax_getNumArgs___rarg(x_3);
x_54 = lean_unsigned_to_nat(0u);
x_55 = lean_nat_dec_eq(x_53, x_54);
lean_dec(x_53);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_56 = l_Lean_Syntax_getArg___rarg(x_3, x_54);
x_57 = l_Lean_Syntax_getKind___rarg(x_56);
x_58 = l_Lean_Parser_Term_binderDefault___elambda__1___rarg___closed__1;
lean_inc(x_1);
x_59 = lean_name_mk_string(x_1, x_58);
x_60 = lean_name_dec_eq(x_57, x_59);
lean_dec(x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; 
lean_dec(x_56);
lean_dec(x_50);
x_61 = l_Lean_Parser_Term_binderTactic___elambda__1___rarg___closed__1;
lean_inc(x_1);
x_62 = lean_name_mk_string(x_1, x_61);
x_63 = lean_name_dec_eq(x_57, x_62);
lean_dec(x_62);
lean_dec(x_57);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; 
lean_dec(x_52);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_18);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_64 = l_Array_ummapAux___main___at___private_init_lean_elaborator_preterm_5__processBinder___spec__1___closed__2;
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_51);
return x_65;
}
else
{
lean_object* x_66; lean_object* x_67; 
lean_dec(x_51);
x_66 = l_Array_ummapAux___main___at___private_init_lean_elaborator_preterm_5__processBinder___spec__1___closed__3;
x_67 = l_Lean_Elab_logErrorAndThrow___rarg(x_3, x_66, x_6, x_52);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_23 = x_68;
x_24 = x_69;
goto block_49;
}
else
{
uint8_t x_70; 
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_18);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_70 = !lean_is_exclusive(x_67);
if (x_70 == 0)
{
return x_67;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_67, 0);
x_72 = lean_ctor_get(x_67, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_67);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_57);
lean_dec(x_51);
x_74 = lean_unsigned_to_nat(1u);
x_75 = l_Lean_Syntax_getArg___rarg(x_56, x_74);
lean_dec(x_56);
lean_inc(x_6);
x_76 = l_Lean_Elab_toPreTerm(x_75, x_6, x_52);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_79 = l_Array_ummapAux___main___at___private_init_lean_elaborator_preterm_5__processBinder___spec__1___closed__6;
x_80 = lean_expr_mk_app(x_79, x_50);
x_81 = lean_expr_mk_app(x_80, x_77);
x_23 = x_81;
x_24 = x_78;
goto block_49;
}
else
{
uint8_t x_82; 
lean_dec(x_50);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_18);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_82 = !lean_is_exclusive(x_76);
if (x_82 == 0)
{
return x_76;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_76, 0);
x_84 = lean_ctor_get(x_76, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_76);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
}
}
else
{
lean_dec(x_52);
x_23 = x_50;
x_24 = x_51;
goto block_49;
}
}
}
}
}
lean_object* l_Array_ummapAux___main___at___private_init_lean_elaborator_preterm_5__processBinder___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_2);
x_6 = lean_nat_dec_lt(x_1, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
uint8_t x_7; 
lean_dec(x_1);
x_7 = !lean_is_exclusive(x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_4, 0);
lean_dec(x_8);
x_9 = l_Array_empty___closed__1;
x_10 = x_2;
lean_ctor_set(x_4, 0, x_10);
return x_4;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_4, 1);
lean_inc(x_11);
lean_dec(x_4);
x_12 = l_Array_empty___closed__1;
x_13 = x_2;
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_array_fget(x_2, x_1);
x_16 = lean_box(0);
lean_inc(x_15);
x_17 = x_16;
x_18 = lean_array_fset(x_2, x_1, x_17);
x_19 = l_Lean_Syntax_getId___rarg(x_15);
x_20 = l___private_init_lean_elaborator_preterm_3__mkHoleFor(x_15, x_3, x_4);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_20, 0);
lean_ctor_set(x_20, 0, x_16);
x_23 = 0;
x_24 = l_Lean_Elab_mkLocalDecl(x_19, x_22, x_23, x_3, x_20);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_26 = lean_ctor_get(x_24, 0);
x_27 = l___private_init_lean_elaborator_preterm_4__mkLocal(x_26);
lean_dec(x_26);
lean_ctor_set(x_24, 0, x_16);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_add(x_1, x_28);
x_30 = x_27;
x_31 = lean_array_fset(x_18, x_1, x_30);
lean_dec(x_1);
x_1 = x_29;
x_2 = x_31;
x_4 = x_24;
goto _start;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_33 = lean_ctor_get(x_24, 0);
x_34 = lean_ctor_get(x_24, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_24);
x_35 = l___private_init_lean_elaborator_preterm_4__mkLocal(x_33);
lean_dec(x_33);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_16);
lean_ctor_set(x_36, 1, x_34);
x_37 = lean_unsigned_to_nat(1u);
x_38 = lean_nat_add(x_1, x_37);
x_39 = x_35;
x_40 = lean_array_fset(x_18, x_1, x_39);
lean_dec(x_1);
x_1 = x_38;
x_2 = x_40;
x_4 = x_36;
goto _start;
}
}
else
{
uint8_t x_42; 
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_24);
if (x_42 == 0)
{
return x_24;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_24, 0);
x_44 = lean_ctor_get(x_24, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_24);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; 
x_46 = lean_ctor_get(x_20, 0);
x_47 = lean_ctor_get(x_20, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_20);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_16);
lean_ctor_set(x_48, 1, x_47);
x_49 = 0;
x_50 = l_Lean_Elab_mkLocalDecl(x_19, x_46, x_49, x_3, x_48);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_53 = x_50;
} else {
 lean_dec_ref(x_50);
 x_53 = lean_box(0);
}
x_54 = l___private_init_lean_elaborator_preterm_4__mkLocal(x_51);
lean_dec(x_51);
if (lean_is_scalar(x_53)) {
 x_55 = lean_alloc_ctor(0, 2, 0);
} else {
 x_55 = x_53;
}
lean_ctor_set(x_55, 0, x_16);
lean_ctor_set(x_55, 1, x_52);
x_56 = lean_unsigned_to_nat(1u);
x_57 = lean_nat_add(x_1, x_56);
x_58 = x_54;
x_59 = lean_array_fset(x_18, x_1, x_58);
lean_dec(x_1);
x_1 = x_57;
x_2 = x_59;
x_4 = x_55;
goto _start;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_1);
x_61 = lean_ctor_get(x_50, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_50, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_63 = x_50;
} else {
 lean_dec_ref(x_50);
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
else
{
uint8_t x_65; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_1);
x_65 = !lean_is_exclusive(x_20);
if (x_65 == 0)
{
return x_20;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_20, 0);
x_67 = lean_ctor_get(x_20, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_20);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
}
}
lean_object* _init_l___private_init_lean_elaborator_preterm_5__processBinder___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unknown binder kind");
return x_1;
}
}
lean_object* _init_l___private_init_lean_elaborator_preterm_5__processBinder___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_init_lean_elaborator_preterm_5__processBinder___closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_init_lean_elaborator_preterm_5__processBinder___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(">> inst ");
return x_1;
}
}
lean_object* _init_l___private_init_lean_elaborator_preterm_5__processBinder___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(">> implict ");
return x_1;
}
}
lean_object* l___private_init_lean_elaborator_preterm_5__processBinder(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = l_Lean_Syntax_getKind___rarg(x_1);
x_5 = l_Lean_Parser_Term_simpleBinder___elambda__1___closed__2;
x_6 = lean_name_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = l_Lean_Parser_Term_explicitBinder___elambda__1___closed__2;
x_8 = lean_name_dec_eq(x_4, x_7);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = l_Lean_Parser_Term_implicitBinder___elambda__1___closed__2;
x_10 = lean_name_dec_eq(x_4, x_9);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Lean_Parser_Term_instBinder___elambda__1___rarg___closed__2;
x_12 = lean_name_dec_eq(x_4, x_11);
lean_dec(x_4);
if (x_12 == 0)
{
uint8_t x_13; 
lean_dec(x_2);
lean_dec(x_1);
x_13 = !lean_is_exclusive(x_3);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_3, 0);
lean_dec(x_14);
x_15 = l___private_init_lean_elaborator_preterm_5__processBinder___closed__2;
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 0, x_15);
return x_3;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_3, 1);
lean_inc(x_16);
lean_dec(x_3);
x_17 = l___private_init_lean_elaborator_preterm_5__processBinder___closed__2;
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_19 = l_Lean_Syntax_formatStx___main___rarg(x_1);
x_20 = l_Lean_Options_empty;
x_21 = l_Lean_Format_pretty(x_19, x_20);
x_22 = l___private_init_lean_elaborator_preterm_5__processBinder___closed__3;
x_23 = lean_string_append(x_22, x_21);
lean_dec(x_21);
x_24 = lean_alloc_closure((void*)(l_IO_println___at_HasRepr_HasEval___spec__1___boxed), 2, 1);
lean_closure_set(x_24, 0, x_23);
x_25 = l_Lean_Elab_runIOUnsafe___rarg(x_24, x_2, x_3);
lean_dec(x_2);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_25, 0);
lean_dec(x_27);
x_28 = l_Array_empty___closed__1;
lean_ctor_set(x_25, 0, x_28);
return x_25;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_25, 1);
lean_inc(x_29);
lean_dec(x_25);
x_30 = l_Array_empty___closed__1;
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
else
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_25);
if (x_32 == 0)
{
return x_25;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_25, 0);
x_34 = lean_ctor_get(x_25, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_25);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_4);
x_36 = l_Lean_Syntax_formatStx___main___rarg(x_1);
x_37 = l_Lean_Options_empty;
x_38 = l_Lean_Format_pretty(x_36, x_37);
x_39 = l___private_init_lean_elaborator_preterm_5__processBinder___closed__4;
x_40 = lean_string_append(x_39, x_38);
lean_dec(x_38);
x_41 = lean_alloc_closure((void*)(l_IO_println___at_HasRepr_HasEval___spec__1___boxed), 2, 1);
lean_closure_set(x_41, 0, x_40);
x_42 = l_Lean_Elab_runIOUnsafe___rarg(x_41, x_2, x_3);
lean_dec(x_2);
if (lean_obj_tag(x_42) == 0)
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_42, 0);
lean_dec(x_44);
x_45 = l_Array_empty___closed__1;
lean_ctor_set(x_42, 0, x_45);
return x_42;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_42, 1);
lean_inc(x_46);
lean_dec(x_42);
x_47 = l_Array_empty___closed__1;
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
}
else
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_42);
if (x_49 == 0)
{
return x_42;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_42, 0);
x_51 = lean_ctor_get(x_42, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_42);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_4);
x_53 = lean_unsigned_to_nat(1u);
x_54 = l_Lean_Syntax_getArg___rarg(x_1, x_53);
x_55 = l_Lean_Syntax_getArgs___rarg(x_54);
lean_dec(x_54);
x_56 = lean_unsigned_to_nat(2u);
x_57 = l_Lean_Syntax_getArg___rarg(x_1, x_56);
x_58 = lean_unsigned_to_nat(3u);
x_59 = l_Lean_Syntax_getArg___rarg(x_1, x_58);
lean_dec(x_1);
x_60 = l_Lean_Parser_Term_explicitUniv___elambda__1___closed__2;
x_61 = lean_unsigned_to_nat(0u);
x_62 = l_Array_ummapAux___main___at___private_init_lean_elaborator_preterm_5__processBinder___spec__1(x_60, x_57, x_59, x_61, x_55, x_2, x_3);
lean_dec(x_59);
lean_dec(x_57);
return x_62;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_4);
x_63 = lean_unsigned_to_nat(0u);
x_64 = l_Lean_Syntax_getArg___rarg(x_1, x_63);
lean_dec(x_1);
x_65 = l_Lean_Syntax_getArgs___rarg(x_64);
lean_dec(x_64);
x_66 = l_Array_ummapAux___main___at___private_init_lean_elaborator_preterm_5__processBinder___spec__2(x_63, x_65, x_2, x_3);
lean_dec(x_2);
return x_66;
}
}
}
lean_object* l_Array_ummapAux___main___at___private_init_lean_elaborator_preterm_5__processBinder___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_ummapAux___main___at___private_init_lean_elaborator_preterm_5__processBinder___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Array_ummapAux___main___at___private_init_lean_elaborator_preterm_5__processBinder___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_ummapAux___main___at___private_init_lean_elaborator_preterm_5__processBinder___spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Array_miterateAux___main___at___private_init_lean_elaborator_preterm_6__processBinders___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_2);
x_8 = lean_nat_dec_lt(x_3, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_5);
lean_dec(x_3);
x_9 = !lean_is_exclusive(x_6);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_6, 0);
lean_dec(x_10);
lean_ctor_set(x_6, 0, x_4);
return x_6;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_6, 1);
lean_inc(x_11);
lean_dec(x_6);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_4);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_array_fget(x_2, x_3);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_3, x_14);
lean_dec(x_3);
lean_inc(x_5);
x_16 = l___private_init_lean_elaborator_preterm_5__processBinder(x_13, x_5, x_6);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_unsigned_to_nat(0u);
x_20 = l_Array_miterateAux___main___at_Array_append___spec__1___rarg(x_18, x_18, x_19, x_4);
lean_dec(x_18);
x_21 = lean_box(0);
lean_ctor_set(x_16, 0, x_21);
x_3 = x_15;
x_4 = x_20;
x_6 = x_16;
goto _start;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_23 = lean_ctor_get(x_16, 0);
x_24 = lean_ctor_get(x_16, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_16);
x_25 = lean_unsigned_to_nat(0u);
x_26 = l_Array_miterateAux___main___at_Array_append___spec__1___rarg(x_23, x_23, x_25, x_4);
lean_dec(x_23);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_24);
x_3 = x_15;
x_4 = x_26;
x_6 = x_28;
goto _start;
}
}
else
{
uint8_t x_30; 
lean_dec(x_15);
lean_dec(x_5);
lean_dec(x_4);
x_30 = !lean_is_exclusive(x_16);
if (x_30 == 0)
{
return x_16;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_16, 0);
x_32 = lean_ctor_get(x_16, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_16);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
}
lean_object* l___private_init_lean_elaborator_preterm_6__processBinders(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Array_empty___closed__1;
x_6 = l_Array_miterateAux___main___at___private_init_lean_elaborator_preterm_6__processBinders___spec__1(x_1, x_1, x_4, x_5, x_2, x_3);
return x_6;
}
}
lean_object* l_Array_miterateAux___main___at___private_init_lean_elaborator_preterm_6__processBinders___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_miterateAux___main___at___private_init_lean_elaborator_preterm_6__processBinders___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l___private_init_lean_elaborator_preterm_6__processBinders___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_init_lean_elaborator_preterm_6__processBinders(x_1, x_2, x_3);
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_3, 0);
lean_dec(x_7);
x_8 = lean_box(0);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_array_get(x_8, x_5, x_9);
x_11 = l_Lean_Syntax_getArgs___rarg(x_10);
lean_dec(x_10);
x_12 = lean_unsigned_to_nat(3u);
x_13 = lean_array_get(x_8, x_5, x_12);
x_14 = !lean_is_exclusive(x_6);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_6, 5);
x_16 = l_List_head___at_Lean_Elab_getScope___spec__1(x_15);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
lean_ctor_set(x_6, 5, x_17);
x_18 = lean_box(0);
lean_ctor_set(x_3, 0, x_18);
lean_inc(x_2);
x_19 = l___private_init_lean_elaborator_preterm_6__processBinders(x_11, x_2, x_3);
lean_dec(x_11);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_19, 0);
lean_ctor_set(x_19, 0, x_18);
lean_inc(x_2);
x_22 = l_Lean_Elab_toPreTerm(x_13, x_2, x_19);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_22, 0);
lean_ctor_set(x_22, 0, x_18);
x_25 = l_Lean_Elab_mkForall(x_21, x_24, x_2, x_22);
lean_dec(x_2);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_25, 1);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_27, 5);
x_30 = l_List_tail___rarg(x_29);
lean_dec(x_29);
lean_ctor_set(x_27, 5, x_30);
return x_25;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_31 = lean_ctor_get(x_27, 0);
x_32 = lean_ctor_get(x_27, 1);
x_33 = lean_ctor_get(x_27, 2);
x_34 = lean_ctor_get(x_27, 3);
x_35 = lean_ctor_get(x_27, 4);
x_36 = lean_ctor_get(x_27, 5);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_27);
x_37 = l_List_tail___rarg(x_36);
lean_dec(x_36);
x_38 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_38, 0, x_31);
lean_ctor_set(x_38, 1, x_32);
lean_ctor_set(x_38, 2, x_33);
lean_ctor_set(x_38, 3, x_34);
lean_ctor_set(x_38, 4, x_35);
lean_ctor_set(x_38, 5, x_37);
lean_ctor_set(x_25, 1, x_38);
return x_25;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_39 = lean_ctor_get(x_25, 1);
x_40 = lean_ctor_get(x_25, 0);
lean_inc(x_39);
lean_inc(x_40);
lean_dec(x_25);
x_41 = lean_ctor_get(x_39, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_39, 1);
lean_inc(x_42);
x_43 = lean_ctor_get(x_39, 2);
lean_inc(x_43);
x_44 = lean_ctor_get(x_39, 3);
lean_inc(x_44);
x_45 = lean_ctor_get(x_39, 4);
lean_inc(x_45);
x_46 = lean_ctor_get(x_39, 5);
lean_inc(x_46);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 lean_ctor_release(x_39, 2);
 lean_ctor_release(x_39, 3);
 lean_ctor_release(x_39, 4);
 lean_ctor_release(x_39, 5);
 x_47 = x_39;
} else {
 lean_dec_ref(x_39);
 x_47 = lean_box(0);
}
x_48 = l_List_tail___rarg(x_46);
lean_dec(x_46);
if (lean_is_scalar(x_47)) {
 x_49 = lean_alloc_ctor(0, 6, 0);
} else {
 x_49 = x_47;
}
lean_ctor_set(x_49, 0, x_41);
lean_ctor_set(x_49, 1, x_42);
lean_ctor_set(x_49, 2, x_43);
lean_ctor_set(x_49, 3, x_44);
lean_ctor_set(x_49, 4, x_45);
lean_ctor_set(x_49, 5, x_48);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_40);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
else
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_25);
if (x_51 == 0)
{
return x_25;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_25, 0);
x_53 = lean_ctor_get(x_25, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_25);
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
x_55 = lean_ctor_get(x_22, 0);
x_56 = lean_ctor_get(x_22, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_22);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_18);
lean_ctor_set(x_57, 1, x_56);
x_58 = l_Lean_Elab_mkForall(x_21, x_55, x_2, x_57);
lean_dec(x_2);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 0);
lean_inc(x_60);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_61 = x_58;
} else {
 lean_dec_ref(x_58);
 x_61 = lean_box(0);
}
x_62 = lean_ctor_get(x_59, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_59, 1);
lean_inc(x_63);
x_64 = lean_ctor_get(x_59, 2);
lean_inc(x_64);
x_65 = lean_ctor_get(x_59, 3);
lean_inc(x_65);
x_66 = lean_ctor_get(x_59, 4);
lean_inc(x_66);
x_67 = lean_ctor_get(x_59, 5);
lean_inc(x_67);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 lean_ctor_release(x_59, 2);
 lean_ctor_release(x_59, 3);
 lean_ctor_release(x_59, 4);
 lean_ctor_release(x_59, 5);
 x_68 = x_59;
} else {
 lean_dec_ref(x_59);
 x_68 = lean_box(0);
}
x_69 = l_List_tail___rarg(x_67);
lean_dec(x_67);
if (lean_is_scalar(x_68)) {
 x_70 = lean_alloc_ctor(0, 6, 0);
} else {
 x_70 = x_68;
}
lean_ctor_set(x_70, 0, x_62);
lean_ctor_set(x_70, 1, x_63);
lean_ctor_set(x_70, 2, x_64);
lean_ctor_set(x_70, 3, x_65);
lean_ctor_set(x_70, 4, x_66);
lean_ctor_set(x_70, 5, x_69);
if (lean_is_scalar(x_61)) {
 x_71 = lean_alloc_ctor(0, 2, 0);
} else {
 x_71 = x_61;
}
lean_ctor_set(x_71, 0, x_60);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_72 = lean_ctor_get(x_58, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_58, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_74 = x_58;
} else {
 lean_dec_ref(x_58);
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
lean_dec(x_21);
lean_dec(x_2);
x_76 = !lean_is_exclusive(x_22);
if (x_76 == 0)
{
return x_22;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_22, 0);
x_78 = lean_ctor_get(x_22, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_22);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_80 = lean_ctor_get(x_19, 0);
x_81 = lean_ctor_get(x_19, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_19);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_18);
lean_ctor_set(x_82, 1, x_81);
lean_inc(x_2);
x_83 = l_Lean_Elab_toPreTerm(x_13, x_2, x_82);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_86 = x_83;
} else {
 lean_dec_ref(x_83);
 x_86 = lean_box(0);
}
if (lean_is_scalar(x_86)) {
 x_87 = lean_alloc_ctor(0, 2, 0);
} else {
 x_87 = x_86;
}
lean_ctor_set(x_87, 0, x_18);
lean_ctor_set(x_87, 1, x_85);
x_88 = l_Lean_Elab_mkForall(x_80, x_84, x_2, x_87);
lean_dec(x_2);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_89 = lean_ctor_get(x_88, 1);
lean_inc(x_89);
x_90 = lean_ctor_get(x_88, 0);
lean_inc(x_90);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 lean_ctor_release(x_88, 1);
 x_91 = x_88;
} else {
 lean_dec_ref(x_88);
 x_91 = lean_box(0);
}
x_92 = lean_ctor_get(x_89, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_89, 1);
lean_inc(x_93);
x_94 = lean_ctor_get(x_89, 2);
lean_inc(x_94);
x_95 = lean_ctor_get(x_89, 3);
lean_inc(x_95);
x_96 = lean_ctor_get(x_89, 4);
lean_inc(x_96);
x_97 = lean_ctor_get(x_89, 5);
lean_inc(x_97);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 lean_ctor_release(x_89, 2);
 lean_ctor_release(x_89, 3);
 lean_ctor_release(x_89, 4);
 lean_ctor_release(x_89, 5);
 x_98 = x_89;
} else {
 lean_dec_ref(x_89);
 x_98 = lean_box(0);
}
x_99 = l_List_tail___rarg(x_97);
lean_dec(x_97);
if (lean_is_scalar(x_98)) {
 x_100 = lean_alloc_ctor(0, 6, 0);
} else {
 x_100 = x_98;
}
lean_ctor_set(x_100, 0, x_92);
lean_ctor_set(x_100, 1, x_93);
lean_ctor_set(x_100, 2, x_94);
lean_ctor_set(x_100, 3, x_95);
lean_ctor_set(x_100, 4, x_96);
lean_ctor_set(x_100, 5, x_99);
if (lean_is_scalar(x_91)) {
 x_101 = lean_alloc_ctor(0, 2, 0);
} else {
 x_101 = x_91;
}
lean_ctor_set(x_101, 0, x_90);
lean_ctor_set(x_101, 1, x_100);
return x_101;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_102 = lean_ctor_get(x_88, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_88, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 lean_ctor_release(x_88, 1);
 x_104 = x_88;
} else {
 lean_dec_ref(x_88);
 x_104 = lean_box(0);
}
if (lean_is_scalar(x_104)) {
 x_105 = lean_alloc_ctor(1, 2, 0);
} else {
 x_105 = x_104;
}
lean_ctor_set(x_105, 0, x_102);
lean_ctor_set(x_105, 1, x_103);
return x_105;
}
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
lean_dec(x_80);
lean_dec(x_2);
x_106 = lean_ctor_get(x_83, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_83, 1);
lean_inc(x_107);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_108 = x_83;
} else {
 lean_dec_ref(x_83);
 x_108 = lean_box(0);
}
if (lean_is_scalar(x_108)) {
 x_109 = lean_alloc_ctor(1, 2, 0);
} else {
 x_109 = x_108;
}
lean_ctor_set(x_109, 0, x_106);
lean_ctor_set(x_109, 1, x_107);
return x_109;
}
}
}
else
{
uint8_t x_110; 
lean_dec(x_13);
lean_dec(x_2);
x_110 = !lean_is_exclusive(x_19);
if (x_110 == 0)
{
return x_19;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_19, 0);
x_112 = lean_ctor_get(x_19, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_19);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
return x_113;
}
}
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_114 = lean_ctor_get(x_6, 0);
x_115 = lean_ctor_get(x_6, 1);
x_116 = lean_ctor_get(x_6, 2);
x_117 = lean_ctor_get(x_6, 3);
x_118 = lean_ctor_get(x_6, 4);
x_119 = lean_ctor_get(x_6, 5);
lean_inc(x_119);
lean_inc(x_118);
lean_inc(x_117);
lean_inc(x_116);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_6);
x_120 = l_List_head___at_Lean_Elab_getScope___spec__1(x_119);
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_119);
x_122 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_122, 0, x_114);
lean_ctor_set(x_122, 1, x_115);
lean_ctor_set(x_122, 2, x_116);
lean_ctor_set(x_122, 3, x_117);
lean_ctor_set(x_122, 4, x_118);
lean_ctor_set(x_122, 5, x_121);
x_123 = lean_box(0);
lean_ctor_set(x_3, 1, x_122);
lean_ctor_set(x_3, 0, x_123);
lean_inc(x_2);
x_124 = l___private_init_lean_elaborator_preterm_6__processBinders(x_11, x_2, x_3);
lean_dec(x_11);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_124, 1);
lean_inc(x_126);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 x_127 = x_124;
} else {
 lean_dec_ref(x_124);
 x_127 = lean_box(0);
}
if (lean_is_scalar(x_127)) {
 x_128 = lean_alloc_ctor(0, 2, 0);
} else {
 x_128 = x_127;
}
lean_ctor_set(x_128, 0, x_123);
lean_ctor_set(x_128, 1, x_126);
lean_inc(x_2);
x_129 = l_Lean_Elab_toPreTerm(x_13, x_2, x_128);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_129, 1);
lean_inc(x_131);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 lean_ctor_release(x_129, 1);
 x_132 = x_129;
} else {
 lean_dec_ref(x_129);
 x_132 = lean_box(0);
}
if (lean_is_scalar(x_132)) {
 x_133 = lean_alloc_ctor(0, 2, 0);
} else {
 x_133 = x_132;
}
lean_ctor_set(x_133, 0, x_123);
lean_ctor_set(x_133, 1, x_131);
x_134 = l_Lean_Elab_mkForall(x_125, x_130, x_2, x_133);
lean_dec(x_2);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_135 = lean_ctor_get(x_134, 1);
lean_inc(x_135);
x_136 = lean_ctor_get(x_134, 0);
lean_inc(x_136);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 lean_ctor_release(x_134, 1);
 x_137 = x_134;
} else {
 lean_dec_ref(x_134);
 x_137 = lean_box(0);
}
x_138 = lean_ctor_get(x_135, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_135, 1);
lean_inc(x_139);
x_140 = lean_ctor_get(x_135, 2);
lean_inc(x_140);
x_141 = lean_ctor_get(x_135, 3);
lean_inc(x_141);
x_142 = lean_ctor_get(x_135, 4);
lean_inc(x_142);
x_143 = lean_ctor_get(x_135, 5);
lean_inc(x_143);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 lean_ctor_release(x_135, 1);
 lean_ctor_release(x_135, 2);
 lean_ctor_release(x_135, 3);
 lean_ctor_release(x_135, 4);
 lean_ctor_release(x_135, 5);
 x_144 = x_135;
} else {
 lean_dec_ref(x_135);
 x_144 = lean_box(0);
}
x_145 = l_List_tail___rarg(x_143);
lean_dec(x_143);
if (lean_is_scalar(x_144)) {
 x_146 = lean_alloc_ctor(0, 6, 0);
} else {
 x_146 = x_144;
}
lean_ctor_set(x_146, 0, x_138);
lean_ctor_set(x_146, 1, x_139);
lean_ctor_set(x_146, 2, x_140);
lean_ctor_set(x_146, 3, x_141);
lean_ctor_set(x_146, 4, x_142);
lean_ctor_set(x_146, 5, x_145);
if (lean_is_scalar(x_137)) {
 x_147 = lean_alloc_ctor(0, 2, 0);
} else {
 x_147 = x_137;
}
lean_ctor_set(x_147, 0, x_136);
lean_ctor_set(x_147, 1, x_146);
return x_147;
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_148 = lean_ctor_get(x_134, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_134, 1);
lean_inc(x_149);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 lean_ctor_release(x_134, 1);
 x_150 = x_134;
} else {
 lean_dec_ref(x_134);
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
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
lean_dec(x_125);
lean_dec(x_2);
x_152 = lean_ctor_get(x_129, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_129, 1);
lean_inc(x_153);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 lean_ctor_release(x_129, 1);
 x_154 = x_129;
} else {
 lean_dec_ref(x_129);
 x_154 = lean_box(0);
}
if (lean_is_scalar(x_154)) {
 x_155 = lean_alloc_ctor(1, 2, 0);
} else {
 x_155 = x_154;
}
lean_ctor_set(x_155, 0, x_152);
lean_ctor_set(x_155, 1, x_153);
return x_155;
}
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
lean_dec(x_13);
lean_dec(x_2);
x_156 = lean_ctor_get(x_124, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_124, 1);
lean_inc(x_157);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 x_158 = x_124;
} else {
 lean_dec_ref(x_124);
 x_158 = lean_box(0);
}
if (lean_is_scalar(x_158)) {
 x_159 = lean_alloc_ctor(1, 2, 0);
} else {
 x_159 = x_158;
}
lean_ctor_set(x_159, 0, x_156);
lean_ctor_set(x_159, 1, x_157);
return x_159;
}
}
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_160 = lean_ctor_get(x_1, 1);
x_161 = lean_ctor_get(x_3, 1);
lean_inc(x_161);
lean_dec(x_3);
x_162 = lean_box(0);
x_163 = lean_unsigned_to_nat(1u);
x_164 = lean_array_get(x_162, x_160, x_163);
x_165 = l_Lean_Syntax_getArgs___rarg(x_164);
lean_dec(x_164);
x_166 = lean_unsigned_to_nat(3u);
x_167 = lean_array_get(x_162, x_160, x_166);
x_168 = lean_ctor_get(x_161, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_161, 1);
lean_inc(x_169);
x_170 = lean_ctor_get(x_161, 2);
lean_inc(x_170);
x_171 = lean_ctor_get(x_161, 3);
lean_inc(x_171);
x_172 = lean_ctor_get(x_161, 4);
lean_inc(x_172);
x_173 = lean_ctor_get(x_161, 5);
lean_inc(x_173);
if (lean_is_exclusive(x_161)) {
 lean_ctor_release(x_161, 0);
 lean_ctor_release(x_161, 1);
 lean_ctor_release(x_161, 2);
 lean_ctor_release(x_161, 3);
 lean_ctor_release(x_161, 4);
 lean_ctor_release(x_161, 5);
 x_174 = x_161;
} else {
 lean_dec_ref(x_161);
 x_174 = lean_box(0);
}
x_175 = l_List_head___at_Lean_Elab_getScope___spec__1(x_173);
x_176 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_176, 0, x_175);
lean_ctor_set(x_176, 1, x_173);
if (lean_is_scalar(x_174)) {
 x_177 = lean_alloc_ctor(0, 6, 0);
} else {
 x_177 = x_174;
}
lean_ctor_set(x_177, 0, x_168);
lean_ctor_set(x_177, 1, x_169);
lean_ctor_set(x_177, 2, x_170);
lean_ctor_set(x_177, 3, x_171);
lean_ctor_set(x_177, 4, x_172);
lean_ctor_set(x_177, 5, x_176);
x_178 = lean_box(0);
x_179 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_179, 0, x_178);
lean_ctor_set(x_179, 1, x_177);
lean_inc(x_2);
x_180 = l___private_init_lean_elaborator_preterm_6__processBinders(x_165, x_2, x_179);
lean_dec(x_165);
if (lean_obj_tag(x_180) == 0)
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_181 = lean_ctor_get(x_180, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_180, 1);
lean_inc(x_182);
if (lean_is_exclusive(x_180)) {
 lean_ctor_release(x_180, 0);
 lean_ctor_release(x_180, 1);
 x_183 = x_180;
} else {
 lean_dec_ref(x_180);
 x_183 = lean_box(0);
}
if (lean_is_scalar(x_183)) {
 x_184 = lean_alloc_ctor(0, 2, 0);
} else {
 x_184 = x_183;
}
lean_ctor_set(x_184, 0, x_178);
lean_ctor_set(x_184, 1, x_182);
lean_inc(x_2);
x_185 = l_Lean_Elab_toPreTerm(x_167, x_2, x_184);
if (lean_obj_tag(x_185) == 0)
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_186 = lean_ctor_get(x_185, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_185, 1);
lean_inc(x_187);
if (lean_is_exclusive(x_185)) {
 lean_ctor_release(x_185, 0);
 lean_ctor_release(x_185, 1);
 x_188 = x_185;
} else {
 lean_dec_ref(x_185);
 x_188 = lean_box(0);
}
if (lean_is_scalar(x_188)) {
 x_189 = lean_alloc_ctor(0, 2, 0);
} else {
 x_189 = x_188;
}
lean_ctor_set(x_189, 0, x_178);
lean_ctor_set(x_189, 1, x_187);
x_190 = l_Lean_Elab_mkForall(x_181, x_186, x_2, x_189);
lean_dec(x_2);
if (lean_obj_tag(x_190) == 0)
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_191 = lean_ctor_get(x_190, 1);
lean_inc(x_191);
x_192 = lean_ctor_get(x_190, 0);
lean_inc(x_192);
if (lean_is_exclusive(x_190)) {
 lean_ctor_release(x_190, 0);
 lean_ctor_release(x_190, 1);
 x_193 = x_190;
} else {
 lean_dec_ref(x_190);
 x_193 = lean_box(0);
}
x_194 = lean_ctor_get(x_191, 0);
lean_inc(x_194);
x_195 = lean_ctor_get(x_191, 1);
lean_inc(x_195);
x_196 = lean_ctor_get(x_191, 2);
lean_inc(x_196);
x_197 = lean_ctor_get(x_191, 3);
lean_inc(x_197);
x_198 = lean_ctor_get(x_191, 4);
lean_inc(x_198);
x_199 = lean_ctor_get(x_191, 5);
lean_inc(x_199);
if (lean_is_exclusive(x_191)) {
 lean_ctor_release(x_191, 0);
 lean_ctor_release(x_191, 1);
 lean_ctor_release(x_191, 2);
 lean_ctor_release(x_191, 3);
 lean_ctor_release(x_191, 4);
 lean_ctor_release(x_191, 5);
 x_200 = x_191;
} else {
 lean_dec_ref(x_191);
 x_200 = lean_box(0);
}
x_201 = l_List_tail___rarg(x_199);
lean_dec(x_199);
if (lean_is_scalar(x_200)) {
 x_202 = lean_alloc_ctor(0, 6, 0);
} else {
 x_202 = x_200;
}
lean_ctor_set(x_202, 0, x_194);
lean_ctor_set(x_202, 1, x_195);
lean_ctor_set(x_202, 2, x_196);
lean_ctor_set(x_202, 3, x_197);
lean_ctor_set(x_202, 4, x_198);
lean_ctor_set(x_202, 5, x_201);
if (lean_is_scalar(x_193)) {
 x_203 = lean_alloc_ctor(0, 2, 0);
} else {
 x_203 = x_193;
}
lean_ctor_set(x_203, 0, x_192);
lean_ctor_set(x_203, 1, x_202);
return x_203;
}
else
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_204 = lean_ctor_get(x_190, 0);
lean_inc(x_204);
x_205 = lean_ctor_get(x_190, 1);
lean_inc(x_205);
if (lean_is_exclusive(x_190)) {
 lean_ctor_release(x_190, 0);
 lean_ctor_release(x_190, 1);
 x_206 = x_190;
} else {
 lean_dec_ref(x_190);
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
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; 
lean_dec(x_181);
lean_dec(x_2);
x_208 = lean_ctor_get(x_185, 0);
lean_inc(x_208);
x_209 = lean_ctor_get(x_185, 1);
lean_inc(x_209);
if (lean_is_exclusive(x_185)) {
 lean_ctor_release(x_185, 0);
 lean_ctor_release(x_185, 1);
 x_210 = x_185;
} else {
 lean_dec_ref(x_185);
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
else
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; 
lean_dec(x_167);
lean_dec(x_2);
x_212 = lean_ctor_get(x_180, 0);
lean_inc(x_212);
x_213 = lean_ctor_get(x_180, 1);
lean_inc(x_213);
if (lean_is_exclusive(x_180)) {
 lean_ctor_release(x_180, 0);
 lean_ctor_release(x_180, 1);
 x_214 = x_180;
} else {
 lean_dec_ref(x_180);
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
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_dec(x_3);
x_4 = l___private_init_lean_elaborator_preterm_3__mkHoleFor___closed__1;
lean_ctor_set(x_1, 0, x_4);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = l___private_init_lean_elaborator_preterm_3__mkHoleFor___closed__1;
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
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
x_3 = lean_expr_mk_const(x_2, x_1);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_convertSorry___rarg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_convertSorry___rarg___closed__3;
x_2 = l___private_init_lean_elaborator_preterm_3__mkHoleFor___closed__1;
x_3 = lean_expr_mk_app(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_convertSorry___rarg(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_dec(x_3);
x_4 = l_Lean_Elab_convertSorry___rarg___closed__4;
lean_ctor_set(x_1, 0, x_4);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = l_Lean_Elab_convertSorry___rarg___closed__4;
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
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
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = l_Lean_Elab_localContext___rarg(x_3);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
x_9 = lean_box(0);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_array_get(x_9, x_4, x_10);
x_12 = l_Lean_Syntax_getId___rarg(x_11);
lean_dec(x_11);
x_13 = lean_box(0);
lean_inc(x_8);
lean_ctor_set(x_5, 0, x_13);
lean_inc(x_12);
x_14 = lean_local_ctx_find_from_user_name(x_7, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_8);
x_15 = l_System_FilePath_dirName___closed__1;
x_16 = l_Lean_Name_toStringWithSep___main(x_15, x_12);
x_17 = l_Lean_Elab_convertId___closed__1;
x_18 = lean_string_append(x_17, x_16);
lean_dec(x_16);
x_19 = l_Char_HasRepr___closed__1;
x_20 = lean_string_append(x_18, x_19);
x_21 = l_Lean_Elab_logErrorAndThrow___rarg(x_1, x_20, x_2, x_5);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_5);
lean_dec(x_12);
x_22 = lean_ctor_get(x_14, 0);
lean_inc(x_22);
lean_dec(x_14);
x_23 = l___private_init_lean_elaborator_preterm_4__mkLocal(x_22);
lean_dec(x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_8);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_25 = lean_ctor_get(x_5, 0);
x_26 = lean_ctor_get(x_5, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_5);
x_27 = lean_box(0);
x_28 = lean_unsigned_to_nat(0u);
x_29 = lean_array_get(x_27, x_4, x_28);
x_30 = l_Lean_Syntax_getId___rarg(x_29);
lean_dec(x_29);
x_31 = lean_box(0);
lean_inc(x_26);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_26);
lean_inc(x_30);
x_33 = lean_local_ctx_find_from_user_name(x_25, x_30);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_26);
x_34 = l_System_FilePath_dirName___closed__1;
x_35 = l_Lean_Name_toStringWithSep___main(x_34, x_30);
x_36 = l_Lean_Elab_convertId___closed__1;
x_37 = lean_string_append(x_36, x_35);
lean_dec(x_35);
x_38 = l_Char_HasRepr___closed__1;
x_39 = lean_string_append(x_37, x_38);
x_40 = l_Lean_Elab_logErrorAndThrow___rarg(x_1, x_39, x_2, x_32);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_32);
lean_dec(x_30);
x_41 = lean_ctor_get(x_33, 0);
lean_inc(x_41);
lean_dec(x_33);
x_42 = l___private_init_lean_elaborator_preterm_4__mkLocal(x_41);
lean_dec(x_41);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_26);
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
return x_5;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_5, 0);
x_46 = lean_ctor_get(x_5, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_5);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
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
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_box(0);
lean_ctor_set(x_5, 0, x_8);
x_9 = l_Lean_Elab_getScope___rarg(x_5);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_ctor_set(x_9, 0, x_8);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
x_16 = lean_ctor_get(x_12, 2);
x_17 = lean_ctor_get(x_12, 3);
x_18 = lean_ctor_get(x_12, 4);
x_19 = lean_ctor_get(x_12, 5);
x_20 = lean_ctor_get(x_11, 2);
lean_inc(x_20);
x_21 = lean_ctor_get(x_11, 6);
lean_inc(x_21);
lean_dec(x_11);
x_22 = l_Lean_mkPreTypeAscriptionIfSome(x_7, x_2);
lean_inc(x_20);
x_23 = lean_old_elaborate(x_14, x_20, x_18, x_21, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; 
lean_free_object(x_12);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_Lean_Format_pretty(x_26, x_20);
lean_dec(x_20);
x_28 = l_Lean_Elab_logErrorAndThrow___rarg(x_1, x_27, x_3, x_9);
lean_dec(x_3);
lean_dec(x_1);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_1);
x_29 = lean_ctor_get(x_24, 1);
lean_inc(x_29);
lean_dec(x_24);
x_30 = lean_ctor_get(x_25, 0);
lean_inc(x_30);
lean_dec(x_25);
x_31 = lean_ctor_get(x_3, 0);
lean_inc(x_31);
x_32 = lean_box(0);
x_33 = l_Lean_Format_pretty(x_29, x_20);
lean_dec(x_20);
x_34 = 2;
x_35 = l_String_splitAux___main___closed__1;
x_36 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_36, 0, x_31);
lean_ctor_set(x_36, 1, x_30);
lean_ctor_set(x_36, 2, x_32);
lean_ctor_set(x_36, 3, x_35);
lean_ctor_set(x_36, 4, x_33);
lean_ctor_set_uint8(x_36, sizeof(void*)*5, x_34);
x_37 = l_Lean_Elab_logMessage(x_36, x_3, x_9);
lean_dec(x_3);
if (lean_obj_tag(x_37) == 0)
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_37, 0);
lean_dec(x_39);
x_40 = lean_box(4);
lean_ctor_set_tag(x_37, 1);
lean_ctor_set(x_37, 0, x_40);
return x_37;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_37, 1);
lean_inc(x_41);
lean_dec(x_37);
x_42 = lean_box(4);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_41);
return x_43;
}
}
else
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_37);
if (x_44 == 0)
{
return x_37;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_37, 0);
x_46 = lean_ctor_get(x_37, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_37);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_20);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_1);
x_48 = lean_ctor_get(x_23, 0);
lean_inc(x_48);
lean_dec(x_23);
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 0);
lean_inc(x_50);
lean_dec(x_48);
x_51 = lean_ctor_get(x_49, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_49, 1);
lean_inc(x_52);
lean_dec(x_49);
lean_ctor_set(x_12, 4, x_51);
lean_ctor_set(x_12, 0, x_50);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_12);
return x_53;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_54 = lean_ctor_get(x_12, 0);
x_55 = lean_ctor_get(x_12, 1);
x_56 = lean_ctor_get(x_12, 2);
x_57 = lean_ctor_get(x_12, 3);
x_58 = lean_ctor_get(x_12, 4);
x_59 = lean_ctor_get(x_12, 5);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_12);
x_60 = lean_ctor_get(x_11, 2);
lean_inc(x_60);
x_61 = lean_ctor_get(x_11, 6);
lean_inc(x_61);
lean_dec(x_11);
x_62 = l_Lean_mkPreTypeAscriptionIfSome(x_7, x_2);
lean_inc(x_60);
x_63 = lean_old_elaborate(x_54, x_60, x_58, x_61, x_62);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; 
lean_dec(x_59);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
lean_dec(x_63);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_67 = l_Lean_Format_pretty(x_66, x_60);
lean_dec(x_60);
x_68 = l_Lean_Elab_logErrorAndThrow___rarg(x_1, x_67, x_3, x_9);
lean_dec(x_3);
lean_dec(x_1);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_1);
x_69 = lean_ctor_get(x_64, 1);
lean_inc(x_69);
lean_dec(x_64);
x_70 = lean_ctor_get(x_65, 0);
lean_inc(x_70);
lean_dec(x_65);
x_71 = lean_ctor_get(x_3, 0);
lean_inc(x_71);
x_72 = lean_box(0);
x_73 = l_Lean_Format_pretty(x_69, x_60);
lean_dec(x_60);
x_74 = 2;
x_75 = l_String_splitAux___main___closed__1;
x_76 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_76, 0, x_71);
lean_ctor_set(x_76, 1, x_70);
lean_ctor_set(x_76, 2, x_72);
lean_ctor_set(x_76, 3, x_75);
lean_ctor_set(x_76, 4, x_73);
lean_ctor_set_uint8(x_76, sizeof(void*)*5, x_74);
x_77 = l_Lean_Elab_logMessage(x_76, x_3, x_9);
lean_dec(x_3);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
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
x_80 = lean_box(4);
if (lean_is_scalar(x_79)) {
 x_81 = lean_alloc_ctor(1, 2, 0);
} else {
 x_81 = x_79;
 lean_ctor_set_tag(x_81, 1);
}
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_78);
return x_81;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
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
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_dec(x_60);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_1);
x_86 = lean_ctor_get(x_63, 0);
lean_inc(x_86);
lean_dec(x_63);
x_87 = lean_ctor_get(x_86, 1);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 0);
lean_inc(x_88);
lean_dec(x_86);
x_89 = lean_ctor_get(x_87, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_87, 1);
lean_inc(x_90);
lean_dec(x_87);
x_91 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_91, 0, x_88);
lean_ctor_set(x_91, 1, x_55);
lean_ctor_set(x_91, 2, x_56);
lean_ctor_set(x_91, 3, x_57);
lean_ctor_set(x_91, 4, x_89);
lean_ctor_set(x_91, 5, x_59);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_93 = lean_ctor_get(x_9, 0);
x_94 = lean_ctor_get(x_9, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_9);
lean_inc(x_94);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_8);
lean_ctor_set(x_95, 1, x_94);
x_96 = lean_ctor_get(x_94, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_94, 1);
lean_inc(x_97);
x_98 = lean_ctor_get(x_94, 2);
lean_inc(x_98);
x_99 = lean_ctor_get(x_94, 3);
lean_inc(x_99);
x_100 = lean_ctor_get(x_94, 4);
lean_inc(x_100);
x_101 = lean_ctor_get(x_94, 5);
lean_inc(x_101);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 lean_ctor_release(x_94, 1);
 lean_ctor_release(x_94, 2);
 lean_ctor_release(x_94, 3);
 lean_ctor_release(x_94, 4);
 lean_ctor_release(x_94, 5);
 x_102 = x_94;
} else {
 lean_dec_ref(x_94);
 x_102 = lean_box(0);
}
x_103 = lean_ctor_get(x_93, 2);
lean_inc(x_103);
x_104 = lean_ctor_get(x_93, 6);
lean_inc(x_104);
lean_dec(x_93);
x_105 = l_Lean_mkPreTypeAscriptionIfSome(x_7, x_2);
lean_inc(x_103);
x_106 = lean_old_elaborate(x_96, x_103, x_100, x_104, x_105);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; lean_object* x_108; 
lean_dec(x_102);
lean_dec(x_101);
lean_dec(x_99);
lean_dec(x_98);
lean_dec(x_97);
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
lean_dec(x_106);
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
lean_dec(x_107);
x_110 = l_Lean_Format_pretty(x_109, x_103);
lean_dec(x_103);
x_111 = l_Lean_Elab_logErrorAndThrow___rarg(x_1, x_110, x_3, x_95);
lean_dec(x_3);
lean_dec(x_1);
return x_111;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
lean_dec(x_1);
x_112 = lean_ctor_get(x_107, 1);
lean_inc(x_112);
lean_dec(x_107);
x_113 = lean_ctor_get(x_108, 0);
lean_inc(x_113);
lean_dec(x_108);
x_114 = lean_ctor_get(x_3, 0);
lean_inc(x_114);
x_115 = lean_box(0);
x_116 = l_Lean_Format_pretty(x_112, x_103);
lean_dec(x_103);
x_117 = 2;
x_118 = l_String_splitAux___main___closed__1;
x_119 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_119, 0, x_114);
lean_ctor_set(x_119, 1, x_113);
lean_ctor_set(x_119, 2, x_115);
lean_ctor_set(x_119, 3, x_118);
lean_ctor_set(x_119, 4, x_116);
lean_ctor_set_uint8(x_119, sizeof(void*)*5, x_117);
x_120 = l_Lean_Elab_logMessage(x_119, x_3, x_95);
lean_dec(x_3);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_121 = lean_ctor_get(x_120, 1);
lean_inc(x_121);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 lean_ctor_release(x_120, 1);
 x_122 = x_120;
} else {
 lean_dec_ref(x_120);
 x_122 = lean_box(0);
}
x_123 = lean_box(4);
if (lean_is_scalar(x_122)) {
 x_124 = lean_alloc_ctor(1, 2, 0);
} else {
 x_124 = x_122;
 lean_ctor_set_tag(x_124, 1);
}
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_121);
return x_124;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_125 = lean_ctor_get(x_120, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_120, 1);
lean_inc(x_126);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 lean_ctor_release(x_120, 1);
 x_127 = x_120;
} else {
 lean_dec_ref(x_120);
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
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
lean_dec(x_103);
lean_dec(x_95);
lean_dec(x_3);
lean_dec(x_1);
x_129 = lean_ctor_get(x_106, 0);
lean_inc(x_129);
lean_dec(x_106);
x_130 = lean_ctor_get(x_129, 1);
lean_inc(x_130);
x_131 = lean_ctor_get(x_129, 0);
lean_inc(x_131);
lean_dec(x_129);
x_132 = lean_ctor_get(x_130, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_130, 1);
lean_inc(x_133);
lean_dec(x_130);
if (lean_is_scalar(x_102)) {
 x_134 = lean_alloc_ctor(0, 6, 0);
} else {
 x_134 = x_102;
}
lean_ctor_set(x_134, 0, x_131);
lean_ctor_set(x_134, 1, x_97);
lean_ctor_set(x_134, 2, x_98);
lean_ctor_set(x_134, 3, x_99);
lean_ctor_set(x_134, 4, x_132);
lean_ctor_set(x_134, 5, x_101);
x_135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_135, 0, x_133);
lean_ctor_set(x_135, 1, x_134);
return x_135;
}
}
}
else
{
uint8_t x_136; 
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_136 = !lean_is_exclusive(x_9);
if (x_136 == 0)
{
return x_9;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_137 = lean_ctor_get(x_9, 0);
x_138 = lean_ctor_get(x_9, 1);
lean_inc(x_138);
lean_inc(x_137);
lean_dec(x_9);
x_139 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_139, 0, x_137);
lean_ctor_set(x_139, 1, x_138);
return x_139;
}
}
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_140 = lean_ctor_get(x_5, 0);
x_141 = lean_ctor_get(x_5, 1);
lean_inc(x_141);
lean_inc(x_140);
lean_dec(x_5);
x_142 = lean_box(0);
x_143 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_143, 0, x_142);
lean_ctor_set(x_143, 1, x_141);
x_144 = l_Lean_Elab_getScope___rarg(x_143);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_144, 1);
lean_inc(x_146);
if (lean_is_exclusive(x_144)) {
 lean_ctor_release(x_144, 0);
 lean_ctor_release(x_144, 1);
 x_147 = x_144;
} else {
 lean_dec_ref(x_144);
 x_147 = lean_box(0);
}
lean_inc(x_146);
if (lean_is_scalar(x_147)) {
 x_148 = lean_alloc_ctor(0, 2, 0);
} else {
 x_148 = x_147;
}
lean_ctor_set(x_148, 0, x_142);
lean_ctor_set(x_148, 1, x_146);
x_149 = lean_ctor_get(x_146, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_146, 1);
lean_inc(x_150);
x_151 = lean_ctor_get(x_146, 2);
lean_inc(x_151);
x_152 = lean_ctor_get(x_146, 3);
lean_inc(x_152);
x_153 = lean_ctor_get(x_146, 4);
lean_inc(x_153);
x_154 = lean_ctor_get(x_146, 5);
lean_inc(x_154);
if (lean_is_exclusive(x_146)) {
 lean_ctor_release(x_146, 0);
 lean_ctor_release(x_146, 1);
 lean_ctor_release(x_146, 2);
 lean_ctor_release(x_146, 3);
 lean_ctor_release(x_146, 4);
 lean_ctor_release(x_146, 5);
 x_155 = x_146;
} else {
 lean_dec_ref(x_146);
 x_155 = lean_box(0);
}
x_156 = lean_ctor_get(x_145, 2);
lean_inc(x_156);
x_157 = lean_ctor_get(x_145, 6);
lean_inc(x_157);
lean_dec(x_145);
x_158 = l_Lean_mkPreTypeAscriptionIfSome(x_140, x_2);
lean_inc(x_156);
x_159 = lean_old_elaborate(x_149, x_156, x_153, x_157, x_158);
if (lean_obj_tag(x_159) == 0)
{
lean_object* x_160; lean_object* x_161; 
lean_dec(x_155);
lean_dec(x_154);
lean_dec(x_152);
lean_dec(x_151);
lean_dec(x_150);
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
lean_dec(x_159);
x_161 = lean_ctor_get(x_160, 0);
lean_inc(x_161);
if (lean_obj_tag(x_161) == 0)
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_162 = lean_ctor_get(x_160, 1);
lean_inc(x_162);
lean_dec(x_160);
x_163 = l_Lean_Format_pretty(x_162, x_156);
lean_dec(x_156);
x_164 = l_Lean_Elab_logErrorAndThrow___rarg(x_1, x_163, x_3, x_148);
lean_dec(x_3);
lean_dec(x_1);
return x_164;
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; uint8_t x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
lean_dec(x_1);
x_165 = lean_ctor_get(x_160, 1);
lean_inc(x_165);
lean_dec(x_160);
x_166 = lean_ctor_get(x_161, 0);
lean_inc(x_166);
lean_dec(x_161);
x_167 = lean_ctor_get(x_3, 0);
lean_inc(x_167);
x_168 = lean_box(0);
x_169 = l_Lean_Format_pretty(x_165, x_156);
lean_dec(x_156);
x_170 = 2;
x_171 = l_String_splitAux___main___closed__1;
x_172 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_172, 0, x_167);
lean_ctor_set(x_172, 1, x_166);
lean_ctor_set(x_172, 2, x_168);
lean_ctor_set(x_172, 3, x_171);
lean_ctor_set(x_172, 4, x_169);
lean_ctor_set_uint8(x_172, sizeof(void*)*5, x_170);
x_173 = l_Lean_Elab_logMessage(x_172, x_3, x_148);
lean_dec(x_3);
if (lean_obj_tag(x_173) == 0)
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_174 = lean_ctor_get(x_173, 1);
lean_inc(x_174);
if (lean_is_exclusive(x_173)) {
 lean_ctor_release(x_173, 0);
 lean_ctor_release(x_173, 1);
 x_175 = x_173;
} else {
 lean_dec_ref(x_173);
 x_175 = lean_box(0);
}
x_176 = lean_box(4);
if (lean_is_scalar(x_175)) {
 x_177 = lean_alloc_ctor(1, 2, 0);
} else {
 x_177 = x_175;
 lean_ctor_set_tag(x_177, 1);
}
lean_ctor_set(x_177, 0, x_176);
lean_ctor_set(x_177, 1, x_174);
return x_177;
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_178 = lean_ctor_get(x_173, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_173, 1);
lean_inc(x_179);
if (lean_is_exclusive(x_173)) {
 lean_ctor_release(x_173, 0);
 lean_ctor_release(x_173, 1);
 x_180 = x_173;
} else {
 lean_dec_ref(x_173);
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
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; 
lean_dec(x_156);
lean_dec(x_148);
lean_dec(x_3);
lean_dec(x_1);
x_182 = lean_ctor_get(x_159, 0);
lean_inc(x_182);
lean_dec(x_159);
x_183 = lean_ctor_get(x_182, 1);
lean_inc(x_183);
x_184 = lean_ctor_get(x_182, 0);
lean_inc(x_184);
lean_dec(x_182);
x_185 = lean_ctor_get(x_183, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_183, 1);
lean_inc(x_186);
lean_dec(x_183);
if (lean_is_scalar(x_155)) {
 x_187 = lean_alloc_ctor(0, 6, 0);
} else {
 x_187 = x_155;
}
lean_ctor_set(x_187, 0, x_184);
lean_ctor_set(x_187, 1, x_150);
lean_ctor_set(x_187, 2, x_151);
lean_ctor_set(x_187, 3, x_152);
lean_ctor_set(x_187, 4, x_185);
lean_ctor_set(x_187, 5, x_154);
x_188 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_188, 0, x_186);
lean_ctor_set(x_188, 1, x_187);
return x_188;
}
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; 
lean_dec(x_140);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_189 = lean_ctor_get(x_144, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_144, 1);
lean_inc(x_190);
if (lean_is_exclusive(x_144)) {
 lean_ctor_release(x_144, 0);
 lean_ctor_release(x_144, 1);
 x_191 = x_144;
} else {
 lean_dec_ref(x_144);
 x_191 = lean_box(0);
}
if (lean_is_scalar(x_191)) {
 x_192 = lean_alloc_ctor(1, 2, 0);
} else {
 x_192 = x_191;
}
lean_ctor_set(x_192, 0, x_189);
lean_ctor_set(x_192, 1, x_190);
return x_192;
}
}
}
else
{
uint8_t x_193; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_193 = !lean_is_exclusive(x_5);
if (x_193 == 0)
{
return x_5;
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_194 = lean_ctor_get(x_5, 0);
x_195 = lean_ctor_get(x_5, 1);
lean_inc(x_195);
lean_inc(x_194);
lean_dec(x_5);
x_196 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_196, 0, x_194);
lean_ctor_set(x_196, 1, x_195);
return x_196;
}
}
}
}
lean_object* initialize_init_lean_elaborator_basic(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_init_lean_elaborator_preterm(lean_object* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (lean_io_result_is_error(w)) return w;
w = initialize_init_lean_elaborator_basic(w);
if (lean_io_result_is_error(w)) return w;
l_Lean_mkBuiltinPreTermElabTable___closed__1 = _init_l_Lean_mkBuiltinPreTermElabTable___closed__1();
lean_mark_persistent(l_Lean_mkBuiltinPreTermElabTable___closed__1);
w = l_Lean_mkBuiltinPreTermElabTable(w);
if (lean_io_result_is_error(w)) return w;
l_Lean_builtinPreTermElabTable = lean_io_result_get_value(w);
lean_mark_persistent(l_Lean_builtinPreTermElabTable);
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
l_Lean_registerBuiltinPreTermElabAttr___lambda__1___closed__5 = _init_l_Lean_registerBuiltinPreTermElabAttr___lambda__1___closed__5();
lean_mark_persistent(l_Lean_registerBuiltinPreTermElabAttr___lambda__1___closed__5);
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
w = l_Lean_registerBuiltinPreTermElabAttr(w);
if (lean_io_result_is_error(w)) return w;
l_Lean_Expr_mkAnnotation___closed__1 = _init_l_Lean_Expr_mkAnnotation___closed__1();
lean_mark_persistent(l_Lean_Expr_mkAnnotation___closed__1);
l_Lean_Expr_mkAnnotation___closed__2 = _init_l_Lean_Expr_mkAnnotation___closed__2();
lean_mark_persistent(l_Lean_Expr_mkAnnotation___closed__2);
l___private_init_lean_elaborator_preterm_1__dummy___closed__1 = _init_l___private_init_lean_elaborator_preterm_1__dummy___closed__1();
lean_mark_persistent(l___private_init_lean_elaborator_preterm_1__dummy___closed__1);
l___private_init_lean_elaborator_preterm_1__dummy___closed__2 = _init_l___private_init_lean_elaborator_preterm_1__dummy___closed__2();
lean_mark_persistent(l___private_init_lean_elaborator_preterm_1__dummy___closed__2);
l___private_init_lean_elaborator_preterm_1__dummy = _init_l___private_init_lean_elaborator_preterm_1__dummy();
lean_mark_persistent(l___private_init_lean_elaborator_preterm_1__dummy);
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
l_Lean_Elab_toLevel___main___closed__4 = _init_l_Lean_Elab_toLevel___main___closed__4();
lean_mark_persistent(l_Lean_Elab_toLevel___main___closed__4);
l___private_init_lean_elaborator_preterm_2__setPos___closed__1 = _init_l___private_init_lean_elaborator_preterm_2__setPos___closed__1();
lean_mark_persistent(l___private_init_lean_elaborator_preterm_2__setPos___closed__1);
l___private_init_lean_elaborator_preterm_2__setPos___closed__2 = _init_l___private_init_lean_elaborator_preterm_2__setPos___closed__2();
lean_mark_persistent(l___private_init_lean_elaborator_preterm_2__setPos___closed__2);
l___private_init_lean_elaborator_preterm_2__setPos___closed__3 = _init_l___private_init_lean_elaborator_preterm_2__setPos___closed__3();
lean_mark_persistent(l___private_init_lean_elaborator_preterm_2__setPos___closed__3);
l___private_init_lean_elaborator_preterm_2__setPos___closed__4 = _init_l___private_init_lean_elaborator_preterm_2__setPos___closed__4();
lean_mark_persistent(l___private_init_lean_elaborator_preterm_2__setPos___closed__4);
l_Lean_Elab_toPreTerm___closed__1 = _init_l_Lean_Elab_toPreTerm___closed__1();
lean_mark_persistent(l_Lean_Elab_toPreTerm___closed__1);
l_Lean_Elab_toPreTerm___closed__2 = _init_l_Lean_Elab_toPreTerm___closed__2();
lean_mark_persistent(l_Lean_Elab_toPreTerm___closed__2);
l_Lean_Elab_toPreTerm___closed__3 = _init_l_Lean_Elab_toPreTerm___closed__3();
lean_mark_persistent(l_Lean_Elab_toPreTerm___closed__3);
l_Lean_Elab_toPreTerm___closed__4 = _init_l_Lean_Elab_toPreTerm___closed__4();
lean_mark_persistent(l_Lean_Elab_toPreTerm___closed__4);
l___private_init_lean_elaborator_preterm_3__mkHoleFor___closed__1 = _init_l___private_init_lean_elaborator_preterm_3__mkHoleFor___closed__1();
lean_mark_persistent(l___private_init_lean_elaborator_preterm_3__mkHoleFor___closed__1);
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
w = l___regBuiltinTermElab_Lean_Elab_convertType(w);
if (lean_io_result_is_error(w)) return w;
l___regBuiltinTermElab_Lean_Elab_convertSort___closed__1 = _init_l___regBuiltinTermElab_Lean_Elab_convertSort___closed__1();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_convertSort___closed__1);
l___regBuiltinTermElab_Lean_Elab_convertSort___closed__2 = _init_l___regBuiltinTermElab_Lean_Elab_convertSort___closed__2();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_convertSort___closed__2);
l___regBuiltinTermElab_Lean_Elab_convertSort___closed__3 = _init_l___regBuiltinTermElab_Lean_Elab_convertSort___closed__3();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_convertSort___closed__3);
w = l___regBuiltinTermElab_Lean_Elab_convertSort(w);
if (lean_io_result_is_error(w)) return w;
l___regBuiltinTermElab_Lean_Elab_convertProp___closed__1 = _init_l___regBuiltinTermElab_Lean_Elab_convertProp___closed__1();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_convertProp___closed__1);
l___regBuiltinTermElab_Lean_Elab_convertProp___closed__2 = _init_l___regBuiltinTermElab_Lean_Elab_convertProp___closed__2();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_convertProp___closed__2);
l___regBuiltinTermElab_Lean_Elab_convertProp___closed__3 = _init_l___regBuiltinTermElab_Lean_Elab_convertProp___closed__3();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_convertProp___closed__3);
w = l___regBuiltinTermElab_Lean_Elab_convertProp(w);
if (lean_io_result_is_error(w)) return w;
l___regBuiltinTermElab_Lean_Elab_convertSortApp___closed__1 = _init_l___regBuiltinTermElab_Lean_Elab_convertSortApp___closed__1();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_convertSortApp___closed__1);
l___regBuiltinTermElab_Lean_Elab_convertSortApp___closed__2 = _init_l___regBuiltinTermElab_Lean_Elab_convertSortApp___closed__2();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_convertSortApp___closed__2);
l___regBuiltinTermElab_Lean_Elab_convertSortApp___closed__3 = _init_l___regBuiltinTermElab_Lean_Elab_convertSortApp___closed__3();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_convertSortApp___closed__3);
w = l___regBuiltinTermElab_Lean_Elab_convertSortApp(w);
if (lean_io_result_is_error(w)) return w;
l_Array_ummapAux___main___at___private_init_lean_elaborator_preterm_5__processBinder___spec__1___closed__1 = _init_l_Array_ummapAux___main___at___private_init_lean_elaborator_preterm_5__processBinder___spec__1___closed__1();
lean_mark_persistent(l_Array_ummapAux___main___at___private_init_lean_elaborator_preterm_5__processBinder___spec__1___closed__1);
l_Array_ummapAux___main___at___private_init_lean_elaborator_preterm_5__processBinder___spec__1___closed__2 = _init_l_Array_ummapAux___main___at___private_init_lean_elaborator_preterm_5__processBinder___spec__1___closed__2();
lean_mark_persistent(l_Array_ummapAux___main___at___private_init_lean_elaborator_preterm_5__processBinder___spec__1___closed__2);
l_Array_ummapAux___main___at___private_init_lean_elaborator_preterm_5__processBinder___spec__1___closed__3 = _init_l_Array_ummapAux___main___at___private_init_lean_elaborator_preterm_5__processBinder___spec__1___closed__3();
lean_mark_persistent(l_Array_ummapAux___main___at___private_init_lean_elaborator_preterm_5__processBinder___spec__1___closed__3);
l_Array_ummapAux___main___at___private_init_lean_elaborator_preterm_5__processBinder___spec__1___closed__4 = _init_l_Array_ummapAux___main___at___private_init_lean_elaborator_preterm_5__processBinder___spec__1___closed__4();
lean_mark_persistent(l_Array_ummapAux___main___at___private_init_lean_elaborator_preterm_5__processBinder___spec__1___closed__4);
l_Array_ummapAux___main___at___private_init_lean_elaborator_preterm_5__processBinder___spec__1___closed__5 = _init_l_Array_ummapAux___main___at___private_init_lean_elaborator_preterm_5__processBinder___spec__1___closed__5();
lean_mark_persistent(l_Array_ummapAux___main___at___private_init_lean_elaborator_preterm_5__processBinder___spec__1___closed__5);
l_Array_ummapAux___main___at___private_init_lean_elaborator_preterm_5__processBinder___spec__1___closed__6 = _init_l_Array_ummapAux___main___at___private_init_lean_elaborator_preterm_5__processBinder___spec__1___closed__6();
lean_mark_persistent(l_Array_ummapAux___main___at___private_init_lean_elaborator_preterm_5__processBinder___spec__1___closed__6);
l___private_init_lean_elaborator_preterm_5__processBinder___closed__1 = _init_l___private_init_lean_elaborator_preterm_5__processBinder___closed__1();
lean_mark_persistent(l___private_init_lean_elaborator_preterm_5__processBinder___closed__1);
l___private_init_lean_elaborator_preterm_5__processBinder___closed__2 = _init_l___private_init_lean_elaborator_preterm_5__processBinder___closed__2();
lean_mark_persistent(l___private_init_lean_elaborator_preterm_5__processBinder___closed__2);
l___private_init_lean_elaborator_preterm_5__processBinder___closed__3 = _init_l___private_init_lean_elaborator_preterm_5__processBinder___closed__3();
lean_mark_persistent(l___private_init_lean_elaborator_preterm_5__processBinder___closed__3);
l___private_init_lean_elaborator_preterm_5__processBinder___closed__4 = _init_l___private_init_lean_elaborator_preterm_5__processBinder___closed__4();
lean_mark_persistent(l___private_init_lean_elaborator_preterm_5__processBinder___closed__4);
l___regBuiltinTermElab_Lean_Elab_convertForall___closed__1 = _init_l___regBuiltinTermElab_Lean_Elab_convertForall___closed__1();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_convertForall___closed__1);
l___regBuiltinTermElab_Lean_Elab_convertForall___closed__2 = _init_l___regBuiltinTermElab_Lean_Elab_convertForall___closed__2();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_convertForall___closed__2);
l___regBuiltinTermElab_Lean_Elab_convertForall___closed__3 = _init_l___regBuiltinTermElab_Lean_Elab_convertForall___closed__3();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_convertForall___closed__3);
w = l___regBuiltinTermElab_Lean_Elab_convertForall(w);
if (lean_io_result_is_error(w)) return w;
l___regBuiltinTermElab_Lean_Elab_convertHole___closed__1 = _init_l___regBuiltinTermElab_Lean_Elab_convertHole___closed__1();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_convertHole___closed__1);
l___regBuiltinTermElab_Lean_Elab_convertHole___closed__2 = _init_l___regBuiltinTermElab_Lean_Elab_convertHole___closed__2();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_convertHole___closed__2);
l___regBuiltinTermElab_Lean_Elab_convertHole___closed__3 = _init_l___regBuiltinTermElab_Lean_Elab_convertHole___closed__3();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_convertHole___closed__3);
w = l___regBuiltinTermElab_Lean_Elab_convertHole(w);
if (lean_io_result_is_error(w)) return w;
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
w = l___regBuiltinTermElab_Lean_Elab_convertSorry(w);
if (lean_io_result_is_error(w)) return w;
l_Lean_Elab_convertId___closed__1 = _init_l_Lean_Elab_convertId___closed__1();
lean_mark_persistent(l_Lean_Elab_convertId___closed__1);
l___regBuiltinTermElab_Lean_Elab_convertId___closed__1 = _init_l___regBuiltinTermElab_Lean_Elab_convertId___closed__1();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_convertId___closed__1);
l___regBuiltinTermElab_Lean_Elab_convertId___closed__2 = _init_l___regBuiltinTermElab_Lean_Elab_convertId___closed__2();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_convertId___closed__2);
l___regBuiltinTermElab_Lean_Elab_convertId___closed__3 = _init_l___regBuiltinTermElab_Lean_Elab_convertId___closed__3();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_convertId___closed__3);
w = l___regBuiltinTermElab_Lean_Elab_convertId(w);
if (lean_io_result_is_error(w)) return w;
return w;
}
#ifdef __cplusplus
}
#endif
