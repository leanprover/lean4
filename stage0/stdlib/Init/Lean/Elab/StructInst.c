// Lean compiler output
// Module: Init.Lean.Elab.StructInst
// Imports: Init.Lean.Elab.App Init.Lean.Elab.Binders Init.Lean.Elab.Quotation
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
lean_object* l_Lean_Elab_Term_StructInst_formatStruct___main(lean_object*);
lean_object* l___private_Init_Lean_Elab_StructInst_17__groupFields(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_Struct_modifyFields(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getEnv___rarg(lean_object*);
extern lean_object* l_Lean_Name_toString___closed__1;
lean_object* l___private_Init_Lean_Elab_StructInst_12__mkFieldMap___closed__1;
lean_object* l___private_Init_Lean_Elab_StructInst_17__groupFields___lambda__3___closed__2;
lean_object* l_List_map___main___at___private_Init_Lean_Elab_StructInst_10__expandParentFields___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_Source_hasFormat(lean_object*);
lean_object* l_List_tail_x21___rarg(lean_object*);
lean_object* l___private_Init_Lean_Elab_StructInst_2__getStructSource(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_isNatLitAux(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_Struct_modifyFieldsM(lean_object*);
extern lean_object* l_Lean_Parser_declareBuiltinParser___closed__8;
lean_object* l_List_foldlM___main___at___private_Init_Lean_Elab_StructInst_12__mkFieldMap___spec__10(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t l_AssocList_contains___main___at___private_Init_Lean_Elab_StructInst_12__mkFieldMap___spec__4(lean_object*, lean_object*);
lean_object* l_List_foldlM___main___at___private_Init_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__6;
lean_object* l_HashMap_toList___rarg(lean_object*);
lean_object* l___private_Init_Lean_Elab_StructInst_17__groupFields___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_Source_addSyntax(lean_object*, lean_object*);
lean_object* l_unreachable_x21___rarg(lean_object*);
extern lean_object* l_Lean_nullKind;
lean_object* l_Array_foldlStepMAux___main___at___private_Init_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__3;
lean_object* l___private_Init_Lean_Elab_StructInst_1__expandNonAtomicExplicitSource___closed__1;
lean_object* l_List_mapM___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_MessageData_ofList___closed__3;
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Array_foldlStepMAux___main___at___private_Init_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Format_joinSep___main___at_Lean_Elab_Term_StructInst_formatField___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_inferType(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_HashMapImp_find_x3f___at___private_Init_Lean_Elab_StructInst_12__mkFieldMap___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Array_foldlStepMAux___main___at___private_Init_Lean_Elab_StructInst_2__getStructSource___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__1;
lean_object* l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_10__expandParentFields___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Format_pretty(lean_object*, lean_object*);
extern lean_object* l_Lean_List_format___rarg___closed__2;
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Array_foldlStepMAux___main___at___private_Init_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__5;
lean_object* l_List_head_x21___at___private_Init_Lean_Elab_StructInst_18__expandStruct___main___spec__3___boxed(lean_object*);
extern lean_object* l_Option_get_x21___rarg___closed__3;
lean_object* l___private_Init_Lean_Elab_StructInst_17__groupFields___at___private_Init_Lean_Elab_StructInst_18__expandStruct___main___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_StructInst_16__mkSubstructSource(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_Struct_hasToString;
lean_object* l_Lean_Syntax_getIdAt(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__7;
extern lean_object* l_Lean_Parser_Term_structInstArrayRef___elambda__1___closed__2;
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_StructInst_18__expandStruct(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_Elab_StructInst_18__expandStruct___main___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_StructInst_13__isSimpleField_x3f(lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_StructInst_elabStructInst___closed__5;
extern lean_object* l_Lean_Parser_Term_structInst___elambda__1___closed__6;
lean_object* l___private_Init_Lean_Elab_StructInst_10__expandParentFields(lean_object*, lean_object*, lean_object*);
lean_object* l_List_append___rarg(lean_object*, lean_object*);
lean_object* l_mkHashMap___at___private_Init_Lean_Elab_StructInst_12__mkFieldMap___spec__9(lean_object*);
lean_object* l_List_foldlM___main___at___private_Init_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__3;
lean_object* l_Lean_fmt___at_Lean_Elab_Term_StructInst_formatStruct___main___spec__2(lean_object*);
lean_object* l_Array_foldlStepMAux___main___at___private_Init_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__6;
lean_object* l_Lean_Elab_Term_StructInst_FieldLHS_inhabited___closed__1;
lean_object* l_Lean_Format_joinSep___main___at___private_Init_Lean_Data_Trie_6__toStringAux___main___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*);
lean_object* l_List_map___main___at___private_Init_Lean_Elab_StructInst_7__mkStructView___spec__2(lean_object*);
lean_object* l_List_foldlM___main___at___private_Init_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__5;
lean_object* l_Lean_Elab_Term_StructInst_Struct_ref(lean_object*);
lean_object* l___private_Init_Lean_Elab_StructInst_4__elabModifyOp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
extern lean_object* l___private_Init_Lean_Elab_Quotation_5__quoteSyntax___main___closed__1;
lean_object* lean_array_get_size(lean_object*);
lean_object* l_List_map___main___rarg(lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_StructInst_ExpandNonAtomicExplicitSource_main___spec__1___closed__6;
lean_object* l_HashMap_toList___at___private_Init_Lean_Elab_StructInst_18__expandStruct___main___spec__6(lean_object*);
lean_object* l_Lean_Expr_getAppFn___main(lean_object*);
extern lean_object* l_Lean_formatKVMap___closed__1;
extern lean_object* l_Lean_Name_inhabited;
lean_object* l___private_Init_Lean_Elab_StructInst_8__expandCompositeFields(lean_object*);
lean_object* l___private_Init_Lean_Elab_StructInst_5__getStructName___closed__3;
lean_object* l_Lean_Elab_Term_StructInst_formatField(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_StructInst_17__groupFields___lambda__1(lean_object*);
lean_object* l___private_Init_Lean_Elab_StructInst_17__groupFields___lambda__3___closed__3;
lean_object* l_Lean_Elab_Term_StructInst_Field_hasFormat___closed__1;
lean_object* l_Lean_Elab_Term_StructInst_formatStruct___main___closed__1;
extern lean_object* l_Id_monad;
lean_object* l_Lean_Elab_Term_StructInst_ExpandNonAtomicExplicitSource_main(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_StructInst_ExpandNonAtomicExplicitSource_main___spec__1___closed__3;
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_List_head_x21___rarg(lean_object*, lean_object*);
lean_object* l_AssocList_contains___main___at___private_Init_Lean_Elab_StructInst_12__mkFieldMap___spec__4___boxed(lean_object*, lean_object*);
lean_object* l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__6;
lean_object* l_Lean_Elab_Term_getMainModule___rarg(lean_object*);
lean_object* l___private_Init_Lean_Elab_StructInst_6__toFieldLHS(lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_StructInst_elabStructInst(lean_object*);
lean_object* l_List_map___main___at___private_Init_Lean_Elab_StructInst_18__expandStruct___main___spec__2(lean_object*);
lean_object* l_Lean_fmt___at_Lean_Level_LevelToFormat_toResult___main___spec__1(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_Field_isSimple___rarg___boxed(lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_Source_hasFormat___closed__3;
extern lean_object* l_Lean_Format_sbracket___closed__2;
lean_object* l_HashMapImp_insert___at___private_Init_Lean_Elab_StructInst_12__mkFieldMap___spec__3(lean_object*, lean_object*, lean_object*);
extern lean_object* l_PersistentHashMap_Stats_toString___closed__5;
lean_object* l_Lean_Elab_Term_whnf(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_FieldLHS_toSyntax___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_FieldLHS_hasFormat(lean_object*);
extern lean_object* l_Lean_mkTermIdFromIdent___closed__2;
extern lean_object* l_Array_forMAux___main___at_Lean_Meta_clear___spec__5___closed__8;
lean_object* l_Lean_Elab_Term_StructInst_Source_isNone___boxed(lean_object*);
lean_object* l___private_Init_Lean_Elab_StructInst_4__elabModifyOp___closed__1;
extern lean_object* l_Lean_Parser_Term_proj___elambda__1___closed__2;
lean_object* l_Lean_Elab_Term_StructInst_Struct_structName(lean_object*);
lean_object* l___private_Init_Lean_Elab_StructInst_19__elabStructInstAux___closed__10;
lean_object* l_List_head_x21___at___private_Init_Lean_Elab_StructInst_18__expandStruct___main___spec__3(lean_object*);
lean_object* l_List_foldlM___main___at___private_Init_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__1;
lean_object* l_Lean_Elab_Term_tryPostponeIfNoneOrMVar(lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__5;
lean_object* lean_array_fget(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_declareBuiltinTermElab___closed__3;
lean_object* l_Lean_mkProj(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_List_map___main___at___private_Init_Lean_Elab_StructInst_8__expandCompositeFields___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_FieldVal_toSyntax___boxed(lean_object*);
lean_object* l___private_Init_Lean_Elab_StructInst_15__mkProjStx(lean_object*, lean_object*);
lean_object* l_Array_findIdxAux___main___at___private_Init_Lean_Elab_StructInst_14__getFieldIdx___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_AssocList_foldlM___main___at___private_Init_Lean_Elab_StructInst_18__expandStruct___main___spec__7___boxed(lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Elab_StructInst_18__expandStruct___main___spec__4(lean_object*, lean_object*);
lean_object* l_Array_findIdxAux___main___at___private_Init_Lean_Elab_StructInst_14__getFieldIdx___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_9__expandNumLitFields___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_StructInst_4__elabModifyOp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_numLitKind;
lean_object* l___private_Init_Lean_Elab_StructInst_14__getFieldIdx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__6;
lean_object* l___private_Init_Lean_Elab_StructInst_14__getFieldIdx___closed__3;
lean_object* l_HashMap_toList___at___private_Init_Lean_Elab_StructInst_18__expandStruct___main___spec__6___boxed(lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_formatStruct(lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_Field_isSimple(lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_Struct_fields___boxed(lean_object*);
lean_object* l_Array_shrink___main___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_FieldLHS_toSyntax(uint8_t, lean_object*);
lean_object* l_Lean_Elab_Term_elabTerm(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_StructInst_4__elabModifyOp___closed__2;
lean_object* l___private_Init_Lean_Elab_StructInst_13__isSimpleField_x3f___boxed(lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_StructInst_ExpandNonAtomicExplicitSource_main___spec__1___closed__5;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_AssocList_foldlM___main___at___private_Init_Lean_Elab_StructInst_12__mkFieldMap___spec__7(lean_object*, lean_object*);
lean_object* l_List_foldlM___main___at___private_Init_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__2;
lean_object* l___private_Init_Lean_Elab_StructInst_14__getFieldIdx___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_formatEntry___closed__2;
lean_object* l___private_Init_Lean_Elab_StructInst_4__elabModifyOp___closed__3;
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_Elab_StructInst_18__expandStruct___main___spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_AssocList_find___main___at___private_Init_Lean_Elab_StructInst_12__mkFieldMap___spec__2(lean_object*, lean_object*);
lean_object* l_HashMapImp_find_x3f___at___private_Init_Lean_Elab_StructInst_12__mkFieldMap___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_Field_inhabited(lean_object*);
extern lean_object* l_Lean_Format_join___closed__1;
lean_object* l___private_Init_Lean_Elab_StructInst_14__getFieldIdx___closed__1;
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_StructInst_Field_toSyntax___spec__1(lean_object*, lean_object*);
extern lean_object* l___private_Init_Lean_Elab_Quotation_7__getHeadInfo___elambda__3___closed__2;
size_t l_Lean_Name_hash(lean_object*);
lean_object* l_Nat_repr(lean_object*);
lean_object* l___private_Init_Lean_Elab_StructInst_14__getFieldIdx___closed__2;
lean_object* l_List_head_x21___at___private_Init_Lean_Elab_StructInst_18__expandStruct___main___spec__5(lean_object*);
lean_object* l___private_Init_Lean_Elab_StructInst_19__elabStructInstAux___closed__7;
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l_Lean_Syntax_prettyPrint(lean_object*);
lean_object* l_List_map___main___at___private_Init_Lean_Elab_StructInst_8__expandCompositeFields___spec__2(lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__3;
lean_object* l_Lean_Elab_Term_throwError___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_StructInst_17__groupFields___lambda__2(lean_object*, lean_object*);
lean_object* l_Lean_fmt___at_Lean_Level_LevelToFormat_Result_format___main___spec__1(lean_object*);
lean_object* l_Lean_getStructureFields(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_StructInst_5__getStructName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Function_comp___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getCurrMacroScope(lean_object*, lean_object*);
extern lean_object* l___private_Init_Lean_Elab_Quotation_7__getHeadInfo___elambda__3___closed__4;
lean_object* l_Lean_Elab_Term_StructInst_Struct_hasFormat___closed__1;
extern lean_object* l_Lean_Options_empty;
lean_object* lean_expr_dbg_to_string(lean_object*);
lean_object* l___private_Init_Lean_Elab_StructInst_16__mkSubstructSource___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getPathToBaseStructure_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_StructInst_12__mkFieldMap(lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__8;
size_t lean_usize_modn(size_t, lean_object*);
lean_object* l_AssocList_foldlM___main___at___private_Init_Lean_Elab_StructInst_18__expandStruct___main___spec__7(lean_object*, lean_object*);
lean_object* l_Lean_fmt___at_Lean_Elab_Term_StructInst_formatStruct___main___spec__2___boxed(lean_object*);
extern lean_object* l_List_head_x21___rarg___closed__2;
lean_object* l_Lean_Elab_Term_StructInst_elabStructInst___closed__1;
extern lean_object* l_Lean_Parser_Term_structInst___elambda__1___closed__2;
extern lean_object* l_Lean_Parser_Term_let___elambda__1___closed__2;
lean_object* l_List_redLength___main___rarg(lean_object*);
lean_object* l_mkHashMapImp___rarg(lean_object*);
lean_object* l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__1;
lean_object* l___private_Init_Lean_Elab_StructInst_9__expandNumLitFields___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__2;
uint8_t l_Lean_Elab_Term_StructInst_Field_isSimple___rarg(lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_Struct_fields(lean_object*);
lean_object* l___private_Init_Lean_Elab_StructInst_19__elabStructInstAux___closed__5;
lean_object* l___private_Init_Lean_Elab_StructInst_7__mkStructView(lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_Struct_structName___boxed(lean_object*);
lean_object* l_List_foldlM___main___at___private_Init_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__4;
extern lean_object* l_Lean_Parser_Term_structInstField___elambda__1___closed__2;
lean_object* l___private_Init_Lean_Elab_StructInst_2__getStructSource___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_StructInst_8__expandCompositeFields___closed__1;
lean_object* l_HashMapImp_expand___at___private_Init_Lean_Elab_StructInst_12__mkFieldMap___spec__5(lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_StructInst_ExpandNonAtomicExplicitSource_main___spec__1___closed__4;
lean_object* l_Lean_mkSepStx(lean_object*, lean_object*);
extern lean_object* l_Lean_Format_sbracket___closed__3;
lean_object* l_List_map___main___at_Lean_Elab_Term_StructInst_formatStruct___main___spec__1(lean_object*);
lean_object* l_Lean_mkAtomFrom(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_StructInst_9__expandNumLitFields(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_FieldLHS_inhabited;
lean_object* l___private_Init_Lean_Elab_StructInst_19__elabStructInstAux___closed__3;
lean_object* l_Array_umapMAux___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_HasRepr___closed__1;
lean_object* l_Lean_Elab_Term_StructInst_Field_hasToString;
lean_object* l_List_head_x21___at___private_Init_Lean_Elab_StructInst_18__expandStruct___main___spec__5___boxed(lean_object*);
lean_object* l_Array_foldlStepMAux___main___at___private_Init_Lean_Elab_StructInst_2__getStructSource___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__4;
extern lean_object* l_Lean_Syntax_inhabited;
lean_object* l___private_Init_Lean_Elab_StructInst_17__groupFields___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_StructInst_3__isModifyOp_x3f___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_Source_hasFormat___boxed(lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_formatField___closed__1;
lean_object* l_List_map___main___at___private_Init_Lean_Elab_StructInst_7__mkStructView___spec__3(lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_Source_hasFormat___closed__1;
lean_object* l_Lean_Syntax_setArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_Struct_modifyFieldsM___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_Source_hasFormat___closed__4;
lean_object* l_AssocList_find___main___at___private_Init_Lean_Elab_StructInst_12__mkFieldMap___spec__2___boxed(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_Struct_source___boxed(lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_Source_hasFormat___closed__2;
lean_object* l___private_Init_Lean_Elab_StructInst_3__isModifyOp_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_Struct_modifyFieldsM___at___private_Init_Lean_Elab_StructInst_9__expandNumLitFields___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_StructInst_19__elabStructInstAux___closed__6;
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_Struct_ref___boxed(lean_object*);
extern lean_object* l_Lean_getBuiltinSearchPath___closed__2;
lean_object* l_Lean_Elab_Term_StructInst_Struct_modifyFieldsM___at_Lean_Elab_Term_StructInst_Struct_modifyFields___spec__1(lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_StructInst_elabStructInst___closed__4;
lean_object* l_Array_foldlStepMAux___main___at___private_Init_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_tryPostponeIfMVar(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_Struct_source(lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_Struct_hasToString___closed__1;
lean_object* l___private_Init_Lean_Elab_StructInst_19__elabStructInstAux___closed__1;
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_StructInst_ExpandNonAtomicExplicitSource_main___spec__1___closed__1;
lean_object* l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__5;
extern lean_object* l_Lean_Parser_Term_letIdDecl___closed__2;
lean_object* l_Array_foldlStepMAux___main___at___private_Init_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__1;
extern lean_object* l_Lean_mkAppStx___closed__9;
lean_object* l___private_Init_Lean_Elab_StructInst_19__elabStructInstAux___closed__2;
uint8_t l_Lean_Syntax_isNone(lean_object*);
extern lean_object* l___private_Init_Lean_Elab_Quotation_7__getHeadInfo___elambda__3___closed__10;
extern lean_object* l_Lean_mkOptionalNode___closed__1;
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_StructInst_elabStructInst___closed__2;
lean_object* l___private_Init_Lean_Elab_StructInst_18__expandStruct___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_elabStructInst___closed__3;
lean_object* l___private_Init_Lean_Elab_StructInst_5__getStructName___closed__5;
lean_object* l_Array_foldlStepMAux___main___at___private_Init_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__2;
lean_object* l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_10__expandParentFields___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_StructInst_elabStructInst___closed__1;
lean_object* l_Array_toList___rarg(lean_object*);
extern lean_object* l_Lean_Expr_Inhabited;
lean_object* l_Lean_Elab_Term_addBuiltinTermElab(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_isSubobjectField_x3f(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_StructInst_9__expandNumLitFields___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_Struct_modifyFieldsM___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_StructInst_5__getStructName___closed__6;
uint8_t l_Lean_Elab_Term_StructInst_Source_isNone(lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_Struct_hasFormat;
lean_object* l___private_Init_Lean_Elab_StructInst_17__groupFields___at___private_Init_Lean_Elab_StructInst_18__expandStruct___main___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___main___at_Lean_Elab_Term_StructInst_formatStruct___main___spec__1___closed__1;
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_StructInst_elabStructInst___closed__3;
lean_object* l_Lean_Elab_Term_StructInst_Field_hasToString___closed__1;
lean_object* l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_18__expandStruct___main___spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_StructInst_ExpandNonAtomicExplicitSource_main___spec__1___closed__2;
lean_object* l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__3;
lean_object* l_Array_filterAux___main___at___private_Init_Lean_Elab_StructInst_7__mkStructView___spec__1(lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__4;
extern lean_object* l_Lean_Parser_Term_structInstSource___elambda__1___closed__2;
lean_object* l_Lean_Elab_Term_StructInst_Field_inhabited___closed__1;
lean_object* l_List_toArrayAux___main___rarg(lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_StructInst_ExpandNonAtomicExplicitSource_main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_StructInst_19__elabStructInstAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_Field_hasFormat;
lean_object* l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__9;
lean_object* l___private_Init_Lean_Elab_StructInst_5__getStructName___closed__1;
lean_object* l_Lean_Elab_Term_StructInst_Field_inhabited___closed__2;
uint8_t l_Lean_isStructureLike(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_StructInst_5__getStructName___closed__2;
lean_object* l_Lean_Elab_Term_isLocalTermId_x3f(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l___private_Init_Lean_Elab_StructInst_19__elabStructInstAux___closed__9;
lean_object* l___private_Init_Lean_Elab_StructInst_1__expandNonAtomicExplicitSource(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_Field_toSyntax(lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_formatStruct___main___closed__2;
lean_object* l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__2;
lean_object* l_Array_foldlStepMAux___main___at___private_Init_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__4;
lean_object* l_Lean_Elab_Term_StructInst_FieldVal_toSyntax(lean_object*);
lean_object* l_Lean_findField_x3f___main(lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_18__expandStruct___main___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__4;
lean_object* l_Lean_Name_components(lean_object*);
lean_object* l___private_Init_Lean_Elab_StructInst_5__getStructName___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_HashMapImp_moveEntries___main___at___private_Init_Lean_Elab_StructInst_12__mkFieldMap___spec__6(lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__9;
lean_object* l___private_Init_Lean_Elab_StructInst_17__groupFields___lambda__2___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_StructInst_5__getStructName___closed__4;
extern lean_object* l_addParenHeuristic___closed__1;
lean_object* l_Lean_Elab_Term_StructInst_elabStructInst___closed__2;
extern lean_object* l_Lean_MetavarContext_MkBinding_mkBinding___closed__1;
lean_object* l___private_Init_Lean_Elab_StructInst_17__groupFields___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_StructInst_17__groupFields___lambda__3___closed__1;
lean_object* l___private_Init_Lean_Elab_StructInst_19__elabStructInstAux___closed__4;
lean_object* l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__7;
lean_object* l___private_Init_Lean_Elab_StructInst_19__elabStructInstAux___closed__8;
lean_object* l_AssocList_replace___main___at___private_Init_Lean_Elab_StructInst_12__mkFieldMap___spec__8(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_elabStructInst(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_StructInst_17__groupFields___at___private_Init_Lean_Elab_StructInst_18__expandStruct___main___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__8;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isIdent(lean_object*);
lean_object* _init_l_Array_umapMAux___main___at_Lean_Elab_Term_StructInst_ExpandNonAtomicExplicitSource_main___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_getBuiltinSearchPath___closed__2;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
lean_object* _init_l_Array_umapMAux___main___at_Lean_Elab_Term_StructInst_ExpandNonAtomicExplicitSource_main___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_getBuiltinSearchPath___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Array_umapMAux___main___at_Lean_Elab_Term_StructInst_ExpandNonAtomicExplicitSource_main___spec__1___closed__1;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* _init_l_Array_umapMAux___main___at_Lean_Elab_Term_StructInst_ExpandNonAtomicExplicitSource_main___spec__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_getBuiltinSearchPath___closed__2;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Array_umapMAux___main___at_Lean_Elab_Term_StructInst_ExpandNonAtomicExplicitSource_main___spec__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("source has already been specified");
return x_1;
}
}
lean_object* _init_l_Array_umapMAux___main___at_Lean_Elab_Term_StructInst_ExpandNonAtomicExplicitSource_main___spec__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_umapMAux___main___at_Lean_Elab_Term_StructInst_ExpandNonAtomicExplicitSource_main___spec__1___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Array_umapMAux___main___at_Lean_Elab_Term_StructInst_ExpandNonAtomicExplicitSource_main___spec__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_umapMAux___main___at_Lean_Elab_Term_StructInst_ExpandNonAtomicExplicitSource_main___spec__1___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_StructInst_ExpandNonAtomicExplicitSource_main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_2);
x_7 = lean_nat_dec_lt(x_1, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_4);
lean_dec(x_1);
x_8 = l_Array_empty___closed__1;
x_9 = x_2;
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_3);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_5);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_12 = lean_array_fget(x_2, x_1);
x_13 = lean_box(0);
x_14 = x_13;
x_15 = lean_array_fset(x_2, x_1, x_14);
lean_inc(x_12);
x_26 = l_Lean_Syntax_getKind(x_12);
x_27 = l_Lean_Parser_Term_structInstSource___elambda__1___closed__2;
x_28 = lean_name_eq(x_26, x_27);
lean_dec(x_26);
if (x_28 == 0)
{
lean_object* x_29; 
lean_inc(x_12);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_12);
lean_ctor_set(x_29, 1, x_3);
x_16 = x_29;
x_17 = x_5;
goto block_25;
}
else
{
uint8_t x_30; 
x_30 = lean_ctor_get_uint8(x_3, sizeof(void*)*1);
if (x_30 == 0)
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_3);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_32 = lean_ctor_get(x_3, 0);
x_33 = lean_unsigned_to_nat(1u);
x_34 = l_Lean_Syntax_getArg(x_12, x_33);
x_35 = l_Lean_Syntax_isNone(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; 
x_36 = lean_unsigned_to_nat(0u);
x_37 = l_Lean_Syntax_getArg(x_34, x_36);
x_38 = 0;
lean_inc(x_37);
x_39 = l_Lean_Elab_Term_isLocalTermId_x3f(x_37, x_38, x_4, x_5);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_32);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = l_Lean_Elab_Term_getCurrMacroScope(x_4, x_41);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = l_Lean_Elab_Term_getMainModule___rarg(x_44);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = lean_box(0);
x_49 = l_Array_umapMAux___main___at_Lean_Elab_Term_StructInst_ExpandNonAtomicExplicitSource_main___spec__1___closed__3;
x_50 = l_Lean_addMacroScope(x_46, x_49, x_43);
x_51 = lean_box(0);
x_52 = l_Array_umapMAux___main___at_Lean_Elab_Term_StructInst_ExpandNonAtomicExplicitSource_main___spec__1___closed__2;
x_53 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_53, 0, x_48);
lean_ctor_set(x_53, 1, x_52);
lean_ctor_set(x_53, 2, x_50);
lean_ctor_set(x_53, 3, x_51);
x_54 = l_Array_empty___closed__1;
x_55 = lean_array_push(x_54, x_53);
x_56 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_57 = lean_array_push(x_55, x_56);
x_58 = l_Lean_mkTermIdFromIdent___closed__2;
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_57);
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_37);
x_61 = 1;
lean_ctor_set(x_3, 0, x_60);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_61);
x_62 = l_Lean_Syntax_setArg(x_34, x_36, x_59);
lean_inc(x_12);
x_63 = l_Lean_Syntax_setArg(x_12, x_33, x_62);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_3);
x_16 = x_64;
x_17 = x_47;
goto block_25;
}
else
{
lean_object* x_65; uint8_t x_66; lean_object* x_67; 
lean_dec(x_40);
lean_dec(x_37);
lean_dec(x_34);
x_65 = lean_ctor_get(x_39, 1);
lean_inc(x_65);
lean_dec(x_39);
x_66 = 1;
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_66);
lean_inc(x_12);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_12);
lean_ctor_set(x_67, 1, x_3);
x_16 = x_67;
x_17 = x_65;
goto block_25;
}
}
else
{
uint8_t x_68; lean_object* x_69; 
lean_dec(x_34);
x_68 = 1;
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_68);
lean_inc(x_12);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_12);
lean_ctor_set(x_69, 1, x_3);
x_16 = x_69;
x_17 = x_5;
goto block_25;
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_70 = lean_ctor_get(x_3, 0);
lean_inc(x_70);
lean_dec(x_3);
x_71 = lean_unsigned_to_nat(1u);
x_72 = l_Lean_Syntax_getArg(x_12, x_71);
x_73 = l_Lean_Syntax_isNone(x_72);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; uint8_t x_76; lean_object* x_77; lean_object* x_78; 
x_74 = lean_unsigned_to_nat(0u);
x_75 = l_Lean_Syntax_getArg(x_72, x_74);
x_76 = 0;
lean_inc(x_75);
x_77 = l_Lean_Elab_Term_isLocalTermId_x3f(x_75, x_76, x_4, x_5);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec(x_70);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
x_80 = l_Lean_Elab_Term_getCurrMacroScope(x_4, x_79);
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec(x_80);
x_83 = l_Lean_Elab_Term_getMainModule___rarg(x_82);
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec(x_83);
x_86 = lean_box(0);
x_87 = l_Array_umapMAux___main___at_Lean_Elab_Term_StructInst_ExpandNonAtomicExplicitSource_main___spec__1___closed__3;
x_88 = l_Lean_addMacroScope(x_84, x_87, x_81);
x_89 = lean_box(0);
x_90 = l_Array_umapMAux___main___at_Lean_Elab_Term_StructInst_ExpandNonAtomicExplicitSource_main___spec__1___closed__2;
x_91 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_91, 0, x_86);
lean_ctor_set(x_91, 1, x_90);
lean_ctor_set(x_91, 2, x_88);
lean_ctor_set(x_91, 3, x_89);
x_92 = l_Array_empty___closed__1;
x_93 = lean_array_push(x_92, x_91);
x_94 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_95 = lean_array_push(x_93, x_94);
x_96 = l_Lean_mkTermIdFromIdent___closed__2;
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_95);
x_98 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_98, 0, x_75);
x_99 = 1;
x_100 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set_uint8(x_100, sizeof(void*)*1, x_99);
x_101 = l_Lean_Syntax_setArg(x_72, x_74, x_97);
lean_inc(x_12);
x_102 = l_Lean_Syntax_setArg(x_12, x_71, x_101);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_100);
x_16 = x_103;
x_17 = x_85;
goto block_25;
}
else
{
lean_object* x_104; uint8_t x_105; lean_object* x_106; lean_object* x_107; 
lean_dec(x_78);
lean_dec(x_75);
lean_dec(x_72);
x_104 = lean_ctor_get(x_77, 1);
lean_inc(x_104);
lean_dec(x_77);
x_105 = 1;
x_106 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_106, 0, x_70);
lean_ctor_set_uint8(x_106, sizeof(void*)*1, x_105);
lean_inc(x_12);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_12);
lean_ctor_set(x_107, 1, x_106);
x_16 = x_107;
x_17 = x_104;
goto block_25;
}
}
else
{
uint8_t x_108; lean_object* x_109; lean_object* x_110; 
lean_dec(x_72);
x_108 = 1;
x_109 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_109, 0, x_70);
lean_ctor_set_uint8(x_109, sizeof(void*)*1, x_108);
lean_inc(x_12);
x_110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_110, 0, x_12);
lean_ctor_set(x_110, 1, x_109);
x_16 = x_110;
x_17 = x_5;
goto block_25;
}
}
}
else
{
lean_object* x_111; lean_object* x_112; uint8_t x_113; 
lean_dec(x_15);
lean_dec(x_3);
lean_dec(x_1);
x_111 = l_Array_umapMAux___main___at_Lean_Elab_Term_StructInst_ExpandNonAtomicExplicitSource_main___spec__1___closed__6;
x_112 = l_Lean_Elab_Term_throwError___rarg(x_12, x_111, x_4, x_5);
lean_dec(x_12);
x_113 = !lean_is_exclusive(x_112);
if (x_113 == 0)
{
return x_112;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_112, 0);
x_115 = lean_ctor_get(x_112, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_112);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
return x_116;
}
}
}
block_25:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_1, x_20);
x_22 = x_18;
lean_dec(x_12);
x_23 = lean_array_fset(x_15, x_1, x_22);
lean_dec(x_1);
x_1 = x_21;
x_2 = x_23;
x_3 = x_19;
x_5 = x_17;
goto _start;
}
}
}
}
lean_object* l_Lean_Elab_Term_StructInst_ExpandNonAtomicExplicitSource_main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_unsigned_to_nat(2u);
x_6 = l_Lean_Syntax_getArg(x_1, x_5);
x_7 = l_Lean_Syntax_getArgs(x_6);
lean_dec(x_6);
x_8 = lean_unsigned_to_nat(0u);
lean_inc(x_3);
x_9 = l_Array_umapMAux___main___at_Lean_Elab_Term_StructInst_ExpandNonAtomicExplicitSource_main___spec__1(x_8, x_7, x_2, x_3, x_4);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
lean_dec(x_3);
lean_dec(x_1);
x_13 = !lean_is_exclusive(x_10);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_10, 1);
lean_dec(x_14);
x_15 = lean_ctor_get(x_10, 0);
lean_dec(x_15);
x_16 = !lean_is_exclusive(x_9);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_9, 0);
lean_dec(x_17);
lean_ctor_set(x_10, 0, x_12);
return x_9;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_9, 1);
lean_inc(x_18);
lean_dec(x_9);
lean_ctor_set(x_10, 0, x_12);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_10);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_10);
x_20 = lean_ctor_get(x_9, 1);
lean_inc(x_20);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_21 = x_9;
} else {
 lean_dec_ref(x_9);
 x_21 = lean_box(0);
}
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_12);
lean_ctor_set(x_22, 1, x_11);
if (lean_is_scalar(x_21)) {
 x_23 = lean_alloc_ctor(0, 2, 0);
} else {
 x_23 = x_21;
}
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_20);
return x_23;
}
}
else
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_9, 1);
lean_inc(x_24);
lean_dec(x_9);
x_25 = !lean_is_exclusive(x_10);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_10, 0);
x_27 = lean_ctor_get(x_10, 1);
lean_dec(x_27);
x_28 = !lean_is_exclusive(x_12);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_29 = lean_ctor_get(x_12, 0);
x_30 = l_Lean_nullKind;
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_26);
x_32 = l_Lean_Syntax_setArg(x_1, x_5, x_31);
x_33 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_24);
lean_dec(x_3);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = l_Lean_Elab_Term_getMainModule___rarg(x_35);
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_38 = lean_ctor_get(x_36, 0);
x_39 = lean_box(0);
x_40 = l_Array_umapMAux___main___at_Lean_Elab_Term_StructInst_ExpandNonAtomicExplicitSource_main___spec__1___closed__3;
x_41 = l_Lean_addMacroScope(x_38, x_40, x_34);
x_42 = lean_box(0);
x_43 = l_Array_umapMAux___main___at_Lean_Elab_Term_StructInst_ExpandNonAtomicExplicitSource_main___spec__1___closed__2;
x_44 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_44, 0, x_39);
lean_ctor_set(x_44, 1, x_43);
lean_ctor_set(x_44, 2, x_41);
lean_ctor_set(x_44, 3, x_42);
x_45 = l_Array_empty___closed__1;
x_46 = lean_array_push(x_45, x_44);
x_47 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_48 = lean_array_push(x_46, x_47);
x_49 = lean_array_push(x_48, x_47);
x_50 = l___private_Init_Lean_Elab_Quotation_7__getHeadInfo___elambda__3___closed__4;
x_51 = lean_array_push(x_49, x_50);
x_52 = lean_array_push(x_51, x_29);
x_53 = l_Lean_Parser_Term_letIdDecl___closed__2;
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_52);
x_55 = l___private_Init_Lean_Elab_Quotation_7__getHeadInfo___elambda__3___closed__2;
x_56 = lean_array_push(x_55, x_54);
x_57 = l___private_Init_Lean_Elab_Quotation_7__getHeadInfo___elambda__3___closed__10;
x_58 = lean_array_push(x_56, x_57);
x_59 = lean_array_push(x_58, x_32);
x_60 = l_Lean_Parser_Term_let___elambda__1___closed__2;
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_59);
lean_ctor_set(x_12, 0, x_61);
lean_ctor_set(x_10, 0, x_12);
lean_ctor_set(x_36, 0, x_10);
return x_36;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_62 = lean_ctor_get(x_36, 0);
x_63 = lean_ctor_get(x_36, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_36);
x_64 = lean_box(0);
x_65 = l_Array_umapMAux___main___at_Lean_Elab_Term_StructInst_ExpandNonAtomicExplicitSource_main___spec__1___closed__3;
x_66 = l_Lean_addMacroScope(x_62, x_65, x_34);
x_67 = lean_box(0);
x_68 = l_Array_umapMAux___main___at_Lean_Elab_Term_StructInst_ExpandNonAtomicExplicitSource_main___spec__1___closed__2;
x_69 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_69, 0, x_64);
lean_ctor_set(x_69, 1, x_68);
lean_ctor_set(x_69, 2, x_66);
lean_ctor_set(x_69, 3, x_67);
x_70 = l_Array_empty___closed__1;
x_71 = lean_array_push(x_70, x_69);
x_72 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_73 = lean_array_push(x_71, x_72);
x_74 = lean_array_push(x_73, x_72);
x_75 = l___private_Init_Lean_Elab_Quotation_7__getHeadInfo___elambda__3___closed__4;
x_76 = lean_array_push(x_74, x_75);
x_77 = lean_array_push(x_76, x_29);
x_78 = l_Lean_Parser_Term_letIdDecl___closed__2;
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_77);
x_80 = l___private_Init_Lean_Elab_Quotation_7__getHeadInfo___elambda__3___closed__2;
x_81 = lean_array_push(x_80, x_79);
x_82 = l___private_Init_Lean_Elab_Quotation_7__getHeadInfo___elambda__3___closed__10;
x_83 = lean_array_push(x_81, x_82);
x_84 = lean_array_push(x_83, x_32);
x_85 = l_Lean_Parser_Term_let___elambda__1___closed__2;
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_84);
lean_ctor_set(x_12, 0, x_86);
lean_ctor_set(x_10, 0, x_12);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_10);
lean_ctor_set(x_87, 1, x_63);
return x_87;
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_88 = lean_ctor_get(x_12, 0);
lean_inc(x_88);
lean_dec(x_12);
x_89 = l_Lean_nullKind;
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_26);
x_91 = l_Lean_Syntax_setArg(x_1, x_5, x_90);
x_92 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_24);
lean_dec(x_3);
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
lean_dec(x_92);
x_95 = l_Lean_Elab_Term_getMainModule___rarg(x_94);
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 x_98 = x_95;
} else {
 lean_dec_ref(x_95);
 x_98 = lean_box(0);
}
x_99 = lean_box(0);
x_100 = l_Array_umapMAux___main___at_Lean_Elab_Term_StructInst_ExpandNonAtomicExplicitSource_main___spec__1___closed__3;
x_101 = l_Lean_addMacroScope(x_96, x_100, x_93);
x_102 = lean_box(0);
x_103 = l_Array_umapMAux___main___at_Lean_Elab_Term_StructInst_ExpandNonAtomicExplicitSource_main___spec__1___closed__2;
x_104 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_104, 0, x_99);
lean_ctor_set(x_104, 1, x_103);
lean_ctor_set(x_104, 2, x_101);
lean_ctor_set(x_104, 3, x_102);
x_105 = l_Array_empty___closed__1;
x_106 = lean_array_push(x_105, x_104);
x_107 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_108 = lean_array_push(x_106, x_107);
x_109 = lean_array_push(x_108, x_107);
x_110 = l___private_Init_Lean_Elab_Quotation_7__getHeadInfo___elambda__3___closed__4;
x_111 = lean_array_push(x_109, x_110);
x_112 = lean_array_push(x_111, x_88);
x_113 = l_Lean_Parser_Term_letIdDecl___closed__2;
x_114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_112);
x_115 = l___private_Init_Lean_Elab_Quotation_7__getHeadInfo___elambda__3___closed__2;
x_116 = lean_array_push(x_115, x_114);
x_117 = l___private_Init_Lean_Elab_Quotation_7__getHeadInfo___elambda__3___closed__10;
x_118 = lean_array_push(x_116, x_117);
x_119 = lean_array_push(x_118, x_91);
x_120 = l_Lean_Parser_Term_let___elambda__1___closed__2;
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_119);
x_122 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set(x_10, 0, x_122);
if (lean_is_scalar(x_98)) {
 x_123 = lean_alloc_ctor(0, 2, 0);
} else {
 x_123 = x_98;
}
lean_ctor_set(x_123, 0, x_10);
lean_ctor_set(x_123, 1, x_97);
return x_123;
}
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_124 = lean_ctor_get(x_10, 0);
lean_inc(x_124);
lean_dec(x_10);
x_125 = lean_ctor_get(x_12, 0);
lean_inc(x_125);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 x_126 = x_12;
} else {
 lean_dec_ref(x_12);
 x_126 = lean_box(0);
}
x_127 = l_Lean_nullKind;
x_128 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_124);
x_129 = l_Lean_Syntax_setArg(x_1, x_5, x_128);
x_130 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_24);
lean_dec(x_3);
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_130, 1);
lean_inc(x_132);
lean_dec(x_130);
x_133 = l_Lean_Elab_Term_getMainModule___rarg(x_132);
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_133, 1);
lean_inc(x_135);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 lean_ctor_release(x_133, 1);
 x_136 = x_133;
} else {
 lean_dec_ref(x_133);
 x_136 = lean_box(0);
}
x_137 = lean_box(0);
x_138 = l_Array_umapMAux___main___at_Lean_Elab_Term_StructInst_ExpandNonAtomicExplicitSource_main___spec__1___closed__3;
x_139 = l_Lean_addMacroScope(x_134, x_138, x_131);
x_140 = lean_box(0);
x_141 = l_Array_umapMAux___main___at_Lean_Elab_Term_StructInst_ExpandNonAtomicExplicitSource_main___spec__1___closed__2;
x_142 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_142, 0, x_137);
lean_ctor_set(x_142, 1, x_141);
lean_ctor_set(x_142, 2, x_139);
lean_ctor_set(x_142, 3, x_140);
x_143 = l_Array_empty___closed__1;
x_144 = lean_array_push(x_143, x_142);
x_145 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_146 = lean_array_push(x_144, x_145);
x_147 = lean_array_push(x_146, x_145);
x_148 = l___private_Init_Lean_Elab_Quotation_7__getHeadInfo___elambda__3___closed__4;
x_149 = lean_array_push(x_147, x_148);
x_150 = lean_array_push(x_149, x_125);
x_151 = l_Lean_Parser_Term_letIdDecl___closed__2;
x_152 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_152, 0, x_151);
lean_ctor_set(x_152, 1, x_150);
x_153 = l___private_Init_Lean_Elab_Quotation_7__getHeadInfo___elambda__3___closed__2;
x_154 = lean_array_push(x_153, x_152);
x_155 = l___private_Init_Lean_Elab_Quotation_7__getHeadInfo___elambda__3___closed__10;
x_156 = lean_array_push(x_154, x_155);
x_157 = lean_array_push(x_156, x_129);
x_158 = l_Lean_Parser_Term_let___elambda__1___closed__2;
x_159 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_159, 0, x_158);
lean_ctor_set(x_159, 1, x_157);
if (lean_is_scalar(x_126)) {
 x_160 = lean_alloc_ctor(1, 1, 0);
} else {
 x_160 = x_126;
}
lean_ctor_set(x_160, 0, x_159);
x_161 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_161, 0, x_160);
lean_ctor_set(x_161, 1, x_11);
if (lean_is_scalar(x_136)) {
 x_162 = lean_alloc_ctor(0, 2, 0);
} else {
 x_162 = x_136;
}
lean_ctor_set(x_162, 0, x_161);
lean_ctor_set(x_162, 1, x_135);
return x_162;
}
}
}
else
{
uint8_t x_163; 
lean_dec(x_3);
lean_dec(x_1);
x_163 = !lean_is_exclusive(x_9);
if (x_163 == 0)
{
return x_9;
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_164 = lean_ctor_get(x_9, 0);
x_165 = lean_ctor_get(x_9, 1);
lean_inc(x_165);
lean_inc(x_164);
lean_dec(x_9);
x_166 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_166, 0, x_164);
lean_ctor_set(x_166, 1, x_165);
return x_166;
}
}
}
}
lean_object* _init_l___private_Init_Lean_Elab_StructInst_1__expandNonAtomicExplicitSource___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = 0;
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
lean_object* l___private_Init_Lean_Elab_StructInst_1__expandNonAtomicExplicitSource(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_3, 5);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_add(x_5, x_6);
lean_ctor_set(x_3, 5, x_7);
x_8 = !lean_is_exclusive(x_2);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_2, 9);
lean_dec(x_9);
lean_ctor_set(x_2, 9, x_5);
x_10 = l___private_Init_Lean_Elab_StructInst_1__expandNonAtomicExplicitSource___closed__1;
x_11 = l_Lean_Elab_Term_StructInst_ExpandNonAtomicExplicitSource_main(x_1, x_10, x_2, x_3);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
lean_ctor_set(x_11, 0, x_14);
return x_11;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_11, 0);
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_11);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_11);
if (x_19 == 0)
{
return x_11;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_11, 0);
x_21 = lean_ctor_get(x_11, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_11);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; uint8_t x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_23 = lean_ctor_get(x_2, 0);
x_24 = lean_ctor_get(x_2, 1);
x_25 = lean_ctor_get(x_2, 2);
x_26 = lean_ctor_get(x_2, 3);
x_27 = lean_ctor_get(x_2, 4);
x_28 = lean_ctor_get(x_2, 5);
x_29 = lean_ctor_get(x_2, 6);
x_30 = lean_ctor_get(x_2, 7);
x_31 = lean_ctor_get(x_2, 8);
x_32 = lean_ctor_get_uint8(x_2, sizeof(void*)*10);
x_33 = lean_ctor_get_uint8(x_2, sizeof(void*)*10 + 1);
x_34 = lean_ctor_get_uint8(x_2, sizeof(void*)*10 + 2);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_2);
x_35 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_35, 0, x_23);
lean_ctor_set(x_35, 1, x_24);
lean_ctor_set(x_35, 2, x_25);
lean_ctor_set(x_35, 3, x_26);
lean_ctor_set(x_35, 4, x_27);
lean_ctor_set(x_35, 5, x_28);
lean_ctor_set(x_35, 6, x_29);
lean_ctor_set(x_35, 7, x_30);
lean_ctor_set(x_35, 8, x_31);
lean_ctor_set(x_35, 9, x_5);
lean_ctor_set_uint8(x_35, sizeof(void*)*10, x_32);
lean_ctor_set_uint8(x_35, sizeof(void*)*10 + 1, x_33);
lean_ctor_set_uint8(x_35, sizeof(void*)*10 + 2, x_34);
x_36 = l___private_Init_Lean_Elab_StructInst_1__expandNonAtomicExplicitSource___closed__1;
x_37 = l_Lean_Elab_Term_StructInst_ExpandNonAtomicExplicitSource_main(x_1, x_36, x_35, x_3);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_40 = x_37;
} else {
 lean_dec_ref(x_37);
 x_40 = lean_box(0);
}
x_41 = lean_ctor_get(x_38, 0);
lean_inc(x_41);
lean_dec(x_38);
if (lean_is_scalar(x_40)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_40;
}
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_39);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_43 = lean_ctor_get(x_37, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_37, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_45 = x_37;
} else {
 lean_dec_ref(x_37);
 x_45 = lean_box(0);
}
if (lean_is_scalar(x_45)) {
 x_46 = lean_alloc_ctor(1, 2, 0);
} else {
 x_46 = x_45;
}
lean_ctor_set(x_46, 0, x_43);
lean_ctor_set(x_46, 1, x_44);
return x_46;
}
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; uint8_t x_66; uint8_t x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_47 = lean_ctor_get(x_3, 0);
x_48 = lean_ctor_get(x_3, 1);
x_49 = lean_ctor_get(x_3, 2);
x_50 = lean_ctor_get(x_3, 3);
x_51 = lean_ctor_get(x_3, 4);
x_52 = lean_ctor_get(x_3, 5);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_3);
x_53 = lean_unsigned_to_nat(1u);
x_54 = lean_nat_add(x_52, x_53);
x_55 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_55, 0, x_47);
lean_ctor_set(x_55, 1, x_48);
lean_ctor_set(x_55, 2, x_49);
lean_ctor_set(x_55, 3, x_50);
lean_ctor_set(x_55, 4, x_51);
lean_ctor_set(x_55, 5, x_54);
x_56 = lean_ctor_get(x_2, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_2, 1);
lean_inc(x_57);
x_58 = lean_ctor_get(x_2, 2);
lean_inc(x_58);
x_59 = lean_ctor_get(x_2, 3);
lean_inc(x_59);
x_60 = lean_ctor_get(x_2, 4);
lean_inc(x_60);
x_61 = lean_ctor_get(x_2, 5);
lean_inc(x_61);
x_62 = lean_ctor_get(x_2, 6);
lean_inc(x_62);
x_63 = lean_ctor_get(x_2, 7);
lean_inc(x_63);
x_64 = lean_ctor_get(x_2, 8);
lean_inc(x_64);
x_65 = lean_ctor_get_uint8(x_2, sizeof(void*)*10);
x_66 = lean_ctor_get_uint8(x_2, sizeof(void*)*10 + 1);
x_67 = lean_ctor_get_uint8(x_2, sizeof(void*)*10 + 2);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 lean_ctor_release(x_2, 3);
 lean_ctor_release(x_2, 4);
 lean_ctor_release(x_2, 5);
 lean_ctor_release(x_2, 6);
 lean_ctor_release(x_2, 7);
 lean_ctor_release(x_2, 8);
 lean_ctor_release(x_2, 9);
 x_68 = x_2;
} else {
 lean_dec_ref(x_2);
 x_68 = lean_box(0);
}
if (lean_is_scalar(x_68)) {
 x_69 = lean_alloc_ctor(0, 10, 3);
} else {
 x_69 = x_68;
}
lean_ctor_set(x_69, 0, x_56);
lean_ctor_set(x_69, 1, x_57);
lean_ctor_set(x_69, 2, x_58);
lean_ctor_set(x_69, 3, x_59);
lean_ctor_set(x_69, 4, x_60);
lean_ctor_set(x_69, 5, x_61);
lean_ctor_set(x_69, 6, x_62);
lean_ctor_set(x_69, 7, x_63);
lean_ctor_set(x_69, 8, x_64);
lean_ctor_set(x_69, 9, x_52);
lean_ctor_set_uint8(x_69, sizeof(void*)*10, x_65);
lean_ctor_set_uint8(x_69, sizeof(void*)*10 + 1, x_66);
lean_ctor_set_uint8(x_69, sizeof(void*)*10 + 2, x_67);
x_70 = l___private_Init_Lean_Elab_StructInst_1__expandNonAtomicExplicitSource___closed__1;
x_71 = l_Lean_Elab_Term_StructInst_ExpandNonAtomicExplicitSource_main(x_1, x_70, x_69, x_55);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_74 = x_71;
} else {
 lean_dec_ref(x_71);
 x_74 = lean_box(0);
}
x_75 = lean_ctor_get(x_72, 0);
lean_inc(x_75);
lean_dec(x_72);
if (lean_is_scalar(x_74)) {
 x_76 = lean_alloc_ctor(0, 2, 0);
} else {
 x_76 = x_74;
}
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_73);
return x_76;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_77 = lean_ctor_get(x_71, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_71, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_79 = x_71;
} else {
 lean_dec_ref(x_71);
 x_79 = lean_box(0);
}
if (lean_is_scalar(x_79)) {
 x_80 = lean_alloc_ctor(1, 2, 0);
} else {
 x_80 = x_79;
}
lean_ctor_set(x_80, 0, x_77);
lean_ctor_set(x_80, 1, x_78);
return x_80;
}
}
}
}
uint8_t l_Lean_Elab_Term_StructInst_Source_isNone(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_2; 
x_2 = 1;
return x_2;
}
else
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
}
}
lean_object* l_Lean_Elab_Term_StructInst_Source_isNone___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_Term_StructInst_Source_isNone(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_StructInst_Source_hasFormat___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" ..");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_StructInst_Source_hasFormat___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_StructInst_Source_hasFormat___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_StructInst_Source_hasFormat___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" .. ");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_StructInst_Source_hasFormat___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_StructInst_Source_hasFormat___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_StructInst_Source_hasFormat(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; 
x_2 = l_Lean_Format_join___closed__1;
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Term_StructInst_Source_hasFormat___closed__2;
return x_3;
}
default: 
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_expr_dbg_to_string(x_4);
x_6 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = 0;
x_8 = l_Lean_Elab_Term_StructInst_Source_hasFormat___closed__4;
x_9 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_6);
lean_ctor_set_uint8(x_9, sizeof(void*)*2, x_7);
return x_9;
}
}
}
}
lean_object* l_Lean_Elab_Term_StructInst_Source_hasFormat___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Term_StructInst_Source_hasFormat(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_StructInst_Source_addSyntax(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_array_push(x_2, x_3);
return x_4;
}
}
}
lean_object* l_Array_foldlStepMAux___main___at___private_Init_Lean_Elab_StructInst_2__getStructSource___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_array_fget(x_2, x_3);
lean_inc(x_10);
x_11 = l_Lean_Syntax_getKind(x_10);
x_12 = l_Lean_Parser_Term_structInstSource___elambda__1___closed__2;
x_13 = lean_name_eq(x_11, x_12);
lean_dec(x_11);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_10);
x_14 = lean_nat_add(x_3, x_1);
lean_dec(x_3);
x_3 = x_14;
goto _start;
}
else
{
uint8_t x_16; 
x_16 = l_Lean_Elab_Term_StructInst_Source_isNone(x_4);
lean_dec(x_4);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
lean_dec(x_3);
x_17 = l_Array_umapMAux___main___at_Lean_Elab_Term_StructInst_ExpandNonAtomicExplicitSource_main___spec__1___closed__6;
x_18 = l_Lean_Elab_Term_throwError___rarg(x_10, x_17, x_5, x_6);
lean_dec(x_10);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
return x_18;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_18);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_unsigned_to_nat(1u);
x_24 = l_Lean_Syntax_getArg(x_10, x_23);
x_25 = l_Lean_Syntax_isNone(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_unsigned_to_nat(0u);
x_27 = l_Lean_Syntax_getArg(x_24, x_26);
lean_dec(x_24);
x_28 = 0;
x_29 = l_Lean_Elab_Term_isLocalTermId_x3f(x_27, x_28, x_5, x_6);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_10);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l___private_Init_Lean_Elab_Quotation_5__quoteSyntax___main___closed__1;
x_33 = l_unreachable_x21___rarg(x_32);
lean_inc(x_5);
x_34 = lean_apply_2(x_33, x_5, x_31);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_nat_add(x_3, x_1);
lean_dec(x_3);
x_3 = x_37;
x_4 = x_35;
x_6 = x_36;
goto _start;
}
else
{
uint8_t x_39; 
lean_dec(x_5);
lean_dec(x_3);
x_39 = !lean_is_exclusive(x_34);
if (x_39 == 0)
{
return x_34;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_34, 0);
x_41 = lean_ctor_get(x_34, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_34);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_43 = lean_ctor_get(x_29, 1);
lean_inc(x_43);
lean_dec(x_29);
x_44 = lean_ctor_get(x_30, 0);
lean_inc(x_44);
lean_dec(x_30);
x_45 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_45, 0, x_10);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_nat_add(x_3, x_1);
lean_dec(x_3);
x_3 = x_46;
x_4 = x_45;
x_6 = x_43;
goto _start;
}
}
else
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_24);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_10);
x_49 = lean_nat_add(x_3, x_1);
lean_dec(x_3);
x_3 = x_49;
x_4 = x_48;
goto _start;
}
}
}
}
}
}
lean_object* l___private_Init_Lean_Elab_StructInst_2__getStructSource(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_unsigned_to_nat(2u);
x_5 = l_Lean_Syntax_getArg(x_1, x_4);
x_6 = l_Lean_Syntax_getArgs(x_5);
lean_dec(x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_box(0);
x_9 = l_Array_foldlStepMAux___main___at___private_Init_Lean_Elab_StructInst_2__getStructSource___spec__1(x_4, x_6, x_7, x_8, x_2, x_3);
lean_dec(x_6);
return x_9;
}
}
lean_object* l_Array_foldlStepMAux___main___at___private_Init_Lean_Elab_StructInst_2__getStructSource___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_foldlStepMAux___main___at___private_Init_Lean_Elab_StructInst_2__getStructSource___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l___private_Init_Lean_Elab_StructInst_2__getStructSource___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Elab_StructInst_2__getStructSource(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* _init_l_Array_foldlStepMAux___main___at___private_Init_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid {...} notation, can't mix field and `[..]` at a given level");
return x_1;
}
}
lean_object* _init_l_Array_foldlStepMAux___main___at___private_Init_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_foldlStepMAux___main___at___private_Init_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Array_foldlStepMAux___main___at___private_Init_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_foldlStepMAux___main___at___private_Init_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Array_foldlStepMAux___main___at___private_Init_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid {...} notation, at most one `[..]` at a given level");
return x_1;
}
}
lean_object* _init_l_Array_foldlStepMAux___main___at___private_Init_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_foldlStepMAux___main___at___private_Init_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Array_foldlStepMAux___main___at___private_Init_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_foldlStepMAux___main___at___private_Init_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Array_foldlStepMAux___main___at___private_Init_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_array_fget(x_2, x_3);
lean_inc(x_10);
x_11 = l_Lean_Syntax_getKind(x_10);
x_12 = l_Lean_Parser_Term_structInstSource___elambda__1___closed__2;
x_13 = lean_name_eq(x_11, x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = l_Lean_Parser_Term_structInstArrayRef___elambda__1___closed__2;
x_15 = lean_name_eq(x_11, x_14);
lean_dec(x_11);
if (x_15 == 0)
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_10);
x_17 = lean_nat_add(x_3, x_1);
lean_dec(x_3);
x_3 = x_17;
x_4 = x_16;
goto _start;
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_4, 0);
lean_inc(x_19);
x_20 = l_Lean_Syntax_getKind(x_19);
x_21 = lean_name_eq(x_20, x_14);
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_10);
x_22 = lean_nat_add(x_3, x_1);
lean_dec(x_3);
x_3 = x_22;
goto _start;
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
lean_dec(x_4);
lean_dec(x_3);
x_24 = l_Array_foldlStepMAux___main___at___private_Init_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__3;
x_25 = l_Lean_Elab_Term_throwError___rarg(x_10, x_24, x_5, x_6);
lean_dec(x_10);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
return x_25;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_25);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
else
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_10);
x_31 = lean_nat_add(x_3, x_1);
lean_dec(x_3);
x_3 = x_31;
x_4 = x_30;
goto _start;
}
else
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; 
lean_dec(x_3);
x_33 = lean_ctor_get(x_4, 0);
lean_inc(x_33);
lean_dec(x_4);
x_34 = l_Lean_Syntax_getKind(x_33);
x_35 = lean_name_eq(x_34, x_14);
lean_dec(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_36 = l_Array_foldlStepMAux___main___at___private_Init_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__3;
x_37 = l_Lean_Elab_Term_throwError___rarg(x_10, x_36, x_5, x_6);
lean_dec(x_10);
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
return x_37;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_37, 0);
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_37);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
else
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_42 = l_Array_foldlStepMAux___main___at___private_Init_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__6;
x_43 = l_Lean_Elab_Term_throwError___rarg(x_10, x_42, x_5, x_6);
lean_dec(x_10);
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
return x_43;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_43, 0);
x_46 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_43);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
}
}
else
{
lean_object* x_48; 
lean_dec(x_11);
lean_dec(x_10);
x_48 = lean_nat_add(x_3, x_1);
lean_dec(x_3);
x_3 = x_48;
goto _start;
}
}
}
}
lean_object* l___private_Init_Lean_Elab_StructInst_3__isModifyOp_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_unsigned_to_nat(2u);
x_5 = l_Lean_Syntax_getArg(x_1, x_4);
x_6 = l_Lean_Syntax_getArgs(x_5);
lean_dec(x_5);
x_7 = lean_box(0);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Array_foldlStepMAux___main___at___private_Init_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1(x_4, x_6, x_8, x_7, x_2, x_3);
lean_dec(x_6);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_9, 0);
lean_dec(x_12);
lean_ctor_set(x_9, 0, x_7);
return x_9;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_9, 1);
lean_inc(x_13);
lean_dec(x_9);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_9);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_16 = lean_ctor_get(x_9, 0);
lean_dec(x_16);
x_17 = lean_ctor_get(x_10, 0);
lean_inc(x_17);
x_18 = l_Lean_Syntax_getKind(x_17);
x_19 = l_Lean_Parser_Term_structInstArrayRef___elambda__1___closed__2;
x_20 = lean_name_eq(x_18, x_19);
lean_dec(x_18);
if (x_20 == 0)
{
lean_dec(x_10);
lean_ctor_set(x_9, 0, x_7);
return x_9;
}
else
{
return x_9;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_21 = lean_ctor_get(x_9, 1);
lean_inc(x_21);
lean_dec(x_9);
x_22 = lean_ctor_get(x_10, 0);
lean_inc(x_22);
x_23 = l_Lean_Syntax_getKind(x_22);
x_24 = l_Lean_Parser_Term_structInstArrayRef___elambda__1___closed__2;
x_25 = lean_name_eq(x_23, x_24);
lean_dec(x_23);
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec(x_10);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_7);
lean_ctor_set(x_26, 1, x_21);
return x_26;
}
else
{
lean_object* x_27; 
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_10);
lean_ctor_set(x_27, 1, x_21);
return x_27;
}
}
}
}
else
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_9);
if (x_28 == 0)
{
return x_9;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_9, 0);
x_30 = lean_ctor_get(x_9, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_9);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
lean_object* l_Array_foldlStepMAux___main___at___private_Init_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_foldlStepMAux___main___at___private_Init_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l___private_Init_Lean_Elab_StructInst_3__isModifyOp_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Elab_StructInst_3__isModifyOp_x3f(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* _init_l___private_Init_Lean_Elab_StructInst_4__elabModifyOp___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("WIP ");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Elab_StructInst_4__elabModifyOp___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_StructInst_4__elabModifyOp___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_StructInst_4__elabModifyOp___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_StructInst_4__elabModifyOp___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Init_Lean_Elab_StructInst_4__elabModifyOp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_inc(x_1);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_1);
x_8 = l___private_Init_Lean_Elab_StructInst_4__elabModifyOp___closed__3;
x_9 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
x_10 = l_Lean_Elab_Term_throwError___rarg(x_1, x_9, x_5, x_6);
lean_dec(x_1);
return x_10;
}
}
lean_object* l___private_Init_Lean_Elab_StructInst_4__elabModifyOp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Lean_Elab_StructInst_4__elabModifyOp(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* _init_l___private_Init_Lean_Elab_StructInst_5__getStructName___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid {...} notation, expected type is not of the form (C ...)");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Elab_StructInst_5__getStructName___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_StructInst_5__getStructName___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_StructInst_5__getStructName___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_StructInst_5__getStructName___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_StructInst_5__getStructName___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid {...} notation, source type is not of the form (C ...)");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Elab_StructInst_5__getStructName___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_StructInst_5__getStructName___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_StructInst_5__getStructName___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_StructInst_5__getStructName___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Init_Lean_Elab_StructInst_5__getStructName(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = l_Lean_Syntax_getArg(x_1, x_6);
x_8 = l_Lean_Syntax_isNone(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Lean_Syntax_getIdAt(x_7, x_9);
lean_dec(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_5);
return x_11;
}
else
{
lean_object* x_12; 
lean_dec(x_7);
x_12 = l_Lean_Elab_Term_tryPostponeIfNoneOrMVar(x_2, x_4, x_5);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
if (lean_obj_tag(x_2) == 0)
{
if (lean_obj_tag(x_3) == 2)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_3, 1);
lean_inc(x_30);
lean_dec(x_3);
lean_inc(x_4);
x_31 = l_Lean_Elab_Term_inferType(x_1, x_30, x_4, x_13);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
lean_inc(x_4);
x_34 = l_Lean_Elab_Term_whnf(x_1, x_32, x_4, x_33);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = l_Lean_Elab_Term_tryPostponeIfMVar(x_35, x_4, x_36);
if (lean_obj_tag(x_37) == 0)
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_48; 
x_39 = lean_ctor_get(x_37, 1);
x_40 = lean_ctor_get(x_37, 0);
lean_dec(x_40);
x_48 = l_Lean_Expr_getAppFn___main(x_35);
if (lean_obj_tag(x_48) == 4)
{
lean_object* x_49; 
lean_dec(x_35);
lean_dec(x_4);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
lean_dec(x_48);
lean_ctor_set(x_37, 0, x_49);
return x_37;
}
else
{
lean_object* x_50; 
lean_dec(x_48);
lean_free_object(x_37);
x_50 = lean_box(0);
x_41 = x_50;
goto block_47;
}
block_47:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_41);
x_42 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_42, 0, x_35);
x_43 = l_Lean_indentExpr(x_42);
x_44 = l___private_Init_Lean_Elab_StructInst_5__getStructName___closed__6;
x_45 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
x_46 = l_Lean_Elab_Term_throwError___rarg(x_1, x_45, x_4, x_39);
return x_46;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_59; 
x_51 = lean_ctor_get(x_37, 1);
lean_inc(x_51);
lean_dec(x_37);
x_59 = l_Lean_Expr_getAppFn___main(x_35);
if (lean_obj_tag(x_59) == 4)
{
lean_object* x_60; lean_object* x_61; 
lean_dec(x_35);
lean_dec(x_4);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
lean_dec(x_59);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_51);
return x_61;
}
else
{
lean_object* x_62; 
lean_dec(x_59);
x_62 = lean_box(0);
x_52 = x_62;
goto block_58;
}
block_58:
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_52);
x_53 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_53, 0, x_35);
x_54 = l_Lean_indentExpr(x_53);
x_55 = l___private_Init_Lean_Elab_StructInst_5__getStructName___closed__6;
x_56 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_54);
x_57 = l_Lean_Elab_Term_throwError___rarg(x_1, x_56, x_4, x_51);
return x_57;
}
}
}
else
{
uint8_t x_63; 
lean_dec(x_35);
lean_dec(x_4);
x_63 = !lean_is_exclusive(x_37);
if (x_63 == 0)
{
return x_37;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_37, 0);
x_65 = lean_ctor_get(x_37, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_37);
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
lean_dec(x_4);
x_67 = !lean_is_exclusive(x_34);
if (x_67 == 0)
{
return x_34;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_34, 0);
x_69 = lean_ctor_get(x_34, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_34);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
else
{
uint8_t x_71; 
lean_dec(x_4);
x_71 = !lean_is_exclusive(x_31);
if (x_71 == 0)
{
return x_31;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_31, 0);
x_73 = lean_ctor_get(x_31, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_31);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
else
{
lean_object* x_75; 
lean_dec(x_3);
x_75 = lean_box(0);
x_14 = x_75;
goto block_29;
}
}
else
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_ctor_get(x_2, 0);
lean_inc(x_76);
lean_dec(x_2);
lean_inc(x_4);
lean_inc(x_76);
x_77 = l_Lean_Elab_Term_whnf(x_1, x_76, x_4, x_13);
if (lean_obj_tag(x_77) == 0)
{
uint8_t x_78; 
x_78 = !lean_is_exclusive(x_77);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_88; 
x_79 = lean_ctor_get(x_77, 0);
x_80 = lean_ctor_get(x_77, 1);
x_88 = l_Lean_Expr_getAppFn___main(x_79);
lean_dec(x_79);
switch (lean_obj_tag(x_88)) {
case 0:
{
lean_dec(x_88);
lean_free_object(x_77);
if (lean_obj_tag(x_3) == 2)
{
lean_object* x_89; lean_object* x_90; 
lean_dec(x_76);
x_89 = lean_ctor_get(x_3, 1);
lean_inc(x_89);
lean_dec(x_3);
lean_inc(x_4);
x_90 = l_Lean_Elab_Term_inferType(x_1, x_89, x_4, x_80);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
lean_dec(x_90);
lean_inc(x_4);
x_93 = l_Lean_Elab_Term_whnf(x_1, x_91, x_4, x_92);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
lean_dec(x_93);
x_96 = l_Lean_Elab_Term_tryPostponeIfMVar(x_94, x_4, x_95);
if (lean_obj_tag(x_96) == 0)
{
uint8_t x_97; 
x_97 = !lean_is_exclusive(x_96);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_107; 
x_98 = lean_ctor_get(x_96, 1);
x_99 = lean_ctor_get(x_96, 0);
lean_dec(x_99);
x_107 = l_Lean_Expr_getAppFn___main(x_94);
if (lean_obj_tag(x_107) == 4)
{
lean_object* x_108; 
lean_dec(x_94);
lean_dec(x_4);
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
lean_dec(x_107);
lean_ctor_set(x_96, 0, x_108);
return x_96;
}
else
{
lean_object* x_109; 
lean_dec(x_107);
lean_free_object(x_96);
x_109 = lean_box(0);
x_100 = x_109;
goto block_106;
}
block_106:
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_dec(x_100);
x_101 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_101, 0, x_94);
x_102 = l_Lean_indentExpr(x_101);
x_103 = l___private_Init_Lean_Elab_StructInst_5__getStructName___closed__6;
x_104 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_102);
x_105 = l_Lean_Elab_Term_throwError___rarg(x_1, x_104, x_4, x_98);
return x_105;
}
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_118; 
x_110 = lean_ctor_get(x_96, 1);
lean_inc(x_110);
lean_dec(x_96);
x_118 = l_Lean_Expr_getAppFn___main(x_94);
if (lean_obj_tag(x_118) == 4)
{
lean_object* x_119; lean_object* x_120; 
lean_dec(x_94);
lean_dec(x_4);
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
lean_dec(x_118);
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_110);
return x_120;
}
else
{
lean_object* x_121; 
lean_dec(x_118);
x_121 = lean_box(0);
x_111 = x_121;
goto block_117;
}
block_117:
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
lean_dec(x_111);
x_112 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_112, 0, x_94);
x_113 = l_Lean_indentExpr(x_112);
x_114 = l___private_Init_Lean_Elab_StructInst_5__getStructName___closed__6;
x_115 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_113);
x_116 = l_Lean_Elab_Term_throwError___rarg(x_1, x_115, x_4, x_110);
return x_116;
}
}
}
else
{
uint8_t x_122; 
lean_dec(x_94);
lean_dec(x_4);
x_122 = !lean_is_exclusive(x_96);
if (x_122 == 0)
{
return x_96;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_123 = lean_ctor_get(x_96, 0);
x_124 = lean_ctor_get(x_96, 1);
lean_inc(x_124);
lean_inc(x_123);
lean_dec(x_96);
x_125 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set(x_125, 1, x_124);
return x_125;
}
}
}
else
{
uint8_t x_126; 
lean_dec(x_4);
x_126 = !lean_is_exclusive(x_93);
if (x_126 == 0)
{
return x_93;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_127 = lean_ctor_get(x_93, 0);
x_128 = lean_ctor_get(x_93, 1);
lean_inc(x_128);
lean_inc(x_127);
lean_dec(x_93);
x_129 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_129, 0, x_127);
lean_ctor_set(x_129, 1, x_128);
return x_129;
}
}
}
else
{
uint8_t x_130; 
lean_dec(x_4);
x_130 = !lean_is_exclusive(x_90);
if (x_130 == 0)
{
return x_90;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_131 = lean_ctor_get(x_90, 0);
x_132 = lean_ctor_get(x_90, 1);
lean_inc(x_132);
lean_inc(x_131);
lean_dec(x_90);
x_133 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set(x_133, 1, x_132);
return x_133;
}
}
}
else
{
lean_object* x_134; 
lean_dec(x_3);
x_134 = lean_box(0);
x_81 = x_134;
goto block_87;
}
}
case 1:
{
lean_dec(x_88);
lean_free_object(x_77);
if (lean_obj_tag(x_3) == 2)
{
lean_object* x_135; lean_object* x_136; 
lean_dec(x_76);
x_135 = lean_ctor_get(x_3, 1);
lean_inc(x_135);
lean_dec(x_3);
lean_inc(x_4);
x_136 = l_Lean_Elab_Term_inferType(x_1, x_135, x_4, x_80);
if (lean_obj_tag(x_136) == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_136, 1);
lean_inc(x_138);
lean_dec(x_136);
lean_inc(x_4);
x_139 = l_Lean_Elab_Term_whnf(x_1, x_137, x_4, x_138);
if (lean_obj_tag(x_139) == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_139, 1);
lean_inc(x_141);
lean_dec(x_139);
x_142 = l_Lean_Elab_Term_tryPostponeIfMVar(x_140, x_4, x_141);
if (lean_obj_tag(x_142) == 0)
{
uint8_t x_143; 
x_143 = !lean_is_exclusive(x_142);
if (x_143 == 0)
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_153; 
x_144 = lean_ctor_get(x_142, 1);
x_145 = lean_ctor_get(x_142, 0);
lean_dec(x_145);
x_153 = l_Lean_Expr_getAppFn___main(x_140);
if (lean_obj_tag(x_153) == 4)
{
lean_object* x_154; 
lean_dec(x_140);
lean_dec(x_4);
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
lean_dec(x_153);
lean_ctor_set(x_142, 0, x_154);
return x_142;
}
else
{
lean_object* x_155; 
lean_dec(x_153);
lean_free_object(x_142);
x_155 = lean_box(0);
x_146 = x_155;
goto block_152;
}
block_152:
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
lean_dec(x_146);
x_147 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_147, 0, x_140);
x_148 = l_Lean_indentExpr(x_147);
x_149 = l___private_Init_Lean_Elab_StructInst_5__getStructName___closed__6;
x_150 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_150, 0, x_149);
lean_ctor_set(x_150, 1, x_148);
x_151 = l_Lean_Elab_Term_throwError___rarg(x_1, x_150, x_4, x_144);
return x_151;
}
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_164; 
x_156 = lean_ctor_get(x_142, 1);
lean_inc(x_156);
lean_dec(x_142);
x_164 = l_Lean_Expr_getAppFn___main(x_140);
if (lean_obj_tag(x_164) == 4)
{
lean_object* x_165; lean_object* x_166; 
lean_dec(x_140);
lean_dec(x_4);
x_165 = lean_ctor_get(x_164, 0);
lean_inc(x_165);
lean_dec(x_164);
x_166 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_166, 0, x_165);
lean_ctor_set(x_166, 1, x_156);
return x_166;
}
else
{
lean_object* x_167; 
lean_dec(x_164);
x_167 = lean_box(0);
x_157 = x_167;
goto block_163;
}
block_163:
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
lean_dec(x_157);
x_158 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_158, 0, x_140);
x_159 = l_Lean_indentExpr(x_158);
x_160 = l___private_Init_Lean_Elab_StructInst_5__getStructName___closed__6;
x_161 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_161, 0, x_160);
lean_ctor_set(x_161, 1, x_159);
x_162 = l_Lean_Elab_Term_throwError___rarg(x_1, x_161, x_4, x_156);
return x_162;
}
}
}
else
{
uint8_t x_168; 
lean_dec(x_140);
lean_dec(x_4);
x_168 = !lean_is_exclusive(x_142);
if (x_168 == 0)
{
return x_142;
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_169 = lean_ctor_get(x_142, 0);
x_170 = lean_ctor_get(x_142, 1);
lean_inc(x_170);
lean_inc(x_169);
lean_dec(x_142);
x_171 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_171, 0, x_169);
lean_ctor_set(x_171, 1, x_170);
return x_171;
}
}
}
else
{
uint8_t x_172; 
lean_dec(x_4);
x_172 = !lean_is_exclusive(x_139);
if (x_172 == 0)
{
return x_139;
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_173 = lean_ctor_get(x_139, 0);
x_174 = lean_ctor_get(x_139, 1);
lean_inc(x_174);
lean_inc(x_173);
lean_dec(x_139);
x_175 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_175, 0, x_173);
lean_ctor_set(x_175, 1, x_174);
return x_175;
}
}
}
else
{
uint8_t x_176; 
lean_dec(x_4);
x_176 = !lean_is_exclusive(x_136);
if (x_176 == 0)
{
return x_136;
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_177 = lean_ctor_get(x_136, 0);
x_178 = lean_ctor_get(x_136, 1);
lean_inc(x_178);
lean_inc(x_177);
lean_dec(x_136);
x_179 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_179, 0, x_177);
lean_ctor_set(x_179, 1, x_178);
return x_179;
}
}
}
else
{
lean_object* x_180; 
lean_dec(x_3);
x_180 = lean_box(0);
x_81 = x_180;
goto block_87;
}
}
case 2:
{
lean_dec(x_88);
lean_free_object(x_77);
if (lean_obj_tag(x_3) == 2)
{
lean_object* x_181; lean_object* x_182; 
lean_dec(x_76);
x_181 = lean_ctor_get(x_3, 1);
lean_inc(x_181);
lean_dec(x_3);
lean_inc(x_4);
x_182 = l_Lean_Elab_Term_inferType(x_1, x_181, x_4, x_80);
if (lean_obj_tag(x_182) == 0)
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_183 = lean_ctor_get(x_182, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_182, 1);
lean_inc(x_184);
lean_dec(x_182);
lean_inc(x_4);
x_185 = l_Lean_Elab_Term_whnf(x_1, x_183, x_4, x_184);
if (lean_obj_tag(x_185) == 0)
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_186 = lean_ctor_get(x_185, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_185, 1);
lean_inc(x_187);
lean_dec(x_185);
x_188 = l_Lean_Elab_Term_tryPostponeIfMVar(x_186, x_4, x_187);
if (lean_obj_tag(x_188) == 0)
{
uint8_t x_189; 
x_189 = !lean_is_exclusive(x_188);
if (x_189 == 0)
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_199; 
x_190 = lean_ctor_get(x_188, 1);
x_191 = lean_ctor_get(x_188, 0);
lean_dec(x_191);
x_199 = l_Lean_Expr_getAppFn___main(x_186);
if (lean_obj_tag(x_199) == 4)
{
lean_object* x_200; 
lean_dec(x_186);
lean_dec(x_4);
x_200 = lean_ctor_get(x_199, 0);
lean_inc(x_200);
lean_dec(x_199);
lean_ctor_set(x_188, 0, x_200);
return x_188;
}
else
{
lean_object* x_201; 
lean_dec(x_199);
lean_free_object(x_188);
x_201 = lean_box(0);
x_192 = x_201;
goto block_198;
}
block_198:
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; 
lean_dec(x_192);
x_193 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_193, 0, x_186);
x_194 = l_Lean_indentExpr(x_193);
x_195 = l___private_Init_Lean_Elab_StructInst_5__getStructName___closed__6;
x_196 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_196, 0, x_195);
lean_ctor_set(x_196, 1, x_194);
x_197 = l_Lean_Elab_Term_throwError___rarg(x_1, x_196, x_4, x_190);
return x_197;
}
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_210; 
x_202 = lean_ctor_get(x_188, 1);
lean_inc(x_202);
lean_dec(x_188);
x_210 = l_Lean_Expr_getAppFn___main(x_186);
if (lean_obj_tag(x_210) == 4)
{
lean_object* x_211; lean_object* x_212; 
lean_dec(x_186);
lean_dec(x_4);
x_211 = lean_ctor_get(x_210, 0);
lean_inc(x_211);
lean_dec(x_210);
x_212 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_212, 0, x_211);
lean_ctor_set(x_212, 1, x_202);
return x_212;
}
else
{
lean_object* x_213; 
lean_dec(x_210);
x_213 = lean_box(0);
x_203 = x_213;
goto block_209;
}
block_209:
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
lean_dec(x_203);
x_204 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_204, 0, x_186);
x_205 = l_Lean_indentExpr(x_204);
x_206 = l___private_Init_Lean_Elab_StructInst_5__getStructName___closed__6;
x_207 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_207, 0, x_206);
lean_ctor_set(x_207, 1, x_205);
x_208 = l_Lean_Elab_Term_throwError___rarg(x_1, x_207, x_4, x_202);
return x_208;
}
}
}
else
{
uint8_t x_214; 
lean_dec(x_186);
lean_dec(x_4);
x_214 = !lean_is_exclusive(x_188);
if (x_214 == 0)
{
return x_188;
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; 
x_215 = lean_ctor_get(x_188, 0);
x_216 = lean_ctor_get(x_188, 1);
lean_inc(x_216);
lean_inc(x_215);
lean_dec(x_188);
x_217 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_217, 0, x_215);
lean_ctor_set(x_217, 1, x_216);
return x_217;
}
}
}
else
{
uint8_t x_218; 
lean_dec(x_4);
x_218 = !lean_is_exclusive(x_185);
if (x_218 == 0)
{
return x_185;
}
else
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; 
x_219 = lean_ctor_get(x_185, 0);
x_220 = lean_ctor_get(x_185, 1);
lean_inc(x_220);
lean_inc(x_219);
lean_dec(x_185);
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
lean_dec(x_4);
x_222 = !lean_is_exclusive(x_182);
if (x_222 == 0)
{
return x_182;
}
else
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; 
x_223 = lean_ctor_get(x_182, 0);
x_224 = lean_ctor_get(x_182, 1);
lean_inc(x_224);
lean_inc(x_223);
lean_dec(x_182);
x_225 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_225, 0, x_223);
lean_ctor_set(x_225, 1, x_224);
return x_225;
}
}
}
else
{
lean_object* x_226; 
lean_dec(x_3);
x_226 = lean_box(0);
x_81 = x_226;
goto block_87;
}
}
case 3:
{
lean_dec(x_88);
lean_free_object(x_77);
if (lean_obj_tag(x_3) == 2)
{
lean_object* x_227; lean_object* x_228; 
lean_dec(x_76);
x_227 = lean_ctor_get(x_3, 1);
lean_inc(x_227);
lean_dec(x_3);
lean_inc(x_4);
x_228 = l_Lean_Elab_Term_inferType(x_1, x_227, x_4, x_80);
if (lean_obj_tag(x_228) == 0)
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; 
x_229 = lean_ctor_get(x_228, 0);
lean_inc(x_229);
x_230 = lean_ctor_get(x_228, 1);
lean_inc(x_230);
lean_dec(x_228);
lean_inc(x_4);
x_231 = l_Lean_Elab_Term_whnf(x_1, x_229, x_4, x_230);
if (lean_obj_tag(x_231) == 0)
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; 
x_232 = lean_ctor_get(x_231, 0);
lean_inc(x_232);
x_233 = lean_ctor_get(x_231, 1);
lean_inc(x_233);
lean_dec(x_231);
x_234 = l_Lean_Elab_Term_tryPostponeIfMVar(x_232, x_4, x_233);
if (lean_obj_tag(x_234) == 0)
{
uint8_t x_235; 
x_235 = !lean_is_exclusive(x_234);
if (x_235 == 0)
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_245; 
x_236 = lean_ctor_get(x_234, 1);
x_237 = lean_ctor_get(x_234, 0);
lean_dec(x_237);
x_245 = l_Lean_Expr_getAppFn___main(x_232);
if (lean_obj_tag(x_245) == 4)
{
lean_object* x_246; 
lean_dec(x_232);
lean_dec(x_4);
x_246 = lean_ctor_get(x_245, 0);
lean_inc(x_246);
lean_dec(x_245);
lean_ctor_set(x_234, 0, x_246);
return x_234;
}
else
{
lean_object* x_247; 
lean_dec(x_245);
lean_free_object(x_234);
x_247 = lean_box(0);
x_238 = x_247;
goto block_244;
}
block_244:
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; 
lean_dec(x_238);
x_239 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_239, 0, x_232);
x_240 = l_Lean_indentExpr(x_239);
x_241 = l___private_Init_Lean_Elab_StructInst_5__getStructName___closed__6;
x_242 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_242, 0, x_241);
lean_ctor_set(x_242, 1, x_240);
x_243 = l_Lean_Elab_Term_throwError___rarg(x_1, x_242, x_4, x_236);
return x_243;
}
}
else
{
lean_object* x_248; lean_object* x_249; lean_object* x_256; 
x_248 = lean_ctor_get(x_234, 1);
lean_inc(x_248);
lean_dec(x_234);
x_256 = l_Lean_Expr_getAppFn___main(x_232);
if (lean_obj_tag(x_256) == 4)
{
lean_object* x_257; lean_object* x_258; 
lean_dec(x_232);
lean_dec(x_4);
x_257 = lean_ctor_get(x_256, 0);
lean_inc(x_257);
lean_dec(x_256);
x_258 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_258, 0, x_257);
lean_ctor_set(x_258, 1, x_248);
return x_258;
}
else
{
lean_object* x_259; 
lean_dec(x_256);
x_259 = lean_box(0);
x_249 = x_259;
goto block_255;
}
block_255:
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; 
lean_dec(x_249);
x_250 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_250, 0, x_232);
x_251 = l_Lean_indentExpr(x_250);
x_252 = l___private_Init_Lean_Elab_StructInst_5__getStructName___closed__6;
x_253 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_253, 0, x_252);
lean_ctor_set(x_253, 1, x_251);
x_254 = l_Lean_Elab_Term_throwError___rarg(x_1, x_253, x_4, x_248);
return x_254;
}
}
}
else
{
uint8_t x_260; 
lean_dec(x_232);
lean_dec(x_4);
x_260 = !lean_is_exclusive(x_234);
if (x_260 == 0)
{
return x_234;
}
else
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; 
x_261 = lean_ctor_get(x_234, 0);
x_262 = lean_ctor_get(x_234, 1);
lean_inc(x_262);
lean_inc(x_261);
lean_dec(x_234);
x_263 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_263, 0, x_261);
lean_ctor_set(x_263, 1, x_262);
return x_263;
}
}
}
else
{
uint8_t x_264; 
lean_dec(x_4);
x_264 = !lean_is_exclusive(x_231);
if (x_264 == 0)
{
return x_231;
}
else
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; 
x_265 = lean_ctor_get(x_231, 0);
x_266 = lean_ctor_get(x_231, 1);
lean_inc(x_266);
lean_inc(x_265);
lean_dec(x_231);
x_267 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_267, 0, x_265);
lean_ctor_set(x_267, 1, x_266);
return x_267;
}
}
}
else
{
uint8_t x_268; 
lean_dec(x_4);
x_268 = !lean_is_exclusive(x_228);
if (x_268 == 0)
{
return x_228;
}
else
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; 
x_269 = lean_ctor_get(x_228, 0);
x_270 = lean_ctor_get(x_228, 1);
lean_inc(x_270);
lean_inc(x_269);
lean_dec(x_228);
x_271 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_271, 0, x_269);
lean_ctor_set(x_271, 1, x_270);
return x_271;
}
}
}
else
{
lean_object* x_272; 
lean_dec(x_3);
x_272 = lean_box(0);
x_81 = x_272;
goto block_87;
}
}
case 4:
{
lean_object* x_273; 
lean_dec(x_76);
lean_dec(x_4);
lean_dec(x_3);
x_273 = lean_ctor_get(x_88, 0);
lean_inc(x_273);
lean_dec(x_88);
lean_ctor_set(x_77, 0, x_273);
return x_77;
}
case 5:
{
lean_dec(x_88);
lean_free_object(x_77);
if (lean_obj_tag(x_3) == 2)
{
lean_object* x_274; lean_object* x_275; 
lean_dec(x_76);
x_274 = lean_ctor_get(x_3, 1);
lean_inc(x_274);
lean_dec(x_3);
lean_inc(x_4);
x_275 = l_Lean_Elab_Term_inferType(x_1, x_274, x_4, x_80);
if (lean_obj_tag(x_275) == 0)
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; 
x_276 = lean_ctor_get(x_275, 0);
lean_inc(x_276);
x_277 = lean_ctor_get(x_275, 1);
lean_inc(x_277);
lean_dec(x_275);
lean_inc(x_4);
x_278 = l_Lean_Elab_Term_whnf(x_1, x_276, x_4, x_277);
if (lean_obj_tag(x_278) == 0)
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; 
x_279 = lean_ctor_get(x_278, 0);
lean_inc(x_279);
x_280 = lean_ctor_get(x_278, 1);
lean_inc(x_280);
lean_dec(x_278);
x_281 = l_Lean_Elab_Term_tryPostponeIfMVar(x_279, x_4, x_280);
if (lean_obj_tag(x_281) == 0)
{
uint8_t x_282; 
x_282 = !lean_is_exclusive(x_281);
if (x_282 == 0)
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_292; 
x_283 = lean_ctor_get(x_281, 1);
x_284 = lean_ctor_get(x_281, 0);
lean_dec(x_284);
x_292 = l_Lean_Expr_getAppFn___main(x_279);
if (lean_obj_tag(x_292) == 4)
{
lean_object* x_293; 
lean_dec(x_279);
lean_dec(x_4);
x_293 = lean_ctor_get(x_292, 0);
lean_inc(x_293);
lean_dec(x_292);
lean_ctor_set(x_281, 0, x_293);
return x_281;
}
else
{
lean_object* x_294; 
lean_dec(x_292);
lean_free_object(x_281);
x_294 = lean_box(0);
x_285 = x_294;
goto block_291;
}
block_291:
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; 
lean_dec(x_285);
x_286 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_286, 0, x_279);
x_287 = l_Lean_indentExpr(x_286);
x_288 = l___private_Init_Lean_Elab_StructInst_5__getStructName___closed__6;
x_289 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_289, 0, x_288);
lean_ctor_set(x_289, 1, x_287);
x_290 = l_Lean_Elab_Term_throwError___rarg(x_1, x_289, x_4, x_283);
return x_290;
}
}
else
{
lean_object* x_295; lean_object* x_296; lean_object* x_303; 
x_295 = lean_ctor_get(x_281, 1);
lean_inc(x_295);
lean_dec(x_281);
x_303 = l_Lean_Expr_getAppFn___main(x_279);
if (lean_obj_tag(x_303) == 4)
{
lean_object* x_304; lean_object* x_305; 
lean_dec(x_279);
lean_dec(x_4);
x_304 = lean_ctor_get(x_303, 0);
lean_inc(x_304);
lean_dec(x_303);
x_305 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_305, 0, x_304);
lean_ctor_set(x_305, 1, x_295);
return x_305;
}
else
{
lean_object* x_306; 
lean_dec(x_303);
x_306 = lean_box(0);
x_296 = x_306;
goto block_302;
}
block_302:
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; 
lean_dec(x_296);
x_297 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_297, 0, x_279);
x_298 = l_Lean_indentExpr(x_297);
x_299 = l___private_Init_Lean_Elab_StructInst_5__getStructName___closed__6;
x_300 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_300, 0, x_299);
lean_ctor_set(x_300, 1, x_298);
x_301 = l_Lean_Elab_Term_throwError___rarg(x_1, x_300, x_4, x_295);
return x_301;
}
}
}
else
{
uint8_t x_307; 
lean_dec(x_279);
lean_dec(x_4);
x_307 = !lean_is_exclusive(x_281);
if (x_307 == 0)
{
return x_281;
}
else
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; 
x_308 = lean_ctor_get(x_281, 0);
x_309 = lean_ctor_get(x_281, 1);
lean_inc(x_309);
lean_inc(x_308);
lean_dec(x_281);
x_310 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_310, 0, x_308);
lean_ctor_set(x_310, 1, x_309);
return x_310;
}
}
}
else
{
uint8_t x_311; 
lean_dec(x_4);
x_311 = !lean_is_exclusive(x_278);
if (x_311 == 0)
{
return x_278;
}
else
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; 
x_312 = lean_ctor_get(x_278, 0);
x_313 = lean_ctor_get(x_278, 1);
lean_inc(x_313);
lean_inc(x_312);
lean_dec(x_278);
x_314 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_314, 0, x_312);
lean_ctor_set(x_314, 1, x_313);
return x_314;
}
}
}
else
{
uint8_t x_315; 
lean_dec(x_4);
x_315 = !lean_is_exclusive(x_275);
if (x_315 == 0)
{
return x_275;
}
else
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; 
x_316 = lean_ctor_get(x_275, 0);
x_317 = lean_ctor_get(x_275, 1);
lean_inc(x_317);
lean_inc(x_316);
lean_dec(x_275);
x_318 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_318, 0, x_316);
lean_ctor_set(x_318, 1, x_317);
return x_318;
}
}
}
else
{
lean_object* x_319; 
lean_dec(x_3);
x_319 = lean_box(0);
x_81 = x_319;
goto block_87;
}
}
case 6:
{
lean_dec(x_88);
lean_free_object(x_77);
if (lean_obj_tag(x_3) == 2)
{
lean_object* x_320; lean_object* x_321; 
lean_dec(x_76);
x_320 = lean_ctor_get(x_3, 1);
lean_inc(x_320);
lean_dec(x_3);
lean_inc(x_4);
x_321 = l_Lean_Elab_Term_inferType(x_1, x_320, x_4, x_80);
if (lean_obj_tag(x_321) == 0)
{
lean_object* x_322; lean_object* x_323; lean_object* x_324; 
x_322 = lean_ctor_get(x_321, 0);
lean_inc(x_322);
x_323 = lean_ctor_get(x_321, 1);
lean_inc(x_323);
lean_dec(x_321);
lean_inc(x_4);
x_324 = l_Lean_Elab_Term_whnf(x_1, x_322, x_4, x_323);
if (lean_obj_tag(x_324) == 0)
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; 
x_325 = lean_ctor_get(x_324, 0);
lean_inc(x_325);
x_326 = lean_ctor_get(x_324, 1);
lean_inc(x_326);
lean_dec(x_324);
x_327 = l_Lean_Elab_Term_tryPostponeIfMVar(x_325, x_4, x_326);
if (lean_obj_tag(x_327) == 0)
{
uint8_t x_328; 
x_328 = !lean_is_exclusive(x_327);
if (x_328 == 0)
{
lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_338; 
x_329 = lean_ctor_get(x_327, 1);
x_330 = lean_ctor_get(x_327, 0);
lean_dec(x_330);
x_338 = l_Lean_Expr_getAppFn___main(x_325);
if (lean_obj_tag(x_338) == 4)
{
lean_object* x_339; 
lean_dec(x_325);
lean_dec(x_4);
x_339 = lean_ctor_get(x_338, 0);
lean_inc(x_339);
lean_dec(x_338);
lean_ctor_set(x_327, 0, x_339);
return x_327;
}
else
{
lean_object* x_340; 
lean_dec(x_338);
lean_free_object(x_327);
x_340 = lean_box(0);
x_331 = x_340;
goto block_337;
}
block_337:
{
lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; 
lean_dec(x_331);
x_332 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_332, 0, x_325);
x_333 = l_Lean_indentExpr(x_332);
x_334 = l___private_Init_Lean_Elab_StructInst_5__getStructName___closed__6;
x_335 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_335, 0, x_334);
lean_ctor_set(x_335, 1, x_333);
x_336 = l_Lean_Elab_Term_throwError___rarg(x_1, x_335, x_4, x_329);
return x_336;
}
}
else
{
lean_object* x_341; lean_object* x_342; lean_object* x_349; 
x_341 = lean_ctor_get(x_327, 1);
lean_inc(x_341);
lean_dec(x_327);
x_349 = l_Lean_Expr_getAppFn___main(x_325);
if (lean_obj_tag(x_349) == 4)
{
lean_object* x_350; lean_object* x_351; 
lean_dec(x_325);
lean_dec(x_4);
x_350 = lean_ctor_get(x_349, 0);
lean_inc(x_350);
lean_dec(x_349);
x_351 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_351, 0, x_350);
lean_ctor_set(x_351, 1, x_341);
return x_351;
}
else
{
lean_object* x_352; 
lean_dec(x_349);
x_352 = lean_box(0);
x_342 = x_352;
goto block_348;
}
block_348:
{
lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; 
lean_dec(x_342);
x_343 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_343, 0, x_325);
x_344 = l_Lean_indentExpr(x_343);
x_345 = l___private_Init_Lean_Elab_StructInst_5__getStructName___closed__6;
x_346 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_346, 0, x_345);
lean_ctor_set(x_346, 1, x_344);
x_347 = l_Lean_Elab_Term_throwError___rarg(x_1, x_346, x_4, x_341);
return x_347;
}
}
}
else
{
uint8_t x_353; 
lean_dec(x_325);
lean_dec(x_4);
x_353 = !lean_is_exclusive(x_327);
if (x_353 == 0)
{
return x_327;
}
else
{
lean_object* x_354; lean_object* x_355; lean_object* x_356; 
x_354 = lean_ctor_get(x_327, 0);
x_355 = lean_ctor_get(x_327, 1);
lean_inc(x_355);
lean_inc(x_354);
lean_dec(x_327);
x_356 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_356, 0, x_354);
lean_ctor_set(x_356, 1, x_355);
return x_356;
}
}
}
else
{
uint8_t x_357; 
lean_dec(x_4);
x_357 = !lean_is_exclusive(x_324);
if (x_357 == 0)
{
return x_324;
}
else
{
lean_object* x_358; lean_object* x_359; lean_object* x_360; 
x_358 = lean_ctor_get(x_324, 0);
x_359 = lean_ctor_get(x_324, 1);
lean_inc(x_359);
lean_inc(x_358);
lean_dec(x_324);
x_360 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_360, 0, x_358);
lean_ctor_set(x_360, 1, x_359);
return x_360;
}
}
}
else
{
uint8_t x_361; 
lean_dec(x_4);
x_361 = !lean_is_exclusive(x_321);
if (x_361 == 0)
{
return x_321;
}
else
{
lean_object* x_362; lean_object* x_363; lean_object* x_364; 
x_362 = lean_ctor_get(x_321, 0);
x_363 = lean_ctor_get(x_321, 1);
lean_inc(x_363);
lean_inc(x_362);
lean_dec(x_321);
x_364 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_364, 0, x_362);
lean_ctor_set(x_364, 1, x_363);
return x_364;
}
}
}
else
{
lean_object* x_365; 
lean_dec(x_3);
x_365 = lean_box(0);
x_81 = x_365;
goto block_87;
}
}
case 7:
{
lean_dec(x_88);
lean_free_object(x_77);
if (lean_obj_tag(x_3) == 2)
{
lean_object* x_366; lean_object* x_367; 
lean_dec(x_76);
x_366 = lean_ctor_get(x_3, 1);
lean_inc(x_366);
lean_dec(x_3);
lean_inc(x_4);
x_367 = l_Lean_Elab_Term_inferType(x_1, x_366, x_4, x_80);
if (lean_obj_tag(x_367) == 0)
{
lean_object* x_368; lean_object* x_369; lean_object* x_370; 
x_368 = lean_ctor_get(x_367, 0);
lean_inc(x_368);
x_369 = lean_ctor_get(x_367, 1);
lean_inc(x_369);
lean_dec(x_367);
lean_inc(x_4);
x_370 = l_Lean_Elab_Term_whnf(x_1, x_368, x_4, x_369);
if (lean_obj_tag(x_370) == 0)
{
lean_object* x_371; lean_object* x_372; lean_object* x_373; 
x_371 = lean_ctor_get(x_370, 0);
lean_inc(x_371);
x_372 = lean_ctor_get(x_370, 1);
lean_inc(x_372);
lean_dec(x_370);
x_373 = l_Lean_Elab_Term_tryPostponeIfMVar(x_371, x_4, x_372);
if (lean_obj_tag(x_373) == 0)
{
uint8_t x_374; 
x_374 = !lean_is_exclusive(x_373);
if (x_374 == 0)
{
lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_384; 
x_375 = lean_ctor_get(x_373, 1);
x_376 = lean_ctor_get(x_373, 0);
lean_dec(x_376);
x_384 = l_Lean_Expr_getAppFn___main(x_371);
if (lean_obj_tag(x_384) == 4)
{
lean_object* x_385; 
lean_dec(x_371);
lean_dec(x_4);
x_385 = lean_ctor_get(x_384, 0);
lean_inc(x_385);
lean_dec(x_384);
lean_ctor_set(x_373, 0, x_385);
return x_373;
}
else
{
lean_object* x_386; 
lean_dec(x_384);
lean_free_object(x_373);
x_386 = lean_box(0);
x_377 = x_386;
goto block_383;
}
block_383:
{
lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; 
lean_dec(x_377);
x_378 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_378, 0, x_371);
x_379 = l_Lean_indentExpr(x_378);
x_380 = l___private_Init_Lean_Elab_StructInst_5__getStructName___closed__6;
x_381 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_381, 0, x_380);
lean_ctor_set(x_381, 1, x_379);
x_382 = l_Lean_Elab_Term_throwError___rarg(x_1, x_381, x_4, x_375);
return x_382;
}
}
else
{
lean_object* x_387; lean_object* x_388; lean_object* x_395; 
x_387 = lean_ctor_get(x_373, 1);
lean_inc(x_387);
lean_dec(x_373);
x_395 = l_Lean_Expr_getAppFn___main(x_371);
if (lean_obj_tag(x_395) == 4)
{
lean_object* x_396; lean_object* x_397; 
lean_dec(x_371);
lean_dec(x_4);
x_396 = lean_ctor_get(x_395, 0);
lean_inc(x_396);
lean_dec(x_395);
x_397 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_397, 0, x_396);
lean_ctor_set(x_397, 1, x_387);
return x_397;
}
else
{
lean_object* x_398; 
lean_dec(x_395);
x_398 = lean_box(0);
x_388 = x_398;
goto block_394;
}
block_394:
{
lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; 
lean_dec(x_388);
x_389 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_389, 0, x_371);
x_390 = l_Lean_indentExpr(x_389);
x_391 = l___private_Init_Lean_Elab_StructInst_5__getStructName___closed__6;
x_392 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_392, 0, x_391);
lean_ctor_set(x_392, 1, x_390);
x_393 = l_Lean_Elab_Term_throwError___rarg(x_1, x_392, x_4, x_387);
return x_393;
}
}
}
else
{
uint8_t x_399; 
lean_dec(x_371);
lean_dec(x_4);
x_399 = !lean_is_exclusive(x_373);
if (x_399 == 0)
{
return x_373;
}
else
{
lean_object* x_400; lean_object* x_401; lean_object* x_402; 
x_400 = lean_ctor_get(x_373, 0);
x_401 = lean_ctor_get(x_373, 1);
lean_inc(x_401);
lean_inc(x_400);
lean_dec(x_373);
x_402 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_402, 0, x_400);
lean_ctor_set(x_402, 1, x_401);
return x_402;
}
}
}
else
{
uint8_t x_403; 
lean_dec(x_4);
x_403 = !lean_is_exclusive(x_370);
if (x_403 == 0)
{
return x_370;
}
else
{
lean_object* x_404; lean_object* x_405; lean_object* x_406; 
x_404 = lean_ctor_get(x_370, 0);
x_405 = lean_ctor_get(x_370, 1);
lean_inc(x_405);
lean_inc(x_404);
lean_dec(x_370);
x_406 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_406, 0, x_404);
lean_ctor_set(x_406, 1, x_405);
return x_406;
}
}
}
else
{
uint8_t x_407; 
lean_dec(x_4);
x_407 = !lean_is_exclusive(x_367);
if (x_407 == 0)
{
return x_367;
}
else
{
lean_object* x_408; lean_object* x_409; lean_object* x_410; 
x_408 = lean_ctor_get(x_367, 0);
x_409 = lean_ctor_get(x_367, 1);
lean_inc(x_409);
lean_inc(x_408);
lean_dec(x_367);
x_410 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_410, 0, x_408);
lean_ctor_set(x_410, 1, x_409);
return x_410;
}
}
}
else
{
lean_object* x_411; 
lean_dec(x_3);
x_411 = lean_box(0);
x_81 = x_411;
goto block_87;
}
}
case 8:
{
lean_dec(x_88);
lean_free_object(x_77);
if (lean_obj_tag(x_3) == 2)
{
lean_object* x_412; lean_object* x_413; 
lean_dec(x_76);
x_412 = lean_ctor_get(x_3, 1);
lean_inc(x_412);
lean_dec(x_3);
lean_inc(x_4);
x_413 = l_Lean_Elab_Term_inferType(x_1, x_412, x_4, x_80);
if (lean_obj_tag(x_413) == 0)
{
lean_object* x_414; lean_object* x_415; lean_object* x_416; 
x_414 = lean_ctor_get(x_413, 0);
lean_inc(x_414);
x_415 = lean_ctor_get(x_413, 1);
lean_inc(x_415);
lean_dec(x_413);
lean_inc(x_4);
x_416 = l_Lean_Elab_Term_whnf(x_1, x_414, x_4, x_415);
if (lean_obj_tag(x_416) == 0)
{
lean_object* x_417; lean_object* x_418; lean_object* x_419; 
x_417 = lean_ctor_get(x_416, 0);
lean_inc(x_417);
x_418 = lean_ctor_get(x_416, 1);
lean_inc(x_418);
lean_dec(x_416);
x_419 = l_Lean_Elab_Term_tryPostponeIfMVar(x_417, x_4, x_418);
if (lean_obj_tag(x_419) == 0)
{
uint8_t x_420; 
x_420 = !lean_is_exclusive(x_419);
if (x_420 == 0)
{
lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_430; 
x_421 = lean_ctor_get(x_419, 1);
x_422 = lean_ctor_get(x_419, 0);
lean_dec(x_422);
x_430 = l_Lean_Expr_getAppFn___main(x_417);
if (lean_obj_tag(x_430) == 4)
{
lean_object* x_431; 
lean_dec(x_417);
lean_dec(x_4);
x_431 = lean_ctor_get(x_430, 0);
lean_inc(x_431);
lean_dec(x_430);
lean_ctor_set(x_419, 0, x_431);
return x_419;
}
else
{
lean_object* x_432; 
lean_dec(x_430);
lean_free_object(x_419);
x_432 = lean_box(0);
x_423 = x_432;
goto block_429;
}
block_429:
{
lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; 
lean_dec(x_423);
x_424 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_424, 0, x_417);
x_425 = l_Lean_indentExpr(x_424);
x_426 = l___private_Init_Lean_Elab_StructInst_5__getStructName___closed__6;
x_427 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_427, 0, x_426);
lean_ctor_set(x_427, 1, x_425);
x_428 = l_Lean_Elab_Term_throwError___rarg(x_1, x_427, x_4, x_421);
return x_428;
}
}
else
{
lean_object* x_433; lean_object* x_434; lean_object* x_441; 
x_433 = lean_ctor_get(x_419, 1);
lean_inc(x_433);
lean_dec(x_419);
x_441 = l_Lean_Expr_getAppFn___main(x_417);
if (lean_obj_tag(x_441) == 4)
{
lean_object* x_442; lean_object* x_443; 
lean_dec(x_417);
lean_dec(x_4);
x_442 = lean_ctor_get(x_441, 0);
lean_inc(x_442);
lean_dec(x_441);
x_443 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_443, 0, x_442);
lean_ctor_set(x_443, 1, x_433);
return x_443;
}
else
{
lean_object* x_444; 
lean_dec(x_441);
x_444 = lean_box(0);
x_434 = x_444;
goto block_440;
}
block_440:
{
lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; 
lean_dec(x_434);
x_435 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_435, 0, x_417);
x_436 = l_Lean_indentExpr(x_435);
x_437 = l___private_Init_Lean_Elab_StructInst_5__getStructName___closed__6;
x_438 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_438, 0, x_437);
lean_ctor_set(x_438, 1, x_436);
x_439 = l_Lean_Elab_Term_throwError___rarg(x_1, x_438, x_4, x_433);
return x_439;
}
}
}
else
{
uint8_t x_445; 
lean_dec(x_417);
lean_dec(x_4);
x_445 = !lean_is_exclusive(x_419);
if (x_445 == 0)
{
return x_419;
}
else
{
lean_object* x_446; lean_object* x_447; lean_object* x_448; 
x_446 = lean_ctor_get(x_419, 0);
x_447 = lean_ctor_get(x_419, 1);
lean_inc(x_447);
lean_inc(x_446);
lean_dec(x_419);
x_448 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_448, 0, x_446);
lean_ctor_set(x_448, 1, x_447);
return x_448;
}
}
}
else
{
uint8_t x_449; 
lean_dec(x_4);
x_449 = !lean_is_exclusive(x_416);
if (x_449 == 0)
{
return x_416;
}
else
{
lean_object* x_450; lean_object* x_451; lean_object* x_452; 
x_450 = lean_ctor_get(x_416, 0);
x_451 = lean_ctor_get(x_416, 1);
lean_inc(x_451);
lean_inc(x_450);
lean_dec(x_416);
x_452 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_452, 0, x_450);
lean_ctor_set(x_452, 1, x_451);
return x_452;
}
}
}
else
{
uint8_t x_453; 
lean_dec(x_4);
x_453 = !lean_is_exclusive(x_413);
if (x_453 == 0)
{
return x_413;
}
else
{
lean_object* x_454; lean_object* x_455; lean_object* x_456; 
x_454 = lean_ctor_get(x_413, 0);
x_455 = lean_ctor_get(x_413, 1);
lean_inc(x_455);
lean_inc(x_454);
lean_dec(x_413);
x_456 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_456, 0, x_454);
lean_ctor_set(x_456, 1, x_455);
return x_456;
}
}
}
else
{
lean_object* x_457; 
lean_dec(x_3);
x_457 = lean_box(0);
x_81 = x_457;
goto block_87;
}
}
case 9:
{
lean_dec(x_88);
lean_free_object(x_77);
if (lean_obj_tag(x_3) == 2)
{
lean_object* x_458; lean_object* x_459; 
lean_dec(x_76);
x_458 = lean_ctor_get(x_3, 1);
lean_inc(x_458);
lean_dec(x_3);
lean_inc(x_4);
x_459 = l_Lean_Elab_Term_inferType(x_1, x_458, x_4, x_80);
if (lean_obj_tag(x_459) == 0)
{
lean_object* x_460; lean_object* x_461; lean_object* x_462; 
x_460 = lean_ctor_get(x_459, 0);
lean_inc(x_460);
x_461 = lean_ctor_get(x_459, 1);
lean_inc(x_461);
lean_dec(x_459);
lean_inc(x_4);
x_462 = l_Lean_Elab_Term_whnf(x_1, x_460, x_4, x_461);
if (lean_obj_tag(x_462) == 0)
{
lean_object* x_463; lean_object* x_464; lean_object* x_465; 
x_463 = lean_ctor_get(x_462, 0);
lean_inc(x_463);
x_464 = lean_ctor_get(x_462, 1);
lean_inc(x_464);
lean_dec(x_462);
x_465 = l_Lean_Elab_Term_tryPostponeIfMVar(x_463, x_4, x_464);
if (lean_obj_tag(x_465) == 0)
{
uint8_t x_466; 
x_466 = !lean_is_exclusive(x_465);
if (x_466 == 0)
{
lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_476; 
x_467 = lean_ctor_get(x_465, 1);
x_468 = lean_ctor_get(x_465, 0);
lean_dec(x_468);
x_476 = l_Lean_Expr_getAppFn___main(x_463);
if (lean_obj_tag(x_476) == 4)
{
lean_object* x_477; 
lean_dec(x_463);
lean_dec(x_4);
x_477 = lean_ctor_get(x_476, 0);
lean_inc(x_477);
lean_dec(x_476);
lean_ctor_set(x_465, 0, x_477);
return x_465;
}
else
{
lean_object* x_478; 
lean_dec(x_476);
lean_free_object(x_465);
x_478 = lean_box(0);
x_469 = x_478;
goto block_475;
}
block_475:
{
lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; 
lean_dec(x_469);
x_470 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_470, 0, x_463);
x_471 = l_Lean_indentExpr(x_470);
x_472 = l___private_Init_Lean_Elab_StructInst_5__getStructName___closed__6;
x_473 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_473, 0, x_472);
lean_ctor_set(x_473, 1, x_471);
x_474 = l_Lean_Elab_Term_throwError___rarg(x_1, x_473, x_4, x_467);
return x_474;
}
}
else
{
lean_object* x_479; lean_object* x_480; lean_object* x_487; 
x_479 = lean_ctor_get(x_465, 1);
lean_inc(x_479);
lean_dec(x_465);
x_487 = l_Lean_Expr_getAppFn___main(x_463);
if (lean_obj_tag(x_487) == 4)
{
lean_object* x_488; lean_object* x_489; 
lean_dec(x_463);
lean_dec(x_4);
x_488 = lean_ctor_get(x_487, 0);
lean_inc(x_488);
lean_dec(x_487);
x_489 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_489, 0, x_488);
lean_ctor_set(x_489, 1, x_479);
return x_489;
}
else
{
lean_object* x_490; 
lean_dec(x_487);
x_490 = lean_box(0);
x_480 = x_490;
goto block_486;
}
block_486:
{
lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; 
lean_dec(x_480);
x_481 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_481, 0, x_463);
x_482 = l_Lean_indentExpr(x_481);
x_483 = l___private_Init_Lean_Elab_StructInst_5__getStructName___closed__6;
x_484 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_484, 0, x_483);
lean_ctor_set(x_484, 1, x_482);
x_485 = l_Lean_Elab_Term_throwError___rarg(x_1, x_484, x_4, x_479);
return x_485;
}
}
}
else
{
uint8_t x_491; 
lean_dec(x_463);
lean_dec(x_4);
x_491 = !lean_is_exclusive(x_465);
if (x_491 == 0)
{
return x_465;
}
else
{
lean_object* x_492; lean_object* x_493; lean_object* x_494; 
x_492 = lean_ctor_get(x_465, 0);
x_493 = lean_ctor_get(x_465, 1);
lean_inc(x_493);
lean_inc(x_492);
lean_dec(x_465);
x_494 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_494, 0, x_492);
lean_ctor_set(x_494, 1, x_493);
return x_494;
}
}
}
else
{
uint8_t x_495; 
lean_dec(x_4);
x_495 = !lean_is_exclusive(x_462);
if (x_495 == 0)
{
return x_462;
}
else
{
lean_object* x_496; lean_object* x_497; lean_object* x_498; 
x_496 = lean_ctor_get(x_462, 0);
x_497 = lean_ctor_get(x_462, 1);
lean_inc(x_497);
lean_inc(x_496);
lean_dec(x_462);
x_498 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_498, 0, x_496);
lean_ctor_set(x_498, 1, x_497);
return x_498;
}
}
}
else
{
uint8_t x_499; 
lean_dec(x_4);
x_499 = !lean_is_exclusive(x_459);
if (x_499 == 0)
{
return x_459;
}
else
{
lean_object* x_500; lean_object* x_501; lean_object* x_502; 
x_500 = lean_ctor_get(x_459, 0);
x_501 = lean_ctor_get(x_459, 1);
lean_inc(x_501);
lean_inc(x_500);
lean_dec(x_459);
x_502 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_502, 0, x_500);
lean_ctor_set(x_502, 1, x_501);
return x_502;
}
}
}
else
{
lean_object* x_503; 
lean_dec(x_3);
x_503 = lean_box(0);
x_81 = x_503;
goto block_87;
}
}
case 10:
{
lean_dec(x_88);
lean_free_object(x_77);
if (lean_obj_tag(x_3) == 2)
{
lean_object* x_504; lean_object* x_505; 
lean_dec(x_76);
x_504 = lean_ctor_get(x_3, 1);
lean_inc(x_504);
lean_dec(x_3);
lean_inc(x_4);
x_505 = l_Lean_Elab_Term_inferType(x_1, x_504, x_4, x_80);
if (lean_obj_tag(x_505) == 0)
{
lean_object* x_506; lean_object* x_507; lean_object* x_508; 
x_506 = lean_ctor_get(x_505, 0);
lean_inc(x_506);
x_507 = lean_ctor_get(x_505, 1);
lean_inc(x_507);
lean_dec(x_505);
lean_inc(x_4);
x_508 = l_Lean_Elab_Term_whnf(x_1, x_506, x_4, x_507);
if (lean_obj_tag(x_508) == 0)
{
lean_object* x_509; lean_object* x_510; lean_object* x_511; 
x_509 = lean_ctor_get(x_508, 0);
lean_inc(x_509);
x_510 = lean_ctor_get(x_508, 1);
lean_inc(x_510);
lean_dec(x_508);
x_511 = l_Lean_Elab_Term_tryPostponeIfMVar(x_509, x_4, x_510);
if (lean_obj_tag(x_511) == 0)
{
uint8_t x_512; 
x_512 = !lean_is_exclusive(x_511);
if (x_512 == 0)
{
lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_522; 
x_513 = lean_ctor_get(x_511, 1);
x_514 = lean_ctor_get(x_511, 0);
lean_dec(x_514);
x_522 = l_Lean_Expr_getAppFn___main(x_509);
if (lean_obj_tag(x_522) == 4)
{
lean_object* x_523; 
lean_dec(x_509);
lean_dec(x_4);
x_523 = lean_ctor_get(x_522, 0);
lean_inc(x_523);
lean_dec(x_522);
lean_ctor_set(x_511, 0, x_523);
return x_511;
}
else
{
lean_object* x_524; 
lean_dec(x_522);
lean_free_object(x_511);
x_524 = lean_box(0);
x_515 = x_524;
goto block_521;
}
block_521:
{
lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; 
lean_dec(x_515);
x_516 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_516, 0, x_509);
x_517 = l_Lean_indentExpr(x_516);
x_518 = l___private_Init_Lean_Elab_StructInst_5__getStructName___closed__6;
x_519 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_519, 0, x_518);
lean_ctor_set(x_519, 1, x_517);
x_520 = l_Lean_Elab_Term_throwError___rarg(x_1, x_519, x_4, x_513);
return x_520;
}
}
else
{
lean_object* x_525; lean_object* x_526; lean_object* x_533; 
x_525 = lean_ctor_get(x_511, 1);
lean_inc(x_525);
lean_dec(x_511);
x_533 = l_Lean_Expr_getAppFn___main(x_509);
if (lean_obj_tag(x_533) == 4)
{
lean_object* x_534; lean_object* x_535; 
lean_dec(x_509);
lean_dec(x_4);
x_534 = lean_ctor_get(x_533, 0);
lean_inc(x_534);
lean_dec(x_533);
x_535 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_535, 0, x_534);
lean_ctor_set(x_535, 1, x_525);
return x_535;
}
else
{
lean_object* x_536; 
lean_dec(x_533);
x_536 = lean_box(0);
x_526 = x_536;
goto block_532;
}
block_532:
{
lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; 
lean_dec(x_526);
x_527 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_527, 0, x_509);
x_528 = l_Lean_indentExpr(x_527);
x_529 = l___private_Init_Lean_Elab_StructInst_5__getStructName___closed__6;
x_530 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_530, 0, x_529);
lean_ctor_set(x_530, 1, x_528);
x_531 = l_Lean_Elab_Term_throwError___rarg(x_1, x_530, x_4, x_525);
return x_531;
}
}
}
else
{
uint8_t x_537; 
lean_dec(x_509);
lean_dec(x_4);
x_537 = !lean_is_exclusive(x_511);
if (x_537 == 0)
{
return x_511;
}
else
{
lean_object* x_538; lean_object* x_539; lean_object* x_540; 
x_538 = lean_ctor_get(x_511, 0);
x_539 = lean_ctor_get(x_511, 1);
lean_inc(x_539);
lean_inc(x_538);
lean_dec(x_511);
x_540 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_540, 0, x_538);
lean_ctor_set(x_540, 1, x_539);
return x_540;
}
}
}
else
{
uint8_t x_541; 
lean_dec(x_4);
x_541 = !lean_is_exclusive(x_508);
if (x_541 == 0)
{
return x_508;
}
else
{
lean_object* x_542; lean_object* x_543; lean_object* x_544; 
x_542 = lean_ctor_get(x_508, 0);
x_543 = lean_ctor_get(x_508, 1);
lean_inc(x_543);
lean_inc(x_542);
lean_dec(x_508);
x_544 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_544, 0, x_542);
lean_ctor_set(x_544, 1, x_543);
return x_544;
}
}
}
else
{
uint8_t x_545; 
lean_dec(x_4);
x_545 = !lean_is_exclusive(x_505);
if (x_545 == 0)
{
return x_505;
}
else
{
lean_object* x_546; lean_object* x_547; lean_object* x_548; 
x_546 = lean_ctor_get(x_505, 0);
x_547 = lean_ctor_get(x_505, 1);
lean_inc(x_547);
lean_inc(x_546);
lean_dec(x_505);
x_548 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_548, 0, x_546);
lean_ctor_set(x_548, 1, x_547);
return x_548;
}
}
}
else
{
lean_object* x_549; 
lean_dec(x_3);
x_549 = lean_box(0);
x_81 = x_549;
goto block_87;
}
}
case 11:
{
lean_dec(x_88);
lean_free_object(x_77);
if (lean_obj_tag(x_3) == 2)
{
lean_object* x_550; lean_object* x_551; 
lean_dec(x_76);
x_550 = lean_ctor_get(x_3, 1);
lean_inc(x_550);
lean_dec(x_3);
lean_inc(x_4);
x_551 = l_Lean_Elab_Term_inferType(x_1, x_550, x_4, x_80);
if (lean_obj_tag(x_551) == 0)
{
lean_object* x_552; lean_object* x_553; lean_object* x_554; 
x_552 = lean_ctor_get(x_551, 0);
lean_inc(x_552);
x_553 = lean_ctor_get(x_551, 1);
lean_inc(x_553);
lean_dec(x_551);
lean_inc(x_4);
x_554 = l_Lean_Elab_Term_whnf(x_1, x_552, x_4, x_553);
if (lean_obj_tag(x_554) == 0)
{
lean_object* x_555; lean_object* x_556; lean_object* x_557; 
x_555 = lean_ctor_get(x_554, 0);
lean_inc(x_555);
x_556 = lean_ctor_get(x_554, 1);
lean_inc(x_556);
lean_dec(x_554);
x_557 = l_Lean_Elab_Term_tryPostponeIfMVar(x_555, x_4, x_556);
if (lean_obj_tag(x_557) == 0)
{
uint8_t x_558; 
x_558 = !lean_is_exclusive(x_557);
if (x_558 == 0)
{
lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_568; 
x_559 = lean_ctor_get(x_557, 1);
x_560 = lean_ctor_get(x_557, 0);
lean_dec(x_560);
x_568 = l_Lean_Expr_getAppFn___main(x_555);
if (lean_obj_tag(x_568) == 4)
{
lean_object* x_569; 
lean_dec(x_555);
lean_dec(x_4);
x_569 = lean_ctor_get(x_568, 0);
lean_inc(x_569);
lean_dec(x_568);
lean_ctor_set(x_557, 0, x_569);
return x_557;
}
else
{
lean_object* x_570; 
lean_dec(x_568);
lean_free_object(x_557);
x_570 = lean_box(0);
x_561 = x_570;
goto block_567;
}
block_567:
{
lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; 
lean_dec(x_561);
x_562 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_562, 0, x_555);
x_563 = l_Lean_indentExpr(x_562);
x_564 = l___private_Init_Lean_Elab_StructInst_5__getStructName___closed__6;
x_565 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_565, 0, x_564);
lean_ctor_set(x_565, 1, x_563);
x_566 = l_Lean_Elab_Term_throwError___rarg(x_1, x_565, x_4, x_559);
return x_566;
}
}
else
{
lean_object* x_571; lean_object* x_572; lean_object* x_579; 
x_571 = lean_ctor_get(x_557, 1);
lean_inc(x_571);
lean_dec(x_557);
x_579 = l_Lean_Expr_getAppFn___main(x_555);
if (lean_obj_tag(x_579) == 4)
{
lean_object* x_580; lean_object* x_581; 
lean_dec(x_555);
lean_dec(x_4);
x_580 = lean_ctor_get(x_579, 0);
lean_inc(x_580);
lean_dec(x_579);
x_581 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_581, 0, x_580);
lean_ctor_set(x_581, 1, x_571);
return x_581;
}
else
{
lean_object* x_582; 
lean_dec(x_579);
x_582 = lean_box(0);
x_572 = x_582;
goto block_578;
}
block_578:
{
lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; 
lean_dec(x_572);
x_573 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_573, 0, x_555);
x_574 = l_Lean_indentExpr(x_573);
x_575 = l___private_Init_Lean_Elab_StructInst_5__getStructName___closed__6;
x_576 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_576, 0, x_575);
lean_ctor_set(x_576, 1, x_574);
x_577 = l_Lean_Elab_Term_throwError___rarg(x_1, x_576, x_4, x_571);
return x_577;
}
}
}
else
{
uint8_t x_583; 
lean_dec(x_555);
lean_dec(x_4);
x_583 = !lean_is_exclusive(x_557);
if (x_583 == 0)
{
return x_557;
}
else
{
lean_object* x_584; lean_object* x_585; lean_object* x_586; 
x_584 = lean_ctor_get(x_557, 0);
x_585 = lean_ctor_get(x_557, 1);
lean_inc(x_585);
lean_inc(x_584);
lean_dec(x_557);
x_586 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_586, 0, x_584);
lean_ctor_set(x_586, 1, x_585);
return x_586;
}
}
}
else
{
uint8_t x_587; 
lean_dec(x_4);
x_587 = !lean_is_exclusive(x_554);
if (x_587 == 0)
{
return x_554;
}
else
{
lean_object* x_588; lean_object* x_589; lean_object* x_590; 
x_588 = lean_ctor_get(x_554, 0);
x_589 = lean_ctor_get(x_554, 1);
lean_inc(x_589);
lean_inc(x_588);
lean_dec(x_554);
x_590 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_590, 0, x_588);
lean_ctor_set(x_590, 1, x_589);
return x_590;
}
}
}
else
{
uint8_t x_591; 
lean_dec(x_4);
x_591 = !lean_is_exclusive(x_551);
if (x_591 == 0)
{
return x_551;
}
else
{
lean_object* x_592; lean_object* x_593; lean_object* x_594; 
x_592 = lean_ctor_get(x_551, 0);
x_593 = lean_ctor_get(x_551, 1);
lean_inc(x_593);
lean_inc(x_592);
lean_dec(x_551);
x_594 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_594, 0, x_592);
lean_ctor_set(x_594, 1, x_593);
return x_594;
}
}
}
else
{
lean_object* x_595; 
lean_dec(x_3);
x_595 = lean_box(0);
x_81 = x_595;
goto block_87;
}
}
default: 
{
lean_dec(x_88);
lean_free_object(x_77);
if (lean_obj_tag(x_3) == 2)
{
lean_object* x_596; lean_object* x_597; 
lean_dec(x_76);
x_596 = lean_ctor_get(x_3, 1);
lean_inc(x_596);
lean_dec(x_3);
lean_inc(x_4);
x_597 = l_Lean_Elab_Term_inferType(x_1, x_596, x_4, x_80);
if (lean_obj_tag(x_597) == 0)
{
lean_object* x_598; lean_object* x_599; lean_object* x_600; 
x_598 = lean_ctor_get(x_597, 0);
lean_inc(x_598);
x_599 = lean_ctor_get(x_597, 1);
lean_inc(x_599);
lean_dec(x_597);
lean_inc(x_4);
x_600 = l_Lean_Elab_Term_whnf(x_1, x_598, x_4, x_599);
if (lean_obj_tag(x_600) == 0)
{
lean_object* x_601; lean_object* x_602; lean_object* x_603; 
x_601 = lean_ctor_get(x_600, 0);
lean_inc(x_601);
x_602 = lean_ctor_get(x_600, 1);
lean_inc(x_602);
lean_dec(x_600);
x_603 = l_Lean_Elab_Term_tryPostponeIfMVar(x_601, x_4, x_602);
if (lean_obj_tag(x_603) == 0)
{
uint8_t x_604; 
x_604 = !lean_is_exclusive(x_603);
if (x_604 == 0)
{
lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_614; 
x_605 = lean_ctor_get(x_603, 1);
x_606 = lean_ctor_get(x_603, 0);
lean_dec(x_606);
x_614 = l_Lean_Expr_getAppFn___main(x_601);
if (lean_obj_tag(x_614) == 4)
{
lean_object* x_615; 
lean_dec(x_601);
lean_dec(x_4);
x_615 = lean_ctor_get(x_614, 0);
lean_inc(x_615);
lean_dec(x_614);
lean_ctor_set(x_603, 0, x_615);
return x_603;
}
else
{
lean_object* x_616; 
lean_dec(x_614);
lean_free_object(x_603);
x_616 = lean_box(0);
x_607 = x_616;
goto block_613;
}
block_613:
{
lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; 
lean_dec(x_607);
x_608 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_608, 0, x_601);
x_609 = l_Lean_indentExpr(x_608);
x_610 = l___private_Init_Lean_Elab_StructInst_5__getStructName___closed__6;
x_611 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_611, 0, x_610);
lean_ctor_set(x_611, 1, x_609);
x_612 = l_Lean_Elab_Term_throwError___rarg(x_1, x_611, x_4, x_605);
return x_612;
}
}
else
{
lean_object* x_617; lean_object* x_618; lean_object* x_625; 
x_617 = lean_ctor_get(x_603, 1);
lean_inc(x_617);
lean_dec(x_603);
x_625 = l_Lean_Expr_getAppFn___main(x_601);
if (lean_obj_tag(x_625) == 4)
{
lean_object* x_626; lean_object* x_627; 
lean_dec(x_601);
lean_dec(x_4);
x_626 = lean_ctor_get(x_625, 0);
lean_inc(x_626);
lean_dec(x_625);
x_627 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_627, 0, x_626);
lean_ctor_set(x_627, 1, x_617);
return x_627;
}
else
{
lean_object* x_628; 
lean_dec(x_625);
x_628 = lean_box(0);
x_618 = x_628;
goto block_624;
}
block_624:
{
lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; 
lean_dec(x_618);
x_619 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_619, 0, x_601);
x_620 = l_Lean_indentExpr(x_619);
x_621 = l___private_Init_Lean_Elab_StructInst_5__getStructName___closed__6;
x_622 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_622, 0, x_621);
lean_ctor_set(x_622, 1, x_620);
x_623 = l_Lean_Elab_Term_throwError___rarg(x_1, x_622, x_4, x_617);
return x_623;
}
}
}
else
{
uint8_t x_629; 
lean_dec(x_601);
lean_dec(x_4);
x_629 = !lean_is_exclusive(x_603);
if (x_629 == 0)
{
return x_603;
}
else
{
lean_object* x_630; lean_object* x_631; lean_object* x_632; 
x_630 = lean_ctor_get(x_603, 0);
x_631 = lean_ctor_get(x_603, 1);
lean_inc(x_631);
lean_inc(x_630);
lean_dec(x_603);
x_632 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_632, 0, x_630);
lean_ctor_set(x_632, 1, x_631);
return x_632;
}
}
}
else
{
uint8_t x_633; 
lean_dec(x_4);
x_633 = !lean_is_exclusive(x_600);
if (x_633 == 0)
{
return x_600;
}
else
{
lean_object* x_634; lean_object* x_635; lean_object* x_636; 
x_634 = lean_ctor_get(x_600, 0);
x_635 = lean_ctor_get(x_600, 1);
lean_inc(x_635);
lean_inc(x_634);
lean_dec(x_600);
x_636 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_636, 0, x_634);
lean_ctor_set(x_636, 1, x_635);
return x_636;
}
}
}
else
{
uint8_t x_637; 
lean_dec(x_4);
x_637 = !lean_is_exclusive(x_597);
if (x_637 == 0)
{
return x_597;
}
else
{
lean_object* x_638; lean_object* x_639; lean_object* x_640; 
x_638 = lean_ctor_get(x_597, 0);
x_639 = lean_ctor_get(x_597, 1);
lean_inc(x_639);
lean_inc(x_638);
lean_dec(x_597);
x_640 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_640, 0, x_638);
lean_ctor_set(x_640, 1, x_639);
return x_640;
}
}
}
else
{
lean_object* x_641; 
lean_dec(x_3);
x_641 = lean_box(0);
x_81 = x_641;
goto block_87;
}
}
}
block_87:
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_81);
x_82 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_82, 0, x_76);
x_83 = l_Lean_indentExpr(x_82);
x_84 = l___private_Init_Lean_Elab_StructInst_5__getStructName___closed__3;
x_85 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_83);
x_86 = l_Lean_Elab_Term_throwError___rarg(x_1, x_85, x_4, x_80);
return x_86;
}
}
else
{
lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_651; 
x_642 = lean_ctor_get(x_77, 0);
x_643 = lean_ctor_get(x_77, 1);
lean_inc(x_643);
lean_inc(x_642);
lean_dec(x_77);
x_651 = l_Lean_Expr_getAppFn___main(x_642);
lean_dec(x_642);
switch (lean_obj_tag(x_651)) {
case 0:
{
lean_dec(x_651);
if (lean_obj_tag(x_3) == 2)
{
lean_object* x_652; lean_object* x_653; 
lean_dec(x_76);
x_652 = lean_ctor_get(x_3, 1);
lean_inc(x_652);
lean_dec(x_3);
lean_inc(x_4);
x_653 = l_Lean_Elab_Term_inferType(x_1, x_652, x_4, x_643);
if (lean_obj_tag(x_653) == 0)
{
lean_object* x_654; lean_object* x_655; lean_object* x_656; 
x_654 = lean_ctor_get(x_653, 0);
lean_inc(x_654);
x_655 = lean_ctor_get(x_653, 1);
lean_inc(x_655);
lean_dec(x_653);
lean_inc(x_4);
x_656 = l_Lean_Elab_Term_whnf(x_1, x_654, x_4, x_655);
if (lean_obj_tag(x_656) == 0)
{
lean_object* x_657; lean_object* x_658; lean_object* x_659; 
x_657 = lean_ctor_get(x_656, 0);
lean_inc(x_657);
x_658 = lean_ctor_get(x_656, 1);
lean_inc(x_658);
lean_dec(x_656);
x_659 = l_Lean_Elab_Term_tryPostponeIfMVar(x_657, x_4, x_658);
if (lean_obj_tag(x_659) == 0)
{
lean_object* x_660; lean_object* x_661; lean_object* x_662; lean_object* x_669; 
x_660 = lean_ctor_get(x_659, 1);
lean_inc(x_660);
if (lean_is_exclusive(x_659)) {
 lean_ctor_release(x_659, 0);
 lean_ctor_release(x_659, 1);
 x_661 = x_659;
} else {
 lean_dec_ref(x_659);
 x_661 = lean_box(0);
}
x_669 = l_Lean_Expr_getAppFn___main(x_657);
if (lean_obj_tag(x_669) == 4)
{
lean_object* x_670; lean_object* x_671; 
lean_dec(x_657);
lean_dec(x_4);
x_670 = lean_ctor_get(x_669, 0);
lean_inc(x_670);
lean_dec(x_669);
if (lean_is_scalar(x_661)) {
 x_671 = lean_alloc_ctor(0, 2, 0);
} else {
 x_671 = x_661;
}
lean_ctor_set(x_671, 0, x_670);
lean_ctor_set(x_671, 1, x_660);
return x_671;
}
else
{
lean_object* x_672; 
lean_dec(x_669);
lean_dec(x_661);
x_672 = lean_box(0);
x_662 = x_672;
goto block_668;
}
block_668:
{
lean_object* x_663; lean_object* x_664; lean_object* x_665; lean_object* x_666; lean_object* x_667; 
lean_dec(x_662);
x_663 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_663, 0, x_657);
x_664 = l_Lean_indentExpr(x_663);
x_665 = l___private_Init_Lean_Elab_StructInst_5__getStructName___closed__6;
x_666 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_666, 0, x_665);
lean_ctor_set(x_666, 1, x_664);
x_667 = l_Lean_Elab_Term_throwError___rarg(x_1, x_666, x_4, x_660);
return x_667;
}
}
else
{
lean_object* x_673; lean_object* x_674; lean_object* x_675; lean_object* x_676; 
lean_dec(x_657);
lean_dec(x_4);
x_673 = lean_ctor_get(x_659, 0);
lean_inc(x_673);
x_674 = lean_ctor_get(x_659, 1);
lean_inc(x_674);
if (lean_is_exclusive(x_659)) {
 lean_ctor_release(x_659, 0);
 lean_ctor_release(x_659, 1);
 x_675 = x_659;
} else {
 lean_dec_ref(x_659);
 x_675 = lean_box(0);
}
if (lean_is_scalar(x_675)) {
 x_676 = lean_alloc_ctor(1, 2, 0);
} else {
 x_676 = x_675;
}
lean_ctor_set(x_676, 0, x_673);
lean_ctor_set(x_676, 1, x_674);
return x_676;
}
}
else
{
lean_object* x_677; lean_object* x_678; lean_object* x_679; lean_object* x_680; 
lean_dec(x_4);
x_677 = lean_ctor_get(x_656, 0);
lean_inc(x_677);
x_678 = lean_ctor_get(x_656, 1);
lean_inc(x_678);
if (lean_is_exclusive(x_656)) {
 lean_ctor_release(x_656, 0);
 lean_ctor_release(x_656, 1);
 x_679 = x_656;
} else {
 lean_dec_ref(x_656);
 x_679 = lean_box(0);
}
if (lean_is_scalar(x_679)) {
 x_680 = lean_alloc_ctor(1, 2, 0);
} else {
 x_680 = x_679;
}
lean_ctor_set(x_680, 0, x_677);
lean_ctor_set(x_680, 1, x_678);
return x_680;
}
}
else
{
lean_object* x_681; lean_object* x_682; lean_object* x_683; lean_object* x_684; 
lean_dec(x_4);
x_681 = lean_ctor_get(x_653, 0);
lean_inc(x_681);
x_682 = lean_ctor_get(x_653, 1);
lean_inc(x_682);
if (lean_is_exclusive(x_653)) {
 lean_ctor_release(x_653, 0);
 lean_ctor_release(x_653, 1);
 x_683 = x_653;
} else {
 lean_dec_ref(x_653);
 x_683 = lean_box(0);
}
if (lean_is_scalar(x_683)) {
 x_684 = lean_alloc_ctor(1, 2, 0);
} else {
 x_684 = x_683;
}
lean_ctor_set(x_684, 0, x_681);
lean_ctor_set(x_684, 1, x_682);
return x_684;
}
}
else
{
lean_object* x_685; 
lean_dec(x_3);
x_685 = lean_box(0);
x_644 = x_685;
goto block_650;
}
}
case 1:
{
lean_dec(x_651);
if (lean_obj_tag(x_3) == 2)
{
lean_object* x_686; lean_object* x_687; 
lean_dec(x_76);
x_686 = lean_ctor_get(x_3, 1);
lean_inc(x_686);
lean_dec(x_3);
lean_inc(x_4);
x_687 = l_Lean_Elab_Term_inferType(x_1, x_686, x_4, x_643);
if (lean_obj_tag(x_687) == 0)
{
lean_object* x_688; lean_object* x_689; lean_object* x_690; 
x_688 = lean_ctor_get(x_687, 0);
lean_inc(x_688);
x_689 = lean_ctor_get(x_687, 1);
lean_inc(x_689);
lean_dec(x_687);
lean_inc(x_4);
x_690 = l_Lean_Elab_Term_whnf(x_1, x_688, x_4, x_689);
if (lean_obj_tag(x_690) == 0)
{
lean_object* x_691; lean_object* x_692; lean_object* x_693; 
x_691 = lean_ctor_get(x_690, 0);
lean_inc(x_691);
x_692 = lean_ctor_get(x_690, 1);
lean_inc(x_692);
lean_dec(x_690);
x_693 = l_Lean_Elab_Term_tryPostponeIfMVar(x_691, x_4, x_692);
if (lean_obj_tag(x_693) == 0)
{
lean_object* x_694; lean_object* x_695; lean_object* x_696; lean_object* x_703; 
x_694 = lean_ctor_get(x_693, 1);
lean_inc(x_694);
if (lean_is_exclusive(x_693)) {
 lean_ctor_release(x_693, 0);
 lean_ctor_release(x_693, 1);
 x_695 = x_693;
} else {
 lean_dec_ref(x_693);
 x_695 = lean_box(0);
}
x_703 = l_Lean_Expr_getAppFn___main(x_691);
if (lean_obj_tag(x_703) == 4)
{
lean_object* x_704; lean_object* x_705; 
lean_dec(x_691);
lean_dec(x_4);
x_704 = lean_ctor_get(x_703, 0);
lean_inc(x_704);
lean_dec(x_703);
if (lean_is_scalar(x_695)) {
 x_705 = lean_alloc_ctor(0, 2, 0);
} else {
 x_705 = x_695;
}
lean_ctor_set(x_705, 0, x_704);
lean_ctor_set(x_705, 1, x_694);
return x_705;
}
else
{
lean_object* x_706; 
lean_dec(x_703);
lean_dec(x_695);
x_706 = lean_box(0);
x_696 = x_706;
goto block_702;
}
block_702:
{
lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; lean_object* x_701; 
lean_dec(x_696);
x_697 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_697, 0, x_691);
x_698 = l_Lean_indentExpr(x_697);
x_699 = l___private_Init_Lean_Elab_StructInst_5__getStructName___closed__6;
x_700 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_700, 0, x_699);
lean_ctor_set(x_700, 1, x_698);
x_701 = l_Lean_Elab_Term_throwError___rarg(x_1, x_700, x_4, x_694);
return x_701;
}
}
else
{
lean_object* x_707; lean_object* x_708; lean_object* x_709; lean_object* x_710; 
lean_dec(x_691);
lean_dec(x_4);
x_707 = lean_ctor_get(x_693, 0);
lean_inc(x_707);
x_708 = lean_ctor_get(x_693, 1);
lean_inc(x_708);
if (lean_is_exclusive(x_693)) {
 lean_ctor_release(x_693, 0);
 lean_ctor_release(x_693, 1);
 x_709 = x_693;
} else {
 lean_dec_ref(x_693);
 x_709 = lean_box(0);
}
if (lean_is_scalar(x_709)) {
 x_710 = lean_alloc_ctor(1, 2, 0);
} else {
 x_710 = x_709;
}
lean_ctor_set(x_710, 0, x_707);
lean_ctor_set(x_710, 1, x_708);
return x_710;
}
}
else
{
lean_object* x_711; lean_object* x_712; lean_object* x_713; lean_object* x_714; 
lean_dec(x_4);
x_711 = lean_ctor_get(x_690, 0);
lean_inc(x_711);
x_712 = lean_ctor_get(x_690, 1);
lean_inc(x_712);
if (lean_is_exclusive(x_690)) {
 lean_ctor_release(x_690, 0);
 lean_ctor_release(x_690, 1);
 x_713 = x_690;
} else {
 lean_dec_ref(x_690);
 x_713 = lean_box(0);
}
if (lean_is_scalar(x_713)) {
 x_714 = lean_alloc_ctor(1, 2, 0);
} else {
 x_714 = x_713;
}
lean_ctor_set(x_714, 0, x_711);
lean_ctor_set(x_714, 1, x_712);
return x_714;
}
}
else
{
lean_object* x_715; lean_object* x_716; lean_object* x_717; lean_object* x_718; 
lean_dec(x_4);
x_715 = lean_ctor_get(x_687, 0);
lean_inc(x_715);
x_716 = lean_ctor_get(x_687, 1);
lean_inc(x_716);
if (lean_is_exclusive(x_687)) {
 lean_ctor_release(x_687, 0);
 lean_ctor_release(x_687, 1);
 x_717 = x_687;
} else {
 lean_dec_ref(x_687);
 x_717 = lean_box(0);
}
if (lean_is_scalar(x_717)) {
 x_718 = lean_alloc_ctor(1, 2, 0);
} else {
 x_718 = x_717;
}
lean_ctor_set(x_718, 0, x_715);
lean_ctor_set(x_718, 1, x_716);
return x_718;
}
}
else
{
lean_object* x_719; 
lean_dec(x_3);
x_719 = lean_box(0);
x_644 = x_719;
goto block_650;
}
}
case 2:
{
lean_dec(x_651);
if (lean_obj_tag(x_3) == 2)
{
lean_object* x_720; lean_object* x_721; 
lean_dec(x_76);
x_720 = lean_ctor_get(x_3, 1);
lean_inc(x_720);
lean_dec(x_3);
lean_inc(x_4);
x_721 = l_Lean_Elab_Term_inferType(x_1, x_720, x_4, x_643);
if (lean_obj_tag(x_721) == 0)
{
lean_object* x_722; lean_object* x_723; lean_object* x_724; 
x_722 = lean_ctor_get(x_721, 0);
lean_inc(x_722);
x_723 = lean_ctor_get(x_721, 1);
lean_inc(x_723);
lean_dec(x_721);
lean_inc(x_4);
x_724 = l_Lean_Elab_Term_whnf(x_1, x_722, x_4, x_723);
if (lean_obj_tag(x_724) == 0)
{
lean_object* x_725; lean_object* x_726; lean_object* x_727; 
x_725 = lean_ctor_get(x_724, 0);
lean_inc(x_725);
x_726 = lean_ctor_get(x_724, 1);
lean_inc(x_726);
lean_dec(x_724);
x_727 = l_Lean_Elab_Term_tryPostponeIfMVar(x_725, x_4, x_726);
if (lean_obj_tag(x_727) == 0)
{
lean_object* x_728; lean_object* x_729; lean_object* x_730; lean_object* x_737; 
x_728 = lean_ctor_get(x_727, 1);
lean_inc(x_728);
if (lean_is_exclusive(x_727)) {
 lean_ctor_release(x_727, 0);
 lean_ctor_release(x_727, 1);
 x_729 = x_727;
} else {
 lean_dec_ref(x_727);
 x_729 = lean_box(0);
}
x_737 = l_Lean_Expr_getAppFn___main(x_725);
if (lean_obj_tag(x_737) == 4)
{
lean_object* x_738; lean_object* x_739; 
lean_dec(x_725);
lean_dec(x_4);
x_738 = lean_ctor_get(x_737, 0);
lean_inc(x_738);
lean_dec(x_737);
if (lean_is_scalar(x_729)) {
 x_739 = lean_alloc_ctor(0, 2, 0);
} else {
 x_739 = x_729;
}
lean_ctor_set(x_739, 0, x_738);
lean_ctor_set(x_739, 1, x_728);
return x_739;
}
else
{
lean_object* x_740; 
lean_dec(x_737);
lean_dec(x_729);
x_740 = lean_box(0);
x_730 = x_740;
goto block_736;
}
block_736:
{
lean_object* x_731; lean_object* x_732; lean_object* x_733; lean_object* x_734; lean_object* x_735; 
lean_dec(x_730);
x_731 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_731, 0, x_725);
x_732 = l_Lean_indentExpr(x_731);
x_733 = l___private_Init_Lean_Elab_StructInst_5__getStructName___closed__6;
x_734 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_734, 0, x_733);
lean_ctor_set(x_734, 1, x_732);
x_735 = l_Lean_Elab_Term_throwError___rarg(x_1, x_734, x_4, x_728);
return x_735;
}
}
else
{
lean_object* x_741; lean_object* x_742; lean_object* x_743; lean_object* x_744; 
lean_dec(x_725);
lean_dec(x_4);
x_741 = lean_ctor_get(x_727, 0);
lean_inc(x_741);
x_742 = lean_ctor_get(x_727, 1);
lean_inc(x_742);
if (lean_is_exclusive(x_727)) {
 lean_ctor_release(x_727, 0);
 lean_ctor_release(x_727, 1);
 x_743 = x_727;
} else {
 lean_dec_ref(x_727);
 x_743 = lean_box(0);
}
if (lean_is_scalar(x_743)) {
 x_744 = lean_alloc_ctor(1, 2, 0);
} else {
 x_744 = x_743;
}
lean_ctor_set(x_744, 0, x_741);
lean_ctor_set(x_744, 1, x_742);
return x_744;
}
}
else
{
lean_object* x_745; lean_object* x_746; lean_object* x_747; lean_object* x_748; 
lean_dec(x_4);
x_745 = lean_ctor_get(x_724, 0);
lean_inc(x_745);
x_746 = lean_ctor_get(x_724, 1);
lean_inc(x_746);
if (lean_is_exclusive(x_724)) {
 lean_ctor_release(x_724, 0);
 lean_ctor_release(x_724, 1);
 x_747 = x_724;
} else {
 lean_dec_ref(x_724);
 x_747 = lean_box(0);
}
if (lean_is_scalar(x_747)) {
 x_748 = lean_alloc_ctor(1, 2, 0);
} else {
 x_748 = x_747;
}
lean_ctor_set(x_748, 0, x_745);
lean_ctor_set(x_748, 1, x_746);
return x_748;
}
}
else
{
lean_object* x_749; lean_object* x_750; lean_object* x_751; lean_object* x_752; 
lean_dec(x_4);
x_749 = lean_ctor_get(x_721, 0);
lean_inc(x_749);
x_750 = lean_ctor_get(x_721, 1);
lean_inc(x_750);
if (lean_is_exclusive(x_721)) {
 lean_ctor_release(x_721, 0);
 lean_ctor_release(x_721, 1);
 x_751 = x_721;
} else {
 lean_dec_ref(x_721);
 x_751 = lean_box(0);
}
if (lean_is_scalar(x_751)) {
 x_752 = lean_alloc_ctor(1, 2, 0);
} else {
 x_752 = x_751;
}
lean_ctor_set(x_752, 0, x_749);
lean_ctor_set(x_752, 1, x_750);
return x_752;
}
}
else
{
lean_object* x_753; 
lean_dec(x_3);
x_753 = lean_box(0);
x_644 = x_753;
goto block_650;
}
}
case 3:
{
lean_dec(x_651);
if (lean_obj_tag(x_3) == 2)
{
lean_object* x_754; lean_object* x_755; 
lean_dec(x_76);
x_754 = lean_ctor_get(x_3, 1);
lean_inc(x_754);
lean_dec(x_3);
lean_inc(x_4);
x_755 = l_Lean_Elab_Term_inferType(x_1, x_754, x_4, x_643);
if (lean_obj_tag(x_755) == 0)
{
lean_object* x_756; lean_object* x_757; lean_object* x_758; 
x_756 = lean_ctor_get(x_755, 0);
lean_inc(x_756);
x_757 = lean_ctor_get(x_755, 1);
lean_inc(x_757);
lean_dec(x_755);
lean_inc(x_4);
x_758 = l_Lean_Elab_Term_whnf(x_1, x_756, x_4, x_757);
if (lean_obj_tag(x_758) == 0)
{
lean_object* x_759; lean_object* x_760; lean_object* x_761; 
x_759 = lean_ctor_get(x_758, 0);
lean_inc(x_759);
x_760 = lean_ctor_get(x_758, 1);
lean_inc(x_760);
lean_dec(x_758);
x_761 = l_Lean_Elab_Term_tryPostponeIfMVar(x_759, x_4, x_760);
if (lean_obj_tag(x_761) == 0)
{
lean_object* x_762; lean_object* x_763; lean_object* x_764; lean_object* x_771; 
x_762 = lean_ctor_get(x_761, 1);
lean_inc(x_762);
if (lean_is_exclusive(x_761)) {
 lean_ctor_release(x_761, 0);
 lean_ctor_release(x_761, 1);
 x_763 = x_761;
} else {
 lean_dec_ref(x_761);
 x_763 = lean_box(0);
}
x_771 = l_Lean_Expr_getAppFn___main(x_759);
if (lean_obj_tag(x_771) == 4)
{
lean_object* x_772; lean_object* x_773; 
lean_dec(x_759);
lean_dec(x_4);
x_772 = lean_ctor_get(x_771, 0);
lean_inc(x_772);
lean_dec(x_771);
if (lean_is_scalar(x_763)) {
 x_773 = lean_alloc_ctor(0, 2, 0);
} else {
 x_773 = x_763;
}
lean_ctor_set(x_773, 0, x_772);
lean_ctor_set(x_773, 1, x_762);
return x_773;
}
else
{
lean_object* x_774; 
lean_dec(x_771);
lean_dec(x_763);
x_774 = lean_box(0);
x_764 = x_774;
goto block_770;
}
block_770:
{
lean_object* x_765; lean_object* x_766; lean_object* x_767; lean_object* x_768; lean_object* x_769; 
lean_dec(x_764);
x_765 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_765, 0, x_759);
x_766 = l_Lean_indentExpr(x_765);
x_767 = l___private_Init_Lean_Elab_StructInst_5__getStructName___closed__6;
x_768 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_768, 0, x_767);
lean_ctor_set(x_768, 1, x_766);
x_769 = l_Lean_Elab_Term_throwError___rarg(x_1, x_768, x_4, x_762);
return x_769;
}
}
else
{
lean_object* x_775; lean_object* x_776; lean_object* x_777; lean_object* x_778; 
lean_dec(x_759);
lean_dec(x_4);
x_775 = lean_ctor_get(x_761, 0);
lean_inc(x_775);
x_776 = lean_ctor_get(x_761, 1);
lean_inc(x_776);
if (lean_is_exclusive(x_761)) {
 lean_ctor_release(x_761, 0);
 lean_ctor_release(x_761, 1);
 x_777 = x_761;
} else {
 lean_dec_ref(x_761);
 x_777 = lean_box(0);
}
if (lean_is_scalar(x_777)) {
 x_778 = lean_alloc_ctor(1, 2, 0);
} else {
 x_778 = x_777;
}
lean_ctor_set(x_778, 0, x_775);
lean_ctor_set(x_778, 1, x_776);
return x_778;
}
}
else
{
lean_object* x_779; lean_object* x_780; lean_object* x_781; lean_object* x_782; 
lean_dec(x_4);
x_779 = lean_ctor_get(x_758, 0);
lean_inc(x_779);
x_780 = lean_ctor_get(x_758, 1);
lean_inc(x_780);
if (lean_is_exclusive(x_758)) {
 lean_ctor_release(x_758, 0);
 lean_ctor_release(x_758, 1);
 x_781 = x_758;
} else {
 lean_dec_ref(x_758);
 x_781 = lean_box(0);
}
if (lean_is_scalar(x_781)) {
 x_782 = lean_alloc_ctor(1, 2, 0);
} else {
 x_782 = x_781;
}
lean_ctor_set(x_782, 0, x_779);
lean_ctor_set(x_782, 1, x_780);
return x_782;
}
}
else
{
lean_object* x_783; lean_object* x_784; lean_object* x_785; lean_object* x_786; 
lean_dec(x_4);
x_783 = lean_ctor_get(x_755, 0);
lean_inc(x_783);
x_784 = lean_ctor_get(x_755, 1);
lean_inc(x_784);
if (lean_is_exclusive(x_755)) {
 lean_ctor_release(x_755, 0);
 lean_ctor_release(x_755, 1);
 x_785 = x_755;
} else {
 lean_dec_ref(x_755);
 x_785 = lean_box(0);
}
if (lean_is_scalar(x_785)) {
 x_786 = lean_alloc_ctor(1, 2, 0);
} else {
 x_786 = x_785;
}
lean_ctor_set(x_786, 0, x_783);
lean_ctor_set(x_786, 1, x_784);
return x_786;
}
}
else
{
lean_object* x_787; 
lean_dec(x_3);
x_787 = lean_box(0);
x_644 = x_787;
goto block_650;
}
}
case 4:
{
lean_object* x_788; lean_object* x_789; 
lean_dec(x_76);
lean_dec(x_4);
lean_dec(x_3);
x_788 = lean_ctor_get(x_651, 0);
lean_inc(x_788);
lean_dec(x_651);
x_789 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_789, 0, x_788);
lean_ctor_set(x_789, 1, x_643);
return x_789;
}
case 5:
{
lean_dec(x_651);
if (lean_obj_tag(x_3) == 2)
{
lean_object* x_790; lean_object* x_791; 
lean_dec(x_76);
x_790 = lean_ctor_get(x_3, 1);
lean_inc(x_790);
lean_dec(x_3);
lean_inc(x_4);
x_791 = l_Lean_Elab_Term_inferType(x_1, x_790, x_4, x_643);
if (lean_obj_tag(x_791) == 0)
{
lean_object* x_792; lean_object* x_793; lean_object* x_794; 
x_792 = lean_ctor_get(x_791, 0);
lean_inc(x_792);
x_793 = lean_ctor_get(x_791, 1);
lean_inc(x_793);
lean_dec(x_791);
lean_inc(x_4);
x_794 = l_Lean_Elab_Term_whnf(x_1, x_792, x_4, x_793);
if (lean_obj_tag(x_794) == 0)
{
lean_object* x_795; lean_object* x_796; lean_object* x_797; 
x_795 = lean_ctor_get(x_794, 0);
lean_inc(x_795);
x_796 = lean_ctor_get(x_794, 1);
lean_inc(x_796);
lean_dec(x_794);
x_797 = l_Lean_Elab_Term_tryPostponeIfMVar(x_795, x_4, x_796);
if (lean_obj_tag(x_797) == 0)
{
lean_object* x_798; lean_object* x_799; lean_object* x_800; lean_object* x_807; 
x_798 = lean_ctor_get(x_797, 1);
lean_inc(x_798);
if (lean_is_exclusive(x_797)) {
 lean_ctor_release(x_797, 0);
 lean_ctor_release(x_797, 1);
 x_799 = x_797;
} else {
 lean_dec_ref(x_797);
 x_799 = lean_box(0);
}
x_807 = l_Lean_Expr_getAppFn___main(x_795);
if (lean_obj_tag(x_807) == 4)
{
lean_object* x_808; lean_object* x_809; 
lean_dec(x_795);
lean_dec(x_4);
x_808 = lean_ctor_get(x_807, 0);
lean_inc(x_808);
lean_dec(x_807);
if (lean_is_scalar(x_799)) {
 x_809 = lean_alloc_ctor(0, 2, 0);
} else {
 x_809 = x_799;
}
lean_ctor_set(x_809, 0, x_808);
lean_ctor_set(x_809, 1, x_798);
return x_809;
}
else
{
lean_object* x_810; 
lean_dec(x_807);
lean_dec(x_799);
x_810 = lean_box(0);
x_800 = x_810;
goto block_806;
}
block_806:
{
lean_object* x_801; lean_object* x_802; lean_object* x_803; lean_object* x_804; lean_object* x_805; 
lean_dec(x_800);
x_801 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_801, 0, x_795);
x_802 = l_Lean_indentExpr(x_801);
x_803 = l___private_Init_Lean_Elab_StructInst_5__getStructName___closed__6;
x_804 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_804, 0, x_803);
lean_ctor_set(x_804, 1, x_802);
x_805 = l_Lean_Elab_Term_throwError___rarg(x_1, x_804, x_4, x_798);
return x_805;
}
}
else
{
lean_object* x_811; lean_object* x_812; lean_object* x_813; lean_object* x_814; 
lean_dec(x_795);
lean_dec(x_4);
x_811 = lean_ctor_get(x_797, 0);
lean_inc(x_811);
x_812 = lean_ctor_get(x_797, 1);
lean_inc(x_812);
if (lean_is_exclusive(x_797)) {
 lean_ctor_release(x_797, 0);
 lean_ctor_release(x_797, 1);
 x_813 = x_797;
} else {
 lean_dec_ref(x_797);
 x_813 = lean_box(0);
}
if (lean_is_scalar(x_813)) {
 x_814 = lean_alloc_ctor(1, 2, 0);
} else {
 x_814 = x_813;
}
lean_ctor_set(x_814, 0, x_811);
lean_ctor_set(x_814, 1, x_812);
return x_814;
}
}
else
{
lean_object* x_815; lean_object* x_816; lean_object* x_817; lean_object* x_818; 
lean_dec(x_4);
x_815 = lean_ctor_get(x_794, 0);
lean_inc(x_815);
x_816 = lean_ctor_get(x_794, 1);
lean_inc(x_816);
if (lean_is_exclusive(x_794)) {
 lean_ctor_release(x_794, 0);
 lean_ctor_release(x_794, 1);
 x_817 = x_794;
} else {
 lean_dec_ref(x_794);
 x_817 = lean_box(0);
}
if (lean_is_scalar(x_817)) {
 x_818 = lean_alloc_ctor(1, 2, 0);
} else {
 x_818 = x_817;
}
lean_ctor_set(x_818, 0, x_815);
lean_ctor_set(x_818, 1, x_816);
return x_818;
}
}
else
{
lean_object* x_819; lean_object* x_820; lean_object* x_821; lean_object* x_822; 
lean_dec(x_4);
x_819 = lean_ctor_get(x_791, 0);
lean_inc(x_819);
x_820 = lean_ctor_get(x_791, 1);
lean_inc(x_820);
if (lean_is_exclusive(x_791)) {
 lean_ctor_release(x_791, 0);
 lean_ctor_release(x_791, 1);
 x_821 = x_791;
} else {
 lean_dec_ref(x_791);
 x_821 = lean_box(0);
}
if (lean_is_scalar(x_821)) {
 x_822 = lean_alloc_ctor(1, 2, 0);
} else {
 x_822 = x_821;
}
lean_ctor_set(x_822, 0, x_819);
lean_ctor_set(x_822, 1, x_820);
return x_822;
}
}
else
{
lean_object* x_823; 
lean_dec(x_3);
x_823 = lean_box(0);
x_644 = x_823;
goto block_650;
}
}
case 6:
{
lean_dec(x_651);
if (lean_obj_tag(x_3) == 2)
{
lean_object* x_824; lean_object* x_825; 
lean_dec(x_76);
x_824 = lean_ctor_get(x_3, 1);
lean_inc(x_824);
lean_dec(x_3);
lean_inc(x_4);
x_825 = l_Lean_Elab_Term_inferType(x_1, x_824, x_4, x_643);
if (lean_obj_tag(x_825) == 0)
{
lean_object* x_826; lean_object* x_827; lean_object* x_828; 
x_826 = lean_ctor_get(x_825, 0);
lean_inc(x_826);
x_827 = lean_ctor_get(x_825, 1);
lean_inc(x_827);
lean_dec(x_825);
lean_inc(x_4);
x_828 = l_Lean_Elab_Term_whnf(x_1, x_826, x_4, x_827);
if (lean_obj_tag(x_828) == 0)
{
lean_object* x_829; lean_object* x_830; lean_object* x_831; 
x_829 = lean_ctor_get(x_828, 0);
lean_inc(x_829);
x_830 = lean_ctor_get(x_828, 1);
lean_inc(x_830);
lean_dec(x_828);
x_831 = l_Lean_Elab_Term_tryPostponeIfMVar(x_829, x_4, x_830);
if (lean_obj_tag(x_831) == 0)
{
lean_object* x_832; lean_object* x_833; lean_object* x_834; lean_object* x_841; 
x_832 = lean_ctor_get(x_831, 1);
lean_inc(x_832);
if (lean_is_exclusive(x_831)) {
 lean_ctor_release(x_831, 0);
 lean_ctor_release(x_831, 1);
 x_833 = x_831;
} else {
 lean_dec_ref(x_831);
 x_833 = lean_box(0);
}
x_841 = l_Lean_Expr_getAppFn___main(x_829);
if (lean_obj_tag(x_841) == 4)
{
lean_object* x_842; lean_object* x_843; 
lean_dec(x_829);
lean_dec(x_4);
x_842 = lean_ctor_get(x_841, 0);
lean_inc(x_842);
lean_dec(x_841);
if (lean_is_scalar(x_833)) {
 x_843 = lean_alloc_ctor(0, 2, 0);
} else {
 x_843 = x_833;
}
lean_ctor_set(x_843, 0, x_842);
lean_ctor_set(x_843, 1, x_832);
return x_843;
}
else
{
lean_object* x_844; 
lean_dec(x_841);
lean_dec(x_833);
x_844 = lean_box(0);
x_834 = x_844;
goto block_840;
}
block_840:
{
lean_object* x_835; lean_object* x_836; lean_object* x_837; lean_object* x_838; lean_object* x_839; 
lean_dec(x_834);
x_835 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_835, 0, x_829);
x_836 = l_Lean_indentExpr(x_835);
x_837 = l___private_Init_Lean_Elab_StructInst_5__getStructName___closed__6;
x_838 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_838, 0, x_837);
lean_ctor_set(x_838, 1, x_836);
x_839 = l_Lean_Elab_Term_throwError___rarg(x_1, x_838, x_4, x_832);
return x_839;
}
}
else
{
lean_object* x_845; lean_object* x_846; lean_object* x_847; lean_object* x_848; 
lean_dec(x_829);
lean_dec(x_4);
x_845 = lean_ctor_get(x_831, 0);
lean_inc(x_845);
x_846 = lean_ctor_get(x_831, 1);
lean_inc(x_846);
if (lean_is_exclusive(x_831)) {
 lean_ctor_release(x_831, 0);
 lean_ctor_release(x_831, 1);
 x_847 = x_831;
} else {
 lean_dec_ref(x_831);
 x_847 = lean_box(0);
}
if (lean_is_scalar(x_847)) {
 x_848 = lean_alloc_ctor(1, 2, 0);
} else {
 x_848 = x_847;
}
lean_ctor_set(x_848, 0, x_845);
lean_ctor_set(x_848, 1, x_846);
return x_848;
}
}
else
{
lean_object* x_849; lean_object* x_850; lean_object* x_851; lean_object* x_852; 
lean_dec(x_4);
x_849 = lean_ctor_get(x_828, 0);
lean_inc(x_849);
x_850 = lean_ctor_get(x_828, 1);
lean_inc(x_850);
if (lean_is_exclusive(x_828)) {
 lean_ctor_release(x_828, 0);
 lean_ctor_release(x_828, 1);
 x_851 = x_828;
} else {
 lean_dec_ref(x_828);
 x_851 = lean_box(0);
}
if (lean_is_scalar(x_851)) {
 x_852 = lean_alloc_ctor(1, 2, 0);
} else {
 x_852 = x_851;
}
lean_ctor_set(x_852, 0, x_849);
lean_ctor_set(x_852, 1, x_850);
return x_852;
}
}
else
{
lean_object* x_853; lean_object* x_854; lean_object* x_855; lean_object* x_856; 
lean_dec(x_4);
x_853 = lean_ctor_get(x_825, 0);
lean_inc(x_853);
x_854 = lean_ctor_get(x_825, 1);
lean_inc(x_854);
if (lean_is_exclusive(x_825)) {
 lean_ctor_release(x_825, 0);
 lean_ctor_release(x_825, 1);
 x_855 = x_825;
} else {
 lean_dec_ref(x_825);
 x_855 = lean_box(0);
}
if (lean_is_scalar(x_855)) {
 x_856 = lean_alloc_ctor(1, 2, 0);
} else {
 x_856 = x_855;
}
lean_ctor_set(x_856, 0, x_853);
lean_ctor_set(x_856, 1, x_854);
return x_856;
}
}
else
{
lean_object* x_857; 
lean_dec(x_3);
x_857 = lean_box(0);
x_644 = x_857;
goto block_650;
}
}
case 7:
{
lean_dec(x_651);
if (lean_obj_tag(x_3) == 2)
{
lean_object* x_858; lean_object* x_859; 
lean_dec(x_76);
x_858 = lean_ctor_get(x_3, 1);
lean_inc(x_858);
lean_dec(x_3);
lean_inc(x_4);
x_859 = l_Lean_Elab_Term_inferType(x_1, x_858, x_4, x_643);
if (lean_obj_tag(x_859) == 0)
{
lean_object* x_860; lean_object* x_861; lean_object* x_862; 
x_860 = lean_ctor_get(x_859, 0);
lean_inc(x_860);
x_861 = lean_ctor_get(x_859, 1);
lean_inc(x_861);
lean_dec(x_859);
lean_inc(x_4);
x_862 = l_Lean_Elab_Term_whnf(x_1, x_860, x_4, x_861);
if (lean_obj_tag(x_862) == 0)
{
lean_object* x_863; lean_object* x_864; lean_object* x_865; 
x_863 = lean_ctor_get(x_862, 0);
lean_inc(x_863);
x_864 = lean_ctor_get(x_862, 1);
lean_inc(x_864);
lean_dec(x_862);
x_865 = l_Lean_Elab_Term_tryPostponeIfMVar(x_863, x_4, x_864);
if (lean_obj_tag(x_865) == 0)
{
lean_object* x_866; lean_object* x_867; lean_object* x_868; lean_object* x_875; 
x_866 = lean_ctor_get(x_865, 1);
lean_inc(x_866);
if (lean_is_exclusive(x_865)) {
 lean_ctor_release(x_865, 0);
 lean_ctor_release(x_865, 1);
 x_867 = x_865;
} else {
 lean_dec_ref(x_865);
 x_867 = lean_box(0);
}
x_875 = l_Lean_Expr_getAppFn___main(x_863);
if (lean_obj_tag(x_875) == 4)
{
lean_object* x_876; lean_object* x_877; 
lean_dec(x_863);
lean_dec(x_4);
x_876 = lean_ctor_get(x_875, 0);
lean_inc(x_876);
lean_dec(x_875);
if (lean_is_scalar(x_867)) {
 x_877 = lean_alloc_ctor(0, 2, 0);
} else {
 x_877 = x_867;
}
lean_ctor_set(x_877, 0, x_876);
lean_ctor_set(x_877, 1, x_866);
return x_877;
}
else
{
lean_object* x_878; 
lean_dec(x_875);
lean_dec(x_867);
x_878 = lean_box(0);
x_868 = x_878;
goto block_874;
}
block_874:
{
lean_object* x_869; lean_object* x_870; lean_object* x_871; lean_object* x_872; lean_object* x_873; 
lean_dec(x_868);
x_869 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_869, 0, x_863);
x_870 = l_Lean_indentExpr(x_869);
x_871 = l___private_Init_Lean_Elab_StructInst_5__getStructName___closed__6;
x_872 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_872, 0, x_871);
lean_ctor_set(x_872, 1, x_870);
x_873 = l_Lean_Elab_Term_throwError___rarg(x_1, x_872, x_4, x_866);
return x_873;
}
}
else
{
lean_object* x_879; lean_object* x_880; lean_object* x_881; lean_object* x_882; 
lean_dec(x_863);
lean_dec(x_4);
x_879 = lean_ctor_get(x_865, 0);
lean_inc(x_879);
x_880 = lean_ctor_get(x_865, 1);
lean_inc(x_880);
if (lean_is_exclusive(x_865)) {
 lean_ctor_release(x_865, 0);
 lean_ctor_release(x_865, 1);
 x_881 = x_865;
} else {
 lean_dec_ref(x_865);
 x_881 = lean_box(0);
}
if (lean_is_scalar(x_881)) {
 x_882 = lean_alloc_ctor(1, 2, 0);
} else {
 x_882 = x_881;
}
lean_ctor_set(x_882, 0, x_879);
lean_ctor_set(x_882, 1, x_880);
return x_882;
}
}
else
{
lean_object* x_883; lean_object* x_884; lean_object* x_885; lean_object* x_886; 
lean_dec(x_4);
x_883 = lean_ctor_get(x_862, 0);
lean_inc(x_883);
x_884 = lean_ctor_get(x_862, 1);
lean_inc(x_884);
if (lean_is_exclusive(x_862)) {
 lean_ctor_release(x_862, 0);
 lean_ctor_release(x_862, 1);
 x_885 = x_862;
} else {
 lean_dec_ref(x_862);
 x_885 = lean_box(0);
}
if (lean_is_scalar(x_885)) {
 x_886 = lean_alloc_ctor(1, 2, 0);
} else {
 x_886 = x_885;
}
lean_ctor_set(x_886, 0, x_883);
lean_ctor_set(x_886, 1, x_884);
return x_886;
}
}
else
{
lean_object* x_887; lean_object* x_888; lean_object* x_889; lean_object* x_890; 
lean_dec(x_4);
x_887 = lean_ctor_get(x_859, 0);
lean_inc(x_887);
x_888 = lean_ctor_get(x_859, 1);
lean_inc(x_888);
if (lean_is_exclusive(x_859)) {
 lean_ctor_release(x_859, 0);
 lean_ctor_release(x_859, 1);
 x_889 = x_859;
} else {
 lean_dec_ref(x_859);
 x_889 = lean_box(0);
}
if (lean_is_scalar(x_889)) {
 x_890 = lean_alloc_ctor(1, 2, 0);
} else {
 x_890 = x_889;
}
lean_ctor_set(x_890, 0, x_887);
lean_ctor_set(x_890, 1, x_888);
return x_890;
}
}
else
{
lean_object* x_891; 
lean_dec(x_3);
x_891 = lean_box(0);
x_644 = x_891;
goto block_650;
}
}
case 8:
{
lean_dec(x_651);
if (lean_obj_tag(x_3) == 2)
{
lean_object* x_892; lean_object* x_893; 
lean_dec(x_76);
x_892 = lean_ctor_get(x_3, 1);
lean_inc(x_892);
lean_dec(x_3);
lean_inc(x_4);
x_893 = l_Lean_Elab_Term_inferType(x_1, x_892, x_4, x_643);
if (lean_obj_tag(x_893) == 0)
{
lean_object* x_894; lean_object* x_895; lean_object* x_896; 
x_894 = lean_ctor_get(x_893, 0);
lean_inc(x_894);
x_895 = lean_ctor_get(x_893, 1);
lean_inc(x_895);
lean_dec(x_893);
lean_inc(x_4);
x_896 = l_Lean_Elab_Term_whnf(x_1, x_894, x_4, x_895);
if (lean_obj_tag(x_896) == 0)
{
lean_object* x_897; lean_object* x_898; lean_object* x_899; 
x_897 = lean_ctor_get(x_896, 0);
lean_inc(x_897);
x_898 = lean_ctor_get(x_896, 1);
lean_inc(x_898);
lean_dec(x_896);
x_899 = l_Lean_Elab_Term_tryPostponeIfMVar(x_897, x_4, x_898);
if (lean_obj_tag(x_899) == 0)
{
lean_object* x_900; lean_object* x_901; lean_object* x_902; lean_object* x_909; 
x_900 = lean_ctor_get(x_899, 1);
lean_inc(x_900);
if (lean_is_exclusive(x_899)) {
 lean_ctor_release(x_899, 0);
 lean_ctor_release(x_899, 1);
 x_901 = x_899;
} else {
 lean_dec_ref(x_899);
 x_901 = lean_box(0);
}
x_909 = l_Lean_Expr_getAppFn___main(x_897);
if (lean_obj_tag(x_909) == 4)
{
lean_object* x_910; lean_object* x_911; 
lean_dec(x_897);
lean_dec(x_4);
x_910 = lean_ctor_get(x_909, 0);
lean_inc(x_910);
lean_dec(x_909);
if (lean_is_scalar(x_901)) {
 x_911 = lean_alloc_ctor(0, 2, 0);
} else {
 x_911 = x_901;
}
lean_ctor_set(x_911, 0, x_910);
lean_ctor_set(x_911, 1, x_900);
return x_911;
}
else
{
lean_object* x_912; 
lean_dec(x_909);
lean_dec(x_901);
x_912 = lean_box(0);
x_902 = x_912;
goto block_908;
}
block_908:
{
lean_object* x_903; lean_object* x_904; lean_object* x_905; lean_object* x_906; lean_object* x_907; 
lean_dec(x_902);
x_903 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_903, 0, x_897);
x_904 = l_Lean_indentExpr(x_903);
x_905 = l___private_Init_Lean_Elab_StructInst_5__getStructName___closed__6;
x_906 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_906, 0, x_905);
lean_ctor_set(x_906, 1, x_904);
x_907 = l_Lean_Elab_Term_throwError___rarg(x_1, x_906, x_4, x_900);
return x_907;
}
}
else
{
lean_object* x_913; lean_object* x_914; lean_object* x_915; lean_object* x_916; 
lean_dec(x_897);
lean_dec(x_4);
x_913 = lean_ctor_get(x_899, 0);
lean_inc(x_913);
x_914 = lean_ctor_get(x_899, 1);
lean_inc(x_914);
if (lean_is_exclusive(x_899)) {
 lean_ctor_release(x_899, 0);
 lean_ctor_release(x_899, 1);
 x_915 = x_899;
} else {
 lean_dec_ref(x_899);
 x_915 = lean_box(0);
}
if (lean_is_scalar(x_915)) {
 x_916 = lean_alloc_ctor(1, 2, 0);
} else {
 x_916 = x_915;
}
lean_ctor_set(x_916, 0, x_913);
lean_ctor_set(x_916, 1, x_914);
return x_916;
}
}
else
{
lean_object* x_917; lean_object* x_918; lean_object* x_919; lean_object* x_920; 
lean_dec(x_4);
x_917 = lean_ctor_get(x_896, 0);
lean_inc(x_917);
x_918 = lean_ctor_get(x_896, 1);
lean_inc(x_918);
if (lean_is_exclusive(x_896)) {
 lean_ctor_release(x_896, 0);
 lean_ctor_release(x_896, 1);
 x_919 = x_896;
} else {
 lean_dec_ref(x_896);
 x_919 = lean_box(0);
}
if (lean_is_scalar(x_919)) {
 x_920 = lean_alloc_ctor(1, 2, 0);
} else {
 x_920 = x_919;
}
lean_ctor_set(x_920, 0, x_917);
lean_ctor_set(x_920, 1, x_918);
return x_920;
}
}
else
{
lean_object* x_921; lean_object* x_922; lean_object* x_923; lean_object* x_924; 
lean_dec(x_4);
x_921 = lean_ctor_get(x_893, 0);
lean_inc(x_921);
x_922 = lean_ctor_get(x_893, 1);
lean_inc(x_922);
if (lean_is_exclusive(x_893)) {
 lean_ctor_release(x_893, 0);
 lean_ctor_release(x_893, 1);
 x_923 = x_893;
} else {
 lean_dec_ref(x_893);
 x_923 = lean_box(0);
}
if (lean_is_scalar(x_923)) {
 x_924 = lean_alloc_ctor(1, 2, 0);
} else {
 x_924 = x_923;
}
lean_ctor_set(x_924, 0, x_921);
lean_ctor_set(x_924, 1, x_922);
return x_924;
}
}
else
{
lean_object* x_925; 
lean_dec(x_3);
x_925 = lean_box(0);
x_644 = x_925;
goto block_650;
}
}
case 9:
{
lean_dec(x_651);
if (lean_obj_tag(x_3) == 2)
{
lean_object* x_926; lean_object* x_927; 
lean_dec(x_76);
x_926 = lean_ctor_get(x_3, 1);
lean_inc(x_926);
lean_dec(x_3);
lean_inc(x_4);
x_927 = l_Lean_Elab_Term_inferType(x_1, x_926, x_4, x_643);
if (lean_obj_tag(x_927) == 0)
{
lean_object* x_928; lean_object* x_929; lean_object* x_930; 
x_928 = lean_ctor_get(x_927, 0);
lean_inc(x_928);
x_929 = lean_ctor_get(x_927, 1);
lean_inc(x_929);
lean_dec(x_927);
lean_inc(x_4);
x_930 = l_Lean_Elab_Term_whnf(x_1, x_928, x_4, x_929);
if (lean_obj_tag(x_930) == 0)
{
lean_object* x_931; lean_object* x_932; lean_object* x_933; 
x_931 = lean_ctor_get(x_930, 0);
lean_inc(x_931);
x_932 = lean_ctor_get(x_930, 1);
lean_inc(x_932);
lean_dec(x_930);
x_933 = l_Lean_Elab_Term_tryPostponeIfMVar(x_931, x_4, x_932);
if (lean_obj_tag(x_933) == 0)
{
lean_object* x_934; lean_object* x_935; lean_object* x_936; lean_object* x_943; 
x_934 = lean_ctor_get(x_933, 1);
lean_inc(x_934);
if (lean_is_exclusive(x_933)) {
 lean_ctor_release(x_933, 0);
 lean_ctor_release(x_933, 1);
 x_935 = x_933;
} else {
 lean_dec_ref(x_933);
 x_935 = lean_box(0);
}
x_943 = l_Lean_Expr_getAppFn___main(x_931);
if (lean_obj_tag(x_943) == 4)
{
lean_object* x_944; lean_object* x_945; 
lean_dec(x_931);
lean_dec(x_4);
x_944 = lean_ctor_get(x_943, 0);
lean_inc(x_944);
lean_dec(x_943);
if (lean_is_scalar(x_935)) {
 x_945 = lean_alloc_ctor(0, 2, 0);
} else {
 x_945 = x_935;
}
lean_ctor_set(x_945, 0, x_944);
lean_ctor_set(x_945, 1, x_934);
return x_945;
}
else
{
lean_object* x_946; 
lean_dec(x_943);
lean_dec(x_935);
x_946 = lean_box(0);
x_936 = x_946;
goto block_942;
}
block_942:
{
lean_object* x_937; lean_object* x_938; lean_object* x_939; lean_object* x_940; lean_object* x_941; 
lean_dec(x_936);
x_937 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_937, 0, x_931);
x_938 = l_Lean_indentExpr(x_937);
x_939 = l___private_Init_Lean_Elab_StructInst_5__getStructName___closed__6;
x_940 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_940, 0, x_939);
lean_ctor_set(x_940, 1, x_938);
x_941 = l_Lean_Elab_Term_throwError___rarg(x_1, x_940, x_4, x_934);
return x_941;
}
}
else
{
lean_object* x_947; lean_object* x_948; lean_object* x_949; lean_object* x_950; 
lean_dec(x_931);
lean_dec(x_4);
x_947 = lean_ctor_get(x_933, 0);
lean_inc(x_947);
x_948 = lean_ctor_get(x_933, 1);
lean_inc(x_948);
if (lean_is_exclusive(x_933)) {
 lean_ctor_release(x_933, 0);
 lean_ctor_release(x_933, 1);
 x_949 = x_933;
} else {
 lean_dec_ref(x_933);
 x_949 = lean_box(0);
}
if (lean_is_scalar(x_949)) {
 x_950 = lean_alloc_ctor(1, 2, 0);
} else {
 x_950 = x_949;
}
lean_ctor_set(x_950, 0, x_947);
lean_ctor_set(x_950, 1, x_948);
return x_950;
}
}
else
{
lean_object* x_951; lean_object* x_952; lean_object* x_953; lean_object* x_954; 
lean_dec(x_4);
x_951 = lean_ctor_get(x_930, 0);
lean_inc(x_951);
x_952 = lean_ctor_get(x_930, 1);
lean_inc(x_952);
if (lean_is_exclusive(x_930)) {
 lean_ctor_release(x_930, 0);
 lean_ctor_release(x_930, 1);
 x_953 = x_930;
} else {
 lean_dec_ref(x_930);
 x_953 = lean_box(0);
}
if (lean_is_scalar(x_953)) {
 x_954 = lean_alloc_ctor(1, 2, 0);
} else {
 x_954 = x_953;
}
lean_ctor_set(x_954, 0, x_951);
lean_ctor_set(x_954, 1, x_952);
return x_954;
}
}
else
{
lean_object* x_955; lean_object* x_956; lean_object* x_957; lean_object* x_958; 
lean_dec(x_4);
x_955 = lean_ctor_get(x_927, 0);
lean_inc(x_955);
x_956 = lean_ctor_get(x_927, 1);
lean_inc(x_956);
if (lean_is_exclusive(x_927)) {
 lean_ctor_release(x_927, 0);
 lean_ctor_release(x_927, 1);
 x_957 = x_927;
} else {
 lean_dec_ref(x_927);
 x_957 = lean_box(0);
}
if (lean_is_scalar(x_957)) {
 x_958 = lean_alloc_ctor(1, 2, 0);
} else {
 x_958 = x_957;
}
lean_ctor_set(x_958, 0, x_955);
lean_ctor_set(x_958, 1, x_956);
return x_958;
}
}
else
{
lean_object* x_959; 
lean_dec(x_3);
x_959 = lean_box(0);
x_644 = x_959;
goto block_650;
}
}
case 10:
{
lean_dec(x_651);
if (lean_obj_tag(x_3) == 2)
{
lean_object* x_960; lean_object* x_961; 
lean_dec(x_76);
x_960 = lean_ctor_get(x_3, 1);
lean_inc(x_960);
lean_dec(x_3);
lean_inc(x_4);
x_961 = l_Lean_Elab_Term_inferType(x_1, x_960, x_4, x_643);
if (lean_obj_tag(x_961) == 0)
{
lean_object* x_962; lean_object* x_963; lean_object* x_964; 
x_962 = lean_ctor_get(x_961, 0);
lean_inc(x_962);
x_963 = lean_ctor_get(x_961, 1);
lean_inc(x_963);
lean_dec(x_961);
lean_inc(x_4);
x_964 = l_Lean_Elab_Term_whnf(x_1, x_962, x_4, x_963);
if (lean_obj_tag(x_964) == 0)
{
lean_object* x_965; lean_object* x_966; lean_object* x_967; 
x_965 = lean_ctor_get(x_964, 0);
lean_inc(x_965);
x_966 = lean_ctor_get(x_964, 1);
lean_inc(x_966);
lean_dec(x_964);
x_967 = l_Lean_Elab_Term_tryPostponeIfMVar(x_965, x_4, x_966);
if (lean_obj_tag(x_967) == 0)
{
lean_object* x_968; lean_object* x_969; lean_object* x_970; lean_object* x_977; 
x_968 = lean_ctor_get(x_967, 1);
lean_inc(x_968);
if (lean_is_exclusive(x_967)) {
 lean_ctor_release(x_967, 0);
 lean_ctor_release(x_967, 1);
 x_969 = x_967;
} else {
 lean_dec_ref(x_967);
 x_969 = lean_box(0);
}
x_977 = l_Lean_Expr_getAppFn___main(x_965);
if (lean_obj_tag(x_977) == 4)
{
lean_object* x_978; lean_object* x_979; 
lean_dec(x_965);
lean_dec(x_4);
x_978 = lean_ctor_get(x_977, 0);
lean_inc(x_978);
lean_dec(x_977);
if (lean_is_scalar(x_969)) {
 x_979 = lean_alloc_ctor(0, 2, 0);
} else {
 x_979 = x_969;
}
lean_ctor_set(x_979, 0, x_978);
lean_ctor_set(x_979, 1, x_968);
return x_979;
}
else
{
lean_object* x_980; 
lean_dec(x_977);
lean_dec(x_969);
x_980 = lean_box(0);
x_970 = x_980;
goto block_976;
}
block_976:
{
lean_object* x_971; lean_object* x_972; lean_object* x_973; lean_object* x_974; lean_object* x_975; 
lean_dec(x_970);
x_971 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_971, 0, x_965);
x_972 = l_Lean_indentExpr(x_971);
x_973 = l___private_Init_Lean_Elab_StructInst_5__getStructName___closed__6;
x_974 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_974, 0, x_973);
lean_ctor_set(x_974, 1, x_972);
x_975 = l_Lean_Elab_Term_throwError___rarg(x_1, x_974, x_4, x_968);
return x_975;
}
}
else
{
lean_object* x_981; lean_object* x_982; lean_object* x_983; lean_object* x_984; 
lean_dec(x_965);
lean_dec(x_4);
x_981 = lean_ctor_get(x_967, 0);
lean_inc(x_981);
x_982 = lean_ctor_get(x_967, 1);
lean_inc(x_982);
if (lean_is_exclusive(x_967)) {
 lean_ctor_release(x_967, 0);
 lean_ctor_release(x_967, 1);
 x_983 = x_967;
} else {
 lean_dec_ref(x_967);
 x_983 = lean_box(0);
}
if (lean_is_scalar(x_983)) {
 x_984 = lean_alloc_ctor(1, 2, 0);
} else {
 x_984 = x_983;
}
lean_ctor_set(x_984, 0, x_981);
lean_ctor_set(x_984, 1, x_982);
return x_984;
}
}
else
{
lean_object* x_985; lean_object* x_986; lean_object* x_987; lean_object* x_988; 
lean_dec(x_4);
x_985 = lean_ctor_get(x_964, 0);
lean_inc(x_985);
x_986 = lean_ctor_get(x_964, 1);
lean_inc(x_986);
if (lean_is_exclusive(x_964)) {
 lean_ctor_release(x_964, 0);
 lean_ctor_release(x_964, 1);
 x_987 = x_964;
} else {
 lean_dec_ref(x_964);
 x_987 = lean_box(0);
}
if (lean_is_scalar(x_987)) {
 x_988 = lean_alloc_ctor(1, 2, 0);
} else {
 x_988 = x_987;
}
lean_ctor_set(x_988, 0, x_985);
lean_ctor_set(x_988, 1, x_986);
return x_988;
}
}
else
{
lean_object* x_989; lean_object* x_990; lean_object* x_991; lean_object* x_992; 
lean_dec(x_4);
x_989 = lean_ctor_get(x_961, 0);
lean_inc(x_989);
x_990 = lean_ctor_get(x_961, 1);
lean_inc(x_990);
if (lean_is_exclusive(x_961)) {
 lean_ctor_release(x_961, 0);
 lean_ctor_release(x_961, 1);
 x_991 = x_961;
} else {
 lean_dec_ref(x_961);
 x_991 = lean_box(0);
}
if (lean_is_scalar(x_991)) {
 x_992 = lean_alloc_ctor(1, 2, 0);
} else {
 x_992 = x_991;
}
lean_ctor_set(x_992, 0, x_989);
lean_ctor_set(x_992, 1, x_990);
return x_992;
}
}
else
{
lean_object* x_993; 
lean_dec(x_3);
x_993 = lean_box(0);
x_644 = x_993;
goto block_650;
}
}
case 11:
{
lean_dec(x_651);
if (lean_obj_tag(x_3) == 2)
{
lean_object* x_994; lean_object* x_995; 
lean_dec(x_76);
x_994 = lean_ctor_get(x_3, 1);
lean_inc(x_994);
lean_dec(x_3);
lean_inc(x_4);
x_995 = l_Lean_Elab_Term_inferType(x_1, x_994, x_4, x_643);
if (lean_obj_tag(x_995) == 0)
{
lean_object* x_996; lean_object* x_997; lean_object* x_998; 
x_996 = lean_ctor_get(x_995, 0);
lean_inc(x_996);
x_997 = lean_ctor_get(x_995, 1);
lean_inc(x_997);
lean_dec(x_995);
lean_inc(x_4);
x_998 = l_Lean_Elab_Term_whnf(x_1, x_996, x_4, x_997);
if (lean_obj_tag(x_998) == 0)
{
lean_object* x_999; lean_object* x_1000; lean_object* x_1001; 
x_999 = lean_ctor_get(x_998, 0);
lean_inc(x_999);
x_1000 = lean_ctor_get(x_998, 1);
lean_inc(x_1000);
lean_dec(x_998);
x_1001 = l_Lean_Elab_Term_tryPostponeIfMVar(x_999, x_4, x_1000);
if (lean_obj_tag(x_1001) == 0)
{
lean_object* x_1002; lean_object* x_1003; lean_object* x_1004; lean_object* x_1011; 
x_1002 = lean_ctor_get(x_1001, 1);
lean_inc(x_1002);
if (lean_is_exclusive(x_1001)) {
 lean_ctor_release(x_1001, 0);
 lean_ctor_release(x_1001, 1);
 x_1003 = x_1001;
} else {
 lean_dec_ref(x_1001);
 x_1003 = lean_box(0);
}
x_1011 = l_Lean_Expr_getAppFn___main(x_999);
if (lean_obj_tag(x_1011) == 4)
{
lean_object* x_1012; lean_object* x_1013; 
lean_dec(x_999);
lean_dec(x_4);
x_1012 = lean_ctor_get(x_1011, 0);
lean_inc(x_1012);
lean_dec(x_1011);
if (lean_is_scalar(x_1003)) {
 x_1013 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1013 = x_1003;
}
lean_ctor_set(x_1013, 0, x_1012);
lean_ctor_set(x_1013, 1, x_1002);
return x_1013;
}
else
{
lean_object* x_1014; 
lean_dec(x_1011);
lean_dec(x_1003);
x_1014 = lean_box(0);
x_1004 = x_1014;
goto block_1010;
}
block_1010:
{
lean_object* x_1005; lean_object* x_1006; lean_object* x_1007; lean_object* x_1008; lean_object* x_1009; 
lean_dec(x_1004);
x_1005 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1005, 0, x_999);
x_1006 = l_Lean_indentExpr(x_1005);
x_1007 = l___private_Init_Lean_Elab_StructInst_5__getStructName___closed__6;
x_1008 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1008, 0, x_1007);
lean_ctor_set(x_1008, 1, x_1006);
x_1009 = l_Lean_Elab_Term_throwError___rarg(x_1, x_1008, x_4, x_1002);
return x_1009;
}
}
else
{
lean_object* x_1015; lean_object* x_1016; lean_object* x_1017; lean_object* x_1018; 
lean_dec(x_999);
lean_dec(x_4);
x_1015 = lean_ctor_get(x_1001, 0);
lean_inc(x_1015);
x_1016 = lean_ctor_get(x_1001, 1);
lean_inc(x_1016);
if (lean_is_exclusive(x_1001)) {
 lean_ctor_release(x_1001, 0);
 lean_ctor_release(x_1001, 1);
 x_1017 = x_1001;
} else {
 lean_dec_ref(x_1001);
 x_1017 = lean_box(0);
}
if (lean_is_scalar(x_1017)) {
 x_1018 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1018 = x_1017;
}
lean_ctor_set(x_1018, 0, x_1015);
lean_ctor_set(x_1018, 1, x_1016);
return x_1018;
}
}
else
{
lean_object* x_1019; lean_object* x_1020; lean_object* x_1021; lean_object* x_1022; 
lean_dec(x_4);
x_1019 = lean_ctor_get(x_998, 0);
lean_inc(x_1019);
x_1020 = lean_ctor_get(x_998, 1);
lean_inc(x_1020);
if (lean_is_exclusive(x_998)) {
 lean_ctor_release(x_998, 0);
 lean_ctor_release(x_998, 1);
 x_1021 = x_998;
} else {
 lean_dec_ref(x_998);
 x_1021 = lean_box(0);
}
if (lean_is_scalar(x_1021)) {
 x_1022 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1022 = x_1021;
}
lean_ctor_set(x_1022, 0, x_1019);
lean_ctor_set(x_1022, 1, x_1020);
return x_1022;
}
}
else
{
lean_object* x_1023; lean_object* x_1024; lean_object* x_1025; lean_object* x_1026; 
lean_dec(x_4);
x_1023 = lean_ctor_get(x_995, 0);
lean_inc(x_1023);
x_1024 = lean_ctor_get(x_995, 1);
lean_inc(x_1024);
if (lean_is_exclusive(x_995)) {
 lean_ctor_release(x_995, 0);
 lean_ctor_release(x_995, 1);
 x_1025 = x_995;
} else {
 lean_dec_ref(x_995);
 x_1025 = lean_box(0);
}
if (lean_is_scalar(x_1025)) {
 x_1026 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1026 = x_1025;
}
lean_ctor_set(x_1026, 0, x_1023);
lean_ctor_set(x_1026, 1, x_1024);
return x_1026;
}
}
else
{
lean_object* x_1027; 
lean_dec(x_3);
x_1027 = lean_box(0);
x_644 = x_1027;
goto block_650;
}
}
default: 
{
lean_dec(x_651);
if (lean_obj_tag(x_3) == 2)
{
lean_object* x_1028; lean_object* x_1029; 
lean_dec(x_76);
x_1028 = lean_ctor_get(x_3, 1);
lean_inc(x_1028);
lean_dec(x_3);
lean_inc(x_4);
x_1029 = l_Lean_Elab_Term_inferType(x_1, x_1028, x_4, x_643);
if (lean_obj_tag(x_1029) == 0)
{
lean_object* x_1030; lean_object* x_1031; lean_object* x_1032; 
x_1030 = lean_ctor_get(x_1029, 0);
lean_inc(x_1030);
x_1031 = lean_ctor_get(x_1029, 1);
lean_inc(x_1031);
lean_dec(x_1029);
lean_inc(x_4);
x_1032 = l_Lean_Elab_Term_whnf(x_1, x_1030, x_4, x_1031);
if (lean_obj_tag(x_1032) == 0)
{
lean_object* x_1033; lean_object* x_1034; lean_object* x_1035; 
x_1033 = lean_ctor_get(x_1032, 0);
lean_inc(x_1033);
x_1034 = lean_ctor_get(x_1032, 1);
lean_inc(x_1034);
lean_dec(x_1032);
x_1035 = l_Lean_Elab_Term_tryPostponeIfMVar(x_1033, x_4, x_1034);
if (lean_obj_tag(x_1035) == 0)
{
lean_object* x_1036; lean_object* x_1037; lean_object* x_1038; lean_object* x_1045; 
x_1036 = lean_ctor_get(x_1035, 1);
lean_inc(x_1036);
if (lean_is_exclusive(x_1035)) {
 lean_ctor_release(x_1035, 0);
 lean_ctor_release(x_1035, 1);
 x_1037 = x_1035;
} else {
 lean_dec_ref(x_1035);
 x_1037 = lean_box(0);
}
x_1045 = l_Lean_Expr_getAppFn___main(x_1033);
if (lean_obj_tag(x_1045) == 4)
{
lean_object* x_1046; lean_object* x_1047; 
lean_dec(x_1033);
lean_dec(x_4);
x_1046 = lean_ctor_get(x_1045, 0);
lean_inc(x_1046);
lean_dec(x_1045);
if (lean_is_scalar(x_1037)) {
 x_1047 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1047 = x_1037;
}
lean_ctor_set(x_1047, 0, x_1046);
lean_ctor_set(x_1047, 1, x_1036);
return x_1047;
}
else
{
lean_object* x_1048; 
lean_dec(x_1045);
lean_dec(x_1037);
x_1048 = lean_box(0);
x_1038 = x_1048;
goto block_1044;
}
block_1044:
{
lean_object* x_1039; lean_object* x_1040; lean_object* x_1041; lean_object* x_1042; lean_object* x_1043; 
lean_dec(x_1038);
x_1039 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1039, 0, x_1033);
x_1040 = l_Lean_indentExpr(x_1039);
x_1041 = l___private_Init_Lean_Elab_StructInst_5__getStructName___closed__6;
x_1042 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1042, 0, x_1041);
lean_ctor_set(x_1042, 1, x_1040);
x_1043 = l_Lean_Elab_Term_throwError___rarg(x_1, x_1042, x_4, x_1036);
return x_1043;
}
}
else
{
lean_object* x_1049; lean_object* x_1050; lean_object* x_1051; lean_object* x_1052; 
lean_dec(x_1033);
lean_dec(x_4);
x_1049 = lean_ctor_get(x_1035, 0);
lean_inc(x_1049);
x_1050 = lean_ctor_get(x_1035, 1);
lean_inc(x_1050);
if (lean_is_exclusive(x_1035)) {
 lean_ctor_release(x_1035, 0);
 lean_ctor_release(x_1035, 1);
 x_1051 = x_1035;
} else {
 lean_dec_ref(x_1035);
 x_1051 = lean_box(0);
}
if (lean_is_scalar(x_1051)) {
 x_1052 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1052 = x_1051;
}
lean_ctor_set(x_1052, 0, x_1049);
lean_ctor_set(x_1052, 1, x_1050);
return x_1052;
}
}
else
{
lean_object* x_1053; lean_object* x_1054; lean_object* x_1055; lean_object* x_1056; 
lean_dec(x_4);
x_1053 = lean_ctor_get(x_1032, 0);
lean_inc(x_1053);
x_1054 = lean_ctor_get(x_1032, 1);
lean_inc(x_1054);
if (lean_is_exclusive(x_1032)) {
 lean_ctor_release(x_1032, 0);
 lean_ctor_release(x_1032, 1);
 x_1055 = x_1032;
} else {
 lean_dec_ref(x_1032);
 x_1055 = lean_box(0);
}
if (lean_is_scalar(x_1055)) {
 x_1056 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1056 = x_1055;
}
lean_ctor_set(x_1056, 0, x_1053);
lean_ctor_set(x_1056, 1, x_1054);
return x_1056;
}
}
else
{
lean_object* x_1057; lean_object* x_1058; lean_object* x_1059; lean_object* x_1060; 
lean_dec(x_4);
x_1057 = lean_ctor_get(x_1029, 0);
lean_inc(x_1057);
x_1058 = lean_ctor_get(x_1029, 1);
lean_inc(x_1058);
if (lean_is_exclusive(x_1029)) {
 lean_ctor_release(x_1029, 0);
 lean_ctor_release(x_1029, 1);
 x_1059 = x_1029;
} else {
 lean_dec_ref(x_1029);
 x_1059 = lean_box(0);
}
if (lean_is_scalar(x_1059)) {
 x_1060 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1060 = x_1059;
}
lean_ctor_set(x_1060, 0, x_1057);
lean_ctor_set(x_1060, 1, x_1058);
return x_1060;
}
}
else
{
lean_object* x_1061; 
lean_dec(x_3);
x_1061 = lean_box(0);
x_644 = x_1061;
goto block_650;
}
}
}
block_650:
{
lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; 
lean_dec(x_644);
x_645 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_645, 0, x_76);
x_646 = l_Lean_indentExpr(x_645);
x_647 = l___private_Init_Lean_Elab_StructInst_5__getStructName___closed__3;
x_648 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_648, 0, x_647);
lean_ctor_set(x_648, 1, x_646);
x_649 = l_Lean_Elab_Term_throwError___rarg(x_1, x_648, x_4, x_643);
return x_649;
}
}
}
else
{
uint8_t x_1062; 
lean_dec(x_76);
lean_dec(x_4);
lean_dec(x_3);
x_1062 = !lean_is_exclusive(x_77);
if (x_1062 == 0)
{
return x_77;
}
else
{
lean_object* x_1063; lean_object* x_1064; lean_object* x_1065; 
x_1063 = lean_ctor_get(x_77, 0);
x_1064 = lean_ctor_get(x_77, 1);
lean_inc(x_1064);
lean_inc(x_1063);
lean_dec(x_77);
x_1065 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1065, 0, x_1063);
lean_ctor_set(x_1065, 1, x_1064);
return x_1065;
}
}
}
block_29:
{
lean_dec(x_14);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_15 = l_Lean_Expr_Inhabited;
x_16 = l_Option_get_x21___rarg___closed__3;
x_17 = lean_panic_fn(x_15, x_16);
x_18 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = l_Lean_indentExpr(x_18);
x_20 = l___private_Init_Lean_Elab_StructInst_5__getStructName___closed__3;
x_21 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
x_22 = l_Lean_Elab_Term_throwError___rarg(x_1, x_21, x_4, x_13);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_23 = lean_ctor_get(x_2, 0);
lean_inc(x_23);
lean_dec(x_2);
x_24 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = l_Lean_indentExpr(x_24);
x_26 = l___private_Init_Lean_Elab_StructInst_5__getStructName___closed__3;
x_27 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
x_28 = l_Lean_Elab_Term_throwError___rarg(x_1, x_27, x_4, x_13);
return x_28;
}
}
}
else
{
uint8_t x_1066; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1066 = !lean_is_exclusive(x_12);
if (x_1066 == 0)
{
return x_12;
}
else
{
lean_object* x_1067; lean_object* x_1068; lean_object* x_1069; 
x_1067 = lean_ctor_get(x_12, 0);
x_1068 = lean_ctor_get(x_12, 1);
lean_inc(x_1068);
lean_inc(x_1067);
lean_dec(x_12);
x_1069 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1069, 0, x_1067);
lean_ctor_set(x_1069, 1, x_1068);
return x_1069;
}
}
}
}
}
lean_object* l___private_Init_Lean_Elab_StructInst_5__getStructName___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Lean_Elab_StructInst_5__getStructName(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
lean_object* _init_l_Lean_Elab_Term_StructInst_FieldLHS_inhabited___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_StructInst_FieldLHS_inhabited() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Term_StructInst_FieldLHS_inhabited___closed__1;
return x_1;
}
}
lean_object* l_Lean_Elab_Term_StructInst_FieldLHS_hasFormat(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
lean_dec(x_1);
x_3 = l_Lean_fmt___at_Lean_Level_LevelToFormat_toResult___main___spec__1(x_2);
return x_3;
}
case 1:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = l_Lean_fmt___at_Lean_Level_LevelToFormat_Result_format___main___spec__1(x_4);
return x_5;
}
default: 
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = l_Lean_Syntax_prettyPrint(x_6);
x_8 = 0;
x_9 = l_Lean_Format_sbracket___closed__2;
x_10 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_7);
lean_ctor_set_uint8(x_10, sizeof(void*)*2, x_8);
x_11 = l_Lean_Format_sbracket___closed__3;
x_12 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
lean_ctor_set_uint8(x_12, sizeof(void*)*2, x_8);
return x_12;
}
}
}
}
lean_object* _init_l_Lean_Elab_Term_StructInst_Field_inhabited___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_StructInst_Field_inhabited___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = l_Lean_Elab_Term_StructInst_Field_inhabited___closed__1;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_1);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* l_Lean_Elab_Term_StructInst_Field_inhabited(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Term_StructInst_Field_inhabited___closed__2;
return x_2;
}
}
uint8_t l_Lean_Elab_Term_StructInst_Field_isSimple___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 1);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_2, 1);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = 1;
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
}
lean_object* l_Lean_Elab_Term_StructInst_Field_isSimple(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_StructInst_Field_isSimple___rarg___boxed), 1, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_StructInst_Field_isSimple___rarg___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_Term_StructInst_Field_isSimple___rarg(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_StructInst_Struct_ref(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_StructInst_Struct_ref___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Term_StructInst_Struct_ref(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_StructInst_Struct_structName(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_StructInst_Struct_structName___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Term_StructInst_Struct_structName(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_StructInst_Struct_fields(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 2);
lean_inc(x_2);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_StructInst_Struct_fields___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Term_StructInst_Struct_fields(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_StructInst_Struct_source(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 3);
lean_inc(x_2);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_StructInst_Struct_source___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Term_StructInst_Struct_source(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Format_joinSep___main___at_Lean_Elab_Term_StructInst_formatField___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
lean_dec(x_2);
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
lean_dec(x_2);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
switch (lean_obj_tag(x_5)) {
case 0:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_Lean_fmt___at_Lean_Level_LevelToFormat_toResult___main___spec__1(x_6);
return x_7;
}
case 1:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec(x_5);
x_9 = l_Lean_fmt___at_Lean_Level_LevelToFormat_Result_format___main___spec__1(x_8);
return x_9;
}
default: 
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
lean_dec(x_5);
x_11 = l_Lean_Syntax_prettyPrint(x_10);
x_12 = 0;
x_13 = l_Lean_Format_sbracket___closed__2;
x_14 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_11);
lean_ctor_set_uint8(x_14, sizeof(void*)*2, x_12);
x_15 = l_Lean_Format_sbracket___closed__3;
x_16 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
lean_ctor_set_uint8(x_16, sizeof(void*)*2, x_12);
return x_16;
}
}
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
lean_dec(x_1);
lean_inc(x_2);
x_18 = l_Lean_Format_joinSep___main___at_Lean_Elab_Term_StructInst_formatField___spec__1(x_4, x_2);
switch (lean_obj_tag(x_17)) {
case 0:
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_fmt___at_Lean_Level_LevelToFormat_toResult___main___spec__1(x_19);
x_21 = 0;
x_22 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_2);
lean_ctor_set_uint8(x_22, sizeof(void*)*2, x_21);
x_23 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_18);
lean_ctor_set_uint8(x_23, sizeof(void*)*2, x_21);
return x_23;
}
case 1:
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_17, 1);
lean_inc(x_24);
lean_dec(x_17);
x_25 = l_Lean_fmt___at_Lean_Level_LevelToFormat_Result_format___main___spec__1(x_24);
x_26 = 0;
x_27 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_2);
lean_ctor_set_uint8(x_27, sizeof(void*)*2, x_26);
x_28 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_18);
lean_ctor_set_uint8(x_28, sizeof(void*)*2, x_26);
return x_28;
}
default: 
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_29 = lean_ctor_get(x_17, 1);
lean_inc(x_29);
lean_dec(x_17);
x_30 = l_Lean_Syntax_prettyPrint(x_29);
x_31 = 0;
x_32 = l_Lean_Format_sbracket___closed__2;
x_33 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_30);
lean_ctor_set_uint8(x_33, sizeof(void*)*2, x_31);
x_34 = l_Lean_Format_sbracket___closed__3;
x_35 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
lean_ctor_set_uint8(x_35, sizeof(void*)*2, x_31);
x_36 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_2);
lean_ctor_set_uint8(x_36, sizeof(void*)*2, x_31);
x_37 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_18);
lean_ctor_set_uint8(x_37, sizeof(void*)*2, x_31);
return x_37;
}
}
}
}
}
}
lean_object* _init_l_Lean_Elab_Term_StructInst_formatField___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Term_structInst___elambda__1___closed__6;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_StructInst_formatField(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
x_4 = l_Lean_Elab_Term_StructInst_formatField___closed__1;
x_5 = l_Lean_Format_joinSep___main___at_Lean_Elab_Term_StructInst_formatField___spec__1(x_3, x_4);
x_6 = 0;
x_7 = l_Lean_formatEntry___closed__2;
x_8 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_7);
lean_ctor_set_uint8(x_8, sizeof(void*)*2, x_6);
x_9 = lean_ctor_get(x_2, 2);
lean_inc(x_9);
lean_dec(x_2);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_1);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = l_Lean_Syntax_prettyPrint(x_10);
x_12 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_11);
lean_ctor_set_uint8(x_12, sizeof(void*)*2, x_6);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_9, 0);
lean_inc(x_13);
lean_dec(x_9);
x_14 = lean_apply_1(x_1, x_13);
x_15 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_15, 0, x_8);
lean_ctor_set(x_15, 1, x_14);
lean_ctor_set_uint8(x_15, sizeof(void*)*2, x_6);
return x_15;
}
}
}
lean_object* _init_l_List_map___main___at_Lean_Elab_Term_StructInst_formatStruct___main___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_StructInst_formatStruct___main), 1, 0);
return x_1;
}
}
lean_object* l_List_map___main___at_Lean_Elab_Term_StructInst_formatStruct___main___spec__1(lean_object* x_1) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = l_List_map___main___at_Lean_Elab_Term_StructInst_formatStruct___main___spec__1___closed__1;
x_7 = l_Lean_Elab_Term_StructInst_formatField(x_6, x_4);
x_8 = l_List_map___main___at_Lean_Elab_Term_StructInst_formatStruct___main___spec__1(x_5);
lean_ctor_set(x_1, 1, x_8);
lean_ctor_set(x_1, 0, x_7);
return x_1;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_1);
x_11 = l_List_map___main___at_Lean_Elab_Term_StructInst_formatStruct___main___spec__1___closed__1;
x_12 = l_Lean_Elab_Term_StructInst_formatField(x_11, x_9);
x_13 = l_List_map___main___at_Lean_Elab_Term_StructInst_formatStruct___main___spec__1(x_10);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
}
lean_object* l_Lean_fmt___at_Lean_Elab_Term_StructInst_formatStruct___main___spec__2(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; 
x_2 = l_Lean_Format_join___closed__1;
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Term_StructInst_Source_hasFormat___closed__2;
return x_3;
}
default: 
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_expr_dbg_to_string(x_4);
x_6 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = 0;
x_8 = l_Lean_Elab_Term_StructInst_Source_hasFormat___closed__4;
x_9 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_6);
lean_ctor_set_uint8(x_9, sizeof(void*)*2, x_7);
return x_9;
}
}
}
}
lean_object* _init_l_Lean_Elab_Term_StructInst_formatStruct___main___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_addParenHeuristic___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_StructInst_formatStruct___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_PersistentHashMap_Stats_toString___closed__5;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_StructInst_formatStruct___main(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 2);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 3);
lean_inc(x_4);
lean_dec(x_1);
x_5 = l_Lean_fmt___at_Lean_Level_LevelToFormat_toResult___main___spec__1(x_2);
x_6 = 0;
x_7 = l_Lean_Elab_Term_StructInst_formatStruct___main___closed__1;
x_8 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_5);
lean_ctor_set_uint8(x_8, sizeof(void*)*2, x_6);
x_9 = l_Lean_Elab_Term_StructInst_formatField___closed__1;
x_10 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
lean_ctor_set_uint8(x_10, sizeof(void*)*2, x_6);
x_11 = l_List_map___main___at_Lean_Elab_Term_StructInst_formatStruct___main___spec__1(x_3);
x_12 = l_Lean_formatKVMap___closed__1;
x_13 = l_Lean_Format_joinSep___main___at___private_Init_Lean_Data_Trie_6__toStringAux___main___spec__1(x_11, x_12);
lean_dec(x_11);
x_14 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_13);
lean_ctor_set_uint8(x_14, sizeof(void*)*2, x_6);
x_15 = l_Lean_fmt___at_Lean_Elab_Term_StructInst_formatStruct___main___spec__2(x_4);
lean_dec(x_4);
x_16 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
lean_ctor_set_uint8(x_16, sizeof(void*)*2, x_6);
x_17 = l_Lean_Elab_Term_StructInst_formatStruct___main___closed__2;
x_18 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set_uint8(x_18, sizeof(void*)*2, x_6);
return x_18;
}
}
lean_object* l_Lean_fmt___at_Lean_Elab_Term_StructInst_formatStruct___main___spec__2___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_fmt___at_Lean_Elab_Term_StructInst_formatStruct___main___spec__2(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_StructInst_formatStruct(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Term_StructInst_formatStruct___main(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_StructInst_Struct_hasFormat___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_StructInst_formatStruct), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_StructInst_Struct_hasFormat() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Term_StructInst_Struct_hasFormat___closed__1;
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_StructInst_Struct_hasToString___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_HasRepr___closed__1;
x_2 = l_Lean_Elab_Term_StructInst_Struct_hasFormat___closed__1;
x_3 = lean_alloc_closure((void*)(l_Function_comp___rarg), 3, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_StructInst_Struct_hasToString() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Term_StructInst_Struct_hasToString___closed__1;
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_StructInst_Field_hasFormat___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_StructInst_Struct_hasFormat___closed__1;
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_StructInst_formatField), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_StructInst_Field_hasFormat() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Term_StructInst_Field_hasFormat___closed__1;
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_StructInst_Field_hasToString___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_HasRepr___closed__1;
x_2 = l_Lean_Elab_Term_StructInst_Field_hasFormat___closed__1;
x_3 = lean_alloc_closure((void*)(l_Function_comp___rarg), 3, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_StructInst_Field_hasToString() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Term_StructInst_Field_hasToString___closed__1;
return x_1;
}
}
lean_object* l_Lean_Elab_Term_StructInst_FieldLHS_toSyntax(uint8_t x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
if (x_1 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = l_Lean_Name_toString___closed__1;
x_6 = l_Lean_mkAtomFrom(x_3, x_5);
x_7 = l_Lean_mkIdentFrom(x_3, x_4);
lean_dec(x_3);
x_8 = l_Lean_mkAppStx___closed__9;
x_9 = lean_array_push(x_8, x_6);
x_10 = lean_array_push(x_9, x_7);
x_11 = l_Lean_nullKind;
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_2, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_2, 1);
lean_inc(x_14);
lean_dec(x_2);
x_15 = l_Lean_mkIdentFrom(x_13, x_14);
lean_dec(x_13);
return x_15;
}
}
case 1:
{
if (x_1 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_16 = lean_ctor_get(x_2, 0);
lean_inc(x_16);
lean_dec(x_2);
x_17 = l_Lean_Name_toString___closed__1;
x_18 = l_Lean_mkAtomFrom(x_16, x_17);
x_19 = l_Lean_mkAppStx___closed__9;
x_20 = lean_array_push(x_19, x_18);
x_21 = lean_array_push(x_20, x_16);
x_22 = l_Lean_nullKind;
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
else
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_2, 0);
lean_inc(x_24);
lean_dec(x_2);
return x_24;
}
}
default: 
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_2, 0);
lean_inc(x_25);
lean_dec(x_2);
return x_25;
}
}
}
}
lean_object* l_Lean_Elab_Term_StructInst_FieldLHS_toSyntax___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lean_Elab_Term_StructInst_FieldLHS_toSyntax(x_3, x_2);
return x_4;
}
}
lean_object* l_Lean_Elab_Term_StructInst_FieldVal_toSyntax(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Syntax_inhabited;
x_4 = l_unreachable_x21___rarg(x_3);
return x_4;
}
}
}
lean_object* l_Lean_Elab_Term_StructInst_FieldVal_toSyntax___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Term_StructInst_FieldVal_toSyntax(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_StructInst_Field_toSyntax___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_nat_dec_lt(x_1, x_3);
lean_dec(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_1);
x_5 = l_Array_empty___closed__1;
x_6 = x_2;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_7 = lean_array_fget(x_2, x_1);
x_8 = lean_box(0);
x_9 = x_8;
x_10 = lean_array_fset(x_2, x_1, x_9);
x_11 = 0;
lean_inc(x_7);
x_12 = l_Lean_Elab_Term_StructInst_FieldLHS_toSyntax(x_11, x_7);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_1, x_13);
x_15 = x_12;
lean_dec(x_7);
x_16 = lean_array_fset(x_10, x_1, x_15);
lean_dec(x_1);
x_1 = x_14;
x_2 = x_16;
goto _start;
}
}
}
lean_object* l_Lean_Elab_Term_StructInst_Field_toSyntax(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; 
lean_dec(x_1);
x_3 = l_Lean_Syntax_inhabited;
x_4 = l_unreachable_x21___rarg(x_3);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
lean_dec(x_1);
x_9 = l_Lean_Elab_Term_StructInst_FieldVal_toSyntax(x_8);
lean_dec(x_8);
x_10 = lean_unsigned_to_nat(3u);
x_11 = l_Lean_Syntax_setArg(x_7, x_10, x_9);
x_12 = 1;
x_13 = l_Lean_Elab_Term_StructInst_FieldLHS_toSyntax(x_12, x_5);
x_14 = lean_unsigned_to_nat(0u);
x_15 = l_Lean_Syntax_setArg(x_11, x_14, x_13);
x_16 = l_List_redLength___main___rarg(x_6);
x_17 = lean_mk_empty_array_with_capacity(x_16);
lean_dec(x_16);
x_18 = l_List_toArrayAux___main___rarg(x_6, x_17);
x_19 = l_Array_umapMAux___main___at_Lean_Elab_Term_StructInst_Field_toSyntax___spec__1(x_14, x_18);
x_20 = l_Lean_nullKind;
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
x_22 = lean_unsigned_to_nat(1u);
x_23 = l_Lean_Syntax_setArg(x_15, x_22, x_21);
return x_23;
}
}
}
lean_object* l___private_Init_Lean_Elab_StructInst_6__toFieldLHS(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
lean_inc(x_1);
x_2 = l_Lean_Syntax_getKind(x_1);
x_3 = l_Lean_Parser_Term_structInstArrayRef___elambda__1___closed__2;
x_4 = lean_name_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_nullKind;
x_6 = lean_name_eq(x_2, x_5);
lean_dec(x_2);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = l_Lean_Syntax_isIdent(x_1);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_numLitKind;
x_9 = l_Lean_Syntax_isNatLitAux(x_8, x_1);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_1);
x_10 = l_Lean_Elab_Term_StructInst_FieldLHS_inhabited;
x_11 = l_unreachable_x21___rarg(x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_9, 0);
lean_inc(x_12);
lean_dec(x_9);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Lean_Syntax_getId(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_unsigned_to_nat(1u);
x_17 = l_Lean_Syntax_getArg(x_1, x_16);
lean_dec(x_1);
x_18 = l_Lean_Syntax_isIdent(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = l_Lean_numLitKind;
x_20 = l_Lean_Syntax_isNatLitAux(x_19, x_17);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_17);
x_21 = l_Lean_Elab_Term_StructInst_FieldLHS_inhabited;
x_22 = l_unreachable_x21___rarg(x_21);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_20, 0);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_17);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = l_Lean_Syntax_getId(x_17);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_17);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_2);
x_27 = lean_unsigned_to_nat(1u);
x_28 = l_Lean_Syntax_getArg(x_1, x_27);
x_29 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_29, 0, x_1);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
lean_object* l_Array_filterAux___main___at___private_Init_Lean_Elab_StructInst_7__mkStructView___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_array_fget(x_1, x_2);
x_8 = l_Lean_Syntax_getKind(x_7);
x_9 = l_Lean_Parser_Term_structInstField___elambda__1___closed__2;
x_10 = lean_name_eq(x_8, x_9);
lean_dec(x_8);
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
}
}
lean_object* l_List_map___main___at___private_Init_Lean_Elab_StructInst_7__mkStructView___spec__2(lean_object* x_1) {
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
x_6 = l___private_Init_Lean_Elab_StructInst_6__toFieldLHS(x_4);
x_7 = l_List_map___main___at___private_Init_Lean_Elab_StructInst_7__mkStructView___spec__2(x_5);
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
x_10 = l___private_Init_Lean_Elab_StructInst_6__toFieldLHS(x_8);
x_11 = l_List_map___main___at___private_Init_Lean_Elab_StructInst_7__mkStructView___spec__2(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
}
lean_object* l_List_map___main___at___private_Init_Lean_Elab_StructInst_7__mkStructView___spec__3(lean_object* x_1) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_unsigned_to_nat(3u);
x_7 = l_Lean_Syntax_getArg(x_4, x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Lean_Syntax_getArg(x_4, x_8);
x_10 = l___private_Init_Lean_Elab_StructInst_6__toFieldLHS(x_9);
x_11 = lean_unsigned_to_nat(1u);
x_12 = l_Lean_Syntax_getArg(x_4, x_11);
x_13 = l_Lean_Syntax_getArgs(x_12);
lean_dec(x_12);
x_14 = l_Array_toList___rarg(x_13);
lean_dec(x_13);
x_15 = l_List_map___main___at___private_Init_Lean_Elab_StructInst_7__mkStructView___spec__2(x_14);
lean_ctor_set(x_1, 1, x_15);
lean_ctor_set(x_1, 0, x_10);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_7);
x_17 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_17, 0, x_4);
lean_ctor_set(x_17, 1, x_1);
lean_ctor_set(x_17, 2, x_16);
x_18 = l_List_map___main___at___private_Init_Lean_Elab_StructInst_7__mkStructView___spec__3(x_5);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_20 = lean_ctor_get(x_1, 0);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_1);
x_22 = lean_unsigned_to_nat(3u);
x_23 = l_Lean_Syntax_getArg(x_20, x_22);
x_24 = lean_unsigned_to_nat(0u);
x_25 = l_Lean_Syntax_getArg(x_20, x_24);
x_26 = l___private_Init_Lean_Elab_StructInst_6__toFieldLHS(x_25);
x_27 = lean_unsigned_to_nat(1u);
x_28 = l_Lean_Syntax_getArg(x_20, x_27);
x_29 = l_Lean_Syntax_getArgs(x_28);
lean_dec(x_28);
x_30 = l_Array_toList___rarg(x_29);
lean_dec(x_29);
x_31 = l_List_map___main___at___private_Init_Lean_Elab_StructInst_7__mkStructView___spec__2(x_30);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_26);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_23);
x_34 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_34, 0, x_20);
lean_ctor_set(x_34, 1, x_32);
lean_ctor_set(x_34, 2, x_33);
x_35 = l_List_map___main___at___private_Init_Lean_Elab_StructInst_7__mkStructView___spec__3(x_21);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
lean_object* l___private_Init_Lean_Elab_StructInst_7__mkStructView(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_unsigned_to_nat(2u);
x_5 = l_Lean_Syntax_getArg(x_1, x_4);
x_6 = l_Lean_Syntax_getArgs(x_5);
lean_dec(x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Array_filterAux___main___at___private_Init_Lean_Elab_StructInst_7__mkStructView___spec__1(x_6, x_7, x_7);
x_9 = l_Array_toList___rarg(x_8);
lean_dec(x_8);
x_10 = l_List_map___main___at___private_Init_Lean_Elab_StructInst_7__mkStructView___spec__3(x_9);
x_11 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_2);
lean_ctor_set(x_11, 2, x_10);
lean_ctor_set(x_11, 3, x_3);
return x_11;
}
}
lean_object* l_Lean_Elab_Term_StructInst_Struct_modifyFieldsM___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_8, 0, x_2);
lean_ctor_set(x_8, 1, x_3);
lean_ctor_set(x_8, 2, x_5);
lean_ctor_set(x_8, 3, x_4);
x_9 = lean_apply_2(x_7, lean_box(0), x_8);
return x_9;
}
}
lean_object* l_Lean_Elab_Term_StructInst_Struct_modifyFieldsM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 3);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_apply_1(x_3, x_6);
x_10 = lean_alloc_closure((void*)(l_Lean_Elab_Term_StructInst_Struct_modifyFieldsM___rarg___lambda__1), 5, 4);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_4);
lean_closure_set(x_10, 2, x_5);
lean_closure_set(x_10, 3, x_7);
x_11 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_9, x_10);
return x_11;
}
}
lean_object* l_Lean_Elab_Term_StructInst_Struct_modifyFieldsM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_StructInst_Struct_modifyFieldsM___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_StructInst_Struct_modifyFieldsM___at_Lean_Elab_Term_StructInst_Struct_modifyFields___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 2);
x_5 = lean_apply_1(x_2, x_4);
lean_ctor_set(x_1, 2, x_5);
return x_1;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get(x_1, 2);
x_9 = lean_ctor_get(x_1, 3);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_1);
x_10 = lean_apply_1(x_2, x_8);
x_11 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_11, 0, x_6);
lean_ctor_set(x_11, 1, x_7);
lean_ctor_set(x_11, 2, x_10);
lean_ctor_set(x_11, 3, x_9);
return x_11;
}
}
}
lean_object* l_Lean_Elab_Term_StructInst_Struct_modifyFields(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Term_StructInst_Struct_modifyFieldsM___at_Lean_Elab_Term_StructInst_Struct_modifyFields___spec__1(x_1, x_2);
return x_3;
}
}
lean_object* l_List_map___main___at___private_Init_Lean_Elab_StructInst_8__expandCompositeFields___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec(x_1);
x_3 = lean_box(0);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_1);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_5);
x_8 = l_List_map___main___at___private_Init_Lean_Elab_StructInst_8__expandCompositeFields___spec__1(x_1, x_6);
lean_ctor_set(x_2, 1, x_8);
lean_ctor_set(x_2, 0, x_7);
return x_2;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_2);
lean_inc(x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_9);
x_12 = l_List_map___main___at___private_Init_Lean_Elab_StructInst_8__expandCompositeFields___spec__1(x_1, x_10);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
}
lean_object* l_List_map___main___at___private_Init_Lean_Elab_StructInst_8__expandCompositeFields___spec__2(lean_object* x_1) {
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
x_6 = l_List_map___main___at___private_Init_Lean_Elab_StructInst_8__expandCompositeFields___spec__2(x_5);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
lean_ctor_set(x_1, 1, x_6);
return x_1;
}
else
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_4, 2);
lean_inc(x_10);
x_11 = lean_ctor_get(x_7, 1);
lean_inc(x_11);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_12 = x_7;
} else {
 lean_dec_ref(x_7);
 x_12 = lean_box(0);
}
x_13 = lean_ctor_get(x_8, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_8, 1);
lean_inc(x_14);
lean_dec(x_8);
if (lean_obj_tag(x_14) == 1)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_14, 0);
lean_inc(x_22);
if (lean_obj_tag(x_22) == 0)
{
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_ctor_set(x_1, 1, x_6);
return x_1;
}
else
{
lean_object* x_23; 
lean_dec(x_22);
lean_free_object(x_1);
lean_dec(x_4);
x_23 = lean_box(0);
x_15 = x_23;
goto block_21;
}
}
else
{
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_ctor_set(x_1, 1, x_6);
return x_1;
}
block_21:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_15);
x_16 = l_Lean_Name_components(x_14);
x_17 = l_List_map___main___at___private_Init_Lean_Elab_StructInst_8__expandCompositeFields___spec__1(x_13, x_16);
x_18 = l_List_append___rarg(x_17, x_11);
x_19 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_19, 0, x_9);
lean_ctor_set(x_19, 1, x_18);
lean_ctor_set(x_19, 2, x_10);
if (lean_is_scalar(x_12)) {
 x_20 = lean_alloc_ctor(1, 2, 0);
} else {
 x_20 = x_12;
}
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_6);
return x_20;
}
}
else
{
uint8_t x_24; 
lean_dec(x_8);
lean_free_object(x_1);
x_24 = !lean_is_exclusive(x_7);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_7, 1);
lean_dec(x_25);
x_26 = lean_ctor_get(x_7, 0);
lean_dec(x_26);
lean_ctor_set(x_7, 1, x_6);
lean_ctor_set(x_7, 0, x_4);
return x_7;
}
else
{
lean_object* x_27; 
lean_dec(x_7);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_4);
lean_ctor_set(x_27, 1, x_6);
return x_27;
}
}
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_1, 0);
x_29 = lean_ctor_get(x_1, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_1);
x_30 = l_List_map___main___at___private_Init_Lean_Elab_StructInst_8__expandCompositeFields___spec__2(x_29);
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; 
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_28);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
else
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_34 = lean_ctor_get(x_28, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_28, 2);
lean_inc(x_35);
x_36 = lean_ctor_get(x_31, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_37 = x_31;
} else {
 lean_dec_ref(x_31);
 x_37 = lean_box(0);
}
x_38 = lean_ctor_get(x_33, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_33, 1);
lean_inc(x_39);
lean_dec(x_33);
if (lean_obj_tag(x_39) == 1)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_39, 0);
lean_inc(x_47);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; 
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_28);
lean_ctor_set(x_48, 1, x_30);
return x_48;
}
else
{
lean_object* x_49; 
lean_dec(x_47);
lean_dec(x_28);
x_49 = lean_box(0);
x_40 = x_49;
goto block_46;
}
}
else
{
lean_object* x_50; 
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_28);
lean_ctor_set(x_50, 1, x_30);
return x_50;
}
block_46:
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_40);
x_41 = l_Lean_Name_components(x_39);
x_42 = l_List_map___main___at___private_Init_Lean_Elab_StructInst_8__expandCompositeFields___spec__1(x_38, x_41);
x_43 = l_List_append___rarg(x_42, x_36);
x_44 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_44, 0, x_34);
lean_ctor_set(x_44, 1, x_43);
lean_ctor_set(x_44, 2, x_35);
if (lean_is_scalar(x_37)) {
 x_45 = lean_alloc_ctor(1, 2, 0);
} else {
 x_45 = x_37;
}
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_30);
return x_45;
}
}
else
{
lean_object* x_51; lean_object* x_52; 
lean_dec(x_33);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_51 = x_31;
} else {
 lean_dec_ref(x_31);
 x_51 = lean_box(0);
}
if (lean_is_scalar(x_51)) {
 x_52 = lean_alloc_ctor(1, 2, 0);
} else {
 x_52 = x_51;
}
lean_ctor_set(x_52, 0, x_28);
lean_ctor_set(x_52, 1, x_30);
return x_52;
}
}
}
}
}
}
lean_object* _init_l___private_Init_Lean_Elab_StructInst_8__expandCompositeFields___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_List_map___main___at___private_Init_Lean_Elab_StructInst_8__expandCompositeFields___spec__2), 1, 0);
return x_1;
}
}
lean_object* l___private_Init_Lean_Elab_StructInst_8__expandCompositeFields(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l___private_Init_Lean_Elab_StructInst_8__expandCompositeFields___closed__1;
x_3 = l_Lean_Elab_Term_StructInst_Struct_modifyFieldsM___at_Lean_Elab_Term_StructInst_Struct_modifyFields___spec__1(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid field index, structure has only #");
return x_1;
}
}
lean_object* _init_l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" fields");
return x_1;
}
}
lean_object* _init_l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid field index, index must be greater than 0");
return x_1;
}
}
lean_object* _init_l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__7;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__8;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_9__expandNumLitFields___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_25; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_9 = x_2;
} else {
 lean_dec_ref(x_2);
 x_9 = lean_box(0);
}
x_25 = lean_ctor_get(x_7, 1);
lean_inc(x_25);
if (lean_obj_tag(x_25) == 0)
{
x_10 = x_7;
x_11 = x_4;
goto block_24;
}
else
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
if (lean_obj_tag(x_26) == 1)
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_7);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_28 = lean_ctor_get(x_7, 0);
x_29 = lean_ctor_get(x_7, 2);
x_30 = lean_ctor_get(x_7, 1);
lean_dec(x_30);
x_31 = !lean_is_exclusive(x_25);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_32 = lean_ctor_get(x_25, 1);
x_33 = lean_ctor_get(x_25, 0);
lean_dec(x_33);
x_34 = !lean_is_exclusive(x_26);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_35 = lean_ctor_get(x_26, 0);
x_36 = lean_ctor_get(x_26, 1);
x_37 = lean_unsigned_to_nat(0u);
x_38 = lean_nat_dec_eq(x_36, x_37);
if (x_38 == 0)
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_array_get_size(x_1);
x_40 = lean_nat_dec_lt(x_39, x_36);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_39);
x_41 = lean_unsigned_to_nat(1u);
x_42 = lean_nat_sub(x_36, x_41);
lean_dec(x_36);
x_43 = l_Lean_Name_inhabited;
x_44 = lean_array_get(x_43, x_1, x_42);
lean_dec(x_42);
lean_ctor_set_tag(x_26, 0);
lean_ctor_set(x_26, 1, x_44);
x_10 = x_7;
x_11 = x_4;
goto block_24;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
lean_free_object(x_26);
lean_dec(x_36);
lean_free_object(x_25);
lean_dec(x_32);
lean_free_object(x_7);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_9);
lean_dec(x_8);
x_45 = l_Nat_repr(x_39);
x_46 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_46, 0, x_45);
x_47 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_47, 0, x_46);
x_48 = l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__3;
x_49 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_47);
x_50 = l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__6;
x_51 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
x_52 = l_Lean_Elab_Term_throwError___rarg(x_35, x_51, x_3, x_4);
lean_dec(x_35);
x_53 = !lean_is_exclusive(x_52);
if (x_53 == 0)
{
return x_52;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_52, 0);
x_55 = lean_ctor_get(x_52, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_52);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
else
{
lean_object* x_57; lean_object* x_58; uint8_t x_59; 
lean_free_object(x_26);
lean_dec(x_36);
lean_free_object(x_25);
lean_dec(x_32);
lean_free_object(x_7);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_9);
lean_dec(x_8);
x_57 = l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__9;
x_58 = l_Lean_Elab_Term_throwError___rarg(x_35, x_57, x_3, x_4);
lean_dec(x_35);
x_59 = !lean_is_exclusive(x_58);
if (x_59 == 0)
{
return x_58;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_58, 0);
x_61 = lean_ctor_get(x_58, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_58);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_63 = lean_ctor_get(x_26, 0);
x_64 = lean_ctor_get(x_26, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_26);
x_65 = lean_unsigned_to_nat(0u);
x_66 = lean_nat_dec_eq(x_64, x_65);
if (x_66 == 0)
{
lean_object* x_67; uint8_t x_68; 
x_67 = lean_array_get_size(x_1);
x_68 = lean_nat_dec_lt(x_67, x_64);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_67);
x_69 = lean_unsigned_to_nat(1u);
x_70 = lean_nat_sub(x_64, x_69);
lean_dec(x_64);
x_71 = l_Lean_Name_inhabited;
x_72 = lean_array_get(x_71, x_1, x_70);
lean_dec(x_70);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_63);
lean_ctor_set(x_73, 1, x_72);
lean_ctor_set(x_25, 0, x_73);
x_10 = x_7;
x_11 = x_4;
goto block_24;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_64);
lean_free_object(x_25);
lean_dec(x_32);
lean_free_object(x_7);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_9);
lean_dec(x_8);
x_74 = l_Nat_repr(x_67);
x_75 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_75, 0, x_74);
x_76 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_76, 0, x_75);
x_77 = l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__3;
x_78 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_76);
x_79 = l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__6;
x_80 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
x_81 = l_Lean_Elab_Term_throwError___rarg(x_63, x_80, x_3, x_4);
lean_dec(x_63);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_84 = x_81;
} else {
 lean_dec_ref(x_81);
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
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_dec(x_64);
lean_free_object(x_25);
lean_dec(x_32);
lean_free_object(x_7);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_9);
lean_dec(x_8);
x_86 = l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__9;
x_87 = l_Lean_Elab_Term_throwError___rarg(x_63, x_86, x_3, x_4);
lean_dec(x_63);
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 x_90 = x_87;
} else {
 lean_dec_ref(x_87);
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
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; 
x_92 = lean_ctor_get(x_25, 1);
lean_inc(x_92);
lean_dec(x_25);
x_93 = lean_ctor_get(x_26, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_26, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_95 = x_26;
} else {
 lean_dec_ref(x_26);
 x_95 = lean_box(0);
}
x_96 = lean_unsigned_to_nat(0u);
x_97 = lean_nat_dec_eq(x_94, x_96);
if (x_97 == 0)
{
lean_object* x_98; uint8_t x_99; 
x_98 = lean_array_get_size(x_1);
x_99 = lean_nat_dec_lt(x_98, x_94);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_dec(x_98);
x_100 = lean_unsigned_to_nat(1u);
x_101 = lean_nat_sub(x_94, x_100);
lean_dec(x_94);
x_102 = l_Lean_Name_inhabited;
x_103 = lean_array_get(x_102, x_1, x_101);
lean_dec(x_101);
if (lean_is_scalar(x_95)) {
 x_104 = lean_alloc_ctor(0, 2, 0);
} else {
 x_104 = x_95;
 lean_ctor_set_tag(x_104, 0);
}
lean_ctor_set(x_104, 0, x_93);
lean_ctor_set(x_104, 1, x_103);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_92);
lean_ctor_set(x_7, 1, x_105);
x_10 = x_7;
x_11 = x_4;
goto block_24;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_92);
lean_free_object(x_7);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_9);
lean_dec(x_8);
x_106 = l_Nat_repr(x_98);
x_107 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_107, 0, x_106);
x_108 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_108, 0, x_107);
x_109 = l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__3;
x_110 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_108);
x_111 = l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__6;
x_112 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
x_113 = l_Lean_Elab_Term_throwError___rarg(x_93, x_112, x_3, x_4);
lean_dec(x_93);
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_113, 1);
lean_inc(x_115);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 lean_ctor_release(x_113, 1);
 x_116 = x_113;
} else {
 lean_dec_ref(x_113);
 x_116 = lean_box(0);
}
if (lean_is_scalar(x_116)) {
 x_117 = lean_alloc_ctor(1, 2, 0);
} else {
 x_117 = x_116;
}
lean_ctor_set(x_117, 0, x_114);
lean_ctor_set(x_117, 1, x_115);
return x_117;
}
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_92);
lean_free_object(x_7);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_9);
lean_dec(x_8);
x_118 = l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__9;
x_119 = l_Lean_Elab_Term_throwError___rarg(x_93, x_118, x_3, x_4);
lean_dec(x_93);
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_119, 1);
lean_inc(x_121);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 x_122 = x_119;
} else {
 lean_dec_ref(x_119);
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
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; uint8_t x_132; 
x_124 = lean_ctor_get(x_7, 0);
x_125 = lean_ctor_get(x_7, 2);
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_7);
x_126 = lean_ctor_get(x_25, 1);
lean_inc(x_126);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_127 = x_25;
} else {
 lean_dec_ref(x_25);
 x_127 = lean_box(0);
}
x_128 = lean_ctor_get(x_26, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_26, 1);
lean_inc(x_129);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_130 = x_26;
} else {
 lean_dec_ref(x_26);
 x_130 = lean_box(0);
}
x_131 = lean_unsigned_to_nat(0u);
x_132 = lean_nat_dec_eq(x_129, x_131);
if (x_132 == 0)
{
lean_object* x_133; uint8_t x_134; 
x_133 = lean_array_get_size(x_1);
x_134 = lean_nat_dec_lt(x_133, x_129);
if (x_134 == 0)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
lean_dec(x_133);
x_135 = lean_unsigned_to_nat(1u);
x_136 = lean_nat_sub(x_129, x_135);
lean_dec(x_129);
x_137 = l_Lean_Name_inhabited;
x_138 = lean_array_get(x_137, x_1, x_136);
lean_dec(x_136);
if (lean_is_scalar(x_130)) {
 x_139 = lean_alloc_ctor(0, 2, 0);
} else {
 x_139 = x_130;
 lean_ctor_set_tag(x_139, 0);
}
lean_ctor_set(x_139, 0, x_128);
lean_ctor_set(x_139, 1, x_138);
if (lean_is_scalar(x_127)) {
 x_140 = lean_alloc_ctor(1, 2, 0);
} else {
 x_140 = x_127;
}
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_126);
x_141 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_141, 0, x_124);
lean_ctor_set(x_141, 1, x_140);
lean_ctor_set(x_141, 2, x_125);
x_10 = x_141;
x_11 = x_4;
goto block_24;
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
lean_dec(x_130);
lean_dec(x_129);
lean_dec(x_127);
lean_dec(x_126);
lean_dec(x_125);
lean_dec(x_124);
lean_dec(x_9);
lean_dec(x_8);
x_142 = l_Nat_repr(x_133);
x_143 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_143, 0, x_142);
x_144 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_144, 0, x_143);
x_145 = l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__3;
x_146 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_146, 0, x_145);
lean_ctor_set(x_146, 1, x_144);
x_147 = l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__6;
x_148 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_148, 0, x_146);
lean_ctor_set(x_148, 1, x_147);
x_149 = l_Lean_Elab_Term_throwError___rarg(x_128, x_148, x_3, x_4);
lean_dec(x_128);
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_149, 1);
lean_inc(x_151);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 lean_ctor_release(x_149, 1);
 x_152 = x_149;
} else {
 lean_dec_ref(x_149);
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
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
lean_dec(x_130);
lean_dec(x_129);
lean_dec(x_127);
lean_dec(x_126);
lean_dec(x_125);
lean_dec(x_124);
lean_dec(x_9);
lean_dec(x_8);
x_154 = l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__9;
x_155 = l_Lean_Elab_Term_throwError___rarg(x_128, x_154, x_3, x_4);
lean_dec(x_128);
x_156 = lean_ctor_get(x_155, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_155, 1);
lean_inc(x_157);
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 lean_ctor_release(x_155, 1);
 x_158 = x_155;
} else {
 lean_dec_ref(x_155);
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
lean_dec(x_26);
lean_dec(x_25);
x_10 = x_7;
x_11 = x_4;
goto block_24;
}
}
block_24:
{
lean_object* x_12; 
x_12 = l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_9__expandNumLitFields___spec__1(x_1, x_8, x_3, x_11);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
if (lean_is_scalar(x_9)) {
 x_15 = lean_alloc_ctor(1, 2, 0);
} else {
 x_15 = x_9;
}
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_14);
lean_ctor_set(x_12, 0, x_15);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_12, 0);
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_12);
if (lean_is_scalar(x_9)) {
 x_18 = lean_alloc_ctor(1, 2, 0);
} else {
 x_18 = x_9;
}
lean_ctor_set(x_18, 0, x_10);
lean_ctor_set(x_18, 1, x_16);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
else
{
uint8_t x_20; 
lean_dec(x_10);
lean_dec(x_9);
x_20 = !lean_is_exclusive(x_12);
if (x_20 == 0)
{
return x_12;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_12, 0);
x_22 = lean_ctor_get(x_12, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_12);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
}
}
lean_object* l_Lean_Elab_Term_StructInst_Struct_modifyFieldsM___at___private_Init_Lean_Elab_StructInst_9__expandNumLitFields___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get(x_1, 2);
x_9 = lean_ctor_get(x_1, 3);
x_10 = lean_apply_3(x_2, x_8, x_3, x_4);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_10, 0);
lean_ctor_set(x_1, 2, x_12);
lean_ctor_set(x_10, 0, x_1);
return x_10;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_10, 0);
x_14 = lean_ctor_get(x_10, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_10);
lean_ctor_set(x_1, 2, x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
else
{
uint8_t x_16; 
lean_free_object(x_1);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_16 = !lean_is_exclusive(x_10);
if (x_16 == 0)
{
return x_10;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_10, 0);
x_18 = lean_ctor_get(x_10, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_10);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_1, 0);
x_21 = lean_ctor_get(x_1, 1);
x_22 = lean_ctor_get(x_1, 2);
x_23 = lean_ctor_get(x_1, 3);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_1);
x_24 = lean_apply_3(x_2, x_22, x_3, x_4);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
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
x_28 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_28, 0, x_20);
lean_ctor_set(x_28, 1, x_21);
lean_ctor_set(x_28, 2, x_25);
lean_ctor_set(x_28, 3, x_23);
if (lean_is_scalar(x_27)) {
 x_29 = lean_alloc_ctor(0, 2, 0);
} else {
 x_29 = x_27;
}
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_26);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_20);
x_30 = lean_ctor_get(x_24, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_24, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_32 = x_24;
} else {
 lean_dec_ref(x_24);
 x_32 = lean_box(0);
}
if (lean_is_scalar(x_32)) {
 x_33 = lean_alloc_ctor(1, 2, 0);
} else {
 x_33 = x_32;
}
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
}
}
lean_object* l___private_Init_Lean_Elab_StructInst_9__expandNumLitFields___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = l_Lean_Elab_Term_getEnv___rarg(x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l_Lean_Elab_Term_StructInst_Struct_structName(x_1);
x_9 = l_Lean_getStructureFields(x_6, x_8);
x_10 = l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_9__expandNumLitFields___spec__1(x_9, x_2, x_3, x_7);
lean_dec(x_9);
return x_10;
}
}
lean_object* l___private_Init_Lean_Elab_StructInst_9__expandNumLitFields(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
lean_inc(x_1);
x_4 = lean_alloc_closure((void*)(l___private_Init_Lean_Elab_StructInst_9__expandNumLitFields___lambda__1___boxed), 4, 1);
lean_closure_set(x_4, 0, x_1);
x_5 = l_Lean_Elab_Term_StructInst_Struct_modifyFieldsM___at___private_Init_Lean_Elab_StructInst_9__expandNumLitFields___spec__2(x_1, x_4, x_2, x_3);
return x_5;
}
}
lean_object* l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_9__expandNumLitFields___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l___private_Init_Lean_Elab_StructInst_9__expandNumLitFields___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Lean_Elab_StructInst_9__expandNumLitFields___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_List_map___main___at___private_Init_Lean_Elab_StructInst_10__expandParentFields___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec(x_1);
x_3 = lean_box(0);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_1);
x_7 = l_List_map___main___at___private_Init_Lean_Elab_StructInst_10__expandParentFields___spec__1(x_1, x_6);
if (lean_obj_tag(x_5) == 1)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec(x_5);
x_9 = lean_box(0);
x_10 = lean_name_mk_string(x_9, x_8);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set(x_2, 1, x_7);
lean_ctor_set(x_2, 0, x_11);
return x_2;
}
else
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_5);
lean_dec(x_1);
x_12 = l_Lean_Elab_Term_StructInst_FieldLHS_inhabited;
x_13 = l_unreachable_x21___rarg(x_12);
lean_ctor_set(x_2, 1, x_7);
lean_ctor_set(x_2, 0, x_13);
return x_2;
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_2, 0);
x_15 = lean_ctor_get(x_2, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_2);
lean_inc(x_1);
x_16 = l_List_map___main___at___private_Init_Lean_Elab_StructInst_10__expandParentFields___spec__1(x_1, x_15);
if (lean_obj_tag(x_14) == 1)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_box(0);
x_19 = lean_name_mk_string(x_18, x_17);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_1);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_16);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_14);
lean_dec(x_1);
x_22 = l_Lean_Elab_Term_StructInst_FieldLHS_inhabited;
x_23 = l_unreachable_x21___rarg(x_22);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_16);
return x_24;
}
}
}
}
}
lean_object* _init_l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' is not a field of structure '");
return x_1;
}
}
lean_object* _init_l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("failed to access field '");
return x_1;
}
}
lean_object* _init_l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' in parent structure");
return x_1;
}
}
lean_object* _init_l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__7;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__8;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_10__expandParentFields___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_4);
lean_dec(x_2);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_26; 
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_10 = x_3;
} else {
 lean_dec_ref(x_3);
 x_10 = lean_box(0);
}
x_26 = lean_ctor_get(x_8, 1);
lean_inc(x_26);
if (lean_obj_tag(x_26) == 0)
{
x_11 = x_8;
x_12 = x_5;
goto block_25;
}
else
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_28 = lean_ctor_get(x_8, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_8, 2);
lean_inc(x_29);
x_30 = lean_ctor_get(x_27, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_27, 1);
lean_inc(x_31);
lean_dec(x_27);
x_32 = l_Lean_Elab_Term_StructInst_Struct_structName(x_1);
lean_inc(x_32);
lean_inc(x_2);
x_33 = l_Lean_findField_x3f___main(x_2, x_32, x_31);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
x_34 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_34, 0, x_31);
x_35 = l_Array_forMAux___main___at_Lean_Meta_clear___spec__5___closed__8;
x_36 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
x_37 = l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__3;
x_38 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_39, 0, x_32);
x_40 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_35);
x_42 = l_Lean_Elab_Term_throwError___rarg(x_30, x_41, x_4, x_5);
lean_dec(x_30);
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
return x_42;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_42, 0);
x_45 = lean_ctor_get(x_42, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_42);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
else
{
lean_object* x_47; uint8_t x_48; 
x_47 = lean_ctor_get(x_33, 0);
lean_inc(x_47);
lean_dec(x_33);
x_48 = lean_name_eq(x_47, x_32);
if (x_48 == 0)
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_8);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_50 = lean_ctor_get(x_8, 2);
lean_dec(x_50);
x_51 = lean_ctor_get(x_8, 1);
lean_dec(x_51);
x_52 = lean_ctor_get(x_8, 0);
lean_dec(x_52);
lean_inc(x_2);
x_53 = l_Lean_getPathToBaseStructure_x3f(x_2, x_47, x_32);
lean_dec(x_47);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
lean_free_object(x_8);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_2);
x_54 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_54, 0, x_31);
x_55 = l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__6;
x_56 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_54);
x_57 = l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__9;
x_58 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
x_59 = l_Lean_Elab_Term_throwError___rarg(x_30, x_58, x_4, x_5);
lean_dec(x_30);
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
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_31);
x_64 = lean_ctor_get(x_53, 0);
lean_inc(x_64);
lean_dec(x_53);
x_65 = l_List_map___main___at___private_Init_Lean_Elab_StructInst_10__expandParentFields___spec__1(x_30, x_64);
x_66 = l_List_append___rarg(x_65, x_26);
lean_ctor_set(x_8, 1, x_66);
x_11 = x_8;
x_12 = x_5;
goto block_25;
}
}
else
{
lean_object* x_67; 
lean_dec(x_8);
lean_inc(x_2);
x_67 = l_Lean_getPathToBaseStructure_x3f(x_2, x_47, x_32);
lean_dec(x_47);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_2);
x_68 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_68, 0, x_31);
x_69 = l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__6;
x_70 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_68);
x_71 = l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__9;
x_72 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
x_73 = l_Lean_Elab_Term_throwError___rarg(x_30, x_72, x_4, x_5);
lean_dec(x_30);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_76 = x_73;
} else {
 lean_dec_ref(x_73);
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
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_31);
x_78 = lean_ctor_get(x_67, 0);
lean_inc(x_78);
lean_dec(x_67);
x_79 = l_List_map___main___at___private_Init_Lean_Elab_StructInst_10__expandParentFields___spec__1(x_30, x_78);
x_80 = l_List_append___rarg(x_79, x_26);
x_81 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_81, 0, x_28);
lean_ctor_set(x_81, 1, x_80);
lean_ctor_set(x_81, 2, x_29);
x_11 = x_81;
x_12 = x_5;
goto block_25;
}
}
}
else
{
lean_dec(x_47);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_26);
x_11 = x_8;
x_12 = x_5;
goto block_25;
}
}
}
else
{
lean_dec(x_27);
lean_dec(x_26);
x_11 = x_8;
x_12 = x_5;
goto block_25;
}
}
block_25:
{
lean_object* x_13; 
x_13 = l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_10__expandParentFields___spec__2(x_1, x_2, x_9, x_4, x_12);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
if (lean_is_scalar(x_10)) {
 x_16 = lean_alloc_ctor(1, 2, 0);
} else {
 x_16 = x_10;
}
lean_ctor_set(x_16, 0, x_11);
lean_ctor_set(x_16, 1, x_15);
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
if (lean_is_scalar(x_10)) {
 x_19 = lean_alloc_ctor(1, 2, 0);
} else {
 x_19 = x_10;
}
lean_ctor_set(x_19, 0, x_11);
lean_ctor_set(x_19, 1, x_17);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
else
{
uint8_t x_21; 
lean_dec(x_11);
lean_dec(x_10);
x_21 = !lean_is_exclusive(x_13);
if (x_21 == 0)
{
return x_13;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_13, 0);
x_23 = lean_ctor_get(x_13, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_13);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
}
}
lean_object* l___private_Init_Lean_Elab_StructInst_10__expandParentFields(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = l_Lean_Elab_Term_getEnv___rarg(x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
lean_inc(x_1);
x_7 = lean_alloc_closure((void*)(l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_10__expandParentFields___spec__2___boxed), 5, 2);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_5);
x_8 = l_Lean_Elab_Term_StructInst_Struct_modifyFieldsM___at___private_Init_Lean_Elab_StructInst_9__expandNumLitFields___spec__2(x_1, x_7, x_2, x_6);
return x_8;
}
}
lean_object* l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_10__expandParentFields___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_10__expandParentFields___spec__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_AssocList_find___main___at___private_Init_Lean_Elab_StructInst_12__mkFieldMap___spec__2(lean_object* x_1, lean_object* x_2) {
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
x_7 = lean_name_eq(x_4, x_1);
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
lean_object* l_HashMapImp_find_x3f___at___private_Init_Lean_Elab_StructInst_12__mkFieldMap___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; size_t x_5; size_t x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Lean_Name_hash(x_2);
x_6 = lean_usize_modn(x_5, x_4);
lean_dec(x_4);
x_7 = lean_array_uget(x_3, x_6);
x_8 = l_AssocList_find___main___at___private_Init_Lean_Elab_StructInst_12__mkFieldMap___spec__2(x_2, x_7);
lean_dec(x_7);
return x_8;
}
}
uint8_t l_AssocList_contains___main___at___private_Init_Lean_Elab_StructInst_12__mkFieldMap___spec__4(lean_object* x_1, lean_object* x_2) {
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
x_6 = lean_name_eq(x_4, x_1);
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
lean_object* l_AssocList_foldlM___main___at___private_Init_Lean_Elab_StructInst_12__mkFieldMap___spec__7(lean_object* x_1, lean_object* x_2) {
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
x_7 = l_Lean_Name_hash(x_4);
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
x_16 = l_Lean_Name_hash(x_12);
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
lean_object* l_HashMapImp_moveEntries___main___at___private_Init_Lean_Elab_StructInst_12__mkFieldMap___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_AssocList_foldlM___main___at___private_Init_Lean_Elab_StructInst_12__mkFieldMap___spec__7(x_3, x_6);
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
lean_object* l_HashMapImp_expand___at___private_Init_Lean_Elab_StructInst_12__mkFieldMap___spec__5(lean_object* x_1, lean_object* x_2) {
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
x_9 = l_HashMapImp_moveEntries___main___at___private_Init_Lean_Elab_StructInst_12__mkFieldMap___spec__6(x_8, x_2, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
lean_object* l_AssocList_replace___main___at___private_Init_Lean_Elab_StructInst_12__mkFieldMap___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_8 = lean_name_eq(x_5, x_1);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = l_AssocList_replace___main___at___private_Init_Lean_Elab_StructInst_12__mkFieldMap___spec__8(x_1, x_2, x_7);
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
x_13 = lean_name_eq(x_10, x_1);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_AssocList_replace___main___at___private_Init_Lean_Elab_StructInst_12__mkFieldMap___spec__8(x_1, x_2, x_12);
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
lean_object* l_HashMapImp_insert___at___private_Init_Lean_Elab_StructInst_12__mkFieldMap___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_8 = l_Lean_Name_hash(x_2);
x_9 = lean_usize_modn(x_8, x_7);
x_10 = lean_array_uget(x_6, x_9);
x_11 = l_AssocList_contains___main___at___private_Init_Lean_Elab_StructInst_12__mkFieldMap___spec__4(x_2, x_10);
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
x_17 = l_HashMapImp_expand___at___private_Init_Lean_Elab_StructInst_12__mkFieldMap___spec__5(x_13, x_15);
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
x_18 = l_AssocList_replace___main___at___private_Init_Lean_Elab_StructInst_12__mkFieldMap___spec__8(x_2, x_3, x_10);
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
x_23 = l_Lean_Name_hash(x_2);
x_24 = lean_usize_modn(x_23, x_22);
x_25 = lean_array_uget(x_21, x_24);
x_26 = l_AssocList_contains___main___at___private_Init_Lean_Elab_StructInst_12__mkFieldMap___spec__4(x_2, x_25);
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
x_32 = l_HashMapImp_expand___at___private_Init_Lean_Elab_StructInst_12__mkFieldMap___spec__5(x_28, x_30);
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
x_34 = l_AssocList_replace___main___at___private_Init_Lean_Elab_StructInst_12__mkFieldMap___spec__8(x_2, x_3, x_25);
x_35 = lean_array_uset(x_21, x_24, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_20);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
lean_object* l_mkHashMap___at___private_Init_Lean_Elab_StructInst_12__mkFieldMap___spec__9(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_mkHashMapImp___rarg(x_1);
return x_2;
}
}
lean_object* _init_l_List_foldlM___main___at___private_Init_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("field '");
return x_1;
}
}
lean_object* _init_l_List_foldlM___main___at___private_Init_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_foldlM___main___at___private_Init_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_List_foldlM___main___at___private_Init_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_foldlM___main___at___private_Init_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_List_foldlM___main___at___private_Init_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' has already beed specified");
return x_1;
}
}
lean_object* _init_l_List_foldlM___main___at___private_Init_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_foldlM___main___at___private_Init_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_List_foldlM___main___at___private_Init_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_foldlM___main___at___private_Init_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_List_foldlM___main___at___private_Init_Lean_Elab_StructInst_12__mkFieldMap___spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; 
lean_dec(x_3);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_6);
lean_dec(x_1);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
lean_dec(x_2);
x_9 = l___private_Init_Lean_Elab_Quotation_5__quoteSyntax___main___closed__1;
x_10 = l_unreachable_x21___rarg(x_9);
lean_inc(x_3);
x_11 = lean_apply_2(x_10, x_3, x_4);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_1 = x_12;
x_2 = x_8;
x_4 = x_13;
goto _start;
}
else
{
uint8_t x_15; 
lean_dec(x_8);
lean_dec(x_3);
x_15 = !lean_is_exclusive(x_11);
if (x_15 == 0)
{
return x_11;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_11, 0);
x_17 = lean_ctor_get(x_11, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_11);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_7);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_7, 0);
x_21 = lean_ctor_get(x_7, 1);
lean_dec(x_21);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_2, 1);
lean_inc(x_22);
lean_dec(x_2);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = l_HashMapImp_find_x3f___at___private_Init_Lean_Elab_StructInst_12__mkFieldMap___spec__1(x_1, x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_box(0);
lean_ctor_set(x_7, 1, x_25);
lean_ctor_set(x_7, 0, x_6);
x_26 = l_HashMapImp_insert___at___private_Init_Lean_Elab_StructInst_12__mkFieldMap___spec__3(x_1, x_23, x_7);
x_1 = x_26;
x_2 = x_22;
goto _start;
}
else
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_24, 0);
lean_inc(x_28);
lean_dec(x_24);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; 
lean_ctor_set(x_7, 1, x_28);
lean_ctor_set(x_7, 0, x_6);
x_29 = l_HashMapImp_insert___at___private_Init_Lean_Elab_StructInst_12__mkFieldMap___spec__3(x_1, x_23, x_7);
x_1 = x_29;
x_2 = x_22;
goto _start;
}
else
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_ctor_get(x_28, 0);
lean_inc(x_31);
x_32 = l_Lean_Elab_Term_StructInst_Field_isSimple___rarg(x_6);
if (x_32 == 0)
{
uint8_t x_33; 
x_33 = l_Lean_Elab_Term_StructInst_Field_isSimple___rarg(x_31);
lean_dec(x_31);
if (x_33 == 0)
{
lean_object* x_34; 
lean_ctor_set(x_7, 1, x_28);
lean_ctor_set(x_7, 0, x_6);
x_34 = l_HashMapImp_insert___at___private_Init_Lean_Elab_StructInst_12__mkFieldMap___spec__3(x_1, x_23, x_7);
x_1 = x_34;
x_2 = x_22;
goto _start;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
lean_dec(x_28);
lean_dec(x_22);
lean_free_object(x_7);
lean_dec(x_1);
x_36 = lean_ctor_get(x_6, 0);
lean_inc(x_36);
lean_dec(x_6);
x_37 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_37, 0, x_23);
x_38 = l_List_foldlM___main___at___private_Init_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__3;
x_39 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
x_40 = l_List_foldlM___main___at___private_Init_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__6;
x_41 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_Lean_Elab_Term_throwError___rarg(x_36, x_41, x_3, x_4);
lean_dec(x_36);
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
return x_42;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_42, 0);
x_45 = lean_ctor_get(x_42, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_42);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
lean_dec(x_31);
lean_dec(x_28);
lean_dec(x_22);
lean_free_object(x_7);
lean_dec(x_1);
x_47 = lean_ctor_get(x_6, 0);
lean_inc(x_47);
lean_dec(x_6);
x_48 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_48, 0, x_23);
x_49 = l_List_foldlM___main___at___private_Init_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__3;
x_50 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_48);
x_51 = l_List_foldlM___main___at___private_Init_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__6;
x_52 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
x_53 = l_Lean_Elab_Term_throwError___rarg(x_47, x_52, x_3, x_4);
lean_dec(x_47);
x_54 = !lean_is_exclusive(x_53);
if (x_54 == 0)
{
return x_53;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_53, 0);
x_56 = lean_ctor_get(x_53, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_53);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_free_object(x_7);
lean_dec(x_20);
lean_dec(x_6);
lean_dec(x_1);
x_58 = lean_ctor_get(x_2, 1);
lean_inc(x_58);
lean_dec(x_2);
x_59 = l___private_Init_Lean_Elab_Quotation_5__quoteSyntax___main___closed__1;
x_60 = l_unreachable_x21___rarg(x_59);
lean_inc(x_3);
x_61 = lean_apply_2(x_60, x_3, x_4);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_1 = x_62;
x_2 = x_58;
x_4 = x_63;
goto _start;
}
else
{
uint8_t x_65; 
lean_dec(x_58);
lean_dec(x_3);
x_65 = !lean_is_exclusive(x_61);
if (x_65 == 0)
{
return x_61;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_61, 0);
x_67 = lean_ctor_get(x_61, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_61);
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
lean_object* x_69; 
x_69 = lean_ctor_get(x_7, 0);
lean_inc(x_69);
lean_dec(x_7);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_2, 1);
lean_inc(x_70);
lean_dec(x_2);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_72 = l_HashMapImp_find_x3f___at___private_Init_Lean_Elab_StructInst_12__mkFieldMap___spec__1(x_1, x_71);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_box(0);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_6);
lean_ctor_set(x_74, 1, x_73);
x_75 = l_HashMapImp_insert___at___private_Init_Lean_Elab_StructInst_12__mkFieldMap___spec__3(x_1, x_71, x_74);
x_1 = x_75;
x_2 = x_70;
goto _start;
}
else
{
lean_object* x_77; 
x_77 = lean_ctor_get(x_72, 0);
lean_inc(x_77);
lean_dec(x_72);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_6);
lean_ctor_set(x_78, 1, x_77);
x_79 = l_HashMapImp_insert___at___private_Init_Lean_Elab_StructInst_12__mkFieldMap___spec__3(x_1, x_71, x_78);
x_1 = x_79;
x_2 = x_70;
goto _start;
}
else
{
lean_object* x_81; uint8_t x_82; 
x_81 = lean_ctor_get(x_77, 0);
lean_inc(x_81);
x_82 = l_Lean_Elab_Term_StructInst_Field_isSimple___rarg(x_6);
if (x_82 == 0)
{
uint8_t x_83; 
x_83 = l_Lean_Elab_Term_StructInst_Field_isSimple___rarg(x_81);
lean_dec(x_81);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_6);
lean_ctor_set(x_84, 1, x_77);
x_85 = l_HashMapImp_insert___at___private_Init_Lean_Elab_StructInst_12__mkFieldMap___spec__3(x_1, x_71, x_84);
x_1 = x_85;
x_2 = x_70;
goto _start;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_77);
lean_dec(x_70);
lean_dec(x_1);
x_87 = lean_ctor_get(x_6, 0);
lean_inc(x_87);
lean_dec(x_6);
x_88 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_88, 0, x_71);
x_89 = l_List_foldlM___main___at___private_Init_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__3;
x_90 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_88);
x_91 = l_List_foldlM___main___at___private_Init_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__6;
x_92 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
x_93 = l_Lean_Elab_Term_throwError___rarg(x_87, x_92, x_3, x_4);
lean_dec(x_87);
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 lean_ctor_release(x_93, 1);
 x_96 = x_93;
} else {
 lean_dec_ref(x_93);
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
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
lean_dec(x_81);
lean_dec(x_77);
lean_dec(x_70);
lean_dec(x_1);
x_98 = lean_ctor_get(x_6, 0);
lean_inc(x_98);
lean_dec(x_6);
x_99 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_99, 0, x_71);
x_100 = l_List_foldlM___main___at___private_Init_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__3;
x_101 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_99);
x_102 = l_List_foldlM___main___at___private_Init_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__6;
x_103 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
x_104 = l_Lean_Elab_Term_throwError___rarg(x_98, x_103, x_3, x_4);
lean_dec(x_98);
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
if (lean_is_exclusive(x_104)) {
 lean_ctor_release(x_104, 0);
 lean_ctor_release(x_104, 1);
 x_107 = x_104;
} else {
 lean_dec_ref(x_104);
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
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
lean_dec(x_69);
lean_dec(x_6);
lean_dec(x_1);
x_109 = lean_ctor_get(x_2, 1);
lean_inc(x_109);
lean_dec(x_2);
x_110 = l___private_Init_Lean_Elab_Quotation_5__quoteSyntax___main___closed__1;
x_111 = l_unreachable_x21___rarg(x_110);
lean_inc(x_3);
x_112 = lean_apply_2(x_111, x_3, x_4);
if (lean_obj_tag(x_112) == 0)
{
lean_object* x_113; lean_object* x_114; 
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_112, 1);
lean_inc(x_114);
lean_dec(x_112);
x_1 = x_113;
x_2 = x_109;
x_4 = x_114;
goto _start;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
lean_dec(x_109);
lean_dec(x_3);
x_116 = lean_ctor_get(x_112, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_112, 1);
lean_inc(x_117);
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 lean_ctor_release(x_112, 1);
 x_118 = x_112;
} else {
 lean_dec_ref(x_112);
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
}
}
}
}
lean_object* _init_l___private_Init_Lean_Elab_StructInst_12__mkFieldMap___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_mkHashMapImp___rarg(x_1);
return x_2;
}
}
lean_object* l___private_Init_Lean_Elab_StructInst_12__mkFieldMap(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l___private_Init_Lean_Elab_StructInst_12__mkFieldMap___closed__1;
x_5 = l_List_foldlM___main___at___private_Init_Lean_Elab_StructInst_12__mkFieldMap___spec__10(x_4, x_1, x_2, x_3);
return x_5;
}
}
lean_object* l_AssocList_find___main___at___private_Init_Lean_Elab_StructInst_12__mkFieldMap___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_AssocList_find___main___at___private_Init_Lean_Elab_StructInst_12__mkFieldMap___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_HashMapImp_find_x3f___at___private_Init_Lean_Elab_StructInst_12__mkFieldMap___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_HashMapImp_find_x3f___at___private_Init_Lean_Elab_StructInst_12__mkFieldMap___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_AssocList_contains___main___at___private_Init_Lean_Elab_StructInst_12__mkFieldMap___spec__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_AssocList_contains___main___at___private_Init_Lean_Elab_StructInst_12__mkFieldMap___spec__4(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l___private_Init_Lean_Elab_StructInst_13__isSimpleField_x3f(lean_object* x_1) {
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
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = l_Lean_Elab_Term_StructInst_Field_isSimple___rarg(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; 
lean_inc(x_4);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_4);
return x_7;
}
}
else
{
lean_object* x_8; 
x_8 = lean_box(0);
return x_8;
}
}
}
}
lean_object* l___private_Init_Lean_Elab_StructInst_13__isSimpleField_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Init_Lean_Elab_StructInst_13__isSimpleField_x3f(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Array_findIdxAux___main___at___private_Init_Lean_Elab_StructInst_14__getFieldIdx___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_3, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_3);
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_fget(x_2, x_3);
x_8 = lean_name_eq(x_7, x_1);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_3, x_9);
lean_dec(x_3);
x_3 = x_10;
goto _start;
}
else
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_3);
return x_12;
}
}
}
}
lean_object* _init_l___private_Init_Lean_Elab_StructInst_14__getFieldIdx___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' is not a valid field of '");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Elab_StructInst_14__getFieldIdx___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_StructInst_14__getFieldIdx___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_StructInst_14__getFieldIdx___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_StructInst_14__getFieldIdx___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Init_Lean_Elab_StructInst_14__getFieldIdx(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Array_findIdxAux___main___at___private_Init_Lean_Elab_StructInst_14__getFieldIdx___spec__1(x_4, x_3, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_9 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_9, 0, x_4);
x_10 = l_List_foldlM___main___at___private_Init_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__3;
x_11 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
x_12 = l___private_Init_Lean_Elab_StructInst_14__getFieldIdx___closed__3;
x_13 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_14, 0, x_2);
x_15 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Array_forMAux___main___at_Lean_Meta_clear___spec__5___closed__8;
x_17 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lean_Elab_Term_throwError___rarg(x_1, x_17, x_5, x_6);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_19 = lean_ctor_get(x_8, 0);
lean_inc(x_19);
lean_dec(x_8);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_6);
return x_20;
}
}
}
lean_object* l_Array_findIdxAux___main___at___private_Init_Lean_Elab_StructInst_14__getFieldIdx___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_findIdxAux___main___at___private_Init_Lean_Elab_StructInst_14__getFieldIdx___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Init_Lean_Elab_StructInst_14__getFieldIdx___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Lean_Elab_StructInst_14__getFieldIdx(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_1);
return x_7;
}
}
lean_object* l___private_Init_Lean_Elab_StructInst_15__mkProjStx(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_3 = l_Lean_Name_toString___closed__1;
x_4 = l_Lean_mkAtomFrom(x_1, x_3);
x_5 = l_Lean_mkIdentFrom(x_1, x_2);
x_6 = l_Lean_Parser_declareBuiltinParser___closed__8;
x_7 = lean_array_push(x_6, x_1);
x_8 = lean_array_push(x_7, x_4);
x_9 = lean_array_push(x_8, x_5);
x_10 = l_Lean_Parser_Term_proj___elambda__1___closed__2;
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
lean_object* l___private_Init_Lean_Elab_StructInst_16__mkSubstructSource(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_5) == 2)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_5, 0);
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_4);
lean_inc(x_2);
x_11 = l___private_Init_Lean_Elab_StructInst_14__getFieldIdx(x_1, x_2, x_3, x_4, x_6, x_7);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = l_Lean_mkProj(x_2, x_13, x_10);
if (lean_obj_tag(x_9) == 1)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_9);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_16 = lean_ctor_get(x_9, 0);
x_17 = lean_ctor_get(x_9, 1);
x_18 = lean_array_get_size(x_17);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_dec_lt(x_19, x_18);
lean_dec(x_18);
if (x_20 == 0)
{
lean_dec(x_4);
lean_ctor_set(x_5, 1, x_14);
lean_ctor_set(x_11, 0, x_5);
return x_11;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_array_fget(x_17, x_19);
x_22 = lean_box(0);
x_23 = lean_array_fset(x_17, x_19, x_22);
switch (lean_obj_tag(x_21)) {
case 1:
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_21);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_25 = lean_ctor_get(x_21, 1);
x_26 = lean_array_get_size(x_25);
x_27 = lean_unsigned_to_nat(0u);
x_28 = lean_nat_dec_lt(x_27, x_26);
lean_dec(x_26);
if (x_28 == 0)
{
lean_object* x_29; 
lean_dec(x_4);
x_29 = lean_array_fset(x_23, x_19, x_21);
lean_ctor_set(x_9, 1, x_29);
lean_ctor_set(x_5, 1, x_14);
lean_ctor_set(x_11, 0, x_5);
return x_11;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_30 = lean_array_fget(x_25, x_27);
x_31 = lean_array_fset(x_25, x_27, x_22);
x_32 = l___private_Init_Lean_Elab_StructInst_15__mkProjStx(x_30, x_4);
x_33 = lean_array_fset(x_31, x_27, x_32);
lean_ctor_set(x_21, 1, x_33);
x_34 = lean_array_fset(x_23, x_19, x_21);
lean_ctor_set(x_9, 1, x_34);
lean_ctor_set(x_5, 1, x_14);
lean_ctor_set(x_11, 0, x_5);
return x_11;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_35 = lean_ctor_get(x_21, 0);
x_36 = lean_ctor_get(x_21, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_21);
x_37 = lean_array_get_size(x_36);
x_38 = lean_unsigned_to_nat(0u);
x_39 = lean_nat_dec_lt(x_38, x_37);
lean_dec(x_37);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
lean_dec(x_4);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_35);
lean_ctor_set(x_40, 1, x_36);
x_41 = lean_array_fset(x_23, x_19, x_40);
lean_ctor_set(x_9, 1, x_41);
lean_ctor_set(x_5, 1, x_14);
lean_ctor_set(x_11, 0, x_5);
return x_11;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_42 = lean_array_fget(x_36, x_38);
x_43 = lean_array_fset(x_36, x_38, x_22);
x_44 = l___private_Init_Lean_Elab_StructInst_15__mkProjStx(x_42, x_4);
x_45 = lean_array_fset(x_43, x_38, x_44);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_35);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_array_fset(x_23, x_19, x_46);
lean_ctor_set(x_9, 1, x_47);
lean_ctor_set(x_5, 1, x_14);
lean_ctor_set(x_11, 0, x_5);
return x_11;
}
}
}
case 2:
{
lean_object* x_48; uint8_t x_49; 
lean_free_object(x_9);
lean_dec(x_4);
lean_inc(x_21);
x_48 = lean_array_fset(x_23, x_19, x_21);
x_49 = !lean_is_exclusive(x_21);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_21, 1);
lean_dec(x_50);
x_51 = lean_ctor_get(x_21, 0);
lean_dec(x_51);
lean_ctor_set_tag(x_21, 1);
lean_ctor_set(x_21, 1, x_48);
lean_ctor_set(x_21, 0, x_16);
lean_ctor_set(x_5, 1, x_14);
lean_ctor_set(x_5, 0, x_21);
lean_ctor_set(x_11, 0, x_5);
return x_11;
}
else
{
lean_object* x_52; 
lean_dec(x_21);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_16);
lean_ctor_set(x_52, 1, x_48);
lean_ctor_set(x_5, 1, x_14);
lean_ctor_set(x_5, 0, x_52);
lean_ctor_set(x_11, 0, x_5);
return x_11;
}
}
default: 
{
lean_object* x_53; 
lean_dec(x_4);
x_53 = lean_array_fset(x_23, x_19, x_21);
lean_ctor_set(x_9, 1, x_53);
lean_ctor_set(x_5, 1, x_14);
lean_ctor_set(x_11, 0, x_5);
return x_11;
}
}
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_54 = lean_ctor_get(x_9, 0);
x_55 = lean_ctor_get(x_9, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_9);
x_56 = lean_array_get_size(x_55);
x_57 = lean_unsigned_to_nat(1u);
x_58 = lean_nat_dec_lt(x_57, x_56);
lean_dec(x_56);
if (x_58 == 0)
{
lean_object* x_59; 
lean_dec(x_4);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_54);
lean_ctor_set(x_59, 1, x_55);
lean_ctor_set(x_5, 1, x_14);
lean_ctor_set(x_5, 0, x_59);
lean_ctor_set(x_11, 0, x_5);
return x_11;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_array_fget(x_55, x_57);
x_61 = lean_box(0);
x_62 = lean_array_fset(x_55, x_57, x_61);
switch (lean_obj_tag(x_60)) {
case 1:
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_63 = lean_ctor_get(x_60, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_60, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_65 = x_60;
} else {
 lean_dec_ref(x_60);
 x_65 = lean_box(0);
}
x_66 = lean_array_get_size(x_64);
x_67 = lean_unsigned_to_nat(0u);
x_68 = lean_nat_dec_lt(x_67, x_66);
lean_dec(x_66);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_4);
if (lean_is_scalar(x_65)) {
 x_69 = lean_alloc_ctor(1, 2, 0);
} else {
 x_69 = x_65;
}
lean_ctor_set(x_69, 0, x_63);
lean_ctor_set(x_69, 1, x_64);
x_70 = lean_array_fset(x_62, x_57, x_69);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_54);
lean_ctor_set(x_71, 1, x_70);
lean_ctor_set(x_5, 1, x_14);
lean_ctor_set(x_5, 0, x_71);
lean_ctor_set(x_11, 0, x_5);
return x_11;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_72 = lean_array_fget(x_64, x_67);
x_73 = lean_array_fset(x_64, x_67, x_61);
x_74 = l___private_Init_Lean_Elab_StructInst_15__mkProjStx(x_72, x_4);
x_75 = lean_array_fset(x_73, x_67, x_74);
if (lean_is_scalar(x_65)) {
 x_76 = lean_alloc_ctor(1, 2, 0);
} else {
 x_76 = x_65;
}
lean_ctor_set(x_76, 0, x_63);
lean_ctor_set(x_76, 1, x_75);
x_77 = lean_array_fset(x_62, x_57, x_76);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_54);
lean_ctor_set(x_78, 1, x_77);
lean_ctor_set(x_5, 1, x_14);
lean_ctor_set(x_5, 0, x_78);
lean_ctor_set(x_11, 0, x_5);
return x_11;
}
}
case 2:
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_4);
lean_inc(x_60);
x_79 = lean_array_fset(x_62, x_57, x_60);
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
 lean_ctor_set_tag(x_81, 1);
}
lean_ctor_set(x_81, 0, x_54);
lean_ctor_set(x_81, 1, x_79);
lean_ctor_set(x_5, 1, x_14);
lean_ctor_set(x_5, 0, x_81);
lean_ctor_set(x_11, 0, x_5);
return x_11;
}
default: 
{
lean_object* x_82; lean_object* x_83; 
lean_dec(x_4);
x_82 = lean_array_fset(x_62, x_57, x_60);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_54);
lean_ctor_set(x_83, 1, x_82);
lean_ctor_set(x_5, 1, x_14);
lean_ctor_set(x_5, 0, x_83);
lean_ctor_set(x_11, 0, x_5);
return x_11;
}
}
}
}
}
else
{
lean_dec(x_4);
lean_ctor_set(x_5, 1, x_14);
lean_ctor_set(x_11, 0, x_5);
return x_11;
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_11, 0);
x_85 = lean_ctor_get(x_11, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_11);
x_86 = l_Lean_mkProj(x_2, x_84, x_10);
if (lean_obj_tag(x_9) == 1)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; 
x_87 = lean_ctor_get(x_9, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_9, 1);
lean_inc(x_88);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_89 = x_9;
} else {
 lean_dec_ref(x_9);
 x_89 = lean_box(0);
}
x_90 = lean_array_get_size(x_88);
x_91 = lean_unsigned_to_nat(1u);
x_92 = lean_nat_dec_lt(x_91, x_90);
lean_dec(x_90);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; 
lean_dec(x_4);
if (lean_is_scalar(x_89)) {
 x_93 = lean_alloc_ctor(1, 2, 0);
} else {
 x_93 = x_89;
}
lean_ctor_set(x_93, 0, x_87);
lean_ctor_set(x_93, 1, x_88);
lean_ctor_set(x_5, 1, x_86);
lean_ctor_set(x_5, 0, x_93);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_5);
lean_ctor_set(x_94, 1, x_85);
return x_94;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_array_fget(x_88, x_91);
x_96 = lean_box(0);
x_97 = lean_array_fset(x_88, x_91, x_96);
switch (lean_obj_tag(x_95)) {
case 1:
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_98 = lean_ctor_get(x_95, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_95, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 x_100 = x_95;
} else {
 lean_dec_ref(x_95);
 x_100 = lean_box(0);
}
x_101 = lean_array_get_size(x_99);
x_102 = lean_unsigned_to_nat(0u);
x_103 = lean_nat_dec_lt(x_102, x_101);
lean_dec(x_101);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
lean_dec(x_4);
if (lean_is_scalar(x_100)) {
 x_104 = lean_alloc_ctor(1, 2, 0);
} else {
 x_104 = x_100;
}
lean_ctor_set(x_104, 0, x_98);
lean_ctor_set(x_104, 1, x_99);
x_105 = lean_array_fset(x_97, x_91, x_104);
if (lean_is_scalar(x_89)) {
 x_106 = lean_alloc_ctor(1, 2, 0);
} else {
 x_106 = x_89;
}
lean_ctor_set(x_106, 0, x_87);
lean_ctor_set(x_106, 1, x_105);
lean_ctor_set(x_5, 1, x_86);
lean_ctor_set(x_5, 0, x_106);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_5);
lean_ctor_set(x_107, 1, x_85);
return x_107;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_108 = lean_array_fget(x_99, x_102);
x_109 = lean_array_fset(x_99, x_102, x_96);
x_110 = l___private_Init_Lean_Elab_StructInst_15__mkProjStx(x_108, x_4);
x_111 = lean_array_fset(x_109, x_102, x_110);
if (lean_is_scalar(x_100)) {
 x_112 = lean_alloc_ctor(1, 2, 0);
} else {
 x_112 = x_100;
}
lean_ctor_set(x_112, 0, x_98);
lean_ctor_set(x_112, 1, x_111);
x_113 = lean_array_fset(x_97, x_91, x_112);
if (lean_is_scalar(x_89)) {
 x_114 = lean_alloc_ctor(1, 2, 0);
} else {
 x_114 = x_89;
}
lean_ctor_set(x_114, 0, x_87);
lean_ctor_set(x_114, 1, x_113);
lean_ctor_set(x_5, 1, x_86);
lean_ctor_set(x_5, 0, x_114);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_5);
lean_ctor_set(x_115, 1, x_85);
return x_115;
}
}
case 2:
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
lean_dec(x_89);
lean_dec(x_4);
lean_inc(x_95);
x_116 = lean_array_fset(x_97, x_91, x_95);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 x_117 = x_95;
} else {
 lean_dec_ref(x_95);
 x_117 = lean_box(0);
}
if (lean_is_scalar(x_117)) {
 x_118 = lean_alloc_ctor(1, 2, 0);
} else {
 x_118 = x_117;
 lean_ctor_set_tag(x_118, 1);
}
lean_ctor_set(x_118, 0, x_87);
lean_ctor_set(x_118, 1, x_116);
lean_ctor_set(x_5, 1, x_86);
lean_ctor_set(x_5, 0, x_118);
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_5);
lean_ctor_set(x_119, 1, x_85);
return x_119;
}
default: 
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
lean_dec(x_4);
x_120 = lean_array_fset(x_97, x_91, x_95);
if (lean_is_scalar(x_89)) {
 x_121 = lean_alloc_ctor(1, 2, 0);
} else {
 x_121 = x_89;
}
lean_ctor_set(x_121, 0, x_87);
lean_ctor_set(x_121, 1, x_120);
lean_ctor_set(x_5, 1, x_86);
lean_ctor_set(x_5, 0, x_121);
x_122 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_122, 0, x_5);
lean_ctor_set(x_122, 1, x_85);
return x_122;
}
}
}
}
else
{
lean_object* x_123; 
lean_dec(x_4);
lean_ctor_set(x_5, 1, x_86);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_5);
lean_ctor_set(x_123, 1, x_85);
return x_123;
}
}
}
else
{
uint8_t x_124; 
lean_free_object(x_5);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_2);
x_124 = !lean_is_exclusive(x_11);
if (x_124 == 0)
{
return x_11;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_11, 0);
x_126 = lean_ctor_get(x_11, 1);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_11);
x_127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
return x_127;
}
}
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_128 = lean_ctor_get(x_5, 0);
x_129 = lean_ctor_get(x_5, 1);
lean_inc(x_129);
lean_inc(x_128);
lean_dec(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_130 = l___private_Init_Lean_Elab_StructInst_14__getFieldIdx(x_1, x_2, x_3, x_4, x_6, x_7);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_130, 1);
lean_inc(x_132);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 x_133 = x_130;
} else {
 lean_dec_ref(x_130);
 x_133 = lean_box(0);
}
x_134 = l_Lean_mkProj(x_2, x_131, x_129);
if (lean_obj_tag(x_128) == 1)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; uint8_t x_140; 
x_135 = lean_ctor_get(x_128, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_128, 1);
lean_inc(x_136);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 lean_ctor_release(x_128, 1);
 x_137 = x_128;
} else {
 lean_dec_ref(x_128);
 x_137 = lean_box(0);
}
x_138 = lean_array_get_size(x_136);
x_139 = lean_unsigned_to_nat(1u);
x_140 = lean_nat_dec_lt(x_139, x_138);
lean_dec(x_138);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; 
lean_dec(x_4);
if (lean_is_scalar(x_137)) {
 x_141 = lean_alloc_ctor(1, 2, 0);
} else {
 x_141 = x_137;
}
lean_ctor_set(x_141, 0, x_135);
lean_ctor_set(x_141, 1, x_136);
x_142 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_134);
if (lean_is_scalar(x_133)) {
 x_143 = lean_alloc_ctor(0, 2, 0);
} else {
 x_143 = x_133;
}
lean_ctor_set(x_143, 0, x_142);
lean_ctor_set(x_143, 1, x_132);
return x_143;
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_144 = lean_array_fget(x_136, x_139);
x_145 = lean_box(0);
x_146 = lean_array_fset(x_136, x_139, x_145);
switch (lean_obj_tag(x_144)) {
case 1:
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; uint8_t x_152; 
x_147 = lean_ctor_get(x_144, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_144, 1);
lean_inc(x_148);
if (lean_is_exclusive(x_144)) {
 lean_ctor_release(x_144, 0);
 lean_ctor_release(x_144, 1);
 x_149 = x_144;
} else {
 lean_dec_ref(x_144);
 x_149 = lean_box(0);
}
x_150 = lean_array_get_size(x_148);
x_151 = lean_unsigned_to_nat(0u);
x_152 = lean_nat_dec_lt(x_151, x_150);
lean_dec(x_150);
if (x_152 == 0)
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
lean_dec(x_4);
if (lean_is_scalar(x_149)) {
 x_153 = lean_alloc_ctor(1, 2, 0);
} else {
 x_153 = x_149;
}
lean_ctor_set(x_153, 0, x_147);
lean_ctor_set(x_153, 1, x_148);
x_154 = lean_array_fset(x_146, x_139, x_153);
if (lean_is_scalar(x_137)) {
 x_155 = lean_alloc_ctor(1, 2, 0);
} else {
 x_155 = x_137;
}
lean_ctor_set(x_155, 0, x_135);
lean_ctor_set(x_155, 1, x_154);
x_156 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_156, 0, x_155);
lean_ctor_set(x_156, 1, x_134);
if (lean_is_scalar(x_133)) {
 x_157 = lean_alloc_ctor(0, 2, 0);
} else {
 x_157 = x_133;
}
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_132);
return x_157;
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_158 = lean_array_fget(x_148, x_151);
x_159 = lean_array_fset(x_148, x_151, x_145);
x_160 = l___private_Init_Lean_Elab_StructInst_15__mkProjStx(x_158, x_4);
x_161 = lean_array_fset(x_159, x_151, x_160);
if (lean_is_scalar(x_149)) {
 x_162 = lean_alloc_ctor(1, 2, 0);
} else {
 x_162 = x_149;
}
lean_ctor_set(x_162, 0, x_147);
lean_ctor_set(x_162, 1, x_161);
x_163 = lean_array_fset(x_146, x_139, x_162);
if (lean_is_scalar(x_137)) {
 x_164 = lean_alloc_ctor(1, 2, 0);
} else {
 x_164 = x_137;
}
lean_ctor_set(x_164, 0, x_135);
lean_ctor_set(x_164, 1, x_163);
x_165 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_165, 0, x_164);
lean_ctor_set(x_165, 1, x_134);
if (lean_is_scalar(x_133)) {
 x_166 = lean_alloc_ctor(0, 2, 0);
} else {
 x_166 = x_133;
}
lean_ctor_set(x_166, 0, x_165);
lean_ctor_set(x_166, 1, x_132);
return x_166;
}
}
case 2:
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
lean_dec(x_137);
lean_dec(x_4);
lean_inc(x_144);
x_167 = lean_array_fset(x_146, x_139, x_144);
if (lean_is_exclusive(x_144)) {
 lean_ctor_release(x_144, 0);
 lean_ctor_release(x_144, 1);
 x_168 = x_144;
} else {
 lean_dec_ref(x_144);
 x_168 = lean_box(0);
}
if (lean_is_scalar(x_168)) {
 x_169 = lean_alloc_ctor(1, 2, 0);
} else {
 x_169 = x_168;
 lean_ctor_set_tag(x_169, 1);
}
lean_ctor_set(x_169, 0, x_135);
lean_ctor_set(x_169, 1, x_167);
x_170 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_170, 0, x_169);
lean_ctor_set(x_170, 1, x_134);
if (lean_is_scalar(x_133)) {
 x_171 = lean_alloc_ctor(0, 2, 0);
} else {
 x_171 = x_133;
}
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_171, 1, x_132);
return x_171;
}
default: 
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
lean_dec(x_4);
x_172 = lean_array_fset(x_146, x_139, x_144);
if (lean_is_scalar(x_137)) {
 x_173 = lean_alloc_ctor(1, 2, 0);
} else {
 x_173 = x_137;
}
lean_ctor_set(x_173, 0, x_135);
lean_ctor_set(x_173, 1, x_172);
x_174 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_174, 0, x_173);
lean_ctor_set(x_174, 1, x_134);
if (lean_is_scalar(x_133)) {
 x_175 = lean_alloc_ctor(0, 2, 0);
} else {
 x_175 = x_133;
}
lean_ctor_set(x_175, 0, x_174);
lean_ctor_set(x_175, 1, x_132);
return x_175;
}
}
}
}
else
{
lean_object* x_176; lean_object* x_177; 
lean_dec(x_4);
x_176 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_176, 0, x_128);
lean_ctor_set(x_176, 1, x_134);
if (lean_is_scalar(x_133)) {
 x_177 = lean_alloc_ctor(0, 2, 0);
} else {
 x_177 = x_133;
}
lean_ctor_set(x_177, 0, x_176);
lean_ctor_set(x_177, 1, x_132);
return x_177;
}
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
lean_dec(x_129);
lean_dec(x_128);
lean_dec(x_4);
lean_dec(x_2);
x_178 = lean_ctor_get(x_130, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_130, 1);
lean_inc(x_179);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 x_180 = x_130;
} else {
 lean_dec_ref(x_130);
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
lean_object* x_182; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_182 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_182, 0, x_5);
lean_ctor_set(x_182, 1, x_7);
return x_182;
}
}
}
lean_object* l___private_Init_Lean_Elab_StructInst_16__mkSubstructSource___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Lean_Elab_StructInst_16__mkSubstructSource(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
lean_dec(x_1);
return x_8;
}
}
lean_object* l___private_Init_Lean_Elab_StructInst_17__groupFields___lambda__1(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = l_List_tail_x21___rarg(x_3);
lean_dec(x_3);
lean_ctor_set(x_1, 1, x_4);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get(x_1, 2);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_1);
x_8 = l_List_tail_x21___rarg(x_6);
lean_dec(x_6);
x_9 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_8);
lean_ctor_set(x_9, 2, x_7);
return x_9;
}
}
}
lean_object* l___private_Init_Lean_Elab_StructInst_17__groupFields___lambda__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Term_StructInst_Field_toSyntax(x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Elab_StructInst_17__groupFields___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Init_Lean_Elab_StructInst_17__groupFields___lambda__1), 1, 0);
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Elab_StructInst_17__groupFields___lambda__3___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Term_StructInst_Field_inhabited(lean_box(0));
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Elab_StructInst_17__groupFields___lambda__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Init_Lean_Elab_StructInst_17__groupFields___lambda__2___boxed), 2, 0);
return x_1;
}
}
lean_object* l___private_Init_Lean_Elab_StructInst_17__groupFields___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_6, 1);
lean_inc(x_10);
lean_dec(x_6);
x_11 = l___private_Init_Lean_Elab_StructInst_13__isSimpleField_x3f(x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = l___private_Init_Lean_Elab_StructInst_17__groupFields___lambda__3___closed__1;
lean_inc(x_10);
x_13 = l_List_map___main___rarg(x_12, x_10);
x_14 = l_Lean_Elab_Term_StructInst_Struct_ref(x_1);
x_15 = l_Lean_Elab_Term_StructInst_Struct_source(x_1);
lean_inc(x_7);
lean_inc(x_9);
lean_inc(x_2);
x_16 = l___private_Init_Lean_Elab_StructInst_16__mkSubstructSource(x_14, x_2, x_3, x_9, x_15, x_7, x_8);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_16, 1);
x_20 = l___private_Init_Lean_Elab_StructInst_17__groupFields___lambda__3___closed__2;
x_21 = l_List_head_x21___rarg(x_20, x_10);
lean_dec(x_10);
x_22 = l_Lean_isSubobjectField_x3f(x_4, x_2, x_9);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
lean_dec(x_7);
lean_dec(x_5);
x_23 = lean_unsigned_to_nat(1u);
x_24 = l_Lean_mkOptionalNode___closed__1;
lean_inc(x_14);
x_25 = l_Lean_Syntax_setArg(x_14, x_23, x_24);
x_26 = l_List_redLength___main___rarg(x_13);
x_27 = lean_mk_empty_array_with_capacity(x_26);
lean_dec(x_26);
x_28 = l_List_toArrayAux___main___rarg(x_13, x_27);
x_29 = l_Id_monad;
x_30 = l___private_Init_Lean_Elab_StructInst_17__groupFields___lambda__3___closed__3;
x_31 = lean_unsigned_to_nat(0u);
x_32 = l_Array_umapMAux___main___rarg(x_29, lean_box(0), x_30, x_31, x_28);
x_33 = l_Lean_Elab_Term_StructInst_Source_addSyntax(x_18, x_32);
x_34 = l_Lean_List_format___rarg___closed__2;
x_35 = l_Lean_mkAtomFrom(x_14, x_34);
lean_dec(x_14);
x_36 = l_Lean_mkSepStx(x_33, x_35);
lean_dec(x_33);
x_37 = lean_unsigned_to_nat(2u);
x_38 = l_Lean_Syntax_setArg(x_25, x_37, x_36);
x_39 = !lean_is_exclusive(x_21);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_40 = lean_ctor_get(x_21, 1);
x_41 = lean_ctor_get(x_21, 2);
lean_dec(x_41);
x_42 = l_Lean_Elab_Term_StructInst_FieldLHS_inhabited;
x_43 = l_List_head_x21___rarg(x_42, x_40);
lean_dec(x_40);
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_46, 0, x_38);
lean_ctor_set(x_21, 2, x_46);
lean_ctor_set(x_21, 1, x_45);
lean_ctor_set(x_16, 0, x_21);
return x_16;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_47 = lean_ctor_get(x_21, 0);
x_48 = lean_ctor_get(x_21, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_21);
x_49 = l_Lean_Elab_Term_StructInst_FieldLHS_inhabited;
x_50 = l_List_head_x21___rarg(x_49, x_48);
lean_dec(x_48);
x_51 = lean_box(0);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_53, 0, x_38);
x_54 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_54, 0, x_47);
lean_ctor_set(x_54, 1, x_52);
lean_ctor_set(x_54, 2, x_53);
lean_ctor_set(x_16, 0, x_54);
return x_16;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_free_object(x_16);
x_55 = lean_ctor_get(x_22, 0);
lean_inc(x_55);
lean_dec(x_22);
x_56 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_56, 0, x_14);
lean_ctor_set(x_56, 1, x_55);
lean_ctor_set(x_56, 2, x_13);
lean_ctor_set(x_56, 3, x_18);
x_57 = lean_apply_3(x_5, x_56, x_7, x_19);
if (lean_obj_tag(x_57) == 0)
{
uint8_t x_58; 
x_58 = !lean_is_exclusive(x_57);
if (x_58 == 0)
{
uint8_t x_59; 
x_59 = !lean_is_exclusive(x_21);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_60 = lean_ctor_get(x_57, 0);
x_61 = lean_ctor_get(x_21, 1);
x_62 = lean_ctor_get(x_21, 2);
lean_dec(x_62);
x_63 = l_Lean_Elab_Term_StructInst_FieldLHS_inhabited;
x_64 = l_List_head_x21___rarg(x_63, x_61);
lean_dec(x_61);
x_65 = lean_box(0);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_60);
lean_ctor_set(x_21, 2, x_67);
lean_ctor_set(x_21, 1, x_66);
lean_ctor_set(x_57, 0, x_21);
return x_57;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_68 = lean_ctor_get(x_57, 0);
x_69 = lean_ctor_get(x_21, 0);
x_70 = lean_ctor_get(x_21, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_21);
x_71 = l_Lean_Elab_Term_StructInst_FieldLHS_inhabited;
x_72 = l_List_head_x21___rarg(x_71, x_70);
lean_dec(x_70);
x_73 = lean_box(0);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
x_75 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_75, 0, x_68);
x_76 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_76, 0, x_69);
lean_ctor_set(x_76, 1, x_74);
lean_ctor_set(x_76, 2, x_75);
lean_ctor_set(x_57, 0, x_76);
return x_57;
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_77 = lean_ctor_get(x_57, 0);
x_78 = lean_ctor_get(x_57, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_57);
x_79 = lean_ctor_get(x_21, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_21, 1);
lean_inc(x_80);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 lean_ctor_release(x_21, 2);
 x_81 = x_21;
} else {
 lean_dec_ref(x_21);
 x_81 = lean_box(0);
}
x_82 = l_Lean_Elab_Term_StructInst_FieldLHS_inhabited;
x_83 = l_List_head_x21___rarg(x_82, x_80);
lean_dec(x_80);
x_84 = lean_box(0);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
x_86 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_86, 0, x_77);
if (lean_is_scalar(x_81)) {
 x_87 = lean_alloc_ctor(0, 3, 0);
} else {
 x_87 = x_81;
}
lean_ctor_set(x_87, 0, x_79);
lean_ctor_set(x_87, 1, x_85);
lean_ctor_set(x_87, 2, x_86);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_78);
return x_88;
}
}
else
{
uint8_t x_89; 
lean_dec(x_21);
x_89 = !lean_is_exclusive(x_57);
if (x_89 == 0)
{
return x_57;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_57, 0);
x_91 = lean_ctor_get(x_57, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_57);
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
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_93 = lean_ctor_get(x_16, 0);
x_94 = lean_ctor_get(x_16, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_16);
x_95 = l___private_Init_Lean_Elab_StructInst_17__groupFields___lambda__3___closed__2;
x_96 = l_List_head_x21___rarg(x_95, x_10);
lean_dec(x_10);
x_97 = l_Lean_isSubobjectField_x3f(x_4, x_2, x_9);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
lean_dec(x_7);
lean_dec(x_5);
x_98 = lean_unsigned_to_nat(1u);
x_99 = l_Lean_mkOptionalNode___closed__1;
lean_inc(x_14);
x_100 = l_Lean_Syntax_setArg(x_14, x_98, x_99);
x_101 = l_List_redLength___main___rarg(x_13);
x_102 = lean_mk_empty_array_with_capacity(x_101);
lean_dec(x_101);
x_103 = l_List_toArrayAux___main___rarg(x_13, x_102);
x_104 = l_Id_monad;
x_105 = l___private_Init_Lean_Elab_StructInst_17__groupFields___lambda__3___closed__3;
x_106 = lean_unsigned_to_nat(0u);
x_107 = l_Array_umapMAux___main___rarg(x_104, lean_box(0), x_105, x_106, x_103);
x_108 = l_Lean_Elab_Term_StructInst_Source_addSyntax(x_93, x_107);
x_109 = l_Lean_List_format___rarg___closed__2;
x_110 = l_Lean_mkAtomFrom(x_14, x_109);
lean_dec(x_14);
x_111 = l_Lean_mkSepStx(x_108, x_110);
lean_dec(x_108);
x_112 = lean_unsigned_to_nat(2u);
x_113 = l_Lean_Syntax_setArg(x_100, x_112, x_111);
x_114 = lean_ctor_get(x_96, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_96, 1);
lean_inc(x_115);
if (lean_is_exclusive(x_96)) {
 lean_ctor_release(x_96, 0);
 lean_ctor_release(x_96, 1);
 lean_ctor_release(x_96, 2);
 x_116 = x_96;
} else {
 lean_dec_ref(x_96);
 x_116 = lean_box(0);
}
x_117 = l_Lean_Elab_Term_StructInst_FieldLHS_inhabited;
x_118 = l_List_head_x21___rarg(x_117, x_115);
lean_dec(x_115);
x_119 = lean_box(0);
x_120 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_119);
x_121 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_121, 0, x_113);
if (lean_is_scalar(x_116)) {
 x_122 = lean_alloc_ctor(0, 3, 0);
} else {
 x_122 = x_116;
}
lean_ctor_set(x_122, 0, x_114);
lean_ctor_set(x_122, 1, x_120);
lean_ctor_set(x_122, 2, x_121);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_94);
return x_123;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_97, 0);
lean_inc(x_124);
lean_dec(x_97);
x_125 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_125, 0, x_14);
lean_ctor_set(x_125, 1, x_124);
lean_ctor_set(x_125, 2, x_13);
lean_ctor_set(x_125, 3, x_93);
x_126 = lean_apply_3(x_5, x_125, x_7, x_94);
if (lean_obj_tag(x_126) == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_126, 1);
lean_inc(x_128);
if (lean_is_exclusive(x_126)) {
 lean_ctor_release(x_126, 0);
 lean_ctor_release(x_126, 1);
 x_129 = x_126;
} else {
 lean_dec_ref(x_126);
 x_129 = lean_box(0);
}
x_130 = lean_ctor_get(x_96, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_96, 1);
lean_inc(x_131);
if (lean_is_exclusive(x_96)) {
 lean_ctor_release(x_96, 0);
 lean_ctor_release(x_96, 1);
 lean_ctor_release(x_96, 2);
 x_132 = x_96;
} else {
 lean_dec_ref(x_96);
 x_132 = lean_box(0);
}
x_133 = l_Lean_Elab_Term_StructInst_FieldLHS_inhabited;
x_134 = l_List_head_x21___rarg(x_133, x_131);
lean_dec(x_131);
x_135 = lean_box(0);
x_136 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_136, 0, x_134);
lean_ctor_set(x_136, 1, x_135);
x_137 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_137, 0, x_127);
if (lean_is_scalar(x_132)) {
 x_138 = lean_alloc_ctor(0, 3, 0);
} else {
 x_138 = x_132;
}
lean_ctor_set(x_138, 0, x_130);
lean_ctor_set(x_138, 1, x_136);
lean_ctor_set(x_138, 2, x_137);
if (lean_is_scalar(x_129)) {
 x_139 = lean_alloc_ctor(0, 2, 0);
} else {
 x_139 = x_129;
}
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set(x_139, 1, x_128);
return x_139;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
lean_dec(x_96);
x_140 = lean_ctor_get(x_126, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_126, 1);
lean_inc(x_141);
if (lean_is_exclusive(x_126)) {
 lean_ctor_release(x_126, 0);
 lean_ctor_release(x_126, 1);
 x_142 = x_126;
} else {
 lean_dec_ref(x_126);
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
}
}
else
{
uint8_t x_144; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_144 = !lean_is_exclusive(x_16);
if (x_144 == 0)
{
return x_16;
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_145 = lean_ctor_get(x_16, 0);
x_146 = lean_ctor_get(x_16, 1);
lean_inc(x_146);
lean_inc(x_145);
lean_dec(x_16);
x_147 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_147, 0, x_145);
lean_ctor_set(x_147, 1, x_146);
return x_147;
}
}
}
else
{
lean_object* x_148; lean_object* x_149; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_148 = lean_ctor_get(x_11, 0);
lean_inc(x_148);
lean_dec(x_11);
x_149 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set(x_149, 1, x_8);
return x_149;
}
}
}
lean_object* l___private_Init_Lean_Elab_StructInst_17__groupFields___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
x_10 = l___private_Init_Lean_Elab_StructInst_12__mkFieldMap(x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_alloc_closure((void*)(l___private_Init_Lean_Elab_StructInst_17__groupFields___lambda__3___boxed), 8, 5);
lean_closure_set(x_13, 0, x_1);
lean_closure_set(x_13, 1, x_2);
lean_closure_set(x_13, 2, x_3);
lean_closure_set(x_13, 3, x_4);
lean_closure_set(x_13, 4, x_5);
x_14 = l_HashMap_toList___rarg(x_11);
lean_dec(x_11);
x_15 = l_List_mapM___main___rarg(x_6, lean_box(0), lean_box(0), x_13, x_14);
x_16 = lean_apply_2(x_15, x_8, x_12);
return x_16;
}
else
{
uint8_t x_17; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_17 = !lean_is_exclusive(x_10);
if (x_17 == 0)
{
return x_10;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_10, 0);
x_19 = lean_ctor_get(x_10, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_10);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
lean_object* l___private_Init_Lean_Elab_StructInst_17__groupFields(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_5 = l_Lean_Elab_Term_getEnv___rarg(x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l_Lean_Elab_Term_StructInst_Struct_structName(x_2);
lean_inc(x_8);
lean_inc(x_6);
x_9 = l_Lean_getStructureFields(x_6, x_8);
x_10 = l_Lean_MetavarContext_MkBinding_mkBinding___closed__1;
lean_inc(x_2);
x_11 = lean_alloc_closure((void*)(l___private_Init_Lean_Elab_StructInst_17__groupFields___lambda__4), 9, 6);
lean_closure_set(x_11, 0, x_2);
lean_closure_set(x_11, 1, x_8);
lean_closure_set(x_11, 2, x_9);
lean_closure_set(x_11, 3, x_6);
lean_closure_set(x_11, 4, x_1);
lean_closure_set(x_11, 5, x_10);
x_12 = l_Lean_Elab_Term_StructInst_Struct_modifyFieldsM___rarg(x_10, x_2, x_11);
x_13 = lean_apply_2(x_12, x_3, x_7);
return x_13;
}
}
lean_object* l___private_Init_Lean_Elab_StructInst_17__groupFields___lambda__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Init_Lean_Elab_StructInst_17__groupFields___lambda__2(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l___private_Init_Lean_Elab_StructInst_17__groupFields___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Init_Lean_Elab_StructInst_17__groupFields___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
lean_object* l_List_map___main___at___private_Init_Lean_Elab_StructInst_18__expandStruct___main___spec__2(lean_object* x_1) {
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
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get(x_4, 1);
x_8 = l_List_tail_x21___rarg(x_7);
lean_dec(x_7);
lean_ctor_set(x_4, 1, x_8);
x_9 = l_List_map___main___at___private_Init_Lean_Elab_StructInst_18__expandStruct___main___spec__2(x_6);
lean_ctor_set(x_1, 1, x_9);
return x_1;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_1, 1);
x_11 = lean_ctor_get(x_4, 0);
x_12 = lean_ctor_get(x_4, 1);
x_13 = lean_ctor_get(x_4, 2);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_4);
x_14 = l_List_tail_x21___rarg(x_12);
lean_dec(x_12);
x_15 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_15, 0, x_11);
lean_ctor_set(x_15, 1, x_14);
lean_ctor_set(x_15, 2, x_13);
x_16 = l_List_map___main___at___private_Init_Lean_Elab_StructInst_18__expandStruct___main___spec__2(x_10);
lean_ctor_set(x_1, 1, x_16);
lean_ctor_set(x_1, 0, x_15);
return x_1;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_17 = lean_ctor_get(x_1, 0);
x_18 = lean_ctor_get(x_1, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_1);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_17, 2);
lean_inc(x_21);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 lean_ctor_release(x_17, 2);
 x_22 = x_17;
} else {
 lean_dec_ref(x_17);
 x_22 = lean_box(0);
}
x_23 = l_List_tail_x21___rarg(x_20);
lean_dec(x_20);
if (lean_is_scalar(x_22)) {
 x_24 = lean_alloc_ctor(0, 3, 0);
} else {
 x_24 = x_22;
}
lean_ctor_set(x_24, 0, x_19);
lean_ctor_set(x_24, 1, x_23);
lean_ctor_set(x_24, 2, x_21);
x_25 = l_List_map___main___at___private_Init_Lean_Elab_StructInst_18__expandStruct___main___spec__2(x_18);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
lean_object* l_List_head_x21___at___private_Init_Lean_Elab_StructInst_18__expandStruct___main___spec__3(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___private_Init_Lean_Elab_StructInst_17__groupFields___lambda__3___closed__2;
x_3 = l_List_head_x21___rarg___closed__2;
x_4 = lean_panic_fn(x_2, x_3);
return x_4;
}
else
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
return x_5;
}
}
}
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Elab_StructInst_18__expandStruct___main___spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_nat_dec_lt(x_1, x_3);
lean_dec(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_1);
x_5 = l_Array_empty___closed__1;
x_6 = x_2;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_array_fget(x_2, x_1);
x_8 = lean_box(0);
x_9 = x_8;
x_10 = lean_array_fset(x_2, x_1, x_9);
lean_inc(x_7);
x_11 = l_Lean_Elab_Term_StructInst_Field_toSyntax(x_7);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_1, x_12);
x_14 = x_11;
lean_dec(x_7);
x_15 = lean_array_fset(x_10, x_1, x_14);
lean_dec(x_1);
x_1 = x_13;
x_2 = x_15;
goto _start;
}
}
}
lean_object* l_List_head_x21___at___private_Init_Lean_Elab_StructInst_18__expandStruct___main___spec__5(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Elab_Term_StructInst_FieldLHS_inhabited;
x_3 = l_List_head_x21___rarg___closed__2;
x_4 = lean_panic_fn(x_2, x_3);
return x_4;
}
else
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
return x_5;
}
}
}
lean_object* l_AssocList_foldlM___main___at___private_Init_Lean_Elab_StructInst_18__expandStruct___main___spec__7(lean_object* x_1, lean_object* x_2) {
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
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_4);
lean_inc(x_3);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_4);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_1);
x_1 = x_7;
x_2 = x_5;
goto _start;
}
}
}
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_Elab_StructInst_18__expandStruct___main___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_2);
x_6 = lean_nat_dec_lt(x_3, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_dec(x_3);
return x_4;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_array_fget(x_2, x_3);
x_8 = l_AssocList_foldlM___main___at___private_Init_Lean_Elab_StructInst_18__expandStruct___main___spec__7(x_4, x_7);
lean_dec(x_7);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_3, x_9);
lean_dec(x_3);
x_3 = x_10;
x_4 = x_8;
goto _start;
}
}
}
lean_object* l_HashMap_toList___at___private_Init_Lean_Elab_StructInst_18__expandStruct___main___spec__6(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_box(0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Array_iterateMAux___main___at___private_Init_Lean_Elab_StructInst_18__expandStruct___main___spec__8(x_1, x_3, x_4, x_2);
return x_5;
}
}
lean_object* l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_18__expandStruct___main___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_5);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_5, 0);
x_12 = lean_ctor_get(x_5, 1);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = l___private_Init_Lean_Elab_StructInst_13__isSimpleField_x3f(x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_inc(x_14);
x_16 = l_List_map___main___at___private_Init_Lean_Elab_StructInst_18__expandStruct___main___spec__2(x_14);
x_17 = l_Lean_Elab_Term_StructInst_Struct_ref(x_1);
x_18 = l_Lean_Elab_Term_StructInst_Struct_source(x_1);
lean_inc(x_6);
lean_inc(x_13);
lean_inc(x_3);
x_19 = l___private_Init_Lean_Elab_StructInst_16__mkSubstructSource(x_17, x_3, x_4, x_13, x_18, x_6, x_7);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_List_head_x21___at___private_Init_Lean_Elab_StructInst_18__expandStruct___main___spec__3(x_14);
lean_dec(x_14);
lean_inc(x_3);
lean_inc(x_2);
x_23 = l_Lean_isSubobjectField_x3f(x_2, x_3, x_13);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_24 = lean_unsigned_to_nat(1u);
x_25 = l_Lean_mkOptionalNode___closed__1;
lean_inc(x_17);
x_26 = l_Lean_Syntax_setArg(x_17, x_24, x_25);
x_27 = l_List_redLength___main___rarg(x_16);
x_28 = lean_mk_empty_array_with_capacity(x_27);
lean_dec(x_27);
x_29 = l_List_toArrayAux___main___rarg(x_16, x_28);
x_30 = lean_unsigned_to_nat(0u);
x_31 = l_Array_umapMAux___main___at___private_Init_Lean_Elab_StructInst_18__expandStruct___main___spec__4(x_30, x_29);
x_32 = l_Lean_Elab_Term_StructInst_Source_addSyntax(x_20, x_31);
x_33 = l_Lean_List_format___rarg___closed__2;
x_34 = l_Lean_mkAtomFrom(x_17, x_33);
lean_dec(x_17);
x_35 = l_Lean_mkSepStx(x_32, x_34);
lean_dec(x_32);
x_36 = lean_unsigned_to_nat(2u);
x_37 = l_Lean_Syntax_setArg(x_26, x_36, x_35);
x_38 = !lean_is_exclusive(x_22);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_39 = lean_ctor_get(x_22, 1);
x_40 = lean_ctor_get(x_22, 2);
lean_dec(x_40);
x_41 = l_List_head_x21___at___private_Init_Lean_Elab_StructInst_18__expandStruct___main___spec__5(x_39);
lean_dec(x_39);
x_42 = lean_box(0);
lean_ctor_set(x_5, 1, x_42);
lean_ctor_set(x_5, 0, x_41);
x_43 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_43, 0, x_37);
lean_ctor_set(x_22, 2, x_43);
lean_ctor_set(x_22, 1, x_5);
x_44 = l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_18__expandStruct___main___spec__9(x_1, x_2, x_3, x_4, x_12, x_6, x_21);
if (lean_obj_tag(x_44) == 0)
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_44, 0);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_22);
lean_ctor_set(x_47, 1, x_46);
lean_ctor_set(x_44, 0, x_47);
return x_44;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_48 = lean_ctor_get(x_44, 0);
x_49 = lean_ctor_get(x_44, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_44);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_22);
lean_ctor_set(x_50, 1, x_48);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_49);
return x_51;
}
}
else
{
uint8_t x_52; 
lean_dec(x_22);
x_52 = !lean_is_exclusive(x_44);
if (x_52 == 0)
{
return x_44;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_44, 0);
x_54 = lean_ctor_get(x_44, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_44);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_56 = lean_ctor_get(x_22, 0);
x_57 = lean_ctor_get(x_22, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_22);
x_58 = l_List_head_x21___at___private_Init_Lean_Elab_StructInst_18__expandStruct___main___spec__5(x_57);
lean_dec(x_57);
x_59 = lean_box(0);
lean_ctor_set(x_5, 1, x_59);
lean_ctor_set(x_5, 0, x_58);
x_60 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_60, 0, x_37);
x_61 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_61, 0, x_56);
lean_ctor_set(x_61, 1, x_5);
lean_ctor_set(x_61, 2, x_60);
x_62 = l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_18__expandStruct___main___spec__9(x_1, x_2, x_3, x_4, x_12, x_6, x_21);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_65 = x_62;
} else {
 lean_dec_ref(x_62);
 x_65 = lean_box(0);
}
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_61);
lean_ctor_set(x_66, 1, x_63);
if (lean_is_scalar(x_65)) {
 x_67 = lean_alloc_ctor(0, 2, 0);
} else {
 x_67 = x_65;
}
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_64);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_61);
x_68 = lean_ctor_get(x_62, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_62, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_70 = x_62;
} else {
 lean_dec_ref(x_62);
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
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_23, 0);
lean_inc(x_72);
lean_dec(x_23);
x_73 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_73, 0, x_17);
lean_ctor_set(x_73, 1, x_72);
lean_ctor_set(x_73, 2, x_16);
lean_ctor_set(x_73, 3, x_20);
lean_inc(x_6);
x_74 = l___private_Init_Lean_Elab_StructInst_18__expandStruct___main(x_73, x_6, x_21);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
x_77 = !lean_is_exclusive(x_22);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_78 = lean_ctor_get(x_22, 1);
x_79 = lean_ctor_get(x_22, 2);
lean_dec(x_79);
x_80 = l_List_head_x21___at___private_Init_Lean_Elab_StructInst_18__expandStruct___main___spec__5(x_78);
lean_dec(x_78);
x_81 = lean_box(0);
lean_ctor_set(x_5, 1, x_81);
lean_ctor_set(x_5, 0, x_80);
x_82 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_82, 0, x_75);
lean_ctor_set(x_22, 2, x_82);
lean_ctor_set(x_22, 1, x_5);
x_83 = l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_18__expandStruct___main___spec__9(x_1, x_2, x_3, x_4, x_12, x_6, x_76);
if (lean_obj_tag(x_83) == 0)
{
uint8_t x_84; 
x_84 = !lean_is_exclusive(x_83);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; 
x_85 = lean_ctor_get(x_83, 0);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_22);
lean_ctor_set(x_86, 1, x_85);
lean_ctor_set(x_83, 0, x_86);
return x_83;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_87 = lean_ctor_get(x_83, 0);
x_88 = lean_ctor_get(x_83, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_83);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_22);
lean_ctor_set(x_89, 1, x_87);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_88);
return x_90;
}
}
else
{
uint8_t x_91; 
lean_dec(x_22);
x_91 = !lean_is_exclusive(x_83);
if (x_91 == 0)
{
return x_83;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_83, 0);
x_93 = lean_ctor_get(x_83, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_83);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_95 = lean_ctor_get(x_22, 0);
x_96 = lean_ctor_get(x_22, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_22);
x_97 = l_List_head_x21___at___private_Init_Lean_Elab_StructInst_18__expandStruct___main___spec__5(x_96);
lean_dec(x_96);
x_98 = lean_box(0);
lean_ctor_set(x_5, 1, x_98);
lean_ctor_set(x_5, 0, x_97);
x_99 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_99, 0, x_75);
x_100 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_100, 0, x_95);
lean_ctor_set(x_100, 1, x_5);
lean_ctor_set(x_100, 2, x_99);
x_101 = l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_18__expandStruct___main___spec__9(x_1, x_2, x_3, x_4, x_12, x_6, x_76);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 x_104 = x_101;
} else {
 lean_dec_ref(x_101);
 x_104 = lean_box(0);
}
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_100);
lean_ctor_set(x_105, 1, x_102);
if (lean_is_scalar(x_104)) {
 x_106 = lean_alloc_ctor(0, 2, 0);
} else {
 x_106 = x_104;
}
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_103);
return x_106;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
lean_dec(x_100);
x_107 = lean_ctor_get(x_101, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_101, 1);
lean_inc(x_108);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 x_109 = x_101;
} else {
 lean_dec_ref(x_101);
 x_109 = lean_box(0);
}
if (lean_is_scalar(x_109)) {
 x_110 = lean_alloc_ctor(1, 2, 0);
} else {
 x_110 = x_109;
}
lean_ctor_set(x_110, 0, x_107);
lean_ctor_set(x_110, 1, x_108);
return x_110;
}
}
}
else
{
uint8_t x_111; 
lean_dec(x_22);
lean_free_object(x_5);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_111 = !lean_is_exclusive(x_74);
if (x_111 == 0)
{
return x_74;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_74, 0);
x_113 = lean_ctor_get(x_74, 1);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_74);
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
uint8_t x_115; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_free_object(x_5);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_115 = !lean_is_exclusive(x_19);
if (x_115 == 0)
{
return x_19;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_116 = lean_ctor_get(x_19, 0);
x_117 = lean_ctor_get(x_19, 1);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_19);
x_118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
return x_118;
}
}
}
else
{
lean_object* x_119; lean_object* x_120; 
lean_dec(x_14);
lean_dec(x_13);
x_119 = lean_ctor_get(x_15, 0);
lean_inc(x_119);
lean_dec(x_15);
x_120 = l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_18__expandStruct___main___spec__9(x_1, x_2, x_3, x_4, x_12, x_6, x_7);
if (lean_obj_tag(x_120) == 0)
{
uint8_t x_121; 
x_121 = !lean_is_exclusive(x_120);
if (x_121 == 0)
{
lean_object* x_122; 
x_122 = lean_ctor_get(x_120, 0);
lean_ctor_set(x_5, 1, x_122);
lean_ctor_set(x_5, 0, x_119);
lean_ctor_set(x_120, 0, x_5);
return x_120;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_123 = lean_ctor_get(x_120, 0);
x_124 = lean_ctor_get(x_120, 1);
lean_inc(x_124);
lean_inc(x_123);
lean_dec(x_120);
lean_ctor_set(x_5, 1, x_123);
lean_ctor_set(x_5, 0, x_119);
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_5);
lean_ctor_set(x_125, 1, x_124);
return x_125;
}
}
else
{
uint8_t x_126; 
lean_dec(x_119);
lean_free_object(x_5);
x_126 = !lean_is_exclusive(x_120);
if (x_126 == 0)
{
return x_120;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_127 = lean_ctor_get(x_120, 0);
x_128 = lean_ctor_get(x_120, 1);
lean_inc(x_128);
lean_inc(x_127);
lean_dec(x_120);
x_129 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_129, 0, x_127);
lean_ctor_set(x_129, 1, x_128);
return x_129;
}
}
}
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_130 = lean_ctor_get(x_5, 0);
x_131 = lean_ctor_get(x_5, 1);
lean_inc(x_131);
lean_inc(x_130);
lean_dec(x_5);
x_132 = lean_ctor_get(x_130, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_130, 1);
lean_inc(x_133);
lean_dec(x_130);
x_134 = l___private_Init_Lean_Elab_StructInst_13__isSimpleField_x3f(x_133);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
lean_inc(x_133);
x_135 = l_List_map___main___at___private_Init_Lean_Elab_StructInst_18__expandStruct___main___spec__2(x_133);
x_136 = l_Lean_Elab_Term_StructInst_Struct_ref(x_1);
x_137 = l_Lean_Elab_Term_StructInst_Struct_source(x_1);
lean_inc(x_6);
lean_inc(x_132);
lean_inc(x_3);
x_138 = l___private_Init_Lean_Elab_StructInst_16__mkSubstructSource(x_136, x_3, x_4, x_132, x_137, x_6, x_7);
if (lean_obj_tag(x_138) == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_138, 1);
lean_inc(x_140);
lean_dec(x_138);
x_141 = l_List_head_x21___at___private_Init_Lean_Elab_StructInst_18__expandStruct___main___spec__3(x_133);
lean_dec(x_133);
lean_inc(x_3);
lean_inc(x_2);
x_142 = l_Lean_isSubobjectField_x3f(x_2, x_3, x_132);
if (lean_obj_tag(x_142) == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_143 = lean_unsigned_to_nat(1u);
x_144 = l_Lean_mkOptionalNode___closed__1;
lean_inc(x_136);
x_145 = l_Lean_Syntax_setArg(x_136, x_143, x_144);
x_146 = l_List_redLength___main___rarg(x_135);
x_147 = lean_mk_empty_array_with_capacity(x_146);
lean_dec(x_146);
x_148 = l_List_toArrayAux___main___rarg(x_135, x_147);
x_149 = lean_unsigned_to_nat(0u);
x_150 = l_Array_umapMAux___main___at___private_Init_Lean_Elab_StructInst_18__expandStruct___main___spec__4(x_149, x_148);
x_151 = l_Lean_Elab_Term_StructInst_Source_addSyntax(x_139, x_150);
x_152 = l_Lean_List_format___rarg___closed__2;
x_153 = l_Lean_mkAtomFrom(x_136, x_152);
lean_dec(x_136);
x_154 = l_Lean_mkSepStx(x_151, x_153);
lean_dec(x_151);
x_155 = lean_unsigned_to_nat(2u);
x_156 = l_Lean_Syntax_setArg(x_145, x_155, x_154);
x_157 = lean_ctor_get(x_141, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_141, 1);
lean_inc(x_158);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 lean_ctor_release(x_141, 1);
 lean_ctor_release(x_141, 2);
 x_159 = x_141;
} else {
 lean_dec_ref(x_141);
 x_159 = lean_box(0);
}
x_160 = l_List_head_x21___at___private_Init_Lean_Elab_StructInst_18__expandStruct___main___spec__5(x_158);
lean_dec(x_158);
x_161 = lean_box(0);
x_162 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_162, 0, x_160);
lean_ctor_set(x_162, 1, x_161);
x_163 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_163, 0, x_156);
if (lean_is_scalar(x_159)) {
 x_164 = lean_alloc_ctor(0, 3, 0);
} else {
 x_164 = x_159;
}
lean_ctor_set(x_164, 0, x_157);
lean_ctor_set(x_164, 1, x_162);
lean_ctor_set(x_164, 2, x_163);
x_165 = l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_18__expandStruct___main___spec__9(x_1, x_2, x_3, x_4, x_131, x_6, x_140);
if (lean_obj_tag(x_165) == 0)
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_166 = lean_ctor_get(x_165, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_165, 1);
lean_inc(x_167);
if (lean_is_exclusive(x_165)) {
 lean_ctor_release(x_165, 0);
 lean_ctor_release(x_165, 1);
 x_168 = x_165;
} else {
 lean_dec_ref(x_165);
 x_168 = lean_box(0);
}
x_169 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_169, 0, x_164);
lean_ctor_set(x_169, 1, x_166);
if (lean_is_scalar(x_168)) {
 x_170 = lean_alloc_ctor(0, 2, 0);
} else {
 x_170 = x_168;
}
lean_ctor_set(x_170, 0, x_169);
lean_ctor_set(x_170, 1, x_167);
return x_170;
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
lean_dec(x_164);
x_171 = lean_ctor_get(x_165, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_165, 1);
lean_inc(x_172);
if (lean_is_exclusive(x_165)) {
 lean_ctor_release(x_165, 0);
 lean_ctor_release(x_165, 1);
 x_173 = x_165;
} else {
 lean_dec_ref(x_165);
 x_173 = lean_box(0);
}
if (lean_is_scalar(x_173)) {
 x_174 = lean_alloc_ctor(1, 2, 0);
} else {
 x_174 = x_173;
}
lean_ctor_set(x_174, 0, x_171);
lean_ctor_set(x_174, 1, x_172);
return x_174;
}
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_175 = lean_ctor_get(x_142, 0);
lean_inc(x_175);
lean_dec(x_142);
x_176 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_176, 0, x_136);
lean_ctor_set(x_176, 1, x_175);
lean_ctor_set(x_176, 2, x_135);
lean_ctor_set(x_176, 3, x_139);
lean_inc(x_6);
x_177 = l___private_Init_Lean_Elab_StructInst_18__expandStruct___main(x_176, x_6, x_140);
if (lean_obj_tag(x_177) == 0)
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_178 = lean_ctor_get(x_177, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_177, 1);
lean_inc(x_179);
lean_dec(x_177);
x_180 = lean_ctor_get(x_141, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_141, 1);
lean_inc(x_181);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 lean_ctor_release(x_141, 1);
 lean_ctor_release(x_141, 2);
 x_182 = x_141;
} else {
 lean_dec_ref(x_141);
 x_182 = lean_box(0);
}
x_183 = l_List_head_x21___at___private_Init_Lean_Elab_StructInst_18__expandStruct___main___spec__5(x_181);
lean_dec(x_181);
x_184 = lean_box(0);
x_185 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_185, 0, x_183);
lean_ctor_set(x_185, 1, x_184);
x_186 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_186, 0, x_178);
if (lean_is_scalar(x_182)) {
 x_187 = lean_alloc_ctor(0, 3, 0);
} else {
 x_187 = x_182;
}
lean_ctor_set(x_187, 0, x_180);
lean_ctor_set(x_187, 1, x_185);
lean_ctor_set(x_187, 2, x_186);
x_188 = l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_18__expandStruct___main___spec__9(x_1, x_2, x_3, x_4, x_131, x_6, x_179);
if (lean_obj_tag(x_188) == 0)
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_189 = lean_ctor_get(x_188, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_188, 1);
lean_inc(x_190);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 lean_ctor_release(x_188, 1);
 x_191 = x_188;
} else {
 lean_dec_ref(x_188);
 x_191 = lean_box(0);
}
x_192 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_192, 0, x_187);
lean_ctor_set(x_192, 1, x_189);
if (lean_is_scalar(x_191)) {
 x_193 = lean_alloc_ctor(0, 2, 0);
} else {
 x_193 = x_191;
}
lean_ctor_set(x_193, 0, x_192);
lean_ctor_set(x_193, 1, x_190);
return x_193;
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; 
lean_dec(x_187);
x_194 = lean_ctor_get(x_188, 0);
lean_inc(x_194);
x_195 = lean_ctor_get(x_188, 1);
lean_inc(x_195);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 lean_ctor_release(x_188, 1);
 x_196 = x_188;
} else {
 lean_dec_ref(x_188);
 x_196 = lean_box(0);
}
if (lean_is_scalar(x_196)) {
 x_197 = lean_alloc_ctor(1, 2, 0);
} else {
 x_197 = x_196;
}
lean_ctor_set(x_197, 0, x_194);
lean_ctor_set(x_197, 1, x_195);
return x_197;
}
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
lean_dec(x_141);
lean_dec(x_131);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_198 = lean_ctor_get(x_177, 0);
lean_inc(x_198);
x_199 = lean_ctor_get(x_177, 1);
lean_inc(x_199);
if (lean_is_exclusive(x_177)) {
 lean_ctor_release(x_177, 0);
 lean_ctor_release(x_177, 1);
 x_200 = x_177;
} else {
 lean_dec_ref(x_177);
 x_200 = lean_box(0);
}
if (lean_is_scalar(x_200)) {
 x_201 = lean_alloc_ctor(1, 2, 0);
} else {
 x_201 = x_200;
}
lean_ctor_set(x_201, 0, x_198);
lean_ctor_set(x_201, 1, x_199);
return x_201;
}
}
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; 
lean_dec(x_136);
lean_dec(x_135);
lean_dec(x_133);
lean_dec(x_132);
lean_dec(x_131);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_202 = lean_ctor_get(x_138, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_138, 1);
lean_inc(x_203);
if (lean_is_exclusive(x_138)) {
 lean_ctor_release(x_138, 0);
 lean_ctor_release(x_138, 1);
 x_204 = x_138;
} else {
 lean_dec_ref(x_138);
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
else
{
lean_object* x_206; lean_object* x_207; 
lean_dec(x_133);
lean_dec(x_132);
x_206 = lean_ctor_get(x_134, 0);
lean_inc(x_206);
lean_dec(x_134);
x_207 = l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_18__expandStruct___main___spec__9(x_1, x_2, x_3, x_4, x_131, x_6, x_7);
if (lean_obj_tag(x_207) == 0)
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_208 = lean_ctor_get(x_207, 0);
lean_inc(x_208);
x_209 = lean_ctor_get(x_207, 1);
lean_inc(x_209);
if (lean_is_exclusive(x_207)) {
 lean_ctor_release(x_207, 0);
 lean_ctor_release(x_207, 1);
 x_210 = x_207;
} else {
 lean_dec_ref(x_207);
 x_210 = lean_box(0);
}
x_211 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_211, 0, x_206);
lean_ctor_set(x_211, 1, x_208);
if (lean_is_scalar(x_210)) {
 x_212 = lean_alloc_ctor(0, 2, 0);
} else {
 x_212 = x_210;
}
lean_ctor_set(x_212, 0, x_211);
lean_ctor_set(x_212, 1, x_209);
return x_212;
}
else
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
lean_dec(x_206);
x_213 = lean_ctor_get(x_207, 0);
lean_inc(x_213);
x_214 = lean_ctor_get(x_207, 1);
lean_inc(x_214);
if (lean_is_exclusive(x_207)) {
 lean_ctor_release(x_207, 0);
 lean_ctor_release(x_207, 1);
 x_215 = x_207;
} else {
 lean_dec_ref(x_207);
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
}
}
}
}
lean_object* l___private_Init_Lean_Elab_StructInst_17__groupFields___at___private_Init_Lean_Elab_StructInst_18__expandStruct___main___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
x_8 = l___private_Init_Lean_Elab_StructInst_12__mkFieldMap(x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_HashMap_toList___at___private_Init_Lean_Elab_StructInst_18__expandStruct___main___spec__6(x_9);
lean_dec(x_9);
x_12 = l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_18__expandStruct___main___spec__9(x_1, x_2, x_3, x_4, x_11, x_6, x_10);
return x_12;
}
else
{
uint8_t x_13; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_13 = !lean_is_exclusive(x_8);
if (x_13 == 0)
{
return x_8;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_8, 0);
x_15 = lean_ctor_get(x_8, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_8);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
lean_object* l___private_Init_Lean_Elab_StructInst_17__groupFields___at___private_Init_Lean_Elab_StructInst_18__expandStruct___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = l_Lean_Elab_Term_getEnv___rarg(x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = l_Lean_Elab_Term_StructInst_Struct_structName(x_1);
lean_inc(x_7);
lean_inc(x_5);
x_8 = l_Lean_getStructureFields(x_5, x_7);
lean_inc(x_1);
x_9 = lean_alloc_closure((void*)(l___private_Init_Lean_Elab_StructInst_17__groupFields___at___private_Init_Lean_Elab_StructInst_18__expandStruct___main___spec__1___lambda__1___boxed), 7, 4);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_5);
lean_closure_set(x_9, 2, x_7);
lean_closure_set(x_9, 3, x_8);
x_10 = l_Lean_Elab_Term_StructInst_Struct_modifyFieldsM___at___private_Init_Lean_Elab_StructInst_9__expandNumLitFields___spec__2(x_1, x_9, x_2, x_6);
return x_10;
}
}
lean_object* l___private_Init_Lean_Elab_StructInst_18__expandStruct___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = l___private_Init_Lean_Elab_StructInst_8__expandCompositeFields___closed__1;
x_5 = l_Lean_Elab_Term_StructInst_Struct_modifyFieldsM___at_Lean_Elab_Term_StructInst_Struct_modifyFields___spec__1(x_1, x_4);
lean_inc(x_2);
x_6 = l___private_Init_Lean_Elab_StructInst_9__expandNumLitFields(x_5, x_2, x_3);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
lean_inc(x_2);
x_9 = l___private_Init_Lean_Elab_StructInst_10__expandParentFields(x_7, x_2, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l___private_Init_Lean_Elab_StructInst_17__groupFields___at___private_Init_Lean_Elab_StructInst_18__expandStruct___main___spec__1(x_10, x_2, x_11);
return x_12;
}
else
{
uint8_t x_13; 
lean_dec(x_2);
x_13 = !lean_is_exclusive(x_9);
if (x_13 == 0)
{
return x_9;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_9, 0);
x_15 = lean_ctor_get(x_9, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_9);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
else
{
uint8_t x_17; 
lean_dec(x_2);
x_17 = !lean_is_exclusive(x_6);
if (x_17 == 0)
{
return x_6;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_6, 0);
x_19 = lean_ctor_get(x_6, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_6);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
lean_object* l_List_head_x21___at___private_Init_Lean_Elab_StructInst_18__expandStruct___main___spec__3___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_List_head_x21___at___private_Init_Lean_Elab_StructInst_18__expandStruct___main___spec__3(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_List_head_x21___at___private_Init_Lean_Elab_StructInst_18__expandStruct___main___spec__5___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_List_head_x21___at___private_Init_Lean_Elab_StructInst_18__expandStruct___main___spec__5(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_AssocList_foldlM___main___at___private_Init_Lean_Elab_StructInst_18__expandStruct___main___spec__7___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_AssocList_foldlM___main___at___private_Init_Lean_Elab_StructInst_18__expandStruct___main___spec__7(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_Elab_StructInst_18__expandStruct___main___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_iterateMAux___main___at___private_Init_Lean_Elab_StructInst_18__expandStruct___main___spec__8(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_HashMap_toList___at___private_Init_Lean_Elab_StructInst_18__expandStruct___main___spec__6___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_HashMap_toList___at___private_Init_Lean_Elab_StructInst_18__expandStruct___main___spec__6(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_18__expandStruct___main___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_18__expandStruct___main___spec__9(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_1);
return x_8;
}
}
lean_object* l___private_Init_Lean_Elab_StructInst_17__groupFields___at___private_Init_Lean_Elab_StructInst_18__expandStruct___main___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Lean_Elab_StructInst_17__groupFields___at___private_Init_Lean_Elab_StructInst_18__expandStruct___main___spec__1___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_1);
return x_8;
}
}
lean_object* l___private_Init_Lean_Elab_StructInst_18__expandStruct(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Elab_StructInst_18__expandStruct___main(x_1, x_2, x_3);
return x_4;
}
}
lean_object* _init_l___private_Init_Lean_Elab_StructInst_19__elabStructInstAux___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid {...} notation, '");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Elab_StructInst_19__elabStructInstAux___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_StructInst_19__elabStructInstAux___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_StructInst_19__elabStructInstAux___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_StructInst_19__elabStructInstAux___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_StructInst_19__elabStructInstAux___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' is not a structure");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Elab_StructInst_19__elabStructInstAux___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_StructInst_19__elabStructInstAux___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_StructInst_19__elabStructInstAux___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_StructInst_19__elabStructInstAux___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_StructInst_19__elabStructInstAux___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("WIP");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Elab_StructInst_19__elabStructInstAux___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_StructInst_19__elabStructInstAux___closed__7;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_StructInst_19__elabStructInstAux___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_StructInst_19__elabStructInstAux___closed__8;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_StructInst_19__elabStructInstAux___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_Lean_Elab_StructInst_19__elabStructInstAux___closed__9;
x_2 = l_Lean_MessageData_ofList___closed__3;
x_3 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l___private_Init_Lean_Elab_StructInst_19__elabStructInstAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
lean_inc(x_4);
lean_inc(x_3);
x_6 = l___private_Init_Lean_Elab_StructInst_5__getStructName(x_1, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_Elab_Term_getEnv___rarg(x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_7);
x_12 = l_Lean_isStructureLike(x_10, x_7);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
lean_dec(x_3);
x_13 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_13, 0, x_7);
x_14 = l___private_Init_Lean_Elab_StructInst_19__elabStructInstAux___closed__3;
x_15 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
x_16 = l___private_Init_Lean_Elab_StructInst_19__elabStructInstAux___closed__6;
x_17 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lean_Elab_Term_throwError___rarg(x_1, x_17, x_4, x_11);
lean_dec(x_1);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
return x_18;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_18);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_inc(x_1);
x_23 = l___private_Init_Lean_Elab_StructInst_7__mkStructView(x_1, x_7, x_3);
lean_inc(x_4);
x_24 = l___private_Init_Lean_Elab_StructInst_18__expandStruct___main(x_23, x_4, x_11);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_Lean_Elab_Term_StructInst_formatStruct___main(x_25);
x_28 = l_Lean_Options_empty;
x_29 = l_Lean_Format_pretty(x_27, x_28);
x_30 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = l___private_Init_Lean_Elab_StructInst_19__elabStructInstAux___closed__10;
x_33 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
x_34 = l_Lean_Elab_Term_throwError___rarg(x_1, x_33, x_4, x_26);
lean_dec(x_1);
return x_34;
}
else
{
uint8_t x_35; 
lean_dec(x_4);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_24);
if (x_35 == 0)
{
return x_24;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_24, 0);
x_37 = lean_ctor_get(x_24, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_24);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
else
{
uint8_t x_39; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_6);
if (x_39 == 0)
{
return x_6;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_6, 0);
x_41 = lean_ctor_get(x_6, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_6);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
}
lean_object* _init_l_Lean_Elab_Term_StructInst_elabStructInst___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid {...} notation, explicit source is required when using '[<index>] := <value>'");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_StructInst_elabStructInst___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_StructInst_elabStructInst___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_StructInst_elabStructInst___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_StructInst_elabStructInst___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_StructInst_elabStructInst(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_3);
lean_inc(x_1);
x_5 = l___private_Init_Lean_Elab_StructInst_1__expandNonAtomicExplicitSource(x_1, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
lean_inc(x_3);
x_8 = l___private_Init_Lean_Elab_StructInst_2__getStructSource(x_1, x_3, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_3);
x_11 = l___private_Init_Lean_Elab_StructInst_3__isModifyOp_x3f(x_1, x_3, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l___private_Init_Lean_Elab_StructInst_19__elabStructInstAux(x_1, x_2, x_9, x_3, x_13);
return x_14;
}
else
{
if (lean_obj_tag(x_9) == 2)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
lean_dec(x_11);
x_16 = lean_ctor_get(x_12, 0);
lean_inc(x_16);
lean_dec(x_12);
x_17 = lean_ctor_get(x_9, 1);
lean_inc(x_17);
lean_dec(x_9);
x_18 = l___private_Init_Lean_Elab_StructInst_4__elabModifyOp(x_1, x_16, x_17, x_2, x_3, x_15);
lean_dec(x_2);
lean_dec(x_17);
lean_dec(x_16);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_2);
x_19 = lean_ctor_get(x_11, 1);
lean_inc(x_19);
lean_dec(x_11);
x_20 = l_Lean_Elab_Term_StructInst_elabStructInst___closed__3;
x_21 = l_Lean_Elab_Term_throwError___rarg(x_1, x_20, x_3, x_19);
lean_dec(x_1);
return x_21;
}
}
}
else
{
uint8_t x_22; 
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
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
uint8_t x_26; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_8);
if (x_26 == 0)
{
return x_8;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_8, 0);
x_28 = lean_ctor_get(x_8, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_8);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
else
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_30 = lean_ctor_get(x_5, 1);
lean_inc(x_30);
lean_dec(x_5);
x_31 = lean_ctor_get(x_6, 0);
lean_inc(x_31);
lean_dec(x_6);
x_32 = !lean_is_exclusive(x_3);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; 
x_33 = lean_ctor_get(x_3, 8);
lean_inc(x_31);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_1);
lean_ctor_set(x_34, 1, x_31);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
lean_ctor_set(x_3, 8, x_35);
x_36 = 1;
x_37 = l_Lean_Elab_Term_elabTerm(x_31, x_2, x_36, x_3, x_30);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; uint8_t x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; 
x_38 = lean_ctor_get(x_3, 0);
x_39 = lean_ctor_get(x_3, 1);
x_40 = lean_ctor_get(x_3, 2);
x_41 = lean_ctor_get(x_3, 3);
x_42 = lean_ctor_get(x_3, 4);
x_43 = lean_ctor_get(x_3, 5);
x_44 = lean_ctor_get(x_3, 6);
x_45 = lean_ctor_get(x_3, 7);
x_46 = lean_ctor_get(x_3, 8);
x_47 = lean_ctor_get(x_3, 9);
x_48 = lean_ctor_get_uint8(x_3, sizeof(void*)*10);
x_49 = lean_ctor_get_uint8(x_3, sizeof(void*)*10 + 1);
x_50 = lean_ctor_get_uint8(x_3, sizeof(void*)*10 + 2);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_3);
lean_inc(x_31);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_1);
lean_ctor_set(x_51, 1, x_31);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_46);
x_53 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_53, 0, x_38);
lean_ctor_set(x_53, 1, x_39);
lean_ctor_set(x_53, 2, x_40);
lean_ctor_set(x_53, 3, x_41);
lean_ctor_set(x_53, 4, x_42);
lean_ctor_set(x_53, 5, x_43);
lean_ctor_set(x_53, 6, x_44);
lean_ctor_set(x_53, 7, x_45);
lean_ctor_set(x_53, 8, x_52);
lean_ctor_set(x_53, 9, x_47);
lean_ctor_set_uint8(x_53, sizeof(void*)*10, x_48);
lean_ctor_set_uint8(x_53, sizeof(void*)*10 + 1, x_49);
lean_ctor_set_uint8(x_53, sizeof(void*)*10 + 2, x_50);
x_54 = 1;
x_55 = l_Lean_Elab_Term_elabTerm(x_31, x_2, x_54, x_53, x_30);
return x_55;
}
}
}
else
{
uint8_t x_56; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_56 = !lean_is_exclusive(x_5);
if (x_56 == 0)
{
return x_5;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_5, 0);
x_58 = lean_ctor_get(x_5, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_5);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_StructInst_elabStructInst___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("StructInst");
return x_1;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_StructInst_elabStructInst___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_declareBuiltinTermElab___closed__3;
x_2 = l___regBuiltinTermElab_Lean_Elab_Term_StructInst_elabStructInst___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_StructInst_elabStructInst___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("elabStructInst");
return x_1;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_StructInst_elabStructInst___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltinTermElab_Lean_Elab_Term_StructInst_elabStructInst___closed__2;
x_2 = l___regBuiltinTermElab_Lean_Elab_Term_StructInst_elabStructInst___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_StructInst_elabStructInst___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_StructInst_elabStructInst), 4, 0);
return x_1;
}
}
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_StructInst_elabStructInst(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Parser_Term_structInst___elambda__1___closed__2;
x_3 = l___regBuiltinTermElab_Lean_Elab_Term_StructInst_elabStructInst___closed__4;
x_4 = l___regBuiltinTermElab_Lean_Elab_Term_StructInst_elabStructInst___closed__5;
x_5 = l_Lean_Elab_Term_addBuiltinTermElab(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* initialize_Init_Lean_Elab_App(lean_object*);
lean_object* initialize_Init_Lean_Elab_Binders(lean_object*);
lean_object* initialize_Init_Lean_Elab_Quotation(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Elab_StructInst(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Lean_Elab_App(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Elab_Binders(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Elab_Quotation(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Array_umapMAux___main___at_Lean_Elab_Term_StructInst_ExpandNonAtomicExplicitSource_main___spec__1___closed__1 = _init_l_Array_umapMAux___main___at_Lean_Elab_Term_StructInst_ExpandNonAtomicExplicitSource_main___spec__1___closed__1();
lean_mark_persistent(l_Array_umapMAux___main___at_Lean_Elab_Term_StructInst_ExpandNonAtomicExplicitSource_main___spec__1___closed__1);
l_Array_umapMAux___main___at_Lean_Elab_Term_StructInst_ExpandNonAtomicExplicitSource_main___spec__1___closed__2 = _init_l_Array_umapMAux___main___at_Lean_Elab_Term_StructInst_ExpandNonAtomicExplicitSource_main___spec__1___closed__2();
lean_mark_persistent(l_Array_umapMAux___main___at_Lean_Elab_Term_StructInst_ExpandNonAtomicExplicitSource_main___spec__1___closed__2);
l_Array_umapMAux___main___at_Lean_Elab_Term_StructInst_ExpandNonAtomicExplicitSource_main___spec__1___closed__3 = _init_l_Array_umapMAux___main___at_Lean_Elab_Term_StructInst_ExpandNonAtomicExplicitSource_main___spec__1___closed__3();
lean_mark_persistent(l_Array_umapMAux___main___at_Lean_Elab_Term_StructInst_ExpandNonAtomicExplicitSource_main___spec__1___closed__3);
l_Array_umapMAux___main___at_Lean_Elab_Term_StructInst_ExpandNonAtomicExplicitSource_main___spec__1___closed__4 = _init_l_Array_umapMAux___main___at_Lean_Elab_Term_StructInst_ExpandNonAtomicExplicitSource_main___spec__1___closed__4();
lean_mark_persistent(l_Array_umapMAux___main___at_Lean_Elab_Term_StructInst_ExpandNonAtomicExplicitSource_main___spec__1___closed__4);
l_Array_umapMAux___main___at_Lean_Elab_Term_StructInst_ExpandNonAtomicExplicitSource_main___spec__1___closed__5 = _init_l_Array_umapMAux___main___at_Lean_Elab_Term_StructInst_ExpandNonAtomicExplicitSource_main___spec__1___closed__5();
lean_mark_persistent(l_Array_umapMAux___main___at_Lean_Elab_Term_StructInst_ExpandNonAtomicExplicitSource_main___spec__1___closed__5);
l_Array_umapMAux___main___at_Lean_Elab_Term_StructInst_ExpandNonAtomicExplicitSource_main___spec__1___closed__6 = _init_l_Array_umapMAux___main___at_Lean_Elab_Term_StructInst_ExpandNonAtomicExplicitSource_main___spec__1___closed__6();
lean_mark_persistent(l_Array_umapMAux___main___at_Lean_Elab_Term_StructInst_ExpandNonAtomicExplicitSource_main___spec__1___closed__6);
l___private_Init_Lean_Elab_StructInst_1__expandNonAtomicExplicitSource___closed__1 = _init_l___private_Init_Lean_Elab_StructInst_1__expandNonAtomicExplicitSource___closed__1();
lean_mark_persistent(l___private_Init_Lean_Elab_StructInst_1__expandNonAtomicExplicitSource___closed__1);
l_Lean_Elab_Term_StructInst_Source_hasFormat___closed__1 = _init_l_Lean_Elab_Term_StructInst_Source_hasFormat___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_Source_hasFormat___closed__1);
l_Lean_Elab_Term_StructInst_Source_hasFormat___closed__2 = _init_l_Lean_Elab_Term_StructInst_Source_hasFormat___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_Source_hasFormat___closed__2);
l_Lean_Elab_Term_StructInst_Source_hasFormat___closed__3 = _init_l_Lean_Elab_Term_StructInst_Source_hasFormat___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_Source_hasFormat___closed__3);
l_Lean_Elab_Term_StructInst_Source_hasFormat___closed__4 = _init_l_Lean_Elab_Term_StructInst_Source_hasFormat___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_Source_hasFormat___closed__4);
l_Array_foldlStepMAux___main___at___private_Init_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__1 = _init_l_Array_foldlStepMAux___main___at___private_Init_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__1();
lean_mark_persistent(l_Array_foldlStepMAux___main___at___private_Init_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__1);
l_Array_foldlStepMAux___main___at___private_Init_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__2 = _init_l_Array_foldlStepMAux___main___at___private_Init_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__2();
lean_mark_persistent(l_Array_foldlStepMAux___main___at___private_Init_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__2);
l_Array_foldlStepMAux___main___at___private_Init_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__3 = _init_l_Array_foldlStepMAux___main___at___private_Init_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__3();
lean_mark_persistent(l_Array_foldlStepMAux___main___at___private_Init_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__3);
l_Array_foldlStepMAux___main___at___private_Init_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__4 = _init_l_Array_foldlStepMAux___main___at___private_Init_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__4();
lean_mark_persistent(l_Array_foldlStepMAux___main___at___private_Init_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__4);
l_Array_foldlStepMAux___main___at___private_Init_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__5 = _init_l_Array_foldlStepMAux___main___at___private_Init_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__5();
lean_mark_persistent(l_Array_foldlStepMAux___main___at___private_Init_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__5);
l_Array_foldlStepMAux___main___at___private_Init_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__6 = _init_l_Array_foldlStepMAux___main___at___private_Init_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__6();
lean_mark_persistent(l_Array_foldlStepMAux___main___at___private_Init_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__6);
l___private_Init_Lean_Elab_StructInst_4__elabModifyOp___closed__1 = _init_l___private_Init_Lean_Elab_StructInst_4__elabModifyOp___closed__1();
lean_mark_persistent(l___private_Init_Lean_Elab_StructInst_4__elabModifyOp___closed__1);
l___private_Init_Lean_Elab_StructInst_4__elabModifyOp___closed__2 = _init_l___private_Init_Lean_Elab_StructInst_4__elabModifyOp___closed__2();
lean_mark_persistent(l___private_Init_Lean_Elab_StructInst_4__elabModifyOp___closed__2);
l___private_Init_Lean_Elab_StructInst_4__elabModifyOp___closed__3 = _init_l___private_Init_Lean_Elab_StructInst_4__elabModifyOp___closed__3();
lean_mark_persistent(l___private_Init_Lean_Elab_StructInst_4__elabModifyOp___closed__3);
l___private_Init_Lean_Elab_StructInst_5__getStructName___closed__1 = _init_l___private_Init_Lean_Elab_StructInst_5__getStructName___closed__1();
lean_mark_persistent(l___private_Init_Lean_Elab_StructInst_5__getStructName___closed__1);
l___private_Init_Lean_Elab_StructInst_5__getStructName___closed__2 = _init_l___private_Init_Lean_Elab_StructInst_5__getStructName___closed__2();
lean_mark_persistent(l___private_Init_Lean_Elab_StructInst_5__getStructName___closed__2);
l___private_Init_Lean_Elab_StructInst_5__getStructName___closed__3 = _init_l___private_Init_Lean_Elab_StructInst_5__getStructName___closed__3();
lean_mark_persistent(l___private_Init_Lean_Elab_StructInst_5__getStructName___closed__3);
l___private_Init_Lean_Elab_StructInst_5__getStructName___closed__4 = _init_l___private_Init_Lean_Elab_StructInst_5__getStructName___closed__4();
lean_mark_persistent(l___private_Init_Lean_Elab_StructInst_5__getStructName___closed__4);
l___private_Init_Lean_Elab_StructInst_5__getStructName___closed__5 = _init_l___private_Init_Lean_Elab_StructInst_5__getStructName___closed__5();
lean_mark_persistent(l___private_Init_Lean_Elab_StructInst_5__getStructName___closed__5);
l___private_Init_Lean_Elab_StructInst_5__getStructName___closed__6 = _init_l___private_Init_Lean_Elab_StructInst_5__getStructName___closed__6();
lean_mark_persistent(l___private_Init_Lean_Elab_StructInst_5__getStructName___closed__6);
l_Lean_Elab_Term_StructInst_FieldLHS_inhabited___closed__1 = _init_l_Lean_Elab_Term_StructInst_FieldLHS_inhabited___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_FieldLHS_inhabited___closed__1);
l_Lean_Elab_Term_StructInst_FieldLHS_inhabited = _init_l_Lean_Elab_Term_StructInst_FieldLHS_inhabited();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_FieldLHS_inhabited);
l_Lean_Elab_Term_StructInst_Field_inhabited___closed__1 = _init_l_Lean_Elab_Term_StructInst_Field_inhabited___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_Field_inhabited___closed__1);
l_Lean_Elab_Term_StructInst_Field_inhabited___closed__2 = _init_l_Lean_Elab_Term_StructInst_Field_inhabited___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_Field_inhabited___closed__2);
l_Lean_Elab_Term_StructInst_formatField___closed__1 = _init_l_Lean_Elab_Term_StructInst_formatField___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_formatField___closed__1);
l_List_map___main___at_Lean_Elab_Term_StructInst_formatStruct___main___spec__1___closed__1 = _init_l_List_map___main___at_Lean_Elab_Term_StructInst_formatStruct___main___spec__1___closed__1();
lean_mark_persistent(l_List_map___main___at_Lean_Elab_Term_StructInst_formatStruct___main___spec__1___closed__1);
l_Lean_Elab_Term_StructInst_formatStruct___main___closed__1 = _init_l_Lean_Elab_Term_StructInst_formatStruct___main___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_formatStruct___main___closed__1);
l_Lean_Elab_Term_StructInst_formatStruct___main___closed__2 = _init_l_Lean_Elab_Term_StructInst_formatStruct___main___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_formatStruct___main___closed__2);
l_Lean_Elab_Term_StructInst_Struct_hasFormat___closed__1 = _init_l_Lean_Elab_Term_StructInst_Struct_hasFormat___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_Struct_hasFormat___closed__1);
l_Lean_Elab_Term_StructInst_Struct_hasFormat = _init_l_Lean_Elab_Term_StructInst_Struct_hasFormat();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_Struct_hasFormat);
l_Lean_Elab_Term_StructInst_Struct_hasToString___closed__1 = _init_l_Lean_Elab_Term_StructInst_Struct_hasToString___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_Struct_hasToString___closed__1);
l_Lean_Elab_Term_StructInst_Struct_hasToString = _init_l_Lean_Elab_Term_StructInst_Struct_hasToString();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_Struct_hasToString);
l_Lean_Elab_Term_StructInst_Field_hasFormat___closed__1 = _init_l_Lean_Elab_Term_StructInst_Field_hasFormat___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_Field_hasFormat___closed__1);
l_Lean_Elab_Term_StructInst_Field_hasFormat = _init_l_Lean_Elab_Term_StructInst_Field_hasFormat();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_Field_hasFormat);
l_Lean_Elab_Term_StructInst_Field_hasToString___closed__1 = _init_l_Lean_Elab_Term_StructInst_Field_hasToString___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_Field_hasToString___closed__1);
l_Lean_Elab_Term_StructInst_Field_hasToString = _init_l_Lean_Elab_Term_StructInst_Field_hasToString();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_Field_hasToString);
l___private_Init_Lean_Elab_StructInst_8__expandCompositeFields___closed__1 = _init_l___private_Init_Lean_Elab_StructInst_8__expandCompositeFields___closed__1();
lean_mark_persistent(l___private_Init_Lean_Elab_StructInst_8__expandCompositeFields___closed__1);
l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__1 = _init_l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__1();
lean_mark_persistent(l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__1);
l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__2 = _init_l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__2();
lean_mark_persistent(l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__2);
l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__3 = _init_l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__3();
lean_mark_persistent(l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__3);
l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__4 = _init_l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__4();
lean_mark_persistent(l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__4);
l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__5 = _init_l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__5();
lean_mark_persistent(l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__5);
l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__6 = _init_l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__6();
lean_mark_persistent(l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__6);
l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__7 = _init_l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__7();
lean_mark_persistent(l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__7);
l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__8 = _init_l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__8();
lean_mark_persistent(l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__8);
l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__9 = _init_l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__9();
lean_mark_persistent(l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__9);
l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__1 = _init_l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__1();
lean_mark_persistent(l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__1);
l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__2 = _init_l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__2();
lean_mark_persistent(l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__2);
l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__3 = _init_l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__3();
lean_mark_persistent(l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__3);
l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__4 = _init_l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__4();
lean_mark_persistent(l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__4);
l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__5 = _init_l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__5();
lean_mark_persistent(l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__5);
l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__6 = _init_l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__6();
lean_mark_persistent(l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__6);
l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__7 = _init_l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__7();
lean_mark_persistent(l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__7);
l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__8 = _init_l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__8();
lean_mark_persistent(l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__8);
l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__9 = _init_l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__9();
lean_mark_persistent(l_List_mapM___main___at___private_Init_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__9);
l_List_foldlM___main___at___private_Init_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__1 = _init_l_List_foldlM___main___at___private_Init_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__1();
lean_mark_persistent(l_List_foldlM___main___at___private_Init_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__1);
l_List_foldlM___main___at___private_Init_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__2 = _init_l_List_foldlM___main___at___private_Init_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__2();
lean_mark_persistent(l_List_foldlM___main___at___private_Init_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__2);
l_List_foldlM___main___at___private_Init_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__3 = _init_l_List_foldlM___main___at___private_Init_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__3();
lean_mark_persistent(l_List_foldlM___main___at___private_Init_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__3);
l_List_foldlM___main___at___private_Init_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__4 = _init_l_List_foldlM___main___at___private_Init_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__4();
lean_mark_persistent(l_List_foldlM___main___at___private_Init_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__4);
l_List_foldlM___main___at___private_Init_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__5 = _init_l_List_foldlM___main___at___private_Init_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__5();
lean_mark_persistent(l_List_foldlM___main___at___private_Init_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__5);
l_List_foldlM___main___at___private_Init_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__6 = _init_l_List_foldlM___main___at___private_Init_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__6();
lean_mark_persistent(l_List_foldlM___main___at___private_Init_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__6);
l___private_Init_Lean_Elab_StructInst_12__mkFieldMap___closed__1 = _init_l___private_Init_Lean_Elab_StructInst_12__mkFieldMap___closed__1();
lean_mark_persistent(l___private_Init_Lean_Elab_StructInst_12__mkFieldMap___closed__1);
l___private_Init_Lean_Elab_StructInst_14__getFieldIdx___closed__1 = _init_l___private_Init_Lean_Elab_StructInst_14__getFieldIdx___closed__1();
lean_mark_persistent(l___private_Init_Lean_Elab_StructInst_14__getFieldIdx___closed__1);
l___private_Init_Lean_Elab_StructInst_14__getFieldIdx___closed__2 = _init_l___private_Init_Lean_Elab_StructInst_14__getFieldIdx___closed__2();
lean_mark_persistent(l___private_Init_Lean_Elab_StructInst_14__getFieldIdx___closed__2);
l___private_Init_Lean_Elab_StructInst_14__getFieldIdx___closed__3 = _init_l___private_Init_Lean_Elab_StructInst_14__getFieldIdx___closed__3();
lean_mark_persistent(l___private_Init_Lean_Elab_StructInst_14__getFieldIdx___closed__3);
l___private_Init_Lean_Elab_StructInst_17__groupFields___lambda__3___closed__1 = _init_l___private_Init_Lean_Elab_StructInst_17__groupFields___lambda__3___closed__1();
lean_mark_persistent(l___private_Init_Lean_Elab_StructInst_17__groupFields___lambda__3___closed__1);
l___private_Init_Lean_Elab_StructInst_17__groupFields___lambda__3___closed__2 = _init_l___private_Init_Lean_Elab_StructInst_17__groupFields___lambda__3___closed__2();
lean_mark_persistent(l___private_Init_Lean_Elab_StructInst_17__groupFields___lambda__3___closed__2);
l___private_Init_Lean_Elab_StructInst_17__groupFields___lambda__3___closed__3 = _init_l___private_Init_Lean_Elab_StructInst_17__groupFields___lambda__3___closed__3();
lean_mark_persistent(l___private_Init_Lean_Elab_StructInst_17__groupFields___lambda__3___closed__3);
l___private_Init_Lean_Elab_StructInst_19__elabStructInstAux___closed__1 = _init_l___private_Init_Lean_Elab_StructInst_19__elabStructInstAux___closed__1();
lean_mark_persistent(l___private_Init_Lean_Elab_StructInst_19__elabStructInstAux___closed__1);
l___private_Init_Lean_Elab_StructInst_19__elabStructInstAux___closed__2 = _init_l___private_Init_Lean_Elab_StructInst_19__elabStructInstAux___closed__2();
lean_mark_persistent(l___private_Init_Lean_Elab_StructInst_19__elabStructInstAux___closed__2);
l___private_Init_Lean_Elab_StructInst_19__elabStructInstAux___closed__3 = _init_l___private_Init_Lean_Elab_StructInst_19__elabStructInstAux___closed__3();
lean_mark_persistent(l___private_Init_Lean_Elab_StructInst_19__elabStructInstAux___closed__3);
l___private_Init_Lean_Elab_StructInst_19__elabStructInstAux___closed__4 = _init_l___private_Init_Lean_Elab_StructInst_19__elabStructInstAux___closed__4();
lean_mark_persistent(l___private_Init_Lean_Elab_StructInst_19__elabStructInstAux___closed__4);
l___private_Init_Lean_Elab_StructInst_19__elabStructInstAux___closed__5 = _init_l___private_Init_Lean_Elab_StructInst_19__elabStructInstAux___closed__5();
lean_mark_persistent(l___private_Init_Lean_Elab_StructInst_19__elabStructInstAux___closed__5);
l___private_Init_Lean_Elab_StructInst_19__elabStructInstAux___closed__6 = _init_l___private_Init_Lean_Elab_StructInst_19__elabStructInstAux___closed__6();
lean_mark_persistent(l___private_Init_Lean_Elab_StructInst_19__elabStructInstAux___closed__6);
l___private_Init_Lean_Elab_StructInst_19__elabStructInstAux___closed__7 = _init_l___private_Init_Lean_Elab_StructInst_19__elabStructInstAux___closed__7();
lean_mark_persistent(l___private_Init_Lean_Elab_StructInst_19__elabStructInstAux___closed__7);
l___private_Init_Lean_Elab_StructInst_19__elabStructInstAux___closed__8 = _init_l___private_Init_Lean_Elab_StructInst_19__elabStructInstAux___closed__8();
lean_mark_persistent(l___private_Init_Lean_Elab_StructInst_19__elabStructInstAux___closed__8);
l___private_Init_Lean_Elab_StructInst_19__elabStructInstAux___closed__9 = _init_l___private_Init_Lean_Elab_StructInst_19__elabStructInstAux___closed__9();
lean_mark_persistent(l___private_Init_Lean_Elab_StructInst_19__elabStructInstAux___closed__9);
l___private_Init_Lean_Elab_StructInst_19__elabStructInstAux___closed__10 = _init_l___private_Init_Lean_Elab_StructInst_19__elabStructInstAux___closed__10();
lean_mark_persistent(l___private_Init_Lean_Elab_StructInst_19__elabStructInstAux___closed__10);
l_Lean_Elab_Term_StructInst_elabStructInst___closed__1 = _init_l_Lean_Elab_Term_StructInst_elabStructInst___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_elabStructInst___closed__1);
l_Lean_Elab_Term_StructInst_elabStructInst___closed__2 = _init_l_Lean_Elab_Term_StructInst_elabStructInst___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_elabStructInst___closed__2);
l_Lean_Elab_Term_StructInst_elabStructInst___closed__3 = _init_l_Lean_Elab_Term_StructInst_elabStructInst___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_elabStructInst___closed__3);
l___regBuiltinTermElab_Lean_Elab_Term_StructInst_elabStructInst___closed__1 = _init_l___regBuiltinTermElab_Lean_Elab_Term_StructInst_elabStructInst___closed__1();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_StructInst_elabStructInst___closed__1);
l___regBuiltinTermElab_Lean_Elab_Term_StructInst_elabStructInst___closed__2 = _init_l___regBuiltinTermElab_Lean_Elab_Term_StructInst_elabStructInst___closed__2();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_StructInst_elabStructInst___closed__2);
l___regBuiltinTermElab_Lean_Elab_Term_StructInst_elabStructInst___closed__3 = _init_l___regBuiltinTermElab_Lean_Elab_Term_StructInst_elabStructInst___closed__3();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_StructInst_elabStructInst___closed__3);
l___regBuiltinTermElab_Lean_Elab_Term_StructInst_elabStructInst___closed__4 = _init_l___regBuiltinTermElab_Lean_Elab_Term_StructInst_elabStructInst___closed__4();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_StructInst_elabStructInst___closed__4);
l___regBuiltinTermElab_Lean_Elab_Term_StructInst_elabStructInst___closed__5 = _init_l___regBuiltinTermElab_Lean_Elab_Term_StructInst_elabStructInst___closed__5();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_StructInst_elabStructInst___closed__5);
res = l___regBuiltinTermElab_Lean_Elab_Term_StructInst_elabStructInst(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
