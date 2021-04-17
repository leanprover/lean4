// Lean compiler output
// Module: Lean.Meta.GeneralizeVars
// Imports: Init Lean.Meta.Basic Lean.Util.CollectFVars
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
lean_object* l_Lean_Meta_getFVarSetToGeneralize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at_Lean_Meta_getFVarSetToGeneralize___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_USize_add(size_t, size_t);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_getFVarSetToGeneralize___spec__53(lean_object*, size_t, size_t, lean_object*);
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__29___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_getFVarSetToGeneralize___spec__57___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_forInAux___at_Lean_Meta_getFVarSetToGeneralize___spec__55(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__35___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_isAuxDecl(lean_object*);
uint8_t l_USize_decEq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Meta_getFVarsToGeneralize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at_Lean_Meta_getFVarSetToGeneralize___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__6(lean_object*, lean_object*, size_t, size_t);
lean_object* l_Lean_Meta_getFVarSetToGeneralize___closed__1;
lean_object* l_Std_PersistentArray_forInAux___at_Lean_Meta_getFVarSetToGeneralize___spec__55___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkGeneralizationForbiddenSet_visit_match__1(lean_object*);
lean_object* l_Std_PersistentArray_forIn___at_Lean_Meta_getFVarSetToGeneralize___spec__48(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkGeneralizationForbiddenSet_visit_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_CollectFVars_main(lean_object*, lean_object*);
uint8_t l_Std_PersistentArray_anyMAux___at_Lean_Meta_getFVarSetToGeneralize___spec__11(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkGeneralizationForbiddenSet_loop_match__2(lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_getFVarSetToGeneralize___spec__47___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__22(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_getExprAssignment_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkGeneralizationForbiddenSet_loop_match__2___rarg(lean_object*, lean_object*, lean_object*);
uint8_t l_Std_PersistentArray_anyMAux___at_Lean_Meta_getFVarSetToGeneralize___spec__4(lean_object*, lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at_Lean_Meta_getFVarSetToGeneralize___spec__37___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFVarSetToGeneralize_match__1(lean_object*);
lean_object* l_Lean_LocalContext_get_x21(lean_object*, lean_object*);
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
uint8_t l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__12(lean_object*, lean_object*, size_t, size_t);
uint8_t l_Std_PersistentArray_anyMAux___at_Lean_Meta_getFVarSetToGeneralize___spec__39(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__34(lean_object*, lean_object*, size_t, size_t);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_getFVarSetToGeneralize___spec__50___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_sortFVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_MetavarContext_findLocalDeclDependsOn___closed__1;
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at_Lean_Meta_getFVarSetToGeneralize___spec__9(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at_Lean_Meta_getFVarSetToGeneralize___spec__30___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_RBNode_fold___at_Lean_Meta_sortFVars___spec__1(lean_object*, lean_object*);
uint8_t l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__19(lean_object*, lean_object*, size_t, size_t);
uint8_t l_USize_decLt(size_t, size_t);
uint8_t l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__7(lean_object*, lean_object*, size_t, size_t);
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__26___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_getFVarSetToGeneralize___spec__58___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at_Lean_Meta_getFVarSetToGeneralize___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkGeneralizationForbiddenSet_loop_match__1(lean_object*);
lean_object* l_Array_qpartition_loop___at_Lean_Meta_sortFVars___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__13(lean_object*, lean_object*, size_t, size_t);
uint8_t l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__14(lean_object*, lean_object*, size_t, size_t);
lean_object* l_Lean_Meta_mkGeneralizationForbiddenSet_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__41(lean_object*, lean_object*, size_t, size_t);
uint8_t l_Std_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__17(lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_getFVarSetToGeneralize___spec__53___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__15(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_swap(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_getFVarSetToGeneralize___spec__51___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_PersistentArray_anyMAux___at_Lean_Meta_getFVarSetToGeneralize___spec__25(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkGeneralizationForbiddenSet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__27___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Std_RBNode_forIn_visit___at_Lean_Meta_mkGeneralizationForbiddenSet_visit___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_PersistentArray_anyMAux___at_Lean_Meta_getFVarSetToGeneralize___spec__32(lean_object*, lean_object*);
lean_object* l_Std_RBNode_forIn_visit___at_Lean_Meta_mkGeneralizationForbiddenSet_visit___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_forInAux___at_Lean_Meta_getFVarSetToGeneralize___spec__44___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_getFVarSetToGeneralize___spec__57(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__10(lean_object*, lean_object*);
lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__33___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_getFVarSetToGeneralize___spec__51(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_forInAux___at_Lean_Meta_getFVarSetToGeneralize___spec__49___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__3___boxed(lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_forIn___at_Lean_Meta_getFVarSetToGeneralize___spec__48___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_binderInfo(lean_object*);
lean_object* l_Array_qpartition_loop___at_Lean_Meta_sortFVars___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_forIn___at_Lean_Meta_getFVarSetToGeneralize___spec__43(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_getFVarSetToGeneralize___spec__45(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFVarsToGeneralize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_forInAux___at_Lean_Meta_getFVarSetToGeneralize___spec__44___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__17___boxed(lean_object*, lean_object*);
lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkGeneralizationForbiddenSet_visit_match__2___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at_Lean_Meta_getFVarSetToGeneralize___spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkGeneralizationForbiddenSet_match__1___rarg(lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_anyMAux___at_Lean_Meta_getFVarSetToGeneralize___spec__11___boxed(lean_object*, lean_object*);
uint8_t l_Std_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__3(lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_anyMAux___at_Lean_Meta_getFVarSetToGeneralize___spec__39___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__36(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkGeneralizationForbiddenSet_match__1(lean_object*);
uint8_t l_Std_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__24(lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_forInAux___at_Lean_Meta_getFVarSetToGeneralize___spec__44___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__40___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_getFVarSetToGeneralize___spec__47(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_BinderInfo_isInstImplicit(uint8_t);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_getFVarSetToGeneralize___spec__46(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_getFVarSetToGeneralize___spec__46___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_getFVarSetToGeneralize___spec__52(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_NameSet_empty;
lean_object* l_Std_PersistentArray_anyMAux___at_Lean_Meta_getFVarSetToGeneralize___spec__25___boxed(lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_forIn___at_Lean_Meta_getFVarSetToGeneralize___spec__54(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
uint8_t l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__35(lean_object*, lean_object*, size_t, size_t);
uint8_t l_Std_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__31(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_LocalDecl_value_x3f(lean_object*);
uint8_t l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__20(lean_object*, lean_object*, size_t, size_t);
lean_object* l_Lean_Meta_mkGeneralizationForbiddenSet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_HashSet_instInhabitedHashSet___closed__1;
uint8_t l_Std_PersistentArray_anyMAux___at_Lean_Meta_getFVarSetToGeneralize___spec__18(lean_object*, lean_object*);
lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__28___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_index(lean_object*);
lean_object* l_Lean_Meta_getFVarSetToGeneralize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__42(lean_object*, lean_object*, size_t, size_t);
lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__42___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__41___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_anyMAux___at_Lean_Meta_getFVarSetToGeneralize___spec__4___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkGeneralizationForbiddenSet_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Std_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__31___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkGeneralizationForbiddenSet_visit___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__24___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_sortFVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_anyMAux___at_Lean_Meta_getFVarSetToGeneralize___spec__32___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at_Lean_Meta_getFVarSetToGeneralize___spec__16(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_qsort_sort___at_Lean_Meta_sortFVars___spec__2___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at_Lean_Meta_getFVarSetToGeneralize___spec__30(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__40(lean_object*, lean_object*, size_t, size_t);
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at_Lean_Meta_getFVarSetToGeneralize___spec__23(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__29(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
uint8_t l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__28(lean_object*, lean_object*, size_t, size_t);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_getFVarSetToGeneralize___spec__52___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkGeneralizationForbiddenSet_visit_match__2(lean_object*);
extern lean_object* l_Lean_instInhabitedName;
lean_object* l_Lean_Meta_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_forInAux___at_Lean_Meta_getFVarSetToGeneralize___spec__49(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_getFVarSetToGeneralize___spec__45___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_qsort_sort___at_Lean_Meta_sortFVars___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_getFVarSetToGeneralize___spec__50(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_anyMAux___at_Lean_Meta_getFVarSetToGeneralize___spec__18___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at_Lean_Meta_getFVarSetToGeneralize___spec__23___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__5(lean_object*, lean_object*, size_t, size_t);
lean_object* l_Lean_Meta_getFVarSetToGeneralize_match__1___rarg(lean_object*, lean_object*);
uint8_t l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__33(lean_object*, lean_object*, size_t, size_t);
uint8_t l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__26(lean_object*, lean_object*, size_t, size_t);
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__36___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_getFVarSetToGeneralize___spec__58(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_forIn___at_Lean_Meta_getFVarSetToGeneralize___spec__43___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_CollectFVars_instInhabitedState___closed__1;
lean_object* l_Std_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__38___boxed(lean_object*, lean_object*);
lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__38(lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_getDecl(lean_object*, lean_object*);
lean_object* l_Array_qsort_sort___at_Lean_Meta_sortFVars___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_mkGeneralizationForbiddenSet___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_getFVarSetToGeneralize___spec__56(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_forIn___at_Lean_Meta_getFVarSetToGeneralize___spec__43___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__10___boxed(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_forInAux___at_Lean_Meta_getFVarSetToGeneralize___spec__44(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__27(lean_object*, lean_object*, size_t, size_t);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_mkGeneralizationForbiddenSet___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_forIn___at_Lean_Meta_getFVarSetToGeneralize___spec__43___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at_Lean_Meta_getFVarSetToGeneralize___spec__37(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkGeneralizationForbiddenSet_visit___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkGeneralizationForbiddenSet_loop_match__1___rarg(lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_forIn___at_Lean_Meta_getFVarSetToGeneralize___spec__54___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_getFVarSetToGeneralize___spec__56___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__21(lean_object*, lean_object*, size_t, size_t);
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_shouldVisit(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t l_Array_qsort_sort___at_Lean_Meta_sortFVars___spec__2___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__34___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkGeneralizationForbiddenSet_visit_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
x_4 = lean_apply_1(x_3, x_1);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
}
}
lean_object* l_Lean_Meta_mkGeneralizationForbiddenSet_visit_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_mkGeneralizationForbiddenSet_visit_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_mkGeneralizationForbiddenSet_visit_match__2___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_Meta_mkGeneralizationForbiddenSet_visit_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_mkGeneralizationForbiddenSet_visit_match__2___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_mkGeneralizationForbiddenSet_loop_match__1___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_Meta_mkGeneralizationForbiddenSet_loop_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_mkGeneralizationForbiddenSet_loop_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_mkGeneralizationForbiddenSet_loop_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_apply_2(x_3, x_6, x_7);
return x_8;
}
}
}
lean_object* l_Lean_Meta_mkGeneralizationForbiddenSet_loop_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_mkGeneralizationForbiddenSet_loop_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_mkGeneralizationForbiddenSet_match__1___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_Meta_mkGeneralizationForbiddenSet_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_mkGeneralizationForbiddenSet_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Std_RBNode_forIn_visit___at_Lean_Meta_mkGeneralizationForbiddenSet_visit___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_2);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 3);
lean_inc(x_12);
lean_dec(x_1);
x_13 = l_Std_RBNode_forIn_visit___at_Lean_Meta_mkGeneralizationForbiddenSet_visit___spec__1(x_10, x_2, x_3, x_4, x_5, x_6, x_7);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = !lean_is_exclusive(x_15);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_ctor_get(x_15, 0);
x_19 = lean_ctor_get(x_15, 1);
x_20 = l_Lean_NameSet_contains(x_18, x_11);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_inc(x_11);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_11);
lean_ctor_set(x_21, 1, x_19);
x_22 = lean_box(0);
x_23 = l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_18, x_11, x_22);
lean_ctor_set(x_15, 1, x_21);
lean_ctor_set(x_15, 0, x_23);
x_1 = x_12;
x_2 = x_15;
x_7 = x_16;
goto _start;
}
else
{
lean_dec(x_11);
x_1 = x_12;
x_2 = x_15;
x_7 = x_16;
goto _start;
}
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_15, 0);
x_27 = lean_ctor_get(x_15, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_15);
x_28 = l_Lean_NameSet_contains(x_26, x_11);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_inc(x_11);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_11);
lean_ctor_set(x_29, 1, x_27);
x_30 = lean_box(0);
x_31 = l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_26, x_11, x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_29);
x_1 = x_12;
x_2 = x_32;
x_7 = x_16;
goto _start;
}
else
{
lean_object* x_34; 
lean_dec(x_11);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_26);
lean_ctor_set(x_34, 1, x_27);
x_1 = x_12;
x_2 = x_34;
x_7 = x_16;
goto _start;
}
}
}
}
}
lean_object* l_Lean_Meta_mkGeneralizationForbiddenSet_visit___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
lean_dec(x_3);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_2);
x_12 = l_Std_RBNode_forIn_visit___at_Lean_Meta_mkGeneralizationForbiddenSet_visit___spec__1(x_10, x_11, x_5, x_6, x_7, x_8, x_9);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
x_15 = !lean_is_exclusive(x_12);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_12, 0);
lean_dec(x_16);
x_17 = lean_ctor_get(x_14, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_14, 1);
lean_inc(x_18);
lean_dec(x_14);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
lean_ctor_set(x_12, 0, x_19);
return x_12;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_12, 1);
lean_inc(x_20);
lean_dec(x_12);
x_21 = lean_ctor_get(x_14, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_14, 1);
lean_inc(x_22);
lean_dec(x_14);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_20);
return x_24;
}
}
}
lean_object* l_Lean_Meta_mkGeneralizationForbiddenSet_visit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_4);
x_9 = l_Lean_Meta_getLocalDecl(x_1, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_LocalDecl_type(x_10);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_13 = l_Lean_Meta_instantiateMVars(x_12, x_4, x_5, x_6, x_7, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_CollectFVars_instInhabitedState___closed__1;
x_17 = l_Lean_CollectFVars_main(x_14, x_16);
x_18 = l_Lean_LocalDecl_value_x3f(x_10);
lean_dec(x_10);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_box(0);
x_20 = l_Lean_Meta_mkGeneralizationForbiddenSet_visit___lambda__1(x_3, x_2, x_17, x_19, x_4, x_5, x_6, x_7, x_15);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_18, 0);
lean_inc(x_21);
lean_dec(x_18);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_22 = l_Lean_Meta_instantiateMVars(x_21, x_4, x_5, x_6, x_7, x_15);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_CollectFVars_main(x_23, x_17);
x_26 = lean_box(0);
x_27 = l_Lean_Meta_mkGeneralizationForbiddenSet_visit___lambda__1(x_3, x_2, x_25, x_26, x_4, x_5, x_6, x_7, x_24);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_27;
}
else
{
uint8_t x_28; 
lean_dec(x_17);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_28 = !lean_is_exclusive(x_22);
if (x_28 == 0)
{
return x_22;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_22, 0);
x_30 = lean_ctor_get(x_22, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_22);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
else
{
uint8_t x_32; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_32 = !lean_is_exclusive(x_13);
if (x_32 == 0)
{
return x_13;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_13, 0);
x_34 = lean_ctor_get(x_13, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_13);
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
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_36 = !lean_is_exclusive(x_9);
if (x_36 == 0)
{
return x_9;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_9, 0);
x_38 = lean_ctor_get(x_9, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_9);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
lean_object* l_Std_RBNode_forIn_visit___at_Lean_Meta_mkGeneralizationForbiddenSet_visit___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_RBNode_forIn_visit___at_Lean_Meta_mkGeneralizationForbiddenSet_visit___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
lean_object* l_Lean_Meta_mkGeneralizationForbiddenSet_visit___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_mkGeneralizationForbiddenSet_visit___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_10;
}
}
lean_object* l_Lean_Meta_mkGeneralizationForbiddenSet_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_8; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_2);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
x_11 = l_Lean_NameSet_contains(x_2, x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_box(0);
lean_inc(x_9);
x_13 = l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_2, x_9, x_12);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_14 = l_Lean_Meta_mkGeneralizationForbiddenSet_visit(x_9, x_10, x_13, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_1 = x_17;
x_2 = x_18;
x_7 = x_16;
goto _start;
}
else
{
uint8_t x_20; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_20 = !lean_is_exclusive(x_14);
if (x_20 == 0)
{
return x_14;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_14, 0);
x_22 = lean_ctor_get(x_14, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_14);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
else
{
lean_dec(x_9);
x_1 = x_10;
goto _start;
}
}
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_mkGeneralizationForbiddenSet___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = x_3 < x_2;
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_4);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_uget(x_1, x_3);
x_13 = !lean_is_exclusive(x_4);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_4, 0);
x_15 = lean_ctor_get(x_4, 1);
x_16 = l_Lean_Expr_isFVar(x_12);
if (x_16 == 0)
{
lean_object* x_17; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_17 = l_Lean_Meta_inferType(x_12, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_20 = l_Lean_Meta_instantiateMVars(x_18, x_5, x_6, x_7, x_8, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; size_t x_24; size_t x_25; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_CollectFVars_main(x_21, x_14);
lean_ctor_set(x_4, 0, x_23);
x_24 = 1;
x_25 = x_3 + x_24;
x_3 = x_25;
x_9 = x_22;
goto _start;
}
else
{
uint8_t x_27; 
lean_free_object(x_4);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_27 = !lean_is_exclusive(x_20);
if (x_27 == 0)
{
return x_20;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_20, 0);
x_29 = lean_ctor_get(x_20, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_20);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
else
{
uint8_t x_31; 
lean_free_object(x_4);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_31 = !lean_is_exclusive(x_17);
if (x_31 == 0)
{
return x_17;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_17, 0);
x_33 = lean_ctor_get(x_17, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_17);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
lean_object* x_35; lean_object* x_36; size_t x_37; size_t x_38; 
x_35 = l_Lean_Expr_fvarId_x21(x_12);
lean_dec(x_12);
x_36 = lean_array_push(x_15, x_35);
lean_ctor_set(x_4, 1, x_36);
x_37 = 1;
x_38 = x_3 + x_37;
x_3 = x_38;
goto _start;
}
}
else
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_40 = lean_ctor_get(x_4, 0);
x_41 = lean_ctor_get(x_4, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_4);
x_42 = l_Lean_Expr_isFVar(x_12);
if (x_42 == 0)
{
lean_object* x_43; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_43 = l_Lean_Meta_inferType(x_12, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_46 = l_Lean_Meta_instantiateMVars(x_44, x_5, x_6, x_7, x_8, x_45);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; size_t x_51; size_t x_52; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = l_Lean_CollectFVars_main(x_47, x_40);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_41);
x_51 = 1;
x_52 = x_3 + x_51;
x_3 = x_52;
x_4 = x_50;
x_9 = x_48;
goto _start;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_54 = lean_ctor_get(x_46, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_46, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_56 = x_46;
} else {
 lean_dec_ref(x_46);
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
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_58 = lean_ctor_get(x_43, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_43, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_60 = x_43;
} else {
 lean_dec_ref(x_43);
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
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; size_t x_65; size_t x_66; 
x_62 = l_Lean_Expr_fvarId_x21(x_12);
lean_dec(x_12);
x_63 = lean_array_push(x_41, x_62);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_40);
lean_ctor_set(x_64, 1, x_63);
x_65 = 1;
x_66 = x_3 + x_65;
x_3 = x_66;
x_4 = x_64;
goto _start;
}
}
}
}
}
lean_object* l_Lean_Meta_mkGeneralizationForbiddenSet(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; lean_object* x_15; 
x_8 = l_Std_HashSet_instInhabitedHashSet___closed__1;
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_2);
x_10 = l_Array_empty___closed__1;
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_array_get_size(x_1);
x_13 = lean_usize_of_nat(x_12);
lean_dec(x_12);
x_14 = 0;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_15 = l_Array_forInUnsafe_loop___at_Lean_Meta_mkGeneralizationForbiddenSet___spec__1(x_1, x_13, x_14, x_11, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_array_to_list(lean_box(0), x_19);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = l_Lean_Meta_mkGeneralizationForbiddenSet_loop(x_20, x_21, x_3, x_4, x_5, x_6, x_17);
return x_22;
}
else
{
uint8_t x_23; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_23 = !lean_is_exclusive(x_15);
if (x_23 == 0)
{
return x_15;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_15, 0);
x_25 = lean_ctor_get(x_15, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_15);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_mkGeneralizationForbiddenSet___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_forInUnsafe_loop___at_Lean_Meta_mkGeneralizationForbiddenSet___spec__1(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_12;
}
}
lean_object* l_Lean_Meta_mkGeneralizationForbiddenSet___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_mkGeneralizationForbiddenSet(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Lean_Meta_getFVarSetToGeneralize_match__1___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_Meta_getFVarSetToGeneralize_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_getFVarSetToGeneralize_match__1___rarg), 2, 0);
return x_2;
}
}
uint8_t l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__5(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = x_3 == x_4;
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = l_Std_PersistentArray_anyMAux___at_Lean_Meta_getFVarSetToGeneralize___spec__4(x_1, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = x_3 + x_8;
x_3 = x_9;
goto _start;
}
else
{
uint8_t x_11; 
x_11 = 1;
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = 0;
return x_12;
}
}
}
uint8_t l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__6(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = x_3 == x_4;
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_array_uget(x_2, x_3);
if (lean_obj_tag(x_6) == 0)
{
size_t x_7; size_t x_8; 
x_7 = 1;
x_8 = x_3 + x_7;
x_3 = x_8;
goto _start;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_10);
lean_dec(x_6);
x_11 = l_Lean_LocalDecl_fvarId(x_10);
lean_dec(x_10);
x_12 = l_Lean_NameSet_contains(x_1, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
size_t x_13; size_t x_14; 
x_13 = 1;
x_14 = x_3 + x_13;
x_3 = x_14;
goto _start;
}
else
{
uint8_t x_16; 
x_16 = 1;
return x_16;
}
}
}
else
{
uint8_t x_17; 
x_17 = 0;
return x_17;
}
}
}
uint8_t l_Std_PersistentArray_anyMAux___at_Lean_Meta_getFVarSetToGeneralize___spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_array_get_size(x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
uint8_t x_7; 
lean_dec(x_4);
x_7 = 0;
return x_7;
}
else
{
uint8_t x_8; 
x_8 = lean_nat_dec_le(x_4, x_4);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_4);
x_9 = 0;
return x_9;
}
else
{
size_t x_10; size_t x_11; uint8_t x_12; 
x_10 = 0;
x_11 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_12 = l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__5(x_1, x_3, x_10, x_11);
return x_12;
}
}
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_ctor_get(x_2, 0);
x_14 = lean_array_get_size(x_13);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_nat_dec_lt(x_15, x_14);
if (x_16 == 0)
{
uint8_t x_17; 
lean_dec(x_14);
x_17 = 0;
return x_17;
}
else
{
uint8_t x_18; 
x_18 = lean_nat_dec_le(x_14, x_14);
if (x_18 == 0)
{
uint8_t x_19; 
lean_dec(x_14);
x_19 = 0;
return x_19;
}
else
{
size_t x_20; size_t x_21; uint8_t x_22; 
x_20 = 0;
x_21 = lean_usize_of_nat(x_14);
lean_dec(x_14);
x_22 = l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__6(x_1, x_13, x_20, x_21);
return x_22;
}
}
}
}
}
uint8_t l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__7(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = x_3 == x_4;
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_array_uget(x_2, x_3);
if (lean_obj_tag(x_6) == 0)
{
size_t x_7; size_t x_8; 
x_7 = 1;
x_8 = x_3 + x_7;
x_3 = x_8;
goto _start;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_10);
lean_dec(x_6);
x_11 = l_Lean_LocalDecl_fvarId(x_10);
lean_dec(x_10);
x_12 = l_Lean_NameSet_contains(x_1, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
size_t x_13; size_t x_14; 
x_13 = 1;
x_14 = x_3 + x_13;
x_3 = x_14;
goto _start;
}
else
{
uint8_t x_16; 
x_16 = 1;
return x_16;
}
}
}
else
{
uint8_t x_17; 
x_17 = 0;
return x_17;
}
}
}
uint8_t l_Std_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = l_Std_PersistentArray_anyMAux___at_Lean_Meta_getFVarSetToGeneralize___spec__4(x_1, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_array_get_size(x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_lt(x_7, x_6);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_6);
x_9 = 0;
return x_9;
}
else
{
uint8_t x_10; 
x_10 = lean_nat_dec_le(x_6, x_6);
if (x_10 == 0)
{
uint8_t x_11; 
lean_dec(x_6);
x_11 = 0;
return x_11;
}
else
{
size_t x_12; size_t x_13; uint8_t x_14; 
x_12 = 0;
x_13 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_14 = l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__7(x_1, x_5, x_12, x_13);
return x_14;
}
}
}
else
{
return x_4;
}
}
}
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at_Lean_Meta_getFVarSetToGeneralize___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_3)) {
case 1:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_2);
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
lean_dec(x_3);
x_7 = l_Lean_NameSet_contains(x_5, x_6);
lean_dec(x_6);
x_8 = lean_box(x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_4);
return x_9;
}
case 2:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_3, 0);
lean_inc(x_11);
lean_dec(x_3);
lean_inc(x_2);
x_12 = l_Lean_MetavarContext_getExprAssignment_x3f(x_2, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_13 = l_Lean_MetavarContext_getDecl(x_2, x_11);
lean_dec(x_11);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = l_Std_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__3(x_10, x_15);
lean_dec(x_15);
x_17 = lean_box(x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_4);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_11);
x_19 = lean_ctor_get(x_12, 0);
lean_inc(x_19);
lean_dec(x_12);
x_20 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__1(x_1, x_2, x_19, x_4);
return x_20;
}
}
case 5:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_21 = lean_ctor_get(x_3, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_3, 1);
lean_inc(x_22);
lean_dec(x_3);
lean_inc(x_2);
x_23 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__1(x_1, x_2, x_22, x_4);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_unbox(x_24);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; 
lean_dec(x_24);
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_27 = l_Lean_Expr_isApp(x_21);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__1(x_1, x_2, x_21, x_26);
return x_28;
}
else
{
x_3 = x_21;
x_4 = x_26;
goto _start;
}
}
else
{
uint8_t x_30; 
lean_dec(x_21);
lean_dec(x_2);
x_30 = !lean_is_exclusive(x_23);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_23, 0);
lean_dec(x_31);
return x_23;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_23, 1);
lean_inc(x_32);
lean_dec(x_23);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_24);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
case 6:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_34 = lean_ctor_get(x_3, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_3, 2);
lean_inc(x_35);
lean_dec(x_3);
lean_inc(x_2);
x_36 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__1(x_1, x_2, x_34, x_4);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_unbox(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
lean_dec(x_37);
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_dec(x_36);
x_40 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__1(x_1, x_2, x_35, x_39);
return x_40;
}
else
{
uint8_t x_41; 
lean_dec(x_35);
lean_dec(x_2);
x_41 = !lean_is_exclusive(x_36);
if (x_41 == 0)
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_36, 0);
lean_dec(x_42);
return x_36;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_36, 1);
lean_inc(x_43);
lean_dec(x_36);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_37);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
case 7:
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_45 = lean_ctor_get(x_3, 1);
lean_inc(x_45);
x_46 = lean_ctor_get(x_3, 2);
lean_inc(x_46);
lean_dec(x_3);
lean_inc(x_2);
x_47 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__1(x_1, x_2, x_45, x_4);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_unbox(x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
lean_dec(x_48);
x_50 = lean_ctor_get(x_47, 1);
lean_inc(x_50);
lean_dec(x_47);
x_51 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__1(x_1, x_2, x_46, x_50);
return x_51;
}
else
{
uint8_t x_52; 
lean_dec(x_46);
lean_dec(x_2);
x_52 = !lean_is_exclusive(x_47);
if (x_52 == 0)
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_47, 0);
lean_dec(x_53);
return x_47;
}
else
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_47, 1);
lean_inc(x_54);
lean_dec(x_47);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_48);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
case 8:
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_56 = lean_ctor_get(x_3, 1);
lean_inc(x_56);
x_57 = lean_ctor_get(x_3, 2);
lean_inc(x_57);
x_58 = lean_ctor_get(x_3, 3);
lean_inc(x_58);
lean_dec(x_3);
lean_inc(x_2);
x_59 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__1(x_1, x_2, x_56, x_4);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_unbox(x_60);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
lean_dec(x_60);
x_62 = lean_ctor_get(x_59, 1);
lean_inc(x_62);
lean_dec(x_59);
lean_inc(x_2);
x_63 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__1(x_1, x_2, x_57, x_62);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_unbox(x_64);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; 
lean_dec(x_64);
x_66 = lean_ctor_get(x_63, 1);
lean_inc(x_66);
lean_dec(x_63);
x_67 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__1(x_1, x_2, x_58, x_66);
return x_67;
}
else
{
uint8_t x_68; 
lean_dec(x_58);
lean_dec(x_2);
x_68 = !lean_is_exclusive(x_63);
if (x_68 == 0)
{
lean_object* x_69; 
x_69 = lean_ctor_get(x_63, 0);
lean_dec(x_69);
return x_63;
}
else
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_63, 1);
lean_inc(x_70);
lean_dec(x_63);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_64);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
else
{
uint8_t x_72; 
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_2);
x_72 = !lean_is_exclusive(x_59);
if (x_72 == 0)
{
lean_object* x_73; 
x_73 = lean_ctor_get(x_59, 0);
lean_dec(x_73);
return x_59;
}
else
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_ctor_get(x_59, 1);
lean_inc(x_74);
lean_dec(x_59);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_60);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
case 10:
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_ctor_get(x_3, 1);
lean_inc(x_76);
lean_dec(x_3);
x_77 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__1(x_1, x_2, x_76, x_4);
return x_77;
}
case 11:
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_ctor_get(x_3, 2);
lean_inc(x_78);
lean_dec(x_3);
x_79 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__1(x_1, x_2, x_78, x_4);
return x_79;
}
default: 
{
uint8_t x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_3);
lean_dec(x_2);
x_80 = 0;
x_81 = lean_box(x_80);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_4);
return x_82;
}
}
}
}
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
lean_inc(x_3);
x_5 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_shouldVisit(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_unbox(x_6);
lean_dec(x_6);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_3);
lean_dec(x_2);
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_5, 0);
lean_dec(x_9);
x_10 = 0;
x_11 = lean_box(x_10);
lean_ctor_set(x_5, 0, x_11);
return x_5;
}
else
{
lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_5, 1);
lean_inc(x_12);
lean_dec(x_5);
x_13 = 0;
x_14 = lean_box(x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_12);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_5, 1);
lean_inc(x_16);
lean_dec(x_5);
x_17 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at_Lean_Meta_getFVarSetToGeneralize___spec__2(x_1, x_2, x_3, x_16);
return x_17;
}
}
}
uint8_t l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__12(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = x_3 == x_4;
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = l_Std_PersistentArray_anyMAux___at_Lean_Meta_getFVarSetToGeneralize___spec__11(x_1, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = x_3 + x_8;
x_3 = x_9;
goto _start;
}
else
{
uint8_t x_11; 
x_11 = 1;
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = 0;
return x_12;
}
}
}
uint8_t l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__13(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = x_3 == x_4;
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_array_uget(x_2, x_3);
if (lean_obj_tag(x_6) == 0)
{
size_t x_7; size_t x_8; 
x_7 = 1;
x_8 = x_3 + x_7;
x_3 = x_8;
goto _start;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_10);
lean_dec(x_6);
x_11 = l_Lean_LocalDecl_fvarId(x_10);
lean_dec(x_10);
x_12 = l_Lean_NameSet_contains(x_1, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
size_t x_13; size_t x_14; 
x_13 = 1;
x_14 = x_3 + x_13;
x_3 = x_14;
goto _start;
}
else
{
uint8_t x_16; 
x_16 = 1;
return x_16;
}
}
}
else
{
uint8_t x_17; 
x_17 = 0;
return x_17;
}
}
}
uint8_t l_Std_PersistentArray_anyMAux___at_Lean_Meta_getFVarSetToGeneralize___spec__11(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_array_get_size(x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
uint8_t x_7; 
lean_dec(x_4);
x_7 = 0;
return x_7;
}
else
{
uint8_t x_8; 
x_8 = lean_nat_dec_le(x_4, x_4);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_4);
x_9 = 0;
return x_9;
}
else
{
size_t x_10; size_t x_11; uint8_t x_12; 
x_10 = 0;
x_11 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_12 = l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__12(x_1, x_3, x_10, x_11);
return x_12;
}
}
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_ctor_get(x_2, 0);
x_14 = lean_array_get_size(x_13);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_nat_dec_lt(x_15, x_14);
if (x_16 == 0)
{
uint8_t x_17; 
lean_dec(x_14);
x_17 = 0;
return x_17;
}
else
{
uint8_t x_18; 
x_18 = lean_nat_dec_le(x_14, x_14);
if (x_18 == 0)
{
uint8_t x_19; 
lean_dec(x_14);
x_19 = 0;
return x_19;
}
else
{
size_t x_20; size_t x_21; uint8_t x_22; 
x_20 = 0;
x_21 = lean_usize_of_nat(x_14);
lean_dec(x_14);
x_22 = l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__13(x_1, x_13, x_20, x_21);
return x_22;
}
}
}
}
}
uint8_t l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__14(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = x_3 == x_4;
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_array_uget(x_2, x_3);
if (lean_obj_tag(x_6) == 0)
{
size_t x_7; size_t x_8; 
x_7 = 1;
x_8 = x_3 + x_7;
x_3 = x_8;
goto _start;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_10);
lean_dec(x_6);
x_11 = l_Lean_LocalDecl_fvarId(x_10);
lean_dec(x_10);
x_12 = l_Lean_NameSet_contains(x_1, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
size_t x_13; size_t x_14; 
x_13 = 1;
x_14 = x_3 + x_13;
x_3 = x_14;
goto _start;
}
else
{
uint8_t x_16; 
x_16 = 1;
return x_16;
}
}
}
else
{
uint8_t x_17; 
x_17 = 0;
return x_17;
}
}
}
uint8_t l_Std_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__10(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = l_Std_PersistentArray_anyMAux___at_Lean_Meta_getFVarSetToGeneralize___spec__11(x_1, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_array_get_size(x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_lt(x_7, x_6);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_6);
x_9 = 0;
return x_9;
}
else
{
uint8_t x_10; 
x_10 = lean_nat_dec_le(x_6, x_6);
if (x_10 == 0)
{
uint8_t x_11; 
lean_dec(x_6);
x_11 = 0;
return x_11;
}
else
{
size_t x_12; size_t x_13; uint8_t x_14; 
x_12 = 0;
x_13 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_14 = l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__14(x_1, x_5, x_12, x_13);
return x_14;
}
}
}
else
{
return x_4;
}
}
}
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at_Lean_Meta_getFVarSetToGeneralize___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_3)) {
case 1:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_2);
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
lean_dec(x_3);
x_7 = l_Lean_NameSet_contains(x_5, x_6);
lean_dec(x_6);
x_8 = lean_box(x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_4);
return x_9;
}
case 2:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_3, 0);
lean_inc(x_11);
lean_dec(x_3);
lean_inc(x_2);
x_12 = l_Lean_MetavarContext_getExprAssignment_x3f(x_2, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_13 = l_Lean_MetavarContext_getDecl(x_2, x_11);
lean_dec(x_11);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = l_Std_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__10(x_10, x_15);
lean_dec(x_15);
x_17 = lean_box(x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_4);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_11);
x_19 = lean_ctor_get(x_12, 0);
lean_inc(x_19);
lean_dec(x_12);
x_20 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__8(x_1, x_2, x_19, x_4);
return x_20;
}
}
case 5:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_21 = lean_ctor_get(x_3, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_3, 1);
lean_inc(x_22);
lean_dec(x_3);
lean_inc(x_2);
x_23 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__8(x_1, x_2, x_22, x_4);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_unbox(x_24);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; 
lean_dec(x_24);
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_27 = l_Lean_Expr_isApp(x_21);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__8(x_1, x_2, x_21, x_26);
return x_28;
}
else
{
x_3 = x_21;
x_4 = x_26;
goto _start;
}
}
else
{
uint8_t x_30; 
lean_dec(x_21);
lean_dec(x_2);
x_30 = !lean_is_exclusive(x_23);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_23, 0);
lean_dec(x_31);
return x_23;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_23, 1);
lean_inc(x_32);
lean_dec(x_23);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_24);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
case 6:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_34 = lean_ctor_get(x_3, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_3, 2);
lean_inc(x_35);
lean_dec(x_3);
lean_inc(x_2);
x_36 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__8(x_1, x_2, x_34, x_4);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_unbox(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
lean_dec(x_37);
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_dec(x_36);
x_40 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__8(x_1, x_2, x_35, x_39);
return x_40;
}
else
{
uint8_t x_41; 
lean_dec(x_35);
lean_dec(x_2);
x_41 = !lean_is_exclusive(x_36);
if (x_41 == 0)
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_36, 0);
lean_dec(x_42);
return x_36;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_36, 1);
lean_inc(x_43);
lean_dec(x_36);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_37);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
case 7:
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_45 = lean_ctor_get(x_3, 1);
lean_inc(x_45);
x_46 = lean_ctor_get(x_3, 2);
lean_inc(x_46);
lean_dec(x_3);
lean_inc(x_2);
x_47 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__8(x_1, x_2, x_45, x_4);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_unbox(x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
lean_dec(x_48);
x_50 = lean_ctor_get(x_47, 1);
lean_inc(x_50);
lean_dec(x_47);
x_51 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__8(x_1, x_2, x_46, x_50);
return x_51;
}
else
{
uint8_t x_52; 
lean_dec(x_46);
lean_dec(x_2);
x_52 = !lean_is_exclusive(x_47);
if (x_52 == 0)
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_47, 0);
lean_dec(x_53);
return x_47;
}
else
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_47, 1);
lean_inc(x_54);
lean_dec(x_47);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_48);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
case 8:
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_56 = lean_ctor_get(x_3, 1);
lean_inc(x_56);
x_57 = lean_ctor_get(x_3, 2);
lean_inc(x_57);
x_58 = lean_ctor_get(x_3, 3);
lean_inc(x_58);
lean_dec(x_3);
lean_inc(x_2);
x_59 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__8(x_1, x_2, x_56, x_4);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_unbox(x_60);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
lean_dec(x_60);
x_62 = lean_ctor_get(x_59, 1);
lean_inc(x_62);
lean_dec(x_59);
lean_inc(x_2);
x_63 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__8(x_1, x_2, x_57, x_62);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_unbox(x_64);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; 
lean_dec(x_64);
x_66 = lean_ctor_get(x_63, 1);
lean_inc(x_66);
lean_dec(x_63);
x_67 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__8(x_1, x_2, x_58, x_66);
return x_67;
}
else
{
uint8_t x_68; 
lean_dec(x_58);
lean_dec(x_2);
x_68 = !lean_is_exclusive(x_63);
if (x_68 == 0)
{
lean_object* x_69; 
x_69 = lean_ctor_get(x_63, 0);
lean_dec(x_69);
return x_63;
}
else
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_63, 1);
lean_inc(x_70);
lean_dec(x_63);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_64);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
else
{
uint8_t x_72; 
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_2);
x_72 = !lean_is_exclusive(x_59);
if (x_72 == 0)
{
lean_object* x_73; 
x_73 = lean_ctor_get(x_59, 0);
lean_dec(x_73);
return x_59;
}
else
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_ctor_get(x_59, 1);
lean_inc(x_74);
lean_dec(x_59);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_60);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
case 10:
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_ctor_get(x_3, 1);
lean_inc(x_76);
lean_dec(x_3);
x_77 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__8(x_1, x_2, x_76, x_4);
return x_77;
}
case 11:
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_ctor_get(x_3, 2);
lean_inc(x_78);
lean_dec(x_3);
x_79 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__8(x_1, x_2, x_78, x_4);
return x_79;
}
default: 
{
uint8_t x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_3);
lean_dec(x_2);
x_80 = 0;
x_81 = lean_box(x_80);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_4);
return x_82;
}
}
}
}
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
lean_inc(x_3);
x_5 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_shouldVisit(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_unbox(x_6);
lean_dec(x_6);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_3);
lean_dec(x_2);
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_5, 0);
lean_dec(x_9);
x_10 = 0;
x_11 = lean_box(x_10);
lean_ctor_set(x_5, 0, x_11);
return x_5;
}
else
{
lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_5, 1);
lean_inc(x_12);
lean_dec(x_5);
x_13 = 0;
x_14 = lean_box(x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_12);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_5, 1);
lean_inc(x_16);
lean_dec(x_5);
x_17 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at_Lean_Meta_getFVarSetToGeneralize___spec__9(x_1, x_2, x_3, x_16);
return x_17;
}
}
}
uint8_t l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__19(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = x_3 == x_4;
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = l_Std_PersistentArray_anyMAux___at_Lean_Meta_getFVarSetToGeneralize___spec__18(x_1, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = x_3 + x_8;
x_3 = x_9;
goto _start;
}
else
{
uint8_t x_11; 
x_11 = 1;
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = 0;
return x_12;
}
}
}
uint8_t l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__20(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = x_3 == x_4;
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_array_uget(x_2, x_3);
if (lean_obj_tag(x_6) == 0)
{
size_t x_7; size_t x_8; 
x_7 = 1;
x_8 = x_3 + x_7;
x_3 = x_8;
goto _start;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_10);
lean_dec(x_6);
x_11 = l_Lean_LocalDecl_fvarId(x_10);
lean_dec(x_10);
x_12 = l_Lean_NameSet_contains(x_1, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
size_t x_13; size_t x_14; 
x_13 = 1;
x_14 = x_3 + x_13;
x_3 = x_14;
goto _start;
}
else
{
uint8_t x_16; 
x_16 = 1;
return x_16;
}
}
}
else
{
uint8_t x_17; 
x_17 = 0;
return x_17;
}
}
}
uint8_t l_Std_PersistentArray_anyMAux___at_Lean_Meta_getFVarSetToGeneralize___spec__18(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_array_get_size(x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
uint8_t x_7; 
lean_dec(x_4);
x_7 = 0;
return x_7;
}
else
{
uint8_t x_8; 
x_8 = lean_nat_dec_le(x_4, x_4);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_4);
x_9 = 0;
return x_9;
}
else
{
size_t x_10; size_t x_11; uint8_t x_12; 
x_10 = 0;
x_11 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_12 = l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__19(x_1, x_3, x_10, x_11);
return x_12;
}
}
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_ctor_get(x_2, 0);
x_14 = lean_array_get_size(x_13);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_nat_dec_lt(x_15, x_14);
if (x_16 == 0)
{
uint8_t x_17; 
lean_dec(x_14);
x_17 = 0;
return x_17;
}
else
{
uint8_t x_18; 
x_18 = lean_nat_dec_le(x_14, x_14);
if (x_18 == 0)
{
uint8_t x_19; 
lean_dec(x_14);
x_19 = 0;
return x_19;
}
else
{
size_t x_20; size_t x_21; uint8_t x_22; 
x_20 = 0;
x_21 = lean_usize_of_nat(x_14);
lean_dec(x_14);
x_22 = l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__20(x_1, x_13, x_20, x_21);
return x_22;
}
}
}
}
}
uint8_t l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__21(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = x_3 == x_4;
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_array_uget(x_2, x_3);
if (lean_obj_tag(x_6) == 0)
{
size_t x_7; size_t x_8; 
x_7 = 1;
x_8 = x_3 + x_7;
x_3 = x_8;
goto _start;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_10);
lean_dec(x_6);
x_11 = l_Lean_LocalDecl_fvarId(x_10);
lean_dec(x_10);
x_12 = l_Lean_NameSet_contains(x_1, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
size_t x_13; size_t x_14; 
x_13 = 1;
x_14 = x_3 + x_13;
x_3 = x_14;
goto _start;
}
else
{
uint8_t x_16; 
x_16 = 1;
return x_16;
}
}
}
else
{
uint8_t x_17; 
x_17 = 0;
return x_17;
}
}
}
uint8_t l_Std_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__17(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = l_Std_PersistentArray_anyMAux___at_Lean_Meta_getFVarSetToGeneralize___spec__18(x_1, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_array_get_size(x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_lt(x_7, x_6);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_6);
x_9 = 0;
return x_9;
}
else
{
uint8_t x_10; 
x_10 = lean_nat_dec_le(x_6, x_6);
if (x_10 == 0)
{
uint8_t x_11; 
lean_dec(x_6);
x_11 = 0;
return x_11;
}
else
{
size_t x_12; size_t x_13; uint8_t x_14; 
x_12 = 0;
x_13 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_14 = l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__21(x_1, x_5, x_12, x_13);
return x_14;
}
}
}
else
{
return x_4;
}
}
}
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at_Lean_Meta_getFVarSetToGeneralize___spec__16(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_3)) {
case 1:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_2);
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
lean_dec(x_3);
x_7 = l_Lean_NameSet_contains(x_5, x_6);
lean_dec(x_6);
x_8 = lean_box(x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_4);
return x_9;
}
case 2:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_3, 0);
lean_inc(x_11);
lean_dec(x_3);
lean_inc(x_2);
x_12 = l_Lean_MetavarContext_getExprAssignment_x3f(x_2, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_13 = l_Lean_MetavarContext_getDecl(x_2, x_11);
lean_dec(x_11);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = l_Std_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__17(x_10, x_15);
lean_dec(x_15);
x_17 = lean_box(x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_4);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_11);
x_19 = lean_ctor_get(x_12, 0);
lean_inc(x_19);
lean_dec(x_12);
x_20 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__15(x_1, x_2, x_19, x_4);
return x_20;
}
}
case 5:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_21 = lean_ctor_get(x_3, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_3, 1);
lean_inc(x_22);
lean_dec(x_3);
lean_inc(x_2);
x_23 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__15(x_1, x_2, x_22, x_4);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_unbox(x_24);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; 
lean_dec(x_24);
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_27 = l_Lean_Expr_isApp(x_21);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__15(x_1, x_2, x_21, x_26);
return x_28;
}
else
{
x_3 = x_21;
x_4 = x_26;
goto _start;
}
}
else
{
uint8_t x_30; 
lean_dec(x_21);
lean_dec(x_2);
x_30 = !lean_is_exclusive(x_23);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_23, 0);
lean_dec(x_31);
return x_23;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_23, 1);
lean_inc(x_32);
lean_dec(x_23);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_24);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
case 6:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_34 = lean_ctor_get(x_3, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_3, 2);
lean_inc(x_35);
lean_dec(x_3);
lean_inc(x_2);
x_36 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__15(x_1, x_2, x_34, x_4);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_unbox(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
lean_dec(x_37);
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_dec(x_36);
x_40 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__15(x_1, x_2, x_35, x_39);
return x_40;
}
else
{
uint8_t x_41; 
lean_dec(x_35);
lean_dec(x_2);
x_41 = !lean_is_exclusive(x_36);
if (x_41 == 0)
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_36, 0);
lean_dec(x_42);
return x_36;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_36, 1);
lean_inc(x_43);
lean_dec(x_36);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_37);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
case 7:
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_45 = lean_ctor_get(x_3, 1);
lean_inc(x_45);
x_46 = lean_ctor_get(x_3, 2);
lean_inc(x_46);
lean_dec(x_3);
lean_inc(x_2);
x_47 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__15(x_1, x_2, x_45, x_4);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_unbox(x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
lean_dec(x_48);
x_50 = lean_ctor_get(x_47, 1);
lean_inc(x_50);
lean_dec(x_47);
x_51 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__15(x_1, x_2, x_46, x_50);
return x_51;
}
else
{
uint8_t x_52; 
lean_dec(x_46);
lean_dec(x_2);
x_52 = !lean_is_exclusive(x_47);
if (x_52 == 0)
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_47, 0);
lean_dec(x_53);
return x_47;
}
else
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_47, 1);
lean_inc(x_54);
lean_dec(x_47);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_48);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
case 8:
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_56 = lean_ctor_get(x_3, 1);
lean_inc(x_56);
x_57 = lean_ctor_get(x_3, 2);
lean_inc(x_57);
x_58 = lean_ctor_get(x_3, 3);
lean_inc(x_58);
lean_dec(x_3);
lean_inc(x_2);
x_59 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__15(x_1, x_2, x_56, x_4);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_unbox(x_60);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
lean_dec(x_60);
x_62 = lean_ctor_get(x_59, 1);
lean_inc(x_62);
lean_dec(x_59);
lean_inc(x_2);
x_63 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__15(x_1, x_2, x_57, x_62);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_unbox(x_64);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; 
lean_dec(x_64);
x_66 = lean_ctor_get(x_63, 1);
lean_inc(x_66);
lean_dec(x_63);
x_67 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__15(x_1, x_2, x_58, x_66);
return x_67;
}
else
{
uint8_t x_68; 
lean_dec(x_58);
lean_dec(x_2);
x_68 = !lean_is_exclusive(x_63);
if (x_68 == 0)
{
lean_object* x_69; 
x_69 = lean_ctor_get(x_63, 0);
lean_dec(x_69);
return x_63;
}
else
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_63, 1);
lean_inc(x_70);
lean_dec(x_63);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_64);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
else
{
uint8_t x_72; 
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_2);
x_72 = !lean_is_exclusive(x_59);
if (x_72 == 0)
{
lean_object* x_73; 
x_73 = lean_ctor_get(x_59, 0);
lean_dec(x_73);
return x_59;
}
else
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_ctor_get(x_59, 1);
lean_inc(x_74);
lean_dec(x_59);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_60);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
case 10:
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_ctor_get(x_3, 1);
lean_inc(x_76);
lean_dec(x_3);
x_77 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__15(x_1, x_2, x_76, x_4);
return x_77;
}
case 11:
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_ctor_get(x_3, 2);
lean_inc(x_78);
lean_dec(x_3);
x_79 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__15(x_1, x_2, x_78, x_4);
return x_79;
}
default: 
{
uint8_t x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_3);
lean_dec(x_2);
x_80 = 0;
x_81 = lean_box(x_80);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_4);
return x_82;
}
}
}
}
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__15(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
lean_inc(x_3);
x_5 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_shouldVisit(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_unbox(x_6);
lean_dec(x_6);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_3);
lean_dec(x_2);
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_5, 0);
lean_dec(x_9);
x_10 = 0;
x_11 = lean_box(x_10);
lean_ctor_set(x_5, 0, x_11);
return x_5;
}
else
{
lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_5, 1);
lean_inc(x_12);
lean_dec(x_5);
x_13 = 0;
x_14 = lean_box(x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_12);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_5, 1);
lean_inc(x_16);
lean_dec(x_5);
x_17 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at_Lean_Meta_getFVarSetToGeneralize___spec__16(x_1, x_2, x_3, x_16);
return x_17;
}
}
}
uint8_t l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__26(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = x_3 == x_4;
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = l_Std_PersistentArray_anyMAux___at_Lean_Meta_getFVarSetToGeneralize___spec__25(x_1, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = x_3 + x_8;
x_3 = x_9;
goto _start;
}
else
{
uint8_t x_11; 
x_11 = 1;
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = 0;
return x_12;
}
}
}
uint8_t l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__27(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = x_3 == x_4;
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_array_uget(x_2, x_3);
if (lean_obj_tag(x_6) == 0)
{
size_t x_7; size_t x_8; 
x_7 = 1;
x_8 = x_3 + x_7;
x_3 = x_8;
goto _start;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_10);
lean_dec(x_6);
x_11 = l_Lean_LocalDecl_fvarId(x_10);
lean_dec(x_10);
x_12 = l_Lean_NameSet_contains(x_1, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
size_t x_13; size_t x_14; 
x_13 = 1;
x_14 = x_3 + x_13;
x_3 = x_14;
goto _start;
}
else
{
uint8_t x_16; 
x_16 = 1;
return x_16;
}
}
}
else
{
uint8_t x_17; 
x_17 = 0;
return x_17;
}
}
}
uint8_t l_Std_PersistentArray_anyMAux___at_Lean_Meta_getFVarSetToGeneralize___spec__25(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_array_get_size(x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
uint8_t x_7; 
lean_dec(x_4);
x_7 = 0;
return x_7;
}
else
{
uint8_t x_8; 
x_8 = lean_nat_dec_le(x_4, x_4);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_4);
x_9 = 0;
return x_9;
}
else
{
size_t x_10; size_t x_11; uint8_t x_12; 
x_10 = 0;
x_11 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_12 = l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__26(x_1, x_3, x_10, x_11);
return x_12;
}
}
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_ctor_get(x_2, 0);
x_14 = lean_array_get_size(x_13);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_nat_dec_lt(x_15, x_14);
if (x_16 == 0)
{
uint8_t x_17; 
lean_dec(x_14);
x_17 = 0;
return x_17;
}
else
{
uint8_t x_18; 
x_18 = lean_nat_dec_le(x_14, x_14);
if (x_18 == 0)
{
uint8_t x_19; 
lean_dec(x_14);
x_19 = 0;
return x_19;
}
else
{
size_t x_20; size_t x_21; uint8_t x_22; 
x_20 = 0;
x_21 = lean_usize_of_nat(x_14);
lean_dec(x_14);
x_22 = l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__27(x_1, x_13, x_20, x_21);
return x_22;
}
}
}
}
}
uint8_t l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__28(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = x_3 == x_4;
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_array_uget(x_2, x_3);
if (lean_obj_tag(x_6) == 0)
{
size_t x_7; size_t x_8; 
x_7 = 1;
x_8 = x_3 + x_7;
x_3 = x_8;
goto _start;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_10);
lean_dec(x_6);
x_11 = l_Lean_LocalDecl_fvarId(x_10);
lean_dec(x_10);
x_12 = l_Lean_NameSet_contains(x_1, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
size_t x_13; size_t x_14; 
x_13 = 1;
x_14 = x_3 + x_13;
x_3 = x_14;
goto _start;
}
else
{
uint8_t x_16; 
x_16 = 1;
return x_16;
}
}
}
else
{
uint8_t x_17; 
x_17 = 0;
return x_17;
}
}
}
uint8_t l_Std_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__24(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = l_Std_PersistentArray_anyMAux___at_Lean_Meta_getFVarSetToGeneralize___spec__25(x_1, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_array_get_size(x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_lt(x_7, x_6);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_6);
x_9 = 0;
return x_9;
}
else
{
uint8_t x_10; 
x_10 = lean_nat_dec_le(x_6, x_6);
if (x_10 == 0)
{
uint8_t x_11; 
lean_dec(x_6);
x_11 = 0;
return x_11;
}
else
{
size_t x_12; size_t x_13; uint8_t x_14; 
x_12 = 0;
x_13 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_14 = l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__28(x_1, x_5, x_12, x_13);
return x_14;
}
}
}
else
{
return x_4;
}
}
}
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at_Lean_Meta_getFVarSetToGeneralize___spec__23(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_3)) {
case 1:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_2);
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
lean_dec(x_3);
x_7 = l_Lean_NameSet_contains(x_5, x_6);
lean_dec(x_6);
x_8 = lean_box(x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_4);
return x_9;
}
case 2:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_3, 0);
lean_inc(x_11);
lean_dec(x_3);
lean_inc(x_2);
x_12 = l_Lean_MetavarContext_getExprAssignment_x3f(x_2, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_13 = l_Lean_MetavarContext_getDecl(x_2, x_11);
lean_dec(x_11);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = l_Std_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__24(x_10, x_15);
lean_dec(x_15);
x_17 = lean_box(x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_4);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_11);
x_19 = lean_ctor_get(x_12, 0);
lean_inc(x_19);
lean_dec(x_12);
x_20 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__22(x_1, x_2, x_19, x_4);
return x_20;
}
}
case 5:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_21 = lean_ctor_get(x_3, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_3, 1);
lean_inc(x_22);
lean_dec(x_3);
lean_inc(x_2);
x_23 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__22(x_1, x_2, x_22, x_4);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_unbox(x_24);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; 
lean_dec(x_24);
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_27 = l_Lean_Expr_isApp(x_21);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__22(x_1, x_2, x_21, x_26);
return x_28;
}
else
{
x_3 = x_21;
x_4 = x_26;
goto _start;
}
}
else
{
uint8_t x_30; 
lean_dec(x_21);
lean_dec(x_2);
x_30 = !lean_is_exclusive(x_23);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_23, 0);
lean_dec(x_31);
return x_23;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_23, 1);
lean_inc(x_32);
lean_dec(x_23);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_24);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
case 6:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_34 = lean_ctor_get(x_3, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_3, 2);
lean_inc(x_35);
lean_dec(x_3);
lean_inc(x_2);
x_36 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__22(x_1, x_2, x_34, x_4);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_unbox(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
lean_dec(x_37);
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_dec(x_36);
x_40 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__22(x_1, x_2, x_35, x_39);
return x_40;
}
else
{
uint8_t x_41; 
lean_dec(x_35);
lean_dec(x_2);
x_41 = !lean_is_exclusive(x_36);
if (x_41 == 0)
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_36, 0);
lean_dec(x_42);
return x_36;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_36, 1);
lean_inc(x_43);
lean_dec(x_36);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_37);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
case 7:
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_45 = lean_ctor_get(x_3, 1);
lean_inc(x_45);
x_46 = lean_ctor_get(x_3, 2);
lean_inc(x_46);
lean_dec(x_3);
lean_inc(x_2);
x_47 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__22(x_1, x_2, x_45, x_4);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_unbox(x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
lean_dec(x_48);
x_50 = lean_ctor_get(x_47, 1);
lean_inc(x_50);
lean_dec(x_47);
x_51 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__22(x_1, x_2, x_46, x_50);
return x_51;
}
else
{
uint8_t x_52; 
lean_dec(x_46);
lean_dec(x_2);
x_52 = !lean_is_exclusive(x_47);
if (x_52 == 0)
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_47, 0);
lean_dec(x_53);
return x_47;
}
else
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_47, 1);
lean_inc(x_54);
lean_dec(x_47);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_48);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
case 8:
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_56 = lean_ctor_get(x_3, 1);
lean_inc(x_56);
x_57 = lean_ctor_get(x_3, 2);
lean_inc(x_57);
x_58 = lean_ctor_get(x_3, 3);
lean_inc(x_58);
lean_dec(x_3);
lean_inc(x_2);
x_59 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__22(x_1, x_2, x_56, x_4);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_unbox(x_60);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
lean_dec(x_60);
x_62 = lean_ctor_get(x_59, 1);
lean_inc(x_62);
lean_dec(x_59);
lean_inc(x_2);
x_63 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__22(x_1, x_2, x_57, x_62);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_unbox(x_64);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; 
lean_dec(x_64);
x_66 = lean_ctor_get(x_63, 1);
lean_inc(x_66);
lean_dec(x_63);
x_67 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__22(x_1, x_2, x_58, x_66);
return x_67;
}
else
{
uint8_t x_68; 
lean_dec(x_58);
lean_dec(x_2);
x_68 = !lean_is_exclusive(x_63);
if (x_68 == 0)
{
lean_object* x_69; 
x_69 = lean_ctor_get(x_63, 0);
lean_dec(x_69);
return x_63;
}
else
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_63, 1);
lean_inc(x_70);
lean_dec(x_63);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_64);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
else
{
uint8_t x_72; 
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_2);
x_72 = !lean_is_exclusive(x_59);
if (x_72 == 0)
{
lean_object* x_73; 
x_73 = lean_ctor_get(x_59, 0);
lean_dec(x_73);
return x_59;
}
else
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_ctor_get(x_59, 1);
lean_inc(x_74);
lean_dec(x_59);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_60);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
case 10:
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_ctor_get(x_3, 1);
lean_inc(x_76);
lean_dec(x_3);
x_77 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__22(x_1, x_2, x_76, x_4);
return x_77;
}
case 11:
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_ctor_get(x_3, 2);
lean_inc(x_78);
lean_dec(x_3);
x_79 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__22(x_1, x_2, x_78, x_4);
return x_79;
}
default: 
{
uint8_t x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_3);
lean_dec(x_2);
x_80 = 0;
x_81 = lean_box(x_80);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_4);
return x_82;
}
}
}
}
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__22(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
lean_inc(x_3);
x_5 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_shouldVisit(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_unbox(x_6);
lean_dec(x_6);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_3);
lean_dec(x_2);
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_5, 0);
lean_dec(x_9);
x_10 = 0;
x_11 = lean_box(x_10);
lean_ctor_set(x_5, 0, x_11);
return x_5;
}
else
{
lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_5, 1);
lean_inc(x_12);
lean_dec(x_5);
x_13 = 0;
x_14 = lean_box(x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_12);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_5, 1);
lean_inc(x_16);
lean_dec(x_5);
x_17 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at_Lean_Meta_getFVarSetToGeneralize___spec__23(x_1, x_2, x_3, x_16);
return x_17;
}
}
}
uint8_t l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__33(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = x_3 == x_4;
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = l_Std_PersistentArray_anyMAux___at_Lean_Meta_getFVarSetToGeneralize___spec__32(x_1, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = x_3 + x_8;
x_3 = x_9;
goto _start;
}
else
{
uint8_t x_11; 
x_11 = 1;
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = 0;
return x_12;
}
}
}
uint8_t l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__34(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = x_3 == x_4;
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_array_uget(x_2, x_3);
if (lean_obj_tag(x_6) == 0)
{
size_t x_7; size_t x_8; 
x_7 = 1;
x_8 = x_3 + x_7;
x_3 = x_8;
goto _start;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_10);
lean_dec(x_6);
x_11 = l_Lean_LocalDecl_fvarId(x_10);
lean_dec(x_10);
x_12 = l_Lean_NameSet_contains(x_1, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
size_t x_13; size_t x_14; 
x_13 = 1;
x_14 = x_3 + x_13;
x_3 = x_14;
goto _start;
}
else
{
uint8_t x_16; 
x_16 = 1;
return x_16;
}
}
}
else
{
uint8_t x_17; 
x_17 = 0;
return x_17;
}
}
}
uint8_t l_Std_PersistentArray_anyMAux___at_Lean_Meta_getFVarSetToGeneralize___spec__32(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_array_get_size(x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
uint8_t x_7; 
lean_dec(x_4);
x_7 = 0;
return x_7;
}
else
{
uint8_t x_8; 
x_8 = lean_nat_dec_le(x_4, x_4);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_4);
x_9 = 0;
return x_9;
}
else
{
size_t x_10; size_t x_11; uint8_t x_12; 
x_10 = 0;
x_11 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_12 = l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__33(x_1, x_3, x_10, x_11);
return x_12;
}
}
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_ctor_get(x_2, 0);
x_14 = lean_array_get_size(x_13);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_nat_dec_lt(x_15, x_14);
if (x_16 == 0)
{
uint8_t x_17; 
lean_dec(x_14);
x_17 = 0;
return x_17;
}
else
{
uint8_t x_18; 
x_18 = lean_nat_dec_le(x_14, x_14);
if (x_18 == 0)
{
uint8_t x_19; 
lean_dec(x_14);
x_19 = 0;
return x_19;
}
else
{
size_t x_20; size_t x_21; uint8_t x_22; 
x_20 = 0;
x_21 = lean_usize_of_nat(x_14);
lean_dec(x_14);
x_22 = l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__34(x_1, x_13, x_20, x_21);
return x_22;
}
}
}
}
}
uint8_t l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__35(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = x_3 == x_4;
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_array_uget(x_2, x_3);
if (lean_obj_tag(x_6) == 0)
{
size_t x_7; size_t x_8; 
x_7 = 1;
x_8 = x_3 + x_7;
x_3 = x_8;
goto _start;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_10);
lean_dec(x_6);
x_11 = l_Lean_LocalDecl_fvarId(x_10);
lean_dec(x_10);
x_12 = l_Lean_NameSet_contains(x_1, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
size_t x_13; size_t x_14; 
x_13 = 1;
x_14 = x_3 + x_13;
x_3 = x_14;
goto _start;
}
else
{
uint8_t x_16; 
x_16 = 1;
return x_16;
}
}
}
else
{
uint8_t x_17; 
x_17 = 0;
return x_17;
}
}
}
uint8_t l_Std_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__31(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = l_Std_PersistentArray_anyMAux___at_Lean_Meta_getFVarSetToGeneralize___spec__32(x_1, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_array_get_size(x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_lt(x_7, x_6);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_6);
x_9 = 0;
return x_9;
}
else
{
uint8_t x_10; 
x_10 = lean_nat_dec_le(x_6, x_6);
if (x_10 == 0)
{
uint8_t x_11; 
lean_dec(x_6);
x_11 = 0;
return x_11;
}
else
{
size_t x_12; size_t x_13; uint8_t x_14; 
x_12 = 0;
x_13 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_14 = l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__35(x_1, x_5, x_12, x_13);
return x_14;
}
}
}
else
{
return x_4;
}
}
}
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at_Lean_Meta_getFVarSetToGeneralize___spec__30(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_3)) {
case 1:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_2);
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
lean_dec(x_3);
x_7 = l_Lean_NameSet_contains(x_5, x_6);
lean_dec(x_6);
x_8 = lean_box(x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_4);
return x_9;
}
case 2:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_3, 0);
lean_inc(x_11);
lean_dec(x_3);
lean_inc(x_2);
x_12 = l_Lean_MetavarContext_getExprAssignment_x3f(x_2, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_13 = l_Lean_MetavarContext_getDecl(x_2, x_11);
lean_dec(x_11);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = l_Std_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__31(x_10, x_15);
lean_dec(x_15);
x_17 = lean_box(x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_4);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_11);
x_19 = lean_ctor_get(x_12, 0);
lean_inc(x_19);
lean_dec(x_12);
x_20 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__29(x_1, x_2, x_19, x_4);
return x_20;
}
}
case 5:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_21 = lean_ctor_get(x_3, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_3, 1);
lean_inc(x_22);
lean_dec(x_3);
lean_inc(x_2);
x_23 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__29(x_1, x_2, x_22, x_4);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_unbox(x_24);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; 
lean_dec(x_24);
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_27 = l_Lean_Expr_isApp(x_21);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__29(x_1, x_2, x_21, x_26);
return x_28;
}
else
{
x_3 = x_21;
x_4 = x_26;
goto _start;
}
}
else
{
uint8_t x_30; 
lean_dec(x_21);
lean_dec(x_2);
x_30 = !lean_is_exclusive(x_23);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_23, 0);
lean_dec(x_31);
return x_23;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_23, 1);
lean_inc(x_32);
lean_dec(x_23);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_24);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
case 6:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_34 = lean_ctor_get(x_3, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_3, 2);
lean_inc(x_35);
lean_dec(x_3);
lean_inc(x_2);
x_36 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__29(x_1, x_2, x_34, x_4);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_unbox(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
lean_dec(x_37);
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_dec(x_36);
x_40 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__29(x_1, x_2, x_35, x_39);
return x_40;
}
else
{
uint8_t x_41; 
lean_dec(x_35);
lean_dec(x_2);
x_41 = !lean_is_exclusive(x_36);
if (x_41 == 0)
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_36, 0);
lean_dec(x_42);
return x_36;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_36, 1);
lean_inc(x_43);
lean_dec(x_36);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_37);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
case 7:
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_45 = lean_ctor_get(x_3, 1);
lean_inc(x_45);
x_46 = lean_ctor_get(x_3, 2);
lean_inc(x_46);
lean_dec(x_3);
lean_inc(x_2);
x_47 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__29(x_1, x_2, x_45, x_4);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_unbox(x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
lean_dec(x_48);
x_50 = lean_ctor_get(x_47, 1);
lean_inc(x_50);
lean_dec(x_47);
x_51 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__29(x_1, x_2, x_46, x_50);
return x_51;
}
else
{
uint8_t x_52; 
lean_dec(x_46);
lean_dec(x_2);
x_52 = !lean_is_exclusive(x_47);
if (x_52 == 0)
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_47, 0);
lean_dec(x_53);
return x_47;
}
else
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_47, 1);
lean_inc(x_54);
lean_dec(x_47);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_48);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
case 8:
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_56 = lean_ctor_get(x_3, 1);
lean_inc(x_56);
x_57 = lean_ctor_get(x_3, 2);
lean_inc(x_57);
x_58 = lean_ctor_get(x_3, 3);
lean_inc(x_58);
lean_dec(x_3);
lean_inc(x_2);
x_59 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__29(x_1, x_2, x_56, x_4);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_unbox(x_60);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
lean_dec(x_60);
x_62 = lean_ctor_get(x_59, 1);
lean_inc(x_62);
lean_dec(x_59);
lean_inc(x_2);
x_63 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__29(x_1, x_2, x_57, x_62);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_unbox(x_64);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; 
lean_dec(x_64);
x_66 = lean_ctor_get(x_63, 1);
lean_inc(x_66);
lean_dec(x_63);
x_67 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__29(x_1, x_2, x_58, x_66);
return x_67;
}
else
{
uint8_t x_68; 
lean_dec(x_58);
lean_dec(x_2);
x_68 = !lean_is_exclusive(x_63);
if (x_68 == 0)
{
lean_object* x_69; 
x_69 = lean_ctor_get(x_63, 0);
lean_dec(x_69);
return x_63;
}
else
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_63, 1);
lean_inc(x_70);
lean_dec(x_63);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_64);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
else
{
uint8_t x_72; 
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_2);
x_72 = !lean_is_exclusive(x_59);
if (x_72 == 0)
{
lean_object* x_73; 
x_73 = lean_ctor_get(x_59, 0);
lean_dec(x_73);
return x_59;
}
else
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_ctor_get(x_59, 1);
lean_inc(x_74);
lean_dec(x_59);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_60);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
case 10:
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_ctor_get(x_3, 1);
lean_inc(x_76);
lean_dec(x_3);
x_77 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__29(x_1, x_2, x_76, x_4);
return x_77;
}
case 11:
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_ctor_get(x_3, 2);
lean_inc(x_78);
lean_dec(x_3);
x_79 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__29(x_1, x_2, x_78, x_4);
return x_79;
}
default: 
{
uint8_t x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_3);
lean_dec(x_2);
x_80 = 0;
x_81 = lean_box(x_80);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_4);
return x_82;
}
}
}
}
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__29(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
lean_inc(x_3);
x_5 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_shouldVisit(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_unbox(x_6);
lean_dec(x_6);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_3);
lean_dec(x_2);
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_5, 0);
lean_dec(x_9);
x_10 = 0;
x_11 = lean_box(x_10);
lean_ctor_set(x_5, 0, x_11);
return x_5;
}
else
{
lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_5, 1);
lean_inc(x_12);
lean_dec(x_5);
x_13 = 0;
x_14 = lean_box(x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_12);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_5, 1);
lean_inc(x_16);
lean_dec(x_5);
x_17 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at_Lean_Meta_getFVarSetToGeneralize___spec__30(x_1, x_2, x_3, x_16);
return x_17;
}
}
}
uint8_t l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__40(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = x_3 == x_4;
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = l_Std_PersistentArray_anyMAux___at_Lean_Meta_getFVarSetToGeneralize___spec__39(x_1, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = x_3 + x_8;
x_3 = x_9;
goto _start;
}
else
{
uint8_t x_11; 
x_11 = 1;
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = 0;
return x_12;
}
}
}
uint8_t l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__41(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = x_3 == x_4;
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_array_uget(x_2, x_3);
if (lean_obj_tag(x_6) == 0)
{
size_t x_7; size_t x_8; 
x_7 = 1;
x_8 = x_3 + x_7;
x_3 = x_8;
goto _start;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_10);
lean_dec(x_6);
x_11 = l_Lean_LocalDecl_fvarId(x_10);
lean_dec(x_10);
x_12 = l_Lean_NameSet_contains(x_1, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
size_t x_13; size_t x_14; 
x_13 = 1;
x_14 = x_3 + x_13;
x_3 = x_14;
goto _start;
}
else
{
uint8_t x_16; 
x_16 = 1;
return x_16;
}
}
}
else
{
uint8_t x_17; 
x_17 = 0;
return x_17;
}
}
}
uint8_t l_Std_PersistentArray_anyMAux___at_Lean_Meta_getFVarSetToGeneralize___spec__39(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_array_get_size(x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
uint8_t x_7; 
lean_dec(x_4);
x_7 = 0;
return x_7;
}
else
{
uint8_t x_8; 
x_8 = lean_nat_dec_le(x_4, x_4);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_4);
x_9 = 0;
return x_9;
}
else
{
size_t x_10; size_t x_11; uint8_t x_12; 
x_10 = 0;
x_11 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_12 = l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__40(x_1, x_3, x_10, x_11);
return x_12;
}
}
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_ctor_get(x_2, 0);
x_14 = lean_array_get_size(x_13);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_nat_dec_lt(x_15, x_14);
if (x_16 == 0)
{
uint8_t x_17; 
lean_dec(x_14);
x_17 = 0;
return x_17;
}
else
{
uint8_t x_18; 
x_18 = lean_nat_dec_le(x_14, x_14);
if (x_18 == 0)
{
uint8_t x_19; 
lean_dec(x_14);
x_19 = 0;
return x_19;
}
else
{
size_t x_20; size_t x_21; uint8_t x_22; 
x_20 = 0;
x_21 = lean_usize_of_nat(x_14);
lean_dec(x_14);
x_22 = l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__41(x_1, x_13, x_20, x_21);
return x_22;
}
}
}
}
}
uint8_t l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__42(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = x_3 == x_4;
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_array_uget(x_2, x_3);
if (lean_obj_tag(x_6) == 0)
{
size_t x_7; size_t x_8; 
x_7 = 1;
x_8 = x_3 + x_7;
x_3 = x_8;
goto _start;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_10);
lean_dec(x_6);
x_11 = l_Lean_LocalDecl_fvarId(x_10);
lean_dec(x_10);
x_12 = l_Lean_NameSet_contains(x_1, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
size_t x_13; size_t x_14; 
x_13 = 1;
x_14 = x_3 + x_13;
x_3 = x_14;
goto _start;
}
else
{
uint8_t x_16; 
x_16 = 1;
return x_16;
}
}
}
else
{
uint8_t x_17; 
x_17 = 0;
return x_17;
}
}
}
uint8_t l_Std_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__38(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = l_Std_PersistentArray_anyMAux___at_Lean_Meta_getFVarSetToGeneralize___spec__39(x_1, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_array_get_size(x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_lt(x_7, x_6);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_6);
x_9 = 0;
return x_9;
}
else
{
uint8_t x_10; 
x_10 = lean_nat_dec_le(x_6, x_6);
if (x_10 == 0)
{
uint8_t x_11; 
lean_dec(x_6);
x_11 = 0;
return x_11;
}
else
{
size_t x_12; size_t x_13; uint8_t x_14; 
x_12 = 0;
x_13 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_14 = l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__42(x_1, x_5, x_12, x_13);
return x_14;
}
}
}
else
{
return x_4;
}
}
}
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at_Lean_Meta_getFVarSetToGeneralize___spec__37(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_3)) {
case 1:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_2);
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
lean_dec(x_3);
x_7 = l_Lean_NameSet_contains(x_5, x_6);
lean_dec(x_6);
x_8 = lean_box(x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_4);
return x_9;
}
case 2:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_3, 0);
lean_inc(x_11);
lean_dec(x_3);
lean_inc(x_2);
x_12 = l_Lean_MetavarContext_getExprAssignment_x3f(x_2, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_13 = l_Lean_MetavarContext_getDecl(x_2, x_11);
lean_dec(x_11);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = l_Std_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__38(x_10, x_15);
lean_dec(x_15);
x_17 = lean_box(x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_4);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_11);
x_19 = lean_ctor_get(x_12, 0);
lean_inc(x_19);
lean_dec(x_12);
x_20 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__36(x_1, x_2, x_19, x_4);
return x_20;
}
}
case 5:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_21 = lean_ctor_get(x_3, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_3, 1);
lean_inc(x_22);
lean_dec(x_3);
lean_inc(x_2);
x_23 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__36(x_1, x_2, x_22, x_4);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_unbox(x_24);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; 
lean_dec(x_24);
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_27 = l_Lean_Expr_isApp(x_21);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__36(x_1, x_2, x_21, x_26);
return x_28;
}
else
{
x_3 = x_21;
x_4 = x_26;
goto _start;
}
}
else
{
uint8_t x_30; 
lean_dec(x_21);
lean_dec(x_2);
x_30 = !lean_is_exclusive(x_23);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_23, 0);
lean_dec(x_31);
return x_23;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_23, 1);
lean_inc(x_32);
lean_dec(x_23);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_24);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
case 6:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_34 = lean_ctor_get(x_3, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_3, 2);
lean_inc(x_35);
lean_dec(x_3);
lean_inc(x_2);
x_36 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__36(x_1, x_2, x_34, x_4);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_unbox(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
lean_dec(x_37);
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_dec(x_36);
x_40 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__36(x_1, x_2, x_35, x_39);
return x_40;
}
else
{
uint8_t x_41; 
lean_dec(x_35);
lean_dec(x_2);
x_41 = !lean_is_exclusive(x_36);
if (x_41 == 0)
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_36, 0);
lean_dec(x_42);
return x_36;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_36, 1);
lean_inc(x_43);
lean_dec(x_36);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_37);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
case 7:
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_45 = lean_ctor_get(x_3, 1);
lean_inc(x_45);
x_46 = lean_ctor_get(x_3, 2);
lean_inc(x_46);
lean_dec(x_3);
lean_inc(x_2);
x_47 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__36(x_1, x_2, x_45, x_4);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_unbox(x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
lean_dec(x_48);
x_50 = lean_ctor_get(x_47, 1);
lean_inc(x_50);
lean_dec(x_47);
x_51 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__36(x_1, x_2, x_46, x_50);
return x_51;
}
else
{
uint8_t x_52; 
lean_dec(x_46);
lean_dec(x_2);
x_52 = !lean_is_exclusive(x_47);
if (x_52 == 0)
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_47, 0);
lean_dec(x_53);
return x_47;
}
else
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_47, 1);
lean_inc(x_54);
lean_dec(x_47);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_48);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
case 8:
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_56 = lean_ctor_get(x_3, 1);
lean_inc(x_56);
x_57 = lean_ctor_get(x_3, 2);
lean_inc(x_57);
x_58 = lean_ctor_get(x_3, 3);
lean_inc(x_58);
lean_dec(x_3);
lean_inc(x_2);
x_59 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__36(x_1, x_2, x_56, x_4);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_unbox(x_60);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
lean_dec(x_60);
x_62 = lean_ctor_get(x_59, 1);
lean_inc(x_62);
lean_dec(x_59);
lean_inc(x_2);
x_63 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__36(x_1, x_2, x_57, x_62);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_unbox(x_64);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; 
lean_dec(x_64);
x_66 = lean_ctor_get(x_63, 1);
lean_inc(x_66);
lean_dec(x_63);
x_67 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__36(x_1, x_2, x_58, x_66);
return x_67;
}
else
{
uint8_t x_68; 
lean_dec(x_58);
lean_dec(x_2);
x_68 = !lean_is_exclusive(x_63);
if (x_68 == 0)
{
lean_object* x_69; 
x_69 = lean_ctor_get(x_63, 0);
lean_dec(x_69);
return x_63;
}
else
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_63, 1);
lean_inc(x_70);
lean_dec(x_63);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_64);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
else
{
uint8_t x_72; 
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_2);
x_72 = !lean_is_exclusive(x_59);
if (x_72 == 0)
{
lean_object* x_73; 
x_73 = lean_ctor_get(x_59, 0);
lean_dec(x_73);
return x_59;
}
else
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_ctor_get(x_59, 1);
lean_inc(x_74);
lean_dec(x_59);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_60);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
case 10:
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_ctor_get(x_3, 1);
lean_inc(x_76);
lean_dec(x_3);
x_77 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__36(x_1, x_2, x_76, x_4);
return x_77;
}
case 11:
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_ctor_get(x_3, 2);
lean_inc(x_78);
lean_dec(x_3);
x_79 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__36(x_1, x_2, x_78, x_4);
return x_79;
}
default: 
{
uint8_t x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_3);
lean_dec(x_2);
x_80 = 0;
x_81 = lean_box(x_80);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_4);
return x_82;
}
}
}
}
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__36(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
lean_inc(x_3);
x_5 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_shouldVisit(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_unbox(x_6);
lean_dec(x_6);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_3);
lean_dec(x_2);
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_5, 0);
lean_dec(x_9);
x_10 = 0;
x_11 = lean_box(x_10);
lean_ctor_set(x_5, 0, x_11);
return x_5;
}
else
{
lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_5, 1);
lean_inc(x_12);
lean_dec(x_5);
x_13 = 0;
x_14 = lean_box(x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_12);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_5, 1);
lean_inc(x_16);
lean_dec(x_5);
x_17 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at_Lean_Meta_getFVarSetToGeneralize___spec__37(x_1, x_2, x_3, x_16);
return x_17;
}
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_getFVarSetToGeneralize___spec__45(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = x_6 < x_5;
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_3);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_array_uget(x_4, x_6);
x_16 = lean_ctor_get(x_7, 1);
lean_inc(x_16);
lean_dec(x_7);
x_17 = l_Std_PersistentArray_forInAux___at_Lean_Meta_getFVarSetToGeneralize___spec__44(x_1, x_2, x_15, x_16, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_15);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
lean_dec(x_3);
x_19 = !lean_is_exclusive(x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_17, 0);
lean_dec(x_20);
x_21 = lean_ctor_get(x_18, 0);
lean_inc(x_21);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_18);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
lean_ctor_set(x_17, 0, x_23);
return x_17;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_17, 1);
lean_inc(x_24);
lean_dec(x_17);
x_25 = lean_ctor_get(x_18, 0);
lean_inc(x_25);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_18);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_24);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; size_t x_32; size_t x_33; 
x_29 = lean_ctor_get(x_17, 1);
lean_inc(x_29);
lean_dec(x_17);
x_30 = lean_ctor_get(x_18, 0);
lean_inc(x_30);
lean_dec(x_18);
lean_inc(x_3);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_3);
lean_ctor_set(x_31, 1, x_30);
x_32 = 1;
x_33 = x_6 + x_32;
x_6 = x_33;
x_7 = x_31;
x_12 = x_29;
goto _start;
}
}
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_getFVarSetToGeneralize___spec__46(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_20; uint8_t x_37; 
x_37 = x_5 < x_4;
if (x_37 == 0)
{
lean_object* x_38; 
lean_dec(x_2);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_6);
lean_ctor_set(x_38, 1, x_11);
return x_38;
}
else
{
lean_object* x_39; 
x_39 = lean_array_uget(x_3, x_5);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_6, 1);
lean_inc(x_40);
lean_dec(x_6);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_11);
x_20 = x_42;
goto block_36;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_43 = lean_ctor_get(x_6, 1);
lean_inc(x_43);
lean_dec(x_6);
x_44 = lean_ctor_get(x_39, 0);
lean_inc(x_44);
lean_dec(x_39);
x_45 = lean_ctor_get(x_43, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
x_47 = l_Lean_LocalDecl_fvarId(x_44);
x_48 = l_Lean_NameSet_contains(x_1, x_47);
if (x_48 == 0)
{
uint8_t x_49; 
x_49 = l_Lean_LocalDecl_isAuxDecl(x_44);
if (x_49 == 0)
{
uint8_t x_50; uint8_t x_51; 
x_50 = l_Lean_LocalDecl_binderInfo(x_44);
x_51 = l_Lean_BinderInfo_isInstImplicit(x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_52 = lean_st_ref_get(x_10, x_11);
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
x_55 = lean_st_ref_get(x_8, x_53);
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
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_67 = lean_ctor_get(x_56, 0);
lean_inc(x_67);
lean_dec(x_56);
x_68 = lean_ctor_get(x_44, 3);
lean_inc(x_68);
lean_dec(x_44);
x_69 = l_Lean_Expr_hasFVar(x_68);
if (x_69 == 0)
{
uint8_t x_70; 
x_70 = l_Lean_Expr_hasMVar(x_68);
if (x_70 == 0)
{
uint8_t x_71; 
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_58);
lean_dec(x_47);
x_71 = !lean_is_exclusive(x_43);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_72 = lean_ctor_get(x_43, 1);
lean_dec(x_72);
x_73 = lean_ctor_get(x_43, 0);
lean_dec(x_73);
x_74 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_74, 0, x_43);
if (lean_is_scalar(x_54)) {
 x_75 = lean_alloc_ctor(0, 2, 0);
} else {
 x_75 = x_54;
}
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_57);
x_20 = x_75;
goto block_36;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_43);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_45);
lean_ctor_set(x_76, 1, x_46);
x_77 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_77, 0, x_76);
if (lean_is_scalar(x_54)) {
 x_78 = lean_alloc_ctor(0, 2, 0);
} else {
 x_78 = x_54;
}
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_57);
x_20 = x_78;
goto block_36;
}
}
else
{
lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_79 = l_Std_HashSet_instInhabitedHashSet___closed__1;
x_80 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__1(x_43, x_67, x_68, x_79);
x_81 = !lean_is_exclusive(x_43);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_82 = lean_ctor_get(x_43, 1);
lean_dec(x_82);
x_83 = lean_ctor_get(x_43, 0);
lean_dec(x_83);
x_84 = lean_ctor_get(x_80, 0);
lean_inc(x_84);
lean_dec(x_80);
x_85 = lean_unbox(x_84);
lean_dec(x_84);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; 
lean_dec(x_58);
lean_dec(x_47);
x_86 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_86, 0, x_43);
if (lean_is_scalar(x_54)) {
 x_87 = lean_alloc_ctor(0, 2, 0);
} else {
 x_87 = x_54;
}
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_57);
x_20 = x_87;
goto block_36;
}
else
{
lean_object* x_88; 
lean_free_object(x_43);
lean_dec(x_54);
x_88 = lean_box(0);
x_59 = x_88;
goto block_66;
}
}
else
{
lean_object* x_89; uint8_t x_90; 
lean_dec(x_43);
x_89 = lean_ctor_get(x_80, 0);
lean_inc(x_89);
lean_dec(x_80);
x_90 = lean_unbox(x_89);
lean_dec(x_89);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec(x_58);
lean_dec(x_47);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_45);
lean_ctor_set(x_91, 1, x_46);
x_92 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_92, 0, x_91);
if (lean_is_scalar(x_54)) {
 x_93 = lean_alloc_ctor(0, 2, 0);
} else {
 x_93 = x_54;
}
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_57);
x_20 = x_93;
goto block_36;
}
else
{
lean_object* x_94; 
lean_dec(x_54);
x_94 = lean_box(0);
x_59 = x_94;
goto block_66;
}
}
}
}
else
{
lean_object* x_95; lean_object* x_96; uint8_t x_97; 
x_95 = l_Std_HashSet_instInhabitedHashSet___closed__1;
x_96 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__8(x_43, x_67, x_68, x_95);
x_97 = !lean_is_exclusive(x_43);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; 
x_98 = lean_ctor_get(x_43, 1);
lean_dec(x_98);
x_99 = lean_ctor_get(x_43, 0);
lean_dec(x_99);
x_100 = lean_ctor_get(x_96, 0);
lean_inc(x_100);
lean_dec(x_96);
x_101 = lean_unbox(x_100);
lean_dec(x_100);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; 
lean_dec(x_58);
lean_dec(x_47);
x_102 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_102, 0, x_43);
if (lean_is_scalar(x_54)) {
 x_103 = lean_alloc_ctor(0, 2, 0);
} else {
 x_103 = x_54;
}
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_57);
x_20 = x_103;
goto block_36;
}
else
{
lean_object* x_104; 
lean_free_object(x_43);
lean_dec(x_54);
x_104 = lean_box(0);
x_59 = x_104;
goto block_66;
}
}
else
{
lean_object* x_105; uint8_t x_106; 
lean_dec(x_43);
x_105 = lean_ctor_get(x_96, 0);
lean_inc(x_105);
lean_dec(x_96);
x_106 = lean_unbox(x_105);
lean_dec(x_105);
if (x_106 == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
lean_dec(x_58);
lean_dec(x_47);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_45);
lean_ctor_set(x_107, 1, x_46);
x_108 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_108, 0, x_107);
if (lean_is_scalar(x_54)) {
 x_109 = lean_alloc_ctor(0, 2, 0);
} else {
 x_109 = x_54;
}
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_57);
x_20 = x_109;
goto block_36;
}
else
{
lean_object* x_110; 
lean_dec(x_54);
x_110 = lean_box(0);
x_59 = x_110;
goto block_66;
}
}
}
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_160; 
x_111 = lean_ctor_get(x_56, 0);
lean_inc(x_111);
lean_dec(x_56);
x_112 = lean_ctor_get(x_44, 3);
lean_inc(x_112);
x_113 = lean_ctor_get(x_44, 4);
lean_inc(x_113);
lean_dec(x_44);
x_160 = l_Lean_Expr_hasFVar(x_112);
if (x_160 == 0)
{
uint8_t x_161; 
x_161 = l_Lean_Expr_hasMVar(x_112);
if (x_161 == 0)
{
lean_object* x_162; 
lean_dec(x_112);
x_162 = l_Lean_MetavarContext_findLocalDeclDependsOn___closed__1;
x_114 = x_162;
goto block_159;
}
else
{
lean_object* x_163; lean_object* x_164; 
x_163 = l_Std_HashSet_instInhabitedHashSet___closed__1;
lean_inc(x_111);
x_164 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__29(x_43, x_111, x_112, x_163);
x_114 = x_164;
goto block_159;
}
}
else
{
lean_object* x_165; lean_object* x_166; 
x_165 = l_Std_HashSet_instInhabitedHashSet___closed__1;
lean_inc(x_111);
x_166 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__36(x_43, x_111, x_112, x_165);
x_114 = x_166;
goto block_159;
}
block_159:
{
lean_object* x_115; uint8_t x_116; 
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
x_116 = lean_unbox(x_115);
lean_dec(x_115);
if (x_116 == 0)
{
lean_object* x_117; uint8_t x_118; 
x_117 = lean_ctor_get(x_114, 1);
lean_inc(x_117);
lean_dec(x_114);
x_118 = l_Lean_Expr_hasFVar(x_113);
if (x_118 == 0)
{
uint8_t x_119; 
x_119 = l_Lean_Expr_hasMVar(x_113);
if (x_119 == 0)
{
uint8_t x_120; 
lean_dec(x_117);
lean_dec(x_113);
lean_dec(x_111);
lean_dec(x_58);
lean_dec(x_47);
x_120 = !lean_is_exclusive(x_43);
if (x_120 == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_121 = lean_ctor_get(x_43, 1);
lean_dec(x_121);
x_122 = lean_ctor_get(x_43, 0);
lean_dec(x_122);
x_123 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_123, 0, x_43);
if (lean_is_scalar(x_54)) {
 x_124 = lean_alloc_ctor(0, 2, 0);
} else {
 x_124 = x_54;
}
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_57);
x_20 = x_124;
goto block_36;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
lean_dec(x_43);
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_45);
lean_ctor_set(x_125, 1, x_46);
x_126 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_126, 0, x_125);
if (lean_is_scalar(x_54)) {
 x_127 = lean_alloc_ctor(0, 2, 0);
} else {
 x_127 = x_54;
}
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_127, 1, x_57);
x_20 = x_127;
goto block_36;
}
}
else
{
lean_object* x_128; uint8_t x_129; 
x_128 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__15(x_43, x_111, x_113, x_117);
x_129 = !lean_is_exclusive(x_43);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_133; 
x_130 = lean_ctor_get(x_43, 1);
lean_dec(x_130);
x_131 = lean_ctor_get(x_43, 0);
lean_dec(x_131);
x_132 = lean_ctor_get(x_128, 0);
lean_inc(x_132);
lean_dec(x_128);
x_133 = lean_unbox(x_132);
lean_dec(x_132);
if (x_133 == 0)
{
lean_object* x_134; lean_object* x_135; 
lean_dec(x_58);
lean_dec(x_47);
x_134 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_134, 0, x_43);
if (lean_is_scalar(x_54)) {
 x_135 = lean_alloc_ctor(0, 2, 0);
} else {
 x_135 = x_54;
}
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_57);
x_20 = x_135;
goto block_36;
}
else
{
lean_object* x_136; 
lean_free_object(x_43);
lean_dec(x_54);
x_136 = lean_box(0);
x_59 = x_136;
goto block_66;
}
}
else
{
lean_object* x_137; uint8_t x_138; 
lean_dec(x_43);
x_137 = lean_ctor_get(x_128, 0);
lean_inc(x_137);
lean_dec(x_128);
x_138 = lean_unbox(x_137);
lean_dec(x_137);
if (x_138 == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
lean_dec(x_58);
lean_dec(x_47);
x_139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_139, 0, x_45);
lean_ctor_set(x_139, 1, x_46);
x_140 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_140, 0, x_139);
if (lean_is_scalar(x_54)) {
 x_141 = lean_alloc_ctor(0, 2, 0);
} else {
 x_141 = x_54;
}
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_57);
x_20 = x_141;
goto block_36;
}
else
{
lean_object* x_142; 
lean_dec(x_54);
x_142 = lean_box(0);
x_59 = x_142;
goto block_66;
}
}
}
}
else
{
lean_object* x_143; uint8_t x_144; 
x_143 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__22(x_43, x_111, x_113, x_117);
x_144 = !lean_is_exclusive(x_43);
if (x_144 == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; uint8_t x_148; 
x_145 = lean_ctor_get(x_43, 1);
lean_dec(x_145);
x_146 = lean_ctor_get(x_43, 0);
lean_dec(x_146);
x_147 = lean_ctor_get(x_143, 0);
lean_inc(x_147);
lean_dec(x_143);
x_148 = lean_unbox(x_147);
lean_dec(x_147);
if (x_148 == 0)
{
lean_object* x_149; lean_object* x_150; 
lean_dec(x_58);
lean_dec(x_47);
x_149 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_149, 0, x_43);
if (lean_is_scalar(x_54)) {
 x_150 = lean_alloc_ctor(0, 2, 0);
} else {
 x_150 = x_54;
}
lean_ctor_set(x_150, 0, x_149);
lean_ctor_set(x_150, 1, x_57);
x_20 = x_150;
goto block_36;
}
else
{
lean_object* x_151; 
lean_free_object(x_43);
lean_dec(x_54);
x_151 = lean_box(0);
x_59 = x_151;
goto block_66;
}
}
else
{
lean_object* x_152; uint8_t x_153; 
lean_dec(x_43);
x_152 = lean_ctor_get(x_143, 0);
lean_inc(x_152);
lean_dec(x_143);
x_153 = lean_unbox(x_152);
lean_dec(x_152);
if (x_153 == 0)
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; 
lean_dec(x_58);
lean_dec(x_47);
x_154 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_154, 0, x_45);
lean_ctor_set(x_154, 1, x_46);
x_155 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_155, 0, x_154);
if (lean_is_scalar(x_54)) {
 x_156 = lean_alloc_ctor(0, 2, 0);
} else {
 x_156 = x_54;
}
lean_ctor_set(x_156, 0, x_155);
lean_ctor_set(x_156, 1, x_57);
x_20 = x_156;
goto block_36;
}
else
{
lean_object* x_157; 
lean_dec(x_54);
x_157 = lean_box(0);
x_59 = x_157;
goto block_66;
}
}
}
}
else
{
lean_object* x_158; 
lean_dec(x_114);
lean_dec(x_113);
lean_dec(x_111);
lean_dec(x_54);
lean_dec(x_43);
x_158 = lean_box(0);
x_59 = x_158;
goto block_66;
}
}
}
block_66:
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_59);
x_60 = lean_box(0);
lean_inc(x_47);
x_61 = l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_46, x_47, x_60);
x_62 = l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_45, x_47, x_60);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_61);
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_63);
if (lean_is_scalar(x_58)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_58;
}
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_57);
x_20 = x_65;
goto block_36;
}
}
else
{
uint8_t x_167; 
lean_dec(x_47);
lean_dec(x_44);
x_167 = !lean_is_exclusive(x_43);
if (x_167 == 0)
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_168 = lean_ctor_get(x_43, 1);
lean_dec(x_168);
x_169 = lean_ctor_get(x_43, 0);
lean_dec(x_169);
x_170 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_170, 0, x_43);
x_171 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_171, 1, x_11);
x_20 = x_171;
goto block_36;
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; 
lean_dec(x_43);
x_172 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_172, 0, x_45);
lean_ctor_set(x_172, 1, x_46);
x_173 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_173, 0, x_172);
x_174 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_174, 0, x_173);
lean_ctor_set(x_174, 1, x_11);
x_20 = x_174;
goto block_36;
}
}
}
else
{
uint8_t x_175; 
lean_dec(x_47);
lean_dec(x_44);
x_175 = !lean_is_exclusive(x_43);
if (x_175 == 0)
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_176 = lean_ctor_get(x_43, 1);
lean_dec(x_176);
x_177 = lean_ctor_get(x_43, 0);
lean_dec(x_177);
x_178 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_178, 0, x_43);
x_179 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_179, 0, x_178);
lean_ctor_set(x_179, 1, x_11);
x_20 = x_179;
goto block_36;
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; 
lean_dec(x_43);
x_180 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_180, 0, x_45);
lean_ctor_set(x_180, 1, x_46);
x_181 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_181, 0, x_180);
x_182 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_182, 0, x_181);
lean_ctor_set(x_182, 1, x_11);
x_20 = x_182;
goto block_36;
}
}
}
else
{
uint8_t x_183; 
lean_dec(x_47);
lean_dec(x_44);
x_183 = !lean_is_exclusive(x_43);
if (x_183 == 0)
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_184 = lean_ctor_get(x_43, 1);
lean_dec(x_184);
x_185 = lean_ctor_get(x_43, 0);
lean_dec(x_185);
x_186 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_186, 0, x_43);
x_187 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_187, 0, x_186);
lean_ctor_set(x_187, 1, x_11);
x_20 = x_187;
goto block_36;
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; 
lean_dec(x_43);
x_188 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_188, 0, x_45);
lean_ctor_set(x_188, 1, x_46);
x_189 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_189, 0, x_188);
x_190 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_190, 0, x_189);
lean_ctor_set(x_190, 1, x_11);
x_20 = x_190;
goto block_36;
}
}
}
}
block_19:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = 1;
x_17 = x_5 + x_16;
x_5 = x_17;
x_6 = x_15;
x_11 = x_14;
goto _start;
}
block_36:
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_2);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_2);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set(x_22, 0, x_25);
x_12 = x_20;
goto block_19;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_22, 0);
lean_inc(x_26);
lean_dec(x_22);
lean_inc(x_2);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_2);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_20, 0, x_28);
x_12 = x_20;
goto block_19;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_29 = lean_ctor_get(x_20, 0);
x_30 = lean_ctor_get(x_20, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_20);
x_31 = lean_ctor_get(x_29, 0);
lean_inc(x_31);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 x_32 = x_29;
} else {
 lean_dec_ref(x_29);
 x_32 = lean_box(0);
}
lean_inc(x_2);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_2);
lean_ctor_set(x_33, 1, x_31);
if (lean_is_scalar(x_32)) {
 x_34 = lean_alloc_ctor(1, 1, 0);
} else {
 x_34 = x_32;
}
lean_ctor_set(x_34, 0, x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_30);
x_12 = x_35;
goto block_19;
}
}
}
}
lean_object* l_Std_PersistentArray_forInAux___at_Lean_Meta_getFVarSetToGeneralize___spec__44___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
}
lean_object* l_Std_PersistentArray_forInAux___at_Lean_Meta_getFVarSetToGeneralize___spec__44(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_4);
x_13 = lean_array_get_size(x_10);
x_14 = lean_usize_of_nat(x_13);
lean_dec(x_13);
x_15 = 0;
x_16 = l_Array_forInUnsafe_loop___at_Lean_Meta_getFVarSetToGeneralize___spec__45(x_1, x_2, x_11, x_10, x_14, x_15, x_12, x_5, x_6, x_7, x_8, x_9);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_box(0);
x_22 = l_Std_PersistentArray_forInAux___at_Lean_Meta_getFVarSetToGeneralize___spec__44___lambda__1(x_20, x_21, x_5, x_6, x_7, x_8, x_19);
return x_22;
}
else
{
uint8_t x_23; 
lean_dec(x_17);
x_23 = !lean_is_exclusive(x_16);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_16, 0);
lean_dec(x_24);
x_25 = lean_ctor_get(x_18, 0);
lean_inc(x_25);
lean_dec(x_18);
lean_ctor_set(x_16, 0, x_25);
return x_16;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_16, 1);
lean_inc(x_26);
lean_dec(x_16);
x_27 = lean_ctor_get(x_18, 0);
lean_inc(x_27);
lean_dec(x_18);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; size_t x_33; size_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_29 = lean_ctor_get(x_3, 0);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_4);
x_32 = lean_array_get_size(x_29);
x_33 = lean_usize_of_nat(x_32);
lean_dec(x_32);
x_34 = 0;
x_35 = l_Array_forInUnsafe_loop___at_Lean_Meta_getFVarSetToGeneralize___spec__46(x_1, x_30, x_29, x_33, x_34, x_31, x_5, x_6, x_7, x_8, x_9);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_dec(x_35);
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_dec(x_36);
x_40 = lean_box(0);
x_41 = l_Std_PersistentArray_forInAux___at_Lean_Meta_getFVarSetToGeneralize___spec__44___lambda__1(x_39, x_40, x_5, x_6, x_7, x_8, x_38);
return x_41;
}
else
{
uint8_t x_42; 
lean_dec(x_36);
x_42 = !lean_is_exclusive(x_35);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_35, 0);
lean_dec(x_43);
x_44 = lean_ctor_get(x_37, 0);
lean_inc(x_44);
lean_dec(x_37);
lean_ctor_set(x_35, 0, x_44);
return x_35;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_35, 1);
lean_inc(x_45);
lean_dec(x_35);
x_46 = lean_ctor_get(x_37, 0);
lean_inc(x_46);
lean_dec(x_37);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
return x_47;
}
}
}
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_getFVarSetToGeneralize___spec__47(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_20; uint8_t x_37; 
x_37 = x_5 < x_4;
if (x_37 == 0)
{
lean_object* x_38; 
lean_dec(x_2);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_6);
lean_ctor_set(x_38, 1, x_11);
return x_38;
}
else
{
lean_object* x_39; 
x_39 = lean_array_uget(x_3, x_5);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_6, 1);
lean_inc(x_40);
lean_dec(x_6);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_11);
x_20 = x_42;
goto block_36;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_43 = lean_ctor_get(x_6, 1);
lean_inc(x_43);
lean_dec(x_6);
x_44 = lean_ctor_get(x_39, 0);
lean_inc(x_44);
lean_dec(x_39);
x_45 = lean_ctor_get(x_43, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
x_47 = l_Lean_LocalDecl_fvarId(x_44);
x_48 = l_Lean_NameSet_contains(x_1, x_47);
if (x_48 == 0)
{
uint8_t x_49; 
x_49 = l_Lean_LocalDecl_isAuxDecl(x_44);
if (x_49 == 0)
{
uint8_t x_50; uint8_t x_51; 
x_50 = l_Lean_LocalDecl_binderInfo(x_44);
x_51 = l_Lean_BinderInfo_isInstImplicit(x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_52 = lean_st_ref_get(x_10, x_11);
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
x_55 = lean_st_ref_get(x_8, x_53);
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
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_67 = lean_ctor_get(x_56, 0);
lean_inc(x_67);
lean_dec(x_56);
x_68 = lean_ctor_get(x_44, 3);
lean_inc(x_68);
lean_dec(x_44);
x_69 = l_Lean_Expr_hasFVar(x_68);
if (x_69 == 0)
{
uint8_t x_70; 
x_70 = l_Lean_Expr_hasMVar(x_68);
if (x_70 == 0)
{
uint8_t x_71; 
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_58);
lean_dec(x_47);
x_71 = !lean_is_exclusive(x_43);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_72 = lean_ctor_get(x_43, 1);
lean_dec(x_72);
x_73 = lean_ctor_get(x_43, 0);
lean_dec(x_73);
x_74 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_74, 0, x_43);
if (lean_is_scalar(x_54)) {
 x_75 = lean_alloc_ctor(0, 2, 0);
} else {
 x_75 = x_54;
}
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_57);
x_20 = x_75;
goto block_36;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_43);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_45);
lean_ctor_set(x_76, 1, x_46);
x_77 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_77, 0, x_76);
if (lean_is_scalar(x_54)) {
 x_78 = lean_alloc_ctor(0, 2, 0);
} else {
 x_78 = x_54;
}
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_57);
x_20 = x_78;
goto block_36;
}
}
else
{
lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_79 = l_Std_HashSet_instInhabitedHashSet___closed__1;
x_80 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__1(x_43, x_67, x_68, x_79);
x_81 = !lean_is_exclusive(x_43);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_82 = lean_ctor_get(x_43, 1);
lean_dec(x_82);
x_83 = lean_ctor_get(x_43, 0);
lean_dec(x_83);
x_84 = lean_ctor_get(x_80, 0);
lean_inc(x_84);
lean_dec(x_80);
x_85 = lean_unbox(x_84);
lean_dec(x_84);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; 
lean_dec(x_58);
lean_dec(x_47);
x_86 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_86, 0, x_43);
if (lean_is_scalar(x_54)) {
 x_87 = lean_alloc_ctor(0, 2, 0);
} else {
 x_87 = x_54;
}
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_57);
x_20 = x_87;
goto block_36;
}
else
{
lean_object* x_88; 
lean_free_object(x_43);
lean_dec(x_54);
x_88 = lean_box(0);
x_59 = x_88;
goto block_66;
}
}
else
{
lean_object* x_89; uint8_t x_90; 
lean_dec(x_43);
x_89 = lean_ctor_get(x_80, 0);
lean_inc(x_89);
lean_dec(x_80);
x_90 = lean_unbox(x_89);
lean_dec(x_89);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec(x_58);
lean_dec(x_47);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_45);
lean_ctor_set(x_91, 1, x_46);
x_92 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_92, 0, x_91);
if (lean_is_scalar(x_54)) {
 x_93 = lean_alloc_ctor(0, 2, 0);
} else {
 x_93 = x_54;
}
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_57);
x_20 = x_93;
goto block_36;
}
else
{
lean_object* x_94; 
lean_dec(x_54);
x_94 = lean_box(0);
x_59 = x_94;
goto block_66;
}
}
}
}
else
{
lean_object* x_95; lean_object* x_96; uint8_t x_97; 
x_95 = l_Std_HashSet_instInhabitedHashSet___closed__1;
x_96 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__8(x_43, x_67, x_68, x_95);
x_97 = !lean_is_exclusive(x_43);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; 
x_98 = lean_ctor_get(x_43, 1);
lean_dec(x_98);
x_99 = lean_ctor_get(x_43, 0);
lean_dec(x_99);
x_100 = lean_ctor_get(x_96, 0);
lean_inc(x_100);
lean_dec(x_96);
x_101 = lean_unbox(x_100);
lean_dec(x_100);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; 
lean_dec(x_58);
lean_dec(x_47);
x_102 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_102, 0, x_43);
if (lean_is_scalar(x_54)) {
 x_103 = lean_alloc_ctor(0, 2, 0);
} else {
 x_103 = x_54;
}
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_57);
x_20 = x_103;
goto block_36;
}
else
{
lean_object* x_104; 
lean_free_object(x_43);
lean_dec(x_54);
x_104 = lean_box(0);
x_59 = x_104;
goto block_66;
}
}
else
{
lean_object* x_105; uint8_t x_106; 
lean_dec(x_43);
x_105 = lean_ctor_get(x_96, 0);
lean_inc(x_105);
lean_dec(x_96);
x_106 = lean_unbox(x_105);
lean_dec(x_105);
if (x_106 == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
lean_dec(x_58);
lean_dec(x_47);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_45);
lean_ctor_set(x_107, 1, x_46);
x_108 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_108, 0, x_107);
if (lean_is_scalar(x_54)) {
 x_109 = lean_alloc_ctor(0, 2, 0);
} else {
 x_109 = x_54;
}
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_57);
x_20 = x_109;
goto block_36;
}
else
{
lean_object* x_110; 
lean_dec(x_54);
x_110 = lean_box(0);
x_59 = x_110;
goto block_66;
}
}
}
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_160; 
x_111 = lean_ctor_get(x_56, 0);
lean_inc(x_111);
lean_dec(x_56);
x_112 = lean_ctor_get(x_44, 3);
lean_inc(x_112);
x_113 = lean_ctor_get(x_44, 4);
lean_inc(x_113);
lean_dec(x_44);
x_160 = l_Lean_Expr_hasFVar(x_112);
if (x_160 == 0)
{
uint8_t x_161; 
x_161 = l_Lean_Expr_hasMVar(x_112);
if (x_161 == 0)
{
lean_object* x_162; 
lean_dec(x_112);
x_162 = l_Lean_MetavarContext_findLocalDeclDependsOn___closed__1;
x_114 = x_162;
goto block_159;
}
else
{
lean_object* x_163; lean_object* x_164; 
x_163 = l_Std_HashSet_instInhabitedHashSet___closed__1;
lean_inc(x_111);
x_164 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__29(x_43, x_111, x_112, x_163);
x_114 = x_164;
goto block_159;
}
}
else
{
lean_object* x_165; lean_object* x_166; 
x_165 = l_Std_HashSet_instInhabitedHashSet___closed__1;
lean_inc(x_111);
x_166 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__36(x_43, x_111, x_112, x_165);
x_114 = x_166;
goto block_159;
}
block_159:
{
lean_object* x_115; uint8_t x_116; 
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
x_116 = lean_unbox(x_115);
lean_dec(x_115);
if (x_116 == 0)
{
lean_object* x_117; uint8_t x_118; 
x_117 = lean_ctor_get(x_114, 1);
lean_inc(x_117);
lean_dec(x_114);
x_118 = l_Lean_Expr_hasFVar(x_113);
if (x_118 == 0)
{
uint8_t x_119; 
x_119 = l_Lean_Expr_hasMVar(x_113);
if (x_119 == 0)
{
uint8_t x_120; 
lean_dec(x_117);
lean_dec(x_113);
lean_dec(x_111);
lean_dec(x_58);
lean_dec(x_47);
x_120 = !lean_is_exclusive(x_43);
if (x_120 == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_121 = lean_ctor_get(x_43, 1);
lean_dec(x_121);
x_122 = lean_ctor_get(x_43, 0);
lean_dec(x_122);
x_123 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_123, 0, x_43);
if (lean_is_scalar(x_54)) {
 x_124 = lean_alloc_ctor(0, 2, 0);
} else {
 x_124 = x_54;
}
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_57);
x_20 = x_124;
goto block_36;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
lean_dec(x_43);
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_45);
lean_ctor_set(x_125, 1, x_46);
x_126 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_126, 0, x_125);
if (lean_is_scalar(x_54)) {
 x_127 = lean_alloc_ctor(0, 2, 0);
} else {
 x_127 = x_54;
}
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_127, 1, x_57);
x_20 = x_127;
goto block_36;
}
}
else
{
lean_object* x_128; uint8_t x_129; 
x_128 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__15(x_43, x_111, x_113, x_117);
x_129 = !lean_is_exclusive(x_43);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_133; 
x_130 = lean_ctor_get(x_43, 1);
lean_dec(x_130);
x_131 = lean_ctor_get(x_43, 0);
lean_dec(x_131);
x_132 = lean_ctor_get(x_128, 0);
lean_inc(x_132);
lean_dec(x_128);
x_133 = lean_unbox(x_132);
lean_dec(x_132);
if (x_133 == 0)
{
lean_object* x_134; lean_object* x_135; 
lean_dec(x_58);
lean_dec(x_47);
x_134 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_134, 0, x_43);
if (lean_is_scalar(x_54)) {
 x_135 = lean_alloc_ctor(0, 2, 0);
} else {
 x_135 = x_54;
}
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_57);
x_20 = x_135;
goto block_36;
}
else
{
lean_object* x_136; 
lean_free_object(x_43);
lean_dec(x_54);
x_136 = lean_box(0);
x_59 = x_136;
goto block_66;
}
}
else
{
lean_object* x_137; uint8_t x_138; 
lean_dec(x_43);
x_137 = lean_ctor_get(x_128, 0);
lean_inc(x_137);
lean_dec(x_128);
x_138 = lean_unbox(x_137);
lean_dec(x_137);
if (x_138 == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
lean_dec(x_58);
lean_dec(x_47);
x_139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_139, 0, x_45);
lean_ctor_set(x_139, 1, x_46);
x_140 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_140, 0, x_139);
if (lean_is_scalar(x_54)) {
 x_141 = lean_alloc_ctor(0, 2, 0);
} else {
 x_141 = x_54;
}
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_57);
x_20 = x_141;
goto block_36;
}
else
{
lean_object* x_142; 
lean_dec(x_54);
x_142 = lean_box(0);
x_59 = x_142;
goto block_66;
}
}
}
}
else
{
lean_object* x_143; uint8_t x_144; 
x_143 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__22(x_43, x_111, x_113, x_117);
x_144 = !lean_is_exclusive(x_43);
if (x_144 == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; uint8_t x_148; 
x_145 = lean_ctor_get(x_43, 1);
lean_dec(x_145);
x_146 = lean_ctor_get(x_43, 0);
lean_dec(x_146);
x_147 = lean_ctor_get(x_143, 0);
lean_inc(x_147);
lean_dec(x_143);
x_148 = lean_unbox(x_147);
lean_dec(x_147);
if (x_148 == 0)
{
lean_object* x_149; lean_object* x_150; 
lean_dec(x_58);
lean_dec(x_47);
x_149 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_149, 0, x_43);
if (lean_is_scalar(x_54)) {
 x_150 = lean_alloc_ctor(0, 2, 0);
} else {
 x_150 = x_54;
}
lean_ctor_set(x_150, 0, x_149);
lean_ctor_set(x_150, 1, x_57);
x_20 = x_150;
goto block_36;
}
else
{
lean_object* x_151; 
lean_free_object(x_43);
lean_dec(x_54);
x_151 = lean_box(0);
x_59 = x_151;
goto block_66;
}
}
else
{
lean_object* x_152; uint8_t x_153; 
lean_dec(x_43);
x_152 = lean_ctor_get(x_143, 0);
lean_inc(x_152);
lean_dec(x_143);
x_153 = lean_unbox(x_152);
lean_dec(x_152);
if (x_153 == 0)
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; 
lean_dec(x_58);
lean_dec(x_47);
x_154 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_154, 0, x_45);
lean_ctor_set(x_154, 1, x_46);
x_155 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_155, 0, x_154);
if (lean_is_scalar(x_54)) {
 x_156 = lean_alloc_ctor(0, 2, 0);
} else {
 x_156 = x_54;
}
lean_ctor_set(x_156, 0, x_155);
lean_ctor_set(x_156, 1, x_57);
x_20 = x_156;
goto block_36;
}
else
{
lean_object* x_157; 
lean_dec(x_54);
x_157 = lean_box(0);
x_59 = x_157;
goto block_66;
}
}
}
}
else
{
lean_object* x_158; 
lean_dec(x_114);
lean_dec(x_113);
lean_dec(x_111);
lean_dec(x_54);
lean_dec(x_43);
x_158 = lean_box(0);
x_59 = x_158;
goto block_66;
}
}
}
block_66:
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_59);
x_60 = lean_box(0);
lean_inc(x_47);
x_61 = l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_46, x_47, x_60);
x_62 = l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_45, x_47, x_60);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_61);
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_63);
if (lean_is_scalar(x_58)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_58;
}
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_57);
x_20 = x_65;
goto block_36;
}
}
else
{
uint8_t x_167; 
lean_dec(x_47);
lean_dec(x_44);
x_167 = !lean_is_exclusive(x_43);
if (x_167 == 0)
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_168 = lean_ctor_get(x_43, 1);
lean_dec(x_168);
x_169 = lean_ctor_get(x_43, 0);
lean_dec(x_169);
x_170 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_170, 0, x_43);
x_171 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_171, 1, x_11);
x_20 = x_171;
goto block_36;
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; 
lean_dec(x_43);
x_172 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_172, 0, x_45);
lean_ctor_set(x_172, 1, x_46);
x_173 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_173, 0, x_172);
x_174 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_174, 0, x_173);
lean_ctor_set(x_174, 1, x_11);
x_20 = x_174;
goto block_36;
}
}
}
else
{
uint8_t x_175; 
lean_dec(x_47);
lean_dec(x_44);
x_175 = !lean_is_exclusive(x_43);
if (x_175 == 0)
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_176 = lean_ctor_get(x_43, 1);
lean_dec(x_176);
x_177 = lean_ctor_get(x_43, 0);
lean_dec(x_177);
x_178 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_178, 0, x_43);
x_179 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_179, 0, x_178);
lean_ctor_set(x_179, 1, x_11);
x_20 = x_179;
goto block_36;
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; 
lean_dec(x_43);
x_180 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_180, 0, x_45);
lean_ctor_set(x_180, 1, x_46);
x_181 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_181, 0, x_180);
x_182 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_182, 0, x_181);
lean_ctor_set(x_182, 1, x_11);
x_20 = x_182;
goto block_36;
}
}
}
else
{
uint8_t x_183; 
lean_dec(x_47);
lean_dec(x_44);
x_183 = !lean_is_exclusive(x_43);
if (x_183 == 0)
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_184 = lean_ctor_get(x_43, 1);
lean_dec(x_184);
x_185 = lean_ctor_get(x_43, 0);
lean_dec(x_185);
x_186 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_186, 0, x_43);
x_187 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_187, 0, x_186);
lean_ctor_set(x_187, 1, x_11);
x_20 = x_187;
goto block_36;
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; 
lean_dec(x_43);
x_188 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_188, 0, x_45);
lean_ctor_set(x_188, 1, x_46);
x_189 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_189, 0, x_188);
x_190 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_190, 0, x_189);
lean_ctor_set(x_190, 1, x_11);
x_20 = x_190;
goto block_36;
}
}
}
}
block_19:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = 1;
x_17 = x_5 + x_16;
x_5 = x_17;
x_6 = x_15;
x_11 = x_14;
goto _start;
}
block_36:
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_2);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_2);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set(x_22, 0, x_25);
x_12 = x_20;
goto block_19;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_22, 0);
lean_inc(x_26);
lean_dec(x_22);
lean_inc(x_2);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_2);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_20, 0, x_28);
x_12 = x_20;
goto block_19;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_29 = lean_ctor_get(x_20, 0);
x_30 = lean_ctor_get(x_20, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_20);
x_31 = lean_ctor_get(x_29, 0);
lean_inc(x_31);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 x_32 = x_29;
} else {
 lean_dec_ref(x_29);
 x_32 = lean_box(0);
}
lean_inc(x_2);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_2);
lean_ctor_set(x_33, 1, x_31);
if (lean_is_scalar(x_32)) {
 x_34 = lean_alloc_ctor(1, 1, 0);
} else {
 x_34 = x_32;
}
lean_ctor_set(x_34, 0, x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_30);
x_12 = x_35;
goto block_19;
}
}
}
}
lean_object* l_Std_PersistentArray_forIn___at_Lean_Meta_getFVarSetToGeneralize___spec__43___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
lean_object* l_Std_PersistentArray_forIn___at_Lean_Meta_getFVarSetToGeneralize___spec__43(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_10 = l_Std_PersistentArray_forInAux___at_Lean_Meta_getFVarSetToGeneralize___spec__44(x_1, x_3, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_10, 0);
lean_dec(x_13);
x_14 = lean_ctor_get(x_11, 0);
lean_inc(x_14);
lean_dec(x_11);
lean_ctor_set(x_10, 0, x_14);
return x_10;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_dec(x_10);
x_16 = lean_ctor_get(x_11, 0);
lean_inc(x_16);
lean_dec(x_11);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; size_t x_24; size_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_18 = lean_ctor_get(x_10, 1);
lean_inc(x_18);
lean_dec(x_10);
x_19 = lean_ctor_get(x_11, 0);
lean_inc(x_19);
lean_dec(x_11);
x_20 = lean_ctor_get(x_2, 1);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_19);
x_23 = lean_array_get_size(x_20);
x_24 = lean_usize_of_nat(x_23);
lean_dec(x_23);
x_25 = 0;
x_26 = l_Array_forInUnsafe_loop___at_Lean_Meta_getFVarSetToGeneralize___spec__47(x_1, x_21, x_20, x_24, x_25, x_22, x_4, x_5, x_6, x_7, x_18);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_26);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_26, 0);
lean_dec(x_30);
x_31 = lean_ctor_get(x_27, 1);
lean_inc(x_31);
lean_dec(x_27);
lean_ctor_set(x_26, 0, x_31);
return x_26;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_26, 1);
lean_inc(x_32);
lean_dec(x_26);
x_33 = lean_ctor_get(x_27, 1);
lean_inc(x_33);
lean_dec(x_27);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
}
else
{
uint8_t x_35; 
lean_dec(x_27);
x_35 = !lean_is_exclusive(x_26);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_26, 0);
lean_dec(x_36);
x_37 = lean_ctor_get(x_28, 0);
lean_inc(x_37);
lean_dec(x_28);
lean_ctor_set(x_26, 0, x_37);
return x_26;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_26, 1);
lean_inc(x_38);
lean_dec(x_26);
x_39 = lean_ctor_get(x_28, 0);
lean_inc(x_39);
lean_dec(x_28);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
return x_40;
}
}
}
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_getFVarSetToGeneralize___spec__50(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = x_6 < x_5;
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_3);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_array_uget(x_4, x_6);
x_16 = lean_ctor_get(x_7, 1);
lean_inc(x_16);
lean_dec(x_7);
x_17 = l_Std_PersistentArray_forInAux___at_Lean_Meta_getFVarSetToGeneralize___spec__49(x_1, x_2, x_15, x_16, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_15);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
lean_dec(x_3);
x_19 = !lean_is_exclusive(x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_17, 0);
lean_dec(x_20);
x_21 = lean_ctor_get(x_18, 0);
lean_inc(x_21);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_18);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
lean_ctor_set(x_17, 0, x_23);
return x_17;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_17, 1);
lean_inc(x_24);
lean_dec(x_17);
x_25 = lean_ctor_get(x_18, 0);
lean_inc(x_25);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_18);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_24);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; size_t x_32; size_t x_33; 
x_29 = lean_ctor_get(x_17, 1);
lean_inc(x_29);
lean_dec(x_17);
x_30 = lean_ctor_get(x_18, 0);
lean_inc(x_30);
lean_dec(x_18);
lean_inc(x_3);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_3);
lean_ctor_set(x_31, 1, x_30);
x_32 = 1;
x_33 = x_6 + x_32;
x_6 = x_33;
x_7 = x_31;
x_12 = x_29;
goto _start;
}
}
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_getFVarSetToGeneralize___spec__51(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_20; uint8_t x_37; 
x_37 = x_5 < x_4;
if (x_37 == 0)
{
lean_object* x_38; 
lean_dec(x_2);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_6);
lean_ctor_set(x_38, 1, x_11);
return x_38;
}
else
{
lean_object* x_39; 
x_39 = lean_array_uget(x_3, x_5);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_6, 1);
lean_inc(x_40);
lean_dec(x_6);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_11);
x_20 = x_42;
goto block_36;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_43 = lean_ctor_get(x_6, 1);
lean_inc(x_43);
lean_dec(x_6);
x_44 = lean_ctor_get(x_39, 0);
lean_inc(x_44);
lean_dec(x_39);
x_45 = lean_ctor_get(x_43, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
x_47 = l_Lean_LocalDecl_fvarId(x_44);
x_48 = l_Lean_NameSet_contains(x_1, x_47);
if (x_48 == 0)
{
uint8_t x_49; 
x_49 = l_Lean_LocalDecl_isAuxDecl(x_44);
if (x_49 == 0)
{
uint8_t x_50; uint8_t x_51; 
x_50 = l_Lean_LocalDecl_binderInfo(x_44);
x_51 = l_Lean_BinderInfo_isInstImplicit(x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_52 = lean_st_ref_get(x_10, x_11);
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
x_55 = lean_st_ref_get(x_8, x_53);
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
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_67 = lean_ctor_get(x_56, 0);
lean_inc(x_67);
lean_dec(x_56);
x_68 = lean_ctor_get(x_44, 3);
lean_inc(x_68);
lean_dec(x_44);
x_69 = l_Lean_Expr_hasFVar(x_68);
if (x_69 == 0)
{
uint8_t x_70; 
x_70 = l_Lean_Expr_hasMVar(x_68);
if (x_70 == 0)
{
uint8_t x_71; 
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_58);
lean_dec(x_47);
x_71 = !lean_is_exclusive(x_43);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_72 = lean_ctor_get(x_43, 1);
lean_dec(x_72);
x_73 = lean_ctor_get(x_43, 0);
lean_dec(x_73);
x_74 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_74, 0, x_43);
if (lean_is_scalar(x_54)) {
 x_75 = lean_alloc_ctor(0, 2, 0);
} else {
 x_75 = x_54;
}
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_57);
x_20 = x_75;
goto block_36;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_43);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_45);
lean_ctor_set(x_76, 1, x_46);
x_77 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_77, 0, x_76);
if (lean_is_scalar(x_54)) {
 x_78 = lean_alloc_ctor(0, 2, 0);
} else {
 x_78 = x_54;
}
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_57);
x_20 = x_78;
goto block_36;
}
}
else
{
lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_79 = l_Std_HashSet_instInhabitedHashSet___closed__1;
x_80 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__1(x_43, x_67, x_68, x_79);
x_81 = !lean_is_exclusive(x_43);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_82 = lean_ctor_get(x_43, 1);
lean_dec(x_82);
x_83 = lean_ctor_get(x_43, 0);
lean_dec(x_83);
x_84 = lean_ctor_get(x_80, 0);
lean_inc(x_84);
lean_dec(x_80);
x_85 = lean_unbox(x_84);
lean_dec(x_84);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; 
lean_dec(x_58);
lean_dec(x_47);
x_86 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_86, 0, x_43);
if (lean_is_scalar(x_54)) {
 x_87 = lean_alloc_ctor(0, 2, 0);
} else {
 x_87 = x_54;
}
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_57);
x_20 = x_87;
goto block_36;
}
else
{
lean_object* x_88; 
lean_free_object(x_43);
lean_dec(x_54);
x_88 = lean_box(0);
x_59 = x_88;
goto block_66;
}
}
else
{
lean_object* x_89; uint8_t x_90; 
lean_dec(x_43);
x_89 = lean_ctor_get(x_80, 0);
lean_inc(x_89);
lean_dec(x_80);
x_90 = lean_unbox(x_89);
lean_dec(x_89);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec(x_58);
lean_dec(x_47);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_45);
lean_ctor_set(x_91, 1, x_46);
x_92 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_92, 0, x_91);
if (lean_is_scalar(x_54)) {
 x_93 = lean_alloc_ctor(0, 2, 0);
} else {
 x_93 = x_54;
}
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_57);
x_20 = x_93;
goto block_36;
}
else
{
lean_object* x_94; 
lean_dec(x_54);
x_94 = lean_box(0);
x_59 = x_94;
goto block_66;
}
}
}
}
else
{
lean_object* x_95; lean_object* x_96; uint8_t x_97; 
x_95 = l_Std_HashSet_instInhabitedHashSet___closed__1;
x_96 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__8(x_43, x_67, x_68, x_95);
x_97 = !lean_is_exclusive(x_43);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; 
x_98 = lean_ctor_get(x_43, 1);
lean_dec(x_98);
x_99 = lean_ctor_get(x_43, 0);
lean_dec(x_99);
x_100 = lean_ctor_get(x_96, 0);
lean_inc(x_100);
lean_dec(x_96);
x_101 = lean_unbox(x_100);
lean_dec(x_100);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; 
lean_dec(x_58);
lean_dec(x_47);
x_102 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_102, 0, x_43);
if (lean_is_scalar(x_54)) {
 x_103 = lean_alloc_ctor(0, 2, 0);
} else {
 x_103 = x_54;
}
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_57);
x_20 = x_103;
goto block_36;
}
else
{
lean_object* x_104; 
lean_free_object(x_43);
lean_dec(x_54);
x_104 = lean_box(0);
x_59 = x_104;
goto block_66;
}
}
else
{
lean_object* x_105; uint8_t x_106; 
lean_dec(x_43);
x_105 = lean_ctor_get(x_96, 0);
lean_inc(x_105);
lean_dec(x_96);
x_106 = lean_unbox(x_105);
lean_dec(x_105);
if (x_106 == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
lean_dec(x_58);
lean_dec(x_47);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_45);
lean_ctor_set(x_107, 1, x_46);
x_108 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_108, 0, x_107);
if (lean_is_scalar(x_54)) {
 x_109 = lean_alloc_ctor(0, 2, 0);
} else {
 x_109 = x_54;
}
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_57);
x_20 = x_109;
goto block_36;
}
else
{
lean_object* x_110; 
lean_dec(x_54);
x_110 = lean_box(0);
x_59 = x_110;
goto block_66;
}
}
}
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_160; 
x_111 = lean_ctor_get(x_56, 0);
lean_inc(x_111);
lean_dec(x_56);
x_112 = lean_ctor_get(x_44, 3);
lean_inc(x_112);
x_113 = lean_ctor_get(x_44, 4);
lean_inc(x_113);
lean_dec(x_44);
x_160 = l_Lean_Expr_hasFVar(x_112);
if (x_160 == 0)
{
uint8_t x_161; 
x_161 = l_Lean_Expr_hasMVar(x_112);
if (x_161 == 0)
{
lean_object* x_162; 
lean_dec(x_112);
x_162 = l_Lean_MetavarContext_findLocalDeclDependsOn___closed__1;
x_114 = x_162;
goto block_159;
}
else
{
lean_object* x_163; lean_object* x_164; 
x_163 = l_Std_HashSet_instInhabitedHashSet___closed__1;
lean_inc(x_111);
x_164 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__29(x_43, x_111, x_112, x_163);
x_114 = x_164;
goto block_159;
}
}
else
{
lean_object* x_165; lean_object* x_166; 
x_165 = l_Std_HashSet_instInhabitedHashSet___closed__1;
lean_inc(x_111);
x_166 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__36(x_43, x_111, x_112, x_165);
x_114 = x_166;
goto block_159;
}
block_159:
{
lean_object* x_115; uint8_t x_116; 
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
x_116 = lean_unbox(x_115);
lean_dec(x_115);
if (x_116 == 0)
{
lean_object* x_117; uint8_t x_118; 
x_117 = lean_ctor_get(x_114, 1);
lean_inc(x_117);
lean_dec(x_114);
x_118 = l_Lean_Expr_hasFVar(x_113);
if (x_118 == 0)
{
uint8_t x_119; 
x_119 = l_Lean_Expr_hasMVar(x_113);
if (x_119 == 0)
{
uint8_t x_120; 
lean_dec(x_117);
lean_dec(x_113);
lean_dec(x_111);
lean_dec(x_58);
lean_dec(x_47);
x_120 = !lean_is_exclusive(x_43);
if (x_120 == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_121 = lean_ctor_get(x_43, 1);
lean_dec(x_121);
x_122 = lean_ctor_get(x_43, 0);
lean_dec(x_122);
x_123 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_123, 0, x_43);
if (lean_is_scalar(x_54)) {
 x_124 = lean_alloc_ctor(0, 2, 0);
} else {
 x_124 = x_54;
}
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_57);
x_20 = x_124;
goto block_36;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
lean_dec(x_43);
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_45);
lean_ctor_set(x_125, 1, x_46);
x_126 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_126, 0, x_125);
if (lean_is_scalar(x_54)) {
 x_127 = lean_alloc_ctor(0, 2, 0);
} else {
 x_127 = x_54;
}
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_127, 1, x_57);
x_20 = x_127;
goto block_36;
}
}
else
{
lean_object* x_128; uint8_t x_129; 
x_128 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__15(x_43, x_111, x_113, x_117);
x_129 = !lean_is_exclusive(x_43);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_133; 
x_130 = lean_ctor_get(x_43, 1);
lean_dec(x_130);
x_131 = lean_ctor_get(x_43, 0);
lean_dec(x_131);
x_132 = lean_ctor_get(x_128, 0);
lean_inc(x_132);
lean_dec(x_128);
x_133 = lean_unbox(x_132);
lean_dec(x_132);
if (x_133 == 0)
{
lean_object* x_134; lean_object* x_135; 
lean_dec(x_58);
lean_dec(x_47);
x_134 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_134, 0, x_43);
if (lean_is_scalar(x_54)) {
 x_135 = lean_alloc_ctor(0, 2, 0);
} else {
 x_135 = x_54;
}
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_57);
x_20 = x_135;
goto block_36;
}
else
{
lean_object* x_136; 
lean_free_object(x_43);
lean_dec(x_54);
x_136 = lean_box(0);
x_59 = x_136;
goto block_66;
}
}
else
{
lean_object* x_137; uint8_t x_138; 
lean_dec(x_43);
x_137 = lean_ctor_get(x_128, 0);
lean_inc(x_137);
lean_dec(x_128);
x_138 = lean_unbox(x_137);
lean_dec(x_137);
if (x_138 == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
lean_dec(x_58);
lean_dec(x_47);
x_139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_139, 0, x_45);
lean_ctor_set(x_139, 1, x_46);
x_140 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_140, 0, x_139);
if (lean_is_scalar(x_54)) {
 x_141 = lean_alloc_ctor(0, 2, 0);
} else {
 x_141 = x_54;
}
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_57);
x_20 = x_141;
goto block_36;
}
else
{
lean_object* x_142; 
lean_dec(x_54);
x_142 = lean_box(0);
x_59 = x_142;
goto block_66;
}
}
}
}
else
{
lean_object* x_143; uint8_t x_144; 
x_143 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__22(x_43, x_111, x_113, x_117);
x_144 = !lean_is_exclusive(x_43);
if (x_144 == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; uint8_t x_148; 
x_145 = lean_ctor_get(x_43, 1);
lean_dec(x_145);
x_146 = lean_ctor_get(x_43, 0);
lean_dec(x_146);
x_147 = lean_ctor_get(x_143, 0);
lean_inc(x_147);
lean_dec(x_143);
x_148 = lean_unbox(x_147);
lean_dec(x_147);
if (x_148 == 0)
{
lean_object* x_149; lean_object* x_150; 
lean_dec(x_58);
lean_dec(x_47);
x_149 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_149, 0, x_43);
if (lean_is_scalar(x_54)) {
 x_150 = lean_alloc_ctor(0, 2, 0);
} else {
 x_150 = x_54;
}
lean_ctor_set(x_150, 0, x_149);
lean_ctor_set(x_150, 1, x_57);
x_20 = x_150;
goto block_36;
}
else
{
lean_object* x_151; 
lean_free_object(x_43);
lean_dec(x_54);
x_151 = lean_box(0);
x_59 = x_151;
goto block_66;
}
}
else
{
lean_object* x_152; uint8_t x_153; 
lean_dec(x_43);
x_152 = lean_ctor_get(x_143, 0);
lean_inc(x_152);
lean_dec(x_143);
x_153 = lean_unbox(x_152);
lean_dec(x_152);
if (x_153 == 0)
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; 
lean_dec(x_58);
lean_dec(x_47);
x_154 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_154, 0, x_45);
lean_ctor_set(x_154, 1, x_46);
x_155 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_155, 0, x_154);
if (lean_is_scalar(x_54)) {
 x_156 = lean_alloc_ctor(0, 2, 0);
} else {
 x_156 = x_54;
}
lean_ctor_set(x_156, 0, x_155);
lean_ctor_set(x_156, 1, x_57);
x_20 = x_156;
goto block_36;
}
else
{
lean_object* x_157; 
lean_dec(x_54);
x_157 = lean_box(0);
x_59 = x_157;
goto block_66;
}
}
}
}
else
{
lean_object* x_158; 
lean_dec(x_114);
lean_dec(x_113);
lean_dec(x_111);
lean_dec(x_54);
lean_dec(x_43);
x_158 = lean_box(0);
x_59 = x_158;
goto block_66;
}
}
}
block_66:
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_59);
x_60 = lean_box(0);
lean_inc(x_47);
x_61 = l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_46, x_47, x_60);
x_62 = l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_45, x_47, x_60);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_61);
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_63);
if (lean_is_scalar(x_58)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_58;
}
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_57);
x_20 = x_65;
goto block_36;
}
}
else
{
uint8_t x_167; 
lean_dec(x_47);
lean_dec(x_44);
x_167 = !lean_is_exclusive(x_43);
if (x_167 == 0)
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_168 = lean_ctor_get(x_43, 1);
lean_dec(x_168);
x_169 = lean_ctor_get(x_43, 0);
lean_dec(x_169);
x_170 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_170, 0, x_43);
x_171 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_171, 1, x_11);
x_20 = x_171;
goto block_36;
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; 
lean_dec(x_43);
x_172 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_172, 0, x_45);
lean_ctor_set(x_172, 1, x_46);
x_173 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_173, 0, x_172);
x_174 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_174, 0, x_173);
lean_ctor_set(x_174, 1, x_11);
x_20 = x_174;
goto block_36;
}
}
}
else
{
uint8_t x_175; 
lean_dec(x_47);
lean_dec(x_44);
x_175 = !lean_is_exclusive(x_43);
if (x_175 == 0)
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_176 = lean_ctor_get(x_43, 1);
lean_dec(x_176);
x_177 = lean_ctor_get(x_43, 0);
lean_dec(x_177);
x_178 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_178, 0, x_43);
x_179 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_179, 0, x_178);
lean_ctor_set(x_179, 1, x_11);
x_20 = x_179;
goto block_36;
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; 
lean_dec(x_43);
x_180 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_180, 0, x_45);
lean_ctor_set(x_180, 1, x_46);
x_181 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_181, 0, x_180);
x_182 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_182, 0, x_181);
lean_ctor_set(x_182, 1, x_11);
x_20 = x_182;
goto block_36;
}
}
}
else
{
uint8_t x_183; 
lean_dec(x_47);
lean_dec(x_44);
x_183 = !lean_is_exclusive(x_43);
if (x_183 == 0)
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_184 = lean_ctor_get(x_43, 1);
lean_dec(x_184);
x_185 = lean_ctor_get(x_43, 0);
lean_dec(x_185);
x_186 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_186, 0, x_43);
x_187 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_187, 0, x_186);
lean_ctor_set(x_187, 1, x_11);
x_20 = x_187;
goto block_36;
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; 
lean_dec(x_43);
x_188 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_188, 0, x_45);
lean_ctor_set(x_188, 1, x_46);
x_189 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_189, 0, x_188);
x_190 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_190, 0, x_189);
lean_ctor_set(x_190, 1, x_11);
x_20 = x_190;
goto block_36;
}
}
}
}
block_19:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = 1;
x_17 = x_5 + x_16;
x_5 = x_17;
x_6 = x_15;
x_11 = x_14;
goto _start;
}
block_36:
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_2);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_2);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set(x_22, 0, x_25);
x_12 = x_20;
goto block_19;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_22, 0);
lean_inc(x_26);
lean_dec(x_22);
lean_inc(x_2);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_2);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_20, 0, x_28);
x_12 = x_20;
goto block_19;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_29 = lean_ctor_get(x_20, 0);
x_30 = lean_ctor_get(x_20, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_20);
x_31 = lean_ctor_get(x_29, 0);
lean_inc(x_31);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 x_32 = x_29;
} else {
 lean_dec_ref(x_29);
 x_32 = lean_box(0);
}
lean_inc(x_2);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_2);
lean_ctor_set(x_33, 1, x_31);
if (lean_is_scalar(x_32)) {
 x_34 = lean_alloc_ctor(1, 1, 0);
} else {
 x_34 = x_32;
}
lean_ctor_set(x_34, 0, x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_30);
x_12 = x_35;
goto block_19;
}
}
}
}
lean_object* l_Std_PersistentArray_forInAux___at_Lean_Meta_getFVarSetToGeneralize___spec__49(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_4);
x_13 = lean_array_get_size(x_10);
x_14 = lean_usize_of_nat(x_13);
lean_dec(x_13);
x_15 = 0;
x_16 = l_Array_forInUnsafe_loop___at_Lean_Meta_getFVarSetToGeneralize___spec__50(x_1, x_2, x_11, x_10, x_14, x_15, x_12, x_5, x_6, x_7, x_8, x_9);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_box(0);
x_22 = l_Std_PersistentArray_forInAux___at_Lean_Meta_getFVarSetToGeneralize___spec__44___lambda__1(x_20, x_21, x_5, x_6, x_7, x_8, x_19);
return x_22;
}
else
{
uint8_t x_23; 
lean_dec(x_17);
x_23 = !lean_is_exclusive(x_16);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_16, 0);
lean_dec(x_24);
x_25 = lean_ctor_get(x_18, 0);
lean_inc(x_25);
lean_dec(x_18);
lean_ctor_set(x_16, 0, x_25);
return x_16;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_16, 1);
lean_inc(x_26);
lean_dec(x_16);
x_27 = lean_ctor_get(x_18, 0);
lean_inc(x_27);
lean_dec(x_18);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; size_t x_33; size_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_29 = lean_ctor_get(x_3, 0);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_4);
x_32 = lean_array_get_size(x_29);
x_33 = lean_usize_of_nat(x_32);
lean_dec(x_32);
x_34 = 0;
x_35 = l_Array_forInUnsafe_loop___at_Lean_Meta_getFVarSetToGeneralize___spec__51(x_1, x_30, x_29, x_33, x_34, x_31, x_5, x_6, x_7, x_8, x_9);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_dec(x_35);
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_dec(x_36);
x_40 = lean_box(0);
x_41 = l_Std_PersistentArray_forInAux___at_Lean_Meta_getFVarSetToGeneralize___spec__44___lambda__1(x_39, x_40, x_5, x_6, x_7, x_8, x_38);
return x_41;
}
else
{
uint8_t x_42; 
lean_dec(x_36);
x_42 = !lean_is_exclusive(x_35);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_35, 0);
lean_dec(x_43);
x_44 = lean_ctor_get(x_37, 0);
lean_inc(x_44);
lean_dec(x_37);
lean_ctor_set(x_35, 0, x_44);
return x_35;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_35, 1);
lean_inc(x_45);
lean_dec(x_35);
x_46 = lean_ctor_get(x_37, 0);
lean_inc(x_46);
lean_dec(x_37);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
return x_47;
}
}
}
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_getFVarSetToGeneralize___spec__52(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_20; uint8_t x_37; 
x_37 = x_5 < x_4;
if (x_37 == 0)
{
lean_object* x_38; 
lean_dec(x_2);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_6);
lean_ctor_set(x_38, 1, x_11);
return x_38;
}
else
{
lean_object* x_39; 
x_39 = lean_array_uget(x_3, x_5);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_6, 1);
lean_inc(x_40);
lean_dec(x_6);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_11);
x_20 = x_42;
goto block_36;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_43 = lean_ctor_get(x_6, 1);
lean_inc(x_43);
lean_dec(x_6);
x_44 = lean_ctor_get(x_39, 0);
lean_inc(x_44);
lean_dec(x_39);
x_45 = lean_ctor_get(x_43, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
x_47 = l_Lean_LocalDecl_fvarId(x_44);
x_48 = l_Lean_NameSet_contains(x_1, x_47);
if (x_48 == 0)
{
uint8_t x_49; 
x_49 = l_Lean_LocalDecl_isAuxDecl(x_44);
if (x_49 == 0)
{
uint8_t x_50; uint8_t x_51; 
x_50 = l_Lean_LocalDecl_binderInfo(x_44);
x_51 = l_Lean_BinderInfo_isInstImplicit(x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_52 = lean_st_ref_get(x_10, x_11);
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
x_55 = lean_st_ref_get(x_8, x_53);
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
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_67 = lean_ctor_get(x_56, 0);
lean_inc(x_67);
lean_dec(x_56);
x_68 = lean_ctor_get(x_44, 3);
lean_inc(x_68);
lean_dec(x_44);
x_69 = l_Lean_Expr_hasFVar(x_68);
if (x_69 == 0)
{
uint8_t x_70; 
x_70 = l_Lean_Expr_hasMVar(x_68);
if (x_70 == 0)
{
uint8_t x_71; 
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_58);
lean_dec(x_47);
x_71 = !lean_is_exclusive(x_43);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_72 = lean_ctor_get(x_43, 1);
lean_dec(x_72);
x_73 = lean_ctor_get(x_43, 0);
lean_dec(x_73);
x_74 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_74, 0, x_43);
if (lean_is_scalar(x_54)) {
 x_75 = lean_alloc_ctor(0, 2, 0);
} else {
 x_75 = x_54;
}
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_57);
x_20 = x_75;
goto block_36;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_43);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_45);
lean_ctor_set(x_76, 1, x_46);
x_77 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_77, 0, x_76);
if (lean_is_scalar(x_54)) {
 x_78 = lean_alloc_ctor(0, 2, 0);
} else {
 x_78 = x_54;
}
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_57);
x_20 = x_78;
goto block_36;
}
}
else
{
lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_79 = l_Std_HashSet_instInhabitedHashSet___closed__1;
x_80 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__1(x_43, x_67, x_68, x_79);
x_81 = !lean_is_exclusive(x_43);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_82 = lean_ctor_get(x_43, 1);
lean_dec(x_82);
x_83 = lean_ctor_get(x_43, 0);
lean_dec(x_83);
x_84 = lean_ctor_get(x_80, 0);
lean_inc(x_84);
lean_dec(x_80);
x_85 = lean_unbox(x_84);
lean_dec(x_84);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; 
lean_dec(x_58);
lean_dec(x_47);
x_86 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_86, 0, x_43);
if (lean_is_scalar(x_54)) {
 x_87 = lean_alloc_ctor(0, 2, 0);
} else {
 x_87 = x_54;
}
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_57);
x_20 = x_87;
goto block_36;
}
else
{
lean_object* x_88; 
lean_free_object(x_43);
lean_dec(x_54);
x_88 = lean_box(0);
x_59 = x_88;
goto block_66;
}
}
else
{
lean_object* x_89; uint8_t x_90; 
lean_dec(x_43);
x_89 = lean_ctor_get(x_80, 0);
lean_inc(x_89);
lean_dec(x_80);
x_90 = lean_unbox(x_89);
lean_dec(x_89);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec(x_58);
lean_dec(x_47);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_45);
lean_ctor_set(x_91, 1, x_46);
x_92 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_92, 0, x_91);
if (lean_is_scalar(x_54)) {
 x_93 = lean_alloc_ctor(0, 2, 0);
} else {
 x_93 = x_54;
}
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_57);
x_20 = x_93;
goto block_36;
}
else
{
lean_object* x_94; 
lean_dec(x_54);
x_94 = lean_box(0);
x_59 = x_94;
goto block_66;
}
}
}
}
else
{
lean_object* x_95; lean_object* x_96; uint8_t x_97; 
x_95 = l_Std_HashSet_instInhabitedHashSet___closed__1;
x_96 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__8(x_43, x_67, x_68, x_95);
x_97 = !lean_is_exclusive(x_43);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; 
x_98 = lean_ctor_get(x_43, 1);
lean_dec(x_98);
x_99 = lean_ctor_get(x_43, 0);
lean_dec(x_99);
x_100 = lean_ctor_get(x_96, 0);
lean_inc(x_100);
lean_dec(x_96);
x_101 = lean_unbox(x_100);
lean_dec(x_100);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; 
lean_dec(x_58);
lean_dec(x_47);
x_102 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_102, 0, x_43);
if (lean_is_scalar(x_54)) {
 x_103 = lean_alloc_ctor(0, 2, 0);
} else {
 x_103 = x_54;
}
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_57);
x_20 = x_103;
goto block_36;
}
else
{
lean_object* x_104; 
lean_free_object(x_43);
lean_dec(x_54);
x_104 = lean_box(0);
x_59 = x_104;
goto block_66;
}
}
else
{
lean_object* x_105; uint8_t x_106; 
lean_dec(x_43);
x_105 = lean_ctor_get(x_96, 0);
lean_inc(x_105);
lean_dec(x_96);
x_106 = lean_unbox(x_105);
lean_dec(x_105);
if (x_106 == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
lean_dec(x_58);
lean_dec(x_47);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_45);
lean_ctor_set(x_107, 1, x_46);
x_108 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_108, 0, x_107);
if (lean_is_scalar(x_54)) {
 x_109 = lean_alloc_ctor(0, 2, 0);
} else {
 x_109 = x_54;
}
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_57);
x_20 = x_109;
goto block_36;
}
else
{
lean_object* x_110; 
lean_dec(x_54);
x_110 = lean_box(0);
x_59 = x_110;
goto block_66;
}
}
}
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_160; 
x_111 = lean_ctor_get(x_56, 0);
lean_inc(x_111);
lean_dec(x_56);
x_112 = lean_ctor_get(x_44, 3);
lean_inc(x_112);
x_113 = lean_ctor_get(x_44, 4);
lean_inc(x_113);
lean_dec(x_44);
x_160 = l_Lean_Expr_hasFVar(x_112);
if (x_160 == 0)
{
uint8_t x_161; 
x_161 = l_Lean_Expr_hasMVar(x_112);
if (x_161 == 0)
{
lean_object* x_162; 
lean_dec(x_112);
x_162 = l_Lean_MetavarContext_findLocalDeclDependsOn___closed__1;
x_114 = x_162;
goto block_159;
}
else
{
lean_object* x_163; lean_object* x_164; 
x_163 = l_Std_HashSet_instInhabitedHashSet___closed__1;
lean_inc(x_111);
x_164 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__29(x_43, x_111, x_112, x_163);
x_114 = x_164;
goto block_159;
}
}
else
{
lean_object* x_165; lean_object* x_166; 
x_165 = l_Std_HashSet_instInhabitedHashSet___closed__1;
lean_inc(x_111);
x_166 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__36(x_43, x_111, x_112, x_165);
x_114 = x_166;
goto block_159;
}
block_159:
{
lean_object* x_115; uint8_t x_116; 
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
x_116 = lean_unbox(x_115);
lean_dec(x_115);
if (x_116 == 0)
{
lean_object* x_117; uint8_t x_118; 
x_117 = lean_ctor_get(x_114, 1);
lean_inc(x_117);
lean_dec(x_114);
x_118 = l_Lean_Expr_hasFVar(x_113);
if (x_118 == 0)
{
uint8_t x_119; 
x_119 = l_Lean_Expr_hasMVar(x_113);
if (x_119 == 0)
{
uint8_t x_120; 
lean_dec(x_117);
lean_dec(x_113);
lean_dec(x_111);
lean_dec(x_58);
lean_dec(x_47);
x_120 = !lean_is_exclusive(x_43);
if (x_120 == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_121 = lean_ctor_get(x_43, 1);
lean_dec(x_121);
x_122 = lean_ctor_get(x_43, 0);
lean_dec(x_122);
x_123 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_123, 0, x_43);
if (lean_is_scalar(x_54)) {
 x_124 = lean_alloc_ctor(0, 2, 0);
} else {
 x_124 = x_54;
}
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_57);
x_20 = x_124;
goto block_36;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
lean_dec(x_43);
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_45);
lean_ctor_set(x_125, 1, x_46);
x_126 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_126, 0, x_125);
if (lean_is_scalar(x_54)) {
 x_127 = lean_alloc_ctor(0, 2, 0);
} else {
 x_127 = x_54;
}
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_127, 1, x_57);
x_20 = x_127;
goto block_36;
}
}
else
{
lean_object* x_128; uint8_t x_129; 
x_128 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__15(x_43, x_111, x_113, x_117);
x_129 = !lean_is_exclusive(x_43);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_133; 
x_130 = lean_ctor_get(x_43, 1);
lean_dec(x_130);
x_131 = lean_ctor_get(x_43, 0);
lean_dec(x_131);
x_132 = lean_ctor_get(x_128, 0);
lean_inc(x_132);
lean_dec(x_128);
x_133 = lean_unbox(x_132);
lean_dec(x_132);
if (x_133 == 0)
{
lean_object* x_134; lean_object* x_135; 
lean_dec(x_58);
lean_dec(x_47);
x_134 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_134, 0, x_43);
if (lean_is_scalar(x_54)) {
 x_135 = lean_alloc_ctor(0, 2, 0);
} else {
 x_135 = x_54;
}
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_57);
x_20 = x_135;
goto block_36;
}
else
{
lean_object* x_136; 
lean_free_object(x_43);
lean_dec(x_54);
x_136 = lean_box(0);
x_59 = x_136;
goto block_66;
}
}
else
{
lean_object* x_137; uint8_t x_138; 
lean_dec(x_43);
x_137 = lean_ctor_get(x_128, 0);
lean_inc(x_137);
lean_dec(x_128);
x_138 = lean_unbox(x_137);
lean_dec(x_137);
if (x_138 == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
lean_dec(x_58);
lean_dec(x_47);
x_139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_139, 0, x_45);
lean_ctor_set(x_139, 1, x_46);
x_140 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_140, 0, x_139);
if (lean_is_scalar(x_54)) {
 x_141 = lean_alloc_ctor(0, 2, 0);
} else {
 x_141 = x_54;
}
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_57);
x_20 = x_141;
goto block_36;
}
else
{
lean_object* x_142; 
lean_dec(x_54);
x_142 = lean_box(0);
x_59 = x_142;
goto block_66;
}
}
}
}
else
{
lean_object* x_143; uint8_t x_144; 
x_143 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__22(x_43, x_111, x_113, x_117);
x_144 = !lean_is_exclusive(x_43);
if (x_144 == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; uint8_t x_148; 
x_145 = lean_ctor_get(x_43, 1);
lean_dec(x_145);
x_146 = lean_ctor_get(x_43, 0);
lean_dec(x_146);
x_147 = lean_ctor_get(x_143, 0);
lean_inc(x_147);
lean_dec(x_143);
x_148 = lean_unbox(x_147);
lean_dec(x_147);
if (x_148 == 0)
{
lean_object* x_149; lean_object* x_150; 
lean_dec(x_58);
lean_dec(x_47);
x_149 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_149, 0, x_43);
if (lean_is_scalar(x_54)) {
 x_150 = lean_alloc_ctor(0, 2, 0);
} else {
 x_150 = x_54;
}
lean_ctor_set(x_150, 0, x_149);
lean_ctor_set(x_150, 1, x_57);
x_20 = x_150;
goto block_36;
}
else
{
lean_object* x_151; 
lean_free_object(x_43);
lean_dec(x_54);
x_151 = lean_box(0);
x_59 = x_151;
goto block_66;
}
}
else
{
lean_object* x_152; uint8_t x_153; 
lean_dec(x_43);
x_152 = lean_ctor_get(x_143, 0);
lean_inc(x_152);
lean_dec(x_143);
x_153 = lean_unbox(x_152);
lean_dec(x_152);
if (x_153 == 0)
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; 
lean_dec(x_58);
lean_dec(x_47);
x_154 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_154, 0, x_45);
lean_ctor_set(x_154, 1, x_46);
x_155 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_155, 0, x_154);
if (lean_is_scalar(x_54)) {
 x_156 = lean_alloc_ctor(0, 2, 0);
} else {
 x_156 = x_54;
}
lean_ctor_set(x_156, 0, x_155);
lean_ctor_set(x_156, 1, x_57);
x_20 = x_156;
goto block_36;
}
else
{
lean_object* x_157; 
lean_dec(x_54);
x_157 = lean_box(0);
x_59 = x_157;
goto block_66;
}
}
}
}
else
{
lean_object* x_158; 
lean_dec(x_114);
lean_dec(x_113);
lean_dec(x_111);
lean_dec(x_54);
lean_dec(x_43);
x_158 = lean_box(0);
x_59 = x_158;
goto block_66;
}
}
}
block_66:
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_59);
x_60 = lean_box(0);
lean_inc(x_47);
x_61 = l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_46, x_47, x_60);
x_62 = l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_45, x_47, x_60);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_61);
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_63);
if (lean_is_scalar(x_58)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_58;
}
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_57);
x_20 = x_65;
goto block_36;
}
}
else
{
uint8_t x_167; 
lean_dec(x_47);
lean_dec(x_44);
x_167 = !lean_is_exclusive(x_43);
if (x_167 == 0)
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_168 = lean_ctor_get(x_43, 1);
lean_dec(x_168);
x_169 = lean_ctor_get(x_43, 0);
lean_dec(x_169);
x_170 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_170, 0, x_43);
x_171 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_171, 1, x_11);
x_20 = x_171;
goto block_36;
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; 
lean_dec(x_43);
x_172 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_172, 0, x_45);
lean_ctor_set(x_172, 1, x_46);
x_173 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_173, 0, x_172);
x_174 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_174, 0, x_173);
lean_ctor_set(x_174, 1, x_11);
x_20 = x_174;
goto block_36;
}
}
}
else
{
uint8_t x_175; 
lean_dec(x_47);
lean_dec(x_44);
x_175 = !lean_is_exclusive(x_43);
if (x_175 == 0)
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_176 = lean_ctor_get(x_43, 1);
lean_dec(x_176);
x_177 = lean_ctor_get(x_43, 0);
lean_dec(x_177);
x_178 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_178, 0, x_43);
x_179 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_179, 0, x_178);
lean_ctor_set(x_179, 1, x_11);
x_20 = x_179;
goto block_36;
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; 
lean_dec(x_43);
x_180 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_180, 0, x_45);
lean_ctor_set(x_180, 1, x_46);
x_181 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_181, 0, x_180);
x_182 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_182, 0, x_181);
lean_ctor_set(x_182, 1, x_11);
x_20 = x_182;
goto block_36;
}
}
}
else
{
uint8_t x_183; 
lean_dec(x_47);
lean_dec(x_44);
x_183 = !lean_is_exclusive(x_43);
if (x_183 == 0)
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_184 = lean_ctor_get(x_43, 1);
lean_dec(x_184);
x_185 = lean_ctor_get(x_43, 0);
lean_dec(x_185);
x_186 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_186, 0, x_43);
x_187 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_187, 0, x_186);
lean_ctor_set(x_187, 1, x_11);
x_20 = x_187;
goto block_36;
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; 
lean_dec(x_43);
x_188 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_188, 0, x_45);
lean_ctor_set(x_188, 1, x_46);
x_189 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_189, 0, x_188);
x_190 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_190, 0, x_189);
lean_ctor_set(x_190, 1, x_11);
x_20 = x_190;
goto block_36;
}
}
}
}
block_19:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = 1;
x_17 = x_5 + x_16;
x_5 = x_17;
x_6 = x_15;
x_11 = x_14;
goto _start;
}
block_36:
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_2);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_2);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set(x_22, 0, x_25);
x_12 = x_20;
goto block_19;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_22, 0);
lean_inc(x_26);
lean_dec(x_22);
lean_inc(x_2);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_2);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_20, 0, x_28);
x_12 = x_20;
goto block_19;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_29 = lean_ctor_get(x_20, 0);
x_30 = lean_ctor_get(x_20, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_20);
x_31 = lean_ctor_get(x_29, 0);
lean_inc(x_31);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 x_32 = x_29;
} else {
 lean_dec_ref(x_29);
 x_32 = lean_box(0);
}
lean_inc(x_2);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_2);
lean_ctor_set(x_33, 1, x_31);
if (lean_is_scalar(x_32)) {
 x_34 = lean_alloc_ctor(1, 1, 0);
} else {
 x_34 = x_32;
}
lean_ctor_set(x_34, 0, x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_30);
x_12 = x_35;
goto block_19;
}
}
}
}
lean_object* l_Std_PersistentArray_forIn___at_Lean_Meta_getFVarSetToGeneralize___spec__48(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_10 = l_Std_PersistentArray_forInAux___at_Lean_Meta_getFVarSetToGeneralize___spec__49(x_1, x_3, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_10, 0);
lean_dec(x_13);
x_14 = lean_ctor_get(x_11, 0);
lean_inc(x_14);
lean_dec(x_11);
lean_ctor_set(x_10, 0, x_14);
return x_10;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_dec(x_10);
x_16 = lean_ctor_get(x_11, 0);
lean_inc(x_16);
lean_dec(x_11);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; size_t x_24; size_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_18 = lean_ctor_get(x_10, 1);
lean_inc(x_18);
lean_dec(x_10);
x_19 = lean_ctor_get(x_11, 0);
lean_inc(x_19);
lean_dec(x_11);
x_20 = lean_ctor_get(x_2, 1);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_19);
x_23 = lean_array_get_size(x_20);
x_24 = lean_usize_of_nat(x_23);
lean_dec(x_23);
x_25 = 0;
x_26 = l_Array_forInUnsafe_loop___at_Lean_Meta_getFVarSetToGeneralize___spec__52(x_1, x_21, x_20, x_24, x_25, x_22, x_4, x_5, x_6, x_7, x_18);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_26);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_26, 0);
lean_dec(x_30);
x_31 = lean_ctor_get(x_27, 1);
lean_inc(x_31);
lean_dec(x_27);
lean_ctor_set(x_26, 0, x_31);
return x_26;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_26, 1);
lean_inc(x_32);
lean_dec(x_26);
x_33 = lean_ctor_get(x_27, 1);
lean_inc(x_33);
lean_dec(x_27);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
}
else
{
uint8_t x_35; 
lean_dec(x_27);
x_35 = !lean_is_exclusive(x_26);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_26, 0);
lean_dec(x_36);
x_37 = lean_ctor_get(x_28, 0);
lean_inc(x_37);
lean_dec(x_28);
lean_ctor_set(x_26, 0, x_37);
return x_26;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_26, 1);
lean_inc(x_38);
lean_dec(x_26);
x_39 = lean_ctor_get(x_28, 0);
lean_inc(x_39);
lean_dec(x_28);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
return x_40;
}
}
}
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_getFVarSetToGeneralize___spec__53(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = x_2 == x_3;
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; size_t x_8; size_t x_9; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Lean_Expr_isFVar(x_6);
x_8 = 1;
x_9 = x_2 + x_8;
if (x_7 == 0)
{
lean_dec(x_6);
x_2 = x_9;
goto _start;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = l_Lean_Expr_fvarId_x21(x_6);
lean_dec(x_6);
x_12 = lean_box(0);
x_13 = l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_4, x_11, x_12);
x_2 = x_9;
x_4 = x_13;
goto _start;
}
}
else
{
return x_4;
}
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_getFVarSetToGeneralize___spec__56(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = x_6 < x_5;
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_3);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_array_uget(x_4, x_6);
x_16 = lean_ctor_get(x_7, 1);
lean_inc(x_16);
lean_dec(x_7);
x_17 = l_Std_PersistentArray_forInAux___at_Lean_Meta_getFVarSetToGeneralize___spec__55(x_1, x_2, x_15, x_16, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_15);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
lean_dec(x_3);
x_19 = !lean_is_exclusive(x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_17, 0);
lean_dec(x_20);
x_21 = lean_ctor_get(x_18, 0);
lean_inc(x_21);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_18);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
lean_ctor_set(x_17, 0, x_23);
return x_17;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_17, 1);
lean_inc(x_24);
lean_dec(x_17);
x_25 = lean_ctor_get(x_18, 0);
lean_inc(x_25);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_18);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_24);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; size_t x_32; size_t x_33; 
x_29 = lean_ctor_get(x_17, 1);
lean_inc(x_29);
lean_dec(x_17);
x_30 = lean_ctor_get(x_18, 0);
lean_inc(x_30);
lean_dec(x_18);
lean_inc(x_3);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_3);
lean_ctor_set(x_31, 1, x_30);
x_32 = 1;
x_33 = x_6 + x_32;
x_6 = x_33;
x_7 = x_31;
x_12 = x_29;
goto _start;
}
}
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_getFVarSetToGeneralize___spec__57(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_20; uint8_t x_37; 
x_37 = x_5 < x_4;
if (x_37 == 0)
{
lean_object* x_38; 
lean_dec(x_2);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_6);
lean_ctor_set(x_38, 1, x_11);
return x_38;
}
else
{
lean_object* x_39; 
x_39 = lean_array_uget(x_3, x_5);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_6, 1);
lean_inc(x_40);
lean_dec(x_6);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_11);
x_20 = x_42;
goto block_36;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_43 = lean_ctor_get(x_6, 1);
lean_inc(x_43);
lean_dec(x_6);
x_44 = lean_ctor_get(x_39, 0);
lean_inc(x_44);
lean_dec(x_39);
x_45 = lean_ctor_get(x_43, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
x_47 = l_Lean_LocalDecl_fvarId(x_44);
x_48 = l_Lean_NameSet_contains(x_1, x_47);
if (x_48 == 0)
{
uint8_t x_49; 
x_49 = l_Lean_LocalDecl_isAuxDecl(x_44);
if (x_49 == 0)
{
uint8_t x_50; uint8_t x_51; 
x_50 = l_Lean_LocalDecl_binderInfo(x_44);
x_51 = l_Lean_BinderInfo_isInstImplicit(x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_52 = lean_st_ref_get(x_10, x_11);
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
x_55 = lean_st_ref_get(x_8, x_53);
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
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_67 = lean_ctor_get(x_56, 0);
lean_inc(x_67);
lean_dec(x_56);
x_68 = lean_ctor_get(x_44, 3);
lean_inc(x_68);
lean_dec(x_44);
x_69 = l_Lean_Expr_hasFVar(x_68);
if (x_69 == 0)
{
uint8_t x_70; 
x_70 = l_Lean_Expr_hasMVar(x_68);
if (x_70 == 0)
{
uint8_t x_71; 
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_58);
lean_dec(x_47);
x_71 = !lean_is_exclusive(x_43);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_72 = lean_ctor_get(x_43, 1);
lean_dec(x_72);
x_73 = lean_ctor_get(x_43, 0);
lean_dec(x_73);
x_74 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_74, 0, x_43);
if (lean_is_scalar(x_54)) {
 x_75 = lean_alloc_ctor(0, 2, 0);
} else {
 x_75 = x_54;
}
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_57);
x_20 = x_75;
goto block_36;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_43);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_45);
lean_ctor_set(x_76, 1, x_46);
x_77 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_77, 0, x_76);
if (lean_is_scalar(x_54)) {
 x_78 = lean_alloc_ctor(0, 2, 0);
} else {
 x_78 = x_54;
}
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_57);
x_20 = x_78;
goto block_36;
}
}
else
{
lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_79 = l_Std_HashSet_instInhabitedHashSet___closed__1;
x_80 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__1(x_43, x_67, x_68, x_79);
x_81 = !lean_is_exclusive(x_43);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_82 = lean_ctor_get(x_43, 1);
lean_dec(x_82);
x_83 = lean_ctor_get(x_43, 0);
lean_dec(x_83);
x_84 = lean_ctor_get(x_80, 0);
lean_inc(x_84);
lean_dec(x_80);
x_85 = lean_unbox(x_84);
lean_dec(x_84);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; 
lean_dec(x_58);
lean_dec(x_47);
x_86 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_86, 0, x_43);
if (lean_is_scalar(x_54)) {
 x_87 = lean_alloc_ctor(0, 2, 0);
} else {
 x_87 = x_54;
}
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_57);
x_20 = x_87;
goto block_36;
}
else
{
lean_object* x_88; 
lean_free_object(x_43);
lean_dec(x_54);
x_88 = lean_box(0);
x_59 = x_88;
goto block_66;
}
}
else
{
lean_object* x_89; uint8_t x_90; 
lean_dec(x_43);
x_89 = lean_ctor_get(x_80, 0);
lean_inc(x_89);
lean_dec(x_80);
x_90 = lean_unbox(x_89);
lean_dec(x_89);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec(x_58);
lean_dec(x_47);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_45);
lean_ctor_set(x_91, 1, x_46);
x_92 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_92, 0, x_91);
if (lean_is_scalar(x_54)) {
 x_93 = lean_alloc_ctor(0, 2, 0);
} else {
 x_93 = x_54;
}
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_57);
x_20 = x_93;
goto block_36;
}
else
{
lean_object* x_94; 
lean_dec(x_54);
x_94 = lean_box(0);
x_59 = x_94;
goto block_66;
}
}
}
}
else
{
lean_object* x_95; lean_object* x_96; uint8_t x_97; 
x_95 = l_Std_HashSet_instInhabitedHashSet___closed__1;
x_96 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__8(x_43, x_67, x_68, x_95);
x_97 = !lean_is_exclusive(x_43);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; 
x_98 = lean_ctor_get(x_43, 1);
lean_dec(x_98);
x_99 = lean_ctor_get(x_43, 0);
lean_dec(x_99);
x_100 = lean_ctor_get(x_96, 0);
lean_inc(x_100);
lean_dec(x_96);
x_101 = lean_unbox(x_100);
lean_dec(x_100);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; 
lean_dec(x_58);
lean_dec(x_47);
x_102 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_102, 0, x_43);
if (lean_is_scalar(x_54)) {
 x_103 = lean_alloc_ctor(0, 2, 0);
} else {
 x_103 = x_54;
}
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_57);
x_20 = x_103;
goto block_36;
}
else
{
lean_object* x_104; 
lean_free_object(x_43);
lean_dec(x_54);
x_104 = lean_box(0);
x_59 = x_104;
goto block_66;
}
}
else
{
lean_object* x_105; uint8_t x_106; 
lean_dec(x_43);
x_105 = lean_ctor_get(x_96, 0);
lean_inc(x_105);
lean_dec(x_96);
x_106 = lean_unbox(x_105);
lean_dec(x_105);
if (x_106 == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
lean_dec(x_58);
lean_dec(x_47);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_45);
lean_ctor_set(x_107, 1, x_46);
x_108 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_108, 0, x_107);
if (lean_is_scalar(x_54)) {
 x_109 = lean_alloc_ctor(0, 2, 0);
} else {
 x_109 = x_54;
}
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_57);
x_20 = x_109;
goto block_36;
}
else
{
lean_object* x_110; 
lean_dec(x_54);
x_110 = lean_box(0);
x_59 = x_110;
goto block_66;
}
}
}
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_160; 
x_111 = lean_ctor_get(x_56, 0);
lean_inc(x_111);
lean_dec(x_56);
x_112 = lean_ctor_get(x_44, 3);
lean_inc(x_112);
x_113 = lean_ctor_get(x_44, 4);
lean_inc(x_113);
lean_dec(x_44);
x_160 = l_Lean_Expr_hasFVar(x_112);
if (x_160 == 0)
{
uint8_t x_161; 
x_161 = l_Lean_Expr_hasMVar(x_112);
if (x_161 == 0)
{
lean_object* x_162; 
lean_dec(x_112);
x_162 = l_Lean_MetavarContext_findLocalDeclDependsOn___closed__1;
x_114 = x_162;
goto block_159;
}
else
{
lean_object* x_163; lean_object* x_164; 
x_163 = l_Std_HashSet_instInhabitedHashSet___closed__1;
lean_inc(x_111);
x_164 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__29(x_43, x_111, x_112, x_163);
x_114 = x_164;
goto block_159;
}
}
else
{
lean_object* x_165; lean_object* x_166; 
x_165 = l_Std_HashSet_instInhabitedHashSet___closed__1;
lean_inc(x_111);
x_166 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__36(x_43, x_111, x_112, x_165);
x_114 = x_166;
goto block_159;
}
block_159:
{
lean_object* x_115; uint8_t x_116; 
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
x_116 = lean_unbox(x_115);
lean_dec(x_115);
if (x_116 == 0)
{
lean_object* x_117; uint8_t x_118; 
x_117 = lean_ctor_get(x_114, 1);
lean_inc(x_117);
lean_dec(x_114);
x_118 = l_Lean_Expr_hasFVar(x_113);
if (x_118 == 0)
{
uint8_t x_119; 
x_119 = l_Lean_Expr_hasMVar(x_113);
if (x_119 == 0)
{
uint8_t x_120; 
lean_dec(x_117);
lean_dec(x_113);
lean_dec(x_111);
lean_dec(x_58);
lean_dec(x_47);
x_120 = !lean_is_exclusive(x_43);
if (x_120 == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_121 = lean_ctor_get(x_43, 1);
lean_dec(x_121);
x_122 = lean_ctor_get(x_43, 0);
lean_dec(x_122);
x_123 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_123, 0, x_43);
if (lean_is_scalar(x_54)) {
 x_124 = lean_alloc_ctor(0, 2, 0);
} else {
 x_124 = x_54;
}
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_57);
x_20 = x_124;
goto block_36;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
lean_dec(x_43);
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_45);
lean_ctor_set(x_125, 1, x_46);
x_126 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_126, 0, x_125);
if (lean_is_scalar(x_54)) {
 x_127 = lean_alloc_ctor(0, 2, 0);
} else {
 x_127 = x_54;
}
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_127, 1, x_57);
x_20 = x_127;
goto block_36;
}
}
else
{
lean_object* x_128; uint8_t x_129; 
x_128 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__15(x_43, x_111, x_113, x_117);
x_129 = !lean_is_exclusive(x_43);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_133; 
x_130 = lean_ctor_get(x_43, 1);
lean_dec(x_130);
x_131 = lean_ctor_get(x_43, 0);
lean_dec(x_131);
x_132 = lean_ctor_get(x_128, 0);
lean_inc(x_132);
lean_dec(x_128);
x_133 = lean_unbox(x_132);
lean_dec(x_132);
if (x_133 == 0)
{
lean_object* x_134; lean_object* x_135; 
lean_dec(x_58);
lean_dec(x_47);
x_134 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_134, 0, x_43);
if (lean_is_scalar(x_54)) {
 x_135 = lean_alloc_ctor(0, 2, 0);
} else {
 x_135 = x_54;
}
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_57);
x_20 = x_135;
goto block_36;
}
else
{
lean_object* x_136; 
lean_free_object(x_43);
lean_dec(x_54);
x_136 = lean_box(0);
x_59 = x_136;
goto block_66;
}
}
else
{
lean_object* x_137; uint8_t x_138; 
lean_dec(x_43);
x_137 = lean_ctor_get(x_128, 0);
lean_inc(x_137);
lean_dec(x_128);
x_138 = lean_unbox(x_137);
lean_dec(x_137);
if (x_138 == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
lean_dec(x_58);
lean_dec(x_47);
x_139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_139, 0, x_45);
lean_ctor_set(x_139, 1, x_46);
x_140 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_140, 0, x_139);
if (lean_is_scalar(x_54)) {
 x_141 = lean_alloc_ctor(0, 2, 0);
} else {
 x_141 = x_54;
}
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_57);
x_20 = x_141;
goto block_36;
}
else
{
lean_object* x_142; 
lean_dec(x_54);
x_142 = lean_box(0);
x_59 = x_142;
goto block_66;
}
}
}
}
else
{
lean_object* x_143; uint8_t x_144; 
x_143 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__22(x_43, x_111, x_113, x_117);
x_144 = !lean_is_exclusive(x_43);
if (x_144 == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; uint8_t x_148; 
x_145 = lean_ctor_get(x_43, 1);
lean_dec(x_145);
x_146 = lean_ctor_get(x_43, 0);
lean_dec(x_146);
x_147 = lean_ctor_get(x_143, 0);
lean_inc(x_147);
lean_dec(x_143);
x_148 = lean_unbox(x_147);
lean_dec(x_147);
if (x_148 == 0)
{
lean_object* x_149; lean_object* x_150; 
lean_dec(x_58);
lean_dec(x_47);
x_149 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_149, 0, x_43);
if (lean_is_scalar(x_54)) {
 x_150 = lean_alloc_ctor(0, 2, 0);
} else {
 x_150 = x_54;
}
lean_ctor_set(x_150, 0, x_149);
lean_ctor_set(x_150, 1, x_57);
x_20 = x_150;
goto block_36;
}
else
{
lean_object* x_151; 
lean_free_object(x_43);
lean_dec(x_54);
x_151 = lean_box(0);
x_59 = x_151;
goto block_66;
}
}
else
{
lean_object* x_152; uint8_t x_153; 
lean_dec(x_43);
x_152 = lean_ctor_get(x_143, 0);
lean_inc(x_152);
lean_dec(x_143);
x_153 = lean_unbox(x_152);
lean_dec(x_152);
if (x_153 == 0)
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; 
lean_dec(x_58);
lean_dec(x_47);
x_154 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_154, 0, x_45);
lean_ctor_set(x_154, 1, x_46);
x_155 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_155, 0, x_154);
if (lean_is_scalar(x_54)) {
 x_156 = lean_alloc_ctor(0, 2, 0);
} else {
 x_156 = x_54;
}
lean_ctor_set(x_156, 0, x_155);
lean_ctor_set(x_156, 1, x_57);
x_20 = x_156;
goto block_36;
}
else
{
lean_object* x_157; 
lean_dec(x_54);
x_157 = lean_box(0);
x_59 = x_157;
goto block_66;
}
}
}
}
else
{
lean_object* x_158; 
lean_dec(x_114);
lean_dec(x_113);
lean_dec(x_111);
lean_dec(x_54);
lean_dec(x_43);
x_158 = lean_box(0);
x_59 = x_158;
goto block_66;
}
}
}
block_66:
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_59);
x_60 = lean_box(0);
lean_inc(x_47);
x_61 = l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_46, x_47, x_60);
x_62 = l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_45, x_47, x_60);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_61);
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_63);
if (lean_is_scalar(x_58)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_58;
}
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_57);
x_20 = x_65;
goto block_36;
}
}
else
{
uint8_t x_167; 
lean_dec(x_47);
lean_dec(x_44);
x_167 = !lean_is_exclusive(x_43);
if (x_167 == 0)
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_168 = lean_ctor_get(x_43, 1);
lean_dec(x_168);
x_169 = lean_ctor_get(x_43, 0);
lean_dec(x_169);
x_170 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_170, 0, x_43);
x_171 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_171, 1, x_11);
x_20 = x_171;
goto block_36;
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; 
lean_dec(x_43);
x_172 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_172, 0, x_45);
lean_ctor_set(x_172, 1, x_46);
x_173 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_173, 0, x_172);
x_174 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_174, 0, x_173);
lean_ctor_set(x_174, 1, x_11);
x_20 = x_174;
goto block_36;
}
}
}
else
{
uint8_t x_175; 
lean_dec(x_47);
lean_dec(x_44);
x_175 = !lean_is_exclusive(x_43);
if (x_175 == 0)
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_176 = lean_ctor_get(x_43, 1);
lean_dec(x_176);
x_177 = lean_ctor_get(x_43, 0);
lean_dec(x_177);
x_178 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_178, 0, x_43);
x_179 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_179, 0, x_178);
lean_ctor_set(x_179, 1, x_11);
x_20 = x_179;
goto block_36;
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; 
lean_dec(x_43);
x_180 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_180, 0, x_45);
lean_ctor_set(x_180, 1, x_46);
x_181 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_181, 0, x_180);
x_182 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_182, 0, x_181);
lean_ctor_set(x_182, 1, x_11);
x_20 = x_182;
goto block_36;
}
}
}
else
{
uint8_t x_183; 
lean_dec(x_47);
lean_dec(x_44);
x_183 = !lean_is_exclusive(x_43);
if (x_183 == 0)
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_184 = lean_ctor_get(x_43, 1);
lean_dec(x_184);
x_185 = lean_ctor_get(x_43, 0);
lean_dec(x_185);
x_186 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_186, 0, x_43);
x_187 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_187, 0, x_186);
lean_ctor_set(x_187, 1, x_11);
x_20 = x_187;
goto block_36;
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; 
lean_dec(x_43);
x_188 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_188, 0, x_45);
lean_ctor_set(x_188, 1, x_46);
x_189 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_189, 0, x_188);
x_190 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_190, 0, x_189);
lean_ctor_set(x_190, 1, x_11);
x_20 = x_190;
goto block_36;
}
}
}
}
block_19:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = 1;
x_17 = x_5 + x_16;
x_5 = x_17;
x_6 = x_15;
x_11 = x_14;
goto _start;
}
block_36:
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_2);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_2);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set(x_22, 0, x_25);
x_12 = x_20;
goto block_19;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_22, 0);
lean_inc(x_26);
lean_dec(x_22);
lean_inc(x_2);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_2);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_20, 0, x_28);
x_12 = x_20;
goto block_19;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_29 = lean_ctor_get(x_20, 0);
x_30 = lean_ctor_get(x_20, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_20);
x_31 = lean_ctor_get(x_29, 0);
lean_inc(x_31);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 x_32 = x_29;
} else {
 lean_dec_ref(x_29);
 x_32 = lean_box(0);
}
lean_inc(x_2);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_2);
lean_ctor_set(x_33, 1, x_31);
if (lean_is_scalar(x_32)) {
 x_34 = lean_alloc_ctor(1, 1, 0);
} else {
 x_34 = x_32;
}
lean_ctor_set(x_34, 0, x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_30);
x_12 = x_35;
goto block_19;
}
}
}
}
lean_object* l_Std_PersistentArray_forInAux___at_Lean_Meta_getFVarSetToGeneralize___spec__55(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_4);
x_13 = lean_array_get_size(x_10);
x_14 = lean_usize_of_nat(x_13);
lean_dec(x_13);
x_15 = 0;
x_16 = l_Array_forInUnsafe_loop___at_Lean_Meta_getFVarSetToGeneralize___spec__56(x_1, x_2, x_11, x_10, x_14, x_15, x_12, x_5, x_6, x_7, x_8, x_9);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_box(0);
x_22 = l_Std_PersistentArray_forInAux___at_Lean_Meta_getFVarSetToGeneralize___spec__44___lambda__1(x_20, x_21, x_5, x_6, x_7, x_8, x_19);
return x_22;
}
else
{
uint8_t x_23; 
lean_dec(x_17);
x_23 = !lean_is_exclusive(x_16);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_16, 0);
lean_dec(x_24);
x_25 = lean_ctor_get(x_18, 0);
lean_inc(x_25);
lean_dec(x_18);
lean_ctor_set(x_16, 0, x_25);
return x_16;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_16, 1);
lean_inc(x_26);
lean_dec(x_16);
x_27 = lean_ctor_get(x_18, 0);
lean_inc(x_27);
lean_dec(x_18);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; size_t x_33; size_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_29 = lean_ctor_get(x_3, 0);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_4);
x_32 = lean_array_get_size(x_29);
x_33 = lean_usize_of_nat(x_32);
lean_dec(x_32);
x_34 = 0;
x_35 = l_Array_forInUnsafe_loop___at_Lean_Meta_getFVarSetToGeneralize___spec__57(x_1, x_30, x_29, x_33, x_34, x_31, x_5, x_6, x_7, x_8, x_9);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_dec(x_35);
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_dec(x_36);
x_40 = lean_box(0);
x_41 = l_Std_PersistentArray_forInAux___at_Lean_Meta_getFVarSetToGeneralize___spec__44___lambda__1(x_39, x_40, x_5, x_6, x_7, x_8, x_38);
return x_41;
}
else
{
uint8_t x_42; 
lean_dec(x_36);
x_42 = !lean_is_exclusive(x_35);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_35, 0);
lean_dec(x_43);
x_44 = lean_ctor_get(x_37, 0);
lean_inc(x_44);
lean_dec(x_37);
lean_ctor_set(x_35, 0, x_44);
return x_35;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_35, 1);
lean_inc(x_45);
lean_dec(x_35);
x_46 = lean_ctor_get(x_37, 0);
lean_inc(x_46);
lean_dec(x_37);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
return x_47;
}
}
}
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_getFVarSetToGeneralize___spec__58(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_20; uint8_t x_37; 
x_37 = x_5 < x_4;
if (x_37 == 0)
{
lean_object* x_38; 
lean_dec(x_2);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_6);
lean_ctor_set(x_38, 1, x_11);
return x_38;
}
else
{
lean_object* x_39; 
x_39 = lean_array_uget(x_3, x_5);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_6, 1);
lean_inc(x_40);
lean_dec(x_6);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_11);
x_20 = x_42;
goto block_36;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_43 = lean_ctor_get(x_6, 1);
lean_inc(x_43);
lean_dec(x_6);
x_44 = lean_ctor_get(x_39, 0);
lean_inc(x_44);
lean_dec(x_39);
x_45 = lean_ctor_get(x_43, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
x_47 = l_Lean_LocalDecl_fvarId(x_44);
x_48 = l_Lean_NameSet_contains(x_1, x_47);
if (x_48 == 0)
{
uint8_t x_49; 
x_49 = l_Lean_LocalDecl_isAuxDecl(x_44);
if (x_49 == 0)
{
uint8_t x_50; uint8_t x_51; 
x_50 = l_Lean_LocalDecl_binderInfo(x_44);
x_51 = l_Lean_BinderInfo_isInstImplicit(x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_52 = lean_st_ref_get(x_10, x_11);
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
x_55 = lean_st_ref_get(x_8, x_53);
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
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_67 = lean_ctor_get(x_56, 0);
lean_inc(x_67);
lean_dec(x_56);
x_68 = lean_ctor_get(x_44, 3);
lean_inc(x_68);
lean_dec(x_44);
x_69 = l_Lean_Expr_hasFVar(x_68);
if (x_69 == 0)
{
uint8_t x_70; 
x_70 = l_Lean_Expr_hasMVar(x_68);
if (x_70 == 0)
{
uint8_t x_71; 
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_58);
lean_dec(x_47);
x_71 = !lean_is_exclusive(x_43);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_72 = lean_ctor_get(x_43, 1);
lean_dec(x_72);
x_73 = lean_ctor_get(x_43, 0);
lean_dec(x_73);
x_74 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_74, 0, x_43);
if (lean_is_scalar(x_54)) {
 x_75 = lean_alloc_ctor(0, 2, 0);
} else {
 x_75 = x_54;
}
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_57);
x_20 = x_75;
goto block_36;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_43);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_45);
lean_ctor_set(x_76, 1, x_46);
x_77 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_77, 0, x_76);
if (lean_is_scalar(x_54)) {
 x_78 = lean_alloc_ctor(0, 2, 0);
} else {
 x_78 = x_54;
}
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_57);
x_20 = x_78;
goto block_36;
}
}
else
{
lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_79 = l_Std_HashSet_instInhabitedHashSet___closed__1;
x_80 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__1(x_43, x_67, x_68, x_79);
x_81 = !lean_is_exclusive(x_43);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_82 = lean_ctor_get(x_43, 1);
lean_dec(x_82);
x_83 = lean_ctor_get(x_43, 0);
lean_dec(x_83);
x_84 = lean_ctor_get(x_80, 0);
lean_inc(x_84);
lean_dec(x_80);
x_85 = lean_unbox(x_84);
lean_dec(x_84);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; 
lean_dec(x_58);
lean_dec(x_47);
x_86 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_86, 0, x_43);
if (lean_is_scalar(x_54)) {
 x_87 = lean_alloc_ctor(0, 2, 0);
} else {
 x_87 = x_54;
}
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_57);
x_20 = x_87;
goto block_36;
}
else
{
lean_object* x_88; 
lean_free_object(x_43);
lean_dec(x_54);
x_88 = lean_box(0);
x_59 = x_88;
goto block_66;
}
}
else
{
lean_object* x_89; uint8_t x_90; 
lean_dec(x_43);
x_89 = lean_ctor_get(x_80, 0);
lean_inc(x_89);
lean_dec(x_80);
x_90 = lean_unbox(x_89);
lean_dec(x_89);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec(x_58);
lean_dec(x_47);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_45);
lean_ctor_set(x_91, 1, x_46);
x_92 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_92, 0, x_91);
if (lean_is_scalar(x_54)) {
 x_93 = lean_alloc_ctor(0, 2, 0);
} else {
 x_93 = x_54;
}
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_57);
x_20 = x_93;
goto block_36;
}
else
{
lean_object* x_94; 
lean_dec(x_54);
x_94 = lean_box(0);
x_59 = x_94;
goto block_66;
}
}
}
}
else
{
lean_object* x_95; lean_object* x_96; uint8_t x_97; 
x_95 = l_Std_HashSet_instInhabitedHashSet___closed__1;
x_96 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__8(x_43, x_67, x_68, x_95);
x_97 = !lean_is_exclusive(x_43);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; 
x_98 = lean_ctor_get(x_43, 1);
lean_dec(x_98);
x_99 = lean_ctor_get(x_43, 0);
lean_dec(x_99);
x_100 = lean_ctor_get(x_96, 0);
lean_inc(x_100);
lean_dec(x_96);
x_101 = lean_unbox(x_100);
lean_dec(x_100);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; 
lean_dec(x_58);
lean_dec(x_47);
x_102 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_102, 0, x_43);
if (lean_is_scalar(x_54)) {
 x_103 = lean_alloc_ctor(0, 2, 0);
} else {
 x_103 = x_54;
}
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_57);
x_20 = x_103;
goto block_36;
}
else
{
lean_object* x_104; 
lean_free_object(x_43);
lean_dec(x_54);
x_104 = lean_box(0);
x_59 = x_104;
goto block_66;
}
}
else
{
lean_object* x_105; uint8_t x_106; 
lean_dec(x_43);
x_105 = lean_ctor_get(x_96, 0);
lean_inc(x_105);
lean_dec(x_96);
x_106 = lean_unbox(x_105);
lean_dec(x_105);
if (x_106 == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
lean_dec(x_58);
lean_dec(x_47);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_45);
lean_ctor_set(x_107, 1, x_46);
x_108 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_108, 0, x_107);
if (lean_is_scalar(x_54)) {
 x_109 = lean_alloc_ctor(0, 2, 0);
} else {
 x_109 = x_54;
}
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_57);
x_20 = x_109;
goto block_36;
}
else
{
lean_object* x_110; 
lean_dec(x_54);
x_110 = lean_box(0);
x_59 = x_110;
goto block_66;
}
}
}
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_160; 
x_111 = lean_ctor_get(x_56, 0);
lean_inc(x_111);
lean_dec(x_56);
x_112 = lean_ctor_get(x_44, 3);
lean_inc(x_112);
x_113 = lean_ctor_get(x_44, 4);
lean_inc(x_113);
lean_dec(x_44);
x_160 = l_Lean_Expr_hasFVar(x_112);
if (x_160 == 0)
{
uint8_t x_161; 
x_161 = l_Lean_Expr_hasMVar(x_112);
if (x_161 == 0)
{
lean_object* x_162; 
lean_dec(x_112);
x_162 = l_Lean_MetavarContext_findLocalDeclDependsOn___closed__1;
x_114 = x_162;
goto block_159;
}
else
{
lean_object* x_163; lean_object* x_164; 
x_163 = l_Std_HashSet_instInhabitedHashSet___closed__1;
lean_inc(x_111);
x_164 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__29(x_43, x_111, x_112, x_163);
x_114 = x_164;
goto block_159;
}
}
else
{
lean_object* x_165; lean_object* x_166; 
x_165 = l_Std_HashSet_instInhabitedHashSet___closed__1;
lean_inc(x_111);
x_166 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__36(x_43, x_111, x_112, x_165);
x_114 = x_166;
goto block_159;
}
block_159:
{
lean_object* x_115; uint8_t x_116; 
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
x_116 = lean_unbox(x_115);
lean_dec(x_115);
if (x_116 == 0)
{
lean_object* x_117; uint8_t x_118; 
x_117 = lean_ctor_get(x_114, 1);
lean_inc(x_117);
lean_dec(x_114);
x_118 = l_Lean_Expr_hasFVar(x_113);
if (x_118 == 0)
{
uint8_t x_119; 
x_119 = l_Lean_Expr_hasMVar(x_113);
if (x_119 == 0)
{
uint8_t x_120; 
lean_dec(x_117);
lean_dec(x_113);
lean_dec(x_111);
lean_dec(x_58);
lean_dec(x_47);
x_120 = !lean_is_exclusive(x_43);
if (x_120 == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_121 = lean_ctor_get(x_43, 1);
lean_dec(x_121);
x_122 = lean_ctor_get(x_43, 0);
lean_dec(x_122);
x_123 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_123, 0, x_43);
if (lean_is_scalar(x_54)) {
 x_124 = lean_alloc_ctor(0, 2, 0);
} else {
 x_124 = x_54;
}
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_57);
x_20 = x_124;
goto block_36;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
lean_dec(x_43);
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_45);
lean_ctor_set(x_125, 1, x_46);
x_126 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_126, 0, x_125);
if (lean_is_scalar(x_54)) {
 x_127 = lean_alloc_ctor(0, 2, 0);
} else {
 x_127 = x_54;
}
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_127, 1, x_57);
x_20 = x_127;
goto block_36;
}
}
else
{
lean_object* x_128; uint8_t x_129; 
x_128 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__15(x_43, x_111, x_113, x_117);
x_129 = !lean_is_exclusive(x_43);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_133; 
x_130 = lean_ctor_get(x_43, 1);
lean_dec(x_130);
x_131 = lean_ctor_get(x_43, 0);
lean_dec(x_131);
x_132 = lean_ctor_get(x_128, 0);
lean_inc(x_132);
lean_dec(x_128);
x_133 = lean_unbox(x_132);
lean_dec(x_132);
if (x_133 == 0)
{
lean_object* x_134; lean_object* x_135; 
lean_dec(x_58);
lean_dec(x_47);
x_134 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_134, 0, x_43);
if (lean_is_scalar(x_54)) {
 x_135 = lean_alloc_ctor(0, 2, 0);
} else {
 x_135 = x_54;
}
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_57);
x_20 = x_135;
goto block_36;
}
else
{
lean_object* x_136; 
lean_free_object(x_43);
lean_dec(x_54);
x_136 = lean_box(0);
x_59 = x_136;
goto block_66;
}
}
else
{
lean_object* x_137; uint8_t x_138; 
lean_dec(x_43);
x_137 = lean_ctor_get(x_128, 0);
lean_inc(x_137);
lean_dec(x_128);
x_138 = lean_unbox(x_137);
lean_dec(x_137);
if (x_138 == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
lean_dec(x_58);
lean_dec(x_47);
x_139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_139, 0, x_45);
lean_ctor_set(x_139, 1, x_46);
x_140 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_140, 0, x_139);
if (lean_is_scalar(x_54)) {
 x_141 = lean_alloc_ctor(0, 2, 0);
} else {
 x_141 = x_54;
}
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_57);
x_20 = x_141;
goto block_36;
}
else
{
lean_object* x_142; 
lean_dec(x_54);
x_142 = lean_box(0);
x_59 = x_142;
goto block_66;
}
}
}
}
else
{
lean_object* x_143; uint8_t x_144; 
x_143 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__22(x_43, x_111, x_113, x_117);
x_144 = !lean_is_exclusive(x_43);
if (x_144 == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; uint8_t x_148; 
x_145 = lean_ctor_get(x_43, 1);
lean_dec(x_145);
x_146 = lean_ctor_get(x_43, 0);
lean_dec(x_146);
x_147 = lean_ctor_get(x_143, 0);
lean_inc(x_147);
lean_dec(x_143);
x_148 = lean_unbox(x_147);
lean_dec(x_147);
if (x_148 == 0)
{
lean_object* x_149; lean_object* x_150; 
lean_dec(x_58);
lean_dec(x_47);
x_149 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_149, 0, x_43);
if (lean_is_scalar(x_54)) {
 x_150 = lean_alloc_ctor(0, 2, 0);
} else {
 x_150 = x_54;
}
lean_ctor_set(x_150, 0, x_149);
lean_ctor_set(x_150, 1, x_57);
x_20 = x_150;
goto block_36;
}
else
{
lean_object* x_151; 
lean_free_object(x_43);
lean_dec(x_54);
x_151 = lean_box(0);
x_59 = x_151;
goto block_66;
}
}
else
{
lean_object* x_152; uint8_t x_153; 
lean_dec(x_43);
x_152 = lean_ctor_get(x_143, 0);
lean_inc(x_152);
lean_dec(x_143);
x_153 = lean_unbox(x_152);
lean_dec(x_152);
if (x_153 == 0)
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; 
lean_dec(x_58);
lean_dec(x_47);
x_154 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_154, 0, x_45);
lean_ctor_set(x_154, 1, x_46);
x_155 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_155, 0, x_154);
if (lean_is_scalar(x_54)) {
 x_156 = lean_alloc_ctor(0, 2, 0);
} else {
 x_156 = x_54;
}
lean_ctor_set(x_156, 0, x_155);
lean_ctor_set(x_156, 1, x_57);
x_20 = x_156;
goto block_36;
}
else
{
lean_object* x_157; 
lean_dec(x_54);
x_157 = lean_box(0);
x_59 = x_157;
goto block_66;
}
}
}
}
else
{
lean_object* x_158; 
lean_dec(x_114);
lean_dec(x_113);
lean_dec(x_111);
lean_dec(x_54);
lean_dec(x_43);
x_158 = lean_box(0);
x_59 = x_158;
goto block_66;
}
}
}
block_66:
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_59);
x_60 = lean_box(0);
lean_inc(x_47);
x_61 = l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_46, x_47, x_60);
x_62 = l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_45, x_47, x_60);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_61);
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_63);
if (lean_is_scalar(x_58)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_58;
}
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_57);
x_20 = x_65;
goto block_36;
}
}
else
{
uint8_t x_167; 
lean_dec(x_47);
lean_dec(x_44);
x_167 = !lean_is_exclusive(x_43);
if (x_167 == 0)
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_168 = lean_ctor_get(x_43, 1);
lean_dec(x_168);
x_169 = lean_ctor_get(x_43, 0);
lean_dec(x_169);
x_170 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_170, 0, x_43);
x_171 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_171, 1, x_11);
x_20 = x_171;
goto block_36;
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; 
lean_dec(x_43);
x_172 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_172, 0, x_45);
lean_ctor_set(x_172, 1, x_46);
x_173 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_173, 0, x_172);
x_174 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_174, 0, x_173);
lean_ctor_set(x_174, 1, x_11);
x_20 = x_174;
goto block_36;
}
}
}
else
{
uint8_t x_175; 
lean_dec(x_47);
lean_dec(x_44);
x_175 = !lean_is_exclusive(x_43);
if (x_175 == 0)
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_176 = lean_ctor_get(x_43, 1);
lean_dec(x_176);
x_177 = lean_ctor_get(x_43, 0);
lean_dec(x_177);
x_178 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_178, 0, x_43);
x_179 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_179, 0, x_178);
lean_ctor_set(x_179, 1, x_11);
x_20 = x_179;
goto block_36;
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; 
lean_dec(x_43);
x_180 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_180, 0, x_45);
lean_ctor_set(x_180, 1, x_46);
x_181 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_181, 0, x_180);
x_182 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_182, 0, x_181);
lean_ctor_set(x_182, 1, x_11);
x_20 = x_182;
goto block_36;
}
}
}
else
{
uint8_t x_183; 
lean_dec(x_47);
lean_dec(x_44);
x_183 = !lean_is_exclusive(x_43);
if (x_183 == 0)
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_184 = lean_ctor_get(x_43, 1);
lean_dec(x_184);
x_185 = lean_ctor_get(x_43, 0);
lean_dec(x_185);
x_186 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_186, 0, x_43);
x_187 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_187, 0, x_186);
lean_ctor_set(x_187, 1, x_11);
x_20 = x_187;
goto block_36;
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; 
lean_dec(x_43);
x_188 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_188, 0, x_45);
lean_ctor_set(x_188, 1, x_46);
x_189 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_189, 0, x_188);
x_190 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_190, 0, x_189);
lean_ctor_set(x_190, 1, x_11);
x_20 = x_190;
goto block_36;
}
}
}
}
block_19:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = 1;
x_17 = x_5 + x_16;
x_5 = x_17;
x_6 = x_15;
x_11 = x_14;
goto _start;
}
block_36:
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_2);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_2);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set(x_22, 0, x_25);
x_12 = x_20;
goto block_19;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_22, 0);
lean_inc(x_26);
lean_dec(x_22);
lean_inc(x_2);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_2);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_20, 0, x_28);
x_12 = x_20;
goto block_19;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_29 = lean_ctor_get(x_20, 0);
x_30 = lean_ctor_get(x_20, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_20);
x_31 = lean_ctor_get(x_29, 0);
lean_inc(x_31);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 x_32 = x_29;
} else {
 lean_dec_ref(x_29);
 x_32 = lean_box(0);
}
lean_inc(x_2);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_2);
lean_ctor_set(x_33, 1, x_31);
if (lean_is_scalar(x_32)) {
 x_34 = lean_alloc_ctor(1, 1, 0);
} else {
 x_34 = x_32;
}
lean_ctor_set(x_34, 0, x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_30);
x_12 = x_35;
goto block_19;
}
}
}
}
lean_object* l_Std_PersistentArray_forIn___at_Lean_Meta_getFVarSetToGeneralize___spec__54(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_10 = l_Std_PersistentArray_forInAux___at_Lean_Meta_getFVarSetToGeneralize___spec__55(x_1, x_3, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_10, 0);
lean_dec(x_13);
x_14 = lean_ctor_get(x_11, 0);
lean_inc(x_14);
lean_dec(x_11);
lean_ctor_set(x_10, 0, x_14);
return x_10;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_dec(x_10);
x_16 = lean_ctor_get(x_11, 0);
lean_inc(x_16);
lean_dec(x_11);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; size_t x_24; size_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_18 = lean_ctor_get(x_10, 1);
lean_inc(x_18);
lean_dec(x_10);
x_19 = lean_ctor_get(x_11, 0);
lean_inc(x_19);
lean_dec(x_11);
x_20 = lean_ctor_get(x_2, 1);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_19);
x_23 = lean_array_get_size(x_20);
x_24 = lean_usize_of_nat(x_23);
lean_dec(x_23);
x_25 = 0;
x_26 = l_Array_forInUnsafe_loop___at_Lean_Meta_getFVarSetToGeneralize___spec__58(x_1, x_21, x_20, x_24, x_25, x_22, x_4, x_5, x_6, x_7, x_18);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_26);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_26, 0);
lean_dec(x_30);
x_31 = lean_ctor_get(x_27, 1);
lean_inc(x_31);
lean_dec(x_27);
lean_ctor_set(x_26, 0, x_31);
return x_26;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_26, 1);
lean_inc(x_32);
lean_dec(x_26);
x_33 = lean_ctor_get(x_27, 1);
lean_inc(x_33);
lean_dec(x_27);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
}
else
{
uint8_t x_35; 
lean_dec(x_27);
x_35 = !lean_is_exclusive(x_26);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_26, 0);
lean_dec(x_36);
x_37 = lean_ctor_get(x_28, 0);
lean_inc(x_37);
lean_dec(x_28);
lean_ctor_set(x_26, 0, x_37);
return x_26;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_26, 1);
lean_inc(x_38);
lean_dec(x_26);
x_39 = lean_ctor_get(x_28, 0);
lean_inc(x_39);
lean_dec(x_28);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
return x_40;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_getFVarSetToGeneralize___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_NameSet_empty;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_getFVarSetToGeneralize(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_array_get_size(x_1);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_lt(x_9, x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
lean_dec(x_8);
x_11 = lean_ctor_get(x_3, 1);
x_12 = lean_ctor_get(x_11, 1);
x_13 = l_Lean_Meta_getFVarSetToGeneralize___closed__1;
x_14 = l_Std_PersistentArray_forIn___at_Lean_Meta_getFVarSetToGeneralize___spec__43(x_2, x_12, x_13, x_3, x_4, x_5, x_6, x_7);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
lean_ctor_set(x_14, 0, x_17);
return x_14;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_14, 0);
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_14);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_3, 1);
x_23 = lean_ctor_get(x_22, 1);
x_24 = lean_nat_dec_le(x_8, x_8);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
lean_dec(x_8);
x_25 = l_Lean_Meta_getFVarSetToGeneralize___closed__1;
x_26 = l_Std_PersistentArray_forIn___at_Lean_Meta_getFVarSetToGeneralize___spec__48(x_2, x_23, x_25, x_3, x_4, x_5, x_6, x_7);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
lean_ctor_set(x_26, 0, x_29);
return x_26;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_26, 0);
x_31 = lean_ctor_get(x_26, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_26);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
else
{
size_t x_34; size_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_34 = 0;
x_35 = lean_usize_of_nat(x_8);
lean_dec(x_8);
x_36 = l_Lean_NameSet_empty;
x_37 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_getFVarSetToGeneralize___spec__53(x_1, x_34, x_35, x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
x_39 = l_Std_PersistentArray_forIn___at_Lean_Meta_getFVarSetToGeneralize___spec__54(x_2, x_23, x_38, x_3, x_4, x_5, x_6, x_7);
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_39, 0);
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
lean_dec(x_41);
lean_ctor_set(x_39, 0, x_42);
return x_39;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_43 = lean_ctor_get(x_39, 0);
x_44 = lean_ctor_get(x_39, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_39);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
return x_46;
}
}
}
}
}
lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__5(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__6(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
lean_object* l_Std_PersistentArray_anyMAux___at_Lean_Meta_getFVarSetToGeneralize___spec__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_PersistentArray_anyMAux___at_Lean_Meta_getFVarSetToGeneralize___spec__4(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__7(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
lean_object* l_Std_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__3(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at_Lean_Meta_getFVarSetToGeneralize___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at_Lean_Meta_getFVarSetToGeneralize___spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__12(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__13___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__13(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
lean_object* l_Std_PersistentArray_anyMAux___at_Lean_Meta_getFVarSetToGeneralize___spec__11___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_PersistentArray_anyMAux___at_Lean_Meta_getFVarSetToGeneralize___spec__11(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__14___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__14(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
lean_object* l_Std_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__10___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__10(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at_Lean_Meta_getFVarSetToGeneralize___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at_Lean_Meta_getFVarSetToGeneralize___spec__9(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__8(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__19___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__19(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__20___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__20(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
lean_object* l_Std_PersistentArray_anyMAux___at_Lean_Meta_getFVarSetToGeneralize___spec__18___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_PersistentArray_anyMAux___at_Lean_Meta_getFVarSetToGeneralize___spec__18(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__21___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__21(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
lean_object* l_Std_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__17___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__17(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at_Lean_Meta_getFVarSetToGeneralize___spec__16___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at_Lean_Meta_getFVarSetToGeneralize___spec__16(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__15___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__15(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__26___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__26(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__27(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
lean_object* l_Std_PersistentArray_anyMAux___at_Lean_Meta_getFVarSetToGeneralize___spec__25___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_PersistentArray_anyMAux___at_Lean_Meta_getFVarSetToGeneralize___spec__25(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__28___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__28(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
lean_object* l_Std_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__24___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__24(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at_Lean_Meta_getFVarSetToGeneralize___spec__23___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at_Lean_Meta_getFVarSetToGeneralize___spec__23(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__22___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__22(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__33___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__33(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__34___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__34(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
lean_object* l_Std_PersistentArray_anyMAux___at_Lean_Meta_getFVarSetToGeneralize___spec__32___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_PersistentArray_anyMAux___at_Lean_Meta_getFVarSetToGeneralize___spec__32(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__35___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__35(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
lean_object* l_Std_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__31___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__31(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at_Lean_Meta_getFVarSetToGeneralize___spec__30___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at_Lean_Meta_getFVarSetToGeneralize___spec__30(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__29___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__29(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__40___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__40(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__41___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__41(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
lean_object* l_Std_PersistentArray_anyMAux___at_Lean_Meta_getFVarSetToGeneralize___spec__39___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_PersistentArray_anyMAux___at_Lean_Meta_getFVarSetToGeneralize___spec__39(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__42___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__42(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
lean_object* l_Std_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__38___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__38(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at_Lean_Meta_getFVarSetToGeneralize___spec__37___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at_Lean_Meta_getFVarSetToGeneralize___spec__37(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__36___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__36(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_getFVarSetToGeneralize___spec__45___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_15 = l_Array_forInUnsafe_loop___at_Lean_Meta_getFVarSetToGeneralize___spec__45(x_1, x_2, x_3, x_4, x_13, x_14, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_15;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_getFVarSetToGeneralize___spec__46___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = l_Array_forInUnsafe_loop___at_Lean_Meta_getFVarSetToGeneralize___spec__46(x_1, x_2, x_3, x_12, x_13, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
return x_14;
}
}
lean_object* l_Std_PersistentArray_forInAux___at_Lean_Meta_getFVarSetToGeneralize___spec__44___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_PersistentArray_forInAux___at_Lean_Meta_getFVarSetToGeneralize___spec__44___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Std_PersistentArray_forInAux___at_Lean_Meta_getFVarSetToGeneralize___spec__44___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Std_PersistentArray_forInAux___at_Lean_Meta_getFVarSetToGeneralize___spec__44(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_getFVarSetToGeneralize___spec__47___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = l_Array_forInUnsafe_loop___at_Lean_Meta_getFVarSetToGeneralize___spec__47(x_1, x_2, x_3, x_12, x_13, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
return x_14;
}
}
lean_object* l_Std_PersistentArray_forIn___at_Lean_Meta_getFVarSetToGeneralize___spec__43___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_PersistentArray_forIn___at_Lean_Meta_getFVarSetToGeneralize___spec__43___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Std_PersistentArray_forIn___at_Lean_Meta_getFVarSetToGeneralize___spec__43___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Std_PersistentArray_forIn___at_Lean_Meta_getFVarSetToGeneralize___spec__43(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_getFVarSetToGeneralize___spec__50___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_15 = l_Array_forInUnsafe_loop___at_Lean_Meta_getFVarSetToGeneralize___spec__50(x_1, x_2, x_3, x_4, x_13, x_14, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_15;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_getFVarSetToGeneralize___spec__51___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = l_Array_forInUnsafe_loop___at_Lean_Meta_getFVarSetToGeneralize___spec__51(x_1, x_2, x_3, x_12, x_13, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
return x_14;
}
}
lean_object* l_Std_PersistentArray_forInAux___at_Lean_Meta_getFVarSetToGeneralize___spec__49___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Std_PersistentArray_forInAux___at_Lean_Meta_getFVarSetToGeneralize___spec__49(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_getFVarSetToGeneralize___spec__52___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = l_Array_forInUnsafe_loop___at_Lean_Meta_getFVarSetToGeneralize___spec__52(x_1, x_2, x_3, x_12, x_13, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
return x_14;
}
}
lean_object* l_Std_PersistentArray_forIn___at_Lean_Meta_getFVarSetToGeneralize___spec__48___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Std_PersistentArray_forIn___at_Lean_Meta_getFVarSetToGeneralize___spec__48(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_getFVarSetToGeneralize___spec__53___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_getFVarSetToGeneralize___spec__53(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_getFVarSetToGeneralize___spec__56___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_15 = l_Array_forInUnsafe_loop___at_Lean_Meta_getFVarSetToGeneralize___spec__56(x_1, x_2, x_3, x_4, x_13, x_14, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_15;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_getFVarSetToGeneralize___spec__57___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = l_Array_forInUnsafe_loop___at_Lean_Meta_getFVarSetToGeneralize___spec__57(x_1, x_2, x_3, x_12, x_13, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
return x_14;
}
}
lean_object* l_Std_PersistentArray_forInAux___at_Lean_Meta_getFVarSetToGeneralize___spec__55___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Std_PersistentArray_forInAux___at_Lean_Meta_getFVarSetToGeneralize___spec__55(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_getFVarSetToGeneralize___spec__58___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = l_Array_forInUnsafe_loop___at_Lean_Meta_getFVarSetToGeneralize___spec__58(x_1, x_2, x_3, x_12, x_13, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
return x_14;
}
}
lean_object* l_Std_PersistentArray_forIn___at_Lean_Meta_getFVarSetToGeneralize___spec__54___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Std_PersistentArray_forIn___at_Lean_Meta_getFVarSetToGeneralize___spec__54(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
lean_object* l_Lean_Meta_getFVarSetToGeneralize___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_getFVarSetToGeneralize(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Std_RBNode_fold___at_Lean_Meta_sortFVars___spec__1(lean_object* x_1, lean_object* x_2) {
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
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 3);
lean_inc(x_5);
lean_dec(x_2);
x_6 = l_Std_RBNode_fold___at_Lean_Meta_sortFVars___spec__1(x_1, x_3);
x_7 = lean_array_push(x_6, x_4);
x_1 = x_7;
x_2 = x_5;
goto _start;
}
}
}
lean_object* l_Array_qpartition_loop___at_Lean_Meta_sortFVars___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_nat_dec_lt(x_6, x_2);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_8 = lean_array_swap(x_4, x_5, x_2);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = l_Lean_instInhabitedName;
x_11 = lean_array_get(x_10, x_4, x_6);
lean_inc(x_1);
lean_inc(x_3);
x_12 = lean_apply_2(x_1, x_11, x_3);
x_13 = lean_unbox(x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_6, x_14);
lean_dec(x_6);
x_6 = x_15;
goto _start;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_array_swap(x_4, x_5, x_6);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_5, x_18);
lean_dec(x_5);
x_20 = lean_nat_add(x_6, x_18);
lean_dec(x_6);
x_4 = x_17;
x_5 = x_19;
x_6 = x_20;
goto _start;
}
}
}
}
uint8_t l_Array_qsort_sort___at_Lean_Meta_sortFVars___spec__2___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
lean_inc(x_1);
x_4 = l_Lean_LocalContext_get_x21(x_1, x_2);
x_5 = l_Lean_LocalDecl_index(x_4);
lean_dec(x_4);
x_6 = l_Lean_LocalContext_get_x21(x_1, x_3);
x_7 = l_Lean_LocalDecl_index(x_6);
lean_dec(x_6);
x_8 = lean_nat_dec_lt(x_5, x_7);
lean_dec(x_7);
lean_dec(x_5);
return x_8;
}
}
lean_object* l_Array_qsort_sort___at_Lean_Meta_sortFVars___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_15; 
lean_inc(x_1);
x_5 = lean_alloc_closure((void*)(l_Array_qsort_sort___at_Lean_Meta_sortFVars___spec__2___lambda__1___boxed), 3, 1);
lean_closure_set(x_5, 0, x_1);
x_15 = lean_nat_dec_lt(x_3, x_4);
if (x_15 == 0)
{
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_16 = lean_nat_add(x_3, x_4);
x_17 = lean_unsigned_to_nat(2u);
x_18 = lean_nat_div(x_16, x_17);
lean_dec(x_16);
x_49 = l_Lean_instInhabitedName;
x_50 = lean_array_get(x_49, x_2, x_18);
x_51 = lean_array_get(x_49, x_2, x_3);
lean_inc(x_1);
x_52 = l_Lean_LocalContext_get_x21(x_1, x_50);
x_53 = l_Lean_LocalDecl_index(x_52);
lean_dec(x_52);
lean_inc(x_1);
x_54 = l_Lean_LocalContext_get_x21(x_1, x_51);
x_55 = l_Lean_LocalDecl_index(x_54);
lean_dec(x_54);
x_56 = lean_nat_dec_lt(x_53, x_55);
lean_dec(x_55);
lean_dec(x_53);
if (x_56 == 0)
{
x_19 = x_2;
goto block_48;
}
else
{
lean_object* x_57; 
x_57 = lean_array_swap(x_2, x_3, x_18);
x_19 = x_57;
goto block_48;
}
block_48:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_20 = l_Lean_instInhabitedName;
x_21 = lean_array_get(x_20, x_19, x_4);
x_22 = lean_array_get(x_20, x_19, x_3);
lean_inc(x_21);
lean_inc(x_1);
x_23 = l_Lean_LocalContext_get_x21(x_1, x_21);
x_24 = l_Lean_LocalDecl_index(x_23);
lean_dec(x_23);
lean_inc(x_1);
x_25 = l_Lean_LocalContext_get_x21(x_1, x_22);
x_26 = l_Lean_LocalDecl_index(x_25);
lean_dec(x_25);
x_27 = lean_nat_dec_lt(x_24, x_26);
lean_dec(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_28 = lean_array_get(x_20, x_19, x_18);
lean_inc(x_1);
x_29 = l_Lean_LocalContext_get_x21(x_1, x_28);
x_30 = l_Lean_LocalDecl_index(x_29);
lean_dec(x_29);
x_31 = lean_nat_dec_lt(x_30, x_24);
lean_dec(x_24);
lean_dec(x_30);
if (x_31 == 0)
{
lean_object* x_32; 
lean_dec(x_18);
lean_inc_n(x_3, 2);
x_32 = l_Array_qpartition_loop___at_Lean_Meta_sortFVars___spec__3(x_5, x_4, x_21, x_19, x_3, x_3);
x_6 = x_32;
goto block_14;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_21);
x_33 = lean_array_swap(x_19, x_18, x_4);
lean_dec(x_18);
x_34 = lean_array_get(x_20, x_33, x_4);
lean_inc_n(x_3, 2);
x_35 = l_Array_qpartition_loop___at_Lean_Meta_sortFVars___spec__3(x_5, x_4, x_34, x_33, x_3, x_3);
x_6 = x_35;
goto block_14;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
lean_dec(x_24);
lean_dec(x_21);
x_36 = lean_array_swap(x_19, x_3, x_4);
x_37 = lean_array_get(x_20, x_36, x_18);
x_38 = lean_array_get(x_20, x_36, x_4);
lean_inc(x_1);
x_39 = l_Lean_LocalContext_get_x21(x_1, x_37);
x_40 = l_Lean_LocalDecl_index(x_39);
lean_dec(x_39);
lean_inc(x_38);
lean_inc(x_1);
x_41 = l_Lean_LocalContext_get_x21(x_1, x_38);
x_42 = l_Lean_LocalDecl_index(x_41);
lean_dec(x_41);
x_43 = lean_nat_dec_lt(x_40, x_42);
lean_dec(x_42);
lean_dec(x_40);
if (x_43 == 0)
{
lean_object* x_44; 
lean_dec(x_18);
lean_inc_n(x_3, 2);
x_44 = l_Array_qpartition_loop___at_Lean_Meta_sortFVars___spec__3(x_5, x_4, x_38, x_36, x_3, x_3);
x_6 = x_44;
goto block_14;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_38);
x_45 = lean_array_swap(x_36, x_18, x_4);
lean_dec(x_18);
x_46 = lean_array_get(x_20, x_45, x_4);
lean_inc_n(x_3, 2);
x_47 = l_Array_qpartition_loop___at_Lean_Meta_sortFVars___spec__3(x_5, x_4, x_46, x_45, x_3, x_3);
x_6 = x_47;
goto block_14;
}
}
}
}
block_14:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_nat_dec_le(x_4, x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_inc(x_1);
x_10 = l_Array_qsort_sort___at_Lean_Meta_sortFVars___spec__2(x_1, x_8, x_3, x_7);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_7, x_11);
lean_dec(x_7);
x_2 = x_10;
x_3 = x_12;
goto _start;
}
else
{
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
return x_8;
}
}
}
}
lean_object* l_Lean_Meta_sortFVars(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_dec(x_2);
x_8 = l_Array_empty___closed__1;
x_9 = l_Std_RBNode_fold___at_Lean_Meta_sortFVars___spec__1(x_8, x_1);
x_10 = lean_array_get_size(x_9);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_sub(x_10, x_11);
lean_dec(x_10);
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Array_qsort_sort___at_Lean_Meta_sortFVars___spec__2(x_7, x_9, x_13, x_12);
lean_dec(x_12);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_6);
return x_15;
}
}
lean_object* l_Array_qpartition_loop___at_Lean_Meta_sortFVars___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_qpartition_loop___at_Lean_Meta_sortFVars___spec__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Array_qsort_sort___at_Lean_Meta_sortFVars___spec__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Array_qsort_sort___at_Lean_Meta_sortFVars___spec__2___lambda__1(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
lean_object* l_Array_qsort_sort___at_Lean_Meta_sortFVars___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_qsort_sort___at_Lean_Meta_sortFVars___spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
lean_object* l_Lean_Meta_sortFVars___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_sortFVars(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
lean_object* l_Lean_Meta_getFVarsToGeneralize(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_8 = l_Lean_Meta_mkGeneralizationForbiddenSet(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Meta_getFVarSetToGeneralize(x_1, x_9, x_3, x_4, x_5, x_6, x_10);
lean_dec(x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Meta_sortFVars(x_12, x_3, x_4, x_5, x_6, x_13);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_14;
}
else
{
uint8_t x_15; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_15 = !lean_is_exclusive(x_8);
if (x_15 == 0)
{
return x_8;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_8, 0);
x_17 = lean_ctor_get(x_8, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_8);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
lean_object* l_Lean_Meta_getFVarsToGeneralize___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_getFVarsToGeneralize(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Meta_Basic(lean_object*);
lean_object* initialize_Lean_Util_CollectFVars(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Meta_GeneralizeVars(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_CollectFVars(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_getFVarSetToGeneralize___closed__1 = _init_l_Lean_Meta_getFVarSetToGeneralize___closed__1();
lean_mark_persistent(l_Lean_Meta_getFVarSetToGeneralize___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
