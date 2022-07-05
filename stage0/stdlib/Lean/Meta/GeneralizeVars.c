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
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__37___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getFVarSetToGeneralize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_getFVarSetToGeneralize___spec__74___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__26___boxed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_shouldVisit(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_getFVarSetToGeneralize___spec__65___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at_Lean_Meta_getFVarSetToGeneralize___spec__41(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__8(lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__55(lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__18(lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT uint8_t l_Std_PersistentArray_anyMAux___at_Lean_Meta_getFVarSetToGeneralize___spec__16(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_isAuxDecl(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_getFVarSetToGeneralize___spec__71(lean_object*, size_t, size_t, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_getFVarsToGeneralize(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__6(lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT uint8_t l_Std_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__15(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_getFVarSetToGeneralize___closed__1;
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__30___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__12(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_CollectFVars_main(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_fold___at_Lean_Meta_getFVarsToGeneralize___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__34___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_getFVarSetToGeneralize___spec__76___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__50___at_Lean_Meta_getFVarSetToGeneralize___spec__58(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__34(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentArray_anyMAux___at_Lean_Meta_getFVarSetToGeneralize___spec__16___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_getFVarSetToGeneralize___spec__68(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_getFVarSetToGeneralize___spec__74(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at_Lean_Meta_getFVarSetToGeneralize___spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_mkHashSetImp___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_forIn_visit___at_Lean_Meta_mkGeneralizationForbiddenSet_visit___spec__2___at_Lean_Meta_mkGeneralizationForbiddenSet_visit___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__31(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__12___at_Lean_Meta_getFVarSetToGeneralize___spec__20(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentArray_forInAux___at_Lean_Meta_getFVarSetToGeneralize___spec__62___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__19(lean_object*, lean_object*, lean_object*, size_t, size_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__7(lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at_Lean_Meta_getFVarSetToGeneralize___spec__13___at_Lean_Meta_getFVarSetToGeneralize___spec__21(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__56(lean_object*, lean_object*, lean_object*, size_t, size_t);
static lean_object* l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at_Lean_Meta_getFVarSetToGeneralize___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__46(lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_getFVarSetToGeneralize___spec__64___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at_Lean_Meta_getFVarSetToGeneralize___spec__41___at_Lean_Meta_getFVarSetToGeneralize___spec__49(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkGeneralizationForbiddenSet_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__36___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_PersistentArray_anyMAux___at_Lean_Meta_getFVarSetToGeneralize___spec__35(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__46___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__56___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__17(lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__55___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentArray_anyMAux___at_Lean_Meta_getFVarSetToGeneralize___spec__43___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_PersistentArray_anyMAux___at_Lean_Meta_getFVarSetToGeneralize___spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkGeneralizationForbiddenSet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_getFVarSetToGeneralize___spec__70___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
LEAN_EXPORT uint8_t l_Std_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__53(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_quickCmp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__23(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_binderInfo(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__39(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentArray_forInAux___at_Lean_Meta_getFVarSetToGeneralize___spec__67___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at_Lean_Meta_getFVarSetToGeneralize___spec__52___at_Lean_Meta_getFVarSetToGeneralize___spec__60(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getFVarsToGeneralize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentArray_forInAux___at_Lean_Meta_getFVarSetToGeneralize___spec__62(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__38(lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Std_PersistentArray_forIn___at_Lean_Meta_getFVarSetToGeneralize___spec__61(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_getFVarSetToGeneralize___spec__69___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__30(lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Std_RBTree_toArray___at_Lean_Meta_getFVarsToGeneralize___spec__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at_Lean_Meta_getFVarSetToGeneralize___spec__40___at_Lean_Meta_getFVarSetToGeneralize___spec__48(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentArray_forIn___at_Lean_Meta_getFVarSetToGeneralize___spec__72___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_forIn_visit___at_Lean_Meta_mkGeneralizationForbiddenSet_visit___spec__2___at_Lean_Meta_mkGeneralizationForbiddenSet_visit___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__42___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_getFVarSetToGeneralize___spec__68___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentArray_anyMAux___at_Lean_Meta_getFVarSetToGeneralize___spec__27___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at_Lean_Meta_getFVarSetToGeneralize___spec__51(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVars(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__29(lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Std_PersistentArray_forInAux___at_Lean_Meta_getFVarSetToGeneralize___spec__73___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentArray_forInAux___at_Lean_Meta_getFVarSetToGeneralize___spec__62___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_BinderInfo_isInstImplicit(uint8_t);
LEAN_EXPORT lean_object* l_Std_PersistentArray_forIn___at_Lean_Meta_getFVarSetToGeneralize___spec__61___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_PersistentArray_anyMAux___at_Lean_Meta_getFVarSetToGeneralize___spec__27(lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at_Lean_Meta_getFVarSetToGeneralize___spec__13(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__50(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_forIn_visit___at_Lean_Meta_mkGeneralizationForbiddenSet_visit___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentArray_forIn___at_Lean_Meta_getFVarSetToGeneralize___spec__66(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__37(lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Std_PersistentArray_forInAux___at_Lean_Meta_getFVarSetToGeneralize___spec__67(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_LocalDecl_value_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentArray_anyMAux___at_Lean_Meta_getFVarSetToGeneralize___spec__54___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkGeneralizationForbiddenSet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_getFVarSetToGeneralize___spec__69(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__28___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getFVarSetToGeneralize(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_getFVarSetToGeneralize___spec__75___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__57___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__15___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__39___at_Lean_Meta_getFVarSetToGeneralize___spec__47(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_PersistentArray_anyMAux___at_Lean_Meta_getFVarSetToGeneralize___spec__43(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkGeneralizationForbiddenSet_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isMVar(lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_getFVarSetToGeneralize___spec__63___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentArray_forIn___at_Lean_Meta_getFVarSetToGeneralize___spec__66___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__42(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_Meta_sortFVarIds(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkGeneralizationForbiddenSet_visit___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at_Lean_Meta_getFVarSetToGeneralize___spec__2___at_Lean_Meta_getFVarSetToGeneralize___spec__10___closed__1;
LEAN_EXPORT lean_object* l_Std_RBNode_forIn_visit___at_Lean_Meta_mkGeneralizationForbiddenSet_visit___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_PersistentArray_anyMAux___at_Lean_Meta_getFVarSetToGeneralize___spec__54(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at_Lean_Meta_getFVarSetToGeneralize___spec__25(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentArray_forIn___at_Lean_Meta_getFVarSetToGeneralize___spec__72(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_getFVarSetToGeneralize___spec__71___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentArray_forInAux___at_Lean_Meta_getFVarSetToGeneralize___spec__73(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at_Lean_Meta_getFVarSetToGeneralize___spec__3___at_Lean_Meta_getFVarSetToGeneralize___spec__11(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_getFVarSetToGeneralize___spec__63(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at_Lean_Meta_getFVarSetToGeneralize___spec__33(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at_Lean_Meta_getFVarSetToGeneralize___spec__2___at_Lean_Meta_getFVarSetToGeneralize___spec__10(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_RBNode_insert___at_Lean_CollectFVars_State_add___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__28(lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_getFVarSetToGeneralize___spec__76(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getExprMVarAssignment_x3f(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__26(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_RBNode_findCore___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__53___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_quickCmp___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__1___at_Lean_Meta_getFVarSetToGeneralize___spec__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at_Lean_Meta_getFVarSetToGeneralize___spec__14___at_Lean_Meta_getFVarSetToGeneralize___spec__22(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_getFVarSetToGeneralize___spec__64(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at_Lean_Meta_getFVarSetToGeneralize___spec__52(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentArray_forIn___at_Lean_Meta_getFVarSetToGeneralize___spec__61___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__57(lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Std_PersistentArray_forInAux___at_Lean_Meta_getFVarSetToGeneralize___spec__62___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_getFVarSetToGeneralize___spec__70(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at_Lean_Meta_getFVarSetToGeneralize___spec__51___at_Lean_Meta_getFVarSetToGeneralize___spec__59(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_getDecl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at_Lean_Meta_getFVarSetToGeneralize___spec__40(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at_Lean_Meta_getFVarSetToGeneralize___spec__32(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_findCore___at_Lean_Meta_mkGeneralizationForbiddenSet_visit___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_getFVarSetToGeneralize___spec__75(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_mkGeneralizationForbiddenSet___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentArray_anyMAux___at_Lean_Meta_getFVarSetToGeneralize___spec__35___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__44(lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__44___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__45___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__29___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__45(lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_mkGeneralizationForbiddenSet___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__36(lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_mkGeneralizationForbiddenSet_visit___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentArray_forIn___at_Lean_Meta_getFVarSetToGeneralize___spec__61___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at_Lean_Meta_getFVarSetToGeneralize___spec__14(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__38___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at_Lean_Meta_getFVarSetToGeneralize___spec__24(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_getFVarSetToGeneralize___spec__65(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_findCore___at_Lean_Meta_mkGeneralizationForbiddenSet_visit___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentArray_anyMAux___at_Lean_Meta_getFVarSetToGeneralize___spec__5___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__3;
uint8_t l_Lean_LocalDecl_isLet(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_findCore___at_Lean_Meta_mkGeneralizationForbiddenSet_visit___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_ctor_get(x_1, 3);
x_8 = l_Lean_Name_quickCmp(x_2, x_5);
switch (x_8) {
case 0:
{
x_1 = x_4;
goto _start;
}
case 1:
{
lean_object* x_10; lean_object* x_11; 
lean_inc(x_6);
lean_inc(x_5);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_6);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
default: 
{
x_1 = x_7;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_forIn_visit___at_Lean_Meta_mkGeneralizationForbiddenSet_visit___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_3);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 3);
lean_inc(x_13);
lean_dec(x_2);
x_14 = l_Std_RBNode_forIn_visit___at_Lean_Meta_mkGeneralizationForbiddenSet_visit___spec__2(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = !lean_is_exclusive(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_16, 0);
x_20 = lean_ctor_get(x_16, 1);
x_21 = l_Std_RBNode_findCore___at_Lean_Meta_mkGeneralizationForbiddenSet_visit___spec__1(x_19, x_12);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_inc(x_12);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_12);
lean_ctor_set(x_22, 1, x_20);
x_23 = lean_box(0);
x_24 = l_Std_RBNode_insert___at_Lean_CollectFVars_State_add___spec__1(x_19, x_12, x_23);
lean_ctor_set(x_16, 1, x_22);
lean_ctor_set(x_16, 0, x_24);
x_2 = x_13;
x_3 = x_16;
x_8 = x_17;
goto _start;
}
else
{
lean_dec(x_21);
lean_dec(x_12);
x_2 = x_13;
x_3 = x_16;
x_8 = x_17;
goto _start;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_16, 0);
x_28 = lean_ctor_get(x_16, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_16);
x_29 = l_Std_RBNode_findCore___at_Lean_Meta_mkGeneralizationForbiddenSet_visit___spec__1(x_27, x_12);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_inc(x_12);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_12);
lean_ctor_set(x_30, 1, x_28);
x_31 = lean_box(0);
x_32 = l_Std_RBNode_insert___at_Lean_CollectFVars_State_add___spec__1(x_27, x_12, x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_30);
x_2 = x_13;
x_3 = x_33;
x_8 = x_17;
goto _start;
}
else
{
lean_object* x_35; 
lean_dec(x_29);
lean_dec(x_12);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_27);
lean_ctor_set(x_35, 1, x_28);
x_2 = x_13;
x_3 = x_35;
x_8 = x_17;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_forIn_visit___at_Lean_Meta_mkGeneralizationForbiddenSet_visit___spec__2___at_Lean_Meta_mkGeneralizationForbiddenSet_visit___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_13 = l_Std_RBNode_forIn_visit___at_Lean_Meta_mkGeneralizationForbiddenSet_visit___spec__2___at_Lean_Meta_mkGeneralizationForbiddenSet_visit___spec__3(x_10, x_2, x_3, x_4, x_5, x_6, x_7);
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
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_15, 0);
x_19 = lean_ctor_get(x_15, 1);
x_20 = l_Std_RBNode_findCore___at_Lean_Meta_mkGeneralizationForbiddenSet_visit___spec__1(x_18, x_11);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_inc(x_11);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_11);
lean_ctor_set(x_21, 1, x_19);
x_22 = lean_box(0);
x_23 = l_Std_RBNode_insert___at_Lean_CollectFVars_State_add___spec__1(x_18, x_11, x_22);
lean_ctor_set(x_15, 1, x_21);
lean_ctor_set(x_15, 0, x_23);
x_1 = x_12;
x_2 = x_15;
x_7 = x_16;
goto _start;
}
else
{
lean_dec(x_20);
lean_dec(x_11);
x_1 = x_12;
x_2 = x_15;
x_7 = x_16;
goto _start;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_15, 0);
x_27 = lean_ctor_get(x_15, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_15);
x_28 = l_Std_RBNode_findCore___at_Lean_Meta_mkGeneralizationForbiddenSet_visit___spec__1(x_26, x_11);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_inc(x_11);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_11);
lean_ctor_set(x_29, 1, x_27);
x_30 = lean_box(0);
x_31 = l_Std_RBNode_insert___at_Lean_CollectFVars_State_add___spec__1(x_26, x_11, x_30);
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
lean_dec(x_28);
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
LEAN_EXPORT lean_object* l_Lean_Meta_mkGeneralizationForbiddenSet_visit___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
lean_dec(x_3);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_2);
x_12 = l_Std_RBNode_forIn_visit___at_Lean_Meta_mkGeneralizationForbiddenSet_visit___spec__2___at_Lean_Meta_mkGeneralizationForbiddenSet_visit___spec__3(x_10, x_11, x_5, x_6, x_7, x_8, x_9);
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
static lean_object* _init_l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_Std_mkHashSetImp___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1;
x_3 = l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__2;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_1);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkGeneralizationForbiddenSet_visit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_4);
x_9 = l_Lean_Meta_getLocalDecl(x_1, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_LocalDecl_type(x_10);
x_13 = lean_st_ref_get(x_7, x_11);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_st_ref_take(x_5, x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = !lean_is_exclusive(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_19 = lean_ctor_get(x_16, 0);
x_20 = l_Lean_instantiateMVars(x_12, x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_ctor_set(x_16, 0, x_22);
x_23 = lean_st_ref_set(x_5, x_16, x_17);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__3;
x_26 = l_Lean_CollectFVars_main(x_21, x_25);
x_27 = l_Lean_LocalDecl_value_x3f(x_10);
lean_dec(x_10);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_box(0);
x_29 = l_Lean_Meta_mkGeneralizationForbiddenSet_visit___lambda__1(x_3, x_2, x_26, x_28, x_4, x_5, x_6, x_7, x_24);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_30 = lean_ctor_get(x_27, 0);
lean_inc(x_30);
lean_dec(x_27);
x_31 = lean_st_ref_get(x_7, x_24);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_st_ref_take(x_5, x_32);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = !lean_is_exclusive(x_34);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_37 = lean_ctor_get(x_34, 0);
x_38 = l_Lean_instantiateMVars(x_30, x_37);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
lean_ctor_set(x_34, 0, x_40);
x_41 = lean_st_ref_set(x_5, x_34, x_35);
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
lean_dec(x_41);
x_43 = l_Lean_CollectFVars_main(x_39, x_26);
x_44 = lean_box(0);
x_45 = l_Lean_Meta_mkGeneralizationForbiddenSet_visit___lambda__1(x_3, x_2, x_43, x_44, x_4, x_5, x_6, x_7, x_42);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_46 = lean_ctor_get(x_34, 0);
x_47 = lean_ctor_get(x_34, 1);
x_48 = lean_ctor_get(x_34, 2);
x_49 = lean_ctor_get(x_34, 3);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_34);
x_50 = l_Lean_instantiateMVars(x_30, x_46);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_47);
lean_ctor_set(x_53, 2, x_48);
lean_ctor_set(x_53, 3, x_49);
x_54 = lean_st_ref_set(x_5, x_53, x_35);
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
lean_dec(x_54);
x_56 = l_Lean_CollectFVars_main(x_51, x_26);
x_57 = lean_box(0);
x_58 = l_Lean_Meta_mkGeneralizationForbiddenSet_visit___lambda__1(x_3, x_2, x_56, x_57, x_4, x_5, x_6, x_7, x_55);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_58;
}
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_59 = lean_ctor_get(x_16, 0);
x_60 = lean_ctor_get(x_16, 1);
x_61 = lean_ctor_get(x_16, 2);
x_62 = lean_ctor_get(x_16, 3);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_16);
x_63 = l_Lean_instantiateMVars(x_12, x_59);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_66 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_60);
lean_ctor_set(x_66, 2, x_61);
lean_ctor_set(x_66, 3, x_62);
x_67 = lean_st_ref_set(x_5, x_66, x_17);
x_68 = lean_ctor_get(x_67, 1);
lean_inc(x_68);
lean_dec(x_67);
x_69 = l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__3;
x_70 = l_Lean_CollectFVars_main(x_64, x_69);
x_71 = l_Lean_LocalDecl_value_x3f(x_10);
lean_dec(x_10);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_box(0);
x_73 = l_Lean_Meta_mkGeneralizationForbiddenSet_visit___lambda__1(x_3, x_2, x_70, x_72, x_4, x_5, x_6, x_7, x_68);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_73;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_74 = lean_ctor_get(x_71, 0);
lean_inc(x_74);
lean_dec(x_71);
x_75 = lean_st_ref_get(x_7, x_68);
x_76 = lean_ctor_get(x_75, 1);
lean_inc(x_76);
lean_dec(x_75);
x_77 = lean_st_ref_take(x_5, x_76);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
x_80 = lean_ctor_get(x_78, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_78, 1);
lean_inc(x_81);
x_82 = lean_ctor_get(x_78, 2);
lean_inc(x_82);
x_83 = lean_ctor_get(x_78, 3);
lean_inc(x_83);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 lean_ctor_release(x_78, 2);
 lean_ctor_release(x_78, 3);
 x_84 = x_78;
} else {
 lean_dec_ref(x_78);
 x_84 = lean_box(0);
}
x_85 = l_Lean_instantiateMVars(x_74, x_80);
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
lean_dec(x_85);
if (lean_is_scalar(x_84)) {
 x_88 = lean_alloc_ctor(0, 4, 0);
} else {
 x_88 = x_84;
}
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_81);
lean_ctor_set(x_88, 2, x_82);
lean_ctor_set(x_88, 3, x_83);
x_89 = lean_st_ref_set(x_5, x_88, x_79);
x_90 = lean_ctor_get(x_89, 1);
lean_inc(x_90);
lean_dec(x_89);
x_91 = l_Lean_CollectFVars_main(x_86, x_70);
x_92 = lean_box(0);
x_93 = l_Lean_Meta_mkGeneralizationForbiddenSet_visit___lambda__1(x_3, x_2, x_91, x_92, x_4, x_5, x_6, x_7, x_90);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_93;
}
}
}
else
{
uint8_t x_94; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_94 = !lean_is_exclusive(x_9);
if (x_94 == 0)
{
return x_9;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_9, 0);
x_96 = lean_ctor_get(x_9, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_9);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_findCore___at_Lean_Meta_mkGeneralizationForbiddenSet_visit___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_RBNode_findCore___at_Lean_Meta_mkGeneralizationForbiddenSet_visit___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_forIn_visit___at_Lean_Meta_mkGeneralizationForbiddenSet_visit___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Std_RBNode_forIn_visit___at_Lean_Meta_mkGeneralizationForbiddenSet_visit___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_forIn_visit___at_Lean_Meta_mkGeneralizationForbiddenSet_visit___spec__2___at_Lean_Meta_mkGeneralizationForbiddenSet_visit___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_RBNode_forIn_visit___at_Lean_Meta_mkGeneralizationForbiddenSet_visit___spec__2___at_Lean_Meta_mkGeneralizationForbiddenSet_visit___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkGeneralizationForbiddenSet_visit___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_mkGeneralizationForbiddenSet_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
x_11 = l_Std_RBNode_findCore___at_Lean_Meta_mkGeneralizationForbiddenSet_visit___spec__1(x_2, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_box(0);
lean_inc(x_9);
x_13 = l_Std_RBNode_insert___at_Lean_CollectFVars_State_add___spec__1(x_2, x_9, x_12);
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
lean_dec(x_11);
lean_dec(x_9);
x_1 = x_10;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_mkGeneralizationForbiddenSet___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_3, x_2);
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
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_20; 
x_12 = lean_array_uget(x_1, x_3);
x_20 = !lean_is_exclusive(x_4);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_4, 0);
x_22 = lean_ctor_get(x_4, 1);
x_23 = l_Lean_Expr_isFVar(x_12);
if (x_23 == 0)
{
lean_object* x_24; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_24 = lean_infer_type(x_12, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_st_ref_get(x_8, x_26);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_st_ref_take(x_6, x_28);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = !lean_is_exclusive(x_30);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_33 = lean_ctor_get(x_30, 0);
x_34 = l_Lean_instantiateMVars(x_25, x_33);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
lean_ctor_set(x_30, 0, x_36);
x_37 = lean_st_ref_set(x_6, x_30, x_31);
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
lean_dec(x_37);
x_39 = l_Lean_CollectFVars_main(x_35, x_21);
lean_ctor_set(x_4, 0, x_39);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_4);
x_13 = x_40;
x_14 = x_38;
goto block_19;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_41 = lean_ctor_get(x_30, 0);
x_42 = lean_ctor_get(x_30, 1);
x_43 = lean_ctor_get(x_30, 2);
x_44 = lean_ctor_get(x_30, 3);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_30);
x_45 = l_Lean_instantiateMVars(x_25, x_41);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_42);
lean_ctor_set(x_48, 2, x_43);
lean_ctor_set(x_48, 3, x_44);
x_49 = lean_st_ref_set(x_6, x_48, x_31);
x_50 = lean_ctor_get(x_49, 1);
lean_inc(x_50);
lean_dec(x_49);
x_51 = l_Lean_CollectFVars_main(x_46, x_21);
lean_ctor_set(x_4, 0, x_51);
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_4);
x_13 = x_52;
x_14 = x_50;
goto block_19;
}
}
else
{
uint8_t x_53; 
lean_free_object(x_4);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_53 = !lean_is_exclusive(x_24);
if (x_53 == 0)
{
return x_24;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_24, 0);
x_55 = lean_ctor_get(x_24, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_24);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = l_Lean_Expr_fvarId_x21(x_12);
x_58 = lean_array_push(x_22, x_57);
lean_ctor_set(x_4, 1, x_58);
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_4);
x_13 = x_59;
x_14 = x_9;
goto block_19;
}
}
else
{
lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_60 = lean_ctor_get(x_4, 0);
x_61 = lean_ctor_get(x_4, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_4);
x_62 = l_Lean_Expr_isFVar(x_12);
if (x_62 == 0)
{
lean_object* x_63; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_63 = lean_infer_type(x_12, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_66 = lean_st_ref_get(x_8, x_65);
x_67 = lean_ctor_get(x_66, 1);
lean_inc(x_67);
lean_dec(x_66);
x_68 = lean_st_ref_take(x_6, x_67);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_71 = lean_ctor_get(x_69, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_69, 1);
lean_inc(x_72);
x_73 = lean_ctor_get(x_69, 2);
lean_inc(x_73);
x_74 = lean_ctor_get(x_69, 3);
lean_inc(x_74);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 lean_ctor_release(x_69, 2);
 lean_ctor_release(x_69, 3);
 x_75 = x_69;
} else {
 lean_dec_ref(x_69);
 x_75 = lean_box(0);
}
x_76 = l_Lean_instantiateMVars(x_64, x_71);
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
if (lean_is_scalar(x_75)) {
 x_79 = lean_alloc_ctor(0, 4, 0);
} else {
 x_79 = x_75;
}
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_72);
lean_ctor_set(x_79, 2, x_73);
lean_ctor_set(x_79, 3, x_74);
x_80 = lean_st_ref_set(x_6, x_79, x_70);
x_81 = lean_ctor_get(x_80, 1);
lean_inc(x_81);
lean_dec(x_80);
x_82 = l_Lean_CollectFVars_main(x_77, x_60);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_61);
x_84 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_84, 0, x_83);
x_13 = x_84;
x_14 = x_81;
goto block_19;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_85 = lean_ctor_get(x_63, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_63, 1);
lean_inc(x_86);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_87 = x_63;
} else {
 lean_dec_ref(x_63);
 x_87 = lean_box(0);
}
if (lean_is_scalar(x_87)) {
 x_88 = lean_alloc_ctor(1, 2, 0);
} else {
 x_88 = x_87;
}
lean_ctor_set(x_88, 0, x_85);
lean_ctor_set(x_88, 1, x_86);
return x_88;
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_89 = l_Lean_Expr_fvarId_x21(x_12);
x_90 = lean_array_push(x_61, x_89);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_60);
lean_ctor_set(x_91, 1, x_90);
x_92 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_92, 0, x_91);
x_13 = x_92;
x_14 = x_9;
goto block_19;
}
}
block_19:
{
lean_object* x_15; size_t x_16; size_t x_17; 
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = 1;
x_17 = lean_usize_add(x_3, x_16);
x_3 = x_17;
x_4 = x_15;
x_9 = x_14;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkGeneralizationForbiddenSet(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; lean_object* x_15; 
x_8 = l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1;
x_9 = l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__2;
x_10 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_2);
lean_ctor_set(x_10, 2, x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
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
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_mkGeneralizationForbiddenSet___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_mkGeneralizationForbiddenSet___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_mkGeneralizationForbiddenSet(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at_Lean_Meta_getFVarSetToGeneralize___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 5)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_7 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at_Lean_Meta_getFVarSetToGeneralize___spec__3(x_1, x_2, x_5, x_4);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_unbox(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_8);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_dec(x_7);
x_11 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__1(x_1, x_2, x_6, x_10);
return x_11;
}
else
{
uint8_t x_12; 
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_12 = !lean_is_exclusive(x_7);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_7, 0);
lean_dec(x_13);
return x_7;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_7, 1);
lean_inc(x_14);
lean_dec(x_7);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_8);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
else
{
lean_object* x_16; 
x_16 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__1(x_1, x_2, x_3, x_4);
return x_16;
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_uget(x_3, x_4);
lean_inc(x_2);
lean_inc(x_1);
x_8 = l_Std_PersistentArray_anyMAux___at_Lean_Meta_getFVarSetToGeneralize___spec__5(x_1, x_2, x_7);
if (x_8 == 0)
{
size_t x_9; size_t x_10; 
x_9 = 1;
x_10 = lean_usize_add(x_4, x_9);
x_4 = x_10;
goto _start;
}
else
{
uint8_t x_12; 
lean_dec(x_2);
lean_dec(x_1);
x_12 = 1;
return x_12;
}
}
else
{
uint8_t x_13; 
lean_dec(x_2);
lean_dec(x_1);
x_13 = 0;
return x_13;
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_array_uget(x_3, x_4);
if (lean_obj_tag(x_7) == 0)
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = lean_usize_add(x_4, x_8);
x_4 = x_9;
goto _start;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
lean_dec(x_7);
x_12 = l_Lean_LocalDecl_fvarId(x_11);
lean_dec(x_11);
lean_inc(x_2);
lean_inc(x_1);
x_13 = l_Std_RBNode_findCore___rarg(x_1, x_2, x_12);
if (lean_obj_tag(x_13) == 0)
{
size_t x_14; size_t x_15; 
x_14 = 1;
x_15 = lean_usize_add(x_4, x_14);
x_4 = x_15;
goto _start;
}
else
{
uint8_t x_17; 
lean_dec(x_13);
lean_dec(x_2);
lean_dec(x_1);
x_17 = 1;
return x_17;
}
}
}
else
{
uint8_t x_18; 
lean_dec(x_2);
lean_dec(x_1);
x_18 = 0;
return x_18;
}
}
}
LEAN_EXPORT uint8_t l_Std_PersistentArray_anyMAux___at_Lean_Meta_getFVarSetToGeneralize___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_array_get_size(x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_lt(x_6, x_5);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_8 = 0;
return x_8;
}
else
{
uint8_t x_9; 
x_9 = lean_nat_dec_le(x_5, x_5);
if (x_9 == 0)
{
uint8_t x_10; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_10 = 0;
return x_10;
}
else
{
size_t x_11; size_t x_12; uint8_t x_13; 
x_11 = 0;
x_12 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_13 = l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__6(x_1, x_2, x_4, x_11, x_12);
lean_dec(x_4);
return x_13;
}
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_3, 0);
lean_inc(x_14);
lean_dec(x_3);
x_15 = lean_array_get_size(x_14);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_nat_dec_lt(x_16, x_15);
if (x_17 == 0)
{
uint8_t x_18; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_2);
lean_dec(x_1);
x_18 = 0;
return x_18;
}
else
{
uint8_t x_19; 
x_19 = lean_nat_dec_le(x_15, x_15);
if (x_19 == 0)
{
uint8_t x_20; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_2);
lean_dec(x_1);
x_20 = 0;
return x_20;
}
else
{
size_t x_21; size_t x_22; uint8_t x_23; 
x_21 = 0;
x_22 = lean_usize_of_nat(x_15);
lean_dec(x_15);
x_23 = l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__7(x_1, x_2, x_14, x_21, x_22);
lean_dec(x_14);
return x_23;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_array_uget(x_3, x_4);
if (lean_obj_tag(x_7) == 0)
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = lean_usize_add(x_4, x_8);
x_4 = x_9;
goto _start;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
lean_dec(x_7);
x_12 = l_Lean_LocalDecl_fvarId(x_11);
lean_dec(x_11);
lean_inc(x_2);
lean_inc(x_1);
x_13 = l_Std_RBNode_findCore___rarg(x_1, x_2, x_12);
if (lean_obj_tag(x_13) == 0)
{
size_t x_14; size_t x_15; 
x_14 = 1;
x_15 = lean_usize_add(x_4, x_14);
x_4 = x_15;
goto _start;
}
else
{
uint8_t x_17; 
lean_dec(x_13);
lean_dec(x_2);
lean_dec(x_1);
x_17 = 1;
return x_17;
}
}
}
else
{
uint8_t x_18; 
lean_dec(x_2);
lean_dec(x_1);
x_18 = 0;
return x_18;
}
}
}
LEAN_EXPORT uint8_t l_Std_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_5 = l_Std_PersistentArray_anyMAux___at_Lean_Meta_getFVarSetToGeneralize___spec__5(x_1, x_2, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec(x_3);
x_7 = lean_array_get_size(x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_lt(x_8, x_7);
if (x_9 == 0)
{
uint8_t x_10; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_10 = 0;
return x_10;
}
else
{
uint8_t x_11; 
x_11 = lean_nat_dec_le(x_7, x_7);
if (x_11 == 0)
{
uint8_t x_12; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_12 = 0;
return x_12;
}
else
{
size_t x_13; size_t x_14; uint8_t x_15; 
x_13 = 0;
x_14 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_15 = l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__8(x_1, x_2, x_6, x_13, x_14);
lean_dec(x_6);
return x_15;
}
}
}
else
{
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at_Lean_Meta_getFVarSetToGeneralize___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_3)) {
case 1:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
x_6 = l_Std_RBNode_findCore___rarg(x_1, x_2, x_5);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; lean_object* x_8; lean_object* x_9; 
x_7 = 0;
x_8 = lean_box(x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_4);
return x_9;
}
else
{
uint8_t x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_6);
x_10 = 1;
x_11 = lean_box(x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_4);
return x_12;
}
}
case 2:
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_3, 0);
lean_inc(x_13);
lean_dec(x_3);
x_14 = !lean_is_exclusive(x_4);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_4, 1);
lean_inc(x_13);
x_16 = l_Lean_getExprMVarAssignment_x3f(x_13, x_15);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_ctor_set(x_4, 1, x_19);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_20 = l_Lean_MetavarContext_getDecl(x_19, x_13);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = l_Std_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__4(x_1, x_2, x_22);
x_24 = lean_box(x_23);
lean_ctor_set(x_16, 1, x_4);
lean_ctor_set(x_16, 0, x_24);
return x_16;
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_free_object(x_16);
lean_dec(x_19);
lean_dec(x_13);
x_25 = lean_ctor_get(x_18, 0);
lean_inc(x_25);
lean_dec(x_18);
x_26 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__1(x_1, x_2, x_25, x_4);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_16, 0);
x_28 = lean_ctor_get(x_16, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_16);
lean_inc(x_28);
lean_ctor_set(x_4, 1, x_28);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; 
x_29 = l_Lean_MetavarContext_getDecl(x_28, x_13);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec(x_30);
x_32 = l_Std_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__4(x_1, x_2, x_31);
x_33 = lean_box(x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_4);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_28);
lean_dec(x_13);
x_35 = lean_ctor_get(x_27, 0);
lean_inc(x_35);
lean_dec(x_27);
x_36 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__1(x_1, x_2, x_35, x_4);
return x_36;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_37 = lean_ctor_get(x_4, 0);
x_38 = lean_ctor_get(x_4, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_4);
lean_inc(x_13);
x_39 = l_Lean_getExprMVarAssignment_x3f(x_13, x_38);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_42 = x_39;
} else {
 lean_dec_ref(x_39);
 x_42 = lean_box(0);
}
lean_inc(x_41);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_37);
lean_ctor_set(x_43, 1, x_41);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; 
x_44 = l_Lean_MetavarContext_getDecl(x_41, x_13);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
lean_dec(x_45);
x_47 = l_Std_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__4(x_1, x_2, x_46);
x_48 = lean_box(x_47);
if (lean_is_scalar(x_42)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_42;
}
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_43);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; 
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_13);
x_50 = lean_ctor_get(x_40, 0);
lean_inc(x_50);
lean_dec(x_40);
x_51 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__1(x_1, x_2, x_50, x_43);
return x_51;
}
}
}
case 5:
{
lean_object* x_52; uint8_t x_53; 
x_52 = l_Lean_Expr_getAppFn(x_3);
x_53 = l_Lean_Expr_isMVar(x_52);
if (x_53 == 0)
{
lean_object* x_54; 
lean_dec(x_52);
x_54 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at_Lean_Meta_getFVarSetToGeneralize___spec__3(x_1, x_2, x_3, x_4);
return x_54;
}
else
{
uint8_t x_55; 
x_55 = !lean_is_exclusive(x_4);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_56 = lean_ctor_get(x_4, 1);
lean_inc(x_3);
x_57 = l_Lean_instantiateMVars(x_3, x_56);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
lean_ctor_set(x_4, 1, x_59);
x_60 = l_Lean_Expr_getAppFn(x_58);
x_61 = lean_expr_eqv(x_60, x_52);
lean_dec(x_52);
lean_dec(x_60);
if (x_61 == 0)
{
lean_dec(x_3);
x_3 = x_58;
goto _start;
}
else
{
lean_object* x_63; 
lean_dec(x_58);
x_63 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at_Lean_Meta_getFVarSetToGeneralize___spec__3(x_1, x_2, x_3, x_4);
return x_63;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_64 = lean_ctor_get(x_4, 0);
x_65 = lean_ctor_get(x_4, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_4);
lean_inc(x_3);
x_66 = l_Lean_instantiateMVars(x_3, x_65);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_64);
lean_ctor_set(x_69, 1, x_68);
x_70 = l_Lean_Expr_getAppFn(x_67);
x_71 = lean_expr_eqv(x_70, x_52);
lean_dec(x_52);
lean_dec(x_70);
if (x_71 == 0)
{
lean_dec(x_3);
x_3 = x_67;
x_4 = x_69;
goto _start;
}
else
{
lean_object* x_73; 
lean_dec(x_67);
x_73 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at_Lean_Meta_getFVarSetToGeneralize___spec__3(x_1, x_2, x_3, x_69);
return x_73;
}
}
}
}
case 6:
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_74 = lean_ctor_get(x_3, 1);
lean_inc(x_74);
x_75 = lean_ctor_get(x_3, 2);
lean_inc(x_75);
lean_dec(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_76 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__1(x_1, x_2, x_74, x_4);
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_unbox(x_77);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; 
lean_dec(x_77);
x_79 = lean_ctor_get(x_76, 1);
lean_inc(x_79);
lean_dec(x_76);
x_80 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__1(x_1, x_2, x_75, x_79);
return x_80;
}
else
{
uint8_t x_81; 
lean_dec(x_75);
lean_dec(x_2);
lean_dec(x_1);
x_81 = !lean_is_exclusive(x_76);
if (x_81 == 0)
{
lean_object* x_82; 
x_82 = lean_ctor_get(x_76, 0);
lean_dec(x_82);
return x_76;
}
else
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_76, 1);
lean_inc(x_83);
lean_dec(x_76);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_77);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
case 7:
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_85 = lean_ctor_get(x_3, 1);
lean_inc(x_85);
x_86 = lean_ctor_get(x_3, 2);
lean_inc(x_86);
lean_dec(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_87 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__1(x_1, x_2, x_85, x_4);
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_unbox(x_88);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; 
lean_dec(x_88);
x_90 = lean_ctor_get(x_87, 1);
lean_inc(x_90);
lean_dec(x_87);
x_91 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__1(x_1, x_2, x_86, x_90);
return x_91;
}
else
{
uint8_t x_92; 
lean_dec(x_86);
lean_dec(x_2);
lean_dec(x_1);
x_92 = !lean_is_exclusive(x_87);
if (x_92 == 0)
{
lean_object* x_93; 
x_93 = lean_ctor_get(x_87, 0);
lean_dec(x_93);
return x_87;
}
else
{
lean_object* x_94; lean_object* x_95; 
x_94 = lean_ctor_get(x_87, 1);
lean_inc(x_94);
lean_dec(x_87);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_88);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
case 8:
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; 
x_96 = lean_ctor_get(x_3, 1);
lean_inc(x_96);
x_97 = lean_ctor_get(x_3, 2);
lean_inc(x_97);
x_98 = lean_ctor_get(x_3, 3);
lean_inc(x_98);
lean_dec(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_99 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__1(x_1, x_2, x_96, x_4);
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_unbox(x_100);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; 
lean_dec(x_100);
x_102 = lean_ctor_get(x_99, 1);
lean_inc(x_102);
lean_dec(x_99);
lean_inc(x_2);
lean_inc(x_1);
x_103 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__1(x_1, x_2, x_97, x_102);
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_unbox(x_104);
if (x_105 == 0)
{
lean_object* x_106; lean_object* x_107; 
lean_dec(x_104);
x_106 = lean_ctor_get(x_103, 1);
lean_inc(x_106);
lean_dec(x_103);
x_107 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__1(x_1, x_2, x_98, x_106);
return x_107;
}
else
{
uint8_t x_108; 
lean_dec(x_98);
lean_dec(x_2);
lean_dec(x_1);
x_108 = !lean_is_exclusive(x_103);
if (x_108 == 0)
{
lean_object* x_109; 
x_109 = lean_ctor_get(x_103, 0);
lean_dec(x_109);
return x_103;
}
else
{
lean_object* x_110; lean_object* x_111; 
x_110 = lean_ctor_get(x_103, 1);
lean_inc(x_110);
lean_dec(x_103);
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_104);
lean_ctor_set(x_111, 1, x_110);
return x_111;
}
}
}
else
{
uint8_t x_112; 
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_2);
lean_dec(x_1);
x_112 = !lean_is_exclusive(x_99);
if (x_112 == 0)
{
lean_object* x_113; 
x_113 = lean_ctor_get(x_99, 0);
lean_dec(x_113);
return x_99;
}
else
{
lean_object* x_114; lean_object* x_115; 
x_114 = lean_ctor_get(x_99, 1);
lean_inc(x_114);
lean_dec(x_99);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_100);
lean_ctor_set(x_115, 1, x_114);
return x_115;
}
}
}
case 10:
{
lean_object* x_116; lean_object* x_117; 
x_116 = lean_ctor_get(x_3, 1);
lean_inc(x_116);
lean_dec(x_3);
x_117 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__1(x_1, x_2, x_116, x_4);
return x_117;
}
case 11:
{
lean_object* x_118; lean_object* x_119; 
x_118 = lean_ctor_get(x_3, 2);
lean_inc(x_118);
lean_dec(x_3);
x_119 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__1(x_1, x_2, x_118, x_4);
return x_119;
}
default: 
{
uint8_t x_120; lean_object* x_121; lean_object* x_122; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_120 = 0;
x_121 = lean_box(x_120);
x_122 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set(x_122, 1, x_4);
return x_122;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
lean_inc(x_3);
x_5 = l___private_Lean_MetavarContext_0__Lean_DependsOn_shouldVisit(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_unbox(x_6);
lean_dec(x_6);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
x_17 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at_Lean_Meta_getFVarSetToGeneralize___spec__2(x_1, x_2, x_3, x_16);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at_Lean_Meta_getFVarSetToGeneralize___spec__3___at_Lean_Meta_getFVarSetToGeneralize___spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 5)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
lean_inc(x_1);
x_6 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at_Lean_Meta_getFVarSetToGeneralize___spec__3___at_Lean_Meta_getFVarSetToGeneralize___spec__11(x_1, x_4, x_3);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_unbox(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_7);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
lean_dec(x_6);
x_10 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__1___at_Lean_Meta_getFVarSetToGeneralize___spec__9(x_1, x_5, x_9);
return x_10;
}
else
{
uint8_t x_11; 
lean_dec(x_5);
lean_dec(x_1);
x_11 = !lean_is_exclusive(x_6);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_6, 0);
lean_dec(x_12);
return x_6;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_6, 1);
lean_inc(x_13);
lean_dec(x_6);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
else
{
lean_object* x_15; 
x_15 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__1___at_Lean_Meta_getFVarSetToGeneralize___spec__9(x_1, x_2, x_3);
return x_15;
}
}
}
static lean_object* _init_l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at_Lean_Meta_getFVarSetToGeneralize___spec__2___at_Lean_Meta_getFVarSetToGeneralize___spec__10___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Name_quickCmp___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at_Lean_Meta_getFVarSetToGeneralize___spec__2___at_Lean_Meta_getFVarSetToGeneralize___spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 1:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = l_Std_RBNode_findCore___at_Lean_Meta_mkGeneralizationForbiddenSet_visit___spec__1(x_1, x_4);
lean_dec(x_4);
lean_dec(x_1);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_6 = 0;
x_7 = lean_box(x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
else
{
uint8_t x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
x_9 = 1;
x_10 = lean_box(x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_3);
return x_11;
}
}
case 2:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
lean_dec(x_2);
x_13 = !lean_is_exclusive(x_3);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
x_15 = l_Lean_getExprMVarAssignment_x3f(x_12, x_14);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_ctor_set(x_3, 1, x_18);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_19 = l_Lean_MetavarContext_getDecl(x_18, x_12);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at_Lean_Meta_getFVarSetToGeneralize___spec__2___at_Lean_Meta_getFVarSetToGeneralize___spec__10___closed__1;
x_23 = l_Std_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__4(x_22, x_1, x_21);
x_24 = lean_box(x_23);
lean_ctor_set(x_15, 1, x_3);
lean_ctor_set(x_15, 0, x_24);
return x_15;
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_free_object(x_15);
lean_dec(x_18);
lean_dec(x_12);
x_25 = lean_ctor_get(x_17, 0);
lean_inc(x_25);
lean_dec(x_17);
x_26 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__1___at_Lean_Meta_getFVarSetToGeneralize___spec__9(x_1, x_25, x_3);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_15, 0);
x_28 = lean_ctor_get(x_15, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_15);
lean_inc(x_28);
lean_ctor_set(x_3, 1, x_28);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; 
x_29 = l_Lean_MetavarContext_getDecl(x_28, x_12);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec(x_30);
x_32 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at_Lean_Meta_getFVarSetToGeneralize___spec__2___at_Lean_Meta_getFVarSetToGeneralize___spec__10___closed__1;
x_33 = l_Std_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__4(x_32, x_1, x_31);
x_34 = lean_box(x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_3);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_28);
lean_dec(x_12);
x_36 = lean_ctor_get(x_27, 0);
lean_inc(x_36);
lean_dec(x_27);
x_37 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__1___at_Lean_Meta_getFVarSetToGeneralize___spec__9(x_1, x_36, x_3);
return x_37;
}
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_38 = lean_ctor_get(x_3, 0);
x_39 = lean_ctor_get(x_3, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_3);
lean_inc(x_12);
x_40 = l_Lean_getExprMVarAssignment_x3f(x_12, x_39);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_43 = x_40;
} else {
 lean_dec_ref(x_40);
 x_43 = lean_box(0);
}
lean_inc(x_42);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_38);
lean_ctor_set(x_44, 1, x_42);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; 
x_45 = l_Lean_MetavarContext_getDecl(x_42, x_12);
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
lean_dec(x_45);
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
lean_dec(x_46);
x_48 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at_Lean_Meta_getFVarSetToGeneralize___spec__2___at_Lean_Meta_getFVarSetToGeneralize___spec__10___closed__1;
x_49 = l_Std_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__4(x_48, x_1, x_47);
x_50 = lean_box(x_49);
if (lean_is_scalar(x_43)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_43;
}
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_44);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; 
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_12);
x_52 = lean_ctor_get(x_41, 0);
lean_inc(x_52);
lean_dec(x_41);
x_53 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__1___at_Lean_Meta_getFVarSetToGeneralize___spec__9(x_1, x_52, x_44);
return x_53;
}
}
}
case 5:
{
lean_object* x_54; uint8_t x_55; 
x_54 = l_Lean_Expr_getAppFn(x_2);
x_55 = l_Lean_Expr_isMVar(x_54);
if (x_55 == 0)
{
lean_object* x_56; 
lean_dec(x_54);
x_56 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at_Lean_Meta_getFVarSetToGeneralize___spec__3___at_Lean_Meta_getFVarSetToGeneralize___spec__11(x_1, x_2, x_3);
return x_56;
}
else
{
uint8_t x_57; 
x_57 = !lean_is_exclusive(x_3);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_58 = lean_ctor_get(x_3, 1);
lean_inc(x_2);
x_59 = l_Lean_instantiateMVars(x_2, x_58);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
lean_ctor_set(x_3, 1, x_61);
x_62 = l_Lean_Expr_getAppFn(x_60);
x_63 = lean_expr_eqv(x_62, x_54);
lean_dec(x_54);
lean_dec(x_62);
if (x_63 == 0)
{
lean_dec(x_2);
x_2 = x_60;
goto _start;
}
else
{
lean_object* x_65; 
lean_dec(x_60);
x_65 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at_Lean_Meta_getFVarSetToGeneralize___spec__3___at_Lean_Meta_getFVarSetToGeneralize___spec__11(x_1, x_2, x_3);
return x_65;
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_66 = lean_ctor_get(x_3, 0);
x_67 = lean_ctor_get(x_3, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_3);
lean_inc(x_2);
x_68 = l_Lean_instantiateMVars(x_2, x_67);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_66);
lean_ctor_set(x_71, 1, x_70);
x_72 = l_Lean_Expr_getAppFn(x_69);
x_73 = lean_expr_eqv(x_72, x_54);
lean_dec(x_54);
lean_dec(x_72);
if (x_73 == 0)
{
lean_dec(x_2);
x_2 = x_69;
x_3 = x_71;
goto _start;
}
else
{
lean_object* x_75; 
lean_dec(x_69);
x_75 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at_Lean_Meta_getFVarSetToGeneralize___spec__3___at_Lean_Meta_getFVarSetToGeneralize___spec__11(x_1, x_2, x_71);
return x_75;
}
}
}
}
case 6:
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_76 = lean_ctor_get(x_2, 1);
lean_inc(x_76);
x_77 = lean_ctor_get(x_2, 2);
lean_inc(x_77);
lean_dec(x_2);
lean_inc(x_1);
x_78 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__1___at_Lean_Meta_getFVarSetToGeneralize___spec__9(x_1, x_76, x_3);
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_unbox(x_79);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; 
lean_dec(x_79);
x_81 = lean_ctor_get(x_78, 1);
lean_inc(x_81);
lean_dec(x_78);
x_82 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__1___at_Lean_Meta_getFVarSetToGeneralize___spec__9(x_1, x_77, x_81);
return x_82;
}
else
{
uint8_t x_83; 
lean_dec(x_77);
lean_dec(x_1);
x_83 = !lean_is_exclusive(x_78);
if (x_83 == 0)
{
lean_object* x_84; 
x_84 = lean_ctor_get(x_78, 0);
lean_dec(x_84);
return x_78;
}
else
{
lean_object* x_85; lean_object* x_86; 
x_85 = lean_ctor_get(x_78, 1);
lean_inc(x_85);
lean_dec(x_78);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_79);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
}
case 7:
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; 
x_87 = lean_ctor_get(x_2, 1);
lean_inc(x_87);
x_88 = lean_ctor_get(x_2, 2);
lean_inc(x_88);
lean_dec(x_2);
lean_inc(x_1);
x_89 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__1___at_Lean_Meta_getFVarSetToGeneralize___spec__9(x_1, x_87, x_3);
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_unbox(x_90);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; 
lean_dec(x_90);
x_92 = lean_ctor_get(x_89, 1);
lean_inc(x_92);
lean_dec(x_89);
x_93 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__1___at_Lean_Meta_getFVarSetToGeneralize___spec__9(x_1, x_88, x_92);
return x_93;
}
else
{
uint8_t x_94; 
lean_dec(x_88);
lean_dec(x_1);
x_94 = !lean_is_exclusive(x_89);
if (x_94 == 0)
{
lean_object* x_95; 
x_95 = lean_ctor_get(x_89, 0);
lean_dec(x_95);
return x_89;
}
else
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_ctor_get(x_89, 1);
lean_inc(x_96);
lean_dec(x_89);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_90);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
}
case 8:
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_98 = lean_ctor_get(x_2, 1);
lean_inc(x_98);
x_99 = lean_ctor_get(x_2, 2);
lean_inc(x_99);
x_100 = lean_ctor_get(x_2, 3);
lean_inc(x_100);
lean_dec(x_2);
lean_inc(x_1);
x_101 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__1___at_Lean_Meta_getFVarSetToGeneralize___spec__9(x_1, x_98, x_3);
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_unbox(x_102);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; 
lean_dec(x_102);
x_104 = lean_ctor_get(x_101, 1);
lean_inc(x_104);
lean_dec(x_101);
lean_inc(x_1);
x_105 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__1___at_Lean_Meta_getFVarSetToGeneralize___spec__9(x_1, x_99, x_104);
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_unbox(x_106);
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; 
lean_dec(x_106);
x_108 = lean_ctor_get(x_105, 1);
lean_inc(x_108);
lean_dec(x_105);
x_109 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__1___at_Lean_Meta_getFVarSetToGeneralize___spec__9(x_1, x_100, x_108);
return x_109;
}
else
{
uint8_t x_110; 
lean_dec(x_100);
lean_dec(x_1);
x_110 = !lean_is_exclusive(x_105);
if (x_110 == 0)
{
lean_object* x_111; 
x_111 = lean_ctor_get(x_105, 0);
lean_dec(x_111);
return x_105;
}
else
{
lean_object* x_112; lean_object* x_113; 
x_112 = lean_ctor_get(x_105, 1);
lean_inc(x_112);
lean_dec(x_105);
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_106);
lean_ctor_set(x_113, 1, x_112);
return x_113;
}
}
}
else
{
uint8_t x_114; 
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_1);
x_114 = !lean_is_exclusive(x_101);
if (x_114 == 0)
{
lean_object* x_115; 
x_115 = lean_ctor_get(x_101, 0);
lean_dec(x_115);
return x_101;
}
else
{
lean_object* x_116; lean_object* x_117; 
x_116 = lean_ctor_get(x_101, 1);
lean_inc(x_116);
lean_dec(x_101);
x_117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_117, 0, x_102);
lean_ctor_set(x_117, 1, x_116);
return x_117;
}
}
}
case 10:
{
lean_object* x_118; lean_object* x_119; 
x_118 = lean_ctor_get(x_2, 1);
lean_inc(x_118);
lean_dec(x_2);
x_119 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__1___at_Lean_Meta_getFVarSetToGeneralize___spec__9(x_1, x_118, x_3);
return x_119;
}
case 11:
{
lean_object* x_120; lean_object* x_121; 
x_120 = lean_ctor_get(x_2, 2);
lean_inc(x_120);
lean_dec(x_2);
x_121 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__1___at_Lean_Meta_getFVarSetToGeneralize___spec__9(x_1, x_120, x_3);
return x_121;
}
default: 
{
uint8_t x_122; lean_object* x_123; lean_object* x_124; 
lean_dec(x_2);
lean_dec(x_1);
x_122 = 0;
x_123 = lean_box(x_122);
x_124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_3);
return x_124;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__1___at_Lean_Meta_getFVarSetToGeneralize___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
lean_inc(x_2);
x_4 = l___private_Lean_MetavarContext_0__Lean_DependsOn_shouldVisit(x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_unbox(x_5);
lean_dec(x_5);
if (x_6 == 0)
{
uint8_t x_7; 
lean_dec(x_2);
lean_dec(x_1);
x_7 = !lean_is_exclusive(x_4);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_4, 0);
lean_dec(x_8);
x_9 = 0;
x_10 = lean_box(x_9);
lean_ctor_set(x_4, 0, x_10);
return x_4;
}
else
{
lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_4, 1);
lean_inc(x_11);
lean_dec(x_4);
x_12 = 0;
x_13 = lean_box(x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_4, 1);
lean_inc(x_15);
lean_dec(x_4);
x_16 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at_Lean_Meta_getFVarSetToGeneralize___spec__2___at_Lean_Meta_getFVarSetToGeneralize___spec__10(x_1, x_2, x_15);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at_Lean_Meta_getFVarSetToGeneralize___spec__14(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 5)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_7 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at_Lean_Meta_getFVarSetToGeneralize___spec__14(x_1, x_2, x_5, x_4);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_unbox(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_8);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_dec(x_7);
x_11 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__12(x_1, x_2, x_6, x_10);
return x_11;
}
else
{
uint8_t x_12; 
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_12 = !lean_is_exclusive(x_7);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_7, 0);
lean_dec(x_13);
return x_7;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_7, 1);
lean_inc(x_14);
lean_dec(x_7);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_8);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
else
{
lean_object* x_16; 
x_16 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__12(x_1, x_2, x_3, x_4);
return x_16;
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__17(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_uget(x_3, x_4);
lean_inc(x_2);
lean_inc(x_1);
x_8 = l_Std_PersistentArray_anyMAux___at_Lean_Meta_getFVarSetToGeneralize___spec__16(x_1, x_2, x_7);
if (x_8 == 0)
{
size_t x_9; size_t x_10; 
x_9 = 1;
x_10 = lean_usize_add(x_4, x_9);
x_4 = x_10;
goto _start;
}
else
{
uint8_t x_12; 
lean_dec(x_2);
lean_dec(x_1);
x_12 = 1;
return x_12;
}
}
else
{
uint8_t x_13; 
lean_dec(x_2);
lean_dec(x_1);
x_13 = 0;
return x_13;
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__18(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_array_uget(x_3, x_4);
if (lean_obj_tag(x_7) == 0)
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = lean_usize_add(x_4, x_8);
x_4 = x_9;
goto _start;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
lean_dec(x_7);
x_12 = l_Lean_LocalDecl_fvarId(x_11);
lean_dec(x_11);
lean_inc(x_2);
lean_inc(x_1);
x_13 = l_Std_RBNode_findCore___rarg(x_1, x_2, x_12);
if (lean_obj_tag(x_13) == 0)
{
size_t x_14; size_t x_15; 
x_14 = 1;
x_15 = lean_usize_add(x_4, x_14);
x_4 = x_15;
goto _start;
}
else
{
uint8_t x_17; 
lean_dec(x_13);
lean_dec(x_2);
lean_dec(x_1);
x_17 = 1;
return x_17;
}
}
}
else
{
uint8_t x_18; 
lean_dec(x_2);
lean_dec(x_1);
x_18 = 0;
return x_18;
}
}
}
LEAN_EXPORT uint8_t l_Std_PersistentArray_anyMAux___at_Lean_Meta_getFVarSetToGeneralize___spec__16(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_array_get_size(x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_lt(x_6, x_5);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_8 = 0;
return x_8;
}
else
{
uint8_t x_9; 
x_9 = lean_nat_dec_le(x_5, x_5);
if (x_9 == 0)
{
uint8_t x_10; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_10 = 0;
return x_10;
}
else
{
size_t x_11; size_t x_12; uint8_t x_13; 
x_11 = 0;
x_12 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_13 = l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__17(x_1, x_2, x_4, x_11, x_12);
lean_dec(x_4);
return x_13;
}
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_3, 0);
lean_inc(x_14);
lean_dec(x_3);
x_15 = lean_array_get_size(x_14);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_nat_dec_lt(x_16, x_15);
if (x_17 == 0)
{
uint8_t x_18; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_2);
lean_dec(x_1);
x_18 = 0;
return x_18;
}
else
{
uint8_t x_19; 
x_19 = lean_nat_dec_le(x_15, x_15);
if (x_19 == 0)
{
uint8_t x_20; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_2);
lean_dec(x_1);
x_20 = 0;
return x_20;
}
else
{
size_t x_21; size_t x_22; uint8_t x_23; 
x_21 = 0;
x_22 = lean_usize_of_nat(x_15);
lean_dec(x_15);
x_23 = l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__18(x_1, x_2, x_14, x_21, x_22);
lean_dec(x_14);
return x_23;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__19(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_array_uget(x_3, x_4);
if (lean_obj_tag(x_7) == 0)
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = lean_usize_add(x_4, x_8);
x_4 = x_9;
goto _start;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
lean_dec(x_7);
x_12 = l_Lean_LocalDecl_fvarId(x_11);
lean_dec(x_11);
lean_inc(x_2);
lean_inc(x_1);
x_13 = l_Std_RBNode_findCore___rarg(x_1, x_2, x_12);
if (lean_obj_tag(x_13) == 0)
{
size_t x_14; size_t x_15; 
x_14 = 1;
x_15 = lean_usize_add(x_4, x_14);
x_4 = x_15;
goto _start;
}
else
{
uint8_t x_17; 
lean_dec(x_13);
lean_dec(x_2);
lean_dec(x_1);
x_17 = 1;
return x_17;
}
}
}
else
{
uint8_t x_18; 
lean_dec(x_2);
lean_dec(x_1);
x_18 = 0;
return x_18;
}
}
}
LEAN_EXPORT uint8_t l_Std_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__15(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_5 = l_Std_PersistentArray_anyMAux___at_Lean_Meta_getFVarSetToGeneralize___spec__16(x_1, x_2, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec(x_3);
x_7 = lean_array_get_size(x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_lt(x_8, x_7);
if (x_9 == 0)
{
uint8_t x_10; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_10 = 0;
return x_10;
}
else
{
uint8_t x_11; 
x_11 = lean_nat_dec_le(x_7, x_7);
if (x_11 == 0)
{
uint8_t x_12; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_12 = 0;
return x_12;
}
else
{
size_t x_13; size_t x_14; uint8_t x_15; 
x_13 = 0;
x_14 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_15 = l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__19(x_1, x_2, x_6, x_13, x_14);
lean_dec(x_6);
return x_15;
}
}
}
else
{
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at_Lean_Meta_getFVarSetToGeneralize___spec__13(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_3)) {
case 1:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
x_6 = l_Std_RBNode_findCore___rarg(x_1, x_2, x_5);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; lean_object* x_8; lean_object* x_9; 
x_7 = 0;
x_8 = lean_box(x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_4);
return x_9;
}
else
{
uint8_t x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_6);
x_10 = 1;
x_11 = lean_box(x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_4);
return x_12;
}
}
case 2:
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_3, 0);
lean_inc(x_13);
lean_dec(x_3);
x_14 = !lean_is_exclusive(x_4);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_4, 1);
lean_inc(x_13);
x_16 = l_Lean_getExprMVarAssignment_x3f(x_13, x_15);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_ctor_set(x_4, 1, x_19);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_20 = l_Lean_MetavarContext_getDecl(x_19, x_13);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = l_Std_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__15(x_1, x_2, x_22);
x_24 = lean_box(x_23);
lean_ctor_set(x_16, 1, x_4);
lean_ctor_set(x_16, 0, x_24);
return x_16;
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_free_object(x_16);
lean_dec(x_19);
lean_dec(x_13);
x_25 = lean_ctor_get(x_18, 0);
lean_inc(x_25);
lean_dec(x_18);
x_26 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__12(x_1, x_2, x_25, x_4);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_16, 0);
x_28 = lean_ctor_get(x_16, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_16);
lean_inc(x_28);
lean_ctor_set(x_4, 1, x_28);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; 
x_29 = l_Lean_MetavarContext_getDecl(x_28, x_13);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec(x_30);
x_32 = l_Std_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__15(x_1, x_2, x_31);
x_33 = lean_box(x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_4);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_28);
lean_dec(x_13);
x_35 = lean_ctor_get(x_27, 0);
lean_inc(x_35);
lean_dec(x_27);
x_36 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__12(x_1, x_2, x_35, x_4);
return x_36;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_37 = lean_ctor_get(x_4, 0);
x_38 = lean_ctor_get(x_4, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_4);
lean_inc(x_13);
x_39 = l_Lean_getExprMVarAssignment_x3f(x_13, x_38);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_42 = x_39;
} else {
 lean_dec_ref(x_39);
 x_42 = lean_box(0);
}
lean_inc(x_41);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_37);
lean_ctor_set(x_43, 1, x_41);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; 
x_44 = l_Lean_MetavarContext_getDecl(x_41, x_13);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
lean_dec(x_45);
x_47 = l_Std_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__15(x_1, x_2, x_46);
x_48 = lean_box(x_47);
if (lean_is_scalar(x_42)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_42;
}
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_43);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; 
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_13);
x_50 = lean_ctor_get(x_40, 0);
lean_inc(x_50);
lean_dec(x_40);
x_51 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__12(x_1, x_2, x_50, x_43);
return x_51;
}
}
}
case 5:
{
lean_object* x_52; uint8_t x_53; 
x_52 = l_Lean_Expr_getAppFn(x_3);
x_53 = l_Lean_Expr_isMVar(x_52);
if (x_53 == 0)
{
lean_object* x_54; 
lean_dec(x_52);
x_54 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at_Lean_Meta_getFVarSetToGeneralize___spec__14(x_1, x_2, x_3, x_4);
return x_54;
}
else
{
uint8_t x_55; 
x_55 = !lean_is_exclusive(x_4);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_56 = lean_ctor_get(x_4, 1);
lean_inc(x_3);
x_57 = l_Lean_instantiateMVars(x_3, x_56);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
lean_ctor_set(x_4, 1, x_59);
x_60 = l_Lean_Expr_getAppFn(x_58);
x_61 = lean_expr_eqv(x_60, x_52);
lean_dec(x_52);
lean_dec(x_60);
if (x_61 == 0)
{
lean_dec(x_3);
x_3 = x_58;
goto _start;
}
else
{
lean_object* x_63; 
lean_dec(x_58);
x_63 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at_Lean_Meta_getFVarSetToGeneralize___spec__14(x_1, x_2, x_3, x_4);
return x_63;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_64 = lean_ctor_get(x_4, 0);
x_65 = lean_ctor_get(x_4, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_4);
lean_inc(x_3);
x_66 = l_Lean_instantiateMVars(x_3, x_65);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_64);
lean_ctor_set(x_69, 1, x_68);
x_70 = l_Lean_Expr_getAppFn(x_67);
x_71 = lean_expr_eqv(x_70, x_52);
lean_dec(x_52);
lean_dec(x_70);
if (x_71 == 0)
{
lean_dec(x_3);
x_3 = x_67;
x_4 = x_69;
goto _start;
}
else
{
lean_object* x_73; 
lean_dec(x_67);
x_73 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at_Lean_Meta_getFVarSetToGeneralize___spec__14(x_1, x_2, x_3, x_69);
return x_73;
}
}
}
}
case 6:
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_74 = lean_ctor_get(x_3, 1);
lean_inc(x_74);
x_75 = lean_ctor_get(x_3, 2);
lean_inc(x_75);
lean_dec(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_76 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__12(x_1, x_2, x_74, x_4);
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_unbox(x_77);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; 
lean_dec(x_77);
x_79 = lean_ctor_get(x_76, 1);
lean_inc(x_79);
lean_dec(x_76);
x_80 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__12(x_1, x_2, x_75, x_79);
return x_80;
}
else
{
uint8_t x_81; 
lean_dec(x_75);
lean_dec(x_2);
lean_dec(x_1);
x_81 = !lean_is_exclusive(x_76);
if (x_81 == 0)
{
lean_object* x_82; 
x_82 = lean_ctor_get(x_76, 0);
lean_dec(x_82);
return x_76;
}
else
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_76, 1);
lean_inc(x_83);
lean_dec(x_76);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_77);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
case 7:
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_85 = lean_ctor_get(x_3, 1);
lean_inc(x_85);
x_86 = lean_ctor_get(x_3, 2);
lean_inc(x_86);
lean_dec(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_87 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__12(x_1, x_2, x_85, x_4);
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_unbox(x_88);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; 
lean_dec(x_88);
x_90 = lean_ctor_get(x_87, 1);
lean_inc(x_90);
lean_dec(x_87);
x_91 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__12(x_1, x_2, x_86, x_90);
return x_91;
}
else
{
uint8_t x_92; 
lean_dec(x_86);
lean_dec(x_2);
lean_dec(x_1);
x_92 = !lean_is_exclusive(x_87);
if (x_92 == 0)
{
lean_object* x_93; 
x_93 = lean_ctor_get(x_87, 0);
lean_dec(x_93);
return x_87;
}
else
{
lean_object* x_94; lean_object* x_95; 
x_94 = lean_ctor_get(x_87, 1);
lean_inc(x_94);
lean_dec(x_87);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_88);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
case 8:
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; 
x_96 = lean_ctor_get(x_3, 1);
lean_inc(x_96);
x_97 = lean_ctor_get(x_3, 2);
lean_inc(x_97);
x_98 = lean_ctor_get(x_3, 3);
lean_inc(x_98);
lean_dec(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_99 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__12(x_1, x_2, x_96, x_4);
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_unbox(x_100);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; 
lean_dec(x_100);
x_102 = lean_ctor_get(x_99, 1);
lean_inc(x_102);
lean_dec(x_99);
lean_inc(x_2);
lean_inc(x_1);
x_103 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__12(x_1, x_2, x_97, x_102);
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_unbox(x_104);
if (x_105 == 0)
{
lean_object* x_106; lean_object* x_107; 
lean_dec(x_104);
x_106 = lean_ctor_get(x_103, 1);
lean_inc(x_106);
lean_dec(x_103);
x_107 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__12(x_1, x_2, x_98, x_106);
return x_107;
}
else
{
uint8_t x_108; 
lean_dec(x_98);
lean_dec(x_2);
lean_dec(x_1);
x_108 = !lean_is_exclusive(x_103);
if (x_108 == 0)
{
lean_object* x_109; 
x_109 = lean_ctor_get(x_103, 0);
lean_dec(x_109);
return x_103;
}
else
{
lean_object* x_110; lean_object* x_111; 
x_110 = lean_ctor_get(x_103, 1);
lean_inc(x_110);
lean_dec(x_103);
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_104);
lean_ctor_set(x_111, 1, x_110);
return x_111;
}
}
}
else
{
uint8_t x_112; 
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_2);
lean_dec(x_1);
x_112 = !lean_is_exclusive(x_99);
if (x_112 == 0)
{
lean_object* x_113; 
x_113 = lean_ctor_get(x_99, 0);
lean_dec(x_113);
return x_99;
}
else
{
lean_object* x_114; lean_object* x_115; 
x_114 = lean_ctor_get(x_99, 1);
lean_inc(x_114);
lean_dec(x_99);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_100);
lean_ctor_set(x_115, 1, x_114);
return x_115;
}
}
}
case 10:
{
lean_object* x_116; lean_object* x_117; 
x_116 = lean_ctor_get(x_3, 1);
lean_inc(x_116);
lean_dec(x_3);
x_117 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__12(x_1, x_2, x_116, x_4);
return x_117;
}
case 11:
{
lean_object* x_118; lean_object* x_119; 
x_118 = lean_ctor_get(x_3, 2);
lean_inc(x_118);
lean_dec(x_3);
x_119 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__12(x_1, x_2, x_118, x_4);
return x_119;
}
default: 
{
uint8_t x_120; lean_object* x_121; lean_object* x_122; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_120 = 0;
x_121 = lean_box(x_120);
x_122 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set(x_122, 1, x_4);
return x_122;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
lean_inc(x_3);
x_5 = l___private_Lean_MetavarContext_0__Lean_DependsOn_shouldVisit(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_unbox(x_6);
lean_dec(x_6);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
x_17 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at_Lean_Meta_getFVarSetToGeneralize___spec__13(x_1, x_2, x_3, x_16);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at_Lean_Meta_getFVarSetToGeneralize___spec__14___at_Lean_Meta_getFVarSetToGeneralize___spec__22(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 5)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
lean_inc(x_1);
x_6 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at_Lean_Meta_getFVarSetToGeneralize___spec__14___at_Lean_Meta_getFVarSetToGeneralize___spec__22(x_1, x_4, x_3);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_unbox(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_7);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
lean_dec(x_6);
x_10 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__12___at_Lean_Meta_getFVarSetToGeneralize___spec__20(x_1, x_5, x_9);
return x_10;
}
else
{
uint8_t x_11; 
lean_dec(x_5);
lean_dec(x_1);
x_11 = !lean_is_exclusive(x_6);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_6, 0);
lean_dec(x_12);
return x_6;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_6, 1);
lean_inc(x_13);
lean_dec(x_6);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
else
{
lean_object* x_15; 
x_15 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__12___at_Lean_Meta_getFVarSetToGeneralize___spec__20(x_1, x_2, x_3);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at_Lean_Meta_getFVarSetToGeneralize___spec__13___at_Lean_Meta_getFVarSetToGeneralize___spec__21(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 1:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = l_Std_RBNode_findCore___at_Lean_Meta_mkGeneralizationForbiddenSet_visit___spec__1(x_1, x_4);
lean_dec(x_4);
lean_dec(x_1);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_6 = 0;
x_7 = lean_box(x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
else
{
uint8_t x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
x_9 = 1;
x_10 = lean_box(x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_3);
return x_11;
}
}
case 2:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
lean_dec(x_2);
x_13 = !lean_is_exclusive(x_3);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
x_15 = l_Lean_getExprMVarAssignment_x3f(x_12, x_14);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_ctor_set(x_3, 1, x_18);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_19 = l_Lean_MetavarContext_getDecl(x_18, x_12);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at_Lean_Meta_getFVarSetToGeneralize___spec__2___at_Lean_Meta_getFVarSetToGeneralize___spec__10___closed__1;
x_23 = l_Std_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__15(x_22, x_1, x_21);
x_24 = lean_box(x_23);
lean_ctor_set(x_15, 1, x_3);
lean_ctor_set(x_15, 0, x_24);
return x_15;
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_free_object(x_15);
lean_dec(x_18);
lean_dec(x_12);
x_25 = lean_ctor_get(x_17, 0);
lean_inc(x_25);
lean_dec(x_17);
x_26 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__12___at_Lean_Meta_getFVarSetToGeneralize___spec__20(x_1, x_25, x_3);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_15, 0);
x_28 = lean_ctor_get(x_15, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_15);
lean_inc(x_28);
lean_ctor_set(x_3, 1, x_28);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; 
x_29 = l_Lean_MetavarContext_getDecl(x_28, x_12);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec(x_30);
x_32 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at_Lean_Meta_getFVarSetToGeneralize___spec__2___at_Lean_Meta_getFVarSetToGeneralize___spec__10___closed__1;
x_33 = l_Std_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__15(x_32, x_1, x_31);
x_34 = lean_box(x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_3);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_28);
lean_dec(x_12);
x_36 = lean_ctor_get(x_27, 0);
lean_inc(x_36);
lean_dec(x_27);
x_37 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__12___at_Lean_Meta_getFVarSetToGeneralize___spec__20(x_1, x_36, x_3);
return x_37;
}
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_38 = lean_ctor_get(x_3, 0);
x_39 = lean_ctor_get(x_3, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_3);
lean_inc(x_12);
x_40 = l_Lean_getExprMVarAssignment_x3f(x_12, x_39);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_43 = x_40;
} else {
 lean_dec_ref(x_40);
 x_43 = lean_box(0);
}
lean_inc(x_42);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_38);
lean_ctor_set(x_44, 1, x_42);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; 
x_45 = l_Lean_MetavarContext_getDecl(x_42, x_12);
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
lean_dec(x_45);
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
lean_dec(x_46);
x_48 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at_Lean_Meta_getFVarSetToGeneralize___spec__2___at_Lean_Meta_getFVarSetToGeneralize___spec__10___closed__1;
x_49 = l_Std_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__15(x_48, x_1, x_47);
x_50 = lean_box(x_49);
if (lean_is_scalar(x_43)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_43;
}
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_44);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; 
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_12);
x_52 = lean_ctor_get(x_41, 0);
lean_inc(x_52);
lean_dec(x_41);
x_53 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__12___at_Lean_Meta_getFVarSetToGeneralize___spec__20(x_1, x_52, x_44);
return x_53;
}
}
}
case 5:
{
lean_object* x_54; uint8_t x_55; 
x_54 = l_Lean_Expr_getAppFn(x_2);
x_55 = l_Lean_Expr_isMVar(x_54);
if (x_55 == 0)
{
lean_object* x_56; 
lean_dec(x_54);
x_56 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at_Lean_Meta_getFVarSetToGeneralize___spec__14___at_Lean_Meta_getFVarSetToGeneralize___spec__22(x_1, x_2, x_3);
return x_56;
}
else
{
uint8_t x_57; 
x_57 = !lean_is_exclusive(x_3);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_58 = lean_ctor_get(x_3, 1);
lean_inc(x_2);
x_59 = l_Lean_instantiateMVars(x_2, x_58);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
lean_ctor_set(x_3, 1, x_61);
x_62 = l_Lean_Expr_getAppFn(x_60);
x_63 = lean_expr_eqv(x_62, x_54);
lean_dec(x_54);
lean_dec(x_62);
if (x_63 == 0)
{
lean_dec(x_2);
x_2 = x_60;
goto _start;
}
else
{
lean_object* x_65; 
lean_dec(x_60);
x_65 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at_Lean_Meta_getFVarSetToGeneralize___spec__14___at_Lean_Meta_getFVarSetToGeneralize___spec__22(x_1, x_2, x_3);
return x_65;
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_66 = lean_ctor_get(x_3, 0);
x_67 = lean_ctor_get(x_3, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_3);
lean_inc(x_2);
x_68 = l_Lean_instantiateMVars(x_2, x_67);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_66);
lean_ctor_set(x_71, 1, x_70);
x_72 = l_Lean_Expr_getAppFn(x_69);
x_73 = lean_expr_eqv(x_72, x_54);
lean_dec(x_54);
lean_dec(x_72);
if (x_73 == 0)
{
lean_dec(x_2);
x_2 = x_69;
x_3 = x_71;
goto _start;
}
else
{
lean_object* x_75; 
lean_dec(x_69);
x_75 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at_Lean_Meta_getFVarSetToGeneralize___spec__14___at_Lean_Meta_getFVarSetToGeneralize___spec__22(x_1, x_2, x_71);
return x_75;
}
}
}
}
case 6:
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_76 = lean_ctor_get(x_2, 1);
lean_inc(x_76);
x_77 = lean_ctor_get(x_2, 2);
lean_inc(x_77);
lean_dec(x_2);
lean_inc(x_1);
x_78 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__12___at_Lean_Meta_getFVarSetToGeneralize___spec__20(x_1, x_76, x_3);
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_unbox(x_79);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; 
lean_dec(x_79);
x_81 = lean_ctor_get(x_78, 1);
lean_inc(x_81);
lean_dec(x_78);
x_82 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__12___at_Lean_Meta_getFVarSetToGeneralize___spec__20(x_1, x_77, x_81);
return x_82;
}
else
{
uint8_t x_83; 
lean_dec(x_77);
lean_dec(x_1);
x_83 = !lean_is_exclusive(x_78);
if (x_83 == 0)
{
lean_object* x_84; 
x_84 = lean_ctor_get(x_78, 0);
lean_dec(x_84);
return x_78;
}
else
{
lean_object* x_85; lean_object* x_86; 
x_85 = lean_ctor_get(x_78, 1);
lean_inc(x_85);
lean_dec(x_78);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_79);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
}
case 7:
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; 
x_87 = lean_ctor_get(x_2, 1);
lean_inc(x_87);
x_88 = lean_ctor_get(x_2, 2);
lean_inc(x_88);
lean_dec(x_2);
lean_inc(x_1);
x_89 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__12___at_Lean_Meta_getFVarSetToGeneralize___spec__20(x_1, x_87, x_3);
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_unbox(x_90);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; 
lean_dec(x_90);
x_92 = lean_ctor_get(x_89, 1);
lean_inc(x_92);
lean_dec(x_89);
x_93 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__12___at_Lean_Meta_getFVarSetToGeneralize___spec__20(x_1, x_88, x_92);
return x_93;
}
else
{
uint8_t x_94; 
lean_dec(x_88);
lean_dec(x_1);
x_94 = !lean_is_exclusive(x_89);
if (x_94 == 0)
{
lean_object* x_95; 
x_95 = lean_ctor_get(x_89, 0);
lean_dec(x_95);
return x_89;
}
else
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_ctor_get(x_89, 1);
lean_inc(x_96);
lean_dec(x_89);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_90);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
}
case 8:
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_98 = lean_ctor_get(x_2, 1);
lean_inc(x_98);
x_99 = lean_ctor_get(x_2, 2);
lean_inc(x_99);
x_100 = lean_ctor_get(x_2, 3);
lean_inc(x_100);
lean_dec(x_2);
lean_inc(x_1);
x_101 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__12___at_Lean_Meta_getFVarSetToGeneralize___spec__20(x_1, x_98, x_3);
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_unbox(x_102);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; 
lean_dec(x_102);
x_104 = lean_ctor_get(x_101, 1);
lean_inc(x_104);
lean_dec(x_101);
lean_inc(x_1);
x_105 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__12___at_Lean_Meta_getFVarSetToGeneralize___spec__20(x_1, x_99, x_104);
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_unbox(x_106);
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; 
lean_dec(x_106);
x_108 = lean_ctor_get(x_105, 1);
lean_inc(x_108);
lean_dec(x_105);
x_109 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__12___at_Lean_Meta_getFVarSetToGeneralize___spec__20(x_1, x_100, x_108);
return x_109;
}
else
{
uint8_t x_110; 
lean_dec(x_100);
lean_dec(x_1);
x_110 = !lean_is_exclusive(x_105);
if (x_110 == 0)
{
lean_object* x_111; 
x_111 = lean_ctor_get(x_105, 0);
lean_dec(x_111);
return x_105;
}
else
{
lean_object* x_112; lean_object* x_113; 
x_112 = lean_ctor_get(x_105, 1);
lean_inc(x_112);
lean_dec(x_105);
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_106);
lean_ctor_set(x_113, 1, x_112);
return x_113;
}
}
}
else
{
uint8_t x_114; 
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_1);
x_114 = !lean_is_exclusive(x_101);
if (x_114 == 0)
{
lean_object* x_115; 
x_115 = lean_ctor_get(x_101, 0);
lean_dec(x_115);
return x_101;
}
else
{
lean_object* x_116; lean_object* x_117; 
x_116 = lean_ctor_get(x_101, 1);
lean_inc(x_116);
lean_dec(x_101);
x_117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_117, 0, x_102);
lean_ctor_set(x_117, 1, x_116);
return x_117;
}
}
}
case 10:
{
lean_object* x_118; lean_object* x_119; 
x_118 = lean_ctor_get(x_2, 1);
lean_inc(x_118);
lean_dec(x_2);
x_119 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__12___at_Lean_Meta_getFVarSetToGeneralize___spec__20(x_1, x_118, x_3);
return x_119;
}
case 11:
{
lean_object* x_120; lean_object* x_121; 
x_120 = lean_ctor_get(x_2, 2);
lean_inc(x_120);
lean_dec(x_2);
x_121 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__12___at_Lean_Meta_getFVarSetToGeneralize___spec__20(x_1, x_120, x_3);
return x_121;
}
default: 
{
uint8_t x_122; lean_object* x_123; lean_object* x_124; 
lean_dec(x_2);
lean_dec(x_1);
x_122 = 0;
x_123 = lean_box(x_122);
x_124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_3);
return x_124;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__12___at_Lean_Meta_getFVarSetToGeneralize___spec__20(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
lean_inc(x_2);
x_4 = l___private_Lean_MetavarContext_0__Lean_DependsOn_shouldVisit(x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_unbox(x_5);
lean_dec(x_5);
if (x_6 == 0)
{
uint8_t x_7; 
lean_dec(x_2);
lean_dec(x_1);
x_7 = !lean_is_exclusive(x_4);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_4, 0);
lean_dec(x_8);
x_9 = 0;
x_10 = lean_box(x_9);
lean_ctor_set(x_4, 0, x_10);
return x_4;
}
else
{
lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_4, 1);
lean_inc(x_11);
lean_dec(x_4);
x_12 = 0;
x_13 = lean_box(x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_4, 1);
lean_inc(x_15);
lean_dec(x_4);
x_16 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at_Lean_Meta_getFVarSetToGeneralize___spec__13___at_Lean_Meta_getFVarSetToGeneralize___spec__21(x_1, x_2, x_15);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at_Lean_Meta_getFVarSetToGeneralize___spec__25(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 5)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_7 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at_Lean_Meta_getFVarSetToGeneralize___spec__25(x_1, x_2, x_5, x_4);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_unbox(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_8);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_dec(x_7);
x_11 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__23(x_1, x_2, x_6, x_10);
return x_11;
}
else
{
uint8_t x_12; 
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_12 = !lean_is_exclusive(x_7);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_7, 0);
lean_dec(x_13);
return x_7;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_7, 1);
lean_inc(x_14);
lean_dec(x_7);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_8);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
else
{
lean_object* x_16; 
x_16 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__23(x_1, x_2, x_3, x_4);
return x_16;
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__28(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_uget(x_3, x_4);
lean_inc(x_2);
lean_inc(x_1);
x_8 = l_Std_PersistentArray_anyMAux___at_Lean_Meta_getFVarSetToGeneralize___spec__27(x_1, x_2, x_7);
if (x_8 == 0)
{
size_t x_9; size_t x_10; 
x_9 = 1;
x_10 = lean_usize_add(x_4, x_9);
x_4 = x_10;
goto _start;
}
else
{
uint8_t x_12; 
lean_dec(x_2);
lean_dec(x_1);
x_12 = 1;
return x_12;
}
}
else
{
uint8_t x_13; 
lean_dec(x_2);
lean_dec(x_1);
x_13 = 0;
return x_13;
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__29(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_array_uget(x_3, x_4);
if (lean_obj_tag(x_7) == 0)
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = lean_usize_add(x_4, x_8);
x_4 = x_9;
goto _start;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
lean_dec(x_7);
x_12 = l_Lean_LocalDecl_fvarId(x_11);
lean_dec(x_11);
lean_inc(x_2);
lean_inc(x_1);
x_13 = l_Std_RBNode_findCore___rarg(x_1, x_2, x_12);
if (lean_obj_tag(x_13) == 0)
{
size_t x_14; size_t x_15; 
x_14 = 1;
x_15 = lean_usize_add(x_4, x_14);
x_4 = x_15;
goto _start;
}
else
{
uint8_t x_17; 
lean_dec(x_13);
lean_dec(x_2);
lean_dec(x_1);
x_17 = 1;
return x_17;
}
}
}
else
{
uint8_t x_18; 
lean_dec(x_2);
lean_dec(x_1);
x_18 = 0;
return x_18;
}
}
}
LEAN_EXPORT uint8_t l_Std_PersistentArray_anyMAux___at_Lean_Meta_getFVarSetToGeneralize___spec__27(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_array_get_size(x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_lt(x_6, x_5);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_8 = 0;
return x_8;
}
else
{
uint8_t x_9; 
x_9 = lean_nat_dec_le(x_5, x_5);
if (x_9 == 0)
{
uint8_t x_10; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_10 = 0;
return x_10;
}
else
{
size_t x_11; size_t x_12; uint8_t x_13; 
x_11 = 0;
x_12 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_13 = l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__28(x_1, x_2, x_4, x_11, x_12);
lean_dec(x_4);
return x_13;
}
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_3, 0);
lean_inc(x_14);
lean_dec(x_3);
x_15 = lean_array_get_size(x_14);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_nat_dec_lt(x_16, x_15);
if (x_17 == 0)
{
uint8_t x_18; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_2);
lean_dec(x_1);
x_18 = 0;
return x_18;
}
else
{
uint8_t x_19; 
x_19 = lean_nat_dec_le(x_15, x_15);
if (x_19 == 0)
{
uint8_t x_20; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_2);
lean_dec(x_1);
x_20 = 0;
return x_20;
}
else
{
size_t x_21; size_t x_22; uint8_t x_23; 
x_21 = 0;
x_22 = lean_usize_of_nat(x_15);
lean_dec(x_15);
x_23 = l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__29(x_1, x_2, x_14, x_21, x_22);
lean_dec(x_14);
return x_23;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__30(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_array_uget(x_3, x_4);
if (lean_obj_tag(x_7) == 0)
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = lean_usize_add(x_4, x_8);
x_4 = x_9;
goto _start;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
lean_dec(x_7);
x_12 = l_Lean_LocalDecl_fvarId(x_11);
lean_dec(x_11);
lean_inc(x_2);
lean_inc(x_1);
x_13 = l_Std_RBNode_findCore___rarg(x_1, x_2, x_12);
if (lean_obj_tag(x_13) == 0)
{
size_t x_14; size_t x_15; 
x_14 = 1;
x_15 = lean_usize_add(x_4, x_14);
x_4 = x_15;
goto _start;
}
else
{
uint8_t x_17; 
lean_dec(x_13);
lean_dec(x_2);
lean_dec(x_1);
x_17 = 1;
return x_17;
}
}
}
else
{
uint8_t x_18; 
lean_dec(x_2);
lean_dec(x_1);
x_18 = 0;
return x_18;
}
}
}
LEAN_EXPORT uint8_t l_Std_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__26(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_5 = l_Std_PersistentArray_anyMAux___at_Lean_Meta_getFVarSetToGeneralize___spec__27(x_1, x_2, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec(x_3);
x_7 = lean_array_get_size(x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_lt(x_8, x_7);
if (x_9 == 0)
{
uint8_t x_10; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_10 = 0;
return x_10;
}
else
{
uint8_t x_11; 
x_11 = lean_nat_dec_le(x_7, x_7);
if (x_11 == 0)
{
uint8_t x_12; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_12 = 0;
return x_12;
}
else
{
size_t x_13; size_t x_14; uint8_t x_15; 
x_13 = 0;
x_14 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_15 = l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__30(x_1, x_2, x_6, x_13, x_14);
lean_dec(x_6);
return x_15;
}
}
}
else
{
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at_Lean_Meta_getFVarSetToGeneralize___spec__24(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_3)) {
case 1:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
x_6 = l_Std_RBNode_findCore___rarg(x_1, x_2, x_5);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; lean_object* x_8; lean_object* x_9; 
x_7 = 0;
x_8 = lean_box(x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_4);
return x_9;
}
else
{
uint8_t x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_6);
x_10 = 1;
x_11 = lean_box(x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_4);
return x_12;
}
}
case 2:
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_3, 0);
lean_inc(x_13);
lean_dec(x_3);
x_14 = !lean_is_exclusive(x_4);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_4, 1);
lean_inc(x_13);
x_16 = l_Lean_getExprMVarAssignment_x3f(x_13, x_15);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_ctor_set(x_4, 1, x_19);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_20 = l_Lean_MetavarContext_getDecl(x_19, x_13);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = l_Std_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__26(x_1, x_2, x_22);
x_24 = lean_box(x_23);
lean_ctor_set(x_16, 1, x_4);
lean_ctor_set(x_16, 0, x_24);
return x_16;
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_free_object(x_16);
lean_dec(x_19);
lean_dec(x_13);
x_25 = lean_ctor_get(x_18, 0);
lean_inc(x_25);
lean_dec(x_18);
x_26 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__23(x_1, x_2, x_25, x_4);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_16, 0);
x_28 = lean_ctor_get(x_16, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_16);
lean_inc(x_28);
lean_ctor_set(x_4, 1, x_28);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; 
x_29 = l_Lean_MetavarContext_getDecl(x_28, x_13);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec(x_30);
x_32 = l_Std_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__26(x_1, x_2, x_31);
x_33 = lean_box(x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_4);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_28);
lean_dec(x_13);
x_35 = lean_ctor_get(x_27, 0);
lean_inc(x_35);
lean_dec(x_27);
x_36 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__23(x_1, x_2, x_35, x_4);
return x_36;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_37 = lean_ctor_get(x_4, 0);
x_38 = lean_ctor_get(x_4, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_4);
lean_inc(x_13);
x_39 = l_Lean_getExprMVarAssignment_x3f(x_13, x_38);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_42 = x_39;
} else {
 lean_dec_ref(x_39);
 x_42 = lean_box(0);
}
lean_inc(x_41);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_37);
lean_ctor_set(x_43, 1, x_41);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; 
x_44 = l_Lean_MetavarContext_getDecl(x_41, x_13);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
lean_dec(x_45);
x_47 = l_Std_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__26(x_1, x_2, x_46);
x_48 = lean_box(x_47);
if (lean_is_scalar(x_42)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_42;
}
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_43);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; 
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_13);
x_50 = lean_ctor_get(x_40, 0);
lean_inc(x_50);
lean_dec(x_40);
x_51 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__23(x_1, x_2, x_50, x_43);
return x_51;
}
}
}
case 5:
{
lean_object* x_52; uint8_t x_53; 
x_52 = l_Lean_Expr_getAppFn(x_3);
x_53 = l_Lean_Expr_isMVar(x_52);
if (x_53 == 0)
{
lean_object* x_54; 
lean_dec(x_52);
x_54 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at_Lean_Meta_getFVarSetToGeneralize___spec__25(x_1, x_2, x_3, x_4);
return x_54;
}
else
{
uint8_t x_55; 
x_55 = !lean_is_exclusive(x_4);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_56 = lean_ctor_get(x_4, 1);
lean_inc(x_3);
x_57 = l_Lean_instantiateMVars(x_3, x_56);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
lean_ctor_set(x_4, 1, x_59);
x_60 = l_Lean_Expr_getAppFn(x_58);
x_61 = lean_expr_eqv(x_60, x_52);
lean_dec(x_52);
lean_dec(x_60);
if (x_61 == 0)
{
lean_dec(x_3);
x_3 = x_58;
goto _start;
}
else
{
lean_object* x_63; 
lean_dec(x_58);
x_63 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at_Lean_Meta_getFVarSetToGeneralize___spec__25(x_1, x_2, x_3, x_4);
return x_63;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_64 = lean_ctor_get(x_4, 0);
x_65 = lean_ctor_get(x_4, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_4);
lean_inc(x_3);
x_66 = l_Lean_instantiateMVars(x_3, x_65);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_64);
lean_ctor_set(x_69, 1, x_68);
x_70 = l_Lean_Expr_getAppFn(x_67);
x_71 = lean_expr_eqv(x_70, x_52);
lean_dec(x_52);
lean_dec(x_70);
if (x_71 == 0)
{
lean_dec(x_3);
x_3 = x_67;
x_4 = x_69;
goto _start;
}
else
{
lean_object* x_73; 
lean_dec(x_67);
x_73 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at_Lean_Meta_getFVarSetToGeneralize___spec__25(x_1, x_2, x_3, x_69);
return x_73;
}
}
}
}
case 6:
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_74 = lean_ctor_get(x_3, 1);
lean_inc(x_74);
x_75 = lean_ctor_get(x_3, 2);
lean_inc(x_75);
lean_dec(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_76 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__23(x_1, x_2, x_74, x_4);
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_unbox(x_77);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; 
lean_dec(x_77);
x_79 = lean_ctor_get(x_76, 1);
lean_inc(x_79);
lean_dec(x_76);
x_80 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__23(x_1, x_2, x_75, x_79);
return x_80;
}
else
{
uint8_t x_81; 
lean_dec(x_75);
lean_dec(x_2);
lean_dec(x_1);
x_81 = !lean_is_exclusive(x_76);
if (x_81 == 0)
{
lean_object* x_82; 
x_82 = lean_ctor_get(x_76, 0);
lean_dec(x_82);
return x_76;
}
else
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_76, 1);
lean_inc(x_83);
lean_dec(x_76);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_77);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
case 7:
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_85 = lean_ctor_get(x_3, 1);
lean_inc(x_85);
x_86 = lean_ctor_get(x_3, 2);
lean_inc(x_86);
lean_dec(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_87 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__23(x_1, x_2, x_85, x_4);
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_unbox(x_88);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; 
lean_dec(x_88);
x_90 = lean_ctor_get(x_87, 1);
lean_inc(x_90);
lean_dec(x_87);
x_91 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__23(x_1, x_2, x_86, x_90);
return x_91;
}
else
{
uint8_t x_92; 
lean_dec(x_86);
lean_dec(x_2);
lean_dec(x_1);
x_92 = !lean_is_exclusive(x_87);
if (x_92 == 0)
{
lean_object* x_93; 
x_93 = lean_ctor_get(x_87, 0);
lean_dec(x_93);
return x_87;
}
else
{
lean_object* x_94; lean_object* x_95; 
x_94 = lean_ctor_get(x_87, 1);
lean_inc(x_94);
lean_dec(x_87);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_88);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
case 8:
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; 
x_96 = lean_ctor_get(x_3, 1);
lean_inc(x_96);
x_97 = lean_ctor_get(x_3, 2);
lean_inc(x_97);
x_98 = lean_ctor_get(x_3, 3);
lean_inc(x_98);
lean_dec(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_99 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__23(x_1, x_2, x_96, x_4);
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_unbox(x_100);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; 
lean_dec(x_100);
x_102 = lean_ctor_get(x_99, 1);
lean_inc(x_102);
lean_dec(x_99);
lean_inc(x_2);
lean_inc(x_1);
x_103 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__23(x_1, x_2, x_97, x_102);
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_unbox(x_104);
if (x_105 == 0)
{
lean_object* x_106; lean_object* x_107; 
lean_dec(x_104);
x_106 = lean_ctor_get(x_103, 1);
lean_inc(x_106);
lean_dec(x_103);
x_107 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__23(x_1, x_2, x_98, x_106);
return x_107;
}
else
{
uint8_t x_108; 
lean_dec(x_98);
lean_dec(x_2);
lean_dec(x_1);
x_108 = !lean_is_exclusive(x_103);
if (x_108 == 0)
{
lean_object* x_109; 
x_109 = lean_ctor_get(x_103, 0);
lean_dec(x_109);
return x_103;
}
else
{
lean_object* x_110; lean_object* x_111; 
x_110 = lean_ctor_get(x_103, 1);
lean_inc(x_110);
lean_dec(x_103);
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_104);
lean_ctor_set(x_111, 1, x_110);
return x_111;
}
}
}
else
{
uint8_t x_112; 
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_2);
lean_dec(x_1);
x_112 = !lean_is_exclusive(x_99);
if (x_112 == 0)
{
lean_object* x_113; 
x_113 = lean_ctor_get(x_99, 0);
lean_dec(x_113);
return x_99;
}
else
{
lean_object* x_114; lean_object* x_115; 
x_114 = lean_ctor_get(x_99, 1);
lean_inc(x_114);
lean_dec(x_99);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_100);
lean_ctor_set(x_115, 1, x_114);
return x_115;
}
}
}
case 10:
{
lean_object* x_116; lean_object* x_117; 
x_116 = lean_ctor_get(x_3, 1);
lean_inc(x_116);
lean_dec(x_3);
x_117 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__23(x_1, x_2, x_116, x_4);
return x_117;
}
case 11:
{
lean_object* x_118; lean_object* x_119; 
x_118 = lean_ctor_get(x_3, 2);
lean_inc(x_118);
lean_dec(x_3);
x_119 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__23(x_1, x_2, x_118, x_4);
return x_119;
}
default: 
{
uint8_t x_120; lean_object* x_121; lean_object* x_122; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_120 = 0;
x_121 = lean_box(x_120);
x_122 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set(x_122, 1, x_4);
return x_122;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__23(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
lean_inc(x_3);
x_5 = l___private_Lean_MetavarContext_0__Lean_DependsOn_shouldVisit(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_unbox(x_6);
lean_dec(x_6);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
x_17 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at_Lean_Meta_getFVarSetToGeneralize___spec__24(x_1, x_2, x_3, x_16);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at_Lean_Meta_getFVarSetToGeneralize___spec__33(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 5)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_7 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at_Lean_Meta_getFVarSetToGeneralize___spec__33(x_1, x_2, x_5, x_4);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_unbox(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_8);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_dec(x_7);
x_11 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__31(x_1, x_2, x_6, x_10);
return x_11;
}
else
{
uint8_t x_12; 
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_12 = !lean_is_exclusive(x_7);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_7, 0);
lean_dec(x_13);
return x_7;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_7, 1);
lean_inc(x_14);
lean_dec(x_7);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_8);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
else
{
lean_object* x_16; 
x_16 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__31(x_1, x_2, x_3, x_4);
return x_16;
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__36(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_uget(x_3, x_4);
lean_inc(x_2);
lean_inc(x_1);
x_8 = l_Std_PersistentArray_anyMAux___at_Lean_Meta_getFVarSetToGeneralize___spec__35(x_1, x_2, x_7);
if (x_8 == 0)
{
size_t x_9; size_t x_10; 
x_9 = 1;
x_10 = lean_usize_add(x_4, x_9);
x_4 = x_10;
goto _start;
}
else
{
uint8_t x_12; 
lean_dec(x_2);
lean_dec(x_1);
x_12 = 1;
return x_12;
}
}
else
{
uint8_t x_13; 
lean_dec(x_2);
lean_dec(x_1);
x_13 = 0;
return x_13;
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__37(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_array_uget(x_3, x_4);
if (lean_obj_tag(x_7) == 0)
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = lean_usize_add(x_4, x_8);
x_4 = x_9;
goto _start;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
lean_dec(x_7);
x_12 = l_Lean_LocalDecl_fvarId(x_11);
lean_dec(x_11);
lean_inc(x_2);
lean_inc(x_1);
x_13 = l_Std_RBNode_findCore___rarg(x_1, x_2, x_12);
if (lean_obj_tag(x_13) == 0)
{
size_t x_14; size_t x_15; 
x_14 = 1;
x_15 = lean_usize_add(x_4, x_14);
x_4 = x_15;
goto _start;
}
else
{
uint8_t x_17; 
lean_dec(x_13);
lean_dec(x_2);
lean_dec(x_1);
x_17 = 1;
return x_17;
}
}
}
else
{
uint8_t x_18; 
lean_dec(x_2);
lean_dec(x_1);
x_18 = 0;
return x_18;
}
}
}
LEAN_EXPORT uint8_t l_Std_PersistentArray_anyMAux___at_Lean_Meta_getFVarSetToGeneralize___spec__35(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_array_get_size(x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_lt(x_6, x_5);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_8 = 0;
return x_8;
}
else
{
uint8_t x_9; 
x_9 = lean_nat_dec_le(x_5, x_5);
if (x_9 == 0)
{
uint8_t x_10; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_10 = 0;
return x_10;
}
else
{
size_t x_11; size_t x_12; uint8_t x_13; 
x_11 = 0;
x_12 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_13 = l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__36(x_1, x_2, x_4, x_11, x_12);
lean_dec(x_4);
return x_13;
}
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_3, 0);
lean_inc(x_14);
lean_dec(x_3);
x_15 = lean_array_get_size(x_14);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_nat_dec_lt(x_16, x_15);
if (x_17 == 0)
{
uint8_t x_18; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_2);
lean_dec(x_1);
x_18 = 0;
return x_18;
}
else
{
uint8_t x_19; 
x_19 = lean_nat_dec_le(x_15, x_15);
if (x_19 == 0)
{
uint8_t x_20; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_2);
lean_dec(x_1);
x_20 = 0;
return x_20;
}
else
{
size_t x_21; size_t x_22; uint8_t x_23; 
x_21 = 0;
x_22 = lean_usize_of_nat(x_15);
lean_dec(x_15);
x_23 = l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__37(x_1, x_2, x_14, x_21, x_22);
lean_dec(x_14);
return x_23;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__38(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_array_uget(x_3, x_4);
if (lean_obj_tag(x_7) == 0)
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = lean_usize_add(x_4, x_8);
x_4 = x_9;
goto _start;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
lean_dec(x_7);
x_12 = l_Lean_LocalDecl_fvarId(x_11);
lean_dec(x_11);
lean_inc(x_2);
lean_inc(x_1);
x_13 = l_Std_RBNode_findCore___rarg(x_1, x_2, x_12);
if (lean_obj_tag(x_13) == 0)
{
size_t x_14; size_t x_15; 
x_14 = 1;
x_15 = lean_usize_add(x_4, x_14);
x_4 = x_15;
goto _start;
}
else
{
uint8_t x_17; 
lean_dec(x_13);
lean_dec(x_2);
lean_dec(x_1);
x_17 = 1;
return x_17;
}
}
}
else
{
uint8_t x_18; 
lean_dec(x_2);
lean_dec(x_1);
x_18 = 0;
return x_18;
}
}
}
LEAN_EXPORT uint8_t l_Std_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__34(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_5 = l_Std_PersistentArray_anyMAux___at_Lean_Meta_getFVarSetToGeneralize___spec__35(x_1, x_2, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec(x_3);
x_7 = lean_array_get_size(x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_lt(x_8, x_7);
if (x_9 == 0)
{
uint8_t x_10; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_10 = 0;
return x_10;
}
else
{
uint8_t x_11; 
x_11 = lean_nat_dec_le(x_7, x_7);
if (x_11 == 0)
{
uint8_t x_12; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_12 = 0;
return x_12;
}
else
{
size_t x_13; size_t x_14; uint8_t x_15; 
x_13 = 0;
x_14 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_15 = l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__38(x_1, x_2, x_6, x_13, x_14);
lean_dec(x_6);
return x_15;
}
}
}
else
{
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at_Lean_Meta_getFVarSetToGeneralize___spec__32(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_3)) {
case 1:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
x_6 = l_Std_RBNode_findCore___rarg(x_1, x_2, x_5);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; lean_object* x_8; lean_object* x_9; 
x_7 = 0;
x_8 = lean_box(x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_4);
return x_9;
}
else
{
uint8_t x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_6);
x_10 = 1;
x_11 = lean_box(x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_4);
return x_12;
}
}
case 2:
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_3, 0);
lean_inc(x_13);
lean_dec(x_3);
x_14 = !lean_is_exclusive(x_4);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_4, 1);
lean_inc(x_13);
x_16 = l_Lean_getExprMVarAssignment_x3f(x_13, x_15);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_ctor_set(x_4, 1, x_19);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_20 = l_Lean_MetavarContext_getDecl(x_19, x_13);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = l_Std_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__34(x_1, x_2, x_22);
x_24 = lean_box(x_23);
lean_ctor_set(x_16, 1, x_4);
lean_ctor_set(x_16, 0, x_24);
return x_16;
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_free_object(x_16);
lean_dec(x_19);
lean_dec(x_13);
x_25 = lean_ctor_get(x_18, 0);
lean_inc(x_25);
lean_dec(x_18);
x_26 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__31(x_1, x_2, x_25, x_4);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_16, 0);
x_28 = lean_ctor_get(x_16, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_16);
lean_inc(x_28);
lean_ctor_set(x_4, 1, x_28);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; 
x_29 = l_Lean_MetavarContext_getDecl(x_28, x_13);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec(x_30);
x_32 = l_Std_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__34(x_1, x_2, x_31);
x_33 = lean_box(x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_4);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_28);
lean_dec(x_13);
x_35 = lean_ctor_get(x_27, 0);
lean_inc(x_35);
lean_dec(x_27);
x_36 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__31(x_1, x_2, x_35, x_4);
return x_36;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_37 = lean_ctor_get(x_4, 0);
x_38 = lean_ctor_get(x_4, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_4);
lean_inc(x_13);
x_39 = l_Lean_getExprMVarAssignment_x3f(x_13, x_38);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_42 = x_39;
} else {
 lean_dec_ref(x_39);
 x_42 = lean_box(0);
}
lean_inc(x_41);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_37);
lean_ctor_set(x_43, 1, x_41);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; 
x_44 = l_Lean_MetavarContext_getDecl(x_41, x_13);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
lean_dec(x_45);
x_47 = l_Std_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__34(x_1, x_2, x_46);
x_48 = lean_box(x_47);
if (lean_is_scalar(x_42)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_42;
}
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_43);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; 
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_13);
x_50 = lean_ctor_get(x_40, 0);
lean_inc(x_50);
lean_dec(x_40);
x_51 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__31(x_1, x_2, x_50, x_43);
return x_51;
}
}
}
case 5:
{
lean_object* x_52; uint8_t x_53; 
x_52 = l_Lean_Expr_getAppFn(x_3);
x_53 = l_Lean_Expr_isMVar(x_52);
if (x_53 == 0)
{
lean_object* x_54; 
lean_dec(x_52);
x_54 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at_Lean_Meta_getFVarSetToGeneralize___spec__33(x_1, x_2, x_3, x_4);
return x_54;
}
else
{
uint8_t x_55; 
x_55 = !lean_is_exclusive(x_4);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_56 = lean_ctor_get(x_4, 1);
lean_inc(x_3);
x_57 = l_Lean_instantiateMVars(x_3, x_56);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
lean_ctor_set(x_4, 1, x_59);
x_60 = l_Lean_Expr_getAppFn(x_58);
x_61 = lean_expr_eqv(x_60, x_52);
lean_dec(x_52);
lean_dec(x_60);
if (x_61 == 0)
{
lean_dec(x_3);
x_3 = x_58;
goto _start;
}
else
{
lean_object* x_63; 
lean_dec(x_58);
x_63 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at_Lean_Meta_getFVarSetToGeneralize___spec__33(x_1, x_2, x_3, x_4);
return x_63;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_64 = lean_ctor_get(x_4, 0);
x_65 = lean_ctor_get(x_4, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_4);
lean_inc(x_3);
x_66 = l_Lean_instantiateMVars(x_3, x_65);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_64);
lean_ctor_set(x_69, 1, x_68);
x_70 = l_Lean_Expr_getAppFn(x_67);
x_71 = lean_expr_eqv(x_70, x_52);
lean_dec(x_52);
lean_dec(x_70);
if (x_71 == 0)
{
lean_dec(x_3);
x_3 = x_67;
x_4 = x_69;
goto _start;
}
else
{
lean_object* x_73; 
lean_dec(x_67);
x_73 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at_Lean_Meta_getFVarSetToGeneralize___spec__33(x_1, x_2, x_3, x_69);
return x_73;
}
}
}
}
case 6:
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_74 = lean_ctor_get(x_3, 1);
lean_inc(x_74);
x_75 = lean_ctor_get(x_3, 2);
lean_inc(x_75);
lean_dec(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_76 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__31(x_1, x_2, x_74, x_4);
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_unbox(x_77);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; 
lean_dec(x_77);
x_79 = lean_ctor_get(x_76, 1);
lean_inc(x_79);
lean_dec(x_76);
x_80 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__31(x_1, x_2, x_75, x_79);
return x_80;
}
else
{
uint8_t x_81; 
lean_dec(x_75);
lean_dec(x_2);
lean_dec(x_1);
x_81 = !lean_is_exclusive(x_76);
if (x_81 == 0)
{
lean_object* x_82; 
x_82 = lean_ctor_get(x_76, 0);
lean_dec(x_82);
return x_76;
}
else
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_76, 1);
lean_inc(x_83);
lean_dec(x_76);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_77);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
case 7:
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_85 = lean_ctor_get(x_3, 1);
lean_inc(x_85);
x_86 = lean_ctor_get(x_3, 2);
lean_inc(x_86);
lean_dec(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_87 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__31(x_1, x_2, x_85, x_4);
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_unbox(x_88);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; 
lean_dec(x_88);
x_90 = lean_ctor_get(x_87, 1);
lean_inc(x_90);
lean_dec(x_87);
x_91 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__31(x_1, x_2, x_86, x_90);
return x_91;
}
else
{
uint8_t x_92; 
lean_dec(x_86);
lean_dec(x_2);
lean_dec(x_1);
x_92 = !lean_is_exclusive(x_87);
if (x_92 == 0)
{
lean_object* x_93; 
x_93 = lean_ctor_get(x_87, 0);
lean_dec(x_93);
return x_87;
}
else
{
lean_object* x_94; lean_object* x_95; 
x_94 = lean_ctor_get(x_87, 1);
lean_inc(x_94);
lean_dec(x_87);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_88);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
case 8:
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; 
x_96 = lean_ctor_get(x_3, 1);
lean_inc(x_96);
x_97 = lean_ctor_get(x_3, 2);
lean_inc(x_97);
x_98 = lean_ctor_get(x_3, 3);
lean_inc(x_98);
lean_dec(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_99 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__31(x_1, x_2, x_96, x_4);
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_unbox(x_100);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; 
lean_dec(x_100);
x_102 = lean_ctor_get(x_99, 1);
lean_inc(x_102);
lean_dec(x_99);
lean_inc(x_2);
lean_inc(x_1);
x_103 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__31(x_1, x_2, x_97, x_102);
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_unbox(x_104);
if (x_105 == 0)
{
lean_object* x_106; lean_object* x_107; 
lean_dec(x_104);
x_106 = lean_ctor_get(x_103, 1);
lean_inc(x_106);
lean_dec(x_103);
x_107 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__31(x_1, x_2, x_98, x_106);
return x_107;
}
else
{
uint8_t x_108; 
lean_dec(x_98);
lean_dec(x_2);
lean_dec(x_1);
x_108 = !lean_is_exclusive(x_103);
if (x_108 == 0)
{
lean_object* x_109; 
x_109 = lean_ctor_get(x_103, 0);
lean_dec(x_109);
return x_103;
}
else
{
lean_object* x_110; lean_object* x_111; 
x_110 = lean_ctor_get(x_103, 1);
lean_inc(x_110);
lean_dec(x_103);
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_104);
lean_ctor_set(x_111, 1, x_110);
return x_111;
}
}
}
else
{
uint8_t x_112; 
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_2);
lean_dec(x_1);
x_112 = !lean_is_exclusive(x_99);
if (x_112 == 0)
{
lean_object* x_113; 
x_113 = lean_ctor_get(x_99, 0);
lean_dec(x_113);
return x_99;
}
else
{
lean_object* x_114; lean_object* x_115; 
x_114 = lean_ctor_get(x_99, 1);
lean_inc(x_114);
lean_dec(x_99);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_100);
lean_ctor_set(x_115, 1, x_114);
return x_115;
}
}
}
case 10:
{
lean_object* x_116; lean_object* x_117; 
x_116 = lean_ctor_get(x_3, 1);
lean_inc(x_116);
lean_dec(x_3);
x_117 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__31(x_1, x_2, x_116, x_4);
return x_117;
}
case 11:
{
lean_object* x_118; lean_object* x_119; 
x_118 = lean_ctor_get(x_3, 2);
lean_inc(x_118);
lean_dec(x_3);
x_119 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__31(x_1, x_2, x_118, x_4);
return x_119;
}
default: 
{
uint8_t x_120; lean_object* x_121; lean_object* x_122; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_120 = 0;
x_121 = lean_box(x_120);
x_122 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set(x_122, 1, x_4);
return x_122;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__31(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
lean_inc(x_3);
x_5 = l___private_Lean_MetavarContext_0__Lean_DependsOn_shouldVisit(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_unbox(x_6);
lean_dec(x_6);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
x_17 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at_Lean_Meta_getFVarSetToGeneralize___spec__32(x_1, x_2, x_3, x_16);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at_Lean_Meta_getFVarSetToGeneralize___spec__41(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 5)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_7 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at_Lean_Meta_getFVarSetToGeneralize___spec__41(x_1, x_2, x_5, x_4);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_unbox(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_8);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_dec(x_7);
x_11 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__39(x_1, x_2, x_6, x_10);
return x_11;
}
else
{
uint8_t x_12; 
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_12 = !lean_is_exclusive(x_7);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_7, 0);
lean_dec(x_13);
return x_7;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_7, 1);
lean_inc(x_14);
lean_dec(x_7);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_8);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
else
{
lean_object* x_16; 
x_16 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__39(x_1, x_2, x_3, x_4);
return x_16;
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__44(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_uget(x_3, x_4);
lean_inc(x_2);
lean_inc(x_1);
x_8 = l_Std_PersistentArray_anyMAux___at_Lean_Meta_getFVarSetToGeneralize___spec__43(x_1, x_2, x_7);
if (x_8 == 0)
{
size_t x_9; size_t x_10; 
x_9 = 1;
x_10 = lean_usize_add(x_4, x_9);
x_4 = x_10;
goto _start;
}
else
{
uint8_t x_12; 
lean_dec(x_2);
lean_dec(x_1);
x_12 = 1;
return x_12;
}
}
else
{
uint8_t x_13; 
lean_dec(x_2);
lean_dec(x_1);
x_13 = 0;
return x_13;
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__45(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_array_uget(x_3, x_4);
if (lean_obj_tag(x_7) == 0)
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = lean_usize_add(x_4, x_8);
x_4 = x_9;
goto _start;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
lean_dec(x_7);
x_12 = l_Lean_LocalDecl_fvarId(x_11);
lean_dec(x_11);
lean_inc(x_2);
lean_inc(x_1);
x_13 = l_Std_RBNode_findCore___rarg(x_1, x_2, x_12);
if (lean_obj_tag(x_13) == 0)
{
size_t x_14; size_t x_15; 
x_14 = 1;
x_15 = lean_usize_add(x_4, x_14);
x_4 = x_15;
goto _start;
}
else
{
uint8_t x_17; 
lean_dec(x_13);
lean_dec(x_2);
lean_dec(x_1);
x_17 = 1;
return x_17;
}
}
}
else
{
uint8_t x_18; 
lean_dec(x_2);
lean_dec(x_1);
x_18 = 0;
return x_18;
}
}
}
LEAN_EXPORT uint8_t l_Std_PersistentArray_anyMAux___at_Lean_Meta_getFVarSetToGeneralize___spec__43(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_array_get_size(x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_lt(x_6, x_5);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_8 = 0;
return x_8;
}
else
{
uint8_t x_9; 
x_9 = lean_nat_dec_le(x_5, x_5);
if (x_9 == 0)
{
uint8_t x_10; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_10 = 0;
return x_10;
}
else
{
size_t x_11; size_t x_12; uint8_t x_13; 
x_11 = 0;
x_12 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_13 = l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__44(x_1, x_2, x_4, x_11, x_12);
lean_dec(x_4);
return x_13;
}
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_3, 0);
lean_inc(x_14);
lean_dec(x_3);
x_15 = lean_array_get_size(x_14);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_nat_dec_lt(x_16, x_15);
if (x_17 == 0)
{
uint8_t x_18; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_2);
lean_dec(x_1);
x_18 = 0;
return x_18;
}
else
{
uint8_t x_19; 
x_19 = lean_nat_dec_le(x_15, x_15);
if (x_19 == 0)
{
uint8_t x_20; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_2);
lean_dec(x_1);
x_20 = 0;
return x_20;
}
else
{
size_t x_21; size_t x_22; uint8_t x_23; 
x_21 = 0;
x_22 = lean_usize_of_nat(x_15);
lean_dec(x_15);
x_23 = l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__45(x_1, x_2, x_14, x_21, x_22);
lean_dec(x_14);
return x_23;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__46(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_array_uget(x_3, x_4);
if (lean_obj_tag(x_7) == 0)
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = lean_usize_add(x_4, x_8);
x_4 = x_9;
goto _start;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
lean_dec(x_7);
x_12 = l_Lean_LocalDecl_fvarId(x_11);
lean_dec(x_11);
lean_inc(x_2);
lean_inc(x_1);
x_13 = l_Std_RBNode_findCore___rarg(x_1, x_2, x_12);
if (lean_obj_tag(x_13) == 0)
{
size_t x_14; size_t x_15; 
x_14 = 1;
x_15 = lean_usize_add(x_4, x_14);
x_4 = x_15;
goto _start;
}
else
{
uint8_t x_17; 
lean_dec(x_13);
lean_dec(x_2);
lean_dec(x_1);
x_17 = 1;
return x_17;
}
}
}
else
{
uint8_t x_18; 
lean_dec(x_2);
lean_dec(x_1);
x_18 = 0;
return x_18;
}
}
}
LEAN_EXPORT uint8_t l_Std_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__42(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_5 = l_Std_PersistentArray_anyMAux___at_Lean_Meta_getFVarSetToGeneralize___spec__43(x_1, x_2, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec(x_3);
x_7 = lean_array_get_size(x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_lt(x_8, x_7);
if (x_9 == 0)
{
uint8_t x_10; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_10 = 0;
return x_10;
}
else
{
uint8_t x_11; 
x_11 = lean_nat_dec_le(x_7, x_7);
if (x_11 == 0)
{
uint8_t x_12; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_12 = 0;
return x_12;
}
else
{
size_t x_13; size_t x_14; uint8_t x_15; 
x_13 = 0;
x_14 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_15 = l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__46(x_1, x_2, x_6, x_13, x_14);
lean_dec(x_6);
return x_15;
}
}
}
else
{
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at_Lean_Meta_getFVarSetToGeneralize___spec__40(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_3)) {
case 1:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
x_6 = l_Std_RBNode_findCore___rarg(x_1, x_2, x_5);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; lean_object* x_8; lean_object* x_9; 
x_7 = 0;
x_8 = lean_box(x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_4);
return x_9;
}
else
{
uint8_t x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_6);
x_10 = 1;
x_11 = lean_box(x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_4);
return x_12;
}
}
case 2:
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_3, 0);
lean_inc(x_13);
lean_dec(x_3);
x_14 = !lean_is_exclusive(x_4);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_4, 1);
lean_inc(x_13);
x_16 = l_Lean_getExprMVarAssignment_x3f(x_13, x_15);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_ctor_set(x_4, 1, x_19);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_20 = l_Lean_MetavarContext_getDecl(x_19, x_13);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = l_Std_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__42(x_1, x_2, x_22);
x_24 = lean_box(x_23);
lean_ctor_set(x_16, 1, x_4);
lean_ctor_set(x_16, 0, x_24);
return x_16;
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_free_object(x_16);
lean_dec(x_19);
lean_dec(x_13);
x_25 = lean_ctor_get(x_18, 0);
lean_inc(x_25);
lean_dec(x_18);
x_26 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__39(x_1, x_2, x_25, x_4);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_16, 0);
x_28 = lean_ctor_get(x_16, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_16);
lean_inc(x_28);
lean_ctor_set(x_4, 1, x_28);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; 
x_29 = l_Lean_MetavarContext_getDecl(x_28, x_13);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec(x_30);
x_32 = l_Std_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__42(x_1, x_2, x_31);
x_33 = lean_box(x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_4);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_28);
lean_dec(x_13);
x_35 = lean_ctor_get(x_27, 0);
lean_inc(x_35);
lean_dec(x_27);
x_36 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__39(x_1, x_2, x_35, x_4);
return x_36;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_37 = lean_ctor_get(x_4, 0);
x_38 = lean_ctor_get(x_4, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_4);
lean_inc(x_13);
x_39 = l_Lean_getExprMVarAssignment_x3f(x_13, x_38);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_42 = x_39;
} else {
 lean_dec_ref(x_39);
 x_42 = lean_box(0);
}
lean_inc(x_41);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_37);
lean_ctor_set(x_43, 1, x_41);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; 
x_44 = l_Lean_MetavarContext_getDecl(x_41, x_13);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
lean_dec(x_45);
x_47 = l_Std_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__42(x_1, x_2, x_46);
x_48 = lean_box(x_47);
if (lean_is_scalar(x_42)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_42;
}
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_43);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; 
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_13);
x_50 = lean_ctor_get(x_40, 0);
lean_inc(x_50);
lean_dec(x_40);
x_51 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__39(x_1, x_2, x_50, x_43);
return x_51;
}
}
}
case 5:
{
lean_object* x_52; uint8_t x_53; 
x_52 = l_Lean_Expr_getAppFn(x_3);
x_53 = l_Lean_Expr_isMVar(x_52);
if (x_53 == 0)
{
lean_object* x_54; 
lean_dec(x_52);
x_54 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at_Lean_Meta_getFVarSetToGeneralize___spec__41(x_1, x_2, x_3, x_4);
return x_54;
}
else
{
uint8_t x_55; 
x_55 = !lean_is_exclusive(x_4);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_56 = lean_ctor_get(x_4, 1);
lean_inc(x_3);
x_57 = l_Lean_instantiateMVars(x_3, x_56);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
lean_ctor_set(x_4, 1, x_59);
x_60 = l_Lean_Expr_getAppFn(x_58);
x_61 = lean_expr_eqv(x_60, x_52);
lean_dec(x_52);
lean_dec(x_60);
if (x_61 == 0)
{
lean_dec(x_3);
x_3 = x_58;
goto _start;
}
else
{
lean_object* x_63; 
lean_dec(x_58);
x_63 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at_Lean_Meta_getFVarSetToGeneralize___spec__41(x_1, x_2, x_3, x_4);
return x_63;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_64 = lean_ctor_get(x_4, 0);
x_65 = lean_ctor_get(x_4, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_4);
lean_inc(x_3);
x_66 = l_Lean_instantiateMVars(x_3, x_65);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_64);
lean_ctor_set(x_69, 1, x_68);
x_70 = l_Lean_Expr_getAppFn(x_67);
x_71 = lean_expr_eqv(x_70, x_52);
lean_dec(x_52);
lean_dec(x_70);
if (x_71 == 0)
{
lean_dec(x_3);
x_3 = x_67;
x_4 = x_69;
goto _start;
}
else
{
lean_object* x_73; 
lean_dec(x_67);
x_73 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at_Lean_Meta_getFVarSetToGeneralize___spec__41(x_1, x_2, x_3, x_69);
return x_73;
}
}
}
}
case 6:
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_74 = lean_ctor_get(x_3, 1);
lean_inc(x_74);
x_75 = lean_ctor_get(x_3, 2);
lean_inc(x_75);
lean_dec(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_76 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__39(x_1, x_2, x_74, x_4);
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_unbox(x_77);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; 
lean_dec(x_77);
x_79 = lean_ctor_get(x_76, 1);
lean_inc(x_79);
lean_dec(x_76);
x_80 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__39(x_1, x_2, x_75, x_79);
return x_80;
}
else
{
uint8_t x_81; 
lean_dec(x_75);
lean_dec(x_2);
lean_dec(x_1);
x_81 = !lean_is_exclusive(x_76);
if (x_81 == 0)
{
lean_object* x_82; 
x_82 = lean_ctor_get(x_76, 0);
lean_dec(x_82);
return x_76;
}
else
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_76, 1);
lean_inc(x_83);
lean_dec(x_76);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_77);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
case 7:
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_85 = lean_ctor_get(x_3, 1);
lean_inc(x_85);
x_86 = lean_ctor_get(x_3, 2);
lean_inc(x_86);
lean_dec(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_87 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__39(x_1, x_2, x_85, x_4);
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_unbox(x_88);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; 
lean_dec(x_88);
x_90 = lean_ctor_get(x_87, 1);
lean_inc(x_90);
lean_dec(x_87);
x_91 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__39(x_1, x_2, x_86, x_90);
return x_91;
}
else
{
uint8_t x_92; 
lean_dec(x_86);
lean_dec(x_2);
lean_dec(x_1);
x_92 = !lean_is_exclusive(x_87);
if (x_92 == 0)
{
lean_object* x_93; 
x_93 = lean_ctor_get(x_87, 0);
lean_dec(x_93);
return x_87;
}
else
{
lean_object* x_94; lean_object* x_95; 
x_94 = lean_ctor_get(x_87, 1);
lean_inc(x_94);
lean_dec(x_87);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_88);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
case 8:
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; 
x_96 = lean_ctor_get(x_3, 1);
lean_inc(x_96);
x_97 = lean_ctor_get(x_3, 2);
lean_inc(x_97);
x_98 = lean_ctor_get(x_3, 3);
lean_inc(x_98);
lean_dec(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_99 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__39(x_1, x_2, x_96, x_4);
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_unbox(x_100);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; 
lean_dec(x_100);
x_102 = lean_ctor_get(x_99, 1);
lean_inc(x_102);
lean_dec(x_99);
lean_inc(x_2);
lean_inc(x_1);
x_103 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__39(x_1, x_2, x_97, x_102);
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_unbox(x_104);
if (x_105 == 0)
{
lean_object* x_106; lean_object* x_107; 
lean_dec(x_104);
x_106 = lean_ctor_get(x_103, 1);
lean_inc(x_106);
lean_dec(x_103);
x_107 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__39(x_1, x_2, x_98, x_106);
return x_107;
}
else
{
uint8_t x_108; 
lean_dec(x_98);
lean_dec(x_2);
lean_dec(x_1);
x_108 = !lean_is_exclusive(x_103);
if (x_108 == 0)
{
lean_object* x_109; 
x_109 = lean_ctor_get(x_103, 0);
lean_dec(x_109);
return x_103;
}
else
{
lean_object* x_110; lean_object* x_111; 
x_110 = lean_ctor_get(x_103, 1);
lean_inc(x_110);
lean_dec(x_103);
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_104);
lean_ctor_set(x_111, 1, x_110);
return x_111;
}
}
}
else
{
uint8_t x_112; 
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_2);
lean_dec(x_1);
x_112 = !lean_is_exclusive(x_99);
if (x_112 == 0)
{
lean_object* x_113; 
x_113 = lean_ctor_get(x_99, 0);
lean_dec(x_113);
return x_99;
}
else
{
lean_object* x_114; lean_object* x_115; 
x_114 = lean_ctor_get(x_99, 1);
lean_inc(x_114);
lean_dec(x_99);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_100);
lean_ctor_set(x_115, 1, x_114);
return x_115;
}
}
}
case 10:
{
lean_object* x_116; lean_object* x_117; 
x_116 = lean_ctor_get(x_3, 1);
lean_inc(x_116);
lean_dec(x_3);
x_117 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__39(x_1, x_2, x_116, x_4);
return x_117;
}
case 11:
{
lean_object* x_118; lean_object* x_119; 
x_118 = lean_ctor_get(x_3, 2);
lean_inc(x_118);
lean_dec(x_3);
x_119 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__39(x_1, x_2, x_118, x_4);
return x_119;
}
default: 
{
uint8_t x_120; lean_object* x_121; lean_object* x_122; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_120 = 0;
x_121 = lean_box(x_120);
x_122 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set(x_122, 1, x_4);
return x_122;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__39(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
lean_inc(x_3);
x_5 = l___private_Lean_MetavarContext_0__Lean_DependsOn_shouldVisit(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_unbox(x_6);
lean_dec(x_6);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
x_17 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at_Lean_Meta_getFVarSetToGeneralize___spec__40(x_1, x_2, x_3, x_16);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at_Lean_Meta_getFVarSetToGeneralize___spec__41___at_Lean_Meta_getFVarSetToGeneralize___spec__49(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 5)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
lean_inc(x_1);
x_6 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at_Lean_Meta_getFVarSetToGeneralize___spec__41___at_Lean_Meta_getFVarSetToGeneralize___spec__49(x_1, x_4, x_3);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_unbox(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_7);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
lean_dec(x_6);
x_10 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__39___at_Lean_Meta_getFVarSetToGeneralize___spec__47(x_1, x_5, x_9);
return x_10;
}
else
{
uint8_t x_11; 
lean_dec(x_5);
lean_dec(x_1);
x_11 = !lean_is_exclusive(x_6);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_6, 0);
lean_dec(x_12);
return x_6;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_6, 1);
lean_inc(x_13);
lean_dec(x_6);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
else
{
lean_object* x_15; 
x_15 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__39___at_Lean_Meta_getFVarSetToGeneralize___spec__47(x_1, x_2, x_3);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at_Lean_Meta_getFVarSetToGeneralize___spec__40___at_Lean_Meta_getFVarSetToGeneralize___spec__48(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 1:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = l_Std_RBNode_findCore___at_Lean_Meta_mkGeneralizationForbiddenSet_visit___spec__1(x_1, x_4);
lean_dec(x_4);
lean_dec(x_1);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_6 = 0;
x_7 = lean_box(x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
else
{
uint8_t x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
x_9 = 1;
x_10 = lean_box(x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_3);
return x_11;
}
}
case 2:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
lean_dec(x_2);
x_13 = !lean_is_exclusive(x_3);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
x_15 = l_Lean_getExprMVarAssignment_x3f(x_12, x_14);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_ctor_set(x_3, 1, x_18);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_19 = l_Lean_MetavarContext_getDecl(x_18, x_12);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at_Lean_Meta_getFVarSetToGeneralize___spec__2___at_Lean_Meta_getFVarSetToGeneralize___spec__10___closed__1;
x_23 = l_Std_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__42(x_22, x_1, x_21);
x_24 = lean_box(x_23);
lean_ctor_set(x_15, 1, x_3);
lean_ctor_set(x_15, 0, x_24);
return x_15;
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_free_object(x_15);
lean_dec(x_18);
lean_dec(x_12);
x_25 = lean_ctor_get(x_17, 0);
lean_inc(x_25);
lean_dec(x_17);
x_26 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__39___at_Lean_Meta_getFVarSetToGeneralize___spec__47(x_1, x_25, x_3);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_15, 0);
x_28 = lean_ctor_get(x_15, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_15);
lean_inc(x_28);
lean_ctor_set(x_3, 1, x_28);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; 
x_29 = l_Lean_MetavarContext_getDecl(x_28, x_12);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec(x_30);
x_32 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at_Lean_Meta_getFVarSetToGeneralize___spec__2___at_Lean_Meta_getFVarSetToGeneralize___spec__10___closed__1;
x_33 = l_Std_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__42(x_32, x_1, x_31);
x_34 = lean_box(x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_3);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_28);
lean_dec(x_12);
x_36 = lean_ctor_get(x_27, 0);
lean_inc(x_36);
lean_dec(x_27);
x_37 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__39___at_Lean_Meta_getFVarSetToGeneralize___spec__47(x_1, x_36, x_3);
return x_37;
}
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_38 = lean_ctor_get(x_3, 0);
x_39 = lean_ctor_get(x_3, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_3);
lean_inc(x_12);
x_40 = l_Lean_getExprMVarAssignment_x3f(x_12, x_39);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_43 = x_40;
} else {
 lean_dec_ref(x_40);
 x_43 = lean_box(0);
}
lean_inc(x_42);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_38);
lean_ctor_set(x_44, 1, x_42);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; 
x_45 = l_Lean_MetavarContext_getDecl(x_42, x_12);
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
lean_dec(x_45);
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
lean_dec(x_46);
x_48 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at_Lean_Meta_getFVarSetToGeneralize___spec__2___at_Lean_Meta_getFVarSetToGeneralize___spec__10___closed__1;
x_49 = l_Std_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__42(x_48, x_1, x_47);
x_50 = lean_box(x_49);
if (lean_is_scalar(x_43)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_43;
}
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_44);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; 
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_12);
x_52 = lean_ctor_get(x_41, 0);
lean_inc(x_52);
lean_dec(x_41);
x_53 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__39___at_Lean_Meta_getFVarSetToGeneralize___spec__47(x_1, x_52, x_44);
return x_53;
}
}
}
case 5:
{
lean_object* x_54; uint8_t x_55; 
x_54 = l_Lean_Expr_getAppFn(x_2);
x_55 = l_Lean_Expr_isMVar(x_54);
if (x_55 == 0)
{
lean_object* x_56; 
lean_dec(x_54);
x_56 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at_Lean_Meta_getFVarSetToGeneralize___spec__41___at_Lean_Meta_getFVarSetToGeneralize___spec__49(x_1, x_2, x_3);
return x_56;
}
else
{
uint8_t x_57; 
x_57 = !lean_is_exclusive(x_3);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_58 = lean_ctor_get(x_3, 1);
lean_inc(x_2);
x_59 = l_Lean_instantiateMVars(x_2, x_58);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
lean_ctor_set(x_3, 1, x_61);
x_62 = l_Lean_Expr_getAppFn(x_60);
x_63 = lean_expr_eqv(x_62, x_54);
lean_dec(x_54);
lean_dec(x_62);
if (x_63 == 0)
{
lean_dec(x_2);
x_2 = x_60;
goto _start;
}
else
{
lean_object* x_65; 
lean_dec(x_60);
x_65 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at_Lean_Meta_getFVarSetToGeneralize___spec__41___at_Lean_Meta_getFVarSetToGeneralize___spec__49(x_1, x_2, x_3);
return x_65;
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_66 = lean_ctor_get(x_3, 0);
x_67 = lean_ctor_get(x_3, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_3);
lean_inc(x_2);
x_68 = l_Lean_instantiateMVars(x_2, x_67);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_66);
lean_ctor_set(x_71, 1, x_70);
x_72 = l_Lean_Expr_getAppFn(x_69);
x_73 = lean_expr_eqv(x_72, x_54);
lean_dec(x_54);
lean_dec(x_72);
if (x_73 == 0)
{
lean_dec(x_2);
x_2 = x_69;
x_3 = x_71;
goto _start;
}
else
{
lean_object* x_75; 
lean_dec(x_69);
x_75 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at_Lean_Meta_getFVarSetToGeneralize___spec__41___at_Lean_Meta_getFVarSetToGeneralize___spec__49(x_1, x_2, x_71);
return x_75;
}
}
}
}
case 6:
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_76 = lean_ctor_get(x_2, 1);
lean_inc(x_76);
x_77 = lean_ctor_get(x_2, 2);
lean_inc(x_77);
lean_dec(x_2);
lean_inc(x_1);
x_78 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__39___at_Lean_Meta_getFVarSetToGeneralize___spec__47(x_1, x_76, x_3);
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_unbox(x_79);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; 
lean_dec(x_79);
x_81 = lean_ctor_get(x_78, 1);
lean_inc(x_81);
lean_dec(x_78);
x_82 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__39___at_Lean_Meta_getFVarSetToGeneralize___spec__47(x_1, x_77, x_81);
return x_82;
}
else
{
uint8_t x_83; 
lean_dec(x_77);
lean_dec(x_1);
x_83 = !lean_is_exclusive(x_78);
if (x_83 == 0)
{
lean_object* x_84; 
x_84 = lean_ctor_get(x_78, 0);
lean_dec(x_84);
return x_78;
}
else
{
lean_object* x_85; lean_object* x_86; 
x_85 = lean_ctor_get(x_78, 1);
lean_inc(x_85);
lean_dec(x_78);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_79);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
}
case 7:
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; 
x_87 = lean_ctor_get(x_2, 1);
lean_inc(x_87);
x_88 = lean_ctor_get(x_2, 2);
lean_inc(x_88);
lean_dec(x_2);
lean_inc(x_1);
x_89 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__39___at_Lean_Meta_getFVarSetToGeneralize___spec__47(x_1, x_87, x_3);
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_unbox(x_90);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; 
lean_dec(x_90);
x_92 = lean_ctor_get(x_89, 1);
lean_inc(x_92);
lean_dec(x_89);
x_93 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__39___at_Lean_Meta_getFVarSetToGeneralize___spec__47(x_1, x_88, x_92);
return x_93;
}
else
{
uint8_t x_94; 
lean_dec(x_88);
lean_dec(x_1);
x_94 = !lean_is_exclusive(x_89);
if (x_94 == 0)
{
lean_object* x_95; 
x_95 = lean_ctor_get(x_89, 0);
lean_dec(x_95);
return x_89;
}
else
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_ctor_get(x_89, 1);
lean_inc(x_96);
lean_dec(x_89);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_90);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
}
case 8:
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_98 = lean_ctor_get(x_2, 1);
lean_inc(x_98);
x_99 = lean_ctor_get(x_2, 2);
lean_inc(x_99);
x_100 = lean_ctor_get(x_2, 3);
lean_inc(x_100);
lean_dec(x_2);
lean_inc(x_1);
x_101 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__39___at_Lean_Meta_getFVarSetToGeneralize___spec__47(x_1, x_98, x_3);
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_unbox(x_102);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; 
lean_dec(x_102);
x_104 = lean_ctor_get(x_101, 1);
lean_inc(x_104);
lean_dec(x_101);
lean_inc(x_1);
x_105 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__39___at_Lean_Meta_getFVarSetToGeneralize___spec__47(x_1, x_99, x_104);
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_unbox(x_106);
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; 
lean_dec(x_106);
x_108 = lean_ctor_get(x_105, 1);
lean_inc(x_108);
lean_dec(x_105);
x_109 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__39___at_Lean_Meta_getFVarSetToGeneralize___spec__47(x_1, x_100, x_108);
return x_109;
}
else
{
uint8_t x_110; 
lean_dec(x_100);
lean_dec(x_1);
x_110 = !lean_is_exclusive(x_105);
if (x_110 == 0)
{
lean_object* x_111; 
x_111 = lean_ctor_get(x_105, 0);
lean_dec(x_111);
return x_105;
}
else
{
lean_object* x_112; lean_object* x_113; 
x_112 = lean_ctor_get(x_105, 1);
lean_inc(x_112);
lean_dec(x_105);
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_106);
lean_ctor_set(x_113, 1, x_112);
return x_113;
}
}
}
else
{
uint8_t x_114; 
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_1);
x_114 = !lean_is_exclusive(x_101);
if (x_114 == 0)
{
lean_object* x_115; 
x_115 = lean_ctor_get(x_101, 0);
lean_dec(x_115);
return x_101;
}
else
{
lean_object* x_116; lean_object* x_117; 
x_116 = lean_ctor_get(x_101, 1);
lean_inc(x_116);
lean_dec(x_101);
x_117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_117, 0, x_102);
lean_ctor_set(x_117, 1, x_116);
return x_117;
}
}
}
case 10:
{
lean_object* x_118; lean_object* x_119; 
x_118 = lean_ctor_get(x_2, 1);
lean_inc(x_118);
lean_dec(x_2);
x_119 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__39___at_Lean_Meta_getFVarSetToGeneralize___spec__47(x_1, x_118, x_3);
return x_119;
}
case 11:
{
lean_object* x_120; lean_object* x_121; 
x_120 = lean_ctor_get(x_2, 2);
lean_inc(x_120);
lean_dec(x_2);
x_121 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__39___at_Lean_Meta_getFVarSetToGeneralize___spec__47(x_1, x_120, x_3);
return x_121;
}
default: 
{
uint8_t x_122; lean_object* x_123; lean_object* x_124; 
lean_dec(x_2);
lean_dec(x_1);
x_122 = 0;
x_123 = lean_box(x_122);
x_124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_3);
return x_124;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__39___at_Lean_Meta_getFVarSetToGeneralize___spec__47(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
lean_inc(x_2);
x_4 = l___private_Lean_MetavarContext_0__Lean_DependsOn_shouldVisit(x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_unbox(x_5);
lean_dec(x_5);
if (x_6 == 0)
{
uint8_t x_7; 
lean_dec(x_2);
lean_dec(x_1);
x_7 = !lean_is_exclusive(x_4);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_4, 0);
lean_dec(x_8);
x_9 = 0;
x_10 = lean_box(x_9);
lean_ctor_set(x_4, 0, x_10);
return x_4;
}
else
{
lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_4, 1);
lean_inc(x_11);
lean_dec(x_4);
x_12 = 0;
x_13 = lean_box(x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_4, 1);
lean_inc(x_15);
lean_dec(x_4);
x_16 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at_Lean_Meta_getFVarSetToGeneralize___spec__40___at_Lean_Meta_getFVarSetToGeneralize___spec__48(x_1, x_2, x_15);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at_Lean_Meta_getFVarSetToGeneralize___spec__52(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 5)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_7 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at_Lean_Meta_getFVarSetToGeneralize___spec__52(x_1, x_2, x_5, x_4);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_unbox(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_8);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_dec(x_7);
x_11 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__50(x_1, x_2, x_6, x_10);
return x_11;
}
else
{
uint8_t x_12; 
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_12 = !lean_is_exclusive(x_7);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_7, 0);
lean_dec(x_13);
return x_7;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_7, 1);
lean_inc(x_14);
lean_dec(x_7);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_8);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
else
{
lean_object* x_16; 
x_16 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__50(x_1, x_2, x_3, x_4);
return x_16;
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__55(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_uget(x_3, x_4);
lean_inc(x_2);
lean_inc(x_1);
x_8 = l_Std_PersistentArray_anyMAux___at_Lean_Meta_getFVarSetToGeneralize___spec__54(x_1, x_2, x_7);
if (x_8 == 0)
{
size_t x_9; size_t x_10; 
x_9 = 1;
x_10 = lean_usize_add(x_4, x_9);
x_4 = x_10;
goto _start;
}
else
{
uint8_t x_12; 
lean_dec(x_2);
lean_dec(x_1);
x_12 = 1;
return x_12;
}
}
else
{
uint8_t x_13; 
lean_dec(x_2);
lean_dec(x_1);
x_13 = 0;
return x_13;
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__56(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_array_uget(x_3, x_4);
if (lean_obj_tag(x_7) == 0)
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = lean_usize_add(x_4, x_8);
x_4 = x_9;
goto _start;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
lean_dec(x_7);
x_12 = l_Lean_LocalDecl_fvarId(x_11);
lean_dec(x_11);
lean_inc(x_2);
lean_inc(x_1);
x_13 = l_Std_RBNode_findCore___rarg(x_1, x_2, x_12);
if (lean_obj_tag(x_13) == 0)
{
size_t x_14; size_t x_15; 
x_14 = 1;
x_15 = lean_usize_add(x_4, x_14);
x_4 = x_15;
goto _start;
}
else
{
uint8_t x_17; 
lean_dec(x_13);
lean_dec(x_2);
lean_dec(x_1);
x_17 = 1;
return x_17;
}
}
}
else
{
uint8_t x_18; 
lean_dec(x_2);
lean_dec(x_1);
x_18 = 0;
return x_18;
}
}
}
LEAN_EXPORT uint8_t l_Std_PersistentArray_anyMAux___at_Lean_Meta_getFVarSetToGeneralize___spec__54(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_array_get_size(x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_lt(x_6, x_5);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_8 = 0;
return x_8;
}
else
{
uint8_t x_9; 
x_9 = lean_nat_dec_le(x_5, x_5);
if (x_9 == 0)
{
uint8_t x_10; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_10 = 0;
return x_10;
}
else
{
size_t x_11; size_t x_12; uint8_t x_13; 
x_11 = 0;
x_12 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_13 = l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__55(x_1, x_2, x_4, x_11, x_12);
lean_dec(x_4);
return x_13;
}
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_3, 0);
lean_inc(x_14);
lean_dec(x_3);
x_15 = lean_array_get_size(x_14);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_nat_dec_lt(x_16, x_15);
if (x_17 == 0)
{
uint8_t x_18; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_2);
lean_dec(x_1);
x_18 = 0;
return x_18;
}
else
{
uint8_t x_19; 
x_19 = lean_nat_dec_le(x_15, x_15);
if (x_19 == 0)
{
uint8_t x_20; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_2);
lean_dec(x_1);
x_20 = 0;
return x_20;
}
else
{
size_t x_21; size_t x_22; uint8_t x_23; 
x_21 = 0;
x_22 = lean_usize_of_nat(x_15);
lean_dec(x_15);
x_23 = l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__56(x_1, x_2, x_14, x_21, x_22);
lean_dec(x_14);
return x_23;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__57(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_array_uget(x_3, x_4);
if (lean_obj_tag(x_7) == 0)
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = lean_usize_add(x_4, x_8);
x_4 = x_9;
goto _start;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
lean_dec(x_7);
x_12 = l_Lean_LocalDecl_fvarId(x_11);
lean_dec(x_11);
lean_inc(x_2);
lean_inc(x_1);
x_13 = l_Std_RBNode_findCore___rarg(x_1, x_2, x_12);
if (lean_obj_tag(x_13) == 0)
{
size_t x_14; size_t x_15; 
x_14 = 1;
x_15 = lean_usize_add(x_4, x_14);
x_4 = x_15;
goto _start;
}
else
{
uint8_t x_17; 
lean_dec(x_13);
lean_dec(x_2);
lean_dec(x_1);
x_17 = 1;
return x_17;
}
}
}
else
{
uint8_t x_18; 
lean_dec(x_2);
lean_dec(x_1);
x_18 = 0;
return x_18;
}
}
}
LEAN_EXPORT uint8_t l_Std_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__53(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_5 = l_Std_PersistentArray_anyMAux___at_Lean_Meta_getFVarSetToGeneralize___spec__54(x_1, x_2, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec(x_3);
x_7 = lean_array_get_size(x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_lt(x_8, x_7);
if (x_9 == 0)
{
uint8_t x_10; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_10 = 0;
return x_10;
}
else
{
uint8_t x_11; 
x_11 = lean_nat_dec_le(x_7, x_7);
if (x_11 == 0)
{
uint8_t x_12; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_12 = 0;
return x_12;
}
else
{
size_t x_13; size_t x_14; uint8_t x_15; 
x_13 = 0;
x_14 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_15 = l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__57(x_1, x_2, x_6, x_13, x_14);
lean_dec(x_6);
return x_15;
}
}
}
else
{
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at_Lean_Meta_getFVarSetToGeneralize___spec__51(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_3)) {
case 1:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
x_6 = l_Std_RBNode_findCore___rarg(x_1, x_2, x_5);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; lean_object* x_8; lean_object* x_9; 
x_7 = 0;
x_8 = lean_box(x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_4);
return x_9;
}
else
{
uint8_t x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_6);
x_10 = 1;
x_11 = lean_box(x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_4);
return x_12;
}
}
case 2:
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_3, 0);
lean_inc(x_13);
lean_dec(x_3);
x_14 = !lean_is_exclusive(x_4);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_4, 1);
lean_inc(x_13);
x_16 = l_Lean_getExprMVarAssignment_x3f(x_13, x_15);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_ctor_set(x_4, 1, x_19);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_20 = l_Lean_MetavarContext_getDecl(x_19, x_13);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = l_Std_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__53(x_1, x_2, x_22);
x_24 = lean_box(x_23);
lean_ctor_set(x_16, 1, x_4);
lean_ctor_set(x_16, 0, x_24);
return x_16;
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_free_object(x_16);
lean_dec(x_19);
lean_dec(x_13);
x_25 = lean_ctor_get(x_18, 0);
lean_inc(x_25);
lean_dec(x_18);
x_26 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__50(x_1, x_2, x_25, x_4);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_16, 0);
x_28 = lean_ctor_get(x_16, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_16);
lean_inc(x_28);
lean_ctor_set(x_4, 1, x_28);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; 
x_29 = l_Lean_MetavarContext_getDecl(x_28, x_13);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec(x_30);
x_32 = l_Std_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__53(x_1, x_2, x_31);
x_33 = lean_box(x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_4);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_28);
lean_dec(x_13);
x_35 = lean_ctor_get(x_27, 0);
lean_inc(x_35);
lean_dec(x_27);
x_36 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__50(x_1, x_2, x_35, x_4);
return x_36;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_37 = lean_ctor_get(x_4, 0);
x_38 = lean_ctor_get(x_4, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_4);
lean_inc(x_13);
x_39 = l_Lean_getExprMVarAssignment_x3f(x_13, x_38);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_42 = x_39;
} else {
 lean_dec_ref(x_39);
 x_42 = lean_box(0);
}
lean_inc(x_41);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_37);
lean_ctor_set(x_43, 1, x_41);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; 
x_44 = l_Lean_MetavarContext_getDecl(x_41, x_13);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
lean_dec(x_45);
x_47 = l_Std_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__53(x_1, x_2, x_46);
x_48 = lean_box(x_47);
if (lean_is_scalar(x_42)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_42;
}
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_43);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; 
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_13);
x_50 = lean_ctor_get(x_40, 0);
lean_inc(x_50);
lean_dec(x_40);
x_51 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__50(x_1, x_2, x_50, x_43);
return x_51;
}
}
}
case 5:
{
lean_object* x_52; uint8_t x_53; 
x_52 = l_Lean_Expr_getAppFn(x_3);
x_53 = l_Lean_Expr_isMVar(x_52);
if (x_53 == 0)
{
lean_object* x_54; 
lean_dec(x_52);
x_54 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at_Lean_Meta_getFVarSetToGeneralize___spec__52(x_1, x_2, x_3, x_4);
return x_54;
}
else
{
uint8_t x_55; 
x_55 = !lean_is_exclusive(x_4);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_56 = lean_ctor_get(x_4, 1);
lean_inc(x_3);
x_57 = l_Lean_instantiateMVars(x_3, x_56);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
lean_ctor_set(x_4, 1, x_59);
x_60 = l_Lean_Expr_getAppFn(x_58);
x_61 = lean_expr_eqv(x_60, x_52);
lean_dec(x_52);
lean_dec(x_60);
if (x_61 == 0)
{
lean_dec(x_3);
x_3 = x_58;
goto _start;
}
else
{
lean_object* x_63; 
lean_dec(x_58);
x_63 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at_Lean_Meta_getFVarSetToGeneralize___spec__52(x_1, x_2, x_3, x_4);
return x_63;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_64 = lean_ctor_get(x_4, 0);
x_65 = lean_ctor_get(x_4, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_4);
lean_inc(x_3);
x_66 = l_Lean_instantiateMVars(x_3, x_65);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_64);
lean_ctor_set(x_69, 1, x_68);
x_70 = l_Lean_Expr_getAppFn(x_67);
x_71 = lean_expr_eqv(x_70, x_52);
lean_dec(x_52);
lean_dec(x_70);
if (x_71 == 0)
{
lean_dec(x_3);
x_3 = x_67;
x_4 = x_69;
goto _start;
}
else
{
lean_object* x_73; 
lean_dec(x_67);
x_73 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at_Lean_Meta_getFVarSetToGeneralize___spec__52(x_1, x_2, x_3, x_69);
return x_73;
}
}
}
}
case 6:
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_74 = lean_ctor_get(x_3, 1);
lean_inc(x_74);
x_75 = lean_ctor_get(x_3, 2);
lean_inc(x_75);
lean_dec(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_76 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__50(x_1, x_2, x_74, x_4);
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_unbox(x_77);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; 
lean_dec(x_77);
x_79 = lean_ctor_get(x_76, 1);
lean_inc(x_79);
lean_dec(x_76);
x_80 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__50(x_1, x_2, x_75, x_79);
return x_80;
}
else
{
uint8_t x_81; 
lean_dec(x_75);
lean_dec(x_2);
lean_dec(x_1);
x_81 = !lean_is_exclusive(x_76);
if (x_81 == 0)
{
lean_object* x_82; 
x_82 = lean_ctor_get(x_76, 0);
lean_dec(x_82);
return x_76;
}
else
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_76, 1);
lean_inc(x_83);
lean_dec(x_76);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_77);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
case 7:
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_85 = lean_ctor_get(x_3, 1);
lean_inc(x_85);
x_86 = lean_ctor_get(x_3, 2);
lean_inc(x_86);
lean_dec(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_87 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__50(x_1, x_2, x_85, x_4);
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_unbox(x_88);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; 
lean_dec(x_88);
x_90 = lean_ctor_get(x_87, 1);
lean_inc(x_90);
lean_dec(x_87);
x_91 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__50(x_1, x_2, x_86, x_90);
return x_91;
}
else
{
uint8_t x_92; 
lean_dec(x_86);
lean_dec(x_2);
lean_dec(x_1);
x_92 = !lean_is_exclusive(x_87);
if (x_92 == 0)
{
lean_object* x_93; 
x_93 = lean_ctor_get(x_87, 0);
lean_dec(x_93);
return x_87;
}
else
{
lean_object* x_94; lean_object* x_95; 
x_94 = lean_ctor_get(x_87, 1);
lean_inc(x_94);
lean_dec(x_87);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_88);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
case 8:
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; 
x_96 = lean_ctor_get(x_3, 1);
lean_inc(x_96);
x_97 = lean_ctor_get(x_3, 2);
lean_inc(x_97);
x_98 = lean_ctor_get(x_3, 3);
lean_inc(x_98);
lean_dec(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_99 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__50(x_1, x_2, x_96, x_4);
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_unbox(x_100);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; 
lean_dec(x_100);
x_102 = lean_ctor_get(x_99, 1);
lean_inc(x_102);
lean_dec(x_99);
lean_inc(x_2);
lean_inc(x_1);
x_103 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__50(x_1, x_2, x_97, x_102);
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_unbox(x_104);
if (x_105 == 0)
{
lean_object* x_106; lean_object* x_107; 
lean_dec(x_104);
x_106 = lean_ctor_get(x_103, 1);
lean_inc(x_106);
lean_dec(x_103);
x_107 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__50(x_1, x_2, x_98, x_106);
return x_107;
}
else
{
uint8_t x_108; 
lean_dec(x_98);
lean_dec(x_2);
lean_dec(x_1);
x_108 = !lean_is_exclusive(x_103);
if (x_108 == 0)
{
lean_object* x_109; 
x_109 = lean_ctor_get(x_103, 0);
lean_dec(x_109);
return x_103;
}
else
{
lean_object* x_110; lean_object* x_111; 
x_110 = lean_ctor_get(x_103, 1);
lean_inc(x_110);
lean_dec(x_103);
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_104);
lean_ctor_set(x_111, 1, x_110);
return x_111;
}
}
}
else
{
uint8_t x_112; 
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_2);
lean_dec(x_1);
x_112 = !lean_is_exclusive(x_99);
if (x_112 == 0)
{
lean_object* x_113; 
x_113 = lean_ctor_get(x_99, 0);
lean_dec(x_113);
return x_99;
}
else
{
lean_object* x_114; lean_object* x_115; 
x_114 = lean_ctor_get(x_99, 1);
lean_inc(x_114);
lean_dec(x_99);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_100);
lean_ctor_set(x_115, 1, x_114);
return x_115;
}
}
}
case 10:
{
lean_object* x_116; lean_object* x_117; 
x_116 = lean_ctor_get(x_3, 1);
lean_inc(x_116);
lean_dec(x_3);
x_117 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__50(x_1, x_2, x_116, x_4);
return x_117;
}
case 11:
{
lean_object* x_118; lean_object* x_119; 
x_118 = lean_ctor_get(x_3, 2);
lean_inc(x_118);
lean_dec(x_3);
x_119 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__50(x_1, x_2, x_118, x_4);
return x_119;
}
default: 
{
uint8_t x_120; lean_object* x_121; lean_object* x_122; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_120 = 0;
x_121 = lean_box(x_120);
x_122 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set(x_122, 1, x_4);
return x_122;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__50(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
lean_inc(x_3);
x_5 = l___private_Lean_MetavarContext_0__Lean_DependsOn_shouldVisit(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_unbox(x_6);
lean_dec(x_6);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
x_17 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at_Lean_Meta_getFVarSetToGeneralize___spec__51(x_1, x_2, x_3, x_16);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at_Lean_Meta_getFVarSetToGeneralize___spec__52___at_Lean_Meta_getFVarSetToGeneralize___spec__60(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 5)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
lean_inc(x_1);
x_6 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at_Lean_Meta_getFVarSetToGeneralize___spec__52___at_Lean_Meta_getFVarSetToGeneralize___spec__60(x_1, x_4, x_3);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_unbox(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_7);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
lean_dec(x_6);
x_10 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__50___at_Lean_Meta_getFVarSetToGeneralize___spec__58(x_1, x_5, x_9);
return x_10;
}
else
{
uint8_t x_11; 
lean_dec(x_5);
lean_dec(x_1);
x_11 = !lean_is_exclusive(x_6);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_6, 0);
lean_dec(x_12);
return x_6;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_6, 1);
lean_inc(x_13);
lean_dec(x_6);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
else
{
lean_object* x_15; 
x_15 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__50___at_Lean_Meta_getFVarSetToGeneralize___spec__58(x_1, x_2, x_3);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at_Lean_Meta_getFVarSetToGeneralize___spec__51___at_Lean_Meta_getFVarSetToGeneralize___spec__59(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 1:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = l_Std_RBNode_findCore___at_Lean_Meta_mkGeneralizationForbiddenSet_visit___spec__1(x_1, x_4);
lean_dec(x_4);
lean_dec(x_1);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_6 = 0;
x_7 = lean_box(x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
else
{
uint8_t x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
x_9 = 1;
x_10 = lean_box(x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_3);
return x_11;
}
}
case 2:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
lean_dec(x_2);
x_13 = !lean_is_exclusive(x_3);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
x_15 = l_Lean_getExprMVarAssignment_x3f(x_12, x_14);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_ctor_set(x_3, 1, x_18);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_19 = l_Lean_MetavarContext_getDecl(x_18, x_12);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at_Lean_Meta_getFVarSetToGeneralize___spec__2___at_Lean_Meta_getFVarSetToGeneralize___spec__10___closed__1;
x_23 = l_Std_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__53(x_22, x_1, x_21);
x_24 = lean_box(x_23);
lean_ctor_set(x_15, 1, x_3);
lean_ctor_set(x_15, 0, x_24);
return x_15;
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_free_object(x_15);
lean_dec(x_18);
lean_dec(x_12);
x_25 = lean_ctor_get(x_17, 0);
lean_inc(x_25);
lean_dec(x_17);
x_26 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__50___at_Lean_Meta_getFVarSetToGeneralize___spec__58(x_1, x_25, x_3);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_15, 0);
x_28 = lean_ctor_get(x_15, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_15);
lean_inc(x_28);
lean_ctor_set(x_3, 1, x_28);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; 
x_29 = l_Lean_MetavarContext_getDecl(x_28, x_12);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec(x_30);
x_32 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at_Lean_Meta_getFVarSetToGeneralize___spec__2___at_Lean_Meta_getFVarSetToGeneralize___spec__10___closed__1;
x_33 = l_Std_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__53(x_32, x_1, x_31);
x_34 = lean_box(x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_3);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_28);
lean_dec(x_12);
x_36 = lean_ctor_get(x_27, 0);
lean_inc(x_36);
lean_dec(x_27);
x_37 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__50___at_Lean_Meta_getFVarSetToGeneralize___spec__58(x_1, x_36, x_3);
return x_37;
}
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_38 = lean_ctor_get(x_3, 0);
x_39 = lean_ctor_get(x_3, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_3);
lean_inc(x_12);
x_40 = l_Lean_getExprMVarAssignment_x3f(x_12, x_39);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_43 = x_40;
} else {
 lean_dec_ref(x_40);
 x_43 = lean_box(0);
}
lean_inc(x_42);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_38);
lean_ctor_set(x_44, 1, x_42);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; 
x_45 = l_Lean_MetavarContext_getDecl(x_42, x_12);
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
lean_dec(x_45);
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
lean_dec(x_46);
x_48 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at_Lean_Meta_getFVarSetToGeneralize___spec__2___at_Lean_Meta_getFVarSetToGeneralize___spec__10___closed__1;
x_49 = l_Std_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__53(x_48, x_1, x_47);
x_50 = lean_box(x_49);
if (lean_is_scalar(x_43)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_43;
}
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_44);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; 
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_12);
x_52 = lean_ctor_get(x_41, 0);
lean_inc(x_52);
lean_dec(x_41);
x_53 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__50___at_Lean_Meta_getFVarSetToGeneralize___spec__58(x_1, x_52, x_44);
return x_53;
}
}
}
case 5:
{
lean_object* x_54; uint8_t x_55; 
x_54 = l_Lean_Expr_getAppFn(x_2);
x_55 = l_Lean_Expr_isMVar(x_54);
if (x_55 == 0)
{
lean_object* x_56; 
lean_dec(x_54);
x_56 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at_Lean_Meta_getFVarSetToGeneralize___spec__52___at_Lean_Meta_getFVarSetToGeneralize___spec__60(x_1, x_2, x_3);
return x_56;
}
else
{
uint8_t x_57; 
x_57 = !lean_is_exclusive(x_3);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_58 = lean_ctor_get(x_3, 1);
lean_inc(x_2);
x_59 = l_Lean_instantiateMVars(x_2, x_58);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
lean_ctor_set(x_3, 1, x_61);
x_62 = l_Lean_Expr_getAppFn(x_60);
x_63 = lean_expr_eqv(x_62, x_54);
lean_dec(x_54);
lean_dec(x_62);
if (x_63 == 0)
{
lean_dec(x_2);
x_2 = x_60;
goto _start;
}
else
{
lean_object* x_65; 
lean_dec(x_60);
x_65 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at_Lean_Meta_getFVarSetToGeneralize___spec__52___at_Lean_Meta_getFVarSetToGeneralize___spec__60(x_1, x_2, x_3);
return x_65;
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_66 = lean_ctor_get(x_3, 0);
x_67 = lean_ctor_get(x_3, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_3);
lean_inc(x_2);
x_68 = l_Lean_instantiateMVars(x_2, x_67);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_66);
lean_ctor_set(x_71, 1, x_70);
x_72 = l_Lean_Expr_getAppFn(x_69);
x_73 = lean_expr_eqv(x_72, x_54);
lean_dec(x_54);
lean_dec(x_72);
if (x_73 == 0)
{
lean_dec(x_2);
x_2 = x_69;
x_3 = x_71;
goto _start;
}
else
{
lean_object* x_75; 
lean_dec(x_69);
x_75 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at_Lean_Meta_getFVarSetToGeneralize___spec__52___at_Lean_Meta_getFVarSetToGeneralize___spec__60(x_1, x_2, x_71);
return x_75;
}
}
}
}
case 6:
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_76 = lean_ctor_get(x_2, 1);
lean_inc(x_76);
x_77 = lean_ctor_get(x_2, 2);
lean_inc(x_77);
lean_dec(x_2);
lean_inc(x_1);
x_78 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__50___at_Lean_Meta_getFVarSetToGeneralize___spec__58(x_1, x_76, x_3);
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_unbox(x_79);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; 
lean_dec(x_79);
x_81 = lean_ctor_get(x_78, 1);
lean_inc(x_81);
lean_dec(x_78);
x_82 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__50___at_Lean_Meta_getFVarSetToGeneralize___spec__58(x_1, x_77, x_81);
return x_82;
}
else
{
uint8_t x_83; 
lean_dec(x_77);
lean_dec(x_1);
x_83 = !lean_is_exclusive(x_78);
if (x_83 == 0)
{
lean_object* x_84; 
x_84 = lean_ctor_get(x_78, 0);
lean_dec(x_84);
return x_78;
}
else
{
lean_object* x_85; lean_object* x_86; 
x_85 = lean_ctor_get(x_78, 1);
lean_inc(x_85);
lean_dec(x_78);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_79);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
}
case 7:
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; 
x_87 = lean_ctor_get(x_2, 1);
lean_inc(x_87);
x_88 = lean_ctor_get(x_2, 2);
lean_inc(x_88);
lean_dec(x_2);
lean_inc(x_1);
x_89 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__50___at_Lean_Meta_getFVarSetToGeneralize___spec__58(x_1, x_87, x_3);
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_unbox(x_90);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; 
lean_dec(x_90);
x_92 = lean_ctor_get(x_89, 1);
lean_inc(x_92);
lean_dec(x_89);
x_93 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__50___at_Lean_Meta_getFVarSetToGeneralize___spec__58(x_1, x_88, x_92);
return x_93;
}
else
{
uint8_t x_94; 
lean_dec(x_88);
lean_dec(x_1);
x_94 = !lean_is_exclusive(x_89);
if (x_94 == 0)
{
lean_object* x_95; 
x_95 = lean_ctor_get(x_89, 0);
lean_dec(x_95);
return x_89;
}
else
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_ctor_get(x_89, 1);
lean_inc(x_96);
lean_dec(x_89);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_90);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
}
case 8:
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_98 = lean_ctor_get(x_2, 1);
lean_inc(x_98);
x_99 = lean_ctor_get(x_2, 2);
lean_inc(x_99);
x_100 = lean_ctor_get(x_2, 3);
lean_inc(x_100);
lean_dec(x_2);
lean_inc(x_1);
x_101 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__50___at_Lean_Meta_getFVarSetToGeneralize___spec__58(x_1, x_98, x_3);
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_unbox(x_102);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; 
lean_dec(x_102);
x_104 = lean_ctor_get(x_101, 1);
lean_inc(x_104);
lean_dec(x_101);
lean_inc(x_1);
x_105 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__50___at_Lean_Meta_getFVarSetToGeneralize___spec__58(x_1, x_99, x_104);
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_unbox(x_106);
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; 
lean_dec(x_106);
x_108 = lean_ctor_get(x_105, 1);
lean_inc(x_108);
lean_dec(x_105);
x_109 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__50___at_Lean_Meta_getFVarSetToGeneralize___spec__58(x_1, x_100, x_108);
return x_109;
}
else
{
uint8_t x_110; 
lean_dec(x_100);
lean_dec(x_1);
x_110 = !lean_is_exclusive(x_105);
if (x_110 == 0)
{
lean_object* x_111; 
x_111 = lean_ctor_get(x_105, 0);
lean_dec(x_111);
return x_105;
}
else
{
lean_object* x_112; lean_object* x_113; 
x_112 = lean_ctor_get(x_105, 1);
lean_inc(x_112);
lean_dec(x_105);
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_106);
lean_ctor_set(x_113, 1, x_112);
return x_113;
}
}
}
else
{
uint8_t x_114; 
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_1);
x_114 = !lean_is_exclusive(x_101);
if (x_114 == 0)
{
lean_object* x_115; 
x_115 = lean_ctor_get(x_101, 0);
lean_dec(x_115);
return x_101;
}
else
{
lean_object* x_116; lean_object* x_117; 
x_116 = lean_ctor_get(x_101, 1);
lean_inc(x_116);
lean_dec(x_101);
x_117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_117, 0, x_102);
lean_ctor_set(x_117, 1, x_116);
return x_117;
}
}
}
case 10:
{
lean_object* x_118; lean_object* x_119; 
x_118 = lean_ctor_get(x_2, 1);
lean_inc(x_118);
lean_dec(x_2);
x_119 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__50___at_Lean_Meta_getFVarSetToGeneralize___spec__58(x_1, x_118, x_3);
return x_119;
}
case 11:
{
lean_object* x_120; lean_object* x_121; 
x_120 = lean_ctor_get(x_2, 2);
lean_inc(x_120);
lean_dec(x_2);
x_121 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__50___at_Lean_Meta_getFVarSetToGeneralize___spec__58(x_1, x_120, x_3);
return x_121;
}
default: 
{
uint8_t x_122; lean_object* x_123; lean_object* x_124; 
lean_dec(x_2);
lean_dec(x_1);
x_122 = 0;
x_123 = lean_box(x_122);
x_124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_3);
return x_124;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__50___at_Lean_Meta_getFVarSetToGeneralize___spec__58(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
lean_inc(x_2);
x_4 = l___private_Lean_MetavarContext_0__Lean_DependsOn_shouldVisit(x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_unbox(x_5);
lean_dec(x_5);
if (x_6 == 0)
{
uint8_t x_7; 
lean_dec(x_2);
lean_dec(x_1);
x_7 = !lean_is_exclusive(x_4);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_4, 0);
lean_dec(x_8);
x_9 = 0;
x_10 = lean_box(x_9);
lean_ctor_set(x_4, 0, x_10);
return x_4;
}
else
{
lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_4, 1);
lean_inc(x_11);
lean_dec(x_4);
x_12 = 0;
x_13 = lean_box(x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_4, 1);
lean_inc(x_15);
lean_dec(x_4);
x_16 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at_Lean_Meta_getFVarSetToGeneralize___spec__51___at_Lean_Meta_getFVarSetToGeneralize___spec__59(x_1, x_2, x_15);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_getFVarSetToGeneralize___spec__63(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, size_t x_7, size_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; 
x_15 = lean_usize_dec_lt(x_8, x_7);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_9);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
else
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_array_uget(x_6, x_8);
x_18 = !lean_is_exclusive(x_9);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_9, 1);
x_20 = lean_ctor_get(x_9, 0);
lean_dec(x_20);
lean_inc(x_10);
lean_inc(x_19);
lean_inc(x_3);
lean_inc(x_1);
x_21 = l_Std_PersistentArray_forInAux___at_Lean_Meta_getFVarSetToGeneralize___spec__62(x_1, x_2, x_3, x_4, x_17, x_19, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_17);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_21);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_21, 0);
lean_dec(x_24);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_9, 0, x_25);
lean_ctor_set(x_21, 0, x_9);
return x_21;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_21, 1);
lean_inc(x_26);
lean_dec(x_21);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_22);
lean_ctor_set(x_9, 0, x_27);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_9);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; size_t x_31; size_t x_32; 
lean_dec(x_19);
x_29 = lean_ctor_get(x_21, 1);
lean_inc(x_29);
lean_dec(x_21);
x_30 = lean_ctor_get(x_22, 0);
lean_inc(x_30);
lean_dec(x_22);
lean_inc(x_5);
lean_ctor_set(x_9, 1, x_30);
lean_ctor_set(x_9, 0, x_5);
x_31 = 1;
x_32 = lean_usize_add(x_8, x_31);
x_8 = x_32;
x_14 = x_29;
goto _start;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_9, 1);
lean_inc(x_34);
lean_dec(x_9);
lean_inc(x_10);
lean_inc(x_34);
lean_inc(x_3);
lean_inc(x_1);
x_35 = l_Std_PersistentArray_forInAux___at_Lean_Meta_getFVarSetToGeneralize___spec__62(x_1, x_2, x_3, x_4, x_17, x_34, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_17);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_38 = x_35;
} else {
 lean_dec_ref(x_35);
 x_38 = lean_box(0);
}
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_36);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_34);
if (lean_is_scalar(x_38)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_38;
}
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_37);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; size_t x_45; size_t x_46; 
lean_dec(x_34);
x_42 = lean_ctor_get(x_35, 1);
lean_inc(x_42);
lean_dec(x_35);
x_43 = lean_ctor_get(x_36, 0);
lean_inc(x_43);
lean_dec(x_36);
lean_inc(x_5);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_5);
lean_ctor_set(x_44, 1, x_43);
x_45 = 1;
x_46 = lean_usize_add(x_8, x_45);
x_8 = x_46;
x_9 = x_44;
x_14 = x_42;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_getFVarSetToGeneralize___spec__64(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = lean_usize_dec_lt(x_7, x_6);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_4);
lean_dec(x_3);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_8);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_16 = lean_array_uget(x_5, x_7);
x_25 = lean_ctor_get(x_8, 1);
lean_inc(x_25);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_26 = x_8;
} else {
 lean_dec_ref(x_8);
 x_26 = lean_box(0);
}
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_44; size_t x_45; size_t x_46; 
lean_dec(x_26);
lean_inc(x_4);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_4);
lean_ctor_set(x_44, 1, x_25);
x_45 = 1;
x_46 = lean_usize_add(x_7, x_45);
x_7 = x_46;
x_8 = x_44;
goto _start;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_186; 
x_48 = lean_ctor_get(x_16, 0);
lean_inc(x_48);
lean_dec(x_16);
x_49 = lean_ctor_get(x_25, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_25, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_51 = x_25;
} else {
 lean_dec_ref(x_25);
 x_51 = lean_box(0);
}
x_52 = l_Lean_LocalDecl_fvarId(x_48);
x_186 = l_Std_RBNode_findCore___at_Lean_Meta_mkGeneralizationForbiddenSet_visit___spec__1(x_1, x_52);
if (lean_obj_tag(x_186) == 0)
{
uint8_t x_187; 
x_187 = l_Lean_LocalDecl_isAuxDecl(x_48);
if (x_187 == 0)
{
uint8_t x_188; uint8_t x_189; 
x_188 = l_Lean_LocalDecl_binderInfo(x_48);
x_189 = l_Lean_BinderInfo_isInstImplicit(x_188);
if (x_189 == 0)
{
if (x_2 == 0)
{
lean_object* x_190; 
x_190 = lean_box(0);
x_53 = x_190;
goto block_185;
}
else
{
uint8_t x_191; 
x_191 = l_Lean_LocalDecl_isLet(x_48);
if (x_191 == 0)
{
lean_object* x_192; 
x_192 = lean_box(0);
x_53 = x_192;
goto block_185;
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; 
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_48);
x_193 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_193, 0, x_49);
lean_ctor_set(x_193, 1, x_50);
x_194 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_194, 0, x_193);
x_195 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_195, 0, x_194);
lean_ctor_set(x_195, 1, x_13);
x_27 = x_195;
goto block_43;
}
}
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; 
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_48);
x_196 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_196, 0, x_49);
lean_ctor_set(x_196, 1, x_50);
x_197 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_197, 0, x_196);
x_198 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_198, 0, x_197);
lean_ctor_set(x_198, 1, x_13);
x_27 = x_198;
goto block_43;
}
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; 
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_48);
x_199 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_199, 0, x_49);
lean_ctor_set(x_199, 1, x_50);
x_200 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_200, 0, x_199);
x_201 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_201, 0, x_200);
lean_ctor_set(x_201, 1, x_13);
x_27 = x_201;
goto block_43;
}
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; 
lean_dec(x_186);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_48);
x_202 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_202, 0, x_49);
lean_ctor_set(x_202, 1, x_50);
x_203 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_203, 0, x_202);
x_204 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_204, 0, x_203);
lean_ctor_set(x_204, 1, x_13);
x_27 = x_204;
goto block_43;
}
block_185:
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; lean_object* x_60; lean_object* x_105; uint8_t x_106; lean_object* x_107; 
lean_dec(x_53);
x_54 = lean_st_ref_get(x_12, x_13);
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
lean_dec(x_54);
x_56 = lean_st_ref_take(x_10, x_55);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_105 = lean_ctor_get(x_57, 0);
lean_inc(x_105);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; uint8_t x_145; 
x_142 = lean_ctor_get(x_48, 3);
lean_inc(x_142);
lean_dec(x_48);
x_143 = l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1;
lean_inc(x_105);
x_144 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set(x_144, 1, x_105);
x_145 = l_Lean_Expr_hasFVar(x_142);
if (x_145 == 0)
{
uint8_t x_146; 
x_146 = l_Lean_Expr_hasMVar(x_142);
if (x_146 == 0)
{
uint8_t x_147; 
lean_dec(x_142);
x_147 = 0;
x_106 = x_147;
x_107 = x_144;
goto block_141;
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; uint8_t x_151; 
lean_inc(x_50);
x_148 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__1___at_Lean_Meta_getFVarSetToGeneralize___spec__9(x_50, x_142, x_144);
x_149 = lean_ctor_get(x_148, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_148, 1);
lean_inc(x_150);
lean_dec(x_148);
x_151 = lean_unbox(x_149);
lean_dec(x_149);
x_106 = x_151;
x_107 = x_150;
goto block_141;
}
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; uint8_t x_155; 
lean_inc(x_50);
x_152 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__12___at_Lean_Meta_getFVarSetToGeneralize___spec__20(x_50, x_142, x_144);
x_153 = lean_ctor_get(x_152, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_152, 1);
lean_inc(x_154);
lean_dec(x_152);
x_155 = lean_unbox(x_153);
lean_dec(x_153);
x_106 = x_155;
x_107 = x_154;
goto block_141;
}
}
else
{
lean_object* x_156; lean_object* x_157; uint8_t x_158; lean_object* x_159; lean_object* x_172; lean_object* x_173; uint8_t x_174; 
x_156 = lean_ctor_get(x_48, 3);
lean_inc(x_156);
x_157 = lean_ctor_get(x_48, 4);
lean_inc(x_157);
lean_dec(x_48);
x_172 = l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1;
lean_inc(x_105);
x_173 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_173, 0, x_172);
lean_ctor_set(x_173, 1, x_105);
x_174 = l_Lean_Expr_hasFVar(x_156);
if (x_174 == 0)
{
uint8_t x_175; 
x_175 = l_Lean_Expr_hasMVar(x_156);
if (x_175 == 0)
{
uint8_t x_176; 
lean_dec(x_156);
x_176 = 0;
x_158 = x_176;
x_159 = x_173;
goto block_171;
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; uint8_t x_180; 
lean_inc(x_50);
x_177 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__39___at_Lean_Meta_getFVarSetToGeneralize___spec__47(x_50, x_156, x_173);
x_178 = lean_ctor_get(x_177, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_177, 1);
lean_inc(x_179);
lean_dec(x_177);
x_180 = lean_unbox(x_178);
lean_dec(x_178);
x_158 = x_180;
x_159 = x_179;
goto block_171;
}
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; uint8_t x_184; 
lean_inc(x_50);
x_181 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__50___at_Lean_Meta_getFVarSetToGeneralize___spec__58(x_50, x_156, x_173);
x_182 = lean_ctor_get(x_181, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_181, 1);
lean_inc(x_183);
lean_dec(x_181);
x_184 = lean_unbox(x_182);
lean_dec(x_182);
x_158 = x_184;
x_159 = x_183;
goto block_171;
}
block_171:
{
if (x_158 == 0)
{
uint8_t x_160; 
x_160 = l_Lean_Expr_hasFVar(x_157);
if (x_160 == 0)
{
uint8_t x_161; 
x_161 = l_Lean_Expr_hasMVar(x_157);
if (x_161 == 0)
{
uint8_t x_162; 
lean_dec(x_157);
x_162 = 0;
x_106 = x_162;
x_107 = x_159;
goto block_141;
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; uint8_t x_166; 
lean_inc(x_50);
lean_inc(x_3);
x_163 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__23(x_3, x_50, x_157, x_159);
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_163, 1);
lean_inc(x_165);
lean_dec(x_163);
x_166 = lean_unbox(x_164);
lean_dec(x_164);
x_106 = x_166;
x_107 = x_165;
goto block_141;
}
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; uint8_t x_170; 
lean_inc(x_50);
lean_inc(x_3);
x_167 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__31(x_3, x_50, x_157, x_159);
x_168 = lean_ctor_get(x_167, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_167, 1);
lean_inc(x_169);
lean_dec(x_167);
x_170 = lean_unbox(x_168);
lean_dec(x_168);
x_106 = x_170;
x_107 = x_169;
goto block_141;
}
}
else
{
lean_dec(x_157);
x_106 = x_158;
x_107 = x_159;
goto block_141;
}
}
}
block_104:
{
uint8_t x_61; 
x_61 = !lean_is_exclusive(x_57);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_57, 0);
lean_dec(x_62);
lean_ctor_set(x_57, 0, x_60);
x_63 = lean_st_ref_set(x_10, x_57, x_58);
if (x_59 == 0)
{
uint8_t x_64; 
lean_dec(x_52);
x_64 = !lean_is_exclusive(x_63);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_63, 0);
lean_dec(x_65);
if (lean_is_scalar(x_51)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_51;
}
lean_ctor_set(x_66, 0, x_49);
lean_ctor_set(x_66, 1, x_50);
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_63, 0, x_67);
x_27 = x_63;
goto block_43;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_68 = lean_ctor_get(x_63, 1);
lean_inc(x_68);
lean_dec(x_63);
if (lean_is_scalar(x_51)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_51;
}
lean_ctor_set(x_69, 0, x_49);
lean_ctor_set(x_69, 1, x_50);
x_70 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_70, 0, x_69);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_68);
x_27 = x_71;
goto block_43;
}
}
else
{
uint8_t x_72; 
x_72 = !lean_is_exclusive(x_63);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_73 = lean_ctor_get(x_63, 0);
lean_dec(x_73);
x_74 = lean_box(0);
lean_inc(x_52);
x_75 = l_Std_RBNode_insert___at_Lean_CollectFVars_State_add___spec__1(x_49, x_52, x_74);
x_76 = l_Std_RBNode_insert___at_Lean_CollectFVars_State_add___spec__1(x_50, x_52, x_74);
if (lean_is_scalar(x_51)) {
 x_77 = lean_alloc_ctor(0, 2, 0);
} else {
 x_77 = x_51;
}
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
x_78 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_63, 0, x_78);
x_27 = x_63;
goto block_43;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_79 = lean_ctor_get(x_63, 1);
lean_inc(x_79);
lean_dec(x_63);
x_80 = lean_box(0);
lean_inc(x_52);
x_81 = l_Std_RBNode_insert___at_Lean_CollectFVars_State_add___spec__1(x_49, x_52, x_80);
x_82 = l_Std_RBNode_insert___at_Lean_CollectFVars_State_add___spec__1(x_50, x_52, x_80);
if (lean_is_scalar(x_51)) {
 x_83 = lean_alloc_ctor(0, 2, 0);
} else {
 x_83 = x_51;
}
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
x_84 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_84, 0, x_83);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_79);
x_27 = x_85;
goto block_43;
}
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_86 = lean_ctor_get(x_57, 1);
x_87 = lean_ctor_get(x_57, 2);
x_88 = lean_ctor_get(x_57, 3);
lean_inc(x_88);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_57);
x_89 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_89, 0, x_60);
lean_ctor_set(x_89, 1, x_86);
lean_ctor_set(x_89, 2, x_87);
lean_ctor_set(x_89, 3, x_88);
x_90 = lean_st_ref_set(x_10, x_89, x_58);
if (x_59 == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_52);
x_91 = lean_ctor_get(x_90, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_92 = x_90;
} else {
 lean_dec_ref(x_90);
 x_92 = lean_box(0);
}
if (lean_is_scalar(x_51)) {
 x_93 = lean_alloc_ctor(0, 2, 0);
} else {
 x_93 = x_51;
}
lean_ctor_set(x_93, 0, x_49);
lean_ctor_set(x_93, 1, x_50);
x_94 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_94, 0, x_93);
if (lean_is_scalar(x_92)) {
 x_95 = lean_alloc_ctor(0, 2, 0);
} else {
 x_95 = x_92;
}
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_91);
x_27 = x_95;
goto block_43;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_96 = lean_ctor_get(x_90, 1);
lean_inc(x_96);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_97 = x_90;
} else {
 lean_dec_ref(x_90);
 x_97 = lean_box(0);
}
x_98 = lean_box(0);
lean_inc(x_52);
x_99 = l_Std_RBNode_insert___at_Lean_CollectFVars_State_add___spec__1(x_49, x_52, x_98);
x_100 = l_Std_RBNode_insert___at_Lean_CollectFVars_State_add___spec__1(x_50, x_52, x_98);
if (lean_is_scalar(x_51)) {
 x_101 = lean_alloc_ctor(0, 2, 0);
} else {
 x_101 = x_51;
}
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
x_102 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_102, 0, x_101);
if (lean_is_scalar(x_97)) {
 x_103 = lean_alloc_ctor(0, 2, 0);
} else {
 x_103 = x_97;
}
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_96);
x_27 = x_103;
goto block_43;
}
}
}
block_141:
{
lean_object* x_108; uint8_t x_109; 
x_108 = lean_ctor_get(x_107, 1);
lean_inc(x_108);
lean_dec(x_107);
x_109 = lean_ctor_get_uint8(x_108, sizeof(void*)*8);
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; uint8_t x_118; 
x_110 = lean_ctor_get(x_108, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_108, 1);
lean_inc(x_111);
x_112 = lean_ctor_get(x_108, 2);
lean_inc(x_112);
x_113 = lean_ctor_get(x_108, 3);
lean_inc(x_113);
x_114 = lean_ctor_get(x_108, 4);
lean_inc(x_114);
x_115 = lean_ctor_get(x_108, 5);
lean_inc(x_115);
x_116 = lean_ctor_get(x_108, 6);
lean_inc(x_116);
x_117 = lean_ctor_get(x_108, 7);
lean_inc(x_117);
lean_dec(x_108);
x_118 = !lean_is_exclusive(x_105);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_119 = lean_ctor_get(x_105, 7);
lean_dec(x_119);
x_120 = lean_ctor_get(x_105, 6);
lean_dec(x_120);
x_121 = lean_ctor_get(x_105, 5);
lean_dec(x_121);
x_122 = lean_ctor_get(x_105, 4);
lean_dec(x_122);
x_123 = lean_ctor_get(x_105, 3);
lean_dec(x_123);
x_124 = lean_ctor_get(x_105, 2);
lean_dec(x_124);
x_125 = lean_ctor_get(x_105, 1);
lean_dec(x_125);
x_126 = lean_ctor_get(x_105, 0);
lean_dec(x_126);
lean_ctor_set(x_105, 7, x_117);
lean_ctor_set(x_105, 6, x_116);
lean_ctor_set(x_105, 5, x_115);
lean_ctor_set(x_105, 4, x_114);
lean_ctor_set(x_105, 3, x_113);
lean_ctor_set(x_105, 2, x_112);
lean_ctor_set(x_105, 1, x_111);
lean_ctor_set(x_105, 0, x_110);
x_59 = x_106;
x_60 = x_105;
goto block_104;
}
else
{
uint8_t x_127; lean_object* x_128; 
x_127 = lean_ctor_get_uint8(x_105, sizeof(void*)*8);
lean_dec(x_105);
x_128 = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(x_128, 0, x_110);
lean_ctor_set(x_128, 1, x_111);
lean_ctor_set(x_128, 2, x_112);
lean_ctor_set(x_128, 3, x_113);
lean_ctor_set(x_128, 4, x_114);
lean_ctor_set(x_128, 5, x_115);
lean_ctor_set(x_128, 6, x_116);
lean_ctor_set(x_128, 7, x_117);
lean_ctor_set_uint8(x_128, sizeof(void*)*8, x_127);
x_59 = x_106;
x_60 = x_128;
goto block_104;
}
}
else
{
uint8_t x_129; 
lean_dec(x_105);
x_129 = !lean_is_exclusive(x_108);
if (x_129 == 0)
{
uint8_t x_130; 
x_130 = 1;
lean_ctor_set_uint8(x_108, sizeof(void*)*8, x_130);
x_59 = x_106;
x_60 = x_108;
goto block_104;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; uint8_t x_139; lean_object* x_140; 
x_131 = lean_ctor_get(x_108, 0);
x_132 = lean_ctor_get(x_108, 1);
x_133 = lean_ctor_get(x_108, 2);
x_134 = lean_ctor_get(x_108, 3);
x_135 = lean_ctor_get(x_108, 4);
x_136 = lean_ctor_get(x_108, 5);
x_137 = lean_ctor_get(x_108, 6);
x_138 = lean_ctor_get(x_108, 7);
lean_inc(x_138);
lean_inc(x_137);
lean_inc(x_136);
lean_inc(x_135);
lean_inc(x_134);
lean_inc(x_133);
lean_inc(x_132);
lean_inc(x_131);
lean_dec(x_108);
x_139 = 1;
x_140 = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(x_140, 0, x_131);
lean_ctor_set(x_140, 1, x_132);
lean_ctor_set(x_140, 2, x_133);
lean_ctor_set(x_140, 3, x_134);
lean_ctor_set(x_140, 4, x_135);
lean_ctor_set(x_140, 5, x_136);
lean_ctor_set(x_140, 6, x_137);
lean_ctor_set(x_140, 7, x_138);
lean_ctor_set_uint8(x_140, sizeof(void*)*8, x_139);
x_59 = x_106;
x_60 = x_140;
goto block_104;
}
}
}
}
}
block_24:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec(x_18);
x_21 = 1;
x_22 = lean_usize_add(x_7, x_21);
x_7 = x_22;
x_8 = x_20;
x_13 = x_19;
goto _start;
}
block_43:
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_29, 0);
lean_inc(x_4);
if (lean_is_scalar(x_26)) {
 x_32 = lean_alloc_ctor(0, 2, 0);
} else {
 x_32 = x_26;
}
lean_ctor_set(x_32, 0, x_4);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set(x_29, 0, x_32);
x_17 = x_27;
goto block_24;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_29, 0);
lean_inc(x_33);
lean_dec(x_29);
lean_inc(x_4);
if (lean_is_scalar(x_26)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_26;
}
lean_ctor_set(x_34, 0, x_4);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_27, 0, x_35);
x_17 = x_27;
goto block_24;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_36 = lean_ctor_get(x_27, 0);
x_37 = lean_ctor_get(x_27, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_27);
x_38 = lean_ctor_get(x_36, 0);
lean_inc(x_38);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 x_39 = x_36;
} else {
 lean_dec_ref(x_36);
 x_39 = lean_box(0);
}
lean_inc(x_4);
if (lean_is_scalar(x_26)) {
 x_40 = lean_alloc_ctor(0, 2, 0);
} else {
 x_40 = x_26;
}
lean_ctor_set(x_40, 0, x_4);
lean_ctor_set(x_40, 1, x_38);
if (lean_is_scalar(x_39)) {
 x_41 = lean_alloc_ctor(1, 1, 0);
} else {
 x_41 = x_39;
}
lean_ctor_set(x_41, 0, x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_37);
x_17 = x_42;
goto block_24;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentArray_forInAux___at_Lean_Meta_getFVarSetToGeneralize___spec__62___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
LEAN_EXPORT lean_object* l_Std_PersistentArray_forInAux___at_Lean_Meta_getFVarSetToGeneralize___spec__62(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_12 = lean_ctor_get(x_5, 0);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_6);
x_15 = lean_array_get_size(x_12);
x_16 = lean_usize_of_nat(x_15);
lean_dec(x_15);
x_17 = 0;
lean_inc(x_7);
x_18 = l_Array_forInUnsafe_loop___at_Lean_Meta_getFVarSetToGeneralize___spec__63(x_1, x_2, x_3, x_4, x_13, x_12, x_16, x_17, x_14, x_7, x_8, x_9, x_10, x_11);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_box(0);
x_24 = l_Std_PersistentArray_forInAux___at_Lean_Meta_getFVarSetToGeneralize___spec__62___lambda__1(x_22, x_23, x_7, x_8, x_9, x_10, x_21);
lean_dec(x_7);
return x_24;
}
else
{
uint8_t x_25; 
lean_dec(x_19);
lean_dec(x_7);
x_25 = !lean_is_exclusive(x_18);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_18, 0);
lean_dec(x_26);
x_27 = lean_ctor_get(x_20, 0);
lean_inc(x_27);
lean_dec(x_20);
lean_ctor_set(x_18, 0, x_27);
return x_18;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_18, 1);
lean_inc(x_28);
lean_dec(x_18);
x_29 = lean_ctor_get(x_20, 0);
lean_inc(x_29);
lean_dec(x_20);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; size_t x_35; size_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_31 = lean_ctor_get(x_5, 0);
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_6);
x_34 = lean_array_get_size(x_31);
x_35 = lean_usize_of_nat(x_34);
lean_dec(x_34);
x_36 = 0;
x_37 = l_Array_forInUnsafe_loop___at_Lean_Meta_getFVarSetToGeneralize___spec__64(x_1, x_2, x_3, x_32, x_31, x_35, x_36, x_33, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_1);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
lean_dec(x_37);
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
lean_dec(x_38);
x_42 = lean_box(0);
x_43 = l_Std_PersistentArray_forInAux___at_Lean_Meta_getFVarSetToGeneralize___spec__62___lambda__1(x_41, x_42, x_7, x_8, x_9, x_10, x_40);
lean_dec(x_7);
return x_43;
}
else
{
uint8_t x_44; 
lean_dec(x_38);
lean_dec(x_7);
x_44 = !lean_is_exclusive(x_37);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_37, 0);
lean_dec(x_45);
x_46 = lean_ctor_get(x_39, 0);
lean_inc(x_46);
lean_dec(x_39);
lean_ctor_set(x_37, 0, x_46);
return x_37;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_37, 1);
lean_inc(x_47);
lean_dec(x_37);
x_48 = lean_ctor_get(x_39, 0);
lean_inc(x_48);
lean_dec(x_39);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_47);
return x_49;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_getFVarSetToGeneralize___spec__65(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = lean_usize_dec_lt(x_7, x_6);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_4);
lean_dec(x_3);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_8);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_16 = lean_array_uget(x_5, x_7);
x_25 = lean_ctor_get(x_8, 1);
lean_inc(x_25);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_26 = x_8;
} else {
 lean_dec_ref(x_8);
 x_26 = lean_box(0);
}
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_44; size_t x_45; size_t x_46; 
lean_dec(x_26);
lean_inc(x_4);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_4);
lean_ctor_set(x_44, 1, x_25);
x_45 = 1;
x_46 = lean_usize_add(x_7, x_45);
x_7 = x_46;
x_8 = x_44;
goto _start;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_186; 
x_48 = lean_ctor_get(x_16, 0);
lean_inc(x_48);
lean_dec(x_16);
x_49 = lean_ctor_get(x_25, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_25, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_51 = x_25;
} else {
 lean_dec_ref(x_25);
 x_51 = lean_box(0);
}
x_52 = l_Lean_LocalDecl_fvarId(x_48);
x_186 = l_Std_RBNode_findCore___at_Lean_Meta_mkGeneralizationForbiddenSet_visit___spec__1(x_1, x_52);
if (lean_obj_tag(x_186) == 0)
{
uint8_t x_187; 
x_187 = l_Lean_LocalDecl_isAuxDecl(x_48);
if (x_187 == 0)
{
uint8_t x_188; uint8_t x_189; 
x_188 = l_Lean_LocalDecl_binderInfo(x_48);
x_189 = l_Lean_BinderInfo_isInstImplicit(x_188);
if (x_189 == 0)
{
if (x_2 == 0)
{
lean_object* x_190; 
x_190 = lean_box(0);
x_53 = x_190;
goto block_185;
}
else
{
uint8_t x_191; 
x_191 = l_Lean_LocalDecl_isLet(x_48);
if (x_191 == 0)
{
lean_object* x_192; 
x_192 = lean_box(0);
x_53 = x_192;
goto block_185;
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; 
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_48);
x_193 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_193, 0, x_49);
lean_ctor_set(x_193, 1, x_50);
x_194 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_194, 0, x_193);
x_195 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_195, 0, x_194);
lean_ctor_set(x_195, 1, x_13);
x_27 = x_195;
goto block_43;
}
}
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; 
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_48);
x_196 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_196, 0, x_49);
lean_ctor_set(x_196, 1, x_50);
x_197 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_197, 0, x_196);
x_198 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_198, 0, x_197);
lean_ctor_set(x_198, 1, x_13);
x_27 = x_198;
goto block_43;
}
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; 
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_48);
x_199 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_199, 0, x_49);
lean_ctor_set(x_199, 1, x_50);
x_200 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_200, 0, x_199);
x_201 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_201, 0, x_200);
lean_ctor_set(x_201, 1, x_13);
x_27 = x_201;
goto block_43;
}
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; 
lean_dec(x_186);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_48);
x_202 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_202, 0, x_49);
lean_ctor_set(x_202, 1, x_50);
x_203 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_203, 0, x_202);
x_204 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_204, 0, x_203);
lean_ctor_set(x_204, 1, x_13);
x_27 = x_204;
goto block_43;
}
block_185:
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; lean_object* x_60; lean_object* x_105; uint8_t x_106; lean_object* x_107; 
lean_dec(x_53);
x_54 = lean_st_ref_get(x_12, x_13);
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
lean_dec(x_54);
x_56 = lean_st_ref_take(x_10, x_55);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_105 = lean_ctor_get(x_57, 0);
lean_inc(x_105);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; uint8_t x_145; 
x_142 = lean_ctor_get(x_48, 3);
lean_inc(x_142);
lean_dec(x_48);
x_143 = l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1;
lean_inc(x_105);
x_144 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set(x_144, 1, x_105);
x_145 = l_Lean_Expr_hasFVar(x_142);
if (x_145 == 0)
{
uint8_t x_146; 
x_146 = l_Lean_Expr_hasMVar(x_142);
if (x_146 == 0)
{
uint8_t x_147; 
lean_dec(x_142);
x_147 = 0;
x_106 = x_147;
x_107 = x_144;
goto block_141;
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; uint8_t x_151; 
lean_inc(x_50);
x_148 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__1___at_Lean_Meta_getFVarSetToGeneralize___spec__9(x_50, x_142, x_144);
x_149 = lean_ctor_get(x_148, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_148, 1);
lean_inc(x_150);
lean_dec(x_148);
x_151 = lean_unbox(x_149);
lean_dec(x_149);
x_106 = x_151;
x_107 = x_150;
goto block_141;
}
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; uint8_t x_155; 
lean_inc(x_50);
x_152 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__12___at_Lean_Meta_getFVarSetToGeneralize___spec__20(x_50, x_142, x_144);
x_153 = lean_ctor_get(x_152, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_152, 1);
lean_inc(x_154);
lean_dec(x_152);
x_155 = lean_unbox(x_153);
lean_dec(x_153);
x_106 = x_155;
x_107 = x_154;
goto block_141;
}
}
else
{
lean_object* x_156; lean_object* x_157; uint8_t x_158; lean_object* x_159; lean_object* x_172; lean_object* x_173; uint8_t x_174; 
x_156 = lean_ctor_get(x_48, 3);
lean_inc(x_156);
x_157 = lean_ctor_get(x_48, 4);
lean_inc(x_157);
lean_dec(x_48);
x_172 = l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1;
lean_inc(x_105);
x_173 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_173, 0, x_172);
lean_ctor_set(x_173, 1, x_105);
x_174 = l_Lean_Expr_hasFVar(x_156);
if (x_174 == 0)
{
uint8_t x_175; 
x_175 = l_Lean_Expr_hasMVar(x_156);
if (x_175 == 0)
{
uint8_t x_176; 
lean_dec(x_156);
x_176 = 0;
x_158 = x_176;
x_159 = x_173;
goto block_171;
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; uint8_t x_180; 
lean_inc(x_50);
x_177 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__39___at_Lean_Meta_getFVarSetToGeneralize___spec__47(x_50, x_156, x_173);
x_178 = lean_ctor_get(x_177, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_177, 1);
lean_inc(x_179);
lean_dec(x_177);
x_180 = lean_unbox(x_178);
lean_dec(x_178);
x_158 = x_180;
x_159 = x_179;
goto block_171;
}
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; uint8_t x_184; 
lean_inc(x_50);
x_181 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__50___at_Lean_Meta_getFVarSetToGeneralize___spec__58(x_50, x_156, x_173);
x_182 = lean_ctor_get(x_181, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_181, 1);
lean_inc(x_183);
lean_dec(x_181);
x_184 = lean_unbox(x_182);
lean_dec(x_182);
x_158 = x_184;
x_159 = x_183;
goto block_171;
}
block_171:
{
if (x_158 == 0)
{
uint8_t x_160; 
x_160 = l_Lean_Expr_hasFVar(x_157);
if (x_160 == 0)
{
uint8_t x_161; 
x_161 = l_Lean_Expr_hasMVar(x_157);
if (x_161 == 0)
{
uint8_t x_162; 
lean_dec(x_157);
x_162 = 0;
x_106 = x_162;
x_107 = x_159;
goto block_141;
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; uint8_t x_166; 
lean_inc(x_50);
lean_inc(x_3);
x_163 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__23(x_3, x_50, x_157, x_159);
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_163, 1);
lean_inc(x_165);
lean_dec(x_163);
x_166 = lean_unbox(x_164);
lean_dec(x_164);
x_106 = x_166;
x_107 = x_165;
goto block_141;
}
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; uint8_t x_170; 
lean_inc(x_50);
lean_inc(x_3);
x_167 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__31(x_3, x_50, x_157, x_159);
x_168 = lean_ctor_get(x_167, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_167, 1);
lean_inc(x_169);
lean_dec(x_167);
x_170 = lean_unbox(x_168);
lean_dec(x_168);
x_106 = x_170;
x_107 = x_169;
goto block_141;
}
}
else
{
lean_dec(x_157);
x_106 = x_158;
x_107 = x_159;
goto block_141;
}
}
}
block_104:
{
uint8_t x_61; 
x_61 = !lean_is_exclusive(x_57);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_57, 0);
lean_dec(x_62);
lean_ctor_set(x_57, 0, x_60);
x_63 = lean_st_ref_set(x_10, x_57, x_58);
if (x_59 == 0)
{
uint8_t x_64; 
lean_dec(x_52);
x_64 = !lean_is_exclusive(x_63);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_63, 0);
lean_dec(x_65);
if (lean_is_scalar(x_51)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_51;
}
lean_ctor_set(x_66, 0, x_49);
lean_ctor_set(x_66, 1, x_50);
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_63, 0, x_67);
x_27 = x_63;
goto block_43;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_68 = lean_ctor_get(x_63, 1);
lean_inc(x_68);
lean_dec(x_63);
if (lean_is_scalar(x_51)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_51;
}
lean_ctor_set(x_69, 0, x_49);
lean_ctor_set(x_69, 1, x_50);
x_70 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_70, 0, x_69);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_68);
x_27 = x_71;
goto block_43;
}
}
else
{
uint8_t x_72; 
x_72 = !lean_is_exclusive(x_63);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_73 = lean_ctor_get(x_63, 0);
lean_dec(x_73);
x_74 = lean_box(0);
lean_inc(x_52);
x_75 = l_Std_RBNode_insert___at_Lean_CollectFVars_State_add___spec__1(x_49, x_52, x_74);
x_76 = l_Std_RBNode_insert___at_Lean_CollectFVars_State_add___spec__1(x_50, x_52, x_74);
if (lean_is_scalar(x_51)) {
 x_77 = lean_alloc_ctor(0, 2, 0);
} else {
 x_77 = x_51;
}
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
x_78 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_63, 0, x_78);
x_27 = x_63;
goto block_43;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_79 = lean_ctor_get(x_63, 1);
lean_inc(x_79);
lean_dec(x_63);
x_80 = lean_box(0);
lean_inc(x_52);
x_81 = l_Std_RBNode_insert___at_Lean_CollectFVars_State_add___spec__1(x_49, x_52, x_80);
x_82 = l_Std_RBNode_insert___at_Lean_CollectFVars_State_add___spec__1(x_50, x_52, x_80);
if (lean_is_scalar(x_51)) {
 x_83 = lean_alloc_ctor(0, 2, 0);
} else {
 x_83 = x_51;
}
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
x_84 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_84, 0, x_83);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_79);
x_27 = x_85;
goto block_43;
}
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_86 = lean_ctor_get(x_57, 1);
x_87 = lean_ctor_get(x_57, 2);
x_88 = lean_ctor_get(x_57, 3);
lean_inc(x_88);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_57);
x_89 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_89, 0, x_60);
lean_ctor_set(x_89, 1, x_86);
lean_ctor_set(x_89, 2, x_87);
lean_ctor_set(x_89, 3, x_88);
x_90 = lean_st_ref_set(x_10, x_89, x_58);
if (x_59 == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_52);
x_91 = lean_ctor_get(x_90, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_92 = x_90;
} else {
 lean_dec_ref(x_90);
 x_92 = lean_box(0);
}
if (lean_is_scalar(x_51)) {
 x_93 = lean_alloc_ctor(0, 2, 0);
} else {
 x_93 = x_51;
}
lean_ctor_set(x_93, 0, x_49);
lean_ctor_set(x_93, 1, x_50);
x_94 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_94, 0, x_93);
if (lean_is_scalar(x_92)) {
 x_95 = lean_alloc_ctor(0, 2, 0);
} else {
 x_95 = x_92;
}
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_91);
x_27 = x_95;
goto block_43;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_96 = lean_ctor_get(x_90, 1);
lean_inc(x_96);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_97 = x_90;
} else {
 lean_dec_ref(x_90);
 x_97 = lean_box(0);
}
x_98 = lean_box(0);
lean_inc(x_52);
x_99 = l_Std_RBNode_insert___at_Lean_CollectFVars_State_add___spec__1(x_49, x_52, x_98);
x_100 = l_Std_RBNode_insert___at_Lean_CollectFVars_State_add___spec__1(x_50, x_52, x_98);
if (lean_is_scalar(x_51)) {
 x_101 = lean_alloc_ctor(0, 2, 0);
} else {
 x_101 = x_51;
}
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
x_102 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_102, 0, x_101);
if (lean_is_scalar(x_97)) {
 x_103 = lean_alloc_ctor(0, 2, 0);
} else {
 x_103 = x_97;
}
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_96);
x_27 = x_103;
goto block_43;
}
}
}
block_141:
{
lean_object* x_108; uint8_t x_109; 
x_108 = lean_ctor_get(x_107, 1);
lean_inc(x_108);
lean_dec(x_107);
x_109 = lean_ctor_get_uint8(x_108, sizeof(void*)*8);
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; uint8_t x_118; 
x_110 = lean_ctor_get(x_108, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_108, 1);
lean_inc(x_111);
x_112 = lean_ctor_get(x_108, 2);
lean_inc(x_112);
x_113 = lean_ctor_get(x_108, 3);
lean_inc(x_113);
x_114 = lean_ctor_get(x_108, 4);
lean_inc(x_114);
x_115 = lean_ctor_get(x_108, 5);
lean_inc(x_115);
x_116 = lean_ctor_get(x_108, 6);
lean_inc(x_116);
x_117 = lean_ctor_get(x_108, 7);
lean_inc(x_117);
lean_dec(x_108);
x_118 = !lean_is_exclusive(x_105);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_119 = lean_ctor_get(x_105, 7);
lean_dec(x_119);
x_120 = lean_ctor_get(x_105, 6);
lean_dec(x_120);
x_121 = lean_ctor_get(x_105, 5);
lean_dec(x_121);
x_122 = lean_ctor_get(x_105, 4);
lean_dec(x_122);
x_123 = lean_ctor_get(x_105, 3);
lean_dec(x_123);
x_124 = lean_ctor_get(x_105, 2);
lean_dec(x_124);
x_125 = lean_ctor_get(x_105, 1);
lean_dec(x_125);
x_126 = lean_ctor_get(x_105, 0);
lean_dec(x_126);
lean_ctor_set(x_105, 7, x_117);
lean_ctor_set(x_105, 6, x_116);
lean_ctor_set(x_105, 5, x_115);
lean_ctor_set(x_105, 4, x_114);
lean_ctor_set(x_105, 3, x_113);
lean_ctor_set(x_105, 2, x_112);
lean_ctor_set(x_105, 1, x_111);
lean_ctor_set(x_105, 0, x_110);
x_59 = x_106;
x_60 = x_105;
goto block_104;
}
else
{
uint8_t x_127; lean_object* x_128; 
x_127 = lean_ctor_get_uint8(x_105, sizeof(void*)*8);
lean_dec(x_105);
x_128 = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(x_128, 0, x_110);
lean_ctor_set(x_128, 1, x_111);
lean_ctor_set(x_128, 2, x_112);
lean_ctor_set(x_128, 3, x_113);
lean_ctor_set(x_128, 4, x_114);
lean_ctor_set(x_128, 5, x_115);
lean_ctor_set(x_128, 6, x_116);
lean_ctor_set(x_128, 7, x_117);
lean_ctor_set_uint8(x_128, sizeof(void*)*8, x_127);
x_59 = x_106;
x_60 = x_128;
goto block_104;
}
}
else
{
uint8_t x_129; 
lean_dec(x_105);
x_129 = !lean_is_exclusive(x_108);
if (x_129 == 0)
{
uint8_t x_130; 
x_130 = 1;
lean_ctor_set_uint8(x_108, sizeof(void*)*8, x_130);
x_59 = x_106;
x_60 = x_108;
goto block_104;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; uint8_t x_139; lean_object* x_140; 
x_131 = lean_ctor_get(x_108, 0);
x_132 = lean_ctor_get(x_108, 1);
x_133 = lean_ctor_get(x_108, 2);
x_134 = lean_ctor_get(x_108, 3);
x_135 = lean_ctor_get(x_108, 4);
x_136 = lean_ctor_get(x_108, 5);
x_137 = lean_ctor_get(x_108, 6);
x_138 = lean_ctor_get(x_108, 7);
lean_inc(x_138);
lean_inc(x_137);
lean_inc(x_136);
lean_inc(x_135);
lean_inc(x_134);
lean_inc(x_133);
lean_inc(x_132);
lean_inc(x_131);
lean_dec(x_108);
x_139 = 1;
x_140 = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(x_140, 0, x_131);
lean_ctor_set(x_140, 1, x_132);
lean_ctor_set(x_140, 2, x_133);
lean_ctor_set(x_140, 3, x_134);
lean_ctor_set(x_140, 4, x_135);
lean_ctor_set(x_140, 5, x_136);
lean_ctor_set(x_140, 6, x_137);
lean_ctor_set(x_140, 7, x_138);
lean_ctor_set_uint8(x_140, sizeof(void*)*8, x_139);
x_59 = x_106;
x_60 = x_140;
goto block_104;
}
}
}
}
}
block_24:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec(x_18);
x_21 = 1;
x_22 = lean_usize_add(x_7, x_21);
x_7 = x_22;
x_8 = x_20;
x_13 = x_19;
goto _start;
}
block_43:
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_29, 0);
lean_inc(x_4);
if (lean_is_scalar(x_26)) {
 x_32 = lean_alloc_ctor(0, 2, 0);
} else {
 x_32 = x_26;
}
lean_ctor_set(x_32, 0, x_4);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set(x_29, 0, x_32);
x_17 = x_27;
goto block_24;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_29, 0);
lean_inc(x_33);
lean_dec(x_29);
lean_inc(x_4);
if (lean_is_scalar(x_26)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_26;
}
lean_ctor_set(x_34, 0, x_4);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_27, 0, x_35);
x_17 = x_27;
goto block_24;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_36 = lean_ctor_get(x_27, 0);
x_37 = lean_ctor_get(x_27, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_27);
x_38 = lean_ctor_get(x_36, 0);
lean_inc(x_38);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 x_39 = x_36;
} else {
 lean_dec_ref(x_36);
 x_39 = lean_box(0);
}
lean_inc(x_4);
if (lean_is_scalar(x_26)) {
 x_40 = lean_alloc_ctor(0, 2, 0);
} else {
 x_40 = x_26;
}
lean_ctor_set(x_40, 0, x_4);
lean_ctor_set(x_40, 1, x_38);
if (lean_is_scalar(x_39)) {
 x_41 = lean_alloc_ctor(1, 1, 0);
} else {
 x_41 = x_39;
}
lean_ctor_set(x_41, 0, x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_37);
x_17 = x_42;
goto block_24;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentArray_forIn___at_Lean_Meta_getFVarSetToGeneralize___spec__61___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentArray_forIn___at_Lean_Meta_getFVarSetToGeneralize___spec__61(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_1);
x_12 = l_Std_PersistentArray_forInAux___at_Lean_Meta_getFVarSetToGeneralize___spec__62(x_1, x_2, x_3, x_5, x_11, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_12, 0);
lean_dec(x_15);
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_16);
lean_dec(x_13);
lean_ctor_set(x_12, 0, x_16);
return x_12;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_dec(x_12);
x_18 = lean_ctor_get(x_13, 0);
lean_inc(x_18);
lean_dec(x_13);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; size_t x_26; size_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_20 = lean_ctor_get(x_12, 1);
lean_inc(x_20);
lean_dec(x_12);
x_21 = lean_ctor_get(x_13, 0);
lean_inc(x_21);
lean_dec(x_13);
x_22 = lean_ctor_get(x_4, 1);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_21);
x_25 = lean_array_get_size(x_22);
x_26 = lean_usize_of_nat(x_25);
lean_dec(x_25);
x_27 = 0;
x_28 = l_Array_forInUnsafe_loop___at_Lean_Meta_getFVarSetToGeneralize___spec__65(x_1, x_2, x_3, x_23, x_22, x_26, x_27, x_24, x_6, x_7, x_8, x_9, x_20);
lean_dec(x_6);
lean_dec(x_1);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_28);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_28, 0);
lean_dec(x_32);
x_33 = lean_ctor_get(x_29, 1);
lean_inc(x_33);
lean_dec(x_29);
lean_ctor_set(x_28, 0, x_33);
return x_28;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_28, 1);
lean_inc(x_34);
lean_dec(x_28);
x_35 = lean_ctor_get(x_29, 1);
lean_inc(x_35);
lean_dec(x_29);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
return x_36;
}
}
else
{
uint8_t x_37; 
lean_dec(x_29);
x_37 = !lean_is_exclusive(x_28);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_28, 0);
lean_dec(x_38);
x_39 = lean_ctor_get(x_30, 0);
lean_inc(x_39);
lean_dec(x_30);
lean_ctor_set(x_28, 0, x_39);
return x_28;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_28, 1);
lean_inc(x_40);
lean_dec(x_28);
x_41 = lean_ctor_get(x_30, 0);
lean_inc(x_41);
lean_dec(x_30);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
return x_42;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_getFVarSetToGeneralize___spec__68(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, size_t x_7, size_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; 
x_15 = lean_usize_dec_lt(x_8, x_7);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_9);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
else
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_array_uget(x_6, x_8);
x_18 = !lean_is_exclusive(x_9);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_9, 1);
x_20 = lean_ctor_get(x_9, 0);
lean_dec(x_20);
lean_inc(x_10);
lean_inc(x_19);
lean_inc(x_3);
lean_inc(x_1);
x_21 = l_Std_PersistentArray_forInAux___at_Lean_Meta_getFVarSetToGeneralize___spec__67(x_1, x_2, x_3, x_4, x_17, x_19, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_17);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_21);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_21, 0);
lean_dec(x_24);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_9, 0, x_25);
lean_ctor_set(x_21, 0, x_9);
return x_21;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_21, 1);
lean_inc(x_26);
lean_dec(x_21);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_22);
lean_ctor_set(x_9, 0, x_27);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_9);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; size_t x_31; size_t x_32; 
lean_dec(x_19);
x_29 = lean_ctor_get(x_21, 1);
lean_inc(x_29);
lean_dec(x_21);
x_30 = lean_ctor_get(x_22, 0);
lean_inc(x_30);
lean_dec(x_22);
lean_inc(x_5);
lean_ctor_set(x_9, 1, x_30);
lean_ctor_set(x_9, 0, x_5);
x_31 = 1;
x_32 = lean_usize_add(x_8, x_31);
x_8 = x_32;
x_14 = x_29;
goto _start;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_9, 1);
lean_inc(x_34);
lean_dec(x_9);
lean_inc(x_10);
lean_inc(x_34);
lean_inc(x_3);
lean_inc(x_1);
x_35 = l_Std_PersistentArray_forInAux___at_Lean_Meta_getFVarSetToGeneralize___spec__67(x_1, x_2, x_3, x_4, x_17, x_34, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_17);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_38 = x_35;
} else {
 lean_dec_ref(x_35);
 x_38 = lean_box(0);
}
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_36);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_34);
if (lean_is_scalar(x_38)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_38;
}
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_37);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; size_t x_45; size_t x_46; 
lean_dec(x_34);
x_42 = lean_ctor_get(x_35, 1);
lean_inc(x_42);
lean_dec(x_35);
x_43 = lean_ctor_get(x_36, 0);
lean_inc(x_43);
lean_dec(x_36);
lean_inc(x_5);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_5);
lean_ctor_set(x_44, 1, x_43);
x_45 = 1;
x_46 = lean_usize_add(x_8, x_45);
x_8 = x_46;
x_9 = x_44;
x_14 = x_42;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_getFVarSetToGeneralize___spec__69(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = lean_usize_dec_lt(x_7, x_6);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_4);
lean_dec(x_3);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_8);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_16 = lean_array_uget(x_5, x_7);
x_25 = lean_ctor_get(x_8, 1);
lean_inc(x_25);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_26 = x_8;
} else {
 lean_dec_ref(x_8);
 x_26 = lean_box(0);
}
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_44; size_t x_45; size_t x_46; 
lean_dec(x_26);
lean_inc(x_4);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_4);
lean_ctor_set(x_44, 1, x_25);
x_45 = 1;
x_46 = lean_usize_add(x_7, x_45);
x_7 = x_46;
x_8 = x_44;
goto _start;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_186; 
x_48 = lean_ctor_get(x_16, 0);
lean_inc(x_48);
lean_dec(x_16);
x_49 = lean_ctor_get(x_25, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_25, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_51 = x_25;
} else {
 lean_dec_ref(x_25);
 x_51 = lean_box(0);
}
x_52 = l_Lean_LocalDecl_fvarId(x_48);
x_186 = l_Std_RBNode_findCore___at_Lean_Meta_mkGeneralizationForbiddenSet_visit___spec__1(x_1, x_52);
if (lean_obj_tag(x_186) == 0)
{
uint8_t x_187; 
x_187 = l_Lean_LocalDecl_isAuxDecl(x_48);
if (x_187 == 0)
{
uint8_t x_188; uint8_t x_189; 
x_188 = l_Lean_LocalDecl_binderInfo(x_48);
x_189 = l_Lean_BinderInfo_isInstImplicit(x_188);
if (x_189 == 0)
{
if (x_2 == 0)
{
lean_object* x_190; 
x_190 = lean_box(0);
x_53 = x_190;
goto block_185;
}
else
{
uint8_t x_191; 
x_191 = l_Lean_LocalDecl_isLet(x_48);
if (x_191 == 0)
{
lean_object* x_192; 
x_192 = lean_box(0);
x_53 = x_192;
goto block_185;
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; 
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_48);
x_193 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_193, 0, x_49);
lean_ctor_set(x_193, 1, x_50);
x_194 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_194, 0, x_193);
x_195 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_195, 0, x_194);
lean_ctor_set(x_195, 1, x_13);
x_27 = x_195;
goto block_43;
}
}
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; 
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_48);
x_196 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_196, 0, x_49);
lean_ctor_set(x_196, 1, x_50);
x_197 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_197, 0, x_196);
x_198 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_198, 0, x_197);
lean_ctor_set(x_198, 1, x_13);
x_27 = x_198;
goto block_43;
}
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; 
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_48);
x_199 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_199, 0, x_49);
lean_ctor_set(x_199, 1, x_50);
x_200 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_200, 0, x_199);
x_201 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_201, 0, x_200);
lean_ctor_set(x_201, 1, x_13);
x_27 = x_201;
goto block_43;
}
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; 
lean_dec(x_186);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_48);
x_202 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_202, 0, x_49);
lean_ctor_set(x_202, 1, x_50);
x_203 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_203, 0, x_202);
x_204 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_204, 0, x_203);
lean_ctor_set(x_204, 1, x_13);
x_27 = x_204;
goto block_43;
}
block_185:
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; lean_object* x_60; lean_object* x_105; uint8_t x_106; lean_object* x_107; 
lean_dec(x_53);
x_54 = lean_st_ref_get(x_12, x_13);
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
lean_dec(x_54);
x_56 = lean_st_ref_take(x_10, x_55);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_105 = lean_ctor_get(x_57, 0);
lean_inc(x_105);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; uint8_t x_145; 
x_142 = lean_ctor_get(x_48, 3);
lean_inc(x_142);
lean_dec(x_48);
x_143 = l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1;
lean_inc(x_105);
x_144 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set(x_144, 1, x_105);
x_145 = l_Lean_Expr_hasFVar(x_142);
if (x_145 == 0)
{
uint8_t x_146; 
x_146 = l_Lean_Expr_hasMVar(x_142);
if (x_146 == 0)
{
uint8_t x_147; 
lean_dec(x_142);
x_147 = 0;
x_106 = x_147;
x_107 = x_144;
goto block_141;
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; uint8_t x_151; 
lean_inc(x_50);
x_148 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__1___at_Lean_Meta_getFVarSetToGeneralize___spec__9(x_50, x_142, x_144);
x_149 = lean_ctor_get(x_148, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_148, 1);
lean_inc(x_150);
lean_dec(x_148);
x_151 = lean_unbox(x_149);
lean_dec(x_149);
x_106 = x_151;
x_107 = x_150;
goto block_141;
}
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; uint8_t x_155; 
lean_inc(x_50);
x_152 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__12___at_Lean_Meta_getFVarSetToGeneralize___spec__20(x_50, x_142, x_144);
x_153 = lean_ctor_get(x_152, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_152, 1);
lean_inc(x_154);
lean_dec(x_152);
x_155 = lean_unbox(x_153);
lean_dec(x_153);
x_106 = x_155;
x_107 = x_154;
goto block_141;
}
}
else
{
lean_object* x_156; lean_object* x_157; uint8_t x_158; lean_object* x_159; lean_object* x_172; lean_object* x_173; uint8_t x_174; 
x_156 = lean_ctor_get(x_48, 3);
lean_inc(x_156);
x_157 = lean_ctor_get(x_48, 4);
lean_inc(x_157);
lean_dec(x_48);
x_172 = l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1;
lean_inc(x_105);
x_173 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_173, 0, x_172);
lean_ctor_set(x_173, 1, x_105);
x_174 = l_Lean_Expr_hasFVar(x_156);
if (x_174 == 0)
{
uint8_t x_175; 
x_175 = l_Lean_Expr_hasMVar(x_156);
if (x_175 == 0)
{
uint8_t x_176; 
lean_dec(x_156);
x_176 = 0;
x_158 = x_176;
x_159 = x_173;
goto block_171;
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; uint8_t x_180; 
lean_inc(x_50);
x_177 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__39___at_Lean_Meta_getFVarSetToGeneralize___spec__47(x_50, x_156, x_173);
x_178 = lean_ctor_get(x_177, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_177, 1);
lean_inc(x_179);
lean_dec(x_177);
x_180 = lean_unbox(x_178);
lean_dec(x_178);
x_158 = x_180;
x_159 = x_179;
goto block_171;
}
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; uint8_t x_184; 
lean_inc(x_50);
x_181 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__50___at_Lean_Meta_getFVarSetToGeneralize___spec__58(x_50, x_156, x_173);
x_182 = lean_ctor_get(x_181, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_181, 1);
lean_inc(x_183);
lean_dec(x_181);
x_184 = lean_unbox(x_182);
lean_dec(x_182);
x_158 = x_184;
x_159 = x_183;
goto block_171;
}
block_171:
{
if (x_158 == 0)
{
uint8_t x_160; 
x_160 = l_Lean_Expr_hasFVar(x_157);
if (x_160 == 0)
{
uint8_t x_161; 
x_161 = l_Lean_Expr_hasMVar(x_157);
if (x_161 == 0)
{
uint8_t x_162; 
lean_dec(x_157);
x_162 = 0;
x_106 = x_162;
x_107 = x_159;
goto block_141;
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; uint8_t x_166; 
lean_inc(x_50);
lean_inc(x_3);
x_163 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__23(x_3, x_50, x_157, x_159);
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_163, 1);
lean_inc(x_165);
lean_dec(x_163);
x_166 = lean_unbox(x_164);
lean_dec(x_164);
x_106 = x_166;
x_107 = x_165;
goto block_141;
}
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; uint8_t x_170; 
lean_inc(x_50);
lean_inc(x_3);
x_167 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__31(x_3, x_50, x_157, x_159);
x_168 = lean_ctor_get(x_167, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_167, 1);
lean_inc(x_169);
lean_dec(x_167);
x_170 = lean_unbox(x_168);
lean_dec(x_168);
x_106 = x_170;
x_107 = x_169;
goto block_141;
}
}
else
{
lean_dec(x_157);
x_106 = x_158;
x_107 = x_159;
goto block_141;
}
}
}
block_104:
{
uint8_t x_61; 
x_61 = !lean_is_exclusive(x_57);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_57, 0);
lean_dec(x_62);
lean_ctor_set(x_57, 0, x_60);
x_63 = lean_st_ref_set(x_10, x_57, x_58);
if (x_59 == 0)
{
uint8_t x_64; 
lean_dec(x_52);
x_64 = !lean_is_exclusive(x_63);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_63, 0);
lean_dec(x_65);
if (lean_is_scalar(x_51)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_51;
}
lean_ctor_set(x_66, 0, x_49);
lean_ctor_set(x_66, 1, x_50);
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_63, 0, x_67);
x_27 = x_63;
goto block_43;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_68 = lean_ctor_get(x_63, 1);
lean_inc(x_68);
lean_dec(x_63);
if (lean_is_scalar(x_51)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_51;
}
lean_ctor_set(x_69, 0, x_49);
lean_ctor_set(x_69, 1, x_50);
x_70 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_70, 0, x_69);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_68);
x_27 = x_71;
goto block_43;
}
}
else
{
uint8_t x_72; 
x_72 = !lean_is_exclusive(x_63);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_73 = lean_ctor_get(x_63, 0);
lean_dec(x_73);
x_74 = lean_box(0);
lean_inc(x_52);
x_75 = l_Std_RBNode_insert___at_Lean_CollectFVars_State_add___spec__1(x_49, x_52, x_74);
x_76 = l_Std_RBNode_insert___at_Lean_CollectFVars_State_add___spec__1(x_50, x_52, x_74);
if (lean_is_scalar(x_51)) {
 x_77 = lean_alloc_ctor(0, 2, 0);
} else {
 x_77 = x_51;
}
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
x_78 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_63, 0, x_78);
x_27 = x_63;
goto block_43;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_79 = lean_ctor_get(x_63, 1);
lean_inc(x_79);
lean_dec(x_63);
x_80 = lean_box(0);
lean_inc(x_52);
x_81 = l_Std_RBNode_insert___at_Lean_CollectFVars_State_add___spec__1(x_49, x_52, x_80);
x_82 = l_Std_RBNode_insert___at_Lean_CollectFVars_State_add___spec__1(x_50, x_52, x_80);
if (lean_is_scalar(x_51)) {
 x_83 = lean_alloc_ctor(0, 2, 0);
} else {
 x_83 = x_51;
}
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
x_84 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_84, 0, x_83);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_79);
x_27 = x_85;
goto block_43;
}
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_86 = lean_ctor_get(x_57, 1);
x_87 = lean_ctor_get(x_57, 2);
x_88 = lean_ctor_get(x_57, 3);
lean_inc(x_88);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_57);
x_89 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_89, 0, x_60);
lean_ctor_set(x_89, 1, x_86);
lean_ctor_set(x_89, 2, x_87);
lean_ctor_set(x_89, 3, x_88);
x_90 = lean_st_ref_set(x_10, x_89, x_58);
if (x_59 == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_52);
x_91 = lean_ctor_get(x_90, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_92 = x_90;
} else {
 lean_dec_ref(x_90);
 x_92 = lean_box(0);
}
if (lean_is_scalar(x_51)) {
 x_93 = lean_alloc_ctor(0, 2, 0);
} else {
 x_93 = x_51;
}
lean_ctor_set(x_93, 0, x_49);
lean_ctor_set(x_93, 1, x_50);
x_94 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_94, 0, x_93);
if (lean_is_scalar(x_92)) {
 x_95 = lean_alloc_ctor(0, 2, 0);
} else {
 x_95 = x_92;
}
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_91);
x_27 = x_95;
goto block_43;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_96 = lean_ctor_get(x_90, 1);
lean_inc(x_96);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_97 = x_90;
} else {
 lean_dec_ref(x_90);
 x_97 = lean_box(0);
}
x_98 = lean_box(0);
lean_inc(x_52);
x_99 = l_Std_RBNode_insert___at_Lean_CollectFVars_State_add___spec__1(x_49, x_52, x_98);
x_100 = l_Std_RBNode_insert___at_Lean_CollectFVars_State_add___spec__1(x_50, x_52, x_98);
if (lean_is_scalar(x_51)) {
 x_101 = lean_alloc_ctor(0, 2, 0);
} else {
 x_101 = x_51;
}
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
x_102 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_102, 0, x_101);
if (lean_is_scalar(x_97)) {
 x_103 = lean_alloc_ctor(0, 2, 0);
} else {
 x_103 = x_97;
}
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_96);
x_27 = x_103;
goto block_43;
}
}
}
block_141:
{
lean_object* x_108; uint8_t x_109; 
x_108 = lean_ctor_get(x_107, 1);
lean_inc(x_108);
lean_dec(x_107);
x_109 = lean_ctor_get_uint8(x_108, sizeof(void*)*8);
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; uint8_t x_118; 
x_110 = lean_ctor_get(x_108, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_108, 1);
lean_inc(x_111);
x_112 = lean_ctor_get(x_108, 2);
lean_inc(x_112);
x_113 = lean_ctor_get(x_108, 3);
lean_inc(x_113);
x_114 = lean_ctor_get(x_108, 4);
lean_inc(x_114);
x_115 = lean_ctor_get(x_108, 5);
lean_inc(x_115);
x_116 = lean_ctor_get(x_108, 6);
lean_inc(x_116);
x_117 = lean_ctor_get(x_108, 7);
lean_inc(x_117);
lean_dec(x_108);
x_118 = !lean_is_exclusive(x_105);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_119 = lean_ctor_get(x_105, 7);
lean_dec(x_119);
x_120 = lean_ctor_get(x_105, 6);
lean_dec(x_120);
x_121 = lean_ctor_get(x_105, 5);
lean_dec(x_121);
x_122 = lean_ctor_get(x_105, 4);
lean_dec(x_122);
x_123 = lean_ctor_get(x_105, 3);
lean_dec(x_123);
x_124 = lean_ctor_get(x_105, 2);
lean_dec(x_124);
x_125 = lean_ctor_get(x_105, 1);
lean_dec(x_125);
x_126 = lean_ctor_get(x_105, 0);
lean_dec(x_126);
lean_ctor_set(x_105, 7, x_117);
lean_ctor_set(x_105, 6, x_116);
lean_ctor_set(x_105, 5, x_115);
lean_ctor_set(x_105, 4, x_114);
lean_ctor_set(x_105, 3, x_113);
lean_ctor_set(x_105, 2, x_112);
lean_ctor_set(x_105, 1, x_111);
lean_ctor_set(x_105, 0, x_110);
x_59 = x_106;
x_60 = x_105;
goto block_104;
}
else
{
uint8_t x_127; lean_object* x_128; 
x_127 = lean_ctor_get_uint8(x_105, sizeof(void*)*8);
lean_dec(x_105);
x_128 = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(x_128, 0, x_110);
lean_ctor_set(x_128, 1, x_111);
lean_ctor_set(x_128, 2, x_112);
lean_ctor_set(x_128, 3, x_113);
lean_ctor_set(x_128, 4, x_114);
lean_ctor_set(x_128, 5, x_115);
lean_ctor_set(x_128, 6, x_116);
lean_ctor_set(x_128, 7, x_117);
lean_ctor_set_uint8(x_128, sizeof(void*)*8, x_127);
x_59 = x_106;
x_60 = x_128;
goto block_104;
}
}
else
{
uint8_t x_129; 
lean_dec(x_105);
x_129 = !lean_is_exclusive(x_108);
if (x_129 == 0)
{
uint8_t x_130; 
x_130 = 1;
lean_ctor_set_uint8(x_108, sizeof(void*)*8, x_130);
x_59 = x_106;
x_60 = x_108;
goto block_104;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; uint8_t x_139; lean_object* x_140; 
x_131 = lean_ctor_get(x_108, 0);
x_132 = lean_ctor_get(x_108, 1);
x_133 = lean_ctor_get(x_108, 2);
x_134 = lean_ctor_get(x_108, 3);
x_135 = lean_ctor_get(x_108, 4);
x_136 = lean_ctor_get(x_108, 5);
x_137 = lean_ctor_get(x_108, 6);
x_138 = lean_ctor_get(x_108, 7);
lean_inc(x_138);
lean_inc(x_137);
lean_inc(x_136);
lean_inc(x_135);
lean_inc(x_134);
lean_inc(x_133);
lean_inc(x_132);
lean_inc(x_131);
lean_dec(x_108);
x_139 = 1;
x_140 = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(x_140, 0, x_131);
lean_ctor_set(x_140, 1, x_132);
lean_ctor_set(x_140, 2, x_133);
lean_ctor_set(x_140, 3, x_134);
lean_ctor_set(x_140, 4, x_135);
lean_ctor_set(x_140, 5, x_136);
lean_ctor_set(x_140, 6, x_137);
lean_ctor_set(x_140, 7, x_138);
lean_ctor_set_uint8(x_140, sizeof(void*)*8, x_139);
x_59 = x_106;
x_60 = x_140;
goto block_104;
}
}
}
}
}
block_24:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec(x_18);
x_21 = 1;
x_22 = lean_usize_add(x_7, x_21);
x_7 = x_22;
x_8 = x_20;
x_13 = x_19;
goto _start;
}
block_43:
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_29, 0);
lean_inc(x_4);
if (lean_is_scalar(x_26)) {
 x_32 = lean_alloc_ctor(0, 2, 0);
} else {
 x_32 = x_26;
}
lean_ctor_set(x_32, 0, x_4);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set(x_29, 0, x_32);
x_17 = x_27;
goto block_24;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_29, 0);
lean_inc(x_33);
lean_dec(x_29);
lean_inc(x_4);
if (lean_is_scalar(x_26)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_26;
}
lean_ctor_set(x_34, 0, x_4);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_27, 0, x_35);
x_17 = x_27;
goto block_24;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_36 = lean_ctor_get(x_27, 0);
x_37 = lean_ctor_get(x_27, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_27);
x_38 = lean_ctor_get(x_36, 0);
lean_inc(x_38);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 x_39 = x_36;
} else {
 lean_dec_ref(x_36);
 x_39 = lean_box(0);
}
lean_inc(x_4);
if (lean_is_scalar(x_26)) {
 x_40 = lean_alloc_ctor(0, 2, 0);
} else {
 x_40 = x_26;
}
lean_ctor_set(x_40, 0, x_4);
lean_ctor_set(x_40, 1, x_38);
if (lean_is_scalar(x_39)) {
 x_41 = lean_alloc_ctor(1, 1, 0);
} else {
 x_41 = x_39;
}
lean_ctor_set(x_41, 0, x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_37);
x_17 = x_42;
goto block_24;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentArray_forInAux___at_Lean_Meta_getFVarSetToGeneralize___spec__67(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_12 = lean_ctor_get(x_5, 0);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_6);
x_15 = lean_array_get_size(x_12);
x_16 = lean_usize_of_nat(x_15);
lean_dec(x_15);
x_17 = 0;
lean_inc(x_7);
x_18 = l_Array_forInUnsafe_loop___at_Lean_Meta_getFVarSetToGeneralize___spec__68(x_1, x_2, x_3, x_4, x_13, x_12, x_16, x_17, x_14, x_7, x_8, x_9, x_10, x_11);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_box(0);
x_24 = l_Std_PersistentArray_forInAux___at_Lean_Meta_getFVarSetToGeneralize___spec__62___lambda__1(x_22, x_23, x_7, x_8, x_9, x_10, x_21);
lean_dec(x_7);
return x_24;
}
else
{
uint8_t x_25; 
lean_dec(x_19);
lean_dec(x_7);
x_25 = !lean_is_exclusive(x_18);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_18, 0);
lean_dec(x_26);
x_27 = lean_ctor_get(x_20, 0);
lean_inc(x_27);
lean_dec(x_20);
lean_ctor_set(x_18, 0, x_27);
return x_18;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_18, 1);
lean_inc(x_28);
lean_dec(x_18);
x_29 = lean_ctor_get(x_20, 0);
lean_inc(x_29);
lean_dec(x_20);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; size_t x_35; size_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_31 = lean_ctor_get(x_5, 0);
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_6);
x_34 = lean_array_get_size(x_31);
x_35 = lean_usize_of_nat(x_34);
lean_dec(x_34);
x_36 = 0;
x_37 = l_Array_forInUnsafe_loop___at_Lean_Meta_getFVarSetToGeneralize___spec__69(x_1, x_2, x_3, x_32, x_31, x_35, x_36, x_33, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_1);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
lean_dec(x_37);
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
lean_dec(x_38);
x_42 = lean_box(0);
x_43 = l_Std_PersistentArray_forInAux___at_Lean_Meta_getFVarSetToGeneralize___spec__62___lambda__1(x_41, x_42, x_7, x_8, x_9, x_10, x_40);
lean_dec(x_7);
return x_43;
}
else
{
uint8_t x_44; 
lean_dec(x_38);
lean_dec(x_7);
x_44 = !lean_is_exclusive(x_37);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_37, 0);
lean_dec(x_45);
x_46 = lean_ctor_get(x_39, 0);
lean_inc(x_46);
lean_dec(x_39);
lean_ctor_set(x_37, 0, x_46);
return x_37;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_37, 1);
lean_inc(x_47);
lean_dec(x_37);
x_48 = lean_ctor_get(x_39, 0);
lean_inc(x_48);
lean_dec(x_39);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_47);
return x_49;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_getFVarSetToGeneralize___spec__70(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = lean_usize_dec_lt(x_7, x_6);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_4);
lean_dec(x_3);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_8);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_16 = lean_array_uget(x_5, x_7);
x_25 = lean_ctor_get(x_8, 1);
lean_inc(x_25);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_26 = x_8;
} else {
 lean_dec_ref(x_8);
 x_26 = lean_box(0);
}
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_44; size_t x_45; size_t x_46; 
lean_dec(x_26);
lean_inc(x_4);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_4);
lean_ctor_set(x_44, 1, x_25);
x_45 = 1;
x_46 = lean_usize_add(x_7, x_45);
x_7 = x_46;
x_8 = x_44;
goto _start;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_186; 
x_48 = lean_ctor_get(x_16, 0);
lean_inc(x_48);
lean_dec(x_16);
x_49 = lean_ctor_get(x_25, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_25, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_51 = x_25;
} else {
 lean_dec_ref(x_25);
 x_51 = lean_box(0);
}
x_52 = l_Lean_LocalDecl_fvarId(x_48);
x_186 = l_Std_RBNode_findCore___at_Lean_Meta_mkGeneralizationForbiddenSet_visit___spec__1(x_1, x_52);
if (lean_obj_tag(x_186) == 0)
{
uint8_t x_187; 
x_187 = l_Lean_LocalDecl_isAuxDecl(x_48);
if (x_187 == 0)
{
uint8_t x_188; uint8_t x_189; 
x_188 = l_Lean_LocalDecl_binderInfo(x_48);
x_189 = l_Lean_BinderInfo_isInstImplicit(x_188);
if (x_189 == 0)
{
if (x_2 == 0)
{
lean_object* x_190; 
x_190 = lean_box(0);
x_53 = x_190;
goto block_185;
}
else
{
uint8_t x_191; 
x_191 = l_Lean_LocalDecl_isLet(x_48);
if (x_191 == 0)
{
lean_object* x_192; 
x_192 = lean_box(0);
x_53 = x_192;
goto block_185;
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; 
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_48);
x_193 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_193, 0, x_49);
lean_ctor_set(x_193, 1, x_50);
x_194 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_194, 0, x_193);
x_195 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_195, 0, x_194);
lean_ctor_set(x_195, 1, x_13);
x_27 = x_195;
goto block_43;
}
}
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; 
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_48);
x_196 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_196, 0, x_49);
lean_ctor_set(x_196, 1, x_50);
x_197 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_197, 0, x_196);
x_198 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_198, 0, x_197);
lean_ctor_set(x_198, 1, x_13);
x_27 = x_198;
goto block_43;
}
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; 
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_48);
x_199 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_199, 0, x_49);
lean_ctor_set(x_199, 1, x_50);
x_200 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_200, 0, x_199);
x_201 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_201, 0, x_200);
lean_ctor_set(x_201, 1, x_13);
x_27 = x_201;
goto block_43;
}
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; 
lean_dec(x_186);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_48);
x_202 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_202, 0, x_49);
lean_ctor_set(x_202, 1, x_50);
x_203 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_203, 0, x_202);
x_204 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_204, 0, x_203);
lean_ctor_set(x_204, 1, x_13);
x_27 = x_204;
goto block_43;
}
block_185:
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; lean_object* x_60; lean_object* x_105; uint8_t x_106; lean_object* x_107; 
lean_dec(x_53);
x_54 = lean_st_ref_get(x_12, x_13);
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
lean_dec(x_54);
x_56 = lean_st_ref_take(x_10, x_55);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_105 = lean_ctor_get(x_57, 0);
lean_inc(x_105);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; uint8_t x_145; 
x_142 = lean_ctor_get(x_48, 3);
lean_inc(x_142);
lean_dec(x_48);
x_143 = l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1;
lean_inc(x_105);
x_144 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set(x_144, 1, x_105);
x_145 = l_Lean_Expr_hasFVar(x_142);
if (x_145 == 0)
{
uint8_t x_146; 
x_146 = l_Lean_Expr_hasMVar(x_142);
if (x_146 == 0)
{
uint8_t x_147; 
lean_dec(x_142);
x_147 = 0;
x_106 = x_147;
x_107 = x_144;
goto block_141;
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; uint8_t x_151; 
lean_inc(x_50);
x_148 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__1___at_Lean_Meta_getFVarSetToGeneralize___spec__9(x_50, x_142, x_144);
x_149 = lean_ctor_get(x_148, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_148, 1);
lean_inc(x_150);
lean_dec(x_148);
x_151 = lean_unbox(x_149);
lean_dec(x_149);
x_106 = x_151;
x_107 = x_150;
goto block_141;
}
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; uint8_t x_155; 
lean_inc(x_50);
x_152 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__12___at_Lean_Meta_getFVarSetToGeneralize___spec__20(x_50, x_142, x_144);
x_153 = lean_ctor_get(x_152, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_152, 1);
lean_inc(x_154);
lean_dec(x_152);
x_155 = lean_unbox(x_153);
lean_dec(x_153);
x_106 = x_155;
x_107 = x_154;
goto block_141;
}
}
else
{
lean_object* x_156; lean_object* x_157; uint8_t x_158; lean_object* x_159; lean_object* x_172; lean_object* x_173; uint8_t x_174; 
x_156 = lean_ctor_get(x_48, 3);
lean_inc(x_156);
x_157 = lean_ctor_get(x_48, 4);
lean_inc(x_157);
lean_dec(x_48);
x_172 = l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1;
lean_inc(x_105);
x_173 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_173, 0, x_172);
lean_ctor_set(x_173, 1, x_105);
x_174 = l_Lean_Expr_hasFVar(x_156);
if (x_174 == 0)
{
uint8_t x_175; 
x_175 = l_Lean_Expr_hasMVar(x_156);
if (x_175 == 0)
{
uint8_t x_176; 
lean_dec(x_156);
x_176 = 0;
x_158 = x_176;
x_159 = x_173;
goto block_171;
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; uint8_t x_180; 
lean_inc(x_50);
x_177 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__39___at_Lean_Meta_getFVarSetToGeneralize___spec__47(x_50, x_156, x_173);
x_178 = lean_ctor_get(x_177, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_177, 1);
lean_inc(x_179);
lean_dec(x_177);
x_180 = lean_unbox(x_178);
lean_dec(x_178);
x_158 = x_180;
x_159 = x_179;
goto block_171;
}
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; uint8_t x_184; 
lean_inc(x_50);
x_181 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__50___at_Lean_Meta_getFVarSetToGeneralize___spec__58(x_50, x_156, x_173);
x_182 = lean_ctor_get(x_181, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_181, 1);
lean_inc(x_183);
lean_dec(x_181);
x_184 = lean_unbox(x_182);
lean_dec(x_182);
x_158 = x_184;
x_159 = x_183;
goto block_171;
}
block_171:
{
if (x_158 == 0)
{
uint8_t x_160; 
x_160 = l_Lean_Expr_hasFVar(x_157);
if (x_160 == 0)
{
uint8_t x_161; 
x_161 = l_Lean_Expr_hasMVar(x_157);
if (x_161 == 0)
{
uint8_t x_162; 
lean_dec(x_157);
x_162 = 0;
x_106 = x_162;
x_107 = x_159;
goto block_141;
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; uint8_t x_166; 
lean_inc(x_50);
lean_inc(x_3);
x_163 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__23(x_3, x_50, x_157, x_159);
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_163, 1);
lean_inc(x_165);
lean_dec(x_163);
x_166 = lean_unbox(x_164);
lean_dec(x_164);
x_106 = x_166;
x_107 = x_165;
goto block_141;
}
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; uint8_t x_170; 
lean_inc(x_50);
lean_inc(x_3);
x_167 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__31(x_3, x_50, x_157, x_159);
x_168 = lean_ctor_get(x_167, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_167, 1);
lean_inc(x_169);
lean_dec(x_167);
x_170 = lean_unbox(x_168);
lean_dec(x_168);
x_106 = x_170;
x_107 = x_169;
goto block_141;
}
}
else
{
lean_dec(x_157);
x_106 = x_158;
x_107 = x_159;
goto block_141;
}
}
}
block_104:
{
uint8_t x_61; 
x_61 = !lean_is_exclusive(x_57);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_57, 0);
lean_dec(x_62);
lean_ctor_set(x_57, 0, x_60);
x_63 = lean_st_ref_set(x_10, x_57, x_58);
if (x_59 == 0)
{
uint8_t x_64; 
lean_dec(x_52);
x_64 = !lean_is_exclusive(x_63);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_63, 0);
lean_dec(x_65);
if (lean_is_scalar(x_51)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_51;
}
lean_ctor_set(x_66, 0, x_49);
lean_ctor_set(x_66, 1, x_50);
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_63, 0, x_67);
x_27 = x_63;
goto block_43;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_68 = lean_ctor_get(x_63, 1);
lean_inc(x_68);
lean_dec(x_63);
if (lean_is_scalar(x_51)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_51;
}
lean_ctor_set(x_69, 0, x_49);
lean_ctor_set(x_69, 1, x_50);
x_70 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_70, 0, x_69);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_68);
x_27 = x_71;
goto block_43;
}
}
else
{
uint8_t x_72; 
x_72 = !lean_is_exclusive(x_63);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_73 = lean_ctor_get(x_63, 0);
lean_dec(x_73);
x_74 = lean_box(0);
lean_inc(x_52);
x_75 = l_Std_RBNode_insert___at_Lean_CollectFVars_State_add___spec__1(x_49, x_52, x_74);
x_76 = l_Std_RBNode_insert___at_Lean_CollectFVars_State_add___spec__1(x_50, x_52, x_74);
if (lean_is_scalar(x_51)) {
 x_77 = lean_alloc_ctor(0, 2, 0);
} else {
 x_77 = x_51;
}
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
x_78 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_63, 0, x_78);
x_27 = x_63;
goto block_43;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_79 = lean_ctor_get(x_63, 1);
lean_inc(x_79);
lean_dec(x_63);
x_80 = lean_box(0);
lean_inc(x_52);
x_81 = l_Std_RBNode_insert___at_Lean_CollectFVars_State_add___spec__1(x_49, x_52, x_80);
x_82 = l_Std_RBNode_insert___at_Lean_CollectFVars_State_add___spec__1(x_50, x_52, x_80);
if (lean_is_scalar(x_51)) {
 x_83 = lean_alloc_ctor(0, 2, 0);
} else {
 x_83 = x_51;
}
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
x_84 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_84, 0, x_83);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_79);
x_27 = x_85;
goto block_43;
}
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_86 = lean_ctor_get(x_57, 1);
x_87 = lean_ctor_get(x_57, 2);
x_88 = lean_ctor_get(x_57, 3);
lean_inc(x_88);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_57);
x_89 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_89, 0, x_60);
lean_ctor_set(x_89, 1, x_86);
lean_ctor_set(x_89, 2, x_87);
lean_ctor_set(x_89, 3, x_88);
x_90 = lean_st_ref_set(x_10, x_89, x_58);
if (x_59 == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_52);
x_91 = lean_ctor_get(x_90, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_92 = x_90;
} else {
 lean_dec_ref(x_90);
 x_92 = lean_box(0);
}
if (lean_is_scalar(x_51)) {
 x_93 = lean_alloc_ctor(0, 2, 0);
} else {
 x_93 = x_51;
}
lean_ctor_set(x_93, 0, x_49);
lean_ctor_set(x_93, 1, x_50);
x_94 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_94, 0, x_93);
if (lean_is_scalar(x_92)) {
 x_95 = lean_alloc_ctor(0, 2, 0);
} else {
 x_95 = x_92;
}
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_91);
x_27 = x_95;
goto block_43;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_96 = lean_ctor_get(x_90, 1);
lean_inc(x_96);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_97 = x_90;
} else {
 lean_dec_ref(x_90);
 x_97 = lean_box(0);
}
x_98 = lean_box(0);
lean_inc(x_52);
x_99 = l_Std_RBNode_insert___at_Lean_CollectFVars_State_add___spec__1(x_49, x_52, x_98);
x_100 = l_Std_RBNode_insert___at_Lean_CollectFVars_State_add___spec__1(x_50, x_52, x_98);
if (lean_is_scalar(x_51)) {
 x_101 = lean_alloc_ctor(0, 2, 0);
} else {
 x_101 = x_51;
}
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
x_102 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_102, 0, x_101);
if (lean_is_scalar(x_97)) {
 x_103 = lean_alloc_ctor(0, 2, 0);
} else {
 x_103 = x_97;
}
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_96);
x_27 = x_103;
goto block_43;
}
}
}
block_141:
{
lean_object* x_108; uint8_t x_109; 
x_108 = lean_ctor_get(x_107, 1);
lean_inc(x_108);
lean_dec(x_107);
x_109 = lean_ctor_get_uint8(x_108, sizeof(void*)*8);
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; uint8_t x_118; 
x_110 = lean_ctor_get(x_108, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_108, 1);
lean_inc(x_111);
x_112 = lean_ctor_get(x_108, 2);
lean_inc(x_112);
x_113 = lean_ctor_get(x_108, 3);
lean_inc(x_113);
x_114 = lean_ctor_get(x_108, 4);
lean_inc(x_114);
x_115 = lean_ctor_get(x_108, 5);
lean_inc(x_115);
x_116 = lean_ctor_get(x_108, 6);
lean_inc(x_116);
x_117 = lean_ctor_get(x_108, 7);
lean_inc(x_117);
lean_dec(x_108);
x_118 = !lean_is_exclusive(x_105);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_119 = lean_ctor_get(x_105, 7);
lean_dec(x_119);
x_120 = lean_ctor_get(x_105, 6);
lean_dec(x_120);
x_121 = lean_ctor_get(x_105, 5);
lean_dec(x_121);
x_122 = lean_ctor_get(x_105, 4);
lean_dec(x_122);
x_123 = lean_ctor_get(x_105, 3);
lean_dec(x_123);
x_124 = lean_ctor_get(x_105, 2);
lean_dec(x_124);
x_125 = lean_ctor_get(x_105, 1);
lean_dec(x_125);
x_126 = lean_ctor_get(x_105, 0);
lean_dec(x_126);
lean_ctor_set(x_105, 7, x_117);
lean_ctor_set(x_105, 6, x_116);
lean_ctor_set(x_105, 5, x_115);
lean_ctor_set(x_105, 4, x_114);
lean_ctor_set(x_105, 3, x_113);
lean_ctor_set(x_105, 2, x_112);
lean_ctor_set(x_105, 1, x_111);
lean_ctor_set(x_105, 0, x_110);
x_59 = x_106;
x_60 = x_105;
goto block_104;
}
else
{
uint8_t x_127; lean_object* x_128; 
x_127 = lean_ctor_get_uint8(x_105, sizeof(void*)*8);
lean_dec(x_105);
x_128 = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(x_128, 0, x_110);
lean_ctor_set(x_128, 1, x_111);
lean_ctor_set(x_128, 2, x_112);
lean_ctor_set(x_128, 3, x_113);
lean_ctor_set(x_128, 4, x_114);
lean_ctor_set(x_128, 5, x_115);
lean_ctor_set(x_128, 6, x_116);
lean_ctor_set(x_128, 7, x_117);
lean_ctor_set_uint8(x_128, sizeof(void*)*8, x_127);
x_59 = x_106;
x_60 = x_128;
goto block_104;
}
}
else
{
uint8_t x_129; 
lean_dec(x_105);
x_129 = !lean_is_exclusive(x_108);
if (x_129 == 0)
{
uint8_t x_130; 
x_130 = 1;
lean_ctor_set_uint8(x_108, sizeof(void*)*8, x_130);
x_59 = x_106;
x_60 = x_108;
goto block_104;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; uint8_t x_139; lean_object* x_140; 
x_131 = lean_ctor_get(x_108, 0);
x_132 = lean_ctor_get(x_108, 1);
x_133 = lean_ctor_get(x_108, 2);
x_134 = lean_ctor_get(x_108, 3);
x_135 = lean_ctor_get(x_108, 4);
x_136 = lean_ctor_get(x_108, 5);
x_137 = lean_ctor_get(x_108, 6);
x_138 = lean_ctor_get(x_108, 7);
lean_inc(x_138);
lean_inc(x_137);
lean_inc(x_136);
lean_inc(x_135);
lean_inc(x_134);
lean_inc(x_133);
lean_inc(x_132);
lean_inc(x_131);
lean_dec(x_108);
x_139 = 1;
x_140 = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(x_140, 0, x_131);
lean_ctor_set(x_140, 1, x_132);
lean_ctor_set(x_140, 2, x_133);
lean_ctor_set(x_140, 3, x_134);
lean_ctor_set(x_140, 4, x_135);
lean_ctor_set(x_140, 5, x_136);
lean_ctor_set(x_140, 6, x_137);
lean_ctor_set(x_140, 7, x_138);
lean_ctor_set_uint8(x_140, sizeof(void*)*8, x_139);
x_59 = x_106;
x_60 = x_140;
goto block_104;
}
}
}
}
}
block_24:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec(x_18);
x_21 = 1;
x_22 = lean_usize_add(x_7, x_21);
x_7 = x_22;
x_8 = x_20;
x_13 = x_19;
goto _start;
}
block_43:
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_29, 0);
lean_inc(x_4);
if (lean_is_scalar(x_26)) {
 x_32 = lean_alloc_ctor(0, 2, 0);
} else {
 x_32 = x_26;
}
lean_ctor_set(x_32, 0, x_4);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set(x_29, 0, x_32);
x_17 = x_27;
goto block_24;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_29, 0);
lean_inc(x_33);
lean_dec(x_29);
lean_inc(x_4);
if (lean_is_scalar(x_26)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_26;
}
lean_ctor_set(x_34, 0, x_4);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_27, 0, x_35);
x_17 = x_27;
goto block_24;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_36 = lean_ctor_get(x_27, 0);
x_37 = lean_ctor_get(x_27, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_27);
x_38 = lean_ctor_get(x_36, 0);
lean_inc(x_38);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 x_39 = x_36;
} else {
 lean_dec_ref(x_36);
 x_39 = lean_box(0);
}
lean_inc(x_4);
if (lean_is_scalar(x_26)) {
 x_40 = lean_alloc_ctor(0, 2, 0);
} else {
 x_40 = x_26;
}
lean_ctor_set(x_40, 0, x_4);
lean_ctor_set(x_40, 1, x_38);
if (lean_is_scalar(x_39)) {
 x_41 = lean_alloc_ctor(1, 1, 0);
} else {
 x_41 = x_39;
}
lean_ctor_set(x_41, 0, x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_37);
x_17 = x_42;
goto block_24;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentArray_forIn___at_Lean_Meta_getFVarSetToGeneralize___spec__66(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_1);
x_12 = l_Std_PersistentArray_forInAux___at_Lean_Meta_getFVarSetToGeneralize___spec__67(x_1, x_2, x_3, x_5, x_11, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_12, 0);
lean_dec(x_15);
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_16);
lean_dec(x_13);
lean_ctor_set(x_12, 0, x_16);
return x_12;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_dec(x_12);
x_18 = lean_ctor_get(x_13, 0);
lean_inc(x_18);
lean_dec(x_13);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; size_t x_26; size_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_20 = lean_ctor_get(x_12, 1);
lean_inc(x_20);
lean_dec(x_12);
x_21 = lean_ctor_get(x_13, 0);
lean_inc(x_21);
lean_dec(x_13);
x_22 = lean_ctor_get(x_4, 1);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_21);
x_25 = lean_array_get_size(x_22);
x_26 = lean_usize_of_nat(x_25);
lean_dec(x_25);
x_27 = 0;
x_28 = l_Array_forInUnsafe_loop___at_Lean_Meta_getFVarSetToGeneralize___spec__70(x_1, x_2, x_3, x_23, x_22, x_26, x_27, x_24, x_6, x_7, x_8, x_9, x_20);
lean_dec(x_6);
lean_dec(x_1);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_28);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_28, 0);
lean_dec(x_32);
x_33 = lean_ctor_get(x_29, 1);
lean_inc(x_33);
lean_dec(x_29);
lean_ctor_set(x_28, 0, x_33);
return x_28;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_28, 1);
lean_inc(x_34);
lean_dec(x_28);
x_35 = lean_ctor_get(x_29, 1);
lean_inc(x_35);
lean_dec(x_29);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
return x_36;
}
}
else
{
uint8_t x_37; 
lean_dec(x_29);
x_37 = !lean_is_exclusive(x_28);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_28, 0);
lean_dec(x_38);
x_39 = lean_ctor_get(x_30, 0);
lean_inc(x_39);
lean_dec(x_30);
lean_ctor_set(x_28, 0, x_39);
return x_28;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_28, 1);
lean_inc(x_40);
lean_dec(x_28);
x_41 = lean_ctor_get(x_30, 0);
lean_inc(x_41);
lean_dec(x_30);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
return x_42;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_getFVarSetToGeneralize___spec__71(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; size_t x_8; size_t x_9; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Lean_Expr_isFVar(x_6);
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
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
x_12 = lean_box(0);
x_13 = l_Std_RBNode_insert___at_Lean_CollectFVars_State_add___spec__1(x_4, x_11, x_12);
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
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_getFVarSetToGeneralize___spec__74(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, size_t x_7, size_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; 
x_15 = lean_usize_dec_lt(x_8, x_7);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_9);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
else
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_array_uget(x_6, x_8);
x_18 = !lean_is_exclusive(x_9);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_9, 1);
x_20 = lean_ctor_get(x_9, 0);
lean_dec(x_20);
lean_inc(x_10);
lean_inc(x_19);
lean_inc(x_3);
lean_inc(x_1);
x_21 = l_Std_PersistentArray_forInAux___at_Lean_Meta_getFVarSetToGeneralize___spec__73(x_1, x_2, x_3, x_4, x_17, x_19, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_17);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_21);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_21, 0);
lean_dec(x_24);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_9, 0, x_25);
lean_ctor_set(x_21, 0, x_9);
return x_21;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_21, 1);
lean_inc(x_26);
lean_dec(x_21);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_22);
lean_ctor_set(x_9, 0, x_27);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_9);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; size_t x_31; size_t x_32; 
lean_dec(x_19);
x_29 = lean_ctor_get(x_21, 1);
lean_inc(x_29);
lean_dec(x_21);
x_30 = lean_ctor_get(x_22, 0);
lean_inc(x_30);
lean_dec(x_22);
lean_inc(x_5);
lean_ctor_set(x_9, 1, x_30);
lean_ctor_set(x_9, 0, x_5);
x_31 = 1;
x_32 = lean_usize_add(x_8, x_31);
x_8 = x_32;
x_14 = x_29;
goto _start;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_9, 1);
lean_inc(x_34);
lean_dec(x_9);
lean_inc(x_10);
lean_inc(x_34);
lean_inc(x_3);
lean_inc(x_1);
x_35 = l_Std_PersistentArray_forInAux___at_Lean_Meta_getFVarSetToGeneralize___spec__73(x_1, x_2, x_3, x_4, x_17, x_34, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_17);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_38 = x_35;
} else {
 lean_dec_ref(x_35);
 x_38 = lean_box(0);
}
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_36);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_34);
if (lean_is_scalar(x_38)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_38;
}
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_37);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; size_t x_45; size_t x_46; 
lean_dec(x_34);
x_42 = lean_ctor_get(x_35, 1);
lean_inc(x_42);
lean_dec(x_35);
x_43 = lean_ctor_get(x_36, 0);
lean_inc(x_43);
lean_dec(x_36);
lean_inc(x_5);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_5);
lean_ctor_set(x_44, 1, x_43);
x_45 = 1;
x_46 = lean_usize_add(x_8, x_45);
x_8 = x_46;
x_9 = x_44;
x_14 = x_42;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_getFVarSetToGeneralize___spec__75(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = lean_usize_dec_lt(x_7, x_6);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_4);
lean_dec(x_3);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_8);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_16 = lean_array_uget(x_5, x_7);
x_25 = lean_ctor_get(x_8, 1);
lean_inc(x_25);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_26 = x_8;
} else {
 lean_dec_ref(x_8);
 x_26 = lean_box(0);
}
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_44; size_t x_45; size_t x_46; 
lean_dec(x_26);
lean_inc(x_4);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_4);
lean_ctor_set(x_44, 1, x_25);
x_45 = 1;
x_46 = lean_usize_add(x_7, x_45);
x_7 = x_46;
x_8 = x_44;
goto _start;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_186; 
x_48 = lean_ctor_get(x_16, 0);
lean_inc(x_48);
lean_dec(x_16);
x_49 = lean_ctor_get(x_25, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_25, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_51 = x_25;
} else {
 lean_dec_ref(x_25);
 x_51 = lean_box(0);
}
x_52 = l_Lean_LocalDecl_fvarId(x_48);
x_186 = l_Std_RBNode_findCore___at_Lean_Meta_mkGeneralizationForbiddenSet_visit___spec__1(x_1, x_52);
if (lean_obj_tag(x_186) == 0)
{
uint8_t x_187; 
x_187 = l_Lean_LocalDecl_isAuxDecl(x_48);
if (x_187 == 0)
{
uint8_t x_188; uint8_t x_189; 
x_188 = l_Lean_LocalDecl_binderInfo(x_48);
x_189 = l_Lean_BinderInfo_isInstImplicit(x_188);
if (x_189 == 0)
{
if (x_2 == 0)
{
lean_object* x_190; 
x_190 = lean_box(0);
x_53 = x_190;
goto block_185;
}
else
{
uint8_t x_191; 
x_191 = l_Lean_LocalDecl_isLet(x_48);
if (x_191 == 0)
{
lean_object* x_192; 
x_192 = lean_box(0);
x_53 = x_192;
goto block_185;
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; 
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_48);
x_193 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_193, 0, x_49);
lean_ctor_set(x_193, 1, x_50);
x_194 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_194, 0, x_193);
x_195 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_195, 0, x_194);
lean_ctor_set(x_195, 1, x_13);
x_27 = x_195;
goto block_43;
}
}
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; 
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_48);
x_196 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_196, 0, x_49);
lean_ctor_set(x_196, 1, x_50);
x_197 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_197, 0, x_196);
x_198 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_198, 0, x_197);
lean_ctor_set(x_198, 1, x_13);
x_27 = x_198;
goto block_43;
}
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; 
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_48);
x_199 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_199, 0, x_49);
lean_ctor_set(x_199, 1, x_50);
x_200 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_200, 0, x_199);
x_201 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_201, 0, x_200);
lean_ctor_set(x_201, 1, x_13);
x_27 = x_201;
goto block_43;
}
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; 
lean_dec(x_186);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_48);
x_202 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_202, 0, x_49);
lean_ctor_set(x_202, 1, x_50);
x_203 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_203, 0, x_202);
x_204 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_204, 0, x_203);
lean_ctor_set(x_204, 1, x_13);
x_27 = x_204;
goto block_43;
}
block_185:
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; lean_object* x_60; lean_object* x_105; uint8_t x_106; lean_object* x_107; 
lean_dec(x_53);
x_54 = lean_st_ref_get(x_12, x_13);
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
lean_dec(x_54);
x_56 = lean_st_ref_take(x_10, x_55);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_105 = lean_ctor_get(x_57, 0);
lean_inc(x_105);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; uint8_t x_145; 
x_142 = lean_ctor_get(x_48, 3);
lean_inc(x_142);
lean_dec(x_48);
x_143 = l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1;
lean_inc(x_105);
x_144 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set(x_144, 1, x_105);
x_145 = l_Lean_Expr_hasFVar(x_142);
if (x_145 == 0)
{
uint8_t x_146; 
x_146 = l_Lean_Expr_hasMVar(x_142);
if (x_146 == 0)
{
uint8_t x_147; 
lean_dec(x_142);
x_147 = 0;
x_106 = x_147;
x_107 = x_144;
goto block_141;
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; uint8_t x_151; 
lean_inc(x_50);
x_148 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__1___at_Lean_Meta_getFVarSetToGeneralize___spec__9(x_50, x_142, x_144);
x_149 = lean_ctor_get(x_148, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_148, 1);
lean_inc(x_150);
lean_dec(x_148);
x_151 = lean_unbox(x_149);
lean_dec(x_149);
x_106 = x_151;
x_107 = x_150;
goto block_141;
}
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; uint8_t x_155; 
lean_inc(x_50);
x_152 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__12___at_Lean_Meta_getFVarSetToGeneralize___spec__20(x_50, x_142, x_144);
x_153 = lean_ctor_get(x_152, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_152, 1);
lean_inc(x_154);
lean_dec(x_152);
x_155 = lean_unbox(x_153);
lean_dec(x_153);
x_106 = x_155;
x_107 = x_154;
goto block_141;
}
}
else
{
lean_object* x_156; lean_object* x_157; uint8_t x_158; lean_object* x_159; lean_object* x_172; lean_object* x_173; uint8_t x_174; 
x_156 = lean_ctor_get(x_48, 3);
lean_inc(x_156);
x_157 = lean_ctor_get(x_48, 4);
lean_inc(x_157);
lean_dec(x_48);
x_172 = l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1;
lean_inc(x_105);
x_173 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_173, 0, x_172);
lean_ctor_set(x_173, 1, x_105);
x_174 = l_Lean_Expr_hasFVar(x_156);
if (x_174 == 0)
{
uint8_t x_175; 
x_175 = l_Lean_Expr_hasMVar(x_156);
if (x_175 == 0)
{
uint8_t x_176; 
lean_dec(x_156);
x_176 = 0;
x_158 = x_176;
x_159 = x_173;
goto block_171;
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; uint8_t x_180; 
lean_inc(x_50);
x_177 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__39___at_Lean_Meta_getFVarSetToGeneralize___spec__47(x_50, x_156, x_173);
x_178 = lean_ctor_get(x_177, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_177, 1);
lean_inc(x_179);
lean_dec(x_177);
x_180 = lean_unbox(x_178);
lean_dec(x_178);
x_158 = x_180;
x_159 = x_179;
goto block_171;
}
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; uint8_t x_184; 
lean_inc(x_50);
x_181 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__50___at_Lean_Meta_getFVarSetToGeneralize___spec__58(x_50, x_156, x_173);
x_182 = lean_ctor_get(x_181, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_181, 1);
lean_inc(x_183);
lean_dec(x_181);
x_184 = lean_unbox(x_182);
lean_dec(x_182);
x_158 = x_184;
x_159 = x_183;
goto block_171;
}
block_171:
{
if (x_158 == 0)
{
uint8_t x_160; 
x_160 = l_Lean_Expr_hasFVar(x_157);
if (x_160 == 0)
{
uint8_t x_161; 
x_161 = l_Lean_Expr_hasMVar(x_157);
if (x_161 == 0)
{
uint8_t x_162; 
lean_dec(x_157);
x_162 = 0;
x_106 = x_162;
x_107 = x_159;
goto block_141;
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; uint8_t x_166; 
lean_inc(x_50);
lean_inc(x_3);
x_163 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__23(x_3, x_50, x_157, x_159);
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_163, 1);
lean_inc(x_165);
lean_dec(x_163);
x_166 = lean_unbox(x_164);
lean_dec(x_164);
x_106 = x_166;
x_107 = x_165;
goto block_141;
}
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; uint8_t x_170; 
lean_inc(x_50);
lean_inc(x_3);
x_167 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__31(x_3, x_50, x_157, x_159);
x_168 = lean_ctor_get(x_167, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_167, 1);
lean_inc(x_169);
lean_dec(x_167);
x_170 = lean_unbox(x_168);
lean_dec(x_168);
x_106 = x_170;
x_107 = x_169;
goto block_141;
}
}
else
{
lean_dec(x_157);
x_106 = x_158;
x_107 = x_159;
goto block_141;
}
}
}
block_104:
{
uint8_t x_61; 
x_61 = !lean_is_exclusive(x_57);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_57, 0);
lean_dec(x_62);
lean_ctor_set(x_57, 0, x_60);
x_63 = lean_st_ref_set(x_10, x_57, x_58);
if (x_59 == 0)
{
uint8_t x_64; 
lean_dec(x_52);
x_64 = !lean_is_exclusive(x_63);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_63, 0);
lean_dec(x_65);
if (lean_is_scalar(x_51)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_51;
}
lean_ctor_set(x_66, 0, x_49);
lean_ctor_set(x_66, 1, x_50);
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_63, 0, x_67);
x_27 = x_63;
goto block_43;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_68 = lean_ctor_get(x_63, 1);
lean_inc(x_68);
lean_dec(x_63);
if (lean_is_scalar(x_51)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_51;
}
lean_ctor_set(x_69, 0, x_49);
lean_ctor_set(x_69, 1, x_50);
x_70 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_70, 0, x_69);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_68);
x_27 = x_71;
goto block_43;
}
}
else
{
uint8_t x_72; 
x_72 = !lean_is_exclusive(x_63);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_73 = lean_ctor_get(x_63, 0);
lean_dec(x_73);
x_74 = lean_box(0);
lean_inc(x_52);
x_75 = l_Std_RBNode_insert___at_Lean_CollectFVars_State_add___spec__1(x_49, x_52, x_74);
x_76 = l_Std_RBNode_insert___at_Lean_CollectFVars_State_add___spec__1(x_50, x_52, x_74);
if (lean_is_scalar(x_51)) {
 x_77 = lean_alloc_ctor(0, 2, 0);
} else {
 x_77 = x_51;
}
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
x_78 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_63, 0, x_78);
x_27 = x_63;
goto block_43;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_79 = lean_ctor_get(x_63, 1);
lean_inc(x_79);
lean_dec(x_63);
x_80 = lean_box(0);
lean_inc(x_52);
x_81 = l_Std_RBNode_insert___at_Lean_CollectFVars_State_add___spec__1(x_49, x_52, x_80);
x_82 = l_Std_RBNode_insert___at_Lean_CollectFVars_State_add___spec__1(x_50, x_52, x_80);
if (lean_is_scalar(x_51)) {
 x_83 = lean_alloc_ctor(0, 2, 0);
} else {
 x_83 = x_51;
}
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
x_84 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_84, 0, x_83);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_79);
x_27 = x_85;
goto block_43;
}
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_86 = lean_ctor_get(x_57, 1);
x_87 = lean_ctor_get(x_57, 2);
x_88 = lean_ctor_get(x_57, 3);
lean_inc(x_88);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_57);
x_89 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_89, 0, x_60);
lean_ctor_set(x_89, 1, x_86);
lean_ctor_set(x_89, 2, x_87);
lean_ctor_set(x_89, 3, x_88);
x_90 = lean_st_ref_set(x_10, x_89, x_58);
if (x_59 == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_52);
x_91 = lean_ctor_get(x_90, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_92 = x_90;
} else {
 lean_dec_ref(x_90);
 x_92 = lean_box(0);
}
if (lean_is_scalar(x_51)) {
 x_93 = lean_alloc_ctor(0, 2, 0);
} else {
 x_93 = x_51;
}
lean_ctor_set(x_93, 0, x_49);
lean_ctor_set(x_93, 1, x_50);
x_94 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_94, 0, x_93);
if (lean_is_scalar(x_92)) {
 x_95 = lean_alloc_ctor(0, 2, 0);
} else {
 x_95 = x_92;
}
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_91);
x_27 = x_95;
goto block_43;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_96 = lean_ctor_get(x_90, 1);
lean_inc(x_96);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_97 = x_90;
} else {
 lean_dec_ref(x_90);
 x_97 = lean_box(0);
}
x_98 = lean_box(0);
lean_inc(x_52);
x_99 = l_Std_RBNode_insert___at_Lean_CollectFVars_State_add___spec__1(x_49, x_52, x_98);
x_100 = l_Std_RBNode_insert___at_Lean_CollectFVars_State_add___spec__1(x_50, x_52, x_98);
if (lean_is_scalar(x_51)) {
 x_101 = lean_alloc_ctor(0, 2, 0);
} else {
 x_101 = x_51;
}
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
x_102 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_102, 0, x_101);
if (lean_is_scalar(x_97)) {
 x_103 = lean_alloc_ctor(0, 2, 0);
} else {
 x_103 = x_97;
}
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_96);
x_27 = x_103;
goto block_43;
}
}
}
block_141:
{
lean_object* x_108; uint8_t x_109; 
x_108 = lean_ctor_get(x_107, 1);
lean_inc(x_108);
lean_dec(x_107);
x_109 = lean_ctor_get_uint8(x_108, sizeof(void*)*8);
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; uint8_t x_118; 
x_110 = lean_ctor_get(x_108, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_108, 1);
lean_inc(x_111);
x_112 = lean_ctor_get(x_108, 2);
lean_inc(x_112);
x_113 = lean_ctor_get(x_108, 3);
lean_inc(x_113);
x_114 = lean_ctor_get(x_108, 4);
lean_inc(x_114);
x_115 = lean_ctor_get(x_108, 5);
lean_inc(x_115);
x_116 = lean_ctor_get(x_108, 6);
lean_inc(x_116);
x_117 = lean_ctor_get(x_108, 7);
lean_inc(x_117);
lean_dec(x_108);
x_118 = !lean_is_exclusive(x_105);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_119 = lean_ctor_get(x_105, 7);
lean_dec(x_119);
x_120 = lean_ctor_get(x_105, 6);
lean_dec(x_120);
x_121 = lean_ctor_get(x_105, 5);
lean_dec(x_121);
x_122 = lean_ctor_get(x_105, 4);
lean_dec(x_122);
x_123 = lean_ctor_get(x_105, 3);
lean_dec(x_123);
x_124 = lean_ctor_get(x_105, 2);
lean_dec(x_124);
x_125 = lean_ctor_get(x_105, 1);
lean_dec(x_125);
x_126 = lean_ctor_get(x_105, 0);
lean_dec(x_126);
lean_ctor_set(x_105, 7, x_117);
lean_ctor_set(x_105, 6, x_116);
lean_ctor_set(x_105, 5, x_115);
lean_ctor_set(x_105, 4, x_114);
lean_ctor_set(x_105, 3, x_113);
lean_ctor_set(x_105, 2, x_112);
lean_ctor_set(x_105, 1, x_111);
lean_ctor_set(x_105, 0, x_110);
x_59 = x_106;
x_60 = x_105;
goto block_104;
}
else
{
uint8_t x_127; lean_object* x_128; 
x_127 = lean_ctor_get_uint8(x_105, sizeof(void*)*8);
lean_dec(x_105);
x_128 = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(x_128, 0, x_110);
lean_ctor_set(x_128, 1, x_111);
lean_ctor_set(x_128, 2, x_112);
lean_ctor_set(x_128, 3, x_113);
lean_ctor_set(x_128, 4, x_114);
lean_ctor_set(x_128, 5, x_115);
lean_ctor_set(x_128, 6, x_116);
lean_ctor_set(x_128, 7, x_117);
lean_ctor_set_uint8(x_128, sizeof(void*)*8, x_127);
x_59 = x_106;
x_60 = x_128;
goto block_104;
}
}
else
{
uint8_t x_129; 
lean_dec(x_105);
x_129 = !lean_is_exclusive(x_108);
if (x_129 == 0)
{
uint8_t x_130; 
x_130 = 1;
lean_ctor_set_uint8(x_108, sizeof(void*)*8, x_130);
x_59 = x_106;
x_60 = x_108;
goto block_104;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; uint8_t x_139; lean_object* x_140; 
x_131 = lean_ctor_get(x_108, 0);
x_132 = lean_ctor_get(x_108, 1);
x_133 = lean_ctor_get(x_108, 2);
x_134 = lean_ctor_get(x_108, 3);
x_135 = lean_ctor_get(x_108, 4);
x_136 = lean_ctor_get(x_108, 5);
x_137 = lean_ctor_get(x_108, 6);
x_138 = lean_ctor_get(x_108, 7);
lean_inc(x_138);
lean_inc(x_137);
lean_inc(x_136);
lean_inc(x_135);
lean_inc(x_134);
lean_inc(x_133);
lean_inc(x_132);
lean_inc(x_131);
lean_dec(x_108);
x_139 = 1;
x_140 = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(x_140, 0, x_131);
lean_ctor_set(x_140, 1, x_132);
lean_ctor_set(x_140, 2, x_133);
lean_ctor_set(x_140, 3, x_134);
lean_ctor_set(x_140, 4, x_135);
lean_ctor_set(x_140, 5, x_136);
lean_ctor_set(x_140, 6, x_137);
lean_ctor_set(x_140, 7, x_138);
lean_ctor_set_uint8(x_140, sizeof(void*)*8, x_139);
x_59 = x_106;
x_60 = x_140;
goto block_104;
}
}
}
}
}
block_24:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec(x_18);
x_21 = 1;
x_22 = lean_usize_add(x_7, x_21);
x_7 = x_22;
x_8 = x_20;
x_13 = x_19;
goto _start;
}
block_43:
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_29, 0);
lean_inc(x_4);
if (lean_is_scalar(x_26)) {
 x_32 = lean_alloc_ctor(0, 2, 0);
} else {
 x_32 = x_26;
}
lean_ctor_set(x_32, 0, x_4);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set(x_29, 0, x_32);
x_17 = x_27;
goto block_24;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_29, 0);
lean_inc(x_33);
lean_dec(x_29);
lean_inc(x_4);
if (lean_is_scalar(x_26)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_26;
}
lean_ctor_set(x_34, 0, x_4);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_27, 0, x_35);
x_17 = x_27;
goto block_24;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_36 = lean_ctor_get(x_27, 0);
x_37 = lean_ctor_get(x_27, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_27);
x_38 = lean_ctor_get(x_36, 0);
lean_inc(x_38);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 x_39 = x_36;
} else {
 lean_dec_ref(x_36);
 x_39 = lean_box(0);
}
lean_inc(x_4);
if (lean_is_scalar(x_26)) {
 x_40 = lean_alloc_ctor(0, 2, 0);
} else {
 x_40 = x_26;
}
lean_ctor_set(x_40, 0, x_4);
lean_ctor_set(x_40, 1, x_38);
if (lean_is_scalar(x_39)) {
 x_41 = lean_alloc_ctor(1, 1, 0);
} else {
 x_41 = x_39;
}
lean_ctor_set(x_41, 0, x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_37);
x_17 = x_42;
goto block_24;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentArray_forInAux___at_Lean_Meta_getFVarSetToGeneralize___spec__73(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_12 = lean_ctor_get(x_5, 0);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_6);
x_15 = lean_array_get_size(x_12);
x_16 = lean_usize_of_nat(x_15);
lean_dec(x_15);
x_17 = 0;
lean_inc(x_7);
x_18 = l_Array_forInUnsafe_loop___at_Lean_Meta_getFVarSetToGeneralize___spec__74(x_1, x_2, x_3, x_4, x_13, x_12, x_16, x_17, x_14, x_7, x_8, x_9, x_10, x_11);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_box(0);
x_24 = l_Std_PersistentArray_forInAux___at_Lean_Meta_getFVarSetToGeneralize___spec__62___lambda__1(x_22, x_23, x_7, x_8, x_9, x_10, x_21);
lean_dec(x_7);
return x_24;
}
else
{
uint8_t x_25; 
lean_dec(x_19);
lean_dec(x_7);
x_25 = !lean_is_exclusive(x_18);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_18, 0);
lean_dec(x_26);
x_27 = lean_ctor_get(x_20, 0);
lean_inc(x_27);
lean_dec(x_20);
lean_ctor_set(x_18, 0, x_27);
return x_18;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_18, 1);
lean_inc(x_28);
lean_dec(x_18);
x_29 = lean_ctor_get(x_20, 0);
lean_inc(x_29);
lean_dec(x_20);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; size_t x_35; size_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_31 = lean_ctor_get(x_5, 0);
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_6);
x_34 = lean_array_get_size(x_31);
x_35 = lean_usize_of_nat(x_34);
lean_dec(x_34);
x_36 = 0;
x_37 = l_Array_forInUnsafe_loop___at_Lean_Meta_getFVarSetToGeneralize___spec__75(x_1, x_2, x_3, x_32, x_31, x_35, x_36, x_33, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_1);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
lean_dec(x_37);
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
lean_dec(x_38);
x_42 = lean_box(0);
x_43 = l_Std_PersistentArray_forInAux___at_Lean_Meta_getFVarSetToGeneralize___spec__62___lambda__1(x_41, x_42, x_7, x_8, x_9, x_10, x_40);
lean_dec(x_7);
return x_43;
}
else
{
uint8_t x_44; 
lean_dec(x_38);
lean_dec(x_7);
x_44 = !lean_is_exclusive(x_37);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_37, 0);
lean_dec(x_45);
x_46 = lean_ctor_get(x_39, 0);
lean_inc(x_46);
lean_dec(x_39);
lean_ctor_set(x_37, 0, x_46);
return x_37;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_37, 1);
lean_inc(x_47);
lean_dec(x_37);
x_48 = lean_ctor_get(x_39, 0);
lean_inc(x_48);
lean_dec(x_39);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_47);
return x_49;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_getFVarSetToGeneralize___spec__76(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = lean_usize_dec_lt(x_7, x_6);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_4);
lean_dec(x_3);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_8);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_16 = lean_array_uget(x_5, x_7);
x_25 = lean_ctor_get(x_8, 1);
lean_inc(x_25);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_26 = x_8;
} else {
 lean_dec_ref(x_8);
 x_26 = lean_box(0);
}
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_44; size_t x_45; size_t x_46; 
lean_dec(x_26);
lean_inc(x_4);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_4);
lean_ctor_set(x_44, 1, x_25);
x_45 = 1;
x_46 = lean_usize_add(x_7, x_45);
x_7 = x_46;
x_8 = x_44;
goto _start;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_186; 
x_48 = lean_ctor_get(x_16, 0);
lean_inc(x_48);
lean_dec(x_16);
x_49 = lean_ctor_get(x_25, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_25, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_51 = x_25;
} else {
 lean_dec_ref(x_25);
 x_51 = lean_box(0);
}
x_52 = l_Lean_LocalDecl_fvarId(x_48);
x_186 = l_Std_RBNode_findCore___at_Lean_Meta_mkGeneralizationForbiddenSet_visit___spec__1(x_1, x_52);
if (lean_obj_tag(x_186) == 0)
{
uint8_t x_187; 
x_187 = l_Lean_LocalDecl_isAuxDecl(x_48);
if (x_187 == 0)
{
uint8_t x_188; uint8_t x_189; 
x_188 = l_Lean_LocalDecl_binderInfo(x_48);
x_189 = l_Lean_BinderInfo_isInstImplicit(x_188);
if (x_189 == 0)
{
if (x_2 == 0)
{
lean_object* x_190; 
x_190 = lean_box(0);
x_53 = x_190;
goto block_185;
}
else
{
uint8_t x_191; 
x_191 = l_Lean_LocalDecl_isLet(x_48);
if (x_191 == 0)
{
lean_object* x_192; 
x_192 = lean_box(0);
x_53 = x_192;
goto block_185;
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; 
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_48);
x_193 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_193, 0, x_49);
lean_ctor_set(x_193, 1, x_50);
x_194 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_194, 0, x_193);
x_195 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_195, 0, x_194);
lean_ctor_set(x_195, 1, x_13);
x_27 = x_195;
goto block_43;
}
}
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; 
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_48);
x_196 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_196, 0, x_49);
lean_ctor_set(x_196, 1, x_50);
x_197 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_197, 0, x_196);
x_198 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_198, 0, x_197);
lean_ctor_set(x_198, 1, x_13);
x_27 = x_198;
goto block_43;
}
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; 
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_48);
x_199 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_199, 0, x_49);
lean_ctor_set(x_199, 1, x_50);
x_200 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_200, 0, x_199);
x_201 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_201, 0, x_200);
lean_ctor_set(x_201, 1, x_13);
x_27 = x_201;
goto block_43;
}
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; 
lean_dec(x_186);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_48);
x_202 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_202, 0, x_49);
lean_ctor_set(x_202, 1, x_50);
x_203 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_203, 0, x_202);
x_204 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_204, 0, x_203);
lean_ctor_set(x_204, 1, x_13);
x_27 = x_204;
goto block_43;
}
block_185:
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; lean_object* x_60; lean_object* x_105; uint8_t x_106; lean_object* x_107; 
lean_dec(x_53);
x_54 = lean_st_ref_get(x_12, x_13);
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
lean_dec(x_54);
x_56 = lean_st_ref_take(x_10, x_55);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_105 = lean_ctor_get(x_57, 0);
lean_inc(x_105);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; uint8_t x_145; 
x_142 = lean_ctor_get(x_48, 3);
lean_inc(x_142);
lean_dec(x_48);
x_143 = l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1;
lean_inc(x_105);
x_144 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set(x_144, 1, x_105);
x_145 = l_Lean_Expr_hasFVar(x_142);
if (x_145 == 0)
{
uint8_t x_146; 
x_146 = l_Lean_Expr_hasMVar(x_142);
if (x_146 == 0)
{
uint8_t x_147; 
lean_dec(x_142);
x_147 = 0;
x_106 = x_147;
x_107 = x_144;
goto block_141;
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; uint8_t x_151; 
lean_inc(x_50);
x_148 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__1___at_Lean_Meta_getFVarSetToGeneralize___spec__9(x_50, x_142, x_144);
x_149 = lean_ctor_get(x_148, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_148, 1);
lean_inc(x_150);
lean_dec(x_148);
x_151 = lean_unbox(x_149);
lean_dec(x_149);
x_106 = x_151;
x_107 = x_150;
goto block_141;
}
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; uint8_t x_155; 
lean_inc(x_50);
x_152 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__12___at_Lean_Meta_getFVarSetToGeneralize___spec__20(x_50, x_142, x_144);
x_153 = lean_ctor_get(x_152, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_152, 1);
lean_inc(x_154);
lean_dec(x_152);
x_155 = lean_unbox(x_153);
lean_dec(x_153);
x_106 = x_155;
x_107 = x_154;
goto block_141;
}
}
else
{
lean_object* x_156; lean_object* x_157; uint8_t x_158; lean_object* x_159; lean_object* x_172; lean_object* x_173; uint8_t x_174; 
x_156 = lean_ctor_get(x_48, 3);
lean_inc(x_156);
x_157 = lean_ctor_get(x_48, 4);
lean_inc(x_157);
lean_dec(x_48);
x_172 = l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1;
lean_inc(x_105);
x_173 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_173, 0, x_172);
lean_ctor_set(x_173, 1, x_105);
x_174 = l_Lean_Expr_hasFVar(x_156);
if (x_174 == 0)
{
uint8_t x_175; 
x_175 = l_Lean_Expr_hasMVar(x_156);
if (x_175 == 0)
{
uint8_t x_176; 
lean_dec(x_156);
x_176 = 0;
x_158 = x_176;
x_159 = x_173;
goto block_171;
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; uint8_t x_180; 
lean_inc(x_50);
x_177 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__39___at_Lean_Meta_getFVarSetToGeneralize___spec__47(x_50, x_156, x_173);
x_178 = lean_ctor_get(x_177, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_177, 1);
lean_inc(x_179);
lean_dec(x_177);
x_180 = lean_unbox(x_178);
lean_dec(x_178);
x_158 = x_180;
x_159 = x_179;
goto block_171;
}
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; uint8_t x_184; 
lean_inc(x_50);
x_181 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__50___at_Lean_Meta_getFVarSetToGeneralize___spec__58(x_50, x_156, x_173);
x_182 = lean_ctor_get(x_181, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_181, 1);
lean_inc(x_183);
lean_dec(x_181);
x_184 = lean_unbox(x_182);
lean_dec(x_182);
x_158 = x_184;
x_159 = x_183;
goto block_171;
}
block_171:
{
if (x_158 == 0)
{
uint8_t x_160; 
x_160 = l_Lean_Expr_hasFVar(x_157);
if (x_160 == 0)
{
uint8_t x_161; 
x_161 = l_Lean_Expr_hasMVar(x_157);
if (x_161 == 0)
{
uint8_t x_162; 
lean_dec(x_157);
x_162 = 0;
x_106 = x_162;
x_107 = x_159;
goto block_141;
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; uint8_t x_166; 
lean_inc(x_50);
lean_inc(x_3);
x_163 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__23(x_3, x_50, x_157, x_159);
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_163, 1);
lean_inc(x_165);
lean_dec(x_163);
x_166 = lean_unbox(x_164);
lean_dec(x_164);
x_106 = x_166;
x_107 = x_165;
goto block_141;
}
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; uint8_t x_170; 
lean_inc(x_50);
lean_inc(x_3);
x_167 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__31(x_3, x_50, x_157, x_159);
x_168 = lean_ctor_get(x_167, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_167, 1);
lean_inc(x_169);
lean_dec(x_167);
x_170 = lean_unbox(x_168);
lean_dec(x_168);
x_106 = x_170;
x_107 = x_169;
goto block_141;
}
}
else
{
lean_dec(x_157);
x_106 = x_158;
x_107 = x_159;
goto block_141;
}
}
}
block_104:
{
uint8_t x_61; 
x_61 = !lean_is_exclusive(x_57);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_57, 0);
lean_dec(x_62);
lean_ctor_set(x_57, 0, x_60);
x_63 = lean_st_ref_set(x_10, x_57, x_58);
if (x_59 == 0)
{
uint8_t x_64; 
lean_dec(x_52);
x_64 = !lean_is_exclusive(x_63);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_63, 0);
lean_dec(x_65);
if (lean_is_scalar(x_51)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_51;
}
lean_ctor_set(x_66, 0, x_49);
lean_ctor_set(x_66, 1, x_50);
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_63, 0, x_67);
x_27 = x_63;
goto block_43;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_68 = lean_ctor_get(x_63, 1);
lean_inc(x_68);
lean_dec(x_63);
if (lean_is_scalar(x_51)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_51;
}
lean_ctor_set(x_69, 0, x_49);
lean_ctor_set(x_69, 1, x_50);
x_70 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_70, 0, x_69);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_68);
x_27 = x_71;
goto block_43;
}
}
else
{
uint8_t x_72; 
x_72 = !lean_is_exclusive(x_63);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_73 = lean_ctor_get(x_63, 0);
lean_dec(x_73);
x_74 = lean_box(0);
lean_inc(x_52);
x_75 = l_Std_RBNode_insert___at_Lean_CollectFVars_State_add___spec__1(x_49, x_52, x_74);
x_76 = l_Std_RBNode_insert___at_Lean_CollectFVars_State_add___spec__1(x_50, x_52, x_74);
if (lean_is_scalar(x_51)) {
 x_77 = lean_alloc_ctor(0, 2, 0);
} else {
 x_77 = x_51;
}
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
x_78 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_63, 0, x_78);
x_27 = x_63;
goto block_43;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_79 = lean_ctor_get(x_63, 1);
lean_inc(x_79);
lean_dec(x_63);
x_80 = lean_box(0);
lean_inc(x_52);
x_81 = l_Std_RBNode_insert___at_Lean_CollectFVars_State_add___spec__1(x_49, x_52, x_80);
x_82 = l_Std_RBNode_insert___at_Lean_CollectFVars_State_add___spec__1(x_50, x_52, x_80);
if (lean_is_scalar(x_51)) {
 x_83 = lean_alloc_ctor(0, 2, 0);
} else {
 x_83 = x_51;
}
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
x_84 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_84, 0, x_83);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_79);
x_27 = x_85;
goto block_43;
}
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_86 = lean_ctor_get(x_57, 1);
x_87 = lean_ctor_get(x_57, 2);
x_88 = lean_ctor_get(x_57, 3);
lean_inc(x_88);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_57);
x_89 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_89, 0, x_60);
lean_ctor_set(x_89, 1, x_86);
lean_ctor_set(x_89, 2, x_87);
lean_ctor_set(x_89, 3, x_88);
x_90 = lean_st_ref_set(x_10, x_89, x_58);
if (x_59 == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_52);
x_91 = lean_ctor_get(x_90, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_92 = x_90;
} else {
 lean_dec_ref(x_90);
 x_92 = lean_box(0);
}
if (lean_is_scalar(x_51)) {
 x_93 = lean_alloc_ctor(0, 2, 0);
} else {
 x_93 = x_51;
}
lean_ctor_set(x_93, 0, x_49);
lean_ctor_set(x_93, 1, x_50);
x_94 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_94, 0, x_93);
if (lean_is_scalar(x_92)) {
 x_95 = lean_alloc_ctor(0, 2, 0);
} else {
 x_95 = x_92;
}
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_91);
x_27 = x_95;
goto block_43;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_96 = lean_ctor_get(x_90, 1);
lean_inc(x_96);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_97 = x_90;
} else {
 lean_dec_ref(x_90);
 x_97 = lean_box(0);
}
x_98 = lean_box(0);
lean_inc(x_52);
x_99 = l_Std_RBNode_insert___at_Lean_CollectFVars_State_add___spec__1(x_49, x_52, x_98);
x_100 = l_Std_RBNode_insert___at_Lean_CollectFVars_State_add___spec__1(x_50, x_52, x_98);
if (lean_is_scalar(x_51)) {
 x_101 = lean_alloc_ctor(0, 2, 0);
} else {
 x_101 = x_51;
}
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
x_102 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_102, 0, x_101);
if (lean_is_scalar(x_97)) {
 x_103 = lean_alloc_ctor(0, 2, 0);
} else {
 x_103 = x_97;
}
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_96);
x_27 = x_103;
goto block_43;
}
}
}
block_141:
{
lean_object* x_108; uint8_t x_109; 
x_108 = lean_ctor_get(x_107, 1);
lean_inc(x_108);
lean_dec(x_107);
x_109 = lean_ctor_get_uint8(x_108, sizeof(void*)*8);
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; uint8_t x_118; 
x_110 = lean_ctor_get(x_108, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_108, 1);
lean_inc(x_111);
x_112 = lean_ctor_get(x_108, 2);
lean_inc(x_112);
x_113 = lean_ctor_get(x_108, 3);
lean_inc(x_113);
x_114 = lean_ctor_get(x_108, 4);
lean_inc(x_114);
x_115 = lean_ctor_get(x_108, 5);
lean_inc(x_115);
x_116 = lean_ctor_get(x_108, 6);
lean_inc(x_116);
x_117 = lean_ctor_get(x_108, 7);
lean_inc(x_117);
lean_dec(x_108);
x_118 = !lean_is_exclusive(x_105);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_119 = lean_ctor_get(x_105, 7);
lean_dec(x_119);
x_120 = lean_ctor_get(x_105, 6);
lean_dec(x_120);
x_121 = lean_ctor_get(x_105, 5);
lean_dec(x_121);
x_122 = lean_ctor_get(x_105, 4);
lean_dec(x_122);
x_123 = lean_ctor_get(x_105, 3);
lean_dec(x_123);
x_124 = lean_ctor_get(x_105, 2);
lean_dec(x_124);
x_125 = lean_ctor_get(x_105, 1);
lean_dec(x_125);
x_126 = lean_ctor_get(x_105, 0);
lean_dec(x_126);
lean_ctor_set(x_105, 7, x_117);
lean_ctor_set(x_105, 6, x_116);
lean_ctor_set(x_105, 5, x_115);
lean_ctor_set(x_105, 4, x_114);
lean_ctor_set(x_105, 3, x_113);
lean_ctor_set(x_105, 2, x_112);
lean_ctor_set(x_105, 1, x_111);
lean_ctor_set(x_105, 0, x_110);
x_59 = x_106;
x_60 = x_105;
goto block_104;
}
else
{
uint8_t x_127; lean_object* x_128; 
x_127 = lean_ctor_get_uint8(x_105, sizeof(void*)*8);
lean_dec(x_105);
x_128 = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(x_128, 0, x_110);
lean_ctor_set(x_128, 1, x_111);
lean_ctor_set(x_128, 2, x_112);
lean_ctor_set(x_128, 3, x_113);
lean_ctor_set(x_128, 4, x_114);
lean_ctor_set(x_128, 5, x_115);
lean_ctor_set(x_128, 6, x_116);
lean_ctor_set(x_128, 7, x_117);
lean_ctor_set_uint8(x_128, sizeof(void*)*8, x_127);
x_59 = x_106;
x_60 = x_128;
goto block_104;
}
}
else
{
uint8_t x_129; 
lean_dec(x_105);
x_129 = !lean_is_exclusive(x_108);
if (x_129 == 0)
{
uint8_t x_130; 
x_130 = 1;
lean_ctor_set_uint8(x_108, sizeof(void*)*8, x_130);
x_59 = x_106;
x_60 = x_108;
goto block_104;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; uint8_t x_139; lean_object* x_140; 
x_131 = lean_ctor_get(x_108, 0);
x_132 = lean_ctor_get(x_108, 1);
x_133 = lean_ctor_get(x_108, 2);
x_134 = lean_ctor_get(x_108, 3);
x_135 = lean_ctor_get(x_108, 4);
x_136 = lean_ctor_get(x_108, 5);
x_137 = lean_ctor_get(x_108, 6);
x_138 = lean_ctor_get(x_108, 7);
lean_inc(x_138);
lean_inc(x_137);
lean_inc(x_136);
lean_inc(x_135);
lean_inc(x_134);
lean_inc(x_133);
lean_inc(x_132);
lean_inc(x_131);
lean_dec(x_108);
x_139 = 1;
x_140 = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(x_140, 0, x_131);
lean_ctor_set(x_140, 1, x_132);
lean_ctor_set(x_140, 2, x_133);
lean_ctor_set(x_140, 3, x_134);
lean_ctor_set(x_140, 4, x_135);
lean_ctor_set(x_140, 5, x_136);
lean_ctor_set(x_140, 6, x_137);
lean_ctor_set(x_140, 7, x_138);
lean_ctor_set_uint8(x_140, sizeof(void*)*8, x_139);
x_59 = x_106;
x_60 = x_140;
goto block_104;
}
}
}
}
}
block_24:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec(x_18);
x_21 = 1;
x_22 = lean_usize_add(x_7, x_21);
x_7 = x_22;
x_8 = x_20;
x_13 = x_19;
goto _start;
}
block_43:
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_29, 0);
lean_inc(x_4);
if (lean_is_scalar(x_26)) {
 x_32 = lean_alloc_ctor(0, 2, 0);
} else {
 x_32 = x_26;
}
lean_ctor_set(x_32, 0, x_4);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set(x_29, 0, x_32);
x_17 = x_27;
goto block_24;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_29, 0);
lean_inc(x_33);
lean_dec(x_29);
lean_inc(x_4);
if (lean_is_scalar(x_26)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_26;
}
lean_ctor_set(x_34, 0, x_4);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_27, 0, x_35);
x_17 = x_27;
goto block_24;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_36 = lean_ctor_get(x_27, 0);
x_37 = lean_ctor_get(x_27, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_27);
x_38 = lean_ctor_get(x_36, 0);
lean_inc(x_38);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 x_39 = x_36;
} else {
 lean_dec_ref(x_36);
 x_39 = lean_box(0);
}
lean_inc(x_4);
if (lean_is_scalar(x_26)) {
 x_40 = lean_alloc_ctor(0, 2, 0);
} else {
 x_40 = x_26;
}
lean_ctor_set(x_40, 0, x_4);
lean_ctor_set(x_40, 1, x_38);
if (lean_is_scalar(x_39)) {
 x_41 = lean_alloc_ctor(1, 1, 0);
} else {
 x_41 = x_39;
}
lean_ctor_set(x_41, 0, x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_37);
x_17 = x_42;
goto block_24;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentArray_forIn___at_Lean_Meta_getFVarSetToGeneralize___spec__72(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_1);
x_12 = l_Std_PersistentArray_forInAux___at_Lean_Meta_getFVarSetToGeneralize___spec__73(x_1, x_2, x_3, x_5, x_11, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_12, 0);
lean_dec(x_15);
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_16);
lean_dec(x_13);
lean_ctor_set(x_12, 0, x_16);
return x_12;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_dec(x_12);
x_18 = lean_ctor_get(x_13, 0);
lean_inc(x_18);
lean_dec(x_13);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; size_t x_26; size_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_20 = lean_ctor_get(x_12, 1);
lean_inc(x_20);
lean_dec(x_12);
x_21 = lean_ctor_get(x_13, 0);
lean_inc(x_21);
lean_dec(x_13);
x_22 = lean_ctor_get(x_4, 1);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_21);
x_25 = lean_array_get_size(x_22);
x_26 = lean_usize_of_nat(x_25);
lean_dec(x_25);
x_27 = 0;
x_28 = l_Array_forInUnsafe_loop___at_Lean_Meta_getFVarSetToGeneralize___spec__76(x_1, x_2, x_3, x_23, x_22, x_26, x_27, x_24, x_6, x_7, x_8, x_9, x_20);
lean_dec(x_6);
lean_dec(x_1);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_28);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_28, 0);
lean_dec(x_32);
x_33 = lean_ctor_get(x_29, 1);
lean_inc(x_33);
lean_dec(x_29);
lean_ctor_set(x_28, 0, x_33);
return x_28;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_28, 1);
lean_inc(x_34);
lean_dec(x_28);
x_35 = lean_ctor_get(x_29, 1);
lean_inc(x_35);
lean_dec(x_29);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
return x_36;
}
}
else
{
uint8_t x_37; 
lean_dec(x_29);
x_37 = !lean_is_exclusive(x_28);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_28, 0);
lean_dec(x_38);
x_39 = lean_ctor_get(x_30, 0);
lean_inc(x_39);
lean_dec(x_30);
lean_ctor_set(x_28, 0, x_39);
return x_28;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_28, 1);
lean_inc(x_40);
lean_dec(x_28);
x_41 = lean_ctor_get(x_30, 0);
lean_inc(x_41);
lean_dec(x_30);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
return x_42;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_getFVarSetToGeneralize___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFVarSetToGeneralize(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_box(0);
x_10 = lean_array_get_size(x_1);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_nat_dec_lt(x_11, x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
lean_dec(x_10);
x_13 = lean_ctor_get(x_4, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at_Lean_Meta_getFVarSetToGeneralize___spec__2___at_Lean_Meta_getFVarSetToGeneralize___spec__10___closed__1;
x_16 = l_Lean_Meta_getFVarSetToGeneralize___closed__1;
x_17 = l_Std_PersistentArray_forIn___at_Lean_Meta_getFVarSetToGeneralize___spec__61(x_2, x_3, x_15, x_14, x_16, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_14);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec(x_19);
lean_ctor_set(x_17, 0, x_20);
return x_17;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_17, 0);
x_22 = lean_ctor_get(x_17, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_17);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_25 = lean_ctor_get(x_4, 1);
lean_inc(x_25);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_nat_dec_le(x_10, x_10);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
lean_dec(x_10);
x_28 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at_Lean_Meta_getFVarSetToGeneralize___spec__2___at_Lean_Meta_getFVarSetToGeneralize___spec__10___closed__1;
x_29 = l_Lean_Meta_getFVarSetToGeneralize___closed__1;
x_30 = l_Std_PersistentArray_forIn___at_Lean_Meta_getFVarSetToGeneralize___spec__66(x_2, x_3, x_28, x_26, x_29, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_26);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_30, 0);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
lean_dec(x_32);
lean_ctor_set(x_30, 0, x_33);
return x_30;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_30, 0);
x_35 = lean_ctor_get(x_30, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_30);
x_36 = lean_ctor_get(x_34, 0);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
else
{
size_t x_38; size_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_38 = 0;
x_39 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_40 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_getFVarSetToGeneralize___spec__71(x_1, x_38, x_39, x_9);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_9);
lean_ctor_set(x_41, 1, x_40);
x_42 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at_Lean_Meta_getFVarSetToGeneralize___spec__2___at_Lean_Meta_getFVarSetToGeneralize___spec__10___closed__1;
x_43 = l_Std_PersistentArray_forIn___at_Lean_Meta_getFVarSetToGeneralize___spec__72(x_2, x_3, x_42, x_26, x_41, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_26);
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_43, 0);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
lean_dec(x_45);
lean_ctor_set(x_43, 0, x_46);
return x_43;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_47 = lean_ctor_get(x_43, 0);
x_48 = lean_ctor_get(x_43, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_43);
x_49 = lean_ctor_get(x_47, 0);
lean_inc(x_49);
lean_dec(x_47);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_48);
return x_50;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; uint8_t x_8; lean_object* x_9; 
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_8 = l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__6(x_1, x_2, x_3, x_6, x_7);
lean_dec(x_3);
x_9 = lean_box(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; uint8_t x_8; lean_object* x_9; 
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_8 = l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__7(x_1, x_2, x_3, x_6, x_7);
lean_dec(x_3);
x_9 = lean_box(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentArray_anyMAux___at_Lean_Meta_getFVarSetToGeneralize___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_PersistentArray_anyMAux___at_Lean_Meta_getFVarSetToGeneralize___spec__5(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; uint8_t x_8; lean_object* x_9; 
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_8 = l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__8(x_1, x_2, x_3, x_6, x_7);
lean_dec(x_3);
x_9 = lean_box(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__4(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__17___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; uint8_t x_8; lean_object* x_9; 
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_8 = l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__17(x_1, x_2, x_3, x_6, x_7);
lean_dec(x_3);
x_9 = lean_box(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__18___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; uint8_t x_8; lean_object* x_9; 
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_8 = l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__18(x_1, x_2, x_3, x_6, x_7);
lean_dec(x_3);
x_9 = lean_box(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentArray_anyMAux___at_Lean_Meta_getFVarSetToGeneralize___spec__16___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_PersistentArray_anyMAux___at_Lean_Meta_getFVarSetToGeneralize___spec__16(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__19___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; uint8_t x_8; lean_object* x_9; 
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_8 = l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__19(x_1, x_2, x_3, x_6, x_7);
lean_dec(x_3);
x_9 = lean_box(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__15___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__15(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__28___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; uint8_t x_8; lean_object* x_9; 
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_8 = l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__28(x_1, x_2, x_3, x_6, x_7);
lean_dec(x_3);
x_9 = lean_box(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__29___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; uint8_t x_8; lean_object* x_9; 
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_8 = l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__29(x_1, x_2, x_3, x_6, x_7);
lean_dec(x_3);
x_9 = lean_box(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentArray_anyMAux___at_Lean_Meta_getFVarSetToGeneralize___spec__27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_PersistentArray_anyMAux___at_Lean_Meta_getFVarSetToGeneralize___spec__27(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__30___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; uint8_t x_8; lean_object* x_9; 
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_8 = l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__30(x_1, x_2, x_3, x_6, x_7);
lean_dec(x_3);
x_9 = lean_box(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__26___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__26(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__36___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; uint8_t x_8; lean_object* x_9; 
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_8 = l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__36(x_1, x_2, x_3, x_6, x_7);
lean_dec(x_3);
x_9 = lean_box(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__37___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; uint8_t x_8; lean_object* x_9; 
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_8 = l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__37(x_1, x_2, x_3, x_6, x_7);
lean_dec(x_3);
x_9 = lean_box(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentArray_anyMAux___at_Lean_Meta_getFVarSetToGeneralize___spec__35___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_PersistentArray_anyMAux___at_Lean_Meta_getFVarSetToGeneralize___spec__35(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__38___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; uint8_t x_8; lean_object* x_9; 
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_8 = l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__38(x_1, x_2, x_3, x_6, x_7);
lean_dec(x_3);
x_9 = lean_box(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__34___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__34(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__44___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; uint8_t x_8; lean_object* x_9; 
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_8 = l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__44(x_1, x_2, x_3, x_6, x_7);
lean_dec(x_3);
x_9 = lean_box(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__45___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; uint8_t x_8; lean_object* x_9; 
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_8 = l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__45(x_1, x_2, x_3, x_6, x_7);
lean_dec(x_3);
x_9 = lean_box(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentArray_anyMAux___at_Lean_Meta_getFVarSetToGeneralize___spec__43___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_PersistentArray_anyMAux___at_Lean_Meta_getFVarSetToGeneralize___spec__43(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__46___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; uint8_t x_8; lean_object* x_9; 
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_8 = l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__46(x_1, x_2, x_3, x_6, x_7);
lean_dec(x_3);
x_9 = lean_box(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__42___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__42(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__55___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; uint8_t x_8; lean_object* x_9; 
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_8 = l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__55(x_1, x_2, x_3, x_6, x_7);
lean_dec(x_3);
x_9 = lean_box(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__56___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; uint8_t x_8; lean_object* x_9; 
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_8 = l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__56(x_1, x_2, x_3, x_6, x_7);
lean_dec(x_3);
x_9 = lean_box(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentArray_anyMAux___at_Lean_Meta_getFVarSetToGeneralize___spec__54___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_PersistentArray_anyMAux___at_Lean_Meta_getFVarSetToGeneralize___spec__54(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__57___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; uint8_t x_8; lean_object* x_9; 
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_8 = l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__57(x_1, x_2, x_3, x_6, x_7);
lean_dec(x_3);
x_9 = lean_box(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__53___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__53(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_getFVarSetToGeneralize___spec__63___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; size_t x_16; size_t x_17; lean_object* x_18; 
x_15 = lean_unbox(x_2);
lean_dec(x_2);
x_16 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_17 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_18 = l_Array_forInUnsafe_loop___at_Lean_Meta_getFVarSetToGeneralize___spec__63(x_1, x_15, x_3, x_4, x_5, x_6, x_16, x_17, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_4);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_getFVarSetToGeneralize___spec__64___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; size_t x_15; size_t x_16; lean_object* x_17; 
x_14 = lean_unbox(x_2);
lean_dec(x_2);
x_15 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_16 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_17 = l_Array_forInUnsafe_loop___at_Lean_Meta_getFVarSetToGeneralize___spec__64(x_1, x_14, x_3, x_4, x_5, x_15, x_16, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_1);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentArray_forInAux___at_Lean_Meta_getFVarSetToGeneralize___spec__62___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_PersistentArray_forInAux___at_Lean_Meta_getFVarSetToGeneralize___spec__62___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentArray_forInAux___at_Lean_Meta_getFVarSetToGeneralize___spec__62___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_2);
lean_dec(x_2);
x_13 = l_Std_PersistentArray_forInAux___at_Lean_Meta_getFVarSetToGeneralize___spec__62(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_getFVarSetToGeneralize___spec__65___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; size_t x_15; size_t x_16; lean_object* x_17; 
x_14 = lean_unbox(x_2);
lean_dec(x_2);
x_15 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_16 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_17 = l_Array_forInUnsafe_loop___at_Lean_Meta_getFVarSetToGeneralize___spec__65(x_1, x_14, x_3, x_4, x_5, x_15, x_16, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_1);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentArray_forIn___at_Lean_Meta_getFVarSetToGeneralize___spec__61___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_PersistentArray_forIn___at_Lean_Meta_getFVarSetToGeneralize___spec__61___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentArray_forIn___at_Lean_Meta_getFVarSetToGeneralize___spec__61___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_2);
lean_dec(x_2);
x_12 = l_Std_PersistentArray_forIn___at_Lean_Meta_getFVarSetToGeneralize___spec__61(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_getFVarSetToGeneralize___spec__68___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; size_t x_16; size_t x_17; lean_object* x_18; 
x_15 = lean_unbox(x_2);
lean_dec(x_2);
x_16 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_17 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_18 = l_Array_forInUnsafe_loop___at_Lean_Meta_getFVarSetToGeneralize___spec__68(x_1, x_15, x_3, x_4, x_5, x_6, x_16, x_17, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_4);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_getFVarSetToGeneralize___spec__69___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; size_t x_15; size_t x_16; lean_object* x_17; 
x_14 = lean_unbox(x_2);
lean_dec(x_2);
x_15 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_16 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_17 = l_Array_forInUnsafe_loop___at_Lean_Meta_getFVarSetToGeneralize___spec__69(x_1, x_14, x_3, x_4, x_5, x_15, x_16, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_1);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentArray_forInAux___at_Lean_Meta_getFVarSetToGeneralize___spec__67___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_2);
lean_dec(x_2);
x_13 = l_Std_PersistentArray_forInAux___at_Lean_Meta_getFVarSetToGeneralize___spec__67(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_getFVarSetToGeneralize___spec__70___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; size_t x_15; size_t x_16; lean_object* x_17; 
x_14 = lean_unbox(x_2);
lean_dec(x_2);
x_15 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_16 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_17 = l_Array_forInUnsafe_loop___at_Lean_Meta_getFVarSetToGeneralize___spec__70(x_1, x_14, x_3, x_4, x_5, x_15, x_16, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_1);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentArray_forIn___at_Lean_Meta_getFVarSetToGeneralize___spec__66___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_2);
lean_dec(x_2);
x_12 = l_Std_PersistentArray_forIn___at_Lean_Meta_getFVarSetToGeneralize___spec__66(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_getFVarSetToGeneralize___spec__71___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_getFVarSetToGeneralize___spec__71(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_getFVarSetToGeneralize___spec__74___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; size_t x_16; size_t x_17; lean_object* x_18; 
x_15 = lean_unbox(x_2);
lean_dec(x_2);
x_16 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_17 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_18 = l_Array_forInUnsafe_loop___at_Lean_Meta_getFVarSetToGeneralize___spec__74(x_1, x_15, x_3, x_4, x_5, x_6, x_16, x_17, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_4);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_getFVarSetToGeneralize___spec__75___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; size_t x_15; size_t x_16; lean_object* x_17; 
x_14 = lean_unbox(x_2);
lean_dec(x_2);
x_15 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_16 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_17 = l_Array_forInUnsafe_loop___at_Lean_Meta_getFVarSetToGeneralize___spec__75(x_1, x_14, x_3, x_4, x_5, x_15, x_16, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_1);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentArray_forInAux___at_Lean_Meta_getFVarSetToGeneralize___spec__73___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_2);
lean_dec(x_2);
x_13 = l_Std_PersistentArray_forInAux___at_Lean_Meta_getFVarSetToGeneralize___spec__73(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_getFVarSetToGeneralize___spec__76___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; size_t x_15; size_t x_16; lean_object* x_17; 
x_14 = lean_unbox(x_2);
lean_dec(x_2);
x_15 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_16 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_17 = l_Array_forInUnsafe_loop___at_Lean_Meta_getFVarSetToGeneralize___spec__76(x_1, x_14, x_3, x_4, x_5, x_15, x_16, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_1);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentArray_forIn___at_Lean_Meta_getFVarSetToGeneralize___spec__72___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_2);
lean_dec(x_2);
x_12 = l_Std_PersistentArray_forIn___at_Lean_Meta_getFVarSetToGeneralize___spec__72(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFVarSetToGeneralize___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = l_Lean_Meta_getFVarSetToGeneralize(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_fold___at_Lean_Meta_getFVarsToGeneralize___spec__2(lean_object* x_1, lean_object* x_2) {
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
x_6 = l_Std_RBNode_fold___at_Lean_Meta_getFVarsToGeneralize___spec__2(x_1, x_3);
x_7 = lean_array_push(x_6, x_4);
x_1 = x_7;
x_2 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_RBTree_toArray___at_Lean_Meta_getFVarsToGeneralize___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__2;
x_3 = l_Std_RBNode_fold___at_Lean_Meta_getFVarsToGeneralize___spec__2(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFVarsToGeneralize(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_9 = l_Lean_Meta_mkGeneralizationForbiddenSet(x_1, x_2, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_4);
x_12 = l_Lean_Meta_getFVarSetToGeneralize(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Std_RBTree_toArray___at_Lean_Meta_getFVarsToGeneralize___spec__1(x_13);
x_16 = l_Lean_Meta_sortFVarIds(x_15, x_4, x_5, x_6, x_7, x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_16;
}
else
{
uint8_t x_17; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_17 = !lean_is_exclusive(x_9);
if (x_17 == 0)
{
return x_9;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_9, 0);
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_9);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFVarsToGeneralize___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = l_Lean_Meta_getFVarsToGeneralize(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
return x_10;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_CollectFVars(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_GeneralizeVars(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_CollectFVars(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1 = _init_l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1();
lean_mark_persistent(l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1);
l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__2 = _init_l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__2();
lean_mark_persistent(l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__2);
l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__3 = _init_l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__3();
lean_mark_persistent(l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__3);
l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at_Lean_Meta_getFVarSetToGeneralize___spec__2___at_Lean_Meta_getFVarSetToGeneralize___spec__10___closed__1 = _init_l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at_Lean_Meta_getFVarSetToGeneralize___spec__2___at_Lean_Meta_getFVarSetToGeneralize___spec__10___closed__1();
lean_mark_persistent(l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at_Lean_Meta_getFVarSetToGeneralize___spec__2___at_Lean_Meta_getFVarSetToGeneralize___spec__10___closed__1);
l_Lean_Meta_getFVarSetToGeneralize___closed__1 = _init_l_Lean_Meta_getFVarSetToGeneralize___closed__1();
lean_mark_persistent(l_Lean_Meta_getFVarSetToGeneralize___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
