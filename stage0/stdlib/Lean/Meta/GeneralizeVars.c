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
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at_Lean_Meta_getFVarSetToGeneralize___spec__3___at_Lean_Meta_getFVarSetToGeneralize___spec__11(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at_Lean_Meta_getFVarSetToGeneralize___spec__2___at_Lean_Meta_getFVarSetToGeneralize___spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at_Lean_Meta_getFVarSetToGeneralize___spec__16___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__6(lean_object*, lean_object*, lean_object*, size_t, size_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at_Lean_Meta_getFVarSetToGeneralize___spec__33(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__38(lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyMAux___at_Lean_Meta_getFVarSetToGeneralize___spec__5(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_shouldVisit(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__15___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__30(lean_object*, lean_object*, lean_object*, size_t, size_t);
lean_object* l_Lean_MetavarContext_getDecl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at_Lean_Meta_getFVarSetToGeneralize___spec__41___at_Lean_Meta_getFVarSetToGeneralize___spec__49(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at_Lean_Meta_getFVarSetToGeneralize___spec__14___at_Lean_Meta_getFVarSetToGeneralize___spec__22(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__45___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkGeneralizationForbiddenSet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__37___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__57(lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_mkGeneralizationForbiddenSet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_getFVarSetToGeneralize___spec__71(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at_Lean_Meta_getFVarSetToGeneralize___spec__51(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at_Lean_Meta_getFVarSetToGeneralize___spec__54___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__12___at_Lean_Meta_getFVarSetToGeneralize___spec__20(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__7(lean_object*, lean_object*, lean_object*, size_t, size_t);
lean_object* l_Lean_mkHashSetImp___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at_Lean_Meta_getFVarSetToGeneralize___spec__27___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_getFVarSetToGeneralize___spec__74___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getFVarsToGeneralize(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkGeneralizationForbiddenSet_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__57___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__26(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_getFVarSetToGeneralize___closed__1;
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyMAux___at_Lean_Meta_getFVarSetToGeneralize___spec__27(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at_Lean_Meta_getFVarSetToGeneralize___spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at_Lean_Meta_getFVarSetToGeneralize___spec__13___at_Lean_Meta_getFVarSetToGeneralize___spec__21(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___at_Lean_Meta_mkGeneralizationForbiddenSet_visit___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_getFVarSetToGeneralize___spec__65___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__12(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_Meta_getFVarSetToGeneralize___spec__61(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkGeneralizationForbiddenSet_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__39___at_Lean_Meta_getFVarSetToGeneralize___spec__47(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__28___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__15(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__1___at_Lean_Meta_getFVarSetToGeneralize___spec__9(lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_Meta_getFVarSetToGeneralize___spec__62___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at_Lean_Meta_getFVarSetToGeneralize___spec__2___at_Lean_Meta_getFVarSetToGeneralize___spec__10___closed__1;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_Meta_getFVarSetToGeneralize___spec__67___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__50(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_getFVarSetToGeneralize___spec__65(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__46(lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__42(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__3;
lean_object* l_Lean_instantiateMVars___at___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___spec__7(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__53(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__23(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_getFVarSetToGeneralize___spec__75___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__44(lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__34(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_getFVarSetToGeneralize___spec__75(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at_Lean_Meta_mkGeneralizationForbiddenSet_visit___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__2;
lean_object* l_Lean_Name_quickCmp___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_getFVarSetToGeneralize___spec__64___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__34___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__38___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__56___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at_Lean_Meta_getFVarSetToGeneralize___spec__24(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__29___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyMAux___at_Lean_Meta_getFVarSetToGeneralize___spec__54(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isMVar(lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__30___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at_Lean_Meta_mkGeneralizationForbiddenSet_visit___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at_Lean_Meta_getFVarSetToGeneralize___spec__14(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__36(lean_object*, lean_object*, lean_object*, size_t, size_t);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_getFVarSetToGeneralize___spec__70___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__50___at_Lean_Meta_getFVarSetToGeneralize___spec__58(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RBNode_findCore___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__53___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_Meta_getFVarSetToGeneralize___spec__72___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__18(lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_Meta_getFVarSetToGeneralize___spec__61___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_mkGeneralizationForbiddenSet___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_BinderInfo_isInstImplicit(uint8_t);
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at_Lean_Meta_mkGeneralizationForbiddenSet_visit___spec__2___at_Lean_Meta_mkGeneralizationForbiddenSet_visit___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_Meta_getFVarSetToGeneralize___spec__66(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at_Lean_Meta_getFVarSetToGeneralize___spec__41(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_getFVarSetToGeneralize___spec__68(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_Meta_getFVarSetToGeneralize___spec__62___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_getFVarSetToGeneralize___spec__69(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_isLet(lean_object*);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__46___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyMAux___at_Lean_Meta_getFVarSetToGeneralize___spec__16(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_isAuxDecl(lean_object*);
lean_object* l_Lean_CollectFVars_main(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_Meta_getFVarSetToGeneralize___spec__62___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__8(lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__55(lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkGeneralizationForbiddenSet_visit___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getFVarSetToGeneralize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__37(lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_Meta_getFVarSetToGeneralize___spec__61___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyMAux___at_Lean_Meta_getFVarSetToGeneralize___spec__35(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__36___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_getFVarSetToGeneralize___spec__68___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__31(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkGeneralizationForbiddenSet_visit___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at_Lean_Meta_getFVarSetToGeneralize___spec__51___at_Lean_Meta_getFVarSetToGeneralize___spec__59(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at_Lean_Meta_getFVarSetToGeneralize___spec__52(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_getFVarSetToGeneralize___spec__76___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_mkGeneralizationForbiddenSet___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__26___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at_Lean_Meta_getFVarsToGeneralize___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_Meta_getFVarSetToGeneralize___spec__62(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at_Lean_Meta_getFVarSetToGeneralize___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_Meta_getFVarSetToGeneralize___spec__66___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_getFVarSetToGeneralize___spec__74(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__29(lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_getFVarSetToGeneralize(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at_Lean_Meta_getFVarSetToGeneralize___spec__52___at_Lean_Meta_getFVarSetToGeneralize___spec__60(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_toArray___at_Lean_Meta_getFVarsToGeneralize___spec__1(lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__17(lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__19(lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__28(lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at_Lean_Meta_getFVarSetToGeneralize___spec__13(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__45(lean_object*, lean_object*, lean_object*, size_t, size_t);
uint8_t l_Lean_LocalDecl_binderInfo(lean_object*);
lean_object* l_Lean_RBNode_insert___at_Lean_FVarIdSet_insert___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_getFVarSetToGeneralize___spec__71___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__55___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_quickCmp(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_getFVarSetToGeneralize___spec__76(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getFVarsToGeneralize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_Meta_getFVarSetToGeneralize___spec__73___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___at_Lean_Meta_mkGeneralizationForbiddenSet_visit___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_getFVarSetToGeneralize___spec__69___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__44___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at_Lean_Meta_getFVarSetToGeneralize___spec__35___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_getFVarSetToGeneralize___spec__63___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_sortFVarIds(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at_Lean_Meta_getFVarSetToGeneralize___spec__25(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at_Lean_Meta_getFVarSetToGeneralize___spec__40(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_Meta_getFVarSetToGeneralize___spec__73(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_value_x3f(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_Meta_getFVarSetToGeneralize___spec__72(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__56(lean_object*, lean_object*, lean_object*, size_t, size_t);
lean_object* l_Lean_getExprMVarAssignment_x3f___at___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at_Lean_Meta_getFVarSetToGeneralize___spec__32(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__42___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_getFVarSetToGeneralize___spec__63(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at_Lean_Meta_mkGeneralizationForbiddenSet_visit___spec__2___at_Lean_Meta_mkGeneralizationForbiddenSet_visit___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at_Lean_Meta_getFVarSetToGeneralize___spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_Meta_getFVarSetToGeneralize___spec__67(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_Meta_getFVarSetToGeneralize___spec__61___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at_Lean_Meta_getFVarSetToGeneralize___spec__43___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_getFVarSetToGeneralize___spec__70(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyMAux___at_Lean_Meta_getFVarSetToGeneralize___spec__43(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_getFVarSetToGeneralize___spec__64(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__39(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at_Lean_Meta_getFVarSetToGeneralize___spec__40___at_Lean_Meta_getFVarSetToGeneralize___spec__48(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___at_Lean_Meta_mkGeneralizationForbiddenSet_visit___spec__1(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at_Lean_Meta_mkGeneralizationForbiddenSet_visit___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
x_14 = l_Lean_RBNode_forIn_visit___at_Lean_Meta_mkGeneralizationForbiddenSet_visit___spec__2(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8);
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
x_21 = l_Lean_RBNode_findCore___at_Lean_Meta_mkGeneralizationForbiddenSet_visit___spec__1(x_19, x_12);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_inc(x_12);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_12);
lean_ctor_set(x_22, 1, x_20);
x_23 = lean_box(0);
x_24 = l_Lean_RBNode_insert___at_Lean_FVarIdSet_insert___spec__1(x_19, x_12, x_23);
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
x_29 = l_Lean_RBNode_findCore___at_Lean_Meta_mkGeneralizationForbiddenSet_visit___spec__1(x_27, x_12);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_inc(x_12);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_12);
lean_ctor_set(x_30, 1, x_28);
x_31 = lean_box(0);
x_32 = l_Lean_RBNode_insert___at_Lean_FVarIdSet_insert___spec__1(x_27, x_12, x_31);
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
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at_Lean_Meta_mkGeneralizationForbiddenSet_visit___spec__2___at_Lean_Meta_mkGeneralizationForbiddenSet_visit___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_13 = l_Lean_RBNode_forIn_visit___at_Lean_Meta_mkGeneralizationForbiddenSet_visit___spec__2___at_Lean_Meta_mkGeneralizationForbiddenSet_visit___spec__3(x_10, x_2, x_3, x_4, x_5, x_6, x_7);
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
x_20 = l_Lean_RBNode_findCore___at_Lean_Meta_mkGeneralizationForbiddenSet_visit___spec__1(x_18, x_11);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_inc(x_11);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_11);
lean_ctor_set(x_21, 1, x_19);
x_22 = lean_box(0);
x_23 = l_Lean_RBNode_insert___at_Lean_FVarIdSet_insert___spec__1(x_18, x_11, x_22);
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
x_28 = l_Lean_RBNode_findCore___at_Lean_Meta_mkGeneralizationForbiddenSet_visit___spec__1(x_26, x_11);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_inc(x_11);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_11);
lean_ctor_set(x_29, 1, x_27);
x_30 = lean_box(0);
x_31 = l_Lean_RBNode_insert___at_Lean_FVarIdSet_insert___spec__1(x_26, x_11, x_30);
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
x_12 = l_Lean_RBNode_forIn_visit___at_Lean_Meta_mkGeneralizationForbiddenSet_visit___spec__2___at_Lean_Meta_mkGeneralizationForbiddenSet_visit___spec__3(x_10, x_11, x_5, x_6, x_7, x_8, x_9);
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
x_2 = l_Lean_mkHashSetImp___rarg(x_1);
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
x_9 = l_Lean_FVarId_getDecl(x_1, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_LocalDecl_type(x_10);
x_13 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_12, x_4, x_5, x_6, x_7, x_11);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__3;
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
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_21 = lean_ctor_get(x_18, 0);
lean_inc(x_21);
lean_dec(x_18);
x_22 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_21, x_4, x_5, x_6, x_7, x_15);
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
}
else
{
uint8_t x_28; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___at_Lean_Meta_mkGeneralizationForbiddenSet_visit___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBNode_findCore___at_Lean_Meta_mkGeneralizationForbiddenSet_visit___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at_Lean_Meta_mkGeneralizationForbiddenSet_visit___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_RBNode_forIn_visit___at_Lean_Meta_mkGeneralizationForbiddenSet_visit___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at_Lean_Meta_mkGeneralizationForbiddenSet_visit___spec__2___at_Lean_Meta_mkGeneralizationForbiddenSet_visit___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_RBNode_forIn_visit___at_Lean_Meta_mkGeneralizationForbiddenSet_visit___spec__2___at_Lean_Meta_mkGeneralizationForbiddenSet_visit___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
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
x_11 = l_Lean_RBNode_findCore___at_Lean_Meta_mkGeneralizationForbiddenSet_visit___spec__1(x_2, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_box(0);
lean_inc(x_9);
x_13 = l_Lean_RBNode_insert___at_Lean_FVarIdSet_insert___spec__1(x_2, x_9, x_12);
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
x_17 = lean_infer_type(x_12, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; size_t x_24; size_t x_25; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_18, x_5, x_6, x_7, x_8, x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_CollectFVars_main(x_21, x_14);
lean_ctor_set(x_4, 0, x_23);
x_24 = 1;
x_25 = lean_usize_add(x_3, x_24);
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
x_27 = !lean_is_exclusive(x_17);
if (x_27 == 0)
{
return x_17;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_17, 0);
x_29 = lean_ctor_get(x_17, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_17);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
else
{
lean_object* x_31; lean_object* x_32; size_t x_33; size_t x_34; 
x_31 = l_Lean_Expr_fvarId_x21(x_12);
x_32 = lean_array_push(x_15, x_31);
lean_ctor_set(x_4, 1, x_32);
x_33 = 1;
x_34 = lean_usize_add(x_3, x_33);
x_3 = x_34;
goto _start;
}
}
else
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_36 = lean_ctor_get(x_4, 0);
x_37 = lean_ctor_get(x_4, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_4);
x_38 = l_Lean_Expr_isFVar(x_12);
if (x_38 == 0)
{
lean_object* x_39; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_39 = lean_infer_type(x_12, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; size_t x_47; size_t x_48; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_40, x_5, x_6, x_7, x_8, x_41);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = l_Lean_CollectFVars_main(x_43, x_36);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_37);
x_47 = 1;
x_48 = lean_usize_add(x_3, x_47);
x_3 = x_48;
x_4 = x_46;
x_9 = x_44;
goto _start;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_50 = lean_ctor_get(x_39, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_39, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_52 = x_39;
} else {
 lean_dec_ref(x_39);
 x_52 = lean_box(0);
}
if (lean_is_scalar(x_52)) {
 x_53 = lean_alloc_ctor(1, 2, 0);
} else {
 x_53 = x_52;
}
lean_ctor_set(x_53, 0, x_50);
lean_ctor_set(x_53, 1, x_51);
return x_53;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; size_t x_57; size_t x_58; 
x_54 = l_Lean_Expr_fvarId_x21(x_12);
x_55 = lean_array_push(x_37, x_54);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_36);
lean_ctor_set(x_56, 1, x_55);
x_57 = 1;
x_58 = lean_usize_add(x_3, x_57);
x_3 = x_58;
x_4 = x_56;
goto _start;
}
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
x_8 = l_Lean_PersistentArray_anyMAux___at_Lean_Meta_getFVarSetToGeneralize___spec__5(x_1, x_2, x_7);
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
x_13 = l_Lean_RBNode_findCore___rarg(x_1, x_2, x_12);
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
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyMAux___at_Lean_Meta_getFVarSetToGeneralize___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
size_t x_9; size_t x_10; uint8_t x_11; 
x_9 = 0;
x_10 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_11 = l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__6(x_1, x_2, x_4, x_9, x_10);
lean_dec(x_4);
return x_11;
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_3, 0);
lean_inc(x_12);
lean_dec(x_3);
x_13 = lean_array_get_size(x_12);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_lt(x_14, x_13);
if (x_15 == 0)
{
uint8_t x_16; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_2);
lean_dec(x_1);
x_16 = 0;
return x_16;
}
else
{
size_t x_17; size_t x_18; uint8_t x_19; 
x_17 = 0;
x_18 = lean_usize_of_nat(x_13);
lean_dec(x_13);
x_19 = l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__7(x_1, x_2, x_12, x_17, x_18);
lean_dec(x_12);
return x_19;
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
x_13 = l_Lean_RBNode_findCore___rarg(x_1, x_2, x_12);
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
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_5 = l_Lean_PersistentArray_anyMAux___at_Lean_Meta_getFVarSetToGeneralize___spec__5(x_1, x_2, x_4);
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
size_t x_11; size_t x_12; uint8_t x_13; 
x_11 = 0;
x_12 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_13 = l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__8(x_1, x_2, x_6, x_11, x_12);
lean_dec(x_6);
return x_13;
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
x_6 = l_Lean_RBNode_findCore___rarg(x_1, x_2, x_5);
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
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_3, 0);
lean_inc(x_13);
lean_dec(x_3);
lean_inc(x_13);
x_14 = l_Lean_getExprMVarAssignment_x3f___at___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___spec__1(x_13, x_4);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_17 = lean_ctor_get(x_14, 1);
x_18 = lean_ctor_get(x_14, 0);
lean_dec(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
x_20 = l_Lean_MetavarContext_getDecl(x_19, x_13);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = l_Lean_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__4(x_1, x_2, x_22);
x_24 = lean_box(x_23);
lean_ctor_set(x_14, 0, x_24);
return x_14;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; 
x_25 = lean_ctor_get(x_14, 1);
lean_inc(x_25);
lean_dec(x_14);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
x_27 = l_Lean_MetavarContext_getDecl(x_26, x_13);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = l_Lean_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__4(x_1, x_2, x_29);
x_31 = lean_box(x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_25);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_13);
x_33 = lean_ctor_get(x_14, 1);
lean_inc(x_33);
lean_dec(x_14);
x_34 = lean_ctor_get(x_15, 0);
lean_inc(x_34);
lean_dec(x_15);
x_35 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__1(x_1, x_2, x_34, x_33);
return x_35;
}
}
case 5:
{
lean_object* x_36; uint8_t x_37; 
x_36 = l_Lean_Expr_getAppFn(x_3);
x_37 = l_Lean_Expr_isMVar(x_36);
if (x_37 == 0)
{
lean_object* x_38; 
lean_dec(x_36);
x_38 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at_Lean_Meta_getFVarSetToGeneralize___spec__3(x_1, x_2, x_3, x_4);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
lean_inc(x_3);
x_39 = l_Lean_instantiateMVars___at___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___spec__7(x_3, x_4);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = l_Lean_Expr_getAppFn(x_40);
x_43 = lean_expr_eqv(x_42, x_36);
lean_dec(x_36);
lean_dec(x_42);
if (x_43 == 0)
{
lean_dec(x_3);
x_3 = x_40;
x_4 = x_41;
goto _start;
}
else
{
lean_object* x_45; 
lean_dec(x_40);
x_45 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at_Lean_Meta_getFVarSetToGeneralize___spec__3(x_1, x_2, x_3, x_41);
return x_45;
}
}
}
case 6:
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_46 = lean_ctor_get(x_3, 1);
lean_inc(x_46);
x_47 = lean_ctor_get(x_3, 2);
lean_inc(x_47);
lean_dec(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_48 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__1(x_1, x_2, x_46, x_4);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_unbox(x_49);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; 
lean_dec(x_49);
x_51 = lean_ctor_get(x_48, 1);
lean_inc(x_51);
lean_dec(x_48);
x_52 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__1(x_1, x_2, x_47, x_51);
return x_52;
}
else
{
uint8_t x_53; 
lean_dec(x_47);
lean_dec(x_2);
lean_dec(x_1);
x_53 = !lean_is_exclusive(x_48);
if (x_53 == 0)
{
lean_object* x_54; 
x_54 = lean_ctor_get(x_48, 0);
lean_dec(x_54);
return x_48;
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_48, 1);
lean_inc(x_55);
lean_dec(x_48);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_49);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
case 7:
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_57 = lean_ctor_get(x_3, 1);
lean_inc(x_57);
x_58 = lean_ctor_get(x_3, 2);
lean_inc(x_58);
lean_dec(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_59 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__1(x_1, x_2, x_57, x_4);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_unbox(x_60);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; 
lean_dec(x_60);
x_62 = lean_ctor_get(x_59, 1);
lean_inc(x_62);
lean_dec(x_59);
x_63 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__1(x_1, x_2, x_58, x_62);
return x_63;
}
else
{
uint8_t x_64; 
lean_dec(x_58);
lean_dec(x_2);
lean_dec(x_1);
x_64 = !lean_is_exclusive(x_59);
if (x_64 == 0)
{
lean_object* x_65; 
x_65 = lean_ctor_get(x_59, 0);
lean_dec(x_65);
return x_59;
}
else
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_59, 1);
lean_inc(x_66);
lean_dec(x_59);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_60);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
case 8:
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_68 = lean_ctor_get(x_3, 1);
lean_inc(x_68);
x_69 = lean_ctor_get(x_3, 2);
lean_inc(x_69);
x_70 = lean_ctor_get(x_3, 3);
lean_inc(x_70);
lean_dec(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_71 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__1(x_1, x_2, x_68, x_4);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_unbox(x_72);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
lean_dec(x_72);
x_74 = lean_ctor_get(x_71, 1);
lean_inc(x_74);
lean_dec(x_71);
lean_inc(x_2);
lean_inc(x_1);
x_75 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__1(x_1, x_2, x_69, x_74);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_unbox(x_76);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; 
lean_dec(x_76);
x_78 = lean_ctor_get(x_75, 1);
lean_inc(x_78);
lean_dec(x_75);
x_79 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__1(x_1, x_2, x_70, x_78);
return x_79;
}
else
{
uint8_t x_80; 
lean_dec(x_70);
lean_dec(x_2);
lean_dec(x_1);
x_80 = !lean_is_exclusive(x_75);
if (x_80 == 0)
{
lean_object* x_81; 
x_81 = lean_ctor_get(x_75, 0);
lean_dec(x_81);
return x_75;
}
else
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_ctor_get(x_75, 1);
lean_inc(x_82);
lean_dec(x_75);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_76);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
}
else
{
uint8_t x_84; 
lean_dec(x_70);
lean_dec(x_69);
lean_dec(x_2);
lean_dec(x_1);
x_84 = !lean_is_exclusive(x_71);
if (x_84 == 0)
{
lean_object* x_85; 
x_85 = lean_ctor_get(x_71, 0);
lean_dec(x_85);
return x_71;
}
else
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_71, 1);
lean_inc(x_86);
lean_dec(x_71);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_72);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
}
case 10:
{
lean_object* x_88; lean_object* x_89; 
x_88 = lean_ctor_get(x_3, 1);
lean_inc(x_88);
lean_dec(x_3);
x_89 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__1(x_1, x_2, x_88, x_4);
return x_89;
}
case 11:
{
lean_object* x_90; lean_object* x_91; 
x_90 = lean_ctor_get(x_3, 2);
lean_inc(x_90);
lean_dec(x_3);
x_91 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__1(x_1, x_2, x_90, x_4);
return x_91;
}
default: 
{
uint8_t x_92; lean_object* x_93; lean_object* x_94; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_92 = 0;
x_93 = lean_box(x_92);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_4);
return x_94;
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
x_5 = l_Lean_RBNode_findCore___at_Lean_Meta_mkGeneralizationForbiddenSet_visit___spec__1(x_1, x_4);
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
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
lean_dec(x_2);
lean_inc(x_12);
x_13 = l_Lean_getExprMVarAssignment_x3f___at___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___spec__1(x_12, x_3);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_16 = lean_ctor_get(x_13, 1);
x_17 = lean_ctor_get(x_13, 0);
lean_dec(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
x_19 = l_Lean_MetavarContext_getDecl(x_18, x_12);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at_Lean_Meta_getFVarSetToGeneralize___spec__2___at_Lean_Meta_getFVarSetToGeneralize___spec__10___closed__1;
x_23 = l_Lean_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__4(x_22, x_1, x_21);
x_24 = lean_box(x_23);
lean_ctor_set(x_13, 0, x_24);
return x_13;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; 
x_25 = lean_ctor_get(x_13, 1);
lean_inc(x_25);
lean_dec(x_13);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
x_27 = l_Lean_MetavarContext_getDecl(x_26, x_12);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at_Lean_Meta_getFVarSetToGeneralize___spec__2___at_Lean_Meta_getFVarSetToGeneralize___spec__10___closed__1;
x_31 = l_Lean_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__4(x_30, x_1, x_29);
x_32 = lean_box(x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_25);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_12);
x_34 = lean_ctor_get(x_13, 1);
lean_inc(x_34);
lean_dec(x_13);
x_35 = lean_ctor_get(x_14, 0);
lean_inc(x_35);
lean_dec(x_14);
x_36 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__1___at_Lean_Meta_getFVarSetToGeneralize___spec__9(x_1, x_35, x_34);
return x_36;
}
}
case 5:
{
lean_object* x_37; uint8_t x_38; 
x_37 = l_Lean_Expr_getAppFn(x_2);
x_38 = l_Lean_Expr_isMVar(x_37);
if (x_38 == 0)
{
lean_object* x_39; 
lean_dec(x_37);
x_39 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at_Lean_Meta_getFVarSetToGeneralize___spec__3___at_Lean_Meta_getFVarSetToGeneralize___spec__11(x_1, x_2, x_3);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
lean_inc(x_2);
x_40 = l_Lean_instantiateMVars___at___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___spec__7(x_2, x_3);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = l_Lean_Expr_getAppFn(x_41);
x_44 = lean_expr_eqv(x_43, x_37);
lean_dec(x_37);
lean_dec(x_43);
if (x_44 == 0)
{
lean_dec(x_2);
x_2 = x_41;
x_3 = x_42;
goto _start;
}
else
{
lean_object* x_46; 
lean_dec(x_41);
x_46 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at_Lean_Meta_getFVarSetToGeneralize___spec__3___at_Lean_Meta_getFVarSetToGeneralize___spec__11(x_1, x_2, x_42);
return x_46;
}
}
}
case 6:
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_47 = lean_ctor_get(x_2, 1);
lean_inc(x_47);
x_48 = lean_ctor_get(x_2, 2);
lean_inc(x_48);
lean_dec(x_2);
lean_inc(x_1);
x_49 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__1___at_Lean_Meta_getFVarSetToGeneralize___spec__9(x_1, x_47, x_3);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_unbox(x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
lean_dec(x_50);
x_52 = lean_ctor_get(x_49, 1);
lean_inc(x_52);
lean_dec(x_49);
x_53 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__1___at_Lean_Meta_getFVarSetToGeneralize___spec__9(x_1, x_48, x_52);
return x_53;
}
else
{
uint8_t x_54; 
lean_dec(x_48);
lean_dec(x_1);
x_54 = !lean_is_exclusive(x_49);
if (x_54 == 0)
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_49, 0);
lean_dec(x_55);
return x_49;
}
else
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_49, 1);
lean_inc(x_56);
lean_dec(x_49);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_50);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
case 7:
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_58 = lean_ctor_get(x_2, 1);
lean_inc(x_58);
x_59 = lean_ctor_get(x_2, 2);
lean_inc(x_59);
lean_dec(x_2);
lean_inc(x_1);
x_60 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__1___at_Lean_Meta_getFVarSetToGeneralize___spec__9(x_1, x_58, x_3);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_unbox(x_61);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_61);
x_63 = lean_ctor_get(x_60, 1);
lean_inc(x_63);
lean_dec(x_60);
x_64 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__1___at_Lean_Meta_getFVarSetToGeneralize___spec__9(x_1, x_59, x_63);
return x_64;
}
else
{
uint8_t x_65; 
lean_dec(x_59);
lean_dec(x_1);
x_65 = !lean_is_exclusive(x_60);
if (x_65 == 0)
{
lean_object* x_66; 
x_66 = lean_ctor_get(x_60, 0);
lean_dec(x_66);
return x_60;
}
else
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_60, 1);
lean_inc(x_67);
lean_dec(x_60);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_61);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
case 8:
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_69 = lean_ctor_get(x_2, 1);
lean_inc(x_69);
x_70 = lean_ctor_get(x_2, 2);
lean_inc(x_70);
x_71 = lean_ctor_get(x_2, 3);
lean_inc(x_71);
lean_dec(x_2);
lean_inc(x_1);
x_72 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__1___at_Lean_Meta_getFVarSetToGeneralize___spec__9(x_1, x_69, x_3);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_unbox(x_73);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; 
lean_dec(x_73);
x_75 = lean_ctor_get(x_72, 1);
lean_inc(x_75);
lean_dec(x_72);
lean_inc(x_1);
x_76 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__1___at_Lean_Meta_getFVarSetToGeneralize___spec__9(x_1, x_70, x_75);
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
x_80 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__1___at_Lean_Meta_getFVarSetToGeneralize___spec__9(x_1, x_71, x_79);
return x_80;
}
else
{
uint8_t x_81; 
lean_dec(x_71);
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
else
{
uint8_t x_85; 
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_1);
x_85 = !lean_is_exclusive(x_72);
if (x_85 == 0)
{
lean_object* x_86; 
x_86 = lean_ctor_get(x_72, 0);
lean_dec(x_86);
return x_72;
}
else
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_72, 1);
lean_inc(x_87);
lean_dec(x_72);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_73);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
case 10:
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_ctor_get(x_2, 1);
lean_inc(x_89);
lean_dec(x_2);
x_90 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__1___at_Lean_Meta_getFVarSetToGeneralize___spec__9(x_1, x_89, x_3);
return x_90;
}
case 11:
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_ctor_get(x_2, 2);
lean_inc(x_91);
lean_dec(x_2);
x_92 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__1___at_Lean_Meta_getFVarSetToGeneralize___spec__9(x_1, x_91, x_3);
return x_92;
}
default: 
{
uint8_t x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_2);
lean_dec(x_1);
x_93 = 0;
x_94 = lean_box(x_93);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_3);
return x_95;
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
x_8 = l_Lean_PersistentArray_anyMAux___at_Lean_Meta_getFVarSetToGeneralize___spec__16(x_1, x_2, x_7);
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
x_13 = l_Lean_RBNode_findCore___rarg(x_1, x_2, x_12);
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
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyMAux___at_Lean_Meta_getFVarSetToGeneralize___spec__16(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
size_t x_9; size_t x_10; uint8_t x_11; 
x_9 = 0;
x_10 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_11 = l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__17(x_1, x_2, x_4, x_9, x_10);
lean_dec(x_4);
return x_11;
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_3, 0);
lean_inc(x_12);
lean_dec(x_3);
x_13 = lean_array_get_size(x_12);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_lt(x_14, x_13);
if (x_15 == 0)
{
uint8_t x_16; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_2);
lean_dec(x_1);
x_16 = 0;
return x_16;
}
else
{
size_t x_17; size_t x_18; uint8_t x_19; 
x_17 = 0;
x_18 = lean_usize_of_nat(x_13);
lean_dec(x_13);
x_19 = l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__18(x_1, x_2, x_12, x_17, x_18);
lean_dec(x_12);
return x_19;
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
x_13 = l_Lean_RBNode_findCore___rarg(x_1, x_2, x_12);
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
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__15(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_5 = l_Lean_PersistentArray_anyMAux___at_Lean_Meta_getFVarSetToGeneralize___spec__16(x_1, x_2, x_4);
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
size_t x_11; size_t x_12; uint8_t x_13; 
x_11 = 0;
x_12 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_13 = l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__19(x_1, x_2, x_6, x_11, x_12);
lean_dec(x_6);
return x_13;
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
x_6 = l_Lean_RBNode_findCore___rarg(x_1, x_2, x_5);
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
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_3, 0);
lean_inc(x_13);
lean_dec(x_3);
lean_inc(x_13);
x_14 = l_Lean_getExprMVarAssignment_x3f___at___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___spec__1(x_13, x_4);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_17 = lean_ctor_get(x_14, 1);
x_18 = lean_ctor_get(x_14, 0);
lean_dec(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
x_20 = l_Lean_MetavarContext_getDecl(x_19, x_13);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = l_Lean_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__15(x_1, x_2, x_22);
x_24 = lean_box(x_23);
lean_ctor_set(x_14, 0, x_24);
return x_14;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; 
x_25 = lean_ctor_get(x_14, 1);
lean_inc(x_25);
lean_dec(x_14);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
x_27 = l_Lean_MetavarContext_getDecl(x_26, x_13);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = l_Lean_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__15(x_1, x_2, x_29);
x_31 = lean_box(x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_25);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_13);
x_33 = lean_ctor_get(x_14, 1);
lean_inc(x_33);
lean_dec(x_14);
x_34 = lean_ctor_get(x_15, 0);
lean_inc(x_34);
lean_dec(x_15);
x_35 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__12(x_1, x_2, x_34, x_33);
return x_35;
}
}
case 5:
{
lean_object* x_36; uint8_t x_37; 
x_36 = l_Lean_Expr_getAppFn(x_3);
x_37 = l_Lean_Expr_isMVar(x_36);
if (x_37 == 0)
{
lean_object* x_38; 
lean_dec(x_36);
x_38 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at_Lean_Meta_getFVarSetToGeneralize___spec__14(x_1, x_2, x_3, x_4);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
lean_inc(x_3);
x_39 = l_Lean_instantiateMVars___at___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___spec__7(x_3, x_4);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = l_Lean_Expr_getAppFn(x_40);
x_43 = lean_expr_eqv(x_42, x_36);
lean_dec(x_36);
lean_dec(x_42);
if (x_43 == 0)
{
lean_dec(x_3);
x_3 = x_40;
x_4 = x_41;
goto _start;
}
else
{
lean_object* x_45; 
lean_dec(x_40);
x_45 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at_Lean_Meta_getFVarSetToGeneralize___spec__14(x_1, x_2, x_3, x_41);
return x_45;
}
}
}
case 6:
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_46 = lean_ctor_get(x_3, 1);
lean_inc(x_46);
x_47 = lean_ctor_get(x_3, 2);
lean_inc(x_47);
lean_dec(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_48 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__12(x_1, x_2, x_46, x_4);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_unbox(x_49);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; 
lean_dec(x_49);
x_51 = lean_ctor_get(x_48, 1);
lean_inc(x_51);
lean_dec(x_48);
x_52 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__12(x_1, x_2, x_47, x_51);
return x_52;
}
else
{
uint8_t x_53; 
lean_dec(x_47);
lean_dec(x_2);
lean_dec(x_1);
x_53 = !lean_is_exclusive(x_48);
if (x_53 == 0)
{
lean_object* x_54; 
x_54 = lean_ctor_get(x_48, 0);
lean_dec(x_54);
return x_48;
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_48, 1);
lean_inc(x_55);
lean_dec(x_48);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_49);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
case 7:
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_57 = lean_ctor_get(x_3, 1);
lean_inc(x_57);
x_58 = lean_ctor_get(x_3, 2);
lean_inc(x_58);
lean_dec(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_59 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__12(x_1, x_2, x_57, x_4);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_unbox(x_60);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; 
lean_dec(x_60);
x_62 = lean_ctor_get(x_59, 1);
lean_inc(x_62);
lean_dec(x_59);
x_63 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__12(x_1, x_2, x_58, x_62);
return x_63;
}
else
{
uint8_t x_64; 
lean_dec(x_58);
lean_dec(x_2);
lean_dec(x_1);
x_64 = !lean_is_exclusive(x_59);
if (x_64 == 0)
{
lean_object* x_65; 
x_65 = lean_ctor_get(x_59, 0);
lean_dec(x_65);
return x_59;
}
else
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_59, 1);
lean_inc(x_66);
lean_dec(x_59);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_60);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
case 8:
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_68 = lean_ctor_get(x_3, 1);
lean_inc(x_68);
x_69 = lean_ctor_get(x_3, 2);
lean_inc(x_69);
x_70 = lean_ctor_get(x_3, 3);
lean_inc(x_70);
lean_dec(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_71 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__12(x_1, x_2, x_68, x_4);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_unbox(x_72);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
lean_dec(x_72);
x_74 = lean_ctor_get(x_71, 1);
lean_inc(x_74);
lean_dec(x_71);
lean_inc(x_2);
lean_inc(x_1);
x_75 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__12(x_1, x_2, x_69, x_74);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_unbox(x_76);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; 
lean_dec(x_76);
x_78 = lean_ctor_get(x_75, 1);
lean_inc(x_78);
lean_dec(x_75);
x_79 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__12(x_1, x_2, x_70, x_78);
return x_79;
}
else
{
uint8_t x_80; 
lean_dec(x_70);
lean_dec(x_2);
lean_dec(x_1);
x_80 = !lean_is_exclusive(x_75);
if (x_80 == 0)
{
lean_object* x_81; 
x_81 = lean_ctor_get(x_75, 0);
lean_dec(x_81);
return x_75;
}
else
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_ctor_get(x_75, 1);
lean_inc(x_82);
lean_dec(x_75);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_76);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
}
else
{
uint8_t x_84; 
lean_dec(x_70);
lean_dec(x_69);
lean_dec(x_2);
lean_dec(x_1);
x_84 = !lean_is_exclusive(x_71);
if (x_84 == 0)
{
lean_object* x_85; 
x_85 = lean_ctor_get(x_71, 0);
lean_dec(x_85);
return x_71;
}
else
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_71, 1);
lean_inc(x_86);
lean_dec(x_71);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_72);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
}
case 10:
{
lean_object* x_88; lean_object* x_89; 
x_88 = lean_ctor_get(x_3, 1);
lean_inc(x_88);
lean_dec(x_3);
x_89 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__12(x_1, x_2, x_88, x_4);
return x_89;
}
case 11:
{
lean_object* x_90; lean_object* x_91; 
x_90 = lean_ctor_get(x_3, 2);
lean_inc(x_90);
lean_dec(x_3);
x_91 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__12(x_1, x_2, x_90, x_4);
return x_91;
}
default: 
{
uint8_t x_92; lean_object* x_93; lean_object* x_94; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_92 = 0;
x_93 = lean_box(x_92);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_4);
return x_94;
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
x_5 = l_Lean_RBNode_findCore___at_Lean_Meta_mkGeneralizationForbiddenSet_visit___spec__1(x_1, x_4);
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
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
lean_dec(x_2);
lean_inc(x_12);
x_13 = l_Lean_getExprMVarAssignment_x3f___at___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___spec__1(x_12, x_3);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_16 = lean_ctor_get(x_13, 1);
x_17 = lean_ctor_get(x_13, 0);
lean_dec(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
x_19 = l_Lean_MetavarContext_getDecl(x_18, x_12);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at_Lean_Meta_getFVarSetToGeneralize___spec__2___at_Lean_Meta_getFVarSetToGeneralize___spec__10___closed__1;
x_23 = l_Lean_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__15(x_22, x_1, x_21);
x_24 = lean_box(x_23);
lean_ctor_set(x_13, 0, x_24);
return x_13;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; 
x_25 = lean_ctor_get(x_13, 1);
lean_inc(x_25);
lean_dec(x_13);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
x_27 = l_Lean_MetavarContext_getDecl(x_26, x_12);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at_Lean_Meta_getFVarSetToGeneralize___spec__2___at_Lean_Meta_getFVarSetToGeneralize___spec__10___closed__1;
x_31 = l_Lean_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__15(x_30, x_1, x_29);
x_32 = lean_box(x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_25);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_12);
x_34 = lean_ctor_get(x_13, 1);
lean_inc(x_34);
lean_dec(x_13);
x_35 = lean_ctor_get(x_14, 0);
lean_inc(x_35);
lean_dec(x_14);
x_36 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__12___at_Lean_Meta_getFVarSetToGeneralize___spec__20(x_1, x_35, x_34);
return x_36;
}
}
case 5:
{
lean_object* x_37; uint8_t x_38; 
x_37 = l_Lean_Expr_getAppFn(x_2);
x_38 = l_Lean_Expr_isMVar(x_37);
if (x_38 == 0)
{
lean_object* x_39; 
lean_dec(x_37);
x_39 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at_Lean_Meta_getFVarSetToGeneralize___spec__14___at_Lean_Meta_getFVarSetToGeneralize___spec__22(x_1, x_2, x_3);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
lean_inc(x_2);
x_40 = l_Lean_instantiateMVars___at___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___spec__7(x_2, x_3);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = l_Lean_Expr_getAppFn(x_41);
x_44 = lean_expr_eqv(x_43, x_37);
lean_dec(x_37);
lean_dec(x_43);
if (x_44 == 0)
{
lean_dec(x_2);
x_2 = x_41;
x_3 = x_42;
goto _start;
}
else
{
lean_object* x_46; 
lean_dec(x_41);
x_46 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at_Lean_Meta_getFVarSetToGeneralize___spec__14___at_Lean_Meta_getFVarSetToGeneralize___spec__22(x_1, x_2, x_42);
return x_46;
}
}
}
case 6:
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_47 = lean_ctor_get(x_2, 1);
lean_inc(x_47);
x_48 = lean_ctor_get(x_2, 2);
lean_inc(x_48);
lean_dec(x_2);
lean_inc(x_1);
x_49 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__12___at_Lean_Meta_getFVarSetToGeneralize___spec__20(x_1, x_47, x_3);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_unbox(x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
lean_dec(x_50);
x_52 = lean_ctor_get(x_49, 1);
lean_inc(x_52);
lean_dec(x_49);
x_53 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__12___at_Lean_Meta_getFVarSetToGeneralize___spec__20(x_1, x_48, x_52);
return x_53;
}
else
{
uint8_t x_54; 
lean_dec(x_48);
lean_dec(x_1);
x_54 = !lean_is_exclusive(x_49);
if (x_54 == 0)
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_49, 0);
lean_dec(x_55);
return x_49;
}
else
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_49, 1);
lean_inc(x_56);
lean_dec(x_49);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_50);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
case 7:
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_58 = lean_ctor_get(x_2, 1);
lean_inc(x_58);
x_59 = lean_ctor_get(x_2, 2);
lean_inc(x_59);
lean_dec(x_2);
lean_inc(x_1);
x_60 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__12___at_Lean_Meta_getFVarSetToGeneralize___spec__20(x_1, x_58, x_3);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_unbox(x_61);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_61);
x_63 = lean_ctor_get(x_60, 1);
lean_inc(x_63);
lean_dec(x_60);
x_64 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__12___at_Lean_Meta_getFVarSetToGeneralize___spec__20(x_1, x_59, x_63);
return x_64;
}
else
{
uint8_t x_65; 
lean_dec(x_59);
lean_dec(x_1);
x_65 = !lean_is_exclusive(x_60);
if (x_65 == 0)
{
lean_object* x_66; 
x_66 = lean_ctor_get(x_60, 0);
lean_dec(x_66);
return x_60;
}
else
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_60, 1);
lean_inc(x_67);
lean_dec(x_60);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_61);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
case 8:
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_69 = lean_ctor_get(x_2, 1);
lean_inc(x_69);
x_70 = lean_ctor_get(x_2, 2);
lean_inc(x_70);
x_71 = lean_ctor_get(x_2, 3);
lean_inc(x_71);
lean_dec(x_2);
lean_inc(x_1);
x_72 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__12___at_Lean_Meta_getFVarSetToGeneralize___spec__20(x_1, x_69, x_3);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_unbox(x_73);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; 
lean_dec(x_73);
x_75 = lean_ctor_get(x_72, 1);
lean_inc(x_75);
lean_dec(x_72);
lean_inc(x_1);
x_76 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__12___at_Lean_Meta_getFVarSetToGeneralize___spec__20(x_1, x_70, x_75);
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
x_80 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__12___at_Lean_Meta_getFVarSetToGeneralize___spec__20(x_1, x_71, x_79);
return x_80;
}
else
{
uint8_t x_81; 
lean_dec(x_71);
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
else
{
uint8_t x_85; 
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_1);
x_85 = !lean_is_exclusive(x_72);
if (x_85 == 0)
{
lean_object* x_86; 
x_86 = lean_ctor_get(x_72, 0);
lean_dec(x_86);
return x_72;
}
else
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_72, 1);
lean_inc(x_87);
lean_dec(x_72);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_73);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
case 10:
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_ctor_get(x_2, 1);
lean_inc(x_89);
lean_dec(x_2);
x_90 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__12___at_Lean_Meta_getFVarSetToGeneralize___spec__20(x_1, x_89, x_3);
return x_90;
}
case 11:
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_ctor_get(x_2, 2);
lean_inc(x_91);
lean_dec(x_2);
x_92 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__12___at_Lean_Meta_getFVarSetToGeneralize___spec__20(x_1, x_91, x_3);
return x_92;
}
default: 
{
uint8_t x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_2);
lean_dec(x_1);
x_93 = 0;
x_94 = lean_box(x_93);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_3);
return x_95;
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
x_8 = l_Lean_PersistentArray_anyMAux___at_Lean_Meta_getFVarSetToGeneralize___spec__27(x_1, x_2, x_7);
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
x_13 = l_Lean_RBNode_findCore___rarg(x_1, x_2, x_12);
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
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyMAux___at_Lean_Meta_getFVarSetToGeneralize___spec__27(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
size_t x_9; size_t x_10; uint8_t x_11; 
x_9 = 0;
x_10 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_11 = l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__28(x_1, x_2, x_4, x_9, x_10);
lean_dec(x_4);
return x_11;
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_3, 0);
lean_inc(x_12);
lean_dec(x_3);
x_13 = lean_array_get_size(x_12);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_lt(x_14, x_13);
if (x_15 == 0)
{
uint8_t x_16; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_2);
lean_dec(x_1);
x_16 = 0;
return x_16;
}
else
{
size_t x_17; size_t x_18; uint8_t x_19; 
x_17 = 0;
x_18 = lean_usize_of_nat(x_13);
lean_dec(x_13);
x_19 = l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__29(x_1, x_2, x_12, x_17, x_18);
lean_dec(x_12);
return x_19;
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
x_13 = l_Lean_RBNode_findCore___rarg(x_1, x_2, x_12);
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
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__26(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_5 = l_Lean_PersistentArray_anyMAux___at_Lean_Meta_getFVarSetToGeneralize___spec__27(x_1, x_2, x_4);
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
size_t x_11; size_t x_12; uint8_t x_13; 
x_11 = 0;
x_12 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_13 = l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__30(x_1, x_2, x_6, x_11, x_12);
lean_dec(x_6);
return x_13;
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
x_6 = l_Lean_RBNode_findCore___rarg(x_1, x_2, x_5);
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
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_3, 0);
lean_inc(x_13);
lean_dec(x_3);
lean_inc(x_13);
x_14 = l_Lean_getExprMVarAssignment_x3f___at___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___spec__1(x_13, x_4);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_17 = lean_ctor_get(x_14, 1);
x_18 = lean_ctor_get(x_14, 0);
lean_dec(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
x_20 = l_Lean_MetavarContext_getDecl(x_19, x_13);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = l_Lean_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__26(x_1, x_2, x_22);
x_24 = lean_box(x_23);
lean_ctor_set(x_14, 0, x_24);
return x_14;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; 
x_25 = lean_ctor_get(x_14, 1);
lean_inc(x_25);
lean_dec(x_14);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
x_27 = l_Lean_MetavarContext_getDecl(x_26, x_13);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = l_Lean_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__26(x_1, x_2, x_29);
x_31 = lean_box(x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_25);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_13);
x_33 = lean_ctor_get(x_14, 1);
lean_inc(x_33);
lean_dec(x_14);
x_34 = lean_ctor_get(x_15, 0);
lean_inc(x_34);
lean_dec(x_15);
x_35 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__23(x_1, x_2, x_34, x_33);
return x_35;
}
}
case 5:
{
lean_object* x_36; uint8_t x_37; 
x_36 = l_Lean_Expr_getAppFn(x_3);
x_37 = l_Lean_Expr_isMVar(x_36);
if (x_37 == 0)
{
lean_object* x_38; 
lean_dec(x_36);
x_38 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at_Lean_Meta_getFVarSetToGeneralize___spec__25(x_1, x_2, x_3, x_4);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
lean_inc(x_3);
x_39 = l_Lean_instantiateMVars___at___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___spec__7(x_3, x_4);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = l_Lean_Expr_getAppFn(x_40);
x_43 = lean_expr_eqv(x_42, x_36);
lean_dec(x_36);
lean_dec(x_42);
if (x_43 == 0)
{
lean_dec(x_3);
x_3 = x_40;
x_4 = x_41;
goto _start;
}
else
{
lean_object* x_45; 
lean_dec(x_40);
x_45 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at_Lean_Meta_getFVarSetToGeneralize___spec__25(x_1, x_2, x_3, x_41);
return x_45;
}
}
}
case 6:
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_46 = lean_ctor_get(x_3, 1);
lean_inc(x_46);
x_47 = lean_ctor_get(x_3, 2);
lean_inc(x_47);
lean_dec(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_48 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__23(x_1, x_2, x_46, x_4);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_unbox(x_49);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; 
lean_dec(x_49);
x_51 = lean_ctor_get(x_48, 1);
lean_inc(x_51);
lean_dec(x_48);
x_52 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__23(x_1, x_2, x_47, x_51);
return x_52;
}
else
{
uint8_t x_53; 
lean_dec(x_47);
lean_dec(x_2);
lean_dec(x_1);
x_53 = !lean_is_exclusive(x_48);
if (x_53 == 0)
{
lean_object* x_54; 
x_54 = lean_ctor_get(x_48, 0);
lean_dec(x_54);
return x_48;
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_48, 1);
lean_inc(x_55);
lean_dec(x_48);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_49);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
case 7:
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_57 = lean_ctor_get(x_3, 1);
lean_inc(x_57);
x_58 = lean_ctor_get(x_3, 2);
lean_inc(x_58);
lean_dec(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_59 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__23(x_1, x_2, x_57, x_4);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_unbox(x_60);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; 
lean_dec(x_60);
x_62 = lean_ctor_get(x_59, 1);
lean_inc(x_62);
lean_dec(x_59);
x_63 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__23(x_1, x_2, x_58, x_62);
return x_63;
}
else
{
uint8_t x_64; 
lean_dec(x_58);
lean_dec(x_2);
lean_dec(x_1);
x_64 = !lean_is_exclusive(x_59);
if (x_64 == 0)
{
lean_object* x_65; 
x_65 = lean_ctor_get(x_59, 0);
lean_dec(x_65);
return x_59;
}
else
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_59, 1);
lean_inc(x_66);
lean_dec(x_59);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_60);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
case 8:
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_68 = lean_ctor_get(x_3, 1);
lean_inc(x_68);
x_69 = lean_ctor_get(x_3, 2);
lean_inc(x_69);
x_70 = lean_ctor_get(x_3, 3);
lean_inc(x_70);
lean_dec(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_71 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__23(x_1, x_2, x_68, x_4);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_unbox(x_72);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
lean_dec(x_72);
x_74 = lean_ctor_get(x_71, 1);
lean_inc(x_74);
lean_dec(x_71);
lean_inc(x_2);
lean_inc(x_1);
x_75 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__23(x_1, x_2, x_69, x_74);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_unbox(x_76);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; 
lean_dec(x_76);
x_78 = lean_ctor_get(x_75, 1);
lean_inc(x_78);
lean_dec(x_75);
x_79 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__23(x_1, x_2, x_70, x_78);
return x_79;
}
else
{
uint8_t x_80; 
lean_dec(x_70);
lean_dec(x_2);
lean_dec(x_1);
x_80 = !lean_is_exclusive(x_75);
if (x_80 == 0)
{
lean_object* x_81; 
x_81 = lean_ctor_get(x_75, 0);
lean_dec(x_81);
return x_75;
}
else
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_ctor_get(x_75, 1);
lean_inc(x_82);
lean_dec(x_75);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_76);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
}
else
{
uint8_t x_84; 
lean_dec(x_70);
lean_dec(x_69);
lean_dec(x_2);
lean_dec(x_1);
x_84 = !lean_is_exclusive(x_71);
if (x_84 == 0)
{
lean_object* x_85; 
x_85 = lean_ctor_get(x_71, 0);
lean_dec(x_85);
return x_71;
}
else
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_71, 1);
lean_inc(x_86);
lean_dec(x_71);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_72);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
}
case 10:
{
lean_object* x_88; lean_object* x_89; 
x_88 = lean_ctor_get(x_3, 1);
lean_inc(x_88);
lean_dec(x_3);
x_89 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__23(x_1, x_2, x_88, x_4);
return x_89;
}
case 11:
{
lean_object* x_90; lean_object* x_91; 
x_90 = lean_ctor_get(x_3, 2);
lean_inc(x_90);
lean_dec(x_3);
x_91 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__23(x_1, x_2, x_90, x_4);
return x_91;
}
default: 
{
uint8_t x_92; lean_object* x_93; lean_object* x_94; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_92 = 0;
x_93 = lean_box(x_92);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_4);
return x_94;
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
x_8 = l_Lean_PersistentArray_anyMAux___at_Lean_Meta_getFVarSetToGeneralize___spec__35(x_1, x_2, x_7);
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
x_13 = l_Lean_RBNode_findCore___rarg(x_1, x_2, x_12);
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
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyMAux___at_Lean_Meta_getFVarSetToGeneralize___spec__35(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
size_t x_9; size_t x_10; uint8_t x_11; 
x_9 = 0;
x_10 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_11 = l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__36(x_1, x_2, x_4, x_9, x_10);
lean_dec(x_4);
return x_11;
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_3, 0);
lean_inc(x_12);
lean_dec(x_3);
x_13 = lean_array_get_size(x_12);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_lt(x_14, x_13);
if (x_15 == 0)
{
uint8_t x_16; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_2);
lean_dec(x_1);
x_16 = 0;
return x_16;
}
else
{
size_t x_17; size_t x_18; uint8_t x_19; 
x_17 = 0;
x_18 = lean_usize_of_nat(x_13);
lean_dec(x_13);
x_19 = l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__37(x_1, x_2, x_12, x_17, x_18);
lean_dec(x_12);
return x_19;
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
x_13 = l_Lean_RBNode_findCore___rarg(x_1, x_2, x_12);
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
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__34(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_5 = l_Lean_PersistentArray_anyMAux___at_Lean_Meta_getFVarSetToGeneralize___spec__35(x_1, x_2, x_4);
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
size_t x_11; size_t x_12; uint8_t x_13; 
x_11 = 0;
x_12 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_13 = l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__38(x_1, x_2, x_6, x_11, x_12);
lean_dec(x_6);
return x_13;
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
x_6 = l_Lean_RBNode_findCore___rarg(x_1, x_2, x_5);
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
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_3, 0);
lean_inc(x_13);
lean_dec(x_3);
lean_inc(x_13);
x_14 = l_Lean_getExprMVarAssignment_x3f___at___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___spec__1(x_13, x_4);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_17 = lean_ctor_get(x_14, 1);
x_18 = lean_ctor_get(x_14, 0);
lean_dec(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
x_20 = l_Lean_MetavarContext_getDecl(x_19, x_13);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = l_Lean_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__34(x_1, x_2, x_22);
x_24 = lean_box(x_23);
lean_ctor_set(x_14, 0, x_24);
return x_14;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; 
x_25 = lean_ctor_get(x_14, 1);
lean_inc(x_25);
lean_dec(x_14);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
x_27 = l_Lean_MetavarContext_getDecl(x_26, x_13);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = l_Lean_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__34(x_1, x_2, x_29);
x_31 = lean_box(x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_25);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_13);
x_33 = lean_ctor_get(x_14, 1);
lean_inc(x_33);
lean_dec(x_14);
x_34 = lean_ctor_get(x_15, 0);
lean_inc(x_34);
lean_dec(x_15);
x_35 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__31(x_1, x_2, x_34, x_33);
return x_35;
}
}
case 5:
{
lean_object* x_36; uint8_t x_37; 
x_36 = l_Lean_Expr_getAppFn(x_3);
x_37 = l_Lean_Expr_isMVar(x_36);
if (x_37 == 0)
{
lean_object* x_38; 
lean_dec(x_36);
x_38 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at_Lean_Meta_getFVarSetToGeneralize___spec__33(x_1, x_2, x_3, x_4);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
lean_inc(x_3);
x_39 = l_Lean_instantiateMVars___at___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___spec__7(x_3, x_4);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = l_Lean_Expr_getAppFn(x_40);
x_43 = lean_expr_eqv(x_42, x_36);
lean_dec(x_36);
lean_dec(x_42);
if (x_43 == 0)
{
lean_dec(x_3);
x_3 = x_40;
x_4 = x_41;
goto _start;
}
else
{
lean_object* x_45; 
lean_dec(x_40);
x_45 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at_Lean_Meta_getFVarSetToGeneralize___spec__33(x_1, x_2, x_3, x_41);
return x_45;
}
}
}
case 6:
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_46 = lean_ctor_get(x_3, 1);
lean_inc(x_46);
x_47 = lean_ctor_get(x_3, 2);
lean_inc(x_47);
lean_dec(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_48 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__31(x_1, x_2, x_46, x_4);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_unbox(x_49);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; 
lean_dec(x_49);
x_51 = lean_ctor_get(x_48, 1);
lean_inc(x_51);
lean_dec(x_48);
x_52 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__31(x_1, x_2, x_47, x_51);
return x_52;
}
else
{
uint8_t x_53; 
lean_dec(x_47);
lean_dec(x_2);
lean_dec(x_1);
x_53 = !lean_is_exclusive(x_48);
if (x_53 == 0)
{
lean_object* x_54; 
x_54 = lean_ctor_get(x_48, 0);
lean_dec(x_54);
return x_48;
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_48, 1);
lean_inc(x_55);
lean_dec(x_48);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_49);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
case 7:
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_57 = lean_ctor_get(x_3, 1);
lean_inc(x_57);
x_58 = lean_ctor_get(x_3, 2);
lean_inc(x_58);
lean_dec(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_59 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__31(x_1, x_2, x_57, x_4);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_unbox(x_60);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; 
lean_dec(x_60);
x_62 = lean_ctor_get(x_59, 1);
lean_inc(x_62);
lean_dec(x_59);
x_63 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__31(x_1, x_2, x_58, x_62);
return x_63;
}
else
{
uint8_t x_64; 
lean_dec(x_58);
lean_dec(x_2);
lean_dec(x_1);
x_64 = !lean_is_exclusive(x_59);
if (x_64 == 0)
{
lean_object* x_65; 
x_65 = lean_ctor_get(x_59, 0);
lean_dec(x_65);
return x_59;
}
else
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_59, 1);
lean_inc(x_66);
lean_dec(x_59);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_60);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
case 8:
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_68 = lean_ctor_get(x_3, 1);
lean_inc(x_68);
x_69 = lean_ctor_get(x_3, 2);
lean_inc(x_69);
x_70 = lean_ctor_get(x_3, 3);
lean_inc(x_70);
lean_dec(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_71 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__31(x_1, x_2, x_68, x_4);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_unbox(x_72);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
lean_dec(x_72);
x_74 = lean_ctor_get(x_71, 1);
lean_inc(x_74);
lean_dec(x_71);
lean_inc(x_2);
lean_inc(x_1);
x_75 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__31(x_1, x_2, x_69, x_74);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_unbox(x_76);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; 
lean_dec(x_76);
x_78 = lean_ctor_get(x_75, 1);
lean_inc(x_78);
lean_dec(x_75);
x_79 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__31(x_1, x_2, x_70, x_78);
return x_79;
}
else
{
uint8_t x_80; 
lean_dec(x_70);
lean_dec(x_2);
lean_dec(x_1);
x_80 = !lean_is_exclusive(x_75);
if (x_80 == 0)
{
lean_object* x_81; 
x_81 = lean_ctor_get(x_75, 0);
lean_dec(x_81);
return x_75;
}
else
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_ctor_get(x_75, 1);
lean_inc(x_82);
lean_dec(x_75);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_76);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
}
else
{
uint8_t x_84; 
lean_dec(x_70);
lean_dec(x_69);
lean_dec(x_2);
lean_dec(x_1);
x_84 = !lean_is_exclusive(x_71);
if (x_84 == 0)
{
lean_object* x_85; 
x_85 = lean_ctor_get(x_71, 0);
lean_dec(x_85);
return x_71;
}
else
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_71, 1);
lean_inc(x_86);
lean_dec(x_71);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_72);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
}
case 10:
{
lean_object* x_88; lean_object* x_89; 
x_88 = lean_ctor_get(x_3, 1);
lean_inc(x_88);
lean_dec(x_3);
x_89 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__31(x_1, x_2, x_88, x_4);
return x_89;
}
case 11:
{
lean_object* x_90; lean_object* x_91; 
x_90 = lean_ctor_get(x_3, 2);
lean_inc(x_90);
lean_dec(x_3);
x_91 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__31(x_1, x_2, x_90, x_4);
return x_91;
}
default: 
{
uint8_t x_92; lean_object* x_93; lean_object* x_94; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_92 = 0;
x_93 = lean_box(x_92);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_4);
return x_94;
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
x_8 = l_Lean_PersistentArray_anyMAux___at_Lean_Meta_getFVarSetToGeneralize___spec__43(x_1, x_2, x_7);
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
x_13 = l_Lean_RBNode_findCore___rarg(x_1, x_2, x_12);
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
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyMAux___at_Lean_Meta_getFVarSetToGeneralize___spec__43(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
size_t x_9; size_t x_10; uint8_t x_11; 
x_9 = 0;
x_10 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_11 = l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__44(x_1, x_2, x_4, x_9, x_10);
lean_dec(x_4);
return x_11;
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_3, 0);
lean_inc(x_12);
lean_dec(x_3);
x_13 = lean_array_get_size(x_12);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_lt(x_14, x_13);
if (x_15 == 0)
{
uint8_t x_16; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_2);
lean_dec(x_1);
x_16 = 0;
return x_16;
}
else
{
size_t x_17; size_t x_18; uint8_t x_19; 
x_17 = 0;
x_18 = lean_usize_of_nat(x_13);
lean_dec(x_13);
x_19 = l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__45(x_1, x_2, x_12, x_17, x_18);
lean_dec(x_12);
return x_19;
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
x_13 = l_Lean_RBNode_findCore___rarg(x_1, x_2, x_12);
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
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__42(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_5 = l_Lean_PersistentArray_anyMAux___at_Lean_Meta_getFVarSetToGeneralize___spec__43(x_1, x_2, x_4);
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
size_t x_11; size_t x_12; uint8_t x_13; 
x_11 = 0;
x_12 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_13 = l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__46(x_1, x_2, x_6, x_11, x_12);
lean_dec(x_6);
return x_13;
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
x_6 = l_Lean_RBNode_findCore___rarg(x_1, x_2, x_5);
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
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_3, 0);
lean_inc(x_13);
lean_dec(x_3);
lean_inc(x_13);
x_14 = l_Lean_getExprMVarAssignment_x3f___at___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___spec__1(x_13, x_4);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_17 = lean_ctor_get(x_14, 1);
x_18 = lean_ctor_get(x_14, 0);
lean_dec(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
x_20 = l_Lean_MetavarContext_getDecl(x_19, x_13);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = l_Lean_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__42(x_1, x_2, x_22);
x_24 = lean_box(x_23);
lean_ctor_set(x_14, 0, x_24);
return x_14;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; 
x_25 = lean_ctor_get(x_14, 1);
lean_inc(x_25);
lean_dec(x_14);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
x_27 = l_Lean_MetavarContext_getDecl(x_26, x_13);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = l_Lean_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__42(x_1, x_2, x_29);
x_31 = lean_box(x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_25);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_13);
x_33 = lean_ctor_get(x_14, 1);
lean_inc(x_33);
lean_dec(x_14);
x_34 = lean_ctor_get(x_15, 0);
lean_inc(x_34);
lean_dec(x_15);
x_35 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__39(x_1, x_2, x_34, x_33);
return x_35;
}
}
case 5:
{
lean_object* x_36; uint8_t x_37; 
x_36 = l_Lean_Expr_getAppFn(x_3);
x_37 = l_Lean_Expr_isMVar(x_36);
if (x_37 == 0)
{
lean_object* x_38; 
lean_dec(x_36);
x_38 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at_Lean_Meta_getFVarSetToGeneralize___spec__41(x_1, x_2, x_3, x_4);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
lean_inc(x_3);
x_39 = l_Lean_instantiateMVars___at___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___spec__7(x_3, x_4);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = l_Lean_Expr_getAppFn(x_40);
x_43 = lean_expr_eqv(x_42, x_36);
lean_dec(x_36);
lean_dec(x_42);
if (x_43 == 0)
{
lean_dec(x_3);
x_3 = x_40;
x_4 = x_41;
goto _start;
}
else
{
lean_object* x_45; 
lean_dec(x_40);
x_45 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at_Lean_Meta_getFVarSetToGeneralize___spec__41(x_1, x_2, x_3, x_41);
return x_45;
}
}
}
case 6:
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_46 = lean_ctor_get(x_3, 1);
lean_inc(x_46);
x_47 = lean_ctor_get(x_3, 2);
lean_inc(x_47);
lean_dec(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_48 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__39(x_1, x_2, x_46, x_4);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_unbox(x_49);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; 
lean_dec(x_49);
x_51 = lean_ctor_get(x_48, 1);
lean_inc(x_51);
lean_dec(x_48);
x_52 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__39(x_1, x_2, x_47, x_51);
return x_52;
}
else
{
uint8_t x_53; 
lean_dec(x_47);
lean_dec(x_2);
lean_dec(x_1);
x_53 = !lean_is_exclusive(x_48);
if (x_53 == 0)
{
lean_object* x_54; 
x_54 = lean_ctor_get(x_48, 0);
lean_dec(x_54);
return x_48;
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_48, 1);
lean_inc(x_55);
lean_dec(x_48);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_49);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
case 7:
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_57 = lean_ctor_get(x_3, 1);
lean_inc(x_57);
x_58 = lean_ctor_get(x_3, 2);
lean_inc(x_58);
lean_dec(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_59 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__39(x_1, x_2, x_57, x_4);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_unbox(x_60);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; 
lean_dec(x_60);
x_62 = lean_ctor_get(x_59, 1);
lean_inc(x_62);
lean_dec(x_59);
x_63 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__39(x_1, x_2, x_58, x_62);
return x_63;
}
else
{
uint8_t x_64; 
lean_dec(x_58);
lean_dec(x_2);
lean_dec(x_1);
x_64 = !lean_is_exclusive(x_59);
if (x_64 == 0)
{
lean_object* x_65; 
x_65 = lean_ctor_get(x_59, 0);
lean_dec(x_65);
return x_59;
}
else
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_59, 1);
lean_inc(x_66);
lean_dec(x_59);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_60);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
case 8:
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_68 = lean_ctor_get(x_3, 1);
lean_inc(x_68);
x_69 = lean_ctor_get(x_3, 2);
lean_inc(x_69);
x_70 = lean_ctor_get(x_3, 3);
lean_inc(x_70);
lean_dec(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_71 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__39(x_1, x_2, x_68, x_4);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_unbox(x_72);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
lean_dec(x_72);
x_74 = lean_ctor_get(x_71, 1);
lean_inc(x_74);
lean_dec(x_71);
lean_inc(x_2);
lean_inc(x_1);
x_75 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__39(x_1, x_2, x_69, x_74);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_unbox(x_76);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; 
lean_dec(x_76);
x_78 = lean_ctor_get(x_75, 1);
lean_inc(x_78);
lean_dec(x_75);
x_79 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__39(x_1, x_2, x_70, x_78);
return x_79;
}
else
{
uint8_t x_80; 
lean_dec(x_70);
lean_dec(x_2);
lean_dec(x_1);
x_80 = !lean_is_exclusive(x_75);
if (x_80 == 0)
{
lean_object* x_81; 
x_81 = lean_ctor_get(x_75, 0);
lean_dec(x_81);
return x_75;
}
else
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_ctor_get(x_75, 1);
lean_inc(x_82);
lean_dec(x_75);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_76);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
}
else
{
uint8_t x_84; 
lean_dec(x_70);
lean_dec(x_69);
lean_dec(x_2);
lean_dec(x_1);
x_84 = !lean_is_exclusive(x_71);
if (x_84 == 0)
{
lean_object* x_85; 
x_85 = lean_ctor_get(x_71, 0);
lean_dec(x_85);
return x_71;
}
else
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_71, 1);
lean_inc(x_86);
lean_dec(x_71);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_72);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
}
case 10:
{
lean_object* x_88; lean_object* x_89; 
x_88 = lean_ctor_get(x_3, 1);
lean_inc(x_88);
lean_dec(x_3);
x_89 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__39(x_1, x_2, x_88, x_4);
return x_89;
}
case 11:
{
lean_object* x_90; lean_object* x_91; 
x_90 = lean_ctor_get(x_3, 2);
lean_inc(x_90);
lean_dec(x_3);
x_91 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__39(x_1, x_2, x_90, x_4);
return x_91;
}
default: 
{
uint8_t x_92; lean_object* x_93; lean_object* x_94; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_92 = 0;
x_93 = lean_box(x_92);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_4);
return x_94;
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
x_5 = l_Lean_RBNode_findCore___at_Lean_Meta_mkGeneralizationForbiddenSet_visit___spec__1(x_1, x_4);
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
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
lean_dec(x_2);
lean_inc(x_12);
x_13 = l_Lean_getExprMVarAssignment_x3f___at___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___spec__1(x_12, x_3);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_16 = lean_ctor_get(x_13, 1);
x_17 = lean_ctor_get(x_13, 0);
lean_dec(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
x_19 = l_Lean_MetavarContext_getDecl(x_18, x_12);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at_Lean_Meta_getFVarSetToGeneralize___spec__2___at_Lean_Meta_getFVarSetToGeneralize___spec__10___closed__1;
x_23 = l_Lean_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__42(x_22, x_1, x_21);
x_24 = lean_box(x_23);
lean_ctor_set(x_13, 0, x_24);
return x_13;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; 
x_25 = lean_ctor_get(x_13, 1);
lean_inc(x_25);
lean_dec(x_13);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
x_27 = l_Lean_MetavarContext_getDecl(x_26, x_12);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at_Lean_Meta_getFVarSetToGeneralize___spec__2___at_Lean_Meta_getFVarSetToGeneralize___spec__10___closed__1;
x_31 = l_Lean_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__42(x_30, x_1, x_29);
x_32 = lean_box(x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_25);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_12);
x_34 = lean_ctor_get(x_13, 1);
lean_inc(x_34);
lean_dec(x_13);
x_35 = lean_ctor_get(x_14, 0);
lean_inc(x_35);
lean_dec(x_14);
x_36 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__39___at_Lean_Meta_getFVarSetToGeneralize___spec__47(x_1, x_35, x_34);
return x_36;
}
}
case 5:
{
lean_object* x_37; uint8_t x_38; 
x_37 = l_Lean_Expr_getAppFn(x_2);
x_38 = l_Lean_Expr_isMVar(x_37);
if (x_38 == 0)
{
lean_object* x_39; 
lean_dec(x_37);
x_39 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at_Lean_Meta_getFVarSetToGeneralize___spec__41___at_Lean_Meta_getFVarSetToGeneralize___spec__49(x_1, x_2, x_3);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
lean_inc(x_2);
x_40 = l_Lean_instantiateMVars___at___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___spec__7(x_2, x_3);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = l_Lean_Expr_getAppFn(x_41);
x_44 = lean_expr_eqv(x_43, x_37);
lean_dec(x_37);
lean_dec(x_43);
if (x_44 == 0)
{
lean_dec(x_2);
x_2 = x_41;
x_3 = x_42;
goto _start;
}
else
{
lean_object* x_46; 
lean_dec(x_41);
x_46 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at_Lean_Meta_getFVarSetToGeneralize___spec__41___at_Lean_Meta_getFVarSetToGeneralize___spec__49(x_1, x_2, x_42);
return x_46;
}
}
}
case 6:
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_47 = lean_ctor_get(x_2, 1);
lean_inc(x_47);
x_48 = lean_ctor_get(x_2, 2);
lean_inc(x_48);
lean_dec(x_2);
lean_inc(x_1);
x_49 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__39___at_Lean_Meta_getFVarSetToGeneralize___spec__47(x_1, x_47, x_3);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_unbox(x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
lean_dec(x_50);
x_52 = lean_ctor_get(x_49, 1);
lean_inc(x_52);
lean_dec(x_49);
x_53 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__39___at_Lean_Meta_getFVarSetToGeneralize___spec__47(x_1, x_48, x_52);
return x_53;
}
else
{
uint8_t x_54; 
lean_dec(x_48);
lean_dec(x_1);
x_54 = !lean_is_exclusive(x_49);
if (x_54 == 0)
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_49, 0);
lean_dec(x_55);
return x_49;
}
else
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_49, 1);
lean_inc(x_56);
lean_dec(x_49);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_50);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
case 7:
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_58 = lean_ctor_get(x_2, 1);
lean_inc(x_58);
x_59 = lean_ctor_get(x_2, 2);
lean_inc(x_59);
lean_dec(x_2);
lean_inc(x_1);
x_60 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__39___at_Lean_Meta_getFVarSetToGeneralize___spec__47(x_1, x_58, x_3);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_unbox(x_61);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_61);
x_63 = lean_ctor_get(x_60, 1);
lean_inc(x_63);
lean_dec(x_60);
x_64 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__39___at_Lean_Meta_getFVarSetToGeneralize___spec__47(x_1, x_59, x_63);
return x_64;
}
else
{
uint8_t x_65; 
lean_dec(x_59);
lean_dec(x_1);
x_65 = !lean_is_exclusive(x_60);
if (x_65 == 0)
{
lean_object* x_66; 
x_66 = lean_ctor_get(x_60, 0);
lean_dec(x_66);
return x_60;
}
else
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_60, 1);
lean_inc(x_67);
lean_dec(x_60);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_61);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
case 8:
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_69 = lean_ctor_get(x_2, 1);
lean_inc(x_69);
x_70 = lean_ctor_get(x_2, 2);
lean_inc(x_70);
x_71 = lean_ctor_get(x_2, 3);
lean_inc(x_71);
lean_dec(x_2);
lean_inc(x_1);
x_72 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__39___at_Lean_Meta_getFVarSetToGeneralize___spec__47(x_1, x_69, x_3);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_unbox(x_73);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; 
lean_dec(x_73);
x_75 = lean_ctor_get(x_72, 1);
lean_inc(x_75);
lean_dec(x_72);
lean_inc(x_1);
x_76 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__39___at_Lean_Meta_getFVarSetToGeneralize___spec__47(x_1, x_70, x_75);
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
x_80 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__39___at_Lean_Meta_getFVarSetToGeneralize___spec__47(x_1, x_71, x_79);
return x_80;
}
else
{
uint8_t x_81; 
lean_dec(x_71);
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
else
{
uint8_t x_85; 
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_1);
x_85 = !lean_is_exclusive(x_72);
if (x_85 == 0)
{
lean_object* x_86; 
x_86 = lean_ctor_get(x_72, 0);
lean_dec(x_86);
return x_72;
}
else
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_72, 1);
lean_inc(x_87);
lean_dec(x_72);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_73);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
case 10:
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_ctor_get(x_2, 1);
lean_inc(x_89);
lean_dec(x_2);
x_90 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__39___at_Lean_Meta_getFVarSetToGeneralize___spec__47(x_1, x_89, x_3);
return x_90;
}
case 11:
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_ctor_get(x_2, 2);
lean_inc(x_91);
lean_dec(x_2);
x_92 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__39___at_Lean_Meta_getFVarSetToGeneralize___spec__47(x_1, x_91, x_3);
return x_92;
}
default: 
{
uint8_t x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_2);
lean_dec(x_1);
x_93 = 0;
x_94 = lean_box(x_93);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_3);
return x_95;
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
x_8 = l_Lean_PersistentArray_anyMAux___at_Lean_Meta_getFVarSetToGeneralize___spec__54(x_1, x_2, x_7);
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
x_13 = l_Lean_RBNode_findCore___rarg(x_1, x_2, x_12);
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
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyMAux___at_Lean_Meta_getFVarSetToGeneralize___spec__54(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
size_t x_9; size_t x_10; uint8_t x_11; 
x_9 = 0;
x_10 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_11 = l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__55(x_1, x_2, x_4, x_9, x_10);
lean_dec(x_4);
return x_11;
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_3, 0);
lean_inc(x_12);
lean_dec(x_3);
x_13 = lean_array_get_size(x_12);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_lt(x_14, x_13);
if (x_15 == 0)
{
uint8_t x_16; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_2);
lean_dec(x_1);
x_16 = 0;
return x_16;
}
else
{
size_t x_17; size_t x_18; uint8_t x_19; 
x_17 = 0;
x_18 = lean_usize_of_nat(x_13);
lean_dec(x_13);
x_19 = l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__56(x_1, x_2, x_12, x_17, x_18);
lean_dec(x_12);
return x_19;
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
x_13 = l_Lean_RBNode_findCore___rarg(x_1, x_2, x_12);
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
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__53(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_5 = l_Lean_PersistentArray_anyMAux___at_Lean_Meta_getFVarSetToGeneralize___spec__54(x_1, x_2, x_4);
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
size_t x_11; size_t x_12; uint8_t x_13; 
x_11 = 0;
x_12 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_13 = l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__57(x_1, x_2, x_6, x_11, x_12);
lean_dec(x_6);
return x_13;
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
x_6 = l_Lean_RBNode_findCore___rarg(x_1, x_2, x_5);
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
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_3, 0);
lean_inc(x_13);
lean_dec(x_3);
lean_inc(x_13);
x_14 = l_Lean_getExprMVarAssignment_x3f___at___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___spec__1(x_13, x_4);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_17 = lean_ctor_get(x_14, 1);
x_18 = lean_ctor_get(x_14, 0);
lean_dec(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
x_20 = l_Lean_MetavarContext_getDecl(x_19, x_13);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = l_Lean_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__53(x_1, x_2, x_22);
x_24 = lean_box(x_23);
lean_ctor_set(x_14, 0, x_24);
return x_14;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; 
x_25 = lean_ctor_get(x_14, 1);
lean_inc(x_25);
lean_dec(x_14);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
x_27 = l_Lean_MetavarContext_getDecl(x_26, x_13);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = l_Lean_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__53(x_1, x_2, x_29);
x_31 = lean_box(x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_25);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_13);
x_33 = lean_ctor_get(x_14, 1);
lean_inc(x_33);
lean_dec(x_14);
x_34 = lean_ctor_get(x_15, 0);
lean_inc(x_34);
lean_dec(x_15);
x_35 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__50(x_1, x_2, x_34, x_33);
return x_35;
}
}
case 5:
{
lean_object* x_36; uint8_t x_37; 
x_36 = l_Lean_Expr_getAppFn(x_3);
x_37 = l_Lean_Expr_isMVar(x_36);
if (x_37 == 0)
{
lean_object* x_38; 
lean_dec(x_36);
x_38 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at_Lean_Meta_getFVarSetToGeneralize___spec__52(x_1, x_2, x_3, x_4);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
lean_inc(x_3);
x_39 = l_Lean_instantiateMVars___at___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___spec__7(x_3, x_4);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = l_Lean_Expr_getAppFn(x_40);
x_43 = lean_expr_eqv(x_42, x_36);
lean_dec(x_36);
lean_dec(x_42);
if (x_43 == 0)
{
lean_dec(x_3);
x_3 = x_40;
x_4 = x_41;
goto _start;
}
else
{
lean_object* x_45; 
lean_dec(x_40);
x_45 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at_Lean_Meta_getFVarSetToGeneralize___spec__52(x_1, x_2, x_3, x_41);
return x_45;
}
}
}
case 6:
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_46 = lean_ctor_get(x_3, 1);
lean_inc(x_46);
x_47 = lean_ctor_get(x_3, 2);
lean_inc(x_47);
lean_dec(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_48 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__50(x_1, x_2, x_46, x_4);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_unbox(x_49);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; 
lean_dec(x_49);
x_51 = lean_ctor_get(x_48, 1);
lean_inc(x_51);
lean_dec(x_48);
x_52 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__50(x_1, x_2, x_47, x_51);
return x_52;
}
else
{
uint8_t x_53; 
lean_dec(x_47);
lean_dec(x_2);
lean_dec(x_1);
x_53 = !lean_is_exclusive(x_48);
if (x_53 == 0)
{
lean_object* x_54; 
x_54 = lean_ctor_get(x_48, 0);
lean_dec(x_54);
return x_48;
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_48, 1);
lean_inc(x_55);
lean_dec(x_48);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_49);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
case 7:
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_57 = lean_ctor_get(x_3, 1);
lean_inc(x_57);
x_58 = lean_ctor_get(x_3, 2);
lean_inc(x_58);
lean_dec(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_59 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__50(x_1, x_2, x_57, x_4);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_unbox(x_60);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; 
lean_dec(x_60);
x_62 = lean_ctor_get(x_59, 1);
lean_inc(x_62);
lean_dec(x_59);
x_63 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__50(x_1, x_2, x_58, x_62);
return x_63;
}
else
{
uint8_t x_64; 
lean_dec(x_58);
lean_dec(x_2);
lean_dec(x_1);
x_64 = !lean_is_exclusive(x_59);
if (x_64 == 0)
{
lean_object* x_65; 
x_65 = lean_ctor_get(x_59, 0);
lean_dec(x_65);
return x_59;
}
else
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_59, 1);
lean_inc(x_66);
lean_dec(x_59);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_60);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
case 8:
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_68 = lean_ctor_get(x_3, 1);
lean_inc(x_68);
x_69 = lean_ctor_get(x_3, 2);
lean_inc(x_69);
x_70 = lean_ctor_get(x_3, 3);
lean_inc(x_70);
lean_dec(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_71 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__50(x_1, x_2, x_68, x_4);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_unbox(x_72);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
lean_dec(x_72);
x_74 = lean_ctor_get(x_71, 1);
lean_inc(x_74);
lean_dec(x_71);
lean_inc(x_2);
lean_inc(x_1);
x_75 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__50(x_1, x_2, x_69, x_74);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_unbox(x_76);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; 
lean_dec(x_76);
x_78 = lean_ctor_get(x_75, 1);
lean_inc(x_78);
lean_dec(x_75);
x_79 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__50(x_1, x_2, x_70, x_78);
return x_79;
}
else
{
uint8_t x_80; 
lean_dec(x_70);
lean_dec(x_2);
lean_dec(x_1);
x_80 = !lean_is_exclusive(x_75);
if (x_80 == 0)
{
lean_object* x_81; 
x_81 = lean_ctor_get(x_75, 0);
lean_dec(x_81);
return x_75;
}
else
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_ctor_get(x_75, 1);
lean_inc(x_82);
lean_dec(x_75);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_76);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
}
else
{
uint8_t x_84; 
lean_dec(x_70);
lean_dec(x_69);
lean_dec(x_2);
lean_dec(x_1);
x_84 = !lean_is_exclusive(x_71);
if (x_84 == 0)
{
lean_object* x_85; 
x_85 = lean_ctor_get(x_71, 0);
lean_dec(x_85);
return x_71;
}
else
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_71, 1);
lean_inc(x_86);
lean_dec(x_71);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_72);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
}
case 10:
{
lean_object* x_88; lean_object* x_89; 
x_88 = lean_ctor_get(x_3, 1);
lean_inc(x_88);
lean_dec(x_3);
x_89 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__50(x_1, x_2, x_88, x_4);
return x_89;
}
case 11:
{
lean_object* x_90; lean_object* x_91; 
x_90 = lean_ctor_get(x_3, 2);
lean_inc(x_90);
lean_dec(x_3);
x_91 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__50(x_1, x_2, x_90, x_4);
return x_91;
}
default: 
{
uint8_t x_92; lean_object* x_93; lean_object* x_94; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_92 = 0;
x_93 = lean_box(x_92);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_4);
return x_94;
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
x_5 = l_Lean_RBNode_findCore___at_Lean_Meta_mkGeneralizationForbiddenSet_visit___spec__1(x_1, x_4);
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
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
lean_dec(x_2);
lean_inc(x_12);
x_13 = l_Lean_getExprMVarAssignment_x3f___at___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___spec__1(x_12, x_3);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_16 = lean_ctor_get(x_13, 1);
x_17 = lean_ctor_get(x_13, 0);
lean_dec(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
x_19 = l_Lean_MetavarContext_getDecl(x_18, x_12);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at_Lean_Meta_getFVarSetToGeneralize___spec__2___at_Lean_Meta_getFVarSetToGeneralize___spec__10___closed__1;
x_23 = l_Lean_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__53(x_22, x_1, x_21);
x_24 = lean_box(x_23);
lean_ctor_set(x_13, 0, x_24);
return x_13;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; 
x_25 = lean_ctor_get(x_13, 1);
lean_inc(x_25);
lean_dec(x_13);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
x_27 = l_Lean_MetavarContext_getDecl(x_26, x_12);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at_Lean_Meta_getFVarSetToGeneralize___spec__2___at_Lean_Meta_getFVarSetToGeneralize___spec__10___closed__1;
x_31 = l_Lean_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__53(x_30, x_1, x_29);
x_32 = lean_box(x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_25);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_12);
x_34 = lean_ctor_get(x_13, 1);
lean_inc(x_34);
lean_dec(x_13);
x_35 = lean_ctor_get(x_14, 0);
lean_inc(x_35);
lean_dec(x_14);
x_36 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__50___at_Lean_Meta_getFVarSetToGeneralize___spec__58(x_1, x_35, x_34);
return x_36;
}
}
case 5:
{
lean_object* x_37; uint8_t x_38; 
x_37 = l_Lean_Expr_getAppFn(x_2);
x_38 = l_Lean_Expr_isMVar(x_37);
if (x_38 == 0)
{
lean_object* x_39; 
lean_dec(x_37);
x_39 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at_Lean_Meta_getFVarSetToGeneralize___spec__52___at_Lean_Meta_getFVarSetToGeneralize___spec__60(x_1, x_2, x_3);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
lean_inc(x_2);
x_40 = l_Lean_instantiateMVars___at___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___spec__7(x_2, x_3);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = l_Lean_Expr_getAppFn(x_41);
x_44 = lean_expr_eqv(x_43, x_37);
lean_dec(x_37);
lean_dec(x_43);
if (x_44 == 0)
{
lean_dec(x_2);
x_2 = x_41;
x_3 = x_42;
goto _start;
}
else
{
lean_object* x_46; 
lean_dec(x_41);
x_46 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at_Lean_Meta_getFVarSetToGeneralize___spec__52___at_Lean_Meta_getFVarSetToGeneralize___spec__60(x_1, x_2, x_42);
return x_46;
}
}
}
case 6:
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_47 = lean_ctor_get(x_2, 1);
lean_inc(x_47);
x_48 = lean_ctor_get(x_2, 2);
lean_inc(x_48);
lean_dec(x_2);
lean_inc(x_1);
x_49 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__50___at_Lean_Meta_getFVarSetToGeneralize___spec__58(x_1, x_47, x_3);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_unbox(x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
lean_dec(x_50);
x_52 = lean_ctor_get(x_49, 1);
lean_inc(x_52);
lean_dec(x_49);
x_53 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__50___at_Lean_Meta_getFVarSetToGeneralize___spec__58(x_1, x_48, x_52);
return x_53;
}
else
{
uint8_t x_54; 
lean_dec(x_48);
lean_dec(x_1);
x_54 = !lean_is_exclusive(x_49);
if (x_54 == 0)
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_49, 0);
lean_dec(x_55);
return x_49;
}
else
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_49, 1);
lean_inc(x_56);
lean_dec(x_49);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_50);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
case 7:
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_58 = lean_ctor_get(x_2, 1);
lean_inc(x_58);
x_59 = lean_ctor_get(x_2, 2);
lean_inc(x_59);
lean_dec(x_2);
lean_inc(x_1);
x_60 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__50___at_Lean_Meta_getFVarSetToGeneralize___spec__58(x_1, x_58, x_3);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_unbox(x_61);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_61);
x_63 = lean_ctor_get(x_60, 1);
lean_inc(x_63);
lean_dec(x_60);
x_64 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__50___at_Lean_Meta_getFVarSetToGeneralize___spec__58(x_1, x_59, x_63);
return x_64;
}
else
{
uint8_t x_65; 
lean_dec(x_59);
lean_dec(x_1);
x_65 = !lean_is_exclusive(x_60);
if (x_65 == 0)
{
lean_object* x_66; 
x_66 = lean_ctor_get(x_60, 0);
lean_dec(x_66);
return x_60;
}
else
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_60, 1);
lean_inc(x_67);
lean_dec(x_60);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_61);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
case 8:
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_69 = lean_ctor_get(x_2, 1);
lean_inc(x_69);
x_70 = lean_ctor_get(x_2, 2);
lean_inc(x_70);
x_71 = lean_ctor_get(x_2, 3);
lean_inc(x_71);
lean_dec(x_2);
lean_inc(x_1);
x_72 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__50___at_Lean_Meta_getFVarSetToGeneralize___spec__58(x_1, x_69, x_3);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_unbox(x_73);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; 
lean_dec(x_73);
x_75 = lean_ctor_get(x_72, 1);
lean_inc(x_75);
lean_dec(x_72);
lean_inc(x_1);
x_76 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__50___at_Lean_Meta_getFVarSetToGeneralize___spec__58(x_1, x_70, x_75);
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
x_80 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__50___at_Lean_Meta_getFVarSetToGeneralize___spec__58(x_1, x_71, x_79);
return x_80;
}
else
{
uint8_t x_81; 
lean_dec(x_71);
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
else
{
uint8_t x_85; 
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_1);
x_85 = !lean_is_exclusive(x_72);
if (x_85 == 0)
{
lean_object* x_86; 
x_86 = lean_ctor_get(x_72, 0);
lean_dec(x_86);
return x_72;
}
else
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_72, 1);
lean_inc(x_87);
lean_dec(x_72);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_73);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
case 10:
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_ctor_get(x_2, 1);
lean_inc(x_89);
lean_dec(x_2);
x_90 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__50___at_Lean_Meta_getFVarSetToGeneralize___spec__58(x_1, x_89, x_3);
return x_90;
}
case 11:
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_ctor_get(x_2, 2);
lean_inc(x_91);
lean_dec(x_2);
x_92 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__50___at_Lean_Meta_getFVarSetToGeneralize___spec__58(x_1, x_91, x_3);
return x_92;
}
default: 
{
uint8_t x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_2);
lean_dec(x_1);
x_93 = 0;
x_94 = lean_box(x_93);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_3);
return x_95;
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
x_21 = l_Lean_PersistentArray_forInAux___at_Lean_Meta_getFVarSetToGeneralize___spec__62(x_1, x_2, x_3, x_4, x_17, x_19, x_10, x_11, x_12, x_13, x_14);
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
x_35 = l_Lean_PersistentArray_forInAux___at_Lean_Meta_getFVarSetToGeneralize___spec__62(x_1, x_2, x_3, x_4, x_17, x_34, x_10, x_11, x_12, x_13, x_14);
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
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_65; lean_object* x_70; lean_object* x_199; 
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
x_199 = l_Lean_RBNode_findCore___at_Lean_Meta_mkGeneralizationForbiddenSet_visit___spec__1(x_1, x_52);
if (lean_obj_tag(x_199) == 0)
{
uint8_t x_200; 
x_200 = l_Lean_LocalDecl_isAuxDecl(x_48);
if (x_200 == 0)
{
uint8_t x_201; uint8_t x_202; 
x_201 = l_Lean_LocalDecl_binderInfo(x_48);
x_202 = l_Lean_BinderInfo_isInstImplicit(x_201);
if (x_202 == 0)
{
if (x_2 == 0)
{
lean_object* x_203; 
x_203 = lean_box(0);
x_70 = x_203;
goto block_198;
}
else
{
uint8_t x_204; 
x_204 = l_Lean_LocalDecl_isLet(x_48);
if (x_204 == 0)
{
lean_object* x_205; 
x_205 = lean_box(0);
x_70 = x_205;
goto block_198;
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; 
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_48);
x_206 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_206, 0, x_49);
lean_ctor_set(x_206, 1, x_50);
x_207 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_207, 0, x_206);
x_208 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_208, 0, x_207);
lean_ctor_set(x_208, 1, x_13);
x_27 = x_208;
goto block_43;
}
}
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; 
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_48);
x_209 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_209, 0, x_49);
lean_ctor_set(x_209, 1, x_50);
x_210 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_210, 0, x_209);
x_211 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_211, 0, x_210);
lean_ctor_set(x_211, 1, x_13);
x_27 = x_211;
goto block_43;
}
}
else
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; 
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_48);
x_212 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_212, 0, x_49);
lean_ctor_set(x_212, 1, x_50);
x_213 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_213, 0, x_212);
x_214 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_214, 0, x_213);
lean_ctor_set(x_214, 1, x_13);
x_27 = x_214;
goto block_43;
}
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; 
lean_dec(x_199);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_48);
x_215 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_215, 0, x_49);
lean_ctor_set(x_215, 1, x_50);
x_216 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_216, 0, x_215);
x_217 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_217, 0, x_216);
lean_ctor_set(x_217, 1, x_13);
x_27 = x_217;
goto block_43;
}
block_64:
{
if (x_53 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_52);
if (lean_is_scalar(x_51)) {
 x_55 = lean_alloc_ctor(0, 2, 0);
} else {
 x_55 = x_51;
}
lean_ctor_set(x_55, 0, x_49);
lean_ctor_set(x_55, 1, x_50);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_55);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_54);
x_27 = x_57;
goto block_43;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_58 = lean_box(0);
lean_inc(x_52);
x_59 = l_Lean_RBNode_insert___at_Lean_FVarIdSet_insert___spec__1(x_49, x_52, x_58);
x_60 = l_Lean_RBNode_insert___at_Lean_FVarIdSet_insert___spec__1(x_50, x_52, x_58);
if (lean_is_scalar(x_51)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_51;
}
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_61);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_54);
x_27 = x_63;
goto block_43;
}
}
block_69:
{
lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
x_68 = lean_unbox(x_66);
lean_dec(x_66);
x_53 = x_68;
x_54 = x_67;
goto block_64;
}
block_198:
{
lean_dec(x_70);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_71 = lean_ctor_get(x_48, 3);
lean_inc(x_71);
lean_dec(x_48);
x_72 = lean_st_ref_get(x_10, x_13);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
x_75 = lean_ctor_get(x_73, 0);
lean_inc(x_75);
lean_dec(x_73);
x_76 = l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1;
lean_inc(x_75);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_75);
x_78 = l_Lean_Expr_hasFVar(x_71);
if (x_78 == 0)
{
uint8_t x_79; 
x_79 = l_Lean_Expr_hasMVar(x_71);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; 
lean_dec(x_77);
lean_dec(x_71);
x_80 = lean_st_ref_take(x_10, x_74);
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec(x_80);
x_83 = !lean_is_exclusive(x_81);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_84 = lean_ctor_get(x_81, 0);
lean_dec(x_84);
lean_ctor_set(x_81, 0, x_75);
x_85 = lean_st_ref_set(x_10, x_81, x_82);
x_86 = !lean_is_exclusive(x_85);
if (x_86 == 0)
{
lean_object* x_87; uint8_t x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_85, 0);
lean_dec(x_87);
x_88 = 0;
x_89 = lean_box(x_88);
lean_ctor_set(x_85, 0, x_89);
x_65 = x_85;
goto block_69;
}
else
{
lean_object* x_90; uint8_t x_91; lean_object* x_92; lean_object* x_93; 
x_90 = lean_ctor_get(x_85, 1);
lean_inc(x_90);
lean_dec(x_85);
x_91 = 0;
x_92 = lean_box(x_91);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_90);
x_65 = x_93;
goto block_69;
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; lean_object* x_102; lean_object* x_103; 
x_94 = lean_ctor_get(x_81, 1);
x_95 = lean_ctor_get(x_81, 2);
x_96 = lean_ctor_get(x_81, 3);
lean_inc(x_96);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_81);
x_97 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_97, 0, x_75);
lean_ctor_set(x_97, 1, x_94);
lean_ctor_set(x_97, 2, x_95);
lean_ctor_set(x_97, 3, x_96);
x_98 = lean_st_ref_set(x_10, x_97, x_82);
x_99 = lean_ctor_get(x_98, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 lean_ctor_release(x_98, 1);
 x_100 = x_98;
} else {
 lean_dec_ref(x_98);
 x_100 = lean_box(0);
}
x_101 = 0;
x_102 = lean_box(x_101);
if (lean_is_scalar(x_100)) {
 x_103 = lean_alloc_ctor(0, 2, 0);
} else {
 x_103 = x_100;
}
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_99);
x_65 = x_103;
goto block_69;
}
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_111; 
lean_dec(x_75);
lean_inc(x_50);
x_104 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__1___at_Lean_Meta_getFVarSetToGeneralize___spec__9(x_50, x_71, x_77);
x_105 = lean_ctor_get(x_104, 1);
lean_inc(x_105);
x_106 = lean_ctor_get(x_104, 0);
lean_inc(x_106);
lean_dec(x_104);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
lean_dec(x_105);
x_108 = lean_st_ref_take(x_10, x_74);
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
lean_dec(x_108);
x_111 = !lean_is_exclusive(x_109);
if (x_111 == 0)
{
lean_object* x_112; lean_object* x_113; uint8_t x_114; 
x_112 = lean_ctor_get(x_109, 0);
lean_dec(x_112);
lean_ctor_set(x_109, 0, x_107);
x_113 = lean_st_ref_set(x_10, x_109, x_110);
x_114 = !lean_is_exclusive(x_113);
if (x_114 == 0)
{
lean_object* x_115; 
x_115 = lean_ctor_get(x_113, 0);
lean_dec(x_115);
lean_ctor_set(x_113, 0, x_106);
x_65 = x_113;
goto block_69;
}
else
{
lean_object* x_116; lean_object* x_117; 
x_116 = lean_ctor_get(x_113, 1);
lean_inc(x_116);
lean_dec(x_113);
x_117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_117, 0, x_106);
lean_ctor_set(x_117, 1, x_116);
x_65 = x_117;
goto block_69;
}
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_118 = lean_ctor_get(x_109, 1);
x_119 = lean_ctor_get(x_109, 2);
x_120 = lean_ctor_get(x_109, 3);
lean_inc(x_120);
lean_inc(x_119);
lean_inc(x_118);
lean_dec(x_109);
x_121 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_121, 0, x_107);
lean_ctor_set(x_121, 1, x_118);
lean_ctor_set(x_121, 2, x_119);
lean_ctor_set(x_121, 3, x_120);
x_122 = lean_st_ref_set(x_10, x_121, x_110);
x_123 = lean_ctor_get(x_122, 1);
lean_inc(x_123);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 lean_ctor_release(x_122, 1);
 x_124 = x_122;
} else {
 lean_dec_ref(x_122);
 x_124 = lean_box(0);
}
if (lean_is_scalar(x_124)) {
 x_125 = lean_alloc_ctor(0, 2, 0);
} else {
 x_125 = x_124;
}
lean_ctor_set(x_125, 0, x_106);
lean_ctor_set(x_125, 1, x_123);
x_65 = x_125;
goto block_69;
}
}
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_133; 
lean_dec(x_75);
lean_inc(x_50);
x_126 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__12___at_Lean_Meta_getFVarSetToGeneralize___spec__20(x_50, x_71, x_77);
x_127 = lean_ctor_get(x_126, 1);
lean_inc(x_127);
x_128 = lean_ctor_get(x_126, 0);
lean_inc(x_128);
lean_dec(x_126);
x_129 = lean_ctor_get(x_127, 1);
lean_inc(x_129);
lean_dec(x_127);
x_130 = lean_st_ref_take(x_10, x_74);
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_130, 1);
lean_inc(x_132);
lean_dec(x_130);
x_133 = !lean_is_exclusive(x_131);
if (x_133 == 0)
{
lean_object* x_134; lean_object* x_135; uint8_t x_136; 
x_134 = lean_ctor_get(x_131, 0);
lean_dec(x_134);
lean_ctor_set(x_131, 0, x_129);
x_135 = lean_st_ref_set(x_10, x_131, x_132);
x_136 = !lean_is_exclusive(x_135);
if (x_136 == 0)
{
lean_object* x_137; 
x_137 = lean_ctor_get(x_135, 0);
lean_dec(x_137);
lean_ctor_set(x_135, 0, x_128);
x_65 = x_135;
goto block_69;
}
else
{
lean_object* x_138; lean_object* x_139; 
x_138 = lean_ctor_get(x_135, 1);
lean_inc(x_138);
lean_dec(x_135);
x_139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_139, 0, x_128);
lean_ctor_set(x_139, 1, x_138);
x_65 = x_139;
goto block_69;
}
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_140 = lean_ctor_get(x_131, 1);
x_141 = lean_ctor_get(x_131, 2);
x_142 = lean_ctor_get(x_131, 3);
lean_inc(x_142);
lean_inc(x_141);
lean_inc(x_140);
lean_dec(x_131);
x_143 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_143, 0, x_129);
lean_ctor_set(x_143, 1, x_140);
lean_ctor_set(x_143, 2, x_141);
lean_ctor_set(x_143, 3, x_142);
x_144 = lean_st_ref_set(x_10, x_143, x_132);
x_145 = lean_ctor_get(x_144, 1);
lean_inc(x_145);
if (lean_is_exclusive(x_144)) {
 lean_ctor_release(x_144, 0);
 lean_ctor_release(x_144, 1);
 x_146 = x_144;
} else {
 lean_dec_ref(x_144);
 x_146 = lean_box(0);
}
if (lean_is_scalar(x_146)) {
 x_147 = lean_alloc_ctor(0, 2, 0);
} else {
 x_147 = x_146;
}
lean_ctor_set(x_147, 0, x_128);
lean_ctor_set(x_147, 1, x_145);
x_65 = x_147;
goto block_69;
}
}
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; uint8_t x_153; lean_object* x_154; uint8_t x_170; lean_object* x_171; lean_object* x_184; lean_object* x_185; lean_object* x_186; uint8_t x_187; 
x_148 = lean_ctor_get(x_48, 3);
lean_inc(x_148);
x_149 = lean_ctor_get(x_48, 4);
lean_inc(x_149);
lean_dec(x_48);
x_150 = lean_st_ref_get(x_10, x_13);
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_150, 1);
lean_inc(x_152);
lean_dec(x_150);
x_184 = lean_ctor_get(x_151, 0);
lean_inc(x_184);
lean_dec(x_151);
x_185 = l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1;
x_186 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_186, 0, x_185);
lean_ctor_set(x_186, 1, x_184);
x_187 = l_Lean_Expr_hasFVar(x_148);
if (x_187 == 0)
{
uint8_t x_188; 
x_188 = l_Lean_Expr_hasMVar(x_148);
if (x_188 == 0)
{
uint8_t x_189; 
lean_dec(x_148);
x_189 = 0;
x_170 = x_189;
x_171 = x_186;
goto block_183;
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; uint8_t x_193; 
lean_inc(x_50);
x_190 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__39___at_Lean_Meta_getFVarSetToGeneralize___spec__47(x_50, x_148, x_186);
x_191 = lean_ctor_get(x_190, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_190, 1);
lean_inc(x_192);
lean_dec(x_190);
x_193 = lean_unbox(x_191);
lean_dec(x_191);
x_170 = x_193;
x_171 = x_192;
goto block_183;
}
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; uint8_t x_197; 
lean_inc(x_50);
x_194 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__50___at_Lean_Meta_getFVarSetToGeneralize___spec__58(x_50, x_148, x_186);
x_195 = lean_ctor_get(x_194, 0);
lean_inc(x_195);
x_196 = lean_ctor_get(x_194, 1);
lean_inc(x_196);
lean_dec(x_194);
x_197 = lean_unbox(x_195);
lean_dec(x_195);
x_170 = x_197;
x_171 = x_196;
goto block_183;
}
block_169:
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; uint8_t x_159; 
x_155 = lean_ctor_get(x_154, 1);
lean_inc(x_155);
lean_dec(x_154);
x_156 = lean_st_ref_take(x_10, x_152);
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_156, 1);
lean_inc(x_158);
lean_dec(x_156);
x_159 = !lean_is_exclusive(x_157);
if (x_159 == 0)
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_160 = lean_ctor_get(x_157, 0);
lean_dec(x_160);
lean_ctor_set(x_157, 0, x_155);
x_161 = lean_st_ref_set(x_10, x_157, x_158);
x_162 = lean_ctor_get(x_161, 1);
lean_inc(x_162);
lean_dec(x_161);
x_53 = x_153;
x_54 = x_162;
goto block_64;
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_163 = lean_ctor_get(x_157, 1);
x_164 = lean_ctor_get(x_157, 2);
x_165 = lean_ctor_get(x_157, 3);
lean_inc(x_165);
lean_inc(x_164);
lean_inc(x_163);
lean_dec(x_157);
x_166 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_166, 0, x_155);
lean_ctor_set(x_166, 1, x_163);
lean_ctor_set(x_166, 2, x_164);
lean_ctor_set(x_166, 3, x_165);
x_167 = lean_st_ref_set(x_10, x_166, x_158);
x_168 = lean_ctor_get(x_167, 1);
lean_inc(x_168);
lean_dec(x_167);
x_53 = x_153;
x_54 = x_168;
goto block_64;
}
}
block_183:
{
if (x_170 == 0)
{
uint8_t x_172; 
x_172 = l_Lean_Expr_hasFVar(x_149);
if (x_172 == 0)
{
uint8_t x_173; 
x_173 = l_Lean_Expr_hasMVar(x_149);
if (x_173 == 0)
{
uint8_t x_174; 
lean_dec(x_149);
x_174 = 0;
x_153 = x_174;
x_154 = x_171;
goto block_169;
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; uint8_t x_178; 
lean_inc(x_50);
lean_inc(x_3);
x_175 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__23(x_3, x_50, x_149, x_171);
x_176 = lean_ctor_get(x_175, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_175, 1);
lean_inc(x_177);
lean_dec(x_175);
x_178 = lean_unbox(x_176);
lean_dec(x_176);
x_153 = x_178;
x_154 = x_177;
goto block_169;
}
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; uint8_t x_182; 
lean_inc(x_50);
lean_inc(x_3);
x_179 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__31(x_3, x_50, x_149, x_171);
x_180 = lean_ctor_get(x_179, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_179, 1);
lean_inc(x_181);
lean_dec(x_179);
x_182 = lean_unbox(x_180);
lean_dec(x_180);
x_153 = x_182;
x_154 = x_181;
goto block_169;
}
}
else
{
lean_dec(x_149);
x_153 = x_170;
x_154 = x_171;
goto block_169;
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
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_Meta_getFVarSetToGeneralize___spec__62___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_Meta_getFVarSetToGeneralize___spec__62(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
x_24 = l_Lean_PersistentArray_forInAux___at_Lean_Meta_getFVarSetToGeneralize___spec__62___lambda__1(x_22, x_23, x_7, x_8, x_9, x_10, x_21);
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
x_43 = l_Lean_PersistentArray_forInAux___at_Lean_Meta_getFVarSetToGeneralize___spec__62___lambda__1(x_41, x_42, x_7, x_8, x_9, x_10, x_40);
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
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_65; lean_object* x_70; lean_object* x_199; 
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
x_199 = l_Lean_RBNode_findCore___at_Lean_Meta_mkGeneralizationForbiddenSet_visit___spec__1(x_1, x_52);
if (lean_obj_tag(x_199) == 0)
{
uint8_t x_200; 
x_200 = l_Lean_LocalDecl_isAuxDecl(x_48);
if (x_200 == 0)
{
uint8_t x_201; uint8_t x_202; 
x_201 = l_Lean_LocalDecl_binderInfo(x_48);
x_202 = l_Lean_BinderInfo_isInstImplicit(x_201);
if (x_202 == 0)
{
if (x_2 == 0)
{
lean_object* x_203; 
x_203 = lean_box(0);
x_70 = x_203;
goto block_198;
}
else
{
uint8_t x_204; 
x_204 = l_Lean_LocalDecl_isLet(x_48);
if (x_204 == 0)
{
lean_object* x_205; 
x_205 = lean_box(0);
x_70 = x_205;
goto block_198;
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; 
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_48);
x_206 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_206, 0, x_49);
lean_ctor_set(x_206, 1, x_50);
x_207 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_207, 0, x_206);
x_208 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_208, 0, x_207);
lean_ctor_set(x_208, 1, x_13);
x_27 = x_208;
goto block_43;
}
}
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; 
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_48);
x_209 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_209, 0, x_49);
lean_ctor_set(x_209, 1, x_50);
x_210 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_210, 0, x_209);
x_211 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_211, 0, x_210);
lean_ctor_set(x_211, 1, x_13);
x_27 = x_211;
goto block_43;
}
}
else
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; 
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_48);
x_212 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_212, 0, x_49);
lean_ctor_set(x_212, 1, x_50);
x_213 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_213, 0, x_212);
x_214 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_214, 0, x_213);
lean_ctor_set(x_214, 1, x_13);
x_27 = x_214;
goto block_43;
}
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; 
lean_dec(x_199);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_48);
x_215 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_215, 0, x_49);
lean_ctor_set(x_215, 1, x_50);
x_216 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_216, 0, x_215);
x_217 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_217, 0, x_216);
lean_ctor_set(x_217, 1, x_13);
x_27 = x_217;
goto block_43;
}
block_64:
{
if (x_53 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_52);
if (lean_is_scalar(x_51)) {
 x_55 = lean_alloc_ctor(0, 2, 0);
} else {
 x_55 = x_51;
}
lean_ctor_set(x_55, 0, x_49);
lean_ctor_set(x_55, 1, x_50);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_55);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_54);
x_27 = x_57;
goto block_43;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_58 = lean_box(0);
lean_inc(x_52);
x_59 = l_Lean_RBNode_insert___at_Lean_FVarIdSet_insert___spec__1(x_49, x_52, x_58);
x_60 = l_Lean_RBNode_insert___at_Lean_FVarIdSet_insert___spec__1(x_50, x_52, x_58);
if (lean_is_scalar(x_51)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_51;
}
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_61);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_54);
x_27 = x_63;
goto block_43;
}
}
block_69:
{
lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
x_68 = lean_unbox(x_66);
lean_dec(x_66);
x_53 = x_68;
x_54 = x_67;
goto block_64;
}
block_198:
{
lean_dec(x_70);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_71 = lean_ctor_get(x_48, 3);
lean_inc(x_71);
lean_dec(x_48);
x_72 = lean_st_ref_get(x_10, x_13);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
x_75 = lean_ctor_get(x_73, 0);
lean_inc(x_75);
lean_dec(x_73);
x_76 = l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1;
lean_inc(x_75);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_75);
x_78 = l_Lean_Expr_hasFVar(x_71);
if (x_78 == 0)
{
uint8_t x_79; 
x_79 = l_Lean_Expr_hasMVar(x_71);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; 
lean_dec(x_77);
lean_dec(x_71);
x_80 = lean_st_ref_take(x_10, x_74);
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec(x_80);
x_83 = !lean_is_exclusive(x_81);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_84 = lean_ctor_get(x_81, 0);
lean_dec(x_84);
lean_ctor_set(x_81, 0, x_75);
x_85 = lean_st_ref_set(x_10, x_81, x_82);
x_86 = !lean_is_exclusive(x_85);
if (x_86 == 0)
{
lean_object* x_87; uint8_t x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_85, 0);
lean_dec(x_87);
x_88 = 0;
x_89 = lean_box(x_88);
lean_ctor_set(x_85, 0, x_89);
x_65 = x_85;
goto block_69;
}
else
{
lean_object* x_90; uint8_t x_91; lean_object* x_92; lean_object* x_93; 
x_90 = lean_ctor_get(x_85, 1);
lean_inc(x_90);
lean_dec(x_85);
x_91 = 0;
x_92 = lean_box(x_91);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_90);
x_65 = x_93;
goto block_69;
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; lean_object* x_102; lean_object* x_103; 
x_94 = lean_ctor_get(x_81, 1);
x_95 = lean_ctor_get(x_81, 2);
x_96 = lean_ctor_get(x_81, 3);
lean_inc(x_96);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_81);
x_97 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_97, 0, x_75);
lean_ctor_set(x_97, 1, x_94);
lean_ctor_set(x_97, 2, x_95);
lean_ctor_set(x_97, 3, x_96);
x_98 = lean_st_ref_set(x_10, x_97, x_82);
x_99 = lean_ctor_get(x_98, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 lean_ctor_release(x_98, 1);
 x_100 = x_98;
} else {
 lean_dec_ref(x_98);
 x_100 = lean_box(0);
}
x_101 = 0;
x_102 = lean_box(x_101);
if (lean_is_scalar(x_100)) {
 x_103 = lean_alloc_ctor(0, 2, 0);
} else {
 x_103 = x_100;
}
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_99);
x_65 = x_103;
goto block_69;
}
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_111; 
lean_dec(x_75);
lean_inc(x_50);
x_104 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__1___at_Lean_Meta_getFVarSetToGeneralize___spec__9(x_50, x_71, x_77);
x_105 = lean_ctor_get(x_104, 1);
lean_inc(x_105);
x_106 = lean_ctor_get(x_104, 0);
lean_inc(x_106);
lean_dec(x_104);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
lean_dec(x_105);
x_108 = lean_st_ref_take(x_10, x_74);
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
lean_dec(x_108);
x_111 = !lean_is_exclusive(x_109);
if (x_111 == 0)
{
lean_object* x_112; lean_object* x_113; uint8_t x_114; 
x_112 = lean_ctor_get(x_109, 0);
lean_dec(x_112);
lean_ctor_set(x_109, 0, x_107);
x_113 = lean_st_ref_set(x_10, x_109, x_110);
x_114 = !lean_is_exclusive(x_113);
if (x_114 == 0)
{
lean_object* x_115; 
x_115 = lean_ctor_get(x_113, 0);
lean_dec(x_115);
lean_ctor_set(x_113, 0, x_106);
x_65 = x_113;
goto block_69;
}
else
{
lean_object* x_116; lean_object* x_117; 
x_116 = lean_ctor_get(x_113, 1);
lean_inc(x_116);
lean_dec(x_113);
x_117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_117, 0, x_106);
lean_ctor_set(x_117, 1, x_116);
x_65 = x_117;
goto block_69;
}
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_118 = lean_ctor_get(x_109, 1);
x_119 = lean_ctor_get(x_109, 2);
x_120 = lean_ctor_get(x_109, 3);
lean_inc(x_120);
lean_inc(x_119);
lean_inc(x_118);
lean_dec(x_109);
x_121 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_121, 0, x_107);
lean_ctor_set(x_121, 1, x_118);
lean_ctor_set(x_121, 2, x_119);
lean_ctor_set(x_121, 3, x_120);
x_122 = lean_st_ref_set(x_10, x_121, x_110);
x_123 = lean_ctor_get(x_122, 1);
lean_inc(x_123);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 lean_ctor_release(x_122, 1);
 x_124 = x_122;
} else {
 lean_dec_ref(x_122);
 x_124 = lean_box(0);
}
if (lean_is_scalar(x_124)) {
 x_125 = lean_alloc_ctor(0, 2, 0);
} else {
 x_125 = x_124;
}
lean_ctor_set(x_125, 0, x_106);
lean_ctor_set(x_125, 1, x_123);
x_65 = x_125;
goto block_69;
}
}
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_133; 
lean_dec(x_75);
lean_inc(x_50);
x_126 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__12___at_Lean_Meta_getFVarSetToGeneralize___spec__20(x_50, x_71, x_77);
x_127 = lean_ctor_get(x_126, 1);
lean_inc(x_127);
x_128 = lean_ctor_get(x_126, 0);
lean_inc(x_128);
lean_dec(x_126);
x_129 = lean_ctor_get(x_127, 1);
lean_inc(x_129);
lean_dec(x_127);
x_130 = lean_st_ref_take(x_10, x_74);
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_130, 1);
lean_inc(x_132);
lean_dec(x_130);
x_133 = !lean_is_exclusive(x_131);
if (x_133 == 0)
{
lean_object* x_134; lean_object* x_135; uint8_t x_136; 
x_134 = lean_ctor_get(x_131, 0);
lean_dec(x_134);
lean_ctor_set(x_131, 0, x_129);
x_135 = lean_st_ref_set(x_10, x_131, x_132);
x_136 = !lean_is_exclusive(x_135);
if (x_136 == 0)
{
lean_object* x_137; 
x_137 = lean_ctor_get(x_135, 0);
lean_dec(x_137);
lean_ctor_set(x_135, 0, x_128);
x_65 = x_135;
goto block_69;
}
else
{
lean_object* x_138; lean_object* x_139; 
x_138 = lean_ctor_get(x_135, 1);
lean_inc(x_138);
lean_dec(x_135);
x_139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_139, 0, x_128);
lean_ctor_set(x_139, 1, x_138);
x_65 = x_139;
goto block_69;
}
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_140 = lean_ctor_get(x_131, 1);
x_141 = lean_ctor_get(x_131, 2);
x_142 = lean_ctor_get(x_131, 3);
lean_inc(x_142);
lean_inc(x_141);
lean_inc(x_140);
lean_dec(x_131);
x_143 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_143, 0, x_129);
lean_ctor_set(x_143, 1, x_140);
lean_ctor_set(x_143, 2, x_141);
lean_ctor_set(x_143, 3, x_142);
x_144 = lean_st_ref_set(x_10, x_143, x_132);
x_145 = lean_ctor_get(x_144, 1);
lean_inc(x_145);
if (lean_is_exclusive(x_144)) {
 lean_ctor_release(x_144, 0);
 lean_ctor_release(x_144, 1);
 x_146 = x_144;
} else {
 lean_dec_ref(x_144);
 x_146 = lean_box(0);
}
if (lean_is_scalar(x_146)) {
 x_147 = lean_alloc_ctor(0, 2, 0);
} else {
 x_147 = x_146;
}
lean_ctor_set(x_147, 0, x_128);
lean_ctor_set(x_147, 1, x_145);
x_65 = x_147;
goto block_69;
}
}
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; uint8_t x_153; lean_object* x_154; uint8_t x_170; lean_object* x_171; lean_object* x_184; lean_object* x_185; lean_object* x_186; uint8_t x_187; 
x_148 = lean_ctor_get(x_48, 3);
lean_inc(x_148);
x_149 = lean_ctor_get(x_48, 4);
lean_inc(x_149);
lean_dec(x_48);
x_150 = lean_st_ref_get(x_10, x_13);
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_150, 1);
lean_inc(x_152);
lean_dec(x_150);
x_184 = lean_ctor_get(x_151, 0);
lean_inc(x_184);
lean_dec(x_151);
x_185 = l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1;
x_186 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_186, 0, x_185);
lean_ctor_set(x_186, 1, x_184);
x_187 = l_Lean_Expr_hasFVar(x_148);
if (x_187 == 0)
{
uint8_t x_188; 
x_188 = l_Lean_Expr_hasMVar(x_148);
if (x_188 == 0)
{
uint8_t x_189; 
lean_dec(x_148);
x_189 = 0;
x_170 = x_189;
x_171 = x_186;
goto block_183;
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; uint8_t x_193; 
lean_inc(x_50);
x_190 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__39___at_Lean_Meta_getFVarSetToGeneralize___spec__47(x_50, x_148, x_186);
x_191 = lean_ctor_get(x_190, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_190, 1);
lean_inc(x_192);
lean_dec(x_190);
x_193 = lean_unbox(x_191);
lean_dec(x_191);
x_170 = x_193;
x_171 = x_192;
goto block_183;
}
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; uint8_t x_197; 
lean_inc(x_50);
x_194 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__50___at_Lean_Meta_getFVarSetToGeneralize___spec__58(x_50, x_148, x_186);
x_195 = lean_ctor_get(x_194, 0);
lean_inc(x_195);
x_196 = lean_ctor_get(x_194, 1);
lean_inc(x_196);
lean_dec(x_194);
x_197 = lean_unbox(x_195);
lean_dec(x_195);
x_170 = x_197;
x_171 = x_196;
goto block_183;
}
block_169:
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; uint8_t x_159; 
x_155 = lean_ctor_get(x_154, 1);
lean_inc(x_155);
lean_dec(x_154);
x_156 = lean_st_ref_take(x_10, x_152);
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_156, 1);
lean_inc(x_158);
lean_dec(x_156);
x_159 = !lean_is_exclusive(x_157);
if (x_159 == 0)
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_160 = lean_ctor_get(x_157, 0);
lean_dec(x_160);
lean_ctor_set(x_157, 0, x_155);
x_161 = lean_st_ref_set(x_10, x_157, x_158);
x_162 = lean_ctor_get(x_161, 1);
lean_inc(x_162);
lean_dec(x_161);
x_53 = x_153;
x_54 = x_162;
goto block_64;
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_163 = lean_ctor_get(x_157, 1);
x_164 = lean_ctor_get(x_157, 2);
x_165 = lean_ctor_get(x_157, 3);
lean_inc(x_165);
lean_inc(x_164);
lean_inc(x_163);
lean_dec(x_157);
x_166 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_166, 0, x_155);
lean_ctor_set(x_166, 1, x_163);
lean_ctor_set(x_166, 2, x_164);
lean_ctor_set(x_166, 3, x_165);
x_167 = lean_st_ref_set(x_10, x_166, x_158);
x_168 = lean_ctor_get(x_167, 1);
lean_inc(x_168);
lean_dec(x_167);
x_53 = x_153;
x_54 = x_168;
goto block_64;
}
}
block_183:
{
if (x_170 == 0)
{
uint8_t x_172; 
x_172 = l_Lean_Expr_hasFVar(x_149);
if (x_172 == 0)
{
uint8_t x_173; 
x_173 = l_Lean_Expr_hasMVar(x_149);
if (x_173 == 0)
{
uint8_t x_174; 
lean_dec(x_149);
x_174 = 0;
x_153 = x_174;
x_154 = x_171;
goto block_169;
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; uint8_t x_178; 
lean_inc(x_50);
lean_inc(x_3);
x_175 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__23(x_3, x_50, x_149, x_171);
x_176 = lean_ctor_get(x_175, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_175, 1);
lean_inc(x_177);
lean_dec(x_175);
x_178 = lean_unbox(x_176);
lean_dec(x_176);
x_153 = x_178;
x_154 = x_177;
goto block_169;
}
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; uint8_t x_182; 
lean_inc(x_50);
lean_inc(x_3);
x_179 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__31(x_3, x_50, x_149, x_171);
x_180 = lean_ctor_get(x_179, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_179, 1);
lean_inc(x_181);
lean_dec(x_179);
x_182 = lean_unbox(x_180);
lean_dec(x_180);
x_153 = x_182;
x_154 = x_181;
goto block_169;
}
}
else
{
lean_dec(x_149);
x_153 = x_170;
x_154 = x_171;
goto block_169;
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
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_Meta_getFVarSetToGeneralize___spec__61___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_Meta_getFVarSetToGeneralize___spec__61(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_1);
x_12 = l_Lean_PersistentArray_forInAux___at_Lean_Meta_getFVarSetToGeneralize___spec__62(x_1, x_2, x_3, x_5, x_11, x_5, x_6, x_7, x_8, x_9, x_10);
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
x_21 = l_Lean_PersistentArray_forInAux___at_Lean_Meta_getFVarSetToGeneralize___spec__67(x_1, x_2, x_3, x_4, x_17, x_19, x_10, x_11, x_12, x_13, x_14);
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
x_35 = l_Lean_PersistentArray_forInAux___at_Lean_Meta_getFVarSetToGeneralize___spec__67(x_1, x_2, x_3, x_4, x_17, x_34, x_10, x_11, x_12, x_13, x_14);
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
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_65; lean_object* x_70; lean_object* x_199; 
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
x_199 = l_Lean_RBNode_findCore___at_Lean_Meta_mkGeneralizationForbiddenSet_visit___spec__1(x_1, x_52);
if (lean_obj_tag(x_199) == 0)
{
uint8_t x_200; 
x_200 = l_Lean_LocalDecl_isAuxDecl(x_48);
if (x_200 == 0)
{
uint8_t x_201; uint8_t x_202; 
x_201 = l_Lean_LocalDecl_binderInfo(x_48);
x_202 = l_Lean_BinderInfo_isInstImplicit(x_201);
if (x_202 == 0)
{
if (x_2 == 0)
{
lean_object* x_203; 
x_203 = lean_box(0);
x_70 = x_203;
goto block_198;
}
else
{
uint8_t x_204; 
x_204 = l_Lean_LocalDecl_isLet(x_48);
if (x_204 == 0)
{
lean_object* x_205; 
x_205 = lean_box(0);
x_70 = x_205;
goto block_198;
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; 
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_48);
x_206 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_206, 0, x_49);
lean_ctor_set(x_206, 1, x_50);
x_207 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_207, 0, x_206);
x_208 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_208, 0, x_207);
lean_ctor_set(x_208, 1, x_13);
x_27 = x_208;
goto block_43;
}
}
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; 
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_48);
x_209 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_209, 0, x_49);
lean_ctor_set(x_209, 1, x_50);
x_210 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_210, 0, x_209);
x_211 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_211, 0, x_210);
lean_ctor_set(x_211, 1, x_13);
x_27 = x_211;
goto block_43;
}
}
else
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; 
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_48);
x_212 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_212, 0, x_49);
lean_ctor_set(x_212, 1, x_50);
x_213 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_213, 0, x_212);
x_214 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_214, 0, x_213);
lean_ctor_set(x_214, 1, x_13);
x_27 = x_214;
goto block_43;
}
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; 
lean_dec(x_199);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_48);
x_215 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_215, 0, x_49);
lean_ctor_set(x_215, 1, x_50);
x_216 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_216, 0, x_215);
x_217 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_217, 0, x_216);
lean_ctor_set(x_217, 1, x_13);
x_27 = x_217;
goto block_43;
}
block_64:
{
if (x_53 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_52);
if (lean_is_scalar(x_51)) {
 x_55 = lean_alloc_ctor(0, 2, 0);
} else {
 x_55 = x_51;
}
lean_ctor_set(x_55, 0, x_49);
lean_ctor_set(x_55, 1, x_50);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_55);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_54);
x_27 = x_57;
goto block_43;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_58 = lean_box(0);
lean_inc(x_52);
x_59 = l_Lean_RBNode_insert___at_Lean_FVarIdSet_insert___spec__1(x_49, x_52, x_58);
x_60 = l_Lean_RBNode_insert___at_Lean_FVarIdSet_insert___spec__1(x_50, x_52, x_58);
if (lean_is_scalar(x_51)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_51;
}
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_61);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_54);
x_27 = x_63;
goto block_43;
}
}
block_69:
{
lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
x_68 = lean_unbox(x_66);
lean_dec(x_66);
x_53 = x_68;
x_54 = x_67;
goto block_64;
}
block_198:
{
lean_dec(x_70);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_71 = lean_ctor_get(x_48, 3);
lean_inc(x_71);
lean_dec(x_48);
x_72 = lean_st_ref_get(x_10, x_13);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
x_75 = lean_ctor_get(x_73, 0);
lean_inc(x_75);
lean_dec(x_73);
x_76 = l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1;
lean_inc(x_75);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_75);
x_78 = l_Lean_Expr_hasFVar(x_71);
if (x_78 == 0)
{
uint8_t x_79; 
x_79 = l_Lean_Expr_hasMVar(x_71);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; 
lean_dec(x_77);
lean_dec(x_71);
x_80 = lean_st_ref_take(x_10, x_74);
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec(x_80);
x_83 = !lean_is_exclusive(x_81);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_84 = lean_ctor_get(x_81, 0);
lean_dec(x_84);
lean_ctor_set(x_81, 0, x_75);
x_85 = lean_st_ref_set(x_10, x_81, x_82);
x_86 = !lean_is_exclusive(x_85);
if (x_86 == 0)
{
lean_object* x_87; uint8_t x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_85, 0);
lean_dec(x_87);
x_88 = 0;
x_89 = lean_box(x_88);
lean_ctor_set(x_85, 0, x_89);
x_65 = x_85;
goto block_69;
}
else
{
lean_object* x_90; uint8_t x_91; lean_object* x_92; lean_object* x_93; 
x_90 = lean_ctor_get(x_85, 1);
lean_inc(x_90);
lean_dec(x_85);
x_91 = 0;
x_92 = lean_box(x_91);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_90);
x_65 = x_93;
goto block_69;
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; lean_object* x_102; lean_object* x_103; 
x_94 = lean_ctor_get(x_81, 1);
x_95 = lean_ctor_get(x_81, 2);
x_96 = lean_ctor_get(x_81, 3);
lean_inc(x_96);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_81);
x_97 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_97, 0, x_75);
lean_ctor_set(x_97, 1, x_94);
lean_ctor_set(x_97, 2, x_95);
lean_ctor_set(x_97, 3, x_96);
x_98 = lean_st_ref_set(x_10, x_97, x_82);
x_99 = lean_ctor_get(x_98, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 lean_ctor_release(x_98, 1);
 x_100 = x_98;
} else {
 lean_dec_ref(x_98);
 x_100 = lean_box(0);
}
x_101 = 0;
x_102 = lean_box(x_101);
if (lean_is_scalar(x_100)) {
 x_103 = lean_alloc_ctor(0, 2, 0);
} else {
 x_103 = x_100;
}
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_99);
x_65 = x_103;
goto block_69;
}
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_111; 
lean_dec(x_75);
lean_inc(x_50);
x_104 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__1___at_Lean_Meta_getFVarSetToGeneralize___spec__9(x_50, x_71, x_77);
x_105 = lean_ctor_get(x_104, 1);
lean_inc(x_105);
x_106 = lean_ctor_get(x_104, 0);
lean_inc(x_106);
lean_dec(x_104);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
lean_dec(x_105);
x_108 = lean_st_ref_take(x_10, x_74);
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
lean_dec(x_108);
x_111 = !lean_is_exclusive(x_109);
if (x_111 == 0)
{
lean_object* x_112; lean_object* x_113; uint8_t x_114; 
x_112 = lean_ctor_get(x_109, 0);
lean_dec(x_112);
lean_ctor_set(x_109, 0, x_107);
x_113 = lean_st_ref_set(x_10, x_109, x_110);
x_114 = !lean_is_exclusive(x_113);
if (x_114 == 0)
{
lean_object* x_115; 
x_115 = lean_ctor_get(x_113, 0);
lean_dec(x_115);
lean_ctor_set(x_113, 0, x_106);
x_65 = x_113;
goto block_69;
}
else
{
lean_object* x_116; lean_object* x_117; 
x_116 = lean_ctor_get(x_113, 1);
lean_inc(x_116);
lean_dec(x_113);
x_117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_117, 0, x_106);
lean_ctor_set(x_117, 1, x_116);
x_65 = x_117;
goto block_69;
}
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_118 = lean_ctor_get(x_109, 1);
x_119 = lean_ctor_get(x_109, 2);
x_120 = lean_ctor_get(x_109, 3);
lean_inc(x_120);
lean_inc(x_119);
lean_inc(x_118);
lean_dec(x_109);
x_121 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_121, 0, x_107);
lean_ctor_set(x_121, 1, x_118);
lean_ctor_set(x_121, 2, x_119);
lean_ctor_set(x_121, 3, x_120);
x_122 = lean_st_ref_set(x_10, x_121, x_110);
x_123 = lean_ctor_get(x_122, 1);
lean_inc(x_123);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 lean_ctor_release(x_122, 1);
 x_124 = x_122;
} else {
 lean_dec_ref(x_122);
 x_124 = lean_box(0);
}
if (lean_is_scalar(x_124)) {
 x_125 = lean_alloc_ctor(0, 2, 0);
} else {
 x_125 = x_124;
}
lean_ctor_set(x_125, 0, x_106);
lean_ctor_set(x_125, 1, x_123);
x_65 = x_125;
goto block_69;
}
}
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_133; 
lean_dec(x_75);
lean_inc(x_50);
x_126 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__12___at_Lean_Meta_getFVarSetToGeneralize___spec__20(x_50, x_71, x_77);
x_127 = lean_ctor_get(x_126, 1);
lean_inc(x_127);
x_128 = lean_ctor_get(x_126, 0);
lean_inc(x_128);
lean_dec(x_126);
x_129 = lean_ctor_get(x_127, 1);
lean_inc(x_129);
lean_dec(x_127);
x_130 = lean_st_ref_take(x_10, x_74);
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_130, 1);
lean_inc(x_132);
lean_dec(x_130);
x_133 = !lean_is_exclusive(x_131);
if (x_133 == 0)
{
lean_object* x_134; lean_object* x_135; uint8_t x_136; 
x_134 = lean_ctor_get(x_131, 0);
lean_dec(x_134);
lean_ctor_set(x_131, 0, x_129);
x_135 = lean_st_ref_set(x_10, x_131, x_132);
x_136 = !lean_is_exclusive(x_135);
if (x_136 == 0)
{
lean_object* x_137; 
x_137 = lean_ctor_get(x_135, 0);
lean_dec(x_137);
lean_ctor_set(x_135, 0, x_128);
x_65 = x_135;
goto block_69;
}
else
{
lean_object* x_138; lean_object* x_139; 
x_138 = lean_ctor_get(x_135, 1);
lean_inc(x_138);
lean_dec(x_135);
x_139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_139, 0, x_128);
lean_ctor_set(x_139, 1, x_138);
x_65 = x_139;
goto block_69;
}
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_140 = lean_ctor_get(x_131, 1);
x_141 = lean_ctor_get(x_131, 2);
x_142 = lean_ctor_get(x_131, 3);
lean_inc(x_142);
lean_inc(x_141);
lean_inc(x_140);
lean_dec(x_131);
x_143 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_143, 0, x_129);
lean_ctor_set(x_143, 1, x_140);
lean_ctor_set(x_143, 2, x_141);
lean_ctor_set(x_143, 3, x_142);
x_144 = lean_st_ref_set(x_10, x_143, x_132);
x_145 = lean_ctor_get(x_144, 1);
lean_inc(x_145);
if (lean_is_exclusive(x_144)) {
 lean_ctor_release(x_144, 0);
 lean_ctor_release(x_144, 1);
 x_146 = x_144;
} else {
 lean_dec_ref(x_144);
 x_146 = lean_box(0);
}
if (lean_is_scalar(x_146)) {
 x_147 = lean_alloc_ctor(0, 2, 0);
} else {
 x_147 = x_146;
}
lean_ctor_set(x_147, 0, x_128);
lean_ctor_set(x_147, 1, x_145);
x_65 = x_147;
goto block_69;
}
}
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; uint8_t x_153; lean_object* x_154; uint8_t x_170; lean_object* x_171; lean_object* x_184; lean_object* x_185; lean_object* x_186; uint8_t x_187; 
x_148 = lean_ctor_get(x_48, 3);
lean_inc(x_148);
x_149 = lean_ctor_get(x_48, 4);
lean_inc(x_149);
lean_dec(x_48);
x_150 = lean_st_ref_get(x_10, x_13);
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_150, 1);
lean_inc(x_152);
lean_dec(x_150);
x_184 = lean_ctor_get(x_151, 0);
lean_inc(x_184);
lean_dec(x_151);
x_185 = l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1;
x_186 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_186, 0, x_185);
lean_ctor_set(x_186, 1, x_184);
x_187 = l_Lean_Expr_hasFVar(x_148);
if (x_187 == 0)
{
uint8_t x_188; 
x_188 = l_Lean_Expr_hasMVar(x_148);
if (x_188 == 0)
{
uint8_t x_189; 
lean_dec(x_148);
x_189 = 0;
x_170 = x_189;
x_171 = x_186;
goto block_183;
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; uint8_t x_193; 
lean_inc(x_50);
x_190 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__39___at_Lean_Meta_getFVarSetToGeneralize___spec__47(x_50, x_148, x_186);
x_191 = lean_ctor_get(x_190, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_190, 1);
lean_inc(x_192);
lean_dec(x_190);
x_193 = lean_unbox(x_191);
lean_dec(x_191);
x_170 = x_193;
x_171 = x_192;
goto block_183;
}
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; uint8_t x_197; 
lean_inc(x_50);
x_194 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__50___at_Lean_Meta_getFVarSetToGeneralize___spec__58(x_50, x_148, x_186);
x_195 = lean_ctor_get(x_194, 0);
lean_inc(x_195);
x_196 = lean_ctor_get(x_194, 1);
lean_inc(x_196);
lean_dec(x_194);
x_197 = lean_unbox(x_195);
lean_dec(x_195);
x_170 = x_197;
x_171 = x_196;
goto block_183;
}
block_169:
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; uint8_t x_159; 
x_155 = lean_ctor_get(x_154, 1);
lean_inc(x_155);
lean_dec(x_154);
x_156 = lean_st_ref_take(x_10, x_152);
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_156, 1);
lean_inc(x_158);
lean_dec(x_156);
x_159 = !lean_is_exclusive(x_157);
if (x_159 == 0)
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_160 = lean_ctor_get(x_157, 0);
lean_dec(x_160);
lean_ctor_set(x_157, 0, x_155);
x_161 = lean_st_ref_set(x_10, x_157, x_158);
x_162 = lean_ctor_get(x_161, 1);
lean_inc(x_162);
lean_dec(x_161);
x_53 = x_153;
x_54 = x_162;
goto block_64;
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_163 = lean_ctor_get(x_157, 1);
x_164 = lean_ctor_get(x_157, 2);
x_165 = lean_ctor_get(x_157, 3);
lean_inc(x_165);
lean_inc(x_164);
lean_inc(x_163);
lean_dec(x_157);
x_166 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_166, 0, x_155);
lean_ctor_set(x_166, 1, x_163);
lean_ctor_set(x_166, 2, x_164);
lean_ctor_set(x_166, 3, x_165);
x_167 = lean_st_ref_set(x_10, x_166, x_158);
x_168 = lean_ctor_get(x_167, 1);
lean_inc(x_168);
lean_dec(x_167);
x_53 = x_153;
x_54 = x_168;
goto block_64;
}
}
block_183:
{
if (x_170 == 0)
{
uint8_t x_172; 
x_172 = l_Lean_Expr_hasFVar(x_149);
if (x_172 == 0)
{
uint8_t x_173; 
x_173 = l_Lean_Expr_hasMVar(x_149);
if (x_173 == 0)
{
uint8_t x_174; 
lean_dec(x_149);
x_174 = 0;
x_153 = x_174;
x_154 = x_171;
goto block_169;
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; uint8_t x_178; 
lean_inc(x_50);
lean_inc(x_3);
x_175 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__23(x_3, x_50, x_149, x_171);
x_176 = lean_ctor_get(x_175, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_175, 1);
lean_inc(x_177);
lean_dec(x_175);
x_178 = lean_unbox(x_176);
lean_dec(x_176);
x_153 = x_178;
x_154 = x_177;
goto block_169;
}
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; uint8_t x_182; 
lean_inc(x_50);
lean_inc(x_3);
x_179 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__31(x_3, x_50, x_149, x_171);
x_180 = lean_ctor_get(x_179, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_179, 1);
lean_inc(x_181);
lean_dec(x_179);
x_182 = lean_unbox(x_180);
lean_dec(x_180);
x_153 = x_182;
x_154 = x_181;
goto block_169;
}
}
else
{
lean_dec(x_149);
x_153 = x_170;
x_154 = x_171;
goto block_169;
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
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_Meta_getFVarSetToGeneralize___spec__67(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
x_24 = l_Lean_PersistentArray_forInAux___at_Lean_Meta_getFVarSetToGeneralize___spec__62___lambda__1(x_22, x_23, x_7, x_8, x_9, x_10, x_21);
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
x_43 = l_Lean_PersistentArray_forInAux___at_Lean_Meta_getFVarSetToGeneralize___spec__62___lambda__1(x_41, x_42, x_7, x_8, x_9, x_10, x_40);
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
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_65; lean_object* x_70; lean_object* x_199; 
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
x_199 = l_Lean_RBNode_findCore___at_Lean_Meta_mkGeneralizationForbiddenSet_visit___spec__1(x_1, x_52);
if (lean_obj_tag(x_199) == 0)
{
uint8_t x_200; 
x_200 = l_Lean_LocalDecl_isAuxDecl(x_48);
if (x_200 == 0)
{
uint8_t x_201; uint8_t x_202; 
x_201 = l_Lean_LocalDecl_binderInfo(x_48);
x_202 = l_Lean_BinderInfo_isInstImplicit(x_201);
if (x_202 == 0)
{
if (x_2 == 0)
{
lean_object* x_203; 
x_203 = lean_box(0);
x_70 = x_203;
goto block_198;
}
else
{
uint8_t x_204; 
x_204 = l_Lean_LocalDecl_isLet(x_48);
if (x_204 == 0)
{
lean_object* x_205; 
x_205 = lean_box(0);
x_70 = x_205;
goto block_198;
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; 
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_48);
x_206 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_206, 0, x_49);
lean_ctor_set(x_206, 1, x_50);
x_207 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_207, 0, x_206);
x_208 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_208, 0, x_207);
lean_ctor_set(x_208, 1, x_13);
x_27 = x_208;
goto block_43;
}
}
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; 
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_48);
x_209 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_209, 0, x_49);
lean_ctor_set(x_209, 1, x_50);
x_210 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_210, 0, x_209);
x_211 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_211, 0, x_210);
lean_ctor_set(x_211, 1, x_13);
x_27 = x_211;
goto block_43;
}
}
else
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; 
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_48);
x_212 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_212, 0, x_49);
lean_ctor_set(x_212, 1, x_50);
x_213 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_213, 0, x_212);
x_214 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_214, 0, x_213);
lean_ctor_set(x_214, 1, x_13);
x_27 = x_214;
goto block_43;
}
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; 
lean_dec(x_199);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_48);
x_215 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_215, 0, x_49);
lean_ctor_set(x_215, 1, x_50);
x_216 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_216, 0, x_215);
x_217 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_217, 0, x_216);
lean_ctor_set(x_217, 1, x_13);
x_27 = x_217;
goto block_43;
}
block_64:
{
if (x_53 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_52);
if (lean_is_scalar(x_51)) {
 x_55 = lean_alloc_ctor(0, 2, 0);
} else {
 x_55 = x_51;
}
lean_ctor_set(x_55, 0, x_49);
lean_ctor_set(x_55, 1, x_50);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_55);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_54);
x_27 = x_57;
goto block_43;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_58 = lean_box(0);
lean_inc(x_52);
x_59 = l_Lean_RBNode_insert___at_Lean_FVarIdSet_insert___spec__1(x_49, x_52, x_58);
x_60 = l_Lean_RBNode_insert___at_Lean_FVarIdSet_insert___spec__1(x_50, x_52, x_58);
if (lean_is_scalar(x_51)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_51;
}
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_61);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_54);
x_27 = x_63;
goto block_43;
}
}
block_69:
{
lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
x_68 = lean_unbox(x_66);
lean_dec(x_66);
x_53 = x_68;
x_54 = x_67;
goto block_64;
}
block_198:
{
lean_dec(x_70);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_71 = lean_ctor_get(x_48, 3);
lean_inc(x_71);
lean_dec(x_48);
x_72 = lean_st_ref_get(x_10, x_13);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
x_75 = lean_ctor_get(x_73, 0);
lean_inc(x_75);
lean_dec(x_73);
x_76 = l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1;
lean_inc(x_75);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_75);
x_78 = l_Lean_Expr_hasFVar(x_71);
if (x_78 == 0)
{
uint8_t x_79; 
x_79 = l_Lean_Expr_hasMVar(x_71);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; 
lean_dec(x_77);
lean_dec(x_71);
x_80 = lean_st_ref_take(x_10, x_74);
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec(x_80);
x_83 = !lean_is_exclusive(x_81);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_84 = lean_ctor_get(x_81, 0);
lean_dec(x_84);
lean_ctor_set(x_81, 0, x_75);
x_85 = lean_st_ref_set(x_10, x_81, x_82);
x_86 = !lean_is_exclusive(x_85);
if (x_86 == 0)
{
lean_object* x_87; uint8_t x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_85, 0);
lean_dec(x_87);
x_88 = 0;
x_89 = lean_box(x_88);
lean_ctor_set(x_85, 0, x_89);
x_65 = x_85;
goto block_69;
}
else
{
lean_object* x_90; uint8_t x_91; lean_object* x_92; lean_object* x_93; 
x_90 = lean_ctor_get(x_85, 1);
lean_inc(x_90);
lean_dec(x_85);
x_91 = 0;
x_92 = lean_box(x_91);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_90);
x_65 = x_93;
goto block_69;
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; lean_object* x_102; lean_object* x_103; 
x_94 = lean_ctor_get(x_81, 1);
x_95 = lean_ctor_get(x_81, 2);
x_96 = lean_ctor_get(x_81, 3);
lean_inc(x_96);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_81);
x_97 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_97, 0, x_75);
lean_ctor_set(x_97, 1, x_94);
lean_ctor_set(x_97, 2, x_95);
lean_ctor_set(x_97, 3, x_96);
x_98 = lean_st_ref_set(x_10, x_97, x_82);
x_99 = lean_ctor_get(x_98, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 lean_ctor_release(x_98, 1);
 x_100 = x_98;
} else {
 lean_dec_ref(x_98);
 x_100 = lean_box(0);
}
x_101 = 0;
x_102 = lean_box(x_101);
if (lean_is_scalar(x_100)) {
 x_103 = lean_alloc_ctor(0, 2, 0);
} else {
 x_103 = x_100;
}
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_99);
x_65 = x_103;
goto block_69;
}
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_111; 
lean_dec(x_75);
lean_inc(x_50);
x_104 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__1___at_Lean_Meta_getFVarSetToGeneralize___spec__9(x_50, x_71, x_77);
x_105 = lean_ctor_get(x_104, 1);
lean_inc(x_105);
x_106 = lean_ctor_get(x_104, 0);
lean_inc(x_106);
lean_dec(x_104);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
lean_dec(x_105);
x_108 = lean_st_ref_take(x_10, x_74);
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
lean_dec(x_108);
x_111 = !lean_is_exclusive(x_109);
if (x_111 == 0)
{
lean_object* x_112; lean_object* x_113; uint8_t x_114; 
x_112 = lean_ctor_get(x_109, 0);
lean_dec(x_112);
lean_ctor_set(x_109, 0, x_107);
x_113 = lean_st_ref_set(x_10, x_109, x_110);
x_114 = !lean_is_exclusive(x_113);
if (x_114 == 0)
{
lean_object* x_115; 
x_115 = lean_ctor_get(x_113, 0);
lean_dec(x_115);
lean_ctor_set(x_113, 0, x_106);
x_65 = x_113;
goto block_69;
}
else
{
lean_object* x_116; lean_object* x_117; 
x_116 = lean_ctor_get(x_113, 1);
lean_inc(x_116);
lean_dec(x_113);
x_117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_117, 0, x_106);
lean_ctor_set(x_117, 1, x_116);
x_65 = x_117;
goto block_69;
}
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_118 = lean_ctor_get(x_109, 1);
x_119 = lean_ctor_get(x_109, 2);
x_120 = lean_ctor_get(x_109, 3);
lean_inc(x_120);
lean_inc(x_119);
lean_inc(x_118);
lean_dec(x_109);
x_121 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_121, 0, x_107);
lean_ctor_set(x_121, 1, x_118);
lean_ctor_set(x_121, 2, x_119);
lean_ctor_set(x_121, 3, x_120);
x_122 = lean_st_ref_set(x_10, x_121, x_110);
x_123 = lean_ctor_get(x_122, 1);
lean_inc(x_123);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 lean_ctor_release(x_122, 1);
 x_124 = x_122;
} else {
 lean_dec_ref(x_122);
 x_124 = lean_box(0);
}
if (lean_is_scalar(x_124)) {
 x_125 = lean_alloc_ctor(0, 2, 0);
} else {
 x_125 = x_124;
}
lean_ctor_set(x_125, 0, x_106);
lean_ctor_set(x_125, 1, x_123);
x_65 = x_125;
goto block_69;
}
}
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_133; 
lean_dec(x_75);
lean_inc(x_50);
x_126 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__12___at_Lean_Meta_getFVarSetToGeneralize___spec__20(x_50, x_71, x_77);
x_127 = lean_ctor_get(x_126, 1);
lean_inc(x_127);
x_128 = lean_ctor_get(x_126, 0);
lean_inc(x_128);
lean_dec(x_126);
x_129 = lean_ctor_get(x_127, 1);
lean_inc(x_129);
lean_dec(x_127);
x_130 = lean_st_ref_take(x_10, x_74);
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_130, 1);
lean_inc(x_132);
lean_dec(x_130);
x_133 = !lean_is_exclusive(x_131);
if (x_133 == 0)
{
lean_object* x_134; lean_object* x_135; uint8_t x_136; 
x_134 = lean_ctor_get(x_131, 0);
lean_dec(x_134);
lean_ctor_set(x_131, 0, x_129);
x_135 = lean_st_ref_set(x_10, x_131, x_132);
x_136 = !lean_is_exclusive(x_135);
if (x_136 == 0)
{
lean_object* x_137; 
x_137 = lean_ctor_get(x_135, 0);
lean_dec(x_137);
lean_ctor_set(x_135, 0, x_128);
x_65 = x_135;
goto block_69;
}
else
{
lean_object* x_138; lean_object* x_139; 
x_138 = lean_ctor_get(x_135, 1);
lean_inc(x_138);
lean_dec(x_135);
x_139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_139, 0, x_128);
lean_ctor_set(x_139, 1, x_138);
x_65 = x_139;
goto block_69;
}
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_140 = lean_ctor_get(x_131, 1);
x_141 = lean_ctor_get(x_131, 2);
x_142 = lean_ctor_get(x_131, 3);
lean_inc(x_142);
lean_inc(x_141);
lean_inc(x_140);
lean_dec(x_131);
x_143 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_143, 0, x_129);
lean_ctor_set(x_143, 1, x_140);
lean_ctor_set(x_143, 2, x_141);
lean_ctor_set(x_143, 3, x_142);
x_144 = lean_st_ref_set(x_10, x_143, x_132);
x_145 = lean_ctor_get(x_144, 1);
lean_inc(x_145);
if (lean_is_exclusive(x_144)) {
 lean_ctor_release(x_144, 0);
 lean_ctor_release(x_144, 1);
 x_146 = x_144;
} else {
 lean_dec_ref(x_144);
 x_146 = lean_box(0);
}
if (lean_is_scalar(x_146)) {
 x_147 = lean_alloc_ctor(0, 2, 0);
} else {
 x_147 = x_146;
}
lean_ctor_set(x_147, 0, x_128);
lean_ctor_set(x_147, 1, x_145);
x_65 = x_147;
goto block_69;
}
}
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; uint8_t x_153; lean_object* x_154; uint8_t x_170; lean_object* x_171; lean_object* x_184; lean_object* x_185; lean_object* x_186; uint8_t x_187; 
x_148 = lean_ctor_get(x_48, 3);
lean_inc(x_148);
x_149 = lean_ctor_get(x_48, 4);
lean_inc(x_149);
lean_dec(x_48);
x_150 = lean_st_ref_get(x_10, x_13);
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_150, 1);
lean_inc(x_152);
lean_dec(x_150);
x_184 = lean_ctor_get(x_151, 0);
lean_inc(x_184);
lean_dec(x_151);
x_185 = l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1;
x_186 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_186, 0, x_185);
lean_ctor_set(x_186, 1, x_184);
x_187 = l_Lean_Expr_hasFVar(x_148);
if (x_187 == 0)
{
uint8_t x_188; 
x_188 = l_Lean_Expr_hasMVar(x_148);
if (x_188 == 0)
{
uint8_t x_189; 
lean_dec(x_148);
x_189 = 0;
x_170 = x_189;
x_171 = x_186;
goto block_183;
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; uint8_t x_193; 
lean_inc(x_50);
x_190 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__39___at_Lean_Meta_getFVarSetToGeneralize___spec__47(x_50, x_148, x_186);
x_191 = lean_ctor_get(x_190, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_190, 1);
lean_inc(x_192);
lean_dec(x_190);
x_193 = lean_unbox(x_191);
lean_dec(x_191);
x_170 = x_193;
x_171 = x_192;
goto block_183;
}
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; uint8_t x_197; 
lean_inc(x_50);
x_194 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__50___at_Lean_Meta_getFVarSetToGeneralize___spec__58(x_50, x_148, x_186);
x_195 = lean_ctor_get(x_194, 0);
lean_inc(x_195);
x_196 = lean_ctor_get(x_194, 1);
lean_inc(x_196);
lean_dec(x_194);
x_197 = lean_unbox(x_195);
lean_dec(x_195);
x_170 = x_197;
x_171 = x_196;
goto block_183;
}
block_169:
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; uint8_t x_159; 
x_155 = lean_ctor_get(x_154, 1);
lean_inc(x_155);
lean_dec(x_154);
x_156 = lean_st_ref_take(x_10, x_152);
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_156, 1);
lean_inc(x_158);
lean_dec(x_156);
x_159 = !lean_is_exclusive(x_157);
if (x_159 == 0)
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_160 = lean_ctor_get(x_157, 0);
lean_dec(x_160);
lean_ctor_set(x_157, 0, x_155);
x_161 = lean_st_ref_set(x_10, x_157, x_158);
x_162 = lean_ctor_get(x_161, 1);
lean_inc(x_162);
lean_dec(x_161);
x_53 = x_153;
x_54 = x_162;
goto block_64;
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_163 = lean_ctor_get(x_157, 1);
x_164 = lean_ctor_get(x_157, 2);
x_165 = lean_ctor_get(x_157, 3);
lean_inc(x_165);
lean_inc(x_164);
lean_inc(x_163);
lean_dec(x_157);
x_166 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_166, 0, x_155);
lean_ctor_set(x_166, 1, x_163);
lean_ctor_set(x_166, 2, x_164);
lean_ctor_set(x_166, 3, x_165);
x_167 = lean_st_ref_set(x_10, x_166, x_158);
x_168 = lean_ctor_get(x_167, 1);
lean_inc(x_168);
lean_dec(x_167);
x_53 = x_153;
x_54 = x_168;
goto block_64;
}
}
block_183:
{
if (x_170 == 0)
{
uint8_t x_172; 
x_172 = l_Lean_Expr_hasFVar(x_149);
if (x_172 == 0)
{
uint8_t x_173; 
x_173 = l_Lean_Expr_hasMVar(x_149);
if (x_173 == 0)
{
uint8_t x_174; 
lean_dec(x_149);
x_174 = 0;
x_153 = x_174;
x_154 = x_171;
goto block_169;
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; uint8_t x_178; 
lean_inc(x_50);
lean_inc(x_3);
x_175 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__23(x_3, x_50, x_149, x_171);
x_176 = lean_ctor_get(x_175, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_175, 1);
lean_inc(x_177);
lean_dec(x_175);
x_178 = lean_unbox(x_176);
lean_dec(x_176);
x_153 = x_178;
x_154 = x_177;
goto block_169;
}
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; uint8_t x_182; 
lean_inc(x_50);
lean_inc(x_3);
x_179 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__31(x_3, x_50, x_149, x_171);
x_180 = lean_ctor_get(x_179, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_179, 1);
lean_inc(x_181);
lean_dec(x_179);
x_182 = lean_unbox(x_180);
lean_dec(x_180);
x_153 = x_182;
x_154 = x_181;
goto block_169;
}
}
else
{
lean_dec(x_149);
x_153 = x_170;
x_154 = x_171;
goto block_169;
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
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_Meta_getFVarSetToGeneralize___spec__66(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_1);
x_12 = l_Lean_PersistentArray_forInAux___at_Lean_Meta_getFVarSetToGeneralize___spec__67(x_1, x_2, x_3, x_5, x_11, x_5, x_6, x_7, x_8, x_9, x_10);
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
x_13 = l_Lean_RBNode_insert___at_Lean_FVarIdSet_insert___spec__1(x_4, x_11, x_12);
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
x_21 = l_Lean_PersistentArray_forInAux___at_Lean_Meta_getFVarSetToGeneralize___spec__73(x_1, x_2, x_3, x_4, x_17, x_19, x_10, x_11, x_12, x_13, x_14);
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
x_35 = l_Lean_PersistentArray_forInAux___at_Lean_Meta_getFVarSetToGeneralize___spec__73(x_1, x_2, x_3, x_4, x_17, x_34, x_10, x_11, x_12, x_13, x_14);
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
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_65; lean_object* x_70; lean_object* x_199; 
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
x_199 = l_Lean_RBNode_findCore___at_Lean_Meta_mkGeneralizationForbiddenSet_visit___spec__1(x_1, x_52);
if (lean_obj_tag(x_199) == 0)
{
uint8_t x_200; 
x_200 = l_Lean_LocalDecl_isAuxDecl(x_48);
if (x_200 == 0)
{
uint8_t x_201; uint8_t x_202; 
x_201 = l_Lean_LocalDecl_binderInfo(x_48);
x_202 = l_Lean_BinderInfo_isInstImplicit(x_201);
if (x_202 == 0)
{
if (x_2 == 0)
{
lean_object* x_203; 
x_203 = lean_box(0);
x_70 = x_203;
goto block_198;
}
else
{
uint8_t x_204; 
x_204 = l_Lean_LocalDecl_isLet(x_48);
if (x_204 == 0)
{
lean_object* x_205; 
x_205 = lean_box(0);
x_70 = x_205;
goto block_198;
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; 
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_48);
x_206 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_206, 0, x_49);
lean_ctor_set(x_206, 1, x_50);
x_207 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_207, 0, x_206);
x_208 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_208, 0, x_207);
lean_ctor_set(x_208, 1, x_13);
x_27 = x_208;
goto block_43;
}
}
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; 
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_48);
x_209 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_209, 0, x_49);
lean_ctor_set(x_209, 1, x_50);
x_210 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_210, 0, x_209);
x_211 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_211, 0, x_210);
lean_ctor_set(x_211, 1, x_13);
x_27 = x_211;
goto block_43;
}
}
else
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; 
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_48);
x_212 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_212, 0, x_49);
lean_ctor_set(x_212, 1, x_50);
x_213 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_213, 0, x_212);
x_214 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_214, 0, x_213);
lean_ctor_set(x_214, 1, x_13);
x_27 = x_214;
goto block_43;
}
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; 
lean_dec(x_199);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_48);
x_215 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_215, 0, x_49);
lean_ctor_set(x_215, 1, x_50);
x_216 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_216, 0, x_215);
x_217 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_217, 0, x_216);
lean_ctor_set(x_217, 1, x_13);
x_27 = x_217;
goto block_43;
}
block_64:
{
if (x_53 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_52);
if (lean_is_scalar(x_51)) {
 x_55 = lean_alloc_ctor(0, 2, 0);
} else {
 x_55 = x_51;
}
lean_ctor_set(x_55, 0, x_49);
lean_ctor_set(x_55, 1, x_50);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_55);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_54);
x_27 = x_57;
goto block_43;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_58 = lean_box(0);
lean_inc(x_52);
x_59 = l_Lean_RBNode_insert___at_Lean_FVarIdSet_insert___spec__1(x_49, x_52, x_58);
x_60 = l_Lean_RBNode_insert___at_Lean_FVarIdSet_insert___spec__1(x_50, x_52, x_58);
if (lean_is_scalar(x_51)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_51;
}
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_61);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_54);
x_27 = x_63;
goto block_43;
}
}
block_69:
{
lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
x_68 = lean_unbox(x_66);
lean_dec(x_66);
x_53 = x_68;
x_54 = x_67;
goto block_64;
}
block_198:
{
lean_dec(x_70);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_71 = lean_ctor_get(x_48, 3);
lean_inc(x_71);
lean_dec(x_48);
x_72 = lean_st_ref_get(x_10, x_13);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
x_75 = lean_ctor_get(x_73, 0);
lean_inc(x_75);
lean_dec(x_73);
x_76 = l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1;
lean_inc(x_75);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_75);
x_78 = l_Lean_Expr_hasFVar(x_71);
if (x_78 == 0)
{
uint8_t x_79; 
x_79 = l_Lean_Expr_hasMVar(x_71);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; 
lean_dec(x_77);
lean_dec(x_71);
x_80 = lean_st_ref_take(x_10, x_74);
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec(x_80);
x_83 = !lean_is_exclusive(x_81);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_84 = lean_ctor_get(x_81, 0);
lean_dec(x_84);
lean_ctor_set(x_81, 0, x_75);
x_85 = lean_st_ref_set(x_10, x_81, x_82);
x_86 = !lean_is_exclusive(x_85);
if (x_86 == 0)
{
lean_object* x_87; uint8_t x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_85, 0);
lean_dec(x_87);
x_88 = 0;
x_89 = lean_box(x_88);
lean_ctor_set(x_85, 0, x_89);
x_65 = x_85;
goto block_69;
}
else
{
lean_object* x_90; uint8_t x_91; lean_object* x_92; lean_object* x_93; 
x_90 = lean_ctor_get(x_85, 1);
lean_inc(x_90);
lean_dec(x_85);
x_91 = 0;
x_92 = lean_box(x_91);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_90);
x_65 = x_93;
goto block_69;
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; lean_object* x_102; lean_object* x_103; 
x_94 = lean_ctor_get(x_81, 1);
x_95 = lean_ctor_get(x_81, 2);
x_96 = lean_ctor_get(x_81, 3);
lean_inc(x_96);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_81);
x_97 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_97, 0, x_75);
lean_ctor_set(x_97, 1, x_94);
lean_ctor_set(x_97, 2, x_95);
lean_ctor_set(x_97, 3, x_96);
x_98 = lean_st_ref_set(x_10, x_97, x_82);
x_99 = lean_ctor_get(x_98, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 lean_ctor_release(x_98, 1);
 x_100 = x_98;
} else {
 lean_dec_ref(x_98);
 x_100 = lean_box(0);
}
x_101 = 0;
x_102 = lean_box(x_101);
if (lean_is_scalar(x_100)) {
 x_103 = lean_alloc_ctor(0, 2, 0);
} else {
 x_103 = x_100;
}
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_99);
x_65 = x_103;
goto block_69;
}
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_111; 
lean_dec(x_75);
lean_inc(x_50);
x_104 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__1___at_Lean_Meta_getFVarSetToGeneralize___spec__9(x_50, x_71, x_77);
x_105 = lean_ctor_get(x_104, 1);
lean_inc(x_105);
x_106 = lean_ctor_get(x_104, 0);
lean_inc(x_106);
lean_dec(x_104);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
lean_dec(x_105);
x_108 = lean_st_ref_take(x_10, x_74);
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
lean_dec(x_108);
x_111 = !lean_is_exclusive(x_109);
if (x_111 == 0)
{
lean_object* x_112; lean_object* x_113; uint8_t x_114; 
x_112 = lean_ctor_get(x_109, 0);
lean_dec(x_112);
lean_ctor_set(x_109, 0, x_107);
x_113 = lean_st_ref_set(x_10, x_109, x_110);
x_114 = !lean_is_exclusive(x_113);
if (x_114 == 0)
{
lean_object* x_115; 
x_115 = lean_ctor_get(x_113, 0);
lean_dec(x_115);
lean_ctor_set(x_113, 0, x_106);
x_65 = x_113;
goto block_69;
}
else
{
lean_object* x_116; lean_object* x_117; 
x_116 = lean_ctor_get(x_113, 1);
lean_inc(x_116);
lean_dec(x_113);
x_117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_117, 0, x_106);
lean_ctor_set(x_117, 1, x_116);
x_65 = x_117;
goto block_69;
}
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_118 = lean_ctor_get(x_109, 1);
x_119 = lean_ctor_get(x_109, 2);
x_120 = lean_ctor_get(x_109, 3);
lean_inc(x_120);
lean_inc(x_119);
lean_inc(x_118);
lean_dec(x_109);
x_121 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_121, 0, x_107);
lean_ctor_set(x_121, 1, x_118);
lean_ctor_set(x_121, 2, x_119);
lean_ctor_set(x_121, 3, x_120);
x_122 = lean_st_ref_set(x_10, x_121, x_110);
x_123 = lean_ctor_get(x_122, 1);
lean_inc(x_123);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 lean_ctor_release(x_122, 1);
 x_124 = x_122;
} else {
 lean_dec_ref(x_122);
 x_124 = lean_box(0);
}
if (lean_is_scalar(x_124)) {
 x_125 = lean_alloc_ctor(0, 2, 0);
} else {
 x_125 = x_124;
}
lean_ctor_set(x_125, 0, x_106);
lean_ctor_set(x_125, 1, x_123);
x_65 = x_125;
goto block_69;
}
}
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_133; 
lean_dec(x_75);
lean_inc(x_50);
x_126 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__12___at_Lean_Meta_getFVarSetToGeneralize___spec__20(x_50, x_71, x_77);
x_127 = lean_ctor_get(x_126, 1);
lean_inc(x_127);
x_128 = lean_ctor_get(x_126, 0);
lean_inc(x_128);
lean_dec(x_126);
x_129 = lean_ctor_get(x_127, 1);
lean_inc(x_129);
lean_dec(x_127);
x_130 = lean_st_ref_take(x_10, x_74);
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_130, 1);
lean_inc(x_132);
lean_dec(x_130);
x_133 = !lean_is_exclusive(x_131);
if (x_133 == 0)
{
lean_object* x_134; lean_object* x_135; uint8_t x_136; 
x_134 = lean_ctor_get(x_131, 0);
lean_dec(x_134);
lean_ctor_set(x_131, 0, x_129);
x_135 = lean_st_ref_set(x_10, x_131, x_132);
x_136 = !lean_is_exclusive(x_135);
if (x_136 == 0)
{
lean_object* x_137; 
x_137 = lean_ctor_get(x_135, 0);
lean_dec(x_137);
lean_ctor_set(x_135, 0, x_128);
x_65 = x_135;
goto block_69;
}
else
{
lean_object* x_138; lean_object* x_139; 
x_138 = lean_ctor_get(x_135, 1);
lean_inc(x_138);
lean_dec(x_135);
x_139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_139, 0, x_128);
lean_ctor_set(x_139, 1, x_138);
x_65 = x_139;
goto block_69;
}
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_140 = lean_ctor_get(x_131, 1);
x_141 = lean_ctor_get(x_131, 2);
x_142 = lean_ctor_get(x_131, 3);
lean_inc(x_142);
lean_inc(x_141);
lean_inc(x_140);
lean_dec(x_131);
x_143 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_143, 0, x_129);
lean_ctor_set(x_143, 1, x_140);
lean_ctor_set(x_143, 2, x_141);
lean_ctor_set(x_143, 3, x_142);
x_144 = lean_st_ref_set(x_10, x_143, x_132);
x_145 = lean_ctor_get(x_144, 1);
lean_inc(x_145);
if (lean_is_exclusive(x_144)) {
 lean_ctor_release(x_144, 0);
 lean_ctor_release(x_144, 1);
 x_146 = x_144;
} else {
 lean_dec_ref(x_144);
 x_146 = lean_box(0);
}
if (lean_is_scalar(x_146)) {
 x_147 = lean_alloc_ctor(0, 2, 0);
} else {
 x_147 = x_146;
}
lean_ctor_set(x_147, 0, x_128);
lean_ctor_set(x_147, 1, x_145);
x_65 = x_147;
goto block_69;
}
}
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; uint8_t x_153; lean_object* x_154; uint8_t x_170; lean_object* x_171; lean_object* x_184; lean_object* x_185; lean_object* x_186; uint8_t x_187; 
x_148 = lean_ctor_get(x_48, 3);
lean_inc(x_148);
x_149 = lean_ctor_get(x_48, 4);
lean_inc(x_149);
lean_dec(x_48);
x_150 = lean_st_ref_get(x_10, x_13);
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_150, 1);
lean_inc(x_152);
lean_dec(x_150);
x_184 = lean_ctor_get(x_151, 0);
lean_inc(x_184);
lean_dec(x_151);
x_185 = l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1;
x_186 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_186, 0, x_185);
lean_ctor_set(x_186, 1, x_184);
x_187 = l_Lean_Expr_hasFVar(x_148);
if (x_187 == 0)
{
uint8_t x_188; 
x_188 = l_Lean_Expr_hasMVar(x_148);
if (x_188 == 0)
{
uint8_t x_189; 
lean_dec(x_148);
x_189 = 0;
x_170 = x_189;
x_171 = x_186;
goto block_183;
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; uint8_t x_193; 
lean_inc(x_50);
x_190 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__39___at_Lean_Meta_getFVarSetToGeneralize___spec__47(x_50, x_148, x_186);
x_191 = lean_ctor_get(x_190, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_190, 1);
lean_inc(x_192);
lean_dec(x_190);
x_193 = lean_unbox(x_191);
lean_dec(x_191);
x_170 = x_193;
x_171 = x_192;
goto block_183;
}
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; uint8_t x_197; 
lean_inc(x_50);
x_194 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__50___at_Lean_Meta_getFVarSetToGeneralize___spec__58(x_50, x_148, x_186);
x_195 = lean_ctor_get(x_194, 0);
lean_inc(x_195);
x_196 = lean_ctor_get(x_194, 1);
lean_inc(x_196);
lean_dec(x_194);
x_197 = lean_unbox(x_195);
lean_dec(x_195);
x_170 = x_197;
x_171 = x_196;
goto block_183;
}
block_169:
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; uint8_t x_159; 
x_155 = lean_ctor_get(x_154, 1);
lean_inc(x_155);
lean_dec(x_154);
x_156 = lean_st_ref_take(x_10, x_152);
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_156, 1);
lean_inc(x_158);
lean_dec(x_156);
x_159 = !lean_is_exclusive(x_157);
if (x_159 == 0)
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_160 = lean_ctor_get(x_157, 0);
lean_dec(x_160);
lean_ctor_set(x_157, 0, x_155);
x_161 = lean_st_ref_set(x_10, x_157, x_158);
x_162 = lean_ctor_get(x_161, 1);
lean_inc(x_162);
lean_dec(x_161);
x_53 = x_153;
x_54 = x_162;
goto block_64;
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_163 = lean_ctor_get(x_157, 1);
x_164 = lean_ctor_get(x_157, 2);
x_165 = lean_ctor_get(x_157, 3);
lean_inc(x_165);
lean_inc(x_164);
lean_inc(x_163);
lean_dec(x_157);
x_166 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_166, 0, x_155);
lean_ctor_set(x_166, 1, x_163);
lean_ctor_set(x_166, 2, x_164);
lean_ctor_set(x_166, 3, x_165);
x_167 = lean_st_ref_set(x_10, x_166, x_158);
x_168 = lean_ctor_get(x_167, 1);
lean_inc(x_168);
lean_dec(x_167);
x_53 = x_153;
x_54 = x_168;
goto block_64;
}
}
block_183:
{
if (x_170 == 0)
{
uint8_t x_172; 
x_172 = l_Lean_Expr_hasFVar(x_149);
if (x_172 == 0)
{
uint8_t x_173; 
x_173 = l_Lean_Expr_hasMVar(x_149);
if (x_173 == 0)
{
uint8_t x_174; 
lean_dec(x_149);
x_174 = 0;
x_153 = x_174;
x_154 = x_171;
goto block_169;
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; uint8_t x_178; 
lean_inc(x_50);
lean_inc(x_3);
x_175 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__23(x_3, x_50, x_149, x_171);
x_176 = lean_ctor_get(x_175, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_175, 1);
lean_inc(x_177);
lean_dec(x_175);
x_178 = lean_unbox(x_176);
lean_dec(x_176);
x_153 = x_178;
x_154 = x_177;
goto block_169;
}
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; uint8_t x_182; 
lean_inc(x_50);
lean_inc(x_3);
x_179 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__31(x_3, x_50, x_149, x_171);
x_180 = lean_ctor_get(x_179, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_179, 1);
lean_inc(x_181);
lean_dec(x_179);
x_182 = lean_unbox(x_180);
lean_dec(x_180);
x_153 = x_182;
x_154 = x_181;
goto block_169;
}
}
else
{
lean_dec(x_149);
x_153 = x_170;
x_154 = x_171;
goto block_169;
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
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_Meta_getFVarSetToGeneralize___spec__73(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
x_24 = l_Lean_PersistentArray_forInAux___at_Lean_Meta_getFVarSetToGeneralize___spec__62___lambda__1(x_22, x_23, x_7, x_8, x_9, x_10, x_21);
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
x_43 = l_Lean_PersistentArray_forInAux___at_Lean_Meta_getFVarSetToGeneralize___spec__62___lambda__1(x_41, x_42, x_7, x_8, x_9, x_10, x_40);
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
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_65; lean_object* x_70; lean_object* x_199; 
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
x_199 = l_Lean_RBNode_findCore___at_Lean_Meta_mkGeneralizationForbiddenSet_visit___spec__1(x_1, x_52);
if (lean_obj_tag(x_199) == 0)
{
uint8_t x_200; 
x_200 = l_Lean_LocalDecl_isAuxDecl(x_48);
if (x_200 == 0)
{
uint8_t x_201; uint8_t x_202; 
x_201 = l_Lean_LocalDecl_binderInfo(x_48);
x_202 = l_Lean_BinderInfo_isInstImplicit(x_201);
if (x_202 == 0)
{
if (x_2 == 0)
{
lean_object* x_203; 
x_203 = lean_box(0);
x_70 = x_203;
goto block_198;
}
else
{
uint8_t x_204; 
x_204 = l_Lean_LocalDecl_isLet(x_48);
if (x_204 == 0)
{
lean_object* x_205; 
x_205 = lean_box(0);
x_70 = x_205;
goto block_198;
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; 
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_48);
x_206 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_206, 0, x_49);
lean_ctor_set(x_206, 1, x_50);
x_207 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_207, 0, x_206);
x_208 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_208, 0, x_207);
lean_ctor_set(x_208, 1, x_13);
x_27 = x_208;
goto block_43;
}
}
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; 
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_48);
x_209 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_209, 0, x_49);
lean_ctor_set(x_209, 1, x_50);
x_210 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_210, 0, x_209);
x_211 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_211, 0, x_210);
lean_ctor_set(x_211, 1, x_13);
x_27 = x_211;
goto block_43;
}
}
else
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; 
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_48);
x_212 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_212, 0, x_49);
lean_ctor_set(x_212, 1, x_50);
x_213 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_213, 0, x_212);
x_214 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_214, 0, x_213);
lean_ctor_set(x_214, 1, x_13);
x_27 = x_214;
goto block_43;
}
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; 
lean_dec(x_199);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_48);
x_215 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_215, 0, x_49);
lean_ctor_set(x_215, 1, x_50);
x_216 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_216, 0, x_215);
x_217 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_217, 0, x_216);
lean_ctor_set(x_217, 1, x_13);
x_27 = x_217;
goto block_43;
}
block_64:
{
if (x_53 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_52);
if (lean_is_scalar(x_51)) {
 x_55 = lean_alloc_ctor(0, 2, 0);
} else {
 x_55 = x_51;
}
lean_ctor_set(x_55, 0, x_49);
lean_ctor_set(x_55, 1, x_50);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_55);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_54);
x_27 = x_57;
goto block_43;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_58 = lean_box(0);
lean_inc(x_52);
x_59 = l_Lean_RBNode_insert___at_Lean_FVarIdSet_insert___spec__1(x_49, x_52, x_58);
x_60 = l_Lean_RBNode_insert___at_Lean_FVarIdSet_insert___spec__1(x_50, x_52, x_58);
if (lean_is_scalar(x_51)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_51;
}
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_61);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_54);
x_27 = x_63;
goto block_43;
}
}
block_69:
{
lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
x_68 = lean_unbox(x_66);
lean_dec(x_66);
x_53 = x_68;
x_54 = x_67;
goto block_64;
}
block_198:
{
lean_dec(x_70);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_71 = lean_ctor_get(x_48, 3);
lean_inc(x_71);
lean_dec(x_48);
x_72 = lean_st_ref_get(x_10, x_13);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
x_75 = lean_ctor_get(x_73, 0);
lean_inc(x_75);
lean_dec(x_73);
x_76 = l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1;
lean_inc(x_75);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_75);
x_78 = l_Lean_Expr_hasFVar(x_71);
if (x_78 == 0)
{
uint8_t x_79; 
x_79 = l_Lean_Expr_hasMVar(x_71);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; 
lean_dec(x_77);
lean_dec(x_71);
x_80 = lean_st_ref_take(x_10, x_74);
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec(x_80);
x_83 = !lean_is_exclusive(x_81);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_84 = lean_ctor_get(x_81, 0);
lean_dec(x_84);
lean_ctor_set(x_81, 0, x_75);
x_85 = lean_st_ref_set(x_10, x_81, x_82);
x_86 = !lean_is_exclusive(x_85);
if (x_86 == 0)
{
lean_object* x_87; uint8_t x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_85, 0);
lean_dec(x_87);
x_88 = 0;
x_89 = lean_box(x_88);
lean_ctor_set(x_85, 0, x_89);
x_65 = x_85;
goto block_69;
}
else
{
lean_object* x_90; uint8_t x_91; lean_object* x_92; lean_object* x_93; 
x_90 = lean_ctor_get(x_85, 1);
lean_inc(x_90);
lean_dec(x_85);
x_91 = 0;
x_92 = lean_box(x_91);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_90);
x_65 = x_93;
goto block_69;
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; lean_object* x_102; lean_object* x_103; 
x_94 = lean_ctor_get(x_81, 1);
x_95 = lean_ctor_get(x_81, 2);
x_96 = lean_ctor_get(x_81, 3);
lean_inc(x_96);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_81);
x_97 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_97, 0, x_75);
lean_ctor_set(x_97, 1, x_94);
lean_ctor_set(x_97, 2, x_95);
lean_ctor_set(x_97, 3, x_96);
x_98 = lean_st_ref_set(x_10, x_97, x_82);
x_99 = lean_ctor_get(x_98, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 lean_ctor_release(x_98, 1);
 x_100 = x_98;
} else {
 lean_dec_ref(x_98);
 x_100 = lean_box(0);
}
x_101 = 0;
x_102 = lean_box(x_101);
if (lean_is_scalar(x_100)) {
 x_103 = lean_alloc_ctor(0, 2, 0);
} else {
 x_103 = x_100;
}
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_99);
x_65 = x_103;
goto block_69;
}
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_111; 
lean_dec(x_75);
lean_inc(x_50);
x_104 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__1___at_Lean_Meta_getFVarSetToGeneralize___spec__9(x_50, x_71, x_77);
x_105 = lean_ctor_get(x_104, 1);
lean_inc(x_105);
x_106 = lean_ctor_get(x_104, 0);
lean_inc(x_106);
lean_dec(x_104);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
lean_dec(x_105);
x_108 = lean_st_ref_take(x_10, x_74);
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
lean_dec(x_108);
x_111 = !lean_is_exclusive(x_109);
if (x_111 == 0)
{
lean_object* x_112; lean_object* x_113; uint8_t x_114; 
x_112 = lean_ctor_get(x_109, 0);
lean_dec(x_112);
lean_ctor_set(x_109, 0, x_107);
x_113 = lean_st_ref_set(x_10, x_109, x_110);
x_114 = !lean_is_exclusive(x_113);
if (x_114 == 0)
{
lean_object* x_115; 
x_115 = lean_ctor_get(x_113, 0);
lean_dec(x_115);
lean_ctor_set(x_113, 0, x_106);
x_65 = x_113;
goto block_69;
}
else
{
lean_object* x_116; lean_object* x_117; 
x_116 = lean_ctor_get(x_113, 1);
lean_inc(x_116);
lean_dec(x_113);
x_117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_117, 0, x_106);
lean_ctor_set(x_117, 1, x_116);
x_65 = x_117;
goto block_69;
}
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_118 = lean_ctor_get(x_109, 1);
x_119 = lean_ctor_get(x_109, 2);
x_120 = lean_ctor_get(x_109, 3);
lean_inc(x_120);
lean_inc(x_119);
lean_inc(x_118);
lean_dec(x_109);
x_121 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_121, 0, x_107);
lean_ctor_set(x_121, 1, x_118);
lean_ctor_set(x_121, 2, x_119);
lean_ctor_set(x_121, 3, x_120);
x_122 = lean_st_ref_set(x_10, x_121, x_110);
x_123 = lean_ctor_get(x_122, 1);
lean_inc(x_123);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 lean_ctor_release(x_122, 1);
 x_124 = x_122;
} else {
 lean_dec_ref(x_122);
 x_124 = lean_box(0);
}
if (lean_is_scalar(x_124)) {
 x_125 = lean_alloc_ctor(0, 2, 0);
} else {
 x_125 = x_124;
}
lean_ctor_set(x_125, 0, x_106);
lean_ctor_set(x_125, 1, x_123);
x_65 = x_125;
goto block_69;
}
}
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_133; 
lean_dec(x_75);
lean_inc(x_50);
x_126 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__12___at_Lean_Meta_getFVarSetToGeneralize___spec__20(x_50, x_71, x_77);
x_127 = lean_ctor_get(x_126, 1);
lean_inc(x_127);
x_128 = lean_ctor_get(x_126, 0);
lean_inc(x_128);
lean_dec(x_126);
x_129 = lean_ctor_get(x_127, 1);
lean_inc(x_129);
lean_dec(x_127);
x_130 = lean_st_ref_take(x_10, x_74);
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_130, 1);
lean_inc(x_132);
lean_dec(x_130);
x_133 = !lean_is_exclusive(x_131);
if (x_133 == 0)
{
lean_object* x_134; lean_object* x_135; uint8_t x_136; 
x_134 = lean_ctor_get(x_131, 0);
lean_dec(x_134);
lean_ctor_set(x_131, 0, x_129);
x_135 = lean_st_ref_set(x_10, x_131, x_132);
x_136 = !lean_is_exclusive(x_135);
if (x_136 == 0)
{
lean_object* x_137; 
x_137 = lean_ctor_get(x_135, 0);
lean_dec(x_137);
lean_ctor_set(x_135, 0, x_128);
x_65 = x_135;
goto block_69;
}
else
{
lean_object* x_138; lean_object* x_139; 
x_138 = lean_ctor_get(x_135, 1);
lean_inc(x_138);
lean_dec(x_135);
x_139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_139, 0, x_128);
lean_ctor_set(x_139, 1, x_138);
x_65 = x_139;
goto block_69;
}
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_140 = lean_ctor_get(x_131, 1);
x_141 = lean_ctor_get(x_131, 2);
x_142 = lean_ctor_get(x_131, 3);
lean_inc(x_142);
lean_inc(x_141);
lean_inc(x_140);
lean_dec(x_131);
x_143 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_143, 0, x_129);
lean_ctor_set(x_143, 1, x_140);
lean_ctor_set(x_143, 2, x_141);
lean_ctor_set(x_143, 3, x_142);
x_144 = lean_st_ref_set(x_10, x_143, x_132);
x_145 = lean_ctor_get(x_144, 1);
lean_inc(x_145);
if (lean_is_exclusive(x_144)) {
 lean_ctor_release(x_144, 0);
 lean_ctor_release(x_144, 1);
 x_146 = x_144;
} else {
 lean_dec_ref(x_144);
 x_146 = lean_box(0);
}
if (lean_is_scalar(x_146)) {
 x_147 = lean_alloc_ctor(0, 2, 0);
} else {
 x_147 = x_146;
}
lean_ctor_set(x_147, 0, x_128);
lean_ctor_set(x_147, 1, x_145);
x_65 = x_147;
goto block_69;
}
}
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; uint8_t x_153; lean_object* x_154; uint8_t x_170; lean_object* x_171; lean_object* x_184; lean_object* x_185; lean_object* x_186; uint8_t x_187; 
x_148 = lean_ctor_get(x_48, 3);
lean_inc(x_148);
x_149 = lean_ctor_get(x_48, 4);
lean_inc(x_149);
lean_dec(x_48);
x_150 = lean_st_ref_get(x_10, x_13);
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_150, 1);
lean_inc(x_152);
lean_dec(x_150);
x_184 = lean_ctor_get(x_151, 0);
lean_inc(x_184);
lean_dec(x_151);
x_185 = l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1;
x_186 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_186, 0, x_185);
lean_ctor_set(x_186, 1, x_184);
x_187 = l_Lean_Expr_hasFVar(x_148);
if (x_187 == 0)
{
uint8_t x_188; 
x_188 = l_Lean_Expr_hasMVar(x_148);
if (x_188 == 0)
{
uint8_t x_189; 
lean_dec(x_148);
x_189 = 0;
x_170 = x_189;
x_171 = x_186;
goto block_183;
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; uint8_t x_193; 
lean_inc(x_50);
x_190 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__39___at_Lean_Meta_getFVarSetToGeneralize___spec__47(x_50, x_148, x_186);
x_191 = lean_ctor_get(x_190, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_190, 1);
lean_inc(x_192);
lean_dec(x_190);
x_193 = lean_unbox(x_191);
lean_dec(x_191);
x_170 = x_193;
x_171 = x_192;
goto block_183;
}
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; uint8_t x_197; 
lean_inc(x_50);
x_194 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__50___at_Lean_Meta_getFVarSetToGeneralize___spec__58(x_50, x_148, x_186);
x_195 = lean_ctor_get(x_194, 0);
lean_inc(x_195);
x_196 = lean_ctor_get(x_194, 1);
lean_inc(x_196);
lean_dec(x_194);
x_197 = lean_unbox(x_195);
lean_dec(x_195);
x_170 = x_197;
x_171 = x_196;
goto block_183;
}
block_169:
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; uint8_t x_159; 
x_155 = lean_ctor_get(x_154, 1);
lean_inc(x_155);
lean_dec(x_154);
x_156 = lean_st_ref_take(x_10, x_152);
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_156, 1);
lean_inc(x_158);
lean_dec(x_156);
x_159 = !lean_is_exclusive(x_157);
if (x_159 == 0)
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_160 = lean_ctor_get(x_157, 0);
lean_dec(x_160);
lean_ctor_set(x_157, 0, x_155);
x_161 = lean_st_ref_set(x_10, x_157, x_158);
x_162 = lean_ctor_get(x_161, 1);
lean_inc(x_162);
lean_dec(x_161);
x_53 = x_153;
x_54 = x_162;
goto block_64;
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_163 = lean_ctor_get(x_157, 1);
x_164 = lean_ctor_get(x_157, 2);
x_165 = lean_ctor_get(x_157, 3);
lean_inc(x_165);
lean_inc(x_164);
lean_inc(x_163);
lean_dec(x_157);
x_166 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_166, 0, x_155);
lean_ctor_set(x_166, 1, x_163);
lean_ctor_set(x_166, 2, x_164);
lean_ctor_set(x_166, 3, x_165);
x_167 = lean_st_ref_set(x_10, x_166, x_158);
x_168 = lean_ctor_get(x_167, 1);
lean_inc(x_168);
lean_dec(x_167);
x_53 = x_153;
x_54 = x_168;
goto block_64;
}
}
block_183:
{
if (x_170 == 0)
{
uint8_t x_172; 
x_172 = l_Lean_Expr_hasFVar(x_149);
if (x_172 == 0)
{
uint8_t x_173; 
x_173 = l_Lean_Expr_hasMVar(x_149);
if (x_173 == 0)
{
uint8_t x_174; 
lean_dec(x_149);
x_174 = 0;
x_153 = x_174;
x_154 = x_171;
goto block_169;
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; uint8_t x_178; 
lean_inc(x_50);
lean_inc(x_3);
x_175 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__23(x_3, x_50, x_149, x_171);
x_176 = lean_ctor_get(x_175, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_175, 1);
lean_inc(x_177);
lean_dec(x_175);
x_178 = lean_unbox(x_176);
lean_dec(x_176);
x_153 = x_178;
x_154 = x_177;
goto block_169;
}
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; uint8_t x_182; 
lean_inc(x_50);
lean_inc(x_3);
x_179 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__31(x_3, x_50, x_149, x_171);
x_180 = lean_ctor_get(x_179, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_179, 1);
lean_inc(x_181);
lean_dec(x_179);
x_182 = lean_unbox(x_180);
lean_dec(x_180);
x_153 = x_182;
x_154 = x_181;
goto block_169;
}
}
else
{
lean_dec(x_149);
x_153 = x_170;
x_154 = x_171;
goto block_169;
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
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_Meta_getFVarSetToGeneralize___spec__72(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_1);
x_12 = l_Lean_PersistentArray_forInAux___at_Lean_Meta_getFVarSetToGeneralize___spec__73(x_1, x_2, x_3, x_5, x_11, x_5, x_6, x_7, x_8, x_9, x_10);
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
x_17 = l_Lean_PersistentArray_forIn___at_Lean_Meta_getFVarSetToGeneralize___spec__61(x_2, x_3, x_15, x_14, x_16, x_4, x_5, x_6, x_7, x_8);
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
x_30 = l_Lean_PersistentArray_forIn___at_Lean_Meta_getFVarSetToGeneralize___spec__66(x_2, x_3, x_28, x_26, x_29, x_4, x_5, x_6, x_7, x_8);
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
x_43 = l_Lean_PersistentArray_forIn___at_Lean_Meta_getFVarSetToGeneralize___spec__72(x_2, x_3, x_42, x_26, x_41, x_4, x_5, x_6, x_7, x_8);
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
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at_Lean_Meta_getFVarSetToGeneralize___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_PersistentArray_anyMAux___at_Lean_Meta_getFVarSetToGeneralize___spec__5(x_1, x_2, x_3);
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
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__4(x_1, x_2, x_3);
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
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at_Lean_Meta_getFVarSetToGeneralize___spec__16___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_PersistentArray_anyMAux___at_Lean_Meta_getFVarSetToGeneralize___spec__16(x_1, x_2, x_3);
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
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__15___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__15(x_1, x_2, x_3);
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
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at_Lean_Meta_getFVarSetToGeneralize___spec__27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_PersistentArray_anyMAux___at_Lean_Meta_getFVarSetToGeneralize___spec__27(x_1, x_2, x_3);
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
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__26___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__26(x_1, x_2, x_3);
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
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at_Lean_Meta_getFVarSetToGeneralize___spec__35___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_PersistentArray_anyMAux___at_Lean_Meta_getFVarSetToGeneralize___spec__35(x_1, x_2, x_3);
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
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__34___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__34(x_1, x_2, x_3);
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
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at_Lean_Meta_getFVarSetToGeneralize___spec__43___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_PersistentArray_anyMAux___at_Lean_Meta_getFVarSetToGeneralize___spec__43(x_1, x_2, x_3);
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
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__42___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__42(x_1, x_2, x_3);
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
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at_Lean_Meta_getFVarSetToGeneralize___spec__54___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_PersistentArray_anyMAux___at_Lean_Meta_getFVarSetToGeneralize___spec__54(x_1, x_2, x_3);
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
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__53___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__53(x_1, x_2, x_3);
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
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_Meta_getFVarSetToGeneralize___spec__62___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PersistentArray_forInAux___at_Lean_Meta_getFVarSetToGeneralize___spec__62___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_Meta_getFVarSetToGeneralize___spec__62___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_2);
lean_dec(x_2);
x_13 = l_Lean_PersistentArray_forInAux___at_Lean_Meta_getFVarSetToGeneralize___spec__62(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_Meta_getFVarSetToGeneralize___spec__61___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PersistentArray_forIn___at_Lean_Meta_getFVarSetToGeneralize___spec__61___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_Meta_getFVarSetToGeneralize___spec__61___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_2);
lean_dec(x_2);
x_12 = l_Lean_PersistentArray_forIn___at_Lean_Meta_getFVarSetToGeneralize___spec__61(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_Meta_getFVarSetToGeneralize___spec__67___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_2);
lean_dec(x_2);
x_13 = l_Lean_PersistentArray_forInAux___at_Lean_Meta_getFVarSetToGeneralize___spec__67(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_Meta_getFVarSetToGeneralize___spec__66___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_2);
lean_dec(x_2);
x_12 = l_Lean_PersistentArray_forIn___at_Lean_Meta_getFVarSetToGeneralize___spec__66(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_Meta_getFVarSetToGeneralize___spec__73___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_2);
lean_dec(x_2);
x_13 = l_Lean_PersistentArray_forInAux___at_Lean_Meta_getFVarSetToGeneralize___spec__73(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_Meta_getFVarSetToGeneralize___spec__72___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_2);
lean_dec(x_2);
x_12 = l_Lean_PersistentArray_forIn___at_Lean_Meta_getFVarSetToGeneralize___spec__72(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at_Lean_Meta_getFVarsToGeneralize___spec__2(lean_object* x_1, lean_object* x_2) {
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
x_6 = l_Lean_RBNode_fold___at_Lean_Meta_getFVarsToGeneralize___spec__2(x_1, x_3);
x_7 = lean_array_push(x_6, x_4);
x_1 = x_7;
x_2 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_toArray___at_Lean_Meta_getFVarsToGeneralize___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__2;
x_3 = l_Lean_RBNode_fold___at_Lean_Meta_getFVarsToGeneralize___spec__2(x_2, x_1);
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
x_15 = l_Lean_RBTree_toArray___at_Lean_Meta_getFVarsToGeneralize___spec__1(x_13);
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
