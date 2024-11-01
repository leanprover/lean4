// Lean compiler output
// Module: Lean.Meta.GeneralizeVars
// Imports: Lean.Meta.Basic Lean.Util.CollectFVars
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
static lean_object* l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at_Lean_Meta_getFVarSetToGeneralize___spec__2___at_Lean_Meta_getFVarSetToGeneralize___spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkGeneralizationForbiddenSet_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at_Lean_Meta_getFVarSetToGeneralize___spec__16___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__6(lean_object*, lean_object*, lean_object*, size_t, size_t);
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
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at_Lean_Meta_getFVarSetToGeneralize___spec__27___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_getFVarSetToGeneralize___spec__74___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getFVarsToGeneralize(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkGeneralizationForbiddenSet_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__57___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__26(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_getFVarSetToGeneralize___closed__1;
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyMAux___at_Lean_Meta_getFVarSetToGeneralize___spec__27(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at_Lean_Meta_getFVarSetToGeneralize___spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at_Lean_Meta_getFVarSetToGeneralize___spec__13___at_Lean_Meta_getFVarSetToGeneralize___spec__21(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___at_Lean_Meta_mkGeneralizationForbiddenSet_visit___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_getFVarSetToGeneralize___spec__65___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__12(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_Meta_getFVarSetToGeneralize___spec__61(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkGeneralizationForbiddenSet_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkGeneralizationForbiddenSet_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* lean_array_to_list(lean_object*);
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
static lean_object* l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__5;
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
lean_object* lean_array_mk(lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_getFVarSetToGeneralize___spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_quickCmp(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_getFVarSetToGeneralize___spec__76(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getFVarsToGeneralize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_Meta_getFVarSetToGeneralize___spec__73___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___at_Lean_Meta_mkGeneralizationForbiddenSet_visit___spec__1___boxed(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
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
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
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
x_17 = !lean_is_exclusive(x_14);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_ctor_get(x_14, 1);
x_19 = lean_ctor_get(x_14, 0);
lean_dec(x_19);
x_20 = !lean_is_exclusive(x_16);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_16, 0);
x_22 = lean_ctor_get(x_16, 1);
x_23 = l_Lean_RBNode_findCore___at_Lean_Meta_mkGeneralizationForbiddenSet_visit___spec__1(x_21, x_12);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; 
lean_inc(x_12);
lean_ctor_set_tag(x_14, 1);
lean_ctor_set(x_14, 1, x_22);
lean_ctor_set(x_14, 0, x_12);
x_24 = lean_box(0);
x_25 = l_Lean_RBNode_insert___at_Lean_FVarIdSet_insert___spec__1(x_21, x_12, x_24);
lean_ctor_set(x_16, 1, x_14);
lean_ctor_set(x_16, 0, x_25);
x_2 = x_13;
x_3 = x_16;
x_8 = x_18;
goto _start;
}
else
{
lean_dec(x_23);
lean_free_object(x_14);
lean_dec(x_12);
x_2 = x_13;
x_3 = x_16;
x_8 = x_18;
goto _start;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_16, 0);
x_29 = lean_ctor_get(x_16, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_16);
x_30 = l_Lean_RBNode_findCore___at_Lean_Meta_mkGeneralizationForbiddenSet_visit___spec__1(x_28, x_12);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_inc(x_12);
lean_ctor_set_tag(x_14, 1);
lean_ctor_set(x_14, 1, x_29);
lean_ctor_set(x_14, 0, x_12);
x_31 = lean_box(0);
x_32 = l_Lean_RBNode_insert___at_Lean_FVarIdSet_insert___spec__1(x_28, x_12, x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_14);
x_2 = x_13;
x_3 = x_33;
x_8 = x_18;
goto _start;
}
else
{
lean_object* x_35; 
lean_dec(x_30);
lean_free_object(x_14);
lean_dec(x_12);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_28);
lean_ctor_set(x_35, 1, x_29);
x_2 = x_13;
x_3 = x_35;
x_8 = x_18;
goto _start;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_37 = lean_ctor_get(x_14, 1);
lean_inc(x_37);
lean_dec(x_14);
x_38 = lean_ctor_get(x_16, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_16, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_40 = x_16;
} else {
 lean_dec_ref(x_16);
 x_40 = lean_box(0);
}
x_41 = l_Lean_RBNode_findCore___at_Lean_Meta_mkGeneralizationForbiddenSet_visit___spec__1(x_38, x_12);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_inc(x_12);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_12);
lean_ctor_set(x_42, 1, x_39);
x_43 = lean_box(0);
x_44 = l_Lean_RBNode_insert___at_Lean_FVarIdSet_insert___spec__1(x_38, x_12, x_43);
if (lean_is_scalar(x_40)) {
 x_45 = lean_alloc_ctor(0, 2, 0);
} else {
 x_45 = x_40;
}
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_42);
x_2 = x_13;
x_3 = x_45;
x_8 = x_37;
goto _start;
}
else
{
lean_object* x_47; 
lean_dec(x_41);
lean_dec(x_12);
if (lean_is_scalar(x_40)) {
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_40;
}
lean_ctor_set(x_47, 0, x_38);
lean_ctor_set(x_47, 1, x_39);
x_2 = x_13;
x_3 = x_47;
x_8 = x_37;
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
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
x_16 = !lean_is_exclusive(x_13);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_13, 1);
x_18 = lean_ctor_get(x_13, 0);
lean_dec(x_18);
x_19 = !lean_is_exclusive(x_15);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_15, 0);
x_21 = lean_ctor_get(x_15, 1);
x_22 = l_Lean_RBNode_findCore___at_Lean_Meta_mkGeneralizationForbiddenSet_visit___spec__1(x_20, x_11);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; 
lean_inc(x_11);
lean_ctor_set_tag(x_13, 1);
lean_ctor_set(x_13, 1, x_21);
lean_ctor_set(x_13, 0, x_11);
x_23 = lean_box(0);
x_24 = l_Lean_RBNode_insert___at_Lean_FVarIdSet_insert___spec__1(x_20, x_11, x_23);
lean_ctor_set(x_15, 1, x_13);
lean_ctor_set(x_15, 0, x_24);
x_1 = x_12;
x_2 = x_15;
x_7 = x_17;
goto _start;
}
else
{
lean_dec(x_22);
lean_free_object(x_13);
lean_dec(x_11);
x_1 = x_12;
x_2 = x_15;
x_7 = x_17;
goto _start;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_15, 0);
x_28 = lean_ctor_get(x_15, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_15);
x_29 = l_Lean_RBNode_findCore___at_Lean_Meta_mkGeneralizationForbiddenSet_visit___spec__1(x_27, x_11);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_inc(x_11);
lean_ctor_set_tag(x_13, 1);
lean_ctor_set(x_13, 1, x_28);
lean_ctor_set(x_13, 0, x_11);
x_30 = lean_box(0);
x_31 = l_Lean_RBNode_insert___at_Lean_FVarIdSet_insert___spec__1(x_27, x_11, x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_13);
x_1 = x_12;
x_2 = x_32;
x_7 = x_17;
goto _start;
}
else
{
lean_object* x_34; 
lean_dec(x_29);
lean_free_object(x_13);
lean_dec(x_11);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_27);
lean_ctor_set(x_34, 1, x_28);
x_1 = x_12;
x_2 = x_34;
x_7 = x_17;
goto _start;
}
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_36 = lean_ctor_get(x_13, 1);
lean_inc(x_36);
lean_dec(x_13);
x_37 = lean_ctor_get(x_15, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_15, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_39 = x_15;
} else {
 lean_dec_ref(x_15);
 x_39 = lean_box(0);
}
x_40 = l_Lean_RBNode_findCore___at_Lean_Meta_mkGeneralizationForbiddenSet_visit___spec__1(x_37, x_11);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_inc(x_11);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_11);
lean_ctor_set(x_41, 1, x_38);
x_42 = lean_box(0);
x_43 = l_Lean_RBNode_insert___at_Lean_FVarIdSet_insert___spec__1(x_37, x_11, x_42);
if (lean_is_scalar(x_39)) {
 x_44 = lean_alloc_ctor(0, 2, 0);
} else {
 x_44 = x_39;
}
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_41);
x_1 = x_12;
x_2 = x_44;
x_7 = x_36;
goto _start;
}
else
{
lean_object* x_46; 
lean_dec(x_40);
lean_dec(x_11);
if (lean_is_scalar(x_39)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_39;
}
lean_ctor_set(x_46, 0, x_37);
lean_ctor_set(x_46, 1, x_38);
x_1 = x_12;
x_2 = x_46;
x_7 = x_36;
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
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_12, 0);
lean_dec(x_16);
x_17 = !lean_is_exclusive(x_14);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_14, 0);
x_19 = lean_ctor_get(x_14, 1);
lean_ctor_set(x_14, 1, x_18);
lean_ctor_set(x_14, 0, x_19);
lean_ctor_set(x_12, 0, x_14);
return x_12;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_14, 0);
x_21 = lean_ctor_get(x_14, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_14);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
lean_ctor_set(x_12, 0, x_22);
return x_12;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_23 = lean_ctor_get(x_12, 1);
lean_inc(x_23);
lean_dec(x_12);
x_24 = lean_ctor_get(x_14, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_14, 1);
lean_inc(x_25);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_26 = x_14;
} else {
 lean_dec_ref(x_14);
 x_26 = lean_box(0);
}
if (lean_is_scalar(x_26)) {
 x_27 = lean_alloc_ctor(0, 2, 0);
} else {
 x_27 = x_26;
}
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_24);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_23);
return x_28;
}
}
}
static lean_object* _init_l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(10u);
x_2 = lean_unsigned_to_nat(1u);
x_3 = l_Nat_nextPowerOfTwo_go(x_1, x_2, lean_box(0));
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1;
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__3;
x_3 = l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__4;
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
x_16 = l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__5;
x_17 = l_Lean_CollectFVars_main(x_14, x_16);
x_18 = l_Lean_LocalDecl_value_x3f(x_10);
lean_dec(x_10);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_box(0);
x_20 = l_Lean_Meta_mkGeneralizationForbiddenSet_visit___lambda__1(x_3, x_2, x_17, x_19, x_4, x_5, x_6, x_7, x_15);
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
lean_dec(x_4);
return x_27;
}
}
else
{
uint8_t x_28; 
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
LEAN_EXPORT lean_object* l_Lean_Meta_mkGeneralizationForbiddenSet_visit___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_mkGeneralizationForbiddenSet_visit(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkGeneralizationForbiddenSet_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_8; 
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
LEAN_EXPORT lean_object* l_Lean_Meta_mkGeneralizationForbiddenSet_loop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_mkGeneralizationForbiddenSet_loop(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_8;
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
lean_dec(x_12);
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
lean_dec(x_12);
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; 
x_8 = l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__3;
x_9 = l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__4;
x_10 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_2);
lean_ctor_set(x_10, 2, x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
x_12 = lean_array_size(x_1);
x_13 = 0;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_14 = l_Array_forInUnsafe_loop___at_Lean_Meta_mkGeneralizationForbiddenSet___spec__1(x_1, x_12, x_13, x_11, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
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
x_19 = lean_array_to_list(x_18);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = l_Lean_Meta_mkGeneralizationForbiddenSet_loop(x_19, x_20, x_3, x_4, x_5, x_6, x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_21;
}
else
{
uint8_t x_22; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_22 = !lean_is_exclusive(x_14);
if (x_22 == 0)
{
return x_14;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_14, 0);
x_24 = lean_ctor_get(x_14, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_14);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
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
lean_dec(x_7);
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
x_5 = lean_array_get_size(x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_lt(x_6, x_5);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_5);
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
return x_11;
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_3, 0);
x_13 = lean_array_get_size(x_12);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_lt(x_14, x_13);
if (x_15 == 0)
{
uint8_t x_16; 
lean_dec(x_13);
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
lean_inc(x_2);
lean_inc(x_1);
x_5 = l_Lean_PersistentArray_anyMAux___at_Lean_Meta_getFVarSetToGeneralize___spec__5(x_1, x_2, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_array_get_size(x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_lt(x_8, x_7);
if (x_9 == 0)
{
uint8_t x_10; 
lean_dec(x_7);
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
return x_13;
}
}
else
{
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
lean_dec(x_13);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = l_Lean_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__4(x_1, x_2, x_22);
lean_dec(x_22);
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
lean_dec(x_13);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = l_Lean_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__4(x_1, x_2, x_29);
lean_dec(x_29);
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
lean_dec(x_12);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at_Lean_Meta_getFVarSetToGeneralize___spec__2___at_Lean_Meta_getFVarSetToGeneralize___spec__10___closed__1;
x_23 = l_Lean_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__4(x_22, x_1, x_21);
lean_dec(x_21);
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
lean_dec(x_12);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at_Lean_Meta_getFVarSetToGeneralize___spec__2___at_Lean_Meta_getFVarSetToGeneralize___spec__10___closed__1;
x_31 = l_Lean_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__4(x_30, x_1, x_29);
lean_dec(x_29);
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
lean_dec(x_7);
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
x_5 = lean_array_get_size(x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_lt(x_6, x_5);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_5);
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
return x_11;
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_3, 0);
x_13 = lean_array_get_size(x_12);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_lt(x_14, x_13);
if (x_15 == 0)
{
uint8_t x_16; 
lean_dec(x_13);
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
lean_inc(x_2);
lean_inc(x_1);
x_5 = l_Lean_PersistentArray_anyMAux___at_Lean_Meta_getFVarSetToGeneralize___spec__16(x_1, x_2, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_array_get_size(x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_lt(x_8, x_7);
if (x_9 == 0)
{
uint8_t x_10; 
lean_dec(x_7);
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
return x_13;
}
}
else
{
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
lean_dec(x_13);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = l_Lean_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__15(x_1, x_2, x_22);
lean_dec(x_22);
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
lean_dec(x_13);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = l_Lean_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__15(x_1, x_2, x_29);
lean_dec(x_29);
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
lean_dec(x_12);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at_Lean_Meta_getFVarSetToGeneralize___spec__2___at_Lean_Meta_getFVarSetToGeneralize___spec__10___closed__1;
x_23 = l_Lean_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__15(x_22, x_1, x_21);
lean_dec(x_21);
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
lean_dec(x_12);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at_Lean_Meta_getFVarSetToGeneralize___spec__2___at_Lean_Meta_getFVarSetToGeneralize___spec__10___closed__1;
x_31 = l_Lean_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__15(x_30, x_1, x_29);
lean_dec(x_29);
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
lean_dec(x_7);
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
x_5 = lean_array_get_size(x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_lt(x_6, x_5);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_5);
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
return x_11;
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_3, 0);
x_13 = lean_array_get_size(x_12);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_lt(x_14, x_13);
if (x_15 == 0)
{
uint8_t x_16; 
lean_dec(x_13);
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
lean_inc(x_2);
lean_inc(x_1);
x_5 = l_Lean_PersistentArray_anyMAux___at_Lean_Meta_getFVarSetToGeneralize___spec__27(x_1, x_2, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_array_get_size(x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_lt(x_8, x_7);
if (x_9 == 0)
{
uint8_t x_10; 
lean_dec(x_7);
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
return x_13;
}
}
else
{
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
lean_dec(x_13);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = l_Lean_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__26(x_1, x_2, x_22);
lean_dec(x_22);
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
lean_dec(x_13);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = l_Lean_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__26(x_1, x_2, x_29);
lean_dec(x_29);
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
lean_dec(x_7);
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
x_5 = lean_array_get_size(x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_lt(x_6, x_5);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_5);
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
return x_11;
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_3, 0);
x_13 = lean_array_get_size(x_12);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_lt(x_14, x_13);
if (x_15 == 0)
{
uint8_t x_16; 
lean_dec(x_13);
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
lean_inc(x_2);
lean_inc(x_1);
x_5 = l_Lean_PersistentArray_anyMAux___at_Lean_Meta_getFVarSetToGeneralize___spec__35(x_1, x_2, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_array_get_size(x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_lt(x_8, x_7);
if (x_9 == 0)
{
uint8_t x_10; 
lean_dec(x_7);
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
return x_13;
}
}
else
{
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
lean_dec(x_13);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = l_Lean_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__34(x_1, x_2, x_22);
lean_dec(x_22);
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
lean_dec(x_13);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = l_Lean_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__34(x_1, x_2, x_29);
lean_dec(x_29);
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
lean_dec(x_7);
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
x_5 = lean_array_get_size(x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_lt(x_6, x_5);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_5);
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
return x_11;
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_3, 0);
x_13 = lean_array_get_size(x_12);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_lt(x_14, x_13);
if (x_15 == 0)
{
uint8_t x_16; 
lean_dec(x_13);
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
lean_inc(x_2);
lean_inc(x_1);
x_5 = l_Lean_PersistentArray_anyMAux___at_Lean_Meta_getFVarSetToGeneralize___spec__43(x_1, x_2, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_array_get_size(x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_lt(x_8, x_7);
if (x_9 == 0)
{
uint8_t x_10; 
lean_dec(x_7);
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
return x_13;
}
}
else
{
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
lean_dec(x_13);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = l_Lean_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__42(x_1, x_2, x_22);
lean_dec(x_22);
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
lean_dec(x_13);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = l_Lean_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__42(x_1, x_2, x_29);
lean_dec(x_29);
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
lean_dec(x_12);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at_Lean_Meta_getFVarSetToGeneralize___spec__2___at_Lean_Meta_getFVarSetToGeneralize___spec__10___closed__1;
x_23 = l_Lean_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__42(x_22, x_1, x_21);
lean_dec(x_21);
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
lean_dec(x_12);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at_Lean_Meta_getFVarSetToGeneralize___spec__2___at_Lean_Meta_getFVarSetToGeneralize___spec__10___closed__1;
x_31 = l_Lean_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__42(x_30, x_1, x_29);
lean_dec(x_29);
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
lean_dec(x_7);
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
x_5 = lean_array_get_size(x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_lt(x_6, x_5);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_5);
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
return x_11;
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_3, 0);
x_13 = lean_array_get_size(x_12);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_lt(x_14, x_13);
if (x_15 == 0)
{
uint8_t x_16; 
lean_dec(x_13);
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
lean_inc(x_2);
lean_inc(x_1);
x_5 = l_Lean_PersistentArray_anyMAux___at_Lean_Meta_getFVarSetToGeneralize___spec__54(x_1, x_2, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_array_get_size(x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_lt(x_8, x_7);
if (x_9 == 0)
{
uint8_t x_10; 
lean_dec(x_7);
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
return x_13;
}
}
else
{
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
lean_dec(x_13);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = l_Lean_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__53(x_1, x_2, x_22);
lean_dec(x_22);
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
lean_dec(x_13);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = l_Lean_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__53(x_1, x_2, x_29);
lean_dec(x_29);
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
lean_dec(x_12);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at_Lean_Meta_getFVarSetToGeneralize___spec__2___at_Lean_Meta_getFVarSetToGeneralize___spec__10___closed__1;
x_23 = l_Lean_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__53(x_22, x_1, x_21);
lean_dec(x_21);
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
lean_dec(x_12);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at_Lean_Meta_getFVarSetToGeneralize___spec__2___at_Lean_Meta_getFVarSetToGeneralize___spec__10___closed__1;
x_31 = l_Lean_PersistentArray_anyM___at_Lean_Meta_getFVarSetToGeneralize___spec__53(x_30, x_1, x_29);
lean_dec(x_29);
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
lean_dec(x_5);
lean_dec(x_3);
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
lean_inc(x_19);
lean_inc(x_3);
x_21 = l_Lean_PersistentArray_forInAux___at_Lean_Meta_getFVarSetToGeneralize___spec__62(x_1, x_2, x_3, x_4, x_17, x_19, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_17);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
lean_dec(x_5);
lean_dec(x_3);
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
lean_inc(x_34);
lean_inc(x_3);
x_35 = l_Lean_PersistentArray_forInAux___at_Lean_Meta_getFVarSetToGeneralize___spec__62(x_1, x_2, x_3, x_4, x_17, x_34, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_17);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_5);
lean_dec(x_3);
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
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; lean_object* x_66; lean_object* x_71; lean_object* x_305; 
x_48 = lean_ctor_get(x_16, 0);
lean_inc(x_48);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 x_49 = x_16;
} else {
 lean_dec_ref(x_16);
 x_49 = lean_box(0);
}
x_50 = lean_ctor_get(x_25, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_25, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_52 = x_25;
} else {
 lean_dec_ref(x_25);
 x_52 = lean_box(0);
}
x_53 = l_Lean_LocalDecl_fvarId(x_48);
x_305 = l_Lean_RBNode_findCore___at_Lean_Meta_mkGeneralizationForbiddenSet_visit___spec__1(x_1, x_53);
if (lean_obj_tag(x_305) == 0)
{
uint8_t x_306; 
x_306 = l_Lean_LocalDecl_isAuxDecl(x_48);
if (x_306 == 0)
{
uint8_t x_307; uint8_t x_308; 
x_307 = l_Lean_LocalDecl_binderInfo(x_48);
x_308 = l_Lean_BinderInfo_isInstImplicit(x_307);
if (x_308 == 0)
{
if (x_2 == 0)
{
lean_object* x_309; 
x_309 = lean_box(0);
x_71 = x_309;
goto block_304;
}
else
{
uint8_t x_310; 
x_310 = l_Lean_LocalDecl_isLet(x_48);
if (x_310 == 0)
{
lean_object* x_311; 
x_311 = lean_box(0);
x_71 = x_311;
goto block_304;
}
else
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; 
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_49);
lean_dec(x_48);
x_312 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_312, 0, x_50);
lean_ctor_set(x_312, 1, x_51);
x_313 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_313, 0, x_312);
x_314 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_314, 0, x_313);
lean_ctor_set(x_314, 1, x_13);
x_27 = x_314;
goto block_43;
}
}
}
else
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; 
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_49);
lean_dec(x_48);
x_315 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_315, 0, x_50);
lean_ctor_set(x_315, 1, x_51);
x_316 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_316, 0, x_315);
x_317 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_317, 0, x_316);
lean_ctor_set(x_317, 1, x_13);
x_27 = x_317;
goto block_43;
}
}
else
{
lean_object* x_318; lean_object* x_319; lean_object* x_320; 
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_49);
lean_dec(x_48);
x_318 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_318, 0, x_50);
lean_ctor_set(x_318, 1, x_51);
x_319 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_319, 0, x_318);
x_320 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_320, 0, x_319);
lean_ctor_set(x_320, 1, x_13);
x_27 = x_320;
goto block_43;
}
}
else
{
uint8_t x_321; 
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_49);
lean_dec(x_48);
x_321 = !lean_is_exclusive(x_305);
if (x_321 == 0)
{
lean_object* x_322; lean_object* x_323; lean_object* x_324; 
x_322 = lean_ctor_get(x_305, 0);
lean_dec(x_322);
x_323 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_323, 0, x_50);
lean_ctor_set(x_323, 1, x_51);
lean_ctor_set(x_305, 0, x_323);
x_324 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_324, 0, x_305);
lean_ctor_set(x_324, 1, x_13);
x_27 = x_324;
goto block_43;
}
else
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; 
lean_dec(x_305);
x_325 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_325, 0, x_50);
lean_ctor_set(x_325, 1, x_51);
x_326 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_326, 0, x_325);
x_327 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_327, 0, x_326);
lean_ctor_set(x_327, 1, x_13);
x_27 = x_327;
goto block_43;
}
}
block_65:
{
if (x_54 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_53);
if (lean_is_scalar(x_52)) {
 x_56 = lean_alloc_ctor(0, 2, 0);
} else {
 x_56 = x_52;
}
lean_ctor_set(x_56, 0, x_50);
lean_ctor_set(x_56, 1, x_51);
if (lean_is_scalar(x_49)) {
 x_57 = lean_alloc_ctor(1, 1, 0);
} else {
 x_57 = x_49;
}
lean_ctor_set(x_57, 0, x_56);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_55);
x_27 = x_58;
goto block_43;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_59 = lean_box(0);
lean_inc(x_53);
x_60 = l_Lean_RBNode_insert___at_Lean_FVarIdSet_insert___spec__1(x_50, x_53, x_59);
x_61 = l_Lean_RBNode_insert___at_Lean_FVarIdSet_insert___spec__1(x_51, x_53, x_59);
if (lean_is_scalar(x_52)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_52;
}
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
if (lean_is_scalar(x_49)) {
 x_63 = lean_alloc_ctor(1, 1, 0);
} else {
 x_63 = x_49;
}
lean_ctor_set(x_63, 0, x_62);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_55);
x_27 = x_64;
goto block_43;
}
}
block_70:
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = lean_unbox(x_67);
lean_dec(x_67);
x_54 = x_69;
x_55 = x_68;
goto block_65;
}
block_304:
{
lean_dec(x_71);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_72 = lean_ctor_get(x_48, 3);
lean_inc(x_72);
lean_dec(x_48);
x_73 = lean_st_ref_get(x_10, x_13);
x_74 = !lean_is_exclusive(x_73);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
x_75 = lean_ctor_get(x_73, 0);
x_76 = lean_ctor_get(x_73, 1);
x_77 = lean_ctor_get(x_75, 0);
lean_inc(x_77);
lean_dec(x_75);
x_78 = l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__3;
lean_inc(x_77);
lean_ctor_set(x_73, 1, x_77);
lean_ctor_set(x_73, 0, x_78);
x_79 = l_Lean_Expr_hasFVar(x_72);
if (x_79 == 0)
{
uint8_t x_80; 
x_80 = l_Lean_Expr_hasMVar(x_72);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; 
lean_dec(x_73);
lean_dec(x_72);
x_81 = lean_st_ref_take(x_10, x_76);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
x_84 = !lean_is_exclusive(x_82);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_85 = lean_ctor_get(x_82, 0);
lean_dec(x_85);
lean_ctor_set(x_82, 0, x_77);
x_86 = lean_st_ref_set(x_10, x_82, x_83);
x_87 = !lean_is_exclusive(x_86);
if (x_87 == 0)
{
lean_object* x_88; uint8_t x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_86, 0);
lean_dec(x_88);
x_89 = 0;
x_90 = lean_box(x_89);
lean_ctor_set(x_86, 0, x_90);
x_66 = x_86;
goto block_70;
}
else
{
lean_object* x_91; uint8_t x_92; lean_object* x_93; lean_object* x_94; 
x_91 = lean_ctor_get(x_86, 1);
lean_inc(x_91);
lean_dec(x_86);
x_92 = 0;
x_93 = lean_box(x_92);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_91);
x_66 = x_94;
goto block_70;
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; lean_object* x_104; lean_object* x_105; 
x_95 = lean_ctor_get(x_82, 1);
x_96 = lean_ctor_get(x_82, 2);
x_97 = lean_ctor_get(x_82, 3);
x_98 = lean_ctor_get(x_82, 4);
lean_inc(x_98);
lean_inc(x_97);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_82);
x_99 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_99, 0, x_77);
lean_ctor_set(x_99, 1, x_95);
lean_ctor_set(x_99, 2, x_96);
lean_ctor_set(x_99, 3, x_97);
lean_ctor_set(x_99, 4, x_98);
x_100 = lean_st_ref_set(x_10, x_99, x_83);
x_101 = lean_ctor_get(x_100, 1);
lean_inc(x_101);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 lean_ctor_release(x_100, 1);
 x_102 = x_100;
} else {
 lean_dec_ref(x_100);
 x_102 = lean_box(0);
}
x_103 = 0;
x_104 = lean_box(x_103);
if (lean_is_scalar(x_102)) {
 x_105 = lean_alloc_ctor(0, 2, 0);
} else {
 x_105 = x_102;
}
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_101);
x_66 = x_105;
goto block_70;
}
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; 
lean_dec(x_77);
lean_inc(x_51);
x_106 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__1___at_Lean_Meta_getFVarSetToGeneralize___spec__9(x_51, x_72, x_73);
x_107 = lean_ctor_get(x_106, 1);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 0);
lean_inc(x_108);
lean_dec(x_106);
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
lean_dec(x_107);
x_110 = lean_st_ref_take(x_10, x_76);
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_110, 1);
lean_inc(x_112);
lean_dec(x_110);
x_113 = !lean_is_exclusive(x_111);
if (x_113 == 0)
{
lean_object* x_114; lean_object* x_115; uint8_t x_116; 
x_114 = lean_ctor_get(x_111, 0);
lean_dec(x_114);
lean_ctor_set(x_111, 0, x_109);
x_115 = lean_st_ref_set(x_10, x_111, x_112);
x_116 = !lean_is_exclusive(x_115);
if (x_116 == 0)
{
lean_object* x_117; 
x_117 = lean_ctor_get(x_115, 0);
lean_dec(x_117);
lean_ctor_set(x_115, 0, x_108);
x_66 = x_115;
goto block_70;
}
else
{
lean_object* x_118; lean_object* x_119; 
x_118 = lean_ctor_get(x_115, 1);
lean_inc(x_118);
lean_dec(x_115);
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_108);
lean_ctor_set(x_119, 1, x_118);
x_66 = x_119;
goto block_70;
}
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_120 = lean_ctor_get(x_111, 1);
x_121 = lean_ctor_get(x_111, 2);
x_122 = lean_ctor_get(x_111, 3);
x_123 = lean_ctor_get(x_111, 4);
lean_inc(x_123);
lean_inc(x_122);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_111);
x_124 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_124, 0, x_109);
lean_ctor_set(x_124, 1, x_120);
lean_ctor_set(x_124, 2, x_121);
lean_ctor_set(x_124, 3, x_122);
lean_ctor_set(x_124, 4, x_123);
x_125 = lean_st_ref_set(x_10, x_124, x_112);
x_126 = lean_ctor_get(x_125, 1);
lean_inc(x_126);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 lean_ctor_release(x_125, 1);
 x_127 = x_125;
} else {
 lean_dec_ref(x_125);
 x_127 = lean_box(0);
}
if (lean_is_scalar(x_127)) {
 x_128 = lean_alloc_ctor(0, 2, 0);
} else {
 x_128 = x_127;
}
lean_ctor_set(x_128, 0, x_108);
lean_ctor_set(x_128, 1, x_126);
x_66 = x_128;
goto block_70;
}
}
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; uint8_t x_136; 
lean_dec(x_77);
lean_inc(x_51);
x_129 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__12___at_Lean_Meta_getFVarSetToGeneralize___spec__20(x_51, x_72, x_73);
x_130 = lean_ctor_get(x_129, 1);
lean_inc(x_130);
x_131 = lean_ctor_get(x_129, 0);
lean_inc(x_131);
lean_dec(x_129);
x_132 = lean_ctor_get(x_130, 1);
lean_inc(x_132);
lean_dec(x_130);
x_133 = lean_st_ref_take(x_10, x_76);
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_133, 1);
lean_inc(x_135);
lean_dec(x_133);
x_136 = !lean_is_exclusive(x_134);
if (x_136 == 0)
{
lean_object* x_137; lean_object* x_138; uint8_t x_139; 
x_137 = lean_ctor_get(x_134, 0);
lean_dec(x_137);
lean_ctor_set(x_134, 0, x_132);
x_138 = lean_st_ref_set(x_10, x_134, x_135);
x_139 = !lean_is_exclusive(x_138);
if (x_139 == 0)
{
lean_object* x_140; 
x_140 = lean_ctor_get(x_138, 0);
lean_dec(x_140);
lean_ctor_set(x_138, 0, x_131);
x_66 = x_138;
goto block_70;
}
else
{
lean_object* x_141; lean_object* x_142; 
x_141 = lean_ctor_get(x_138, 1);
lean_inc(x_141);
lean_dec(x_138);
x_142 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_142, 0, x_131);
lean_ctor_set(x_142, 1, x_141);
x_66 = x_142;
goto block_70;
}
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_143 = lean_ctor_get(x_134, 1);
x_144 = lean_ctor_get(x_134, 2);
x_145 = lean_ctor_get(x_134, 3);
x_146 = lean_ctor_get(x_134, 4);
lean_inc(x_146);
lean_inc(x_145);
lean_inc(x_144);
lean_inc(x_143);
lean_dec(x_134);
x_147 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_147, 0, x_132);
lean_ctor_set(x_147, 1, x_143);
lean_ctor_set(x_147, 2, x_144);
lean_ctor_set(x_147, 3, x_145);
lean_ctor_set(x_147, 4, x_146);
x_148 = lean_st_ref_set(x_10, x_147, x_135);
x_149 = lean_ctor_get(x_148, 1);
lean_inc(x_149);
if (lean_is_exclusive(x_148)) {
 lean_ctor_release(x_148, 0);
 lean_ctor_release(x_148, 1);
 x_150 = x_148;
} else {
 lean_dec_ref(x_148);
 x_150 = lean_box(0);
}
if (lean_is_scalar(x_150)) {
 x_151 = lean_alloc_ctor(0, 2, 0);
} else {
 x_151 = x_150;
}
lean_ctor_set(x_151, 0, x_131);
lean_ctor_set(x_151, 1, x_149);
x_66 = x_151;
goto block_70;
}
}
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; uint8_t x_157; 
x_152 = lean_ctor_get(x_73, 0);
x_153 = lean_ctor_get(x_73, 1);
lean_inc(x_153);
lean_inc(x_152);
lean_dec(x_73);
x_154 = lean_ctor_get(x_152, 0);
lean_inc(x_154);
lean_dec(x_152);
x_155 = l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__3;
lean_inc(x_154);
x_156 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_156, 0, x_155);
lean_ctor_set(x_156, 1, x_154);
x_157 = l_Lean_Expr_hasFVar(x_72);
if (x_157 == 0)
{
uint8_t x_158; 
x_158 = l_Lean_Expr_hasMVar(x_72);
if (x_158 == 0)
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; uint8_t x_171; lean_object* x_172; lean_object* x_173; 
lean_dec(x_156);
lean_dec(x_72);
x_159 = lean_st_ref_take(x_10, x_153);
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_159, 1);
lean_inc(x_161);
lean_dec(x_159);
x_162 = lean_ctor_get(x_160, 1);
lean_inc(x_162);
x_163 = lean_ctor_get(x_160, 2);
lean_inc(x_163);
x_164 = lean_ctor_get(x_160, 3);
lean_inc(x_164);
x_165 = lean_ctor_get(x_160, 4);
lean_inc(x_165);
if (lean_is_exclusive(x_160)) {
 lean_ctor_release(x_160, 0);
 lean_ctor_release(x_160, 1);
 lean_ctor_release(x_160, 2);
 lean_ctor_release(x_160, 3);
 lean_ctor_release(x_160, 4);
 x_166 = x_160;
} else {
 lean_dec_ref(x_160);
 x_166 = lean_box(0);
}
if (lean_is_scalar(x_166)) {
 x_167 = lean_alloc_ctor(0, 5, 0);
} else {
 x_167 = x_166;
}
lean_ctor_set(x_167, 0, x_154);
lean_ctor_set(x_167, 1, x_162);
lean_ctor_set(x_167, 2, x_163);
lean_ctor_set(x_167, 3, x_164);
lean_ctor_set(x_167, 4, x_165);
x_168 = lean_st_ref_set(x_10, x_167, x_161);
x_169 = lean_ctor_get(x_168, 1);
lean_inc(x_169);
if (lean_is_exclusive(x_168)) {
 lean_ctor_release(x_168, 0);
 lean_ctor_release(x_168, 1);
 x_170 = x_168;
} else {
 lean_dec_ref(x_168);
 x_170 = lean_box(0);
}
x_171 = 0;
x_172 = lean_box(x_171);
if (lean_is_scalar(x_170)) {
 x_173 = lean_alloc_ctor(0, 2, 0);
} else {
 x_173 = x_170;
}
lean_ctor_set(x_173, 0, x_172);
lean_ctor_set(x_173, 1, x_169);
x_66 = x_173;
goto block_70;
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
lean_dec(x_154);
lean_inc(x_51);
x_174 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__1___at_Lean_Meta_getFVarSetToGeneralize___spec__9(x_51, x_72, x_156);
x_175 = lean_ctor_get(x_174, 1);
lean_inc(x_175);
x_176 = lean_ctor_get(x_174, 0);
lean_inc(x_176);
lean_dec(x_174);
x_177 = lean_ctor_get(x_175, 1);
lean_inc(x_177);
lean_dec(x_175);
x_178 = lean_st_ref_take(x_10, x_153);
x_179 = lean_ctor_get(x_178, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_178, 1);
lean_inc(x_180);
lean_dec(x_178);
x_181 = lean_ctor_get(x_179, 1);
lean_inc(x_181);
x_182 = lean_ctor_get(x_179, 2);
lean_inc(x_182);
x_183 = lean_ctor_get(x_179, 3);
lean_inc(x_183);
x_184 = lean_ctor_get(x_179, 4);
lean_inc(x_184);
if (lean_is_exclusive(x_179)) {
 lean_ctor_release(x_179, 0);
 lean_ctor_release(x_179, 1);
 lean_ctor_release(x_179, 2);
 lean_ctor_release(x_179, 3);
 lean_ctor_release(x_179, 4);
 x_185 = x_179;
} else {
 lean_dec_ref(x_179);
 x_185 = lean_box(0);
}
if (lean_is_scalar(x_185)) {
 x_186 = lean_alloc_ctor(0, 5, 0);
} else {
 x_186 = x_185;
}
lean_ctor_set(x_186, 0, x_177);
lean_ctor_set(x_186, 1, x_181);
lean_ctor_set(x_186, 2, x_182);
lean_ctor_set(x_186, 3, x_183);
lean_ctor_set(x_186, 4, x_184);
x_187 = lean_st_ref_set(x_10, x_186, x_180);
x_188 = lean_ctor_get(x_187, 1);
lean_inc(x_188);
if (lean_is_exclusive(x_187)) {
 lean_ctor_release(x_187, 0);
 lean_ctor_release(x_187, 1);
 x_189 = x_187;
} else {
 lean_dec_ref(x_187);
 x_189 = lean_box(0);
}
if (lean_is_scalar(x_189)) {
 x_190 = lean_alloc_ctor(0, 2, 0);
} else {
 x_190 = x_189;
}
lean_ctor_set(x_190, 0, x_176);
lean_ctor_set(x_190, 1, x_188);
x_66 = x_190;
goto block_70;
}
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; 
lean_dec(x_154);
lean_inc(x_51);
x_191 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__12___at_Lean_Meta_getFVarSetToGeneralize___spec__20(x_51, x_72, x_156);
x_192 = lean_ctor_get(x_191, 1);
lean_inc(x_192);
x_193 = lean_ctor_get(x_191, 0);
lean_inc(x_193);
lean_dec(x_191);
x_194 = lean_ctor_get(x_192, 1);
lean_inc(x_194);
lean_dec(x_192);
x_195 = lean_st_ref_take(x_10, x_153);
x_196 = lean_ctor_get(x_195, 0);
lean_inc(x_196);
x_197 = lean_ctor_get(x_195, 1);
lean_inc(x_197);
lean_dec(x_195);
x_198 = lean_ctor_get(x_196, 1);
lean_inc(x_198);
x_199 = lean_ctor_get(x_196, 2);
lean_inc(x_199);
x_200 = lean_ctor_get(x_196, 3);
lean_inc(x_200);
x_201 = lean_ctor_get(x_196, 4);
lean_inc(x_201);
if (lean_is_exclusive(x_196)) {
 lean_ctor_release(x_196, 0);
 lean_ctor_release(x_196, 1);
 lean_ctor_release(x_196, 2);
 lean_ctor_release(x_196, 3);
 lean_ctor_release(x_196, 4);
 x_202 = x_196;
} else {
 lean_dec_ref(x_196);
 x_202 = lean_box(0);
}
if (lean_is_scalar(x_202)) {
 x_203 = lean_alloc_ctor(0, 5, 0);
} else {
 x_203 = x_202;
}
lean_ctor_set(x_203, 0, x_194);
lean_ctor_set(x_203, 1, x_198);
lean_ctor_set(x_203, 2, x_199);
lean_ctor_set(x_203, 3, x_200);
lean_ctor_set(x_203, 4, x_201);
x_204 = lean_st_ref_set(x_10, x_203, x_197);
x_205 = lean_ctor_get(x_204, 1);
lean_inc(x_205);
if (lean_is_exclusive(x_204)) {
 lean_ctor_release(x_204, 0);
 lean_ctor_release(x_204, 1);
 x_206 = x_204;
} else {
 lean_dec_ref(x_204);
 x_206 = lean_box(0);
}
if (lean_is_scalar(x_206)) {
 x_207 = lean_alloc_ctor(0, 2, 0);
} else {
 x_207 = x_206;
}
lean_ctor_set(x_207, 0, x_193);
lean_ctor_set(x_207, 1, x_205);
x_66 = x_207;
goto block_70;
}
}
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; uint8_t x_211; 
x_208 = lean_ctor_get(x_48, 3);
lean_inc(x_208);
x_209 = lean_ctor_get(x_48, 4);
lean_inc(x_209);
lean_dec(x_48);
x_210 = lean_st_ref_get(x_10, x_13);
x_211 = !lean_is_exclusive(x_210);
if (x_211 == 0)
{
lean_object* x_212; lean_object* x_213; uint8_t x_214; lean_object* x_215; uint8_t x_232; lean_object* x_233; lean_object* x_246; lean_object* x_247; uint8_t x_248; 
x_212 = lean_ctor_get(x_210, 0);
x_213 = lean_ctor_get(x_210, 1);
x_246 = lean_ctor_get(x_212, 0);
lean_inc(x_246);
lean_dec(x_212);
x_247 = l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__3;
lean_ctor_set(x_210, 1, x_246);
lean_ctor_set(x_210, 0, x_247);
x_248 = l_Lean_Expr_hasFVar(x_208);
if (x_248 == 0)
{
uint8_t x_249; 
x_249 = l_Lean_Expr_hasMVar(x_208);
if (x_249 == 0)
{
uint8_t x_250; 
lean_dec(x_208);
x_250 = 0;
x_232 = x_250;
x_233 = x_210;
goto block_245;
}
else
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; uint8_t x_254; 
lean_inc(x_51);
x_251 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__39___at_Lean_Meta_getFVarSetToGeneralize___spec__47(x_51, x_208, x_210);
x_252 = lean_ctor_get(x_251, 0);
lean_inc(x_252);
x_253 = lean_ctor_get(x_251, 1);
lean_inc(x_253);
lean_dec(x_251);
x_254 = lean_unbox(x_252);
lean_dec(x_252);
x_232 = x_254;
x_233 = x_253;
goto block_245;
}
}
else
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; uint8_t x_258; 
lean_inc(x_51);
x_255 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__50___at_Lean_Meta_getFVarSetToGeneralize___spec__58(x_51, x_208, x_210);
x_256 = lean_ctor_get(x_255, 0);
lean_inc(x_256);
x_257 = lean_ctor_get(x_255, 1);
lean_inc(x_257);
lean_dec(x_255);
x_258 = lean_unbox(x_256);
lean_dec(x_256);
x_232 = x_258;
x_233 = x_257;
goto block_245;
}
block_231:
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; uint8_t x_220; 
x_216 = lean_ctor_get(x_215, 1);
lean_inc(x_216);
lean_dec(x_215);
x_217 = lean_st_ref_take(x_10, x_213);
x_218 = lean_ctor_get(x_217, 0);
lean_inc(x_218);
x_219 = lean_ctor_get(x_217, 1);
lean_inc(x_219);
lean_dec(x_217);
x_220 = !lean_is_exclusive(x_218);
if (x_220 == 0)
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; 
x_221 = lean_ctor_get(x_218, 0);
lean_dec(x_221);
lean_ctor_set(x_218, 0, x_216);
x_222 = lean_st_ref_set(x_10, x_218, x_219);
x_223 = lean_ctor_get(x_222, 1);
lean_inc(x_223);
lean_dec(x_222);
x_54 = x_214;
x_55 = x_223;
goto block_65;
}
else
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; 
x_224 = lean_ctor_get(x_218, 1);
x_225 = lean_ctor_get(x_218, 2);
x_226 = lean_ctor_get(x_218, 3);
x_227 = lean_ctor_get(x_218, 4);
lean_inc(x_227);
lean_inc(x_226);
lean_inc(x_225);
lean_inc(x_224);
lean_dec(x_218);
x_228 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_228, 0, x_216);
lean_ctor_set(x_228, 1, x_224);
lean_ctor_set(x_228, 2, x_225);
lean_ctor_set(x_228, 3, x_226);
lean_ctor_set(x_228, 4, x_227);
x_229 = lean_st_ref_set(x_10, x_228, x_219);
x_230 = lean_ctor_get(x_229, 1);
lean_inc(x_230);
lean_dec(x_229);
x_54 = x_214;
x_55 = x_230;
goto block_65;
}
}
block_245:
{
if (x_232 == 0)
{
uint8_t x_234; 
x_234 = l_Lean_Expr_hasFVar(x_209);
if (x_234 == 0)
{
uint8_t x_235; 
x_235 = l_Lean_Expr_hasMVar(x_209);
if (x_235 == 0)
{
uint8_t x_236; 
lean_dec(x_209);
x_236 = 0;
x_214 = x_236;
x_215 = x_233;
goto block_231;
}
else
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; uint8_t x_240; 
lean_inc(x_51);
lean_inc(x_3);
x_237 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__23(x_3, x_51, x_209, x_233);
x_238 = lean_ctor_get(x_237, 0);
lean_inc(x_238);
x_239 = lean_ctor_get(x_237, 1);
lean_inc(x_239);
lean_dec(x_237);
x_240 = lean_unbox(x_238);
lean_dec(x_238);
x_214 = x_240;
x_215 = x_239;
goto block_231;
}
}
else
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; uint8_t x_244; 
lean_inc(x_51);
lean_inc(x_3);
x_241 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__31(x_3, x_51, x_209, x_233);
x_242 = lean_ctor_get(x_241, 0);
lean_inc(x_242);
x_243 = lean_ctor_get(x_241, 1);
lean_inc(x_243);
lean_dec(x_241);
x_244 = lean_unbox(x_242);
lean_dec(x_242);
x_214 = x_244;
x_215 = x_243;
goto block_231;
}
}
else
{
lean_dec(x_209);
x_214 = x_232;
x_215 = x_233;
goto block_231;
}
}
}
else
{
lean_object* x_259; lean_object* x_260; uint8_t x_261; lean_object* x_262; uint8_t x_276; lean_object* x_277; lean_object* x_290; lean_object* x_291; lean_object* x_292; uint8_t x_293; 
x_259 = lean_ctor_get(x_210, 0);
x_260 = lean_ctor_get(x_210, 1);
lean_inc(x_260);
lean_inc(x_259);
lean_dec(x_210);
x_290 = lean_ctor_get(x_259, 0);
lean_inc(x_290);
lean_dec(x_259);
x_291 = l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__3;
x_292 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_292, 0, x_291);
lean_ctor_set(x_292, 1, x_290);
x_293 = l_Lean_Expr_hasFVar(x_208);
if (x_293 == 0)
{
uint8_t x_294; 
x_294 = l_Lean_Expr_hasMVar(x_208);
if (x_294 == 0)
{
uint8_t x_295; 
lean_dec(x_208);
x_295 = 0;
x_276 = x_295;
x_277 = x_292;
goto block_289;
}
else
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; uint8_t x_299; 
lean_inc(x_51);
x_296 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__39___at_Lean_Meta_getFVarSetToGeneralize___spec__47(x_51, x_208, x_292);
x_297 = lean_ctor_get(x_296, 0);
lean_inc(x_297);
x_298 = lean_ctor_get(x_296, 1);
lean_inc(x_298);
lean_dec(x_296);
x_299 = lean_unbox(x_297);
lean_dec(x_297);
x_276 = x_299;
x_277 = x_298;
goto block_289;
}
}
else
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; uint8_t x_303; 
lean_inc(x_51);
x_300 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__50___at_Lean_Meta_getFVarSetToGeneralize___spec__58(x_51, x_208, x_292);
x_301 = lean_ctor_get(x_300, 0);
lean_inc(x_301);
x_302 = lean_ctor_get(x_300, 1);
lean_inc(x_302);
lean_dec(x_300);
x_303 = lean_unbox(x_301);
lean_dec(x_301);
x_276 = x_303;
x_277 = x_302;
goto block_289;
}
block_275:
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; 
x_263 = lean_ctor_get(x_262, 1);
lean_inc(x_263);
lean_dec(x_262);
x_264 = lean_st_ref_take(x_10, x_260);
x_265 = lean_ctor_get(x_264, 0);
lean_inc(x_265);
x_266 = lean_ctor_get(x_264, 1);
lean_inc(x_266);
lean_dec(x_264);
x_267 = lean_ctor_get(x_265, 1);
lean_inc(x_267);
x_268 = lean_ctor_get(x_265, 2);
lean_inc(x_268);
x_269 = lean_ctor_get(x_265, 3);
lean_inc(x_269);
x_270 = lean_ctor_get(x_265, 4);
lean_inc(x_270);
if (lean_is_exclusive(x_265)) {
 lean_ctor_release(x_265, 0);
 lean_ctor_release(x_265, 1);
 lean_ctor_release(x_265, 2);
 lean_ctor_release(x_265, 3);
 lean_ctor_release(x_265, 4);
 x_271 = x_265;
} else {
 lean_dec_ref(x_265);
 x_271 = lean_box(0);
}
if (lean_is_scalar(x_271)) {
 x_272 = lean_alloc_ctor(0, 5, 0);
} else {
 x_272 = x_271;
}
lean_ctor_set(x_272, 0, x_263);
lean_ctor_set(x_272, 1, x_267);
lean_ctor_set(x_272, 2, x_268);
lean_ctor_set(x_272, 3, x_269);
lean_ctor_set(x_272, 4, x_270);
x_273 = lean_st_ref_set(x_10, x_272, x_266);
x_274 = lean_ctor_get(x_273, 1);
lean_inc(x_274);
lean_dec(x_273);
x_54 = x_261;
x_55 = x_274;
goto block_65;
}
block_289:
{
if (x_276 == 0)
{
uint8_t x_278; 
x_278 = l_Lean_Expr_hasFVar(x_209);
if (x_278 == 0)
{
uint8_t x_279; 
x_279 = l_Lean_Expr_hasMVar(x_209);
if (x_279 == 0)
{
uint8_t x_280; 
lean_dec(x_209);
x_280 = 0;
x_261 = x_280;
x_262 = x_277;
goto block_275;
}
else
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; uint8_t x_284; 
lean_inc(x_51);
lean_inc(x_3);
x_281 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__23(x_3, x_51, x_209, x_277);
x_282 = lean_ctor_get(x_281, 0);
lean_inc(x_282);
x_283 = lean_ctor_get(x_281, 1);
lean_inc(x_283);
lean_dec(x_281);
x_284 = lean_unbox(x_282);
lean_dec(x_282);
x_261 = x_284;
x_262 = x_283;
goto block_275;
}
}
else
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; uint8_t x_288; 
lean_inc(x_51);
lean_inc(x_3);
x_285 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__31(x_3, x_51, x_209, x_277);
x_286 = lean_ctor_get(x_285, 0);
lean_inc(x_286);
x_287 = lean_ctor_get(x_285, 1);
lean_inc(x_287);
lean_dec(x_285);
x_288 = lean_unbox(x_286);
lean_dec(x_286);
x_261 = x_288;
x_262 = x_287;
goto block_275;
}
}
else
{
lean_dec(x_209);
x_261 = x_276;
x_262 = x_277;
goto block_275;
}
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
lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_ctor_get(x_5, 0);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_6);
x_15 = lean_array_size(x_12);
x_16 = 0;
x_17 = l_Array_forInUnsafe_loop___at_Lean_Meta_getFVarSetToGeneralize___spec__63(x_1, x_2, x_3, x_4, x_13, x_12, x_15, x_16, x_14, x_7, x_8, x_9, x_10, x_11);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_box(0);
x_23 = l_Lean_PersistentArray_forInAux___at_Lean_Meta_getFVarSetToGeneralize___spec__62___lambda__1(x_21, x_22, x_7, x_8, x_9, x_10, x_20);
return x_23;
}
else
{
uint8_t x_24; 
lean_dec(x_18);
x_24 = !lean_is_exclusive(x_17);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_17, 0);
lean_dec(x_25);
x_26 = lean_ctor_get(x_19, 0);
lean_inc(x_26);
lean_dec(x_19);
lean_ctor_set(x_17, 0, x_26);
return x_17;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_17, 1);
lean_inc(x_27);
lean_dec(x_17);
x_28 = lean_ctor_get(x_19, 0);
lean_inc(x_28);
lean_dec(x_19);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; size_t x_33; size_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_30 = lean_ctor_get(x_5, 0);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_6);
x_33 = lean_array_size(x_30);
x_34 = 0;
x_35 = l_Array_forInUnsafe_loop___at_Lean_Meta_getFVarSetToGeneralize___spec__64(x_1, x_2, x_3, x_31, x_30, x_33, x_34, x_32, x_7, x_8, x_9, x_10, x_11);
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
x_41 = l_Lean_PersistentArray_forInAux___at_Lean_Meta_getFVarSetToGeneralize___spec__62___lambda__1(x_39, x_40, x_7, x_8, x_9, x_10, x_38);
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
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; lean_object* x_66; lean_object* x_71; lean_object* x_305; 
x_48 = lean_ctor_get(x_16, 0);
lean_inc(x_48);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 x_49 = x_16;
} else {
 lean_dec_ref(x_16);
 x_49 = lean_box(0);
}
x_50 = lean_ctor_get(x_25, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_25, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_52 = x_25;
} else {
 lean_dec_ref(x_25);
 x_52 = lean_box(0);
}
x_53 = l_Lean_LocalDecl_fvarId(x_48);
x_305 = l_Lean_RBNode_findCore___at_Lean_Meta_mkGeneralizationForbiddenSet_visit___spec__1(x_1, x_53);
if (lean_obj_tag(x_305) == 0)
{
uint8_t x_306; 
x_306 = l_Lean_LocalDecl_isAuxDecl(x_48);
if (x_306 == 0)
{
uint8_t x_307; uint8_t x_308; 
x_307 = l_Lean_LocalDecl_binderInfo(x_48);
x_308 = l_Lean_BinderInfo_isInstImplicit(x_307);
if (x_308 == 0)
{
if (x_2 == 0)
{
lean_object* x_309; 
x_309 = lean_box(0);
x_71 = x_309;
goto block_304;
}
else
{
uint8_t x_310; 
x_310 = l_Lean_LocalDecl_isLet(x_48);
if (x_310 == 0)
{
lean_object* x_311; 
x_311 = lean_box(0);
x_71 = x_311;
goto block_304;
}
else
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; 
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_49);
lean_dec(x_48);
x_312 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_312, 0, x_50);
lean_ctor_set(x_312, 1, x_51);
x_313 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_313, 0, x_312);
x_314 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_314, 0, x_313);
lean_ctor_set(x_314, 1, x_13);
x_27 = x_314;
goto block_43;
}
}
}
else
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; 
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_49);
lean_dec(x_48);
x_315 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_315, 0, x_50);
lean_ctor_set(x_315, 1, x_51);
x_316 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_316, 0, x_315);
x_317 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_317, 0, x_316);
lean_ctor_set(x_317, 1, x_13);
x_27 = x_317;
goto block_43;
}
}
else
{
lean_object* x_318; lean_object* x_319; lean_object* x_320; 
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_49);
lean_dec(x_48);
x_318 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_318, 0, x_50);
lean_ctor_set(x_318, 1, x_51);
x_319 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_319, 0, x_318);
x_320 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_320, 0, x_319);
lean_ctor_set(x_320, 1, x_13);
x_27 = x_320;
goto block_43;
}
}
else
{
uint8_t x_321; 
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_49);
lean_dec(x_48);
x_321 = !lean_is_exclusive(x_305);
if (x_321 == 0)
{
lean_object* x_322; lean_object* x_323; lean_object* x_324; 
x_322 = lean_ctor_get(x_305, 0);
lean_dec(x_322);
x_323 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_323, 0, x_50);
lean_ctor_set(x_323, 1, x_51);
lean_ctor_set(x_305, 0, x_323);
x_324 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_324, 0, x_305);
lean_ctor_set(x_324, 1, x_13);
x_27 = x_324;
goto block_43;
}
else
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; 
lean_dec(x_305);
x_325 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_325, 0, x_50);
lean_ctor_set(x_325, 1, x_51);
x_326 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_326, 0, x_325);
x_327 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_327, 0, x_326);
lean_ctor_set(x_327, 1, x_13);
x_27 = x_327;
goto block_43;
}
}
block_65:
{
if (x_54 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_53);
if (lean_is_scalar(x_52)) {
 x_56 = lean_alloc_ctor(0, 2, 0);
} else {
 x_56 = x_52;
}
lean_ctor_set(x_56, 0, x_50);
lean_ctor_set(x_56, 1, x_51);
if (lean_is_scalar(x_49)) {
 x_57 = lean_alloc_ctor(1, 1, 0);
} else {
 x_57 = x_49;
}
lean_ctor_set(x_57, 0, x_56);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_55);
x_27 = x_58;
goto block_43;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_59 = lean_box(0);
lean_inc(x_53);
x_60 = l_Lean_RBNode_insert___at_Lean_FVarIdSet_insert___spec__1(x_50, x_53, x_59);
x_61 = l_Lean_RBNode_insert___at_Lean_FVarIdSet_insert___spec__1(x_51, x_53, x_59);
if (lean_is_scalar(x_52)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_52;
}
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
if (lean_is_scalar(x_49)) {
 x_63 = lean_alloc_ctor(1, 1, 0);
} else {
 x_63 = x_49;
}
lean_ctor_set(x_63, 0, x_62);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_55);
x_27 = x_64;
goto block_43;
}
}
block_70:
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = lean_unbox(x_67);
lean_dec(x_67);
x_54 = x_69;
x_55 = x_68;
goto block_65;
}
block_304:
{
lean_dec(x_71);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_72 = lean_ctor_get(x_48, 3);
lean_inc(x_72);
lean_dec(x_48);
x_73 = lean_st_ref_get(x_10, x_13);
x_74 = !lean_is_exclusive(x_73);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
x_75 = lean_ctor_get(x_73, 0);
x_76 = lean_ctor_get(x_73, 1);
x_77 = lean_ctor_get(x_75, 0);
lean_inc(x_77);
lean_dec(x_75);
x_78 = l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__3;
lean_inc(x_77);
lean_ctor_set(x_73, 1, x_77);
lean_ctor_set(x_73, 0, x_78);
x_79 = l_Lean_Expr_hasFVar(x_72);
if (x_79 == 0)
{
uint8_t x_80; 
x_80 = l_Lean_Expr_hasMVar(x_72);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; 
lean_dec(x_73);
lean_dec(x_72);
x_81 = lean_st_ref_take(x_10, x_76);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
x_84 = !lean_is_exclusive(x_82);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_85 = lean_ctor_get(x_82, 0);
lean_dec(x_85);
lean_ctor_set(x_82, 0, x_77);
x_86 = lean_st_ref_set(x_10, x_82, x_83);
x_87 = !lean_is_exclusive(x_86);
if (x_87 == 0)
{
lean_object* x_88; uint8_t x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_86, 0);
lean_dec(x_88);
x_89 = 0;
x_90 = lean_box(x_89);
lean_ctor_set(x_86, 0, x_90);
x_66 = x_86;
goto block_70;
}
else
{
lean_object* x_91; uint8_t x_92; lean_object* x_93; lean_object* x_94; 
x_91 = lean_ctor_get(x_86, 1);
lean_inc(x_91);
lean_dec(x_86);
x_92 = 0;
x_93 = lean_box(x_92);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_91);
x_66 = x_94;
goto block_70;
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; lean_object* x_104; lean_object* x_105; 
x_95 = lean_ctor_get(x_82, 1);
x_96 = lean_ctor_get(x_82, 2);
x_97 = lean_ctor_get(x_82, 3);
x_98 = lean_ctor_get(x_82, 4);
lean_inc(x_98);
lean_inc(x_97);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_82);
x_99 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_99, 0, x_77);
lean_ctor_set(x_99, 1, x_95);
lean_ctor_set(x_99, 2, x_96);
lean_ctor_set(x_99, 3, x_97);
lean_ctor_set(x_99, 4, x_98);
x_100 = lean_st_ref_set(x_10, x_99, x_83);
x_101 = lean_ctor_get(x_100, 1);
lean_inc(x_101);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 lean_ctor_release(x_100, 1);
 x_102 = x_100;
} else {
 lean_dec_ref(x_100);
 x_102 = lean_box(0);
}
x_103 = 0;
x_104 = lean_box(x_103);
if (lean_is_scalar(x_102)) {
 x_105 = lean_alloc_ctor(0, 2, 0);
} else {
 x_105 = x_102;
}
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_101);
x_66 = x_105;
goto block_70;
}
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; 
lean_dec(x_77);
lean_inc(x_51);
x_106 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__1___at_Lean_Meta_getFVarSetToGeneralize___spec__9(x_51, x_72, x_73);
x_107 = lean_ctor_get(x_106, 1);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 0);
lean_inc(x_108);
lean_dec(x_106);
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
lean_dec(x_107);
x_110 = lean_st_ref_take(x_10, x_76);
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_110, 1);
lean_inc(x_112);
lean_dec(x_110);
x_113 = !lean_is_exclusive(x_111);
if (x_113 == 0)
{
lean_object* x_114; lean_object* x_115; uint8_t x_116; 
x_114 = lean_ctor_get(x_111, 0);
lean_dec(x_114);
lean_ctor_set(x_111, 0, x_109);
x_115 = lean_st_ref_set(x_10, x_111, x_112);
x_116 = !lean_is_exclusive(x_115);
if (x_116 == 0)
{
lean_object* x_117; 
x_117 = lean_ctor_get(x_115, 0);
lean_dec(x_117);
lean_ctor_set(x_115, 0, x_108);
x_66 = x_115;
goto block_70;
}
else
{
lean_object* x_118; lean_object* x_119; 
x_118 = lean_ctor_get(x_115, 1);
lean_inc(x_118);
lean_dec(x_115);
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_108);
lean_ctor_set(x_119, 1, x_118);
x_66 = x_119;
goto block_70;
}
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_120 = lean_ctor_get(x_111, 1);
x_121 = lean_ctor_get(x_111, 2);
x_122 = lean_ctor_get(x_111, 3);
x_123 = lean_ctor_get(x_111, 4);
lean_inc(x_123);
lean_inc(x_122);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_111);
x_124 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_124, 0, x_109);
lean_ctor_set(x_124, 1, x_120);
lean_ctor_set(x_124, 2, x_121);
lean_ctor_set(x_124, 3, x_122);
lean_ctor_set(x_124, 4, x_123);
x_125 = lean_st_ref_set(x_10, x_124, x_112);
x_126 = lean_ctor_get(x_125, 1);
lean_inc(x_126);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 lean_ctor_release(x_125, 1);
 x_127 = x_125;
} else {
 lean_dec_ref(x_125);
 x_127 = lean_box(0);
}
if (lean_is_scalar(x_127)) {
 x_128 = lean_alloc_ctor(0, 2, 0);
} else {
 x_128 = x_127;
}
lean_ctor_set(x_128, 0, x_108);
lean_ctor_set(x_128, 1, x_126);
x_66 = x_128;
goto block_70;
}
}
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; uint8_t x_136; 
lean_dec(x_77);
lean_inc(x_51);
x_129 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__12___at_Lean_Meta_getFVarSetToGeneralize___spec__20(x_51, x_72, x_73);
x_130 = lean_ctor_get(x_129, 1);
lean_inc(x_130);
x_131 = lean_ctor_get(x_129, 0);
lean_inc(x_131);
lean_dec(x_129);
x_132 = lean_ctor_get(x_130, 1);
lean_inc(x_132);
lean_dec(x_130);
x_133 = lean_st_ref_take(x_10, x_76);
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_133, 1);
lean_inc(x_135);
lean_dec(x_133);
x_136 = !lean_is_exclusive(x_134);
if (x_136 == 0)
{
lean_object* x_137; lean_object* x_138; uint8_t x_139; 
x_137 = lean_ctor_get(x_134, 0);
lean_dec(x_137);
lean_ctor_set(x_134, 0, x_132);
x_138 = lean_st_ref_set(x_10, x_134, x_135);
x_139 = !lean_is_exclusive(x_138);
if (x_139 == 0)
{
lean_object* x_140; 
x_140 = lean_ctor_get(x_138, 0);
lean_dec(x_140);
lean_ctor_set(x_138, 0, x_131);
x_66 = x_138;
goto block_70;
}
else
{
lean_object* x_141; lean_object* x_142; 
x_141 = lean_ctor_get(x_138, 1);
lean_inc(x_141);
lean_dec(x_138);
x_142 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_142, 0, x_131);
lean_ctor_set(x_142, 1, x_141);
x_66 = x_142;
goto block_70;
}
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_143 = lean_ctor_get(x_134, 1);
x_144 = lean_ctor_get(x_134, 2);
x_145 = lean_ctor_get(x_134, 3);
x_146 = lean_ctor_get(x_134, 4);
lean_inc(x_146);
lean_inc(x_145);
lean_inc(x_144);
lean_inc(x_143);
lean_dec(x_134);
x_147 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_147, 0, x_132);
lean_ctor_set(x_147, 1, x_143);
lean_ctor_set(x_147, 2, x_144);
lean_ctor_set(x_147, 3, x_145);
lean_ctor_set(x_147, 4, x_146);
x_148 = lean_st_ref_set(x_10, x_147, x_135);
x_149 = lean_ctor_get(x_148, 1);
lean_inc(x_149);
if (lean_is_exclusive(x_148)) {
 lean_ctor_release(x_148, 0);
 lean_ctor_release(x_148, 1);
 x_150 = x_148;
} else {
 lean_dec_ref(x_148);
 x_150 = lean_box(0);
}
if (lean_is_scalar(x_150)) {
 x_151 = lean_alloc_ctor(0, 2, 0);
} else {
 x_151 = x_150;
}
lean_ctor_set(x_151, 0, x_131);
lean_ctor_set(x_151, 1, x_149);
x_66 = x_151;
goto block_70;
}
}
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; uint8_t x_157; 
x_152 = lean_ctor_get(x_73, 0);
x_153 = lean_ctor_get(x_73, 1);
lean_inc(x_153);
lean_inc(x_152);
lean_dec(x_73);
x_154 = lean_ctor_get(x_152, 0);
lean_inc(x_154);
lean_dec(x_152);
x_155 = l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__3;
lean_inc(x_154);
x_156 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_156, 0, x_155);
lean_ctor_set(x_156, 1, x_154);
x_157 = l_Lean_Expr_hasFVar(x_72);
if (x_157 == 0)
{
uint8_t x_158; 
x_158 = l_Lean_Expr_hasMVar(x_72);
if (x_158 == 0)
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; uint8_t x_171; lean_object* x_172; lean_object* x_173; 
lean_dec(x_156);
lean_dec(x_72);
x_159 = lean_st_ref_take(x_10, x_153);
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_159, 1);
lean_inc(x_161);
lean_dec(x_159);
x_162 = lean_ctor_get(x_160, 1);
lean_inc(x_162);
x_163 = lean_ctor_get(x_160, 2);
lean_inc(x_163);
x_164 = lean_ctor_get(x_160, 3);
lean_inc(x_164);
x_165 = lean_ctor_get(x_160, 4);
lean_inc(x_165);
if (lean_is_exclusive(x_160)) {
 lean_ctor_release(x_160, 0);
 lean_ctor_release(x_160, 1);
 lean_ctor_release(x_160, 2);
 lean_ctor_release(x_160, 3);
 lean_ctor_release(x_160, 4);
 x_166 = x_160;
} else {
 lean_dec_ref(x_160);
 x_166 = lean_box(0);
}
if (lean_is_scalar(x_166)) {
 x_167 = lean_alloc_ctor(0, 5, 0);
} else {
 x_167 = x_166;
}
lean_ctor_set(x_167, 0, x_154);
lean_ctor_set(x_167, 1, x_162);
lean_ctor_set(x_167, 2, x_163);
lean_ctor_set(x_167, 3, x_164);
lean_ctor_set(x_167, 4, x_165);
x_168 = lean_st_ref_set(x_10, x_167, x_161);
x_169 = lean_ctor_get(x_168, 1);
lean_inc(x_169);
if (lean_is_exclusive(x_168)) {
 lean_ctor_release(x_168, 0);
 lean_ctor_release(x_168, 1);
 x_170 = x_168;
} else {
 lean_dec_ref(x_168);
 x_170 = lean_box(0);
}
x_171 = 0;
x_172 = lean_box(x_171);
if (lean_is_scalar(x_170)) {
 x_173 = lean_alloc_ctor(0, 2, 0);
} else {
 x_173 = x_170;
}
lean_ctor_set(x_173, 0, x_172);
lean_ctor_set(x_173, 1, x_169);
x_66 = x_173;
goto block_70;
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
lean_dec(x_154);
lean_inc(x_51);
x_174 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__1___at_Lean_Meta_getFVarSetToGeneralize___spec__9(x_51, x_72, x_156);
x_175 = lean_ctor_get(x_174, 1);
lean_inc(x_175);
x_176 = lean_ctor_get(x_174, 0);
lean_inc(x_176);
lean_dec(x_174);
x_177 = lean_ctor_get(x_175, 1);
lean_inc(x_177);
lean_dec(x_175);
x_178 = lean_st_ref_take(x_10, x_153);
x_179 = lean_ctor_get(x_178, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_178, 1);
lean_inc(x_180);
lean_dec(x_178);
x_181 = lean_ctor_get(x_179, 1);
lean_inc(x_181);
x_182 = lean_ctor_get(x_179, 2);
lean_inc(x_182);
x_183 = lean_ctor_get(x_179, 3);
lean_inc(x_183);
x_184 = lean_ctor_get(x_179, 4);
lean_inc(x_184);
if (lean_is_exclusive(x_179)) {
 lean_ctor_release(x_179, 0);
 lean_ctor_release(x_179, 1);
 lean_ctor_release(x_179, 2);
 lean_ctor_release(x_179, 3);
 lean_ctor_release(x_179, 4);
 x_185 = x_179;
} else {
 lean_dec_ref(x_179);
 x_185 = lean_box(0);
}
if (lean_is_scalar(x_185)) {
 x_186 = lean_alloc_ctor(0, 5, 0);
} else {
 x_186 = x_185;
}
lean_ctor_set(x_186, 0, x_177);
lean_ctor_set(x_186, 1, x_181);
lean_ctor_set(x_186, 2, x_182);
lean_ctor_set(x_186, 3, x_183);
lean_ctor_set(x_186, 4, x_184);
x_187 = lean_st_ref_set(x_10, x_186, x_180);
x_188 = lean_ctor_get(x_187, 1);
lean_inc(x_188);
if (lean_is_exclusive(x_187)) {
 lean_ctor_release(x_187, 0);
 lean_ctor_release(x_187, 1);
 x_189 = x_187;
} else {
 lean_dec_ref(x_187);
 x_189 = lean_box(0);
}
if (lean_is_scalar(x_189)) {
 x_190 = lean_alloc_ctor(0, 2, 0);
} else {
 x_190 = x_189;
}
lean_ctor_set(x_190, 0, x_176);
lean_ctor_set(x_190, 1, x_188);
x_66 = x_190;
goto block_70;
}
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; 
lean_dec(x_154);
lean_inc(x_51);
x_191 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__12___at_Lean_Meta_getFVarSetToGeneralize___spec__20(x_51, x_72, x_156);
x_192 = lean_ctor_get(x_191, 1);
lean_inc(x_192);
x_193 = lean_ctor_get(x_191, 0);
lean_inc(x_193);
lean_dec(x_191);
x_194 = lean_ctor_get(x_192, 1);
lean_inc(x_194);
lean_dec(x_192);
x_195 = lean_st_ref_take(x_10, x_153);
x_196 = lean_ctor_get(x_195, 0);
lean_inc(x_196);
x_197 = lean_ctor_get(x_195, 1);
lean_inc(x_197);
lean_dec(x_195);
x_198 = lean_ctor_get(x_196, 1);
lean_inc(x_198);
x_199 = lean_ctor_get(x_196, 2);
lean_inc(x_199);
x_200 = lean_ctor_get(x_196, 3);
lean_inc(x_200);
x_201 = lean_ctor_get(x_196, 4);
lean_inc(x_201);
if (lean_is_exclusive(x_196)) {
 lean_ctor_release(x_196, 0);
 lean_ctor_release(x_196, 1);
 lean_ctor_release(x_196, 2);
 lean_ctor_release(x_196, 3);
 lean_ctor_release(x_196, 4);
 x_202 = x_196;
} else {
 lean_dec_ref(x_196);
 x_202 = lean_box(0);
}
if (lean_is_scalar(x_202)) {
 x_203 = lean_alloc_ctor(0, 5, 0);
} else {
 x_203 = x_202;
}
lean_ctor_set(x_203, 0, x_194);
lean_ctor_set(x_203, 1, x_198);
lean_ctor_set(x_203, 2, x_199);
lean_ctor_set(x_203, 3, x_200);
lean_ctor_set(x_203, 4, x_201);
x_204 = lean_st_ref_set(x_10, x_203, x_197);
x_205 = lean_ctor_get(x_204, 1);
lean_inc(x_205);
if (lean_is_exclusive(x_204)) {
 lean_ctor_release(x_204, 0);
 lean_ctor_release(x_204, 1);
 x_206 = x_204;
} else {
 lean_dec_ref(x_204);
 x_206 = lean_box(0);
}
if (lean_is_scalar(x_206)) {
 x_207 = lean_alloc_ctor(0, 2, 0);
} else {
 x_207 = x_206;
}
lean_ctor_set(x_207, 0, x_193);
lean_ctor_set(x_207, 1, x_205);
x_66 = x_207;
goto block_70;
}
}
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; uint8_t x_211; 
x_208 = lean_ctor_get(x_48, 3);
lean_inc(x_208);
x_209 = lean_ctor_get(x_48, 4);
lean_inc(x_209);
lean_dec(x_48);
x_210 = lean_st_ref_get(x_10, x_13);
x_211 = !lean_is_exclusive(x_210);
if (x_211 == 0)
{
lean_object* x_212; lean_object* x_213; uint8_t x_214; lean_object* x_215; uint8_t x_232; lean_object* x_233; lean_object* x_246; lean_object* x_247; uint8_t x_248; 
x_212 = lean_ctor_get(x_210, 0);
x_213 = lean_ctor_get(x_210, 1);
x_246 = lean_ctor_get(x_212, 0);
lean_inc(x_246);
lean_dec(x_212);
x_247 = l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__3;
lean_ctor_set(x_210, 1, x_246);
lean_ctor_set(x_210, 0, x_247);
x_248 = l_Lean_Expr_hasFVar(x_208);
if (x_248 == 0)
{
uint8_t x_249; 
x_249 = l_Lean_Expr_hasMVar(x_208);
if (x_249 == 0)
{
uint8_t x_250; 
lean_dec(x_208);
x_250 = 0;
x_232 = x_250;
x_233 = x_210;
goto block_245;
}
else
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; uint8_t x_254; 
lean_inc(x_51);
x_251 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__39___at_Lean_Meta_getFVarSetToGeneralize___spec__47(x_51, x_208, x_210);
x_252 = lean_ctor_get(x_251, 0);
lean_inc(x_252);
x_253 = lean_ctor_get(x_251, 1);
lean_inc(x_253);
lean_dec(x_251);
x_254 = lean_unbox(x_252);
lean_dec(x_252);
x_232 = x_254;
x_233 = x_253;
goto block_245;
}
}
else
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; uint8_t x_258; 
lean_inc(x_51);
x_255 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__50___at_Lean_Meta_getFVarSetToGeneralize___spec__58(x_51, x_208, x_210);
x_256 = lean_ctor_get(x_255, 0);
lean_inc(x_256);
x_257 = lean_ctor_get(x_255, 1);
lean_inc(x_257);
lean_dec(x_255);
x_258 = lean_unbox(x_256);
lean_dec(x_256);
x_232 = x_258;
x_233 = x_257;
goto block_245;
}
block_231:
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; uint8_t x_220; 
x_216 = lean_ctor_get(x_215, 1);
lean_inc(x_216);
lean_dec(x_215);
x_217 = lean_st_ref_take(x_10, x_213);
x_218 = lean_ctor_get(x_217, 0);
lean_inc(x_218);
x_219 = lean_ctor_get(x_217, 1);
lean_inc(x_219);
lean_dec(x_217);
x_220 = !lean_is_exclusive(x_218);
if (x_220 == 0)
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; 
x_221 = lean_ctor_get(x_218, 0);
lean_dec(x_221);
lean_ctor_set(x_218, 0, x_216);
x_222 = lean_st_ref_set(x_10, x_218, x_219);
x_223 = lean_ctor_get(x_222, 1);
lean_inc(x_223);
lean_dec(x_222);
x_54 = x_214;
x_55 = x_223;
goto block_65;
}
else
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; 
x_224 = lean_ctor_get(x_218, 1);
x_225 = lean_ctor_get(x_218, 2);
x_226 = lean_ctor_get(x_218, 3);
x_227 = lean_ctor_get(x_218, 4);
lean_inc(x_227);
lean_inc(x_226);
lean_inc(x_225);
lean_inc(x_224);
lean_dec(x_218);
x_228 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_228, 0, x_216);
lean_ctor_set(x_228, 1, x_224);
lean_ctor_set(x_228, 2, x_225);
lean_ctor_set(x_228, 3, x_226);
lean_ctor_set(x_228, 4, x_227);
x_229 = lean_st_ref_set(x_10, x_228, x_219);
x_230 = lean_ctor_get(x_229, 1);
lean_inc(x_230);
lean_dec(x_229);
x_54 = x_214;
x_55 = x_230;
goto block_65;
}
}
block_245:
{
if (x_232 == 0)
{
uint8_t x_234; 
x_234 = l_Lean_Expr_hasFVar(x_209);
if (x_234 == 0)
{
uint8_t x_235; 
x_235 = l_Lean_Expr_hasMVar(x_209);
if (x_235 == 0)
{
uint8_t x_236; 
lean_dec(x_209);
x_236 = 0;
x_214 = x_236;
x_215 = x_233;
goto block_231;
}
else
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; uint8_t x_240; 
lean_inc(x_51);
lean_inc(x_3);
x_237 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__23(x_3, x_51, x_209, x_233);
x_238 = lean_ctor_get(x_237, 0);
lean_inc(x_238);
x_239 = lean_ctor_get(x_237, 1);
lean_inc(x_239);
lean_dec(x_237);
x_240 = lean_unbox(x_238);
lean_dec(x_238);
x_214 = x_240;
x_215 = x_239;
goto block_231;
}
}
else
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; uint8_t x_244; 
lean_inc(x_51);
lean_inc(x_3);
x_241 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__31(x_3, x_51, x_209, x_233);
x_242 = lean_ctor_get(x_241, 0);
lean_inc(x_242);
x_243 = lean_ctor_get(x_241, 1);
lean_inc(x_243);
lean_dec(x_241);
x_244 = lean_unbox(x_242);
lean_dec(x_242);
x_214 = x_244;
x_215 = x_243;
goto block_231;
}
}
else
{
lean_dec(x_209);
x_214 = x_232;
x_215 = x_233;
goto block_231;
}
}
}
else
{
lean_object* x_259; lean_object* x_260; uint8_t x_261; lean_object* x_262; uint8_t x_276; lean_object* x_277; lean_object* x_290; lean_object* x_291; lean_object* x_292; uint8_t x_293; 
x_259 = lean_ctor_get(x_210, 0);
x_260 = lean_ctor_get(x_210, 1);
lean_inc(x_260);
lean_inc(x_259);
lean_dec(x_210);
x_290 = lean_ctor_get(x_259, 0);
lean_inc(x_290);
lean_dec(x_259);
x_291 = l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__3;
x_292 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_292, 0, x_291);
lean_ctor_set(x_292, 1, x_290);
x_293 = l_Lean_Expr_hasFVar(x_208);
if (x_293 == 0)
{
uint8_t x_294; 
x_294 = l_Lean_Expr_hasMVar(x_208);
if (x_294 == 0)
{
uint8_t x_295; 
lean_dec(x_208);
x_295 = 0;
x_276 = x_295;
x_277 = x_292;
goto block_289;
}
else
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; uint8_t x_299; 
lean_inc(x_51);
x_296 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__39___at_Lean_Meta_getFVarSetToGeneralize___spec__47(x_51, x_208, x_292);
x_297 = lean_ctor_get(x_296, 0);
lean_inc(x_297);
x_298 = lean_ctor_get(x_296, 1);
lean_inc(x_298);
lean_dec(x_296);
x_299 = lean_unbox(x_297);
lean_dec(x_297);
x_276 = x_299;
x_277 = x_298;
goto block_289;
}
}
else
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; uint8_t x_303; 
lean_inc(x_51);
x_300 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__50___at_Lean_Meta_getFVarSetToGeneralize___spec__58(x_51, x_208, x_292);
x_301 = lean_ctor_get(x_300, 0);
lean_inc(x_301);
x_302 = lean_ctor_get(x_300, 1);
lean_inc(x_302);
lean_dec(x_300);
x_303 = lean_unbox(x_301);
lean_dec(x_301);
x_276 = x_303;
x_277 = x_302;
goto block_289;
}
block_275:
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; 
x_263 = lean_ctor_get(x_262, 1);
lean_inc(x_263);
lean_dec(x_262);
x_264 = lean_st_ref_take(x_10, x_260);
x_265 = lean_ctor_get(x_264, 0);
lean_inc(x_265);
x_266 = lean_ctor_get(x_264, 1);
lean_inc(x_266);
lean_dec(x_264);
x_267 = lean_ctor_get(x_265, 1);
lean_inc(x_267);
x_268 = lean_ctor_get(x_265, 2);
lean_inc(x_268);
x_269 = lean_ctor_get(x_265, 3);
lean_inc(x_269);
x_270 = lean_ctor_get(x_265, 4);
lean_inc(x_270);
if (lean_is_exclusive(x_265)) {
 lean_ctor_release(x_265, 0);
 lean_ctor_release(x_265, 1);
 lean_ctor_release(x_265, 2);
 lean_ctor_release(x_265, 3);
 lean_ctor_release(x_265, 4);
 x_271 = x_265;
} else {
 lean_dec_ref(x_265);
 x_271 = lean_box(0);
}
if (lean_is_scalar(x_271)) {
 x_272 = lean_alloc_ctor(0, 5, 0);
} else {
 x_272 = x_271;
}
lean_ctor_set(x_272, 0, x_263);
lean_ctor_set(x_272, 1, x_267);
lean_ctor_set(x_272, 2, x_268);
lean_ctor_set(x_272, 3, x_269);
lean_ctor_set(x_272, 4, x_270);
x_273 = lean_st_ref_set(x_10, x_272, x_266);
x_274 = lean_ctor_get(x_273, 1);
lean_inc(x_274);
lean_dec(x_273);
x_54 = x_261;
x_55 = x_274;
goto block_65;
}
block_289:
{
if (x_276 == 0)
{
uint8_t x_278; 
x_278 = l_Lean_Expr_hasFVar(x_209);
if (x_278 == 0)
{
uint8_t x_279; 
x_279 = l_Lean_Expr_hasMVar(x_209);
if (x_279 == 0)
{
uint8_t x_280; 
lean_dec(x_209);
x_280 = 0;
x_261 = x_280;
x_262 = x_277;
goto block_275;
}
else
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; uint8_t x_284; 
lean_inc(x_51);
lean_inc(x_3);
x_281 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__23(x_3, x_51, x_209, x_277);
x_282 = lean_ctor_get(x_281, 0);
lean_inc(x_282);
x_283 = lean_ctor_get(x_281, 1);
lean_inc(x_283);
lean_dec(x_281);
x_284 = lean_unbox(x_282);
lean_dec(x_282);
x_261 = x_284;
x_262 = x_283;
goto block_275;
}
}
else
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; uint8_t x_288; 
lean_inc(x_51);
lean_inc(x_3);
x_285 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__31(x_3, x_51, x_209, x_277);
x_286 = lean_ctor_get(x_285, 0);
lean_inc(x_286);
x_287 = lean_ctor_get(x_285, 1);
lean_inc(x_287);
lean_dec(x_285);
x_288 = lean_unbox(x_286);
lean_dec(x_286);
x_261 = x_288;
x_262 = x_287;
goto block_275;
}
}
else
{
lean_dec(x_209);
x_261 = x_276;
x_262 = x_277;
goto block_275;
}
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
lean_inc(x_5);
lean_inc(x_3);
x_12 = l_Lean_PersistentArray_forInAux___at_Lean_Meta_getFVarSetToGeneralize___spec__62(x_1, x_2, x_3, x_5, x_11, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
lean_dec(x_3);
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
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; size_t x_25; size_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
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
x_25 = lean_array_size(x_22);
x_26 = 0;
x_27 = l_Array_forInUnsafe_loop___at_Lean_Meta_getFVarSetToGeneralize___spec__65(x_1, x_2, x_3, x_23, x_22, x_25, x_26, x_24, x_6, x_7, x_8, x_9, x_20);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_27);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_27, 0);
lean_dec(x_31);
x_32 = lean_ctor_get(x_28, 1);
lean_inc(x_32);
lean_dec(x_28);
lean_ctor_set(x_27, 0, x_32);
return x_27;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_27, 1);
lean_inc(x_33);
lean_dec(x_27);
x_34 = lean_ctor_get(x_28, 1);
lean_inc(x_34);
lean_dec(x_28);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
return x_35;
}
}
else
{
uint8_t x_36; 
lean_dec(x_28);
x_36 = !lean_is_exclusive(x_27);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_27, 0);
lean_dec(x_37);
x_38 = lean_ctor_get(x_29, 0);
lean_inc(x_38);
lean_dec(x_29);
lean_ctor_set(x_27, 0, x_38);
return x_27;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_27, 1);
lean_inc(x_39);
lean_dec(x_27);
x_40 = lean_ctor_get(x_29, 0);
lean_inc(x_40);
lean_dec(x_29);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
return x_41;
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
lean_dec(x_5);
lean_dec(x_3);
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
lean_inc(x_19);
lean_inc(x_3);
x_21 = l_Lean_PersistentArray_forInAux___at_Lean_Meta_getFVarSetToGeneralize___spec__67(x_1, x_2, x_3, x_4, x_17, x_19, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_17);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
lean_dec(x_5);
lean_dec(x_3);
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
lean_inc(x_34);
lean_inc(x_3);
x_35 = l_Lean_PersistentArray_forInAux___at_Lean_Meta_getFVarSetToGeneralize___spec__67(x_1, x_2, x_3, x_4, x_17, x_34, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_17);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_5);
lean_dec(x_3);
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
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; lean_object* x_66; lean_object* x_71; lean_object* x_305; 
x_48 = lean_ctor_get(x_16, 0);
lean_inc(x_48);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 x_49 = x_16;
} else {
 lean_dec_ref(x_16);
 x_49 = lean_box(0);
}
x_50 = lean_ctor_get(x_25, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_25, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_52 = x_25;
} else {
 lean_dec_ref(x_25);
 x_52 = lean_box(0);
}
x_53 = l_Lean_LocalDecl_fvarId(x_48);
x_305 = l_Lean_RBNode_findCore___at_Lean_Meta_mkGeneralizationForbiddenSet_visit___spec__1(x_1, x_53);
if (lean_obj_tag(x_305) == 0)
{
uint8_t x_306; 
x_306 = l_Lean_LocalDecl_isAuxDecl(x_48);
if (x_306 == 0)
{
uint8_t x_307; uint8_t x_308; 
x_307 = l_Lean_LocalDecl_binderInfo(x_48);
x_308 = l_Lean_BinderInfo_isInstImplicit(x_307);
if (x_308 == 0)
{
if (x_2 == 0)
{
lean_object* x_309; 
x_309 = lean_box(0);
x_71 = x_309;
goto block_304;
}
else
{
uint8_t x_310; 
x_310 = l_Lean_LocalDecl_isLet(x_48);
if (x_310 == 0)
{
lean_object* x_311; 
x_311 = lean_box(0);
x_71 = x_311;
goto block_304;
}
else
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; 
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_49);
lean_dec(x_48);
x_312 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_312, 0, x_50);
lean_ctor_set(x_312, 1, x_51);
x_313 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_313, 0, x_312);
x_314 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_314, 0, x_313);
lean_ctor_set(x_314, 1, x_13);
x_27 = x_314;
goto block_43;
}
}
}
else
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; 
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_49);
lean_dec(x_48);
x_315 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_315, 0, x_50);
lean_ctor_set(x_315, 1, x_51);
x_316 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_316, 0, x_315);
x_317 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_317, 0, x_316);
lean_ctor_set(x_317, 1, x_13);
x_27 = x_317;
goto block_43;
}
}
else
{
lean_object* x_318; lean_object* x_319; lean_object* x_320; 
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_49);
lean_dec(x_48);
x_318 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_318, 0, x_50);
lean_ctor_set(x_318, 1, x_51);
x_319 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_319, 0, x_318);
x_320 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_320, 0, x_319);
lean_ctor_set(x_320, 1, x_13);
x_27 = x_320;
goto block_43;
}
}
else
{
uint8_t x_321; 
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_49);
lean_dec(x_48);
x_321 = !lean_is_exclusive(x_305);
if (x_321 == 0)
{
lean_object* x_322; lean_object* x_323; lean_object* x_324; 
x_322 = lean_ctor_get(x_305, 0);
lean_dec(x_322);
x_323 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_323, 0, x_50);
lean_ctor_set(x_323, 1, x_51);
lean_ctor_set(x_305, 0, x_323);
x_324 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_324, 0, x_305);
lean_ctor_set(x_324, 1, x_13);
x_27 = x_324;
goto block_43;
}
else
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; 
lean_dec(x_305);
x_325 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_325, 0, x_50);
lean_ctor_set(x_325, 1, x_51);
x_326 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_326, 0, x_325);
x_327 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_327, 0, x_326);
lean_ctor_set(x_327, 1, x_13);
x_27 = x_327;
goto block_43;
}
}
block_65:
{
if (x_54 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_53);
if (lean_is_scalar(x_52)) {
 x_56 = lean_alloc_ctor(0, 2, 0);
} else {
 x_56 = x_52;
}
lean_ctor_set(x_56, 0, x_50);
lean_ctor_set(x_56, 1, x_51);
if (lean_is_scalar(x_49)) {
 x_57 = lean_alloc_ctor(1, 1, 0);
} else {
 x_57 = x_49;
}
lean_ctor_set(x_57, 0, x_56);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_55);
x_27 = x_58;
goto block_43;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_59 = lean_box(0);
lean_inc(x_53);
x_60 = l_Lean_RBNode_insert___at_Lean_FVarIdSet_insert___spec__1(x_50, x_53, x_59);
x_61 = l_Lean_RBNode_insert___at_Lean_FVarIdSet_insert___spec__1(x_51, x_53, x_59);
if (lean_is_scalar(x_52)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_52;
}
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
if (lean_is_scalar(x_49)) {
 x_63 = lean_alloc_ctor(1, 1, 0);
} else {
 x_63 = x_49;
}
lean_ctor_set(x_63, 0, x_62);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_55);
x_27 = x_64;
goto block_43;
}
}
block_70:
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = lean_unbox(x_67);
lean_dec(x_67);
x_54 = x_69;
x_55 = x_68;
goto block_65;
}
block_304:
{
lean_dec(x_71);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_72 = lean_ctor_get(x_48, 3);
lean_inc(x_72);
lean_dec(x_48);
x_73 = lean_st_ref_get(x_10, x_13);
x_74 = !lean_is_exclusive(x_73);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
x_75 = lean_ctor_get(x_73, 0);
x_76 = lean_ctor_get(x_73, 1);
x_77 = lean_ctor_get(x_75, 0);
lean_inc(x_77);
lean_dec(x_75);
x_78 = l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__3;
lean_inc(x_77);
lean_ctor_set(x_73, 1, x_77);
lean_ctor_set(x_73, 0, x_78);
x_79 = l_Lean_Expr_hasFVar(x_72);
if (x_79 == 0)
{
uint8_t x_80; 
x_80 = l_Lean_Expr_hasMVar(x_72);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; 
lean_dec(x_73);
lean_dec(x_72);
x_81 = lean_st_ref_take(x_10, x_76);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
x_84 = !lean_is_exclusive(x_82);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_85 = lean_ctor_get(x_82, 0);
lean_dec(x_85);
lean_ctor_set(x_82, 0, x_77);
x_86 = lean_st_ref_set(x_10, x_82, x_83);
x_87 = !lean_is_exclusive(x_86);
if (x_87 == 0)
{
lean_object* x_88; uint8_t x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_86, 0);
lean_dec(x_88);
x_89 = 0;
x_90 = lean_box(x_89);
lean_ctor_set(x_86, 0, x_90);
x_66 = x_86;
goto block_70;
}
else
{
lean_object* x_91; uint8_t x_92; lean_object* x_93; lean_object* x_94; 
x_91 = lean_ctor_get(x_86, 1);
lean_inc(x_91);
lean_dec(x_86);
x_92 = 0;
x_93 = lean_box(x_92);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_91);
x_66 = x_94;
goto block_70;
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; lean_object* x_104; lean_object* x_105; 
x_95 = lean_ctor_get(x_82, 1);
x_96 = lean_ctor_get(x_82, 2);
x_97 = lean_ctor_get(x_82, 3);
x_98 = lean_ctor_get(x_82, 4);
lean_inc(x_98);
lean_inc(x_97);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_82);
x_99 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_99, 0, x_77);
lean_ctor_set(x_99, 1, x_95);
lean_ctor_set(x_99, 2, x_96);
lean_ctor_set(x_99, 3, x_97);
lean_ctor_set(x_99, 4, x_98);
x_100 = lean_st_ref_set(x_10, x_99, x_83);
x_101 = lean_ctor_get(x_100, 1);
lean_inc(x_101);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 lean_ctor_release(x_100, 1);
 x_102 = x_100;
} else {
 lean_dec_ref(x_100);
 x_102 = lean_box(0);
}
x_103 = 0;
x_104 = lean_box(x_103);
if (lean_is_scalar(x_102)) {
 x_105 = lean_alloc_ctor(0, 2, 0);
} else {
 x_105 = x_102;
}
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_101);
x_66 = x_105;
goto block_70;
}
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; 
lean_dec(x_77);
lean_inc(x_51);
x_106 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__1___at_Lean_Meta_getFVarSetToGeneralize___spec__9(x_51, x_72, x_73);
x_107 = lean_ctor_get(x_106, 1);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 0);
lean_inc(x_108);
lean_dec(x_106);
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
lean_dec(x_107);
x_110 = lean_st_ref_take(x_10, x_76);
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_110, 1);
lean_inc(x_112);
lean_dec(x_110);
x_113 = !lean_is_exclusive(x_111);
if (x_113 == 0)
{
lean_object* x_114; lean_object* x_115; uint8_t x_116; 
x_114 = lean_ctor_get(x_111, 0);
lean_dec(x_114);
lean_ctor_set(x_111, 0, x_109);
x_115 = lean_st_ref_set(x_10, x_111, x_112);
x_116 = !lean_is_exclusive(x_115);
if (x_116 == 0)
{
lean_object* x_117; 
x_117 = lean_ctor_get(x_115, 0);
lean_dec(x_117);
lean_ctor_set(x_115, 0, x_108);
x_66 = x_115;
goto block_70;
}
else
{
lean_object* x_118; lean_object* x_119; 
x_118 = lean_ctor_get(x_115, 1);
lean_inc(x_118);
lean_dec(x_115);
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_108);
lean_ctor_set(x_119, 1, x_118);
x_66 = x_119;
goto block_70;
}
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_120 = lean_ctor_get(x_111, 1);
x_121 = lean_ctor_get(x_111, 2);
x_122 = lean_ctor_get(x_111, 3);
x_123 = lean_ctor_get(x_111, 4);
lean_inc(x_123);
lean_inc(x_122);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_111);
x_124 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_124, 0, x_109);
lean_ctor_set(x_124, 1, x_120);
lean_ctor_set(x_124, 2, x_121);
lean_ctor_set(x_124, 3, x_122);
lean_ctor_set(x_124, 4, x_123);
x_125 = lean_st_ref_set(x_10, x_124, x_112);
x_126 = lean_ctor_get(x_125, 1);
lean_inc(x_126);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 lean_ctor_release(x_125, 1);
 x_127 = x_125;
} else {
 lean_dec_ref(x_125);
 x_127 = lean_box(0);
}
if (lean_is_scalar(x_127)) {
 x_128 = lean_alloc_ctor(0, 2, 0);
} else {
 x_128 = x_127;
}
lean_ctor_set(x_128, 0, x_108);
lean_ctor_set(x_128, 1, x_126);
x_66 = x_128;
goto block_70;
}
}
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; uint8_t x_136; 
lean_dec(x_77);
lean_inc(x_51);
x_129 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__12___at_Lean_Meta_getFVarSetToGeneralize___spec__20(x_51, x_72, x_73);
x_130 = lean_ctor_get(x_129, 1);
lean_inc(x_130);
x_131 = lean_ctor_get(x_129, 0);
lean_inc(x_131);
lean_dec(x_129);
x_132 = lean_ctor_get(x_130, 1);
lean_inc(x_132);
lean_dec(x_130);
x_133 = lean_st_ref_take(x_10, x_76);
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_133, 1);
lean_inc(x_135);
lean_dec(x_133);
x_136 = !lean_is_exclusive(x_134);
if (x_136 == 0)
{
lean_object* x_137; lean_object* x_138; uint8_t x_139; 
x_137 = lean_ctor_get(x_134, 0);
lean_dec(x_137);
lean_ctor_set(x_134, 0, x_132);
x_138 = lean_st_ref_set(x_10, x_134, x_135);
x_139 = !lean_is_exclusive(x_138);
if (x_139 == 0)
{
lean_object* x_140; 
x_140 = lean_ctor_get(x_138, 0);
lean_dec(x_140);
lean_ctor_set(x_138, 0, x_131);
x_66 = x_138;
goto block_70;
}
else
{
lean_object* x_141; lean_object* x_142; 
x_141 = lean_ctor_get(x_138, 1);
lean_inc(x_141);
lean_dec(x_138);
x_142 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_142, 0, x_131);
lean_ctor_set(x_142, 1, x_141);
x_66 = x_142;
goto block_70;
}
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_143 = lean_ctor_get(x_134, 1);
x_144 = lean_ctor_get(x_134, 2);
x_145 = lean_ctor_get(x_134, 3);
x_146 = lean_ctor_get(x_134, 4);
lean_inc(x_146);
lean_inc(x_145);
lean_inc(x_144);
lean_inc(x_143);
lean_dec(x_134);
x_147 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_147, 0, x_132);
lean_ctor_set(x_147, 1, x_143);
lean_ctor_set(x_147, 2, x_144);
lean_ctor_set(x_147, 3, x_145);
lean_ctor_set(x_147, 4, x_146);
x_148 = lean_st_ref_set(x_10, x_147, x_135);
x_149 = lean_ctor_get(x_148, 1);
lean_inc(x_149);
if (lean_is_exclusive(x_148)) {
 lean_ctor_release(x_148, 0);
 lean_ctor_release(x_148, 1);
 x_150 = x_148;
} else {
 lean_dec_ref(x_148);
 x_150 = lean_box(0);
}
if (lean_is_scalar(x_150)) {
 x_151 = lean_alloc_ctor(0, 2, 0);
} else {
 x_151 = x_150;
}
lean_ctor_set(x_151, 0, x_131);
lean_ctor_set(x_151, 1, x_149);
x_66 = x_151;
goto block_70;
}
}
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; uint8_t x_157; 
x_152 = lean_ctor_get(x_73, 0);
x_153 = lean_ctor_get(x_73, 1);
lean_inc(x_153);
lean_inc(x_152);
lean_dec(x_73);
x_154 = lean_ctor_get(x_152, 0);
lean_inc(x_154);
lean_dec(x_152);
x_155 = l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__3;
lean_inc(x_154);
x_156 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_156, 0, x_155);
lean_ctor_set(x_156, 1, x_154);
x_157 = l_Lean_Expr_hasFVar(x_72);
if (x_157 == 0)
{
uint8_t x_158; 
x_158 = l_Lean_Expr_hasMVar(x_72);
if (x_158 == 0)
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; uint8_t x_171; lean_object* x_172; lean_object* x_173; 
lean_dec(x_156);
lean_dec(x_72);
x_159 = lean_st_ref_take(x_10, x_153);
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_159, 1);
lean_inc(x_161);
lean_dec(x_159);
x_162 = lean_ctor_get(x_160, 1);
lean_inc(x_162);
x_163 = lean_ctor_get(x_160, 2);
lean_inc(x_163);
x_164 = lean_ctor_get(x_160, 3);
lean_inc(x_164);
x_165 = lean_ctor_get(x_160, 4);
lean_inc(x_165);
if (lean_is_exclusive(x_160)) {
 lean_ctor_release(x_160, 0);
 lean_ctor_release(x_160, 1);
 lean_ctor_release(x_160, 2);
 lean_ctor_release(x_160, 3);
 lean_ctor_release(x_160, 4);
 x_166 = x_160;
} else {
 lean_dec_ref(x_160);
 x_166 = lean_box(0);
}
if (lean_is_scalar(x_166)) {
 x_167 = lean_alloc_ctor(0, 5, 0);
} else {
 x_167 = x_166;
}
lean_ctor_set(x_167, 0, x_154);
lean_ctor_set(x_167, 1, x_162);
lean_ctor_set(x_167, 2, x_163);
lean_ctor_set(x_167, 3, x_164);
lean_ctor_set(x_167, 4, x_165);
x_168 = lean_st_ref_set(x_10, x_167, x_161);
x_169 = lean_ctor_get(x_168, 1);
lean_inc(x_169);
if (lean_is_exclusive(x_168)) {
 lean_ctor_release(x_168, 0);
 lean_ctor_release(x_168, 1);
 x_170 = x_168;
} else {
 lean_dec_ref(x_168);
 x_170 = lean_box(0);
}
x_171 = 0;
x_172 = lean_box(x_171);
if (lean_is_scalar(x_170)) {
 x_173 = lean_alloc_ctor(0, 2, 0);
} else {
 x_173 = x_170;
}
lean_ctor_set(x_173, 0, x_172);
lean_ctor_set(x_173, 1, x_169);
x_66 = x_173;
goto block_70;
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
lean_dec(x_154);
lean_inc(x_51);
x_174 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__1___at_Lean_Meta_getFVarSetToGeneralize___spec__9(x_51, x_72, x_156);
x_175 = lean_ctor_get(x_174, 1);
lean_inc(x_175);
x_176 = lean_ctor_get(x_174, 0);
lean_inc(x_176);
lean_dec(x_174);
x_177 = lean_ctor_get(x_175, 1);
lean_inc(x_177);
lean_dec(x_175);
x_178 = lean_st_ref_take(x_10, x_153);
x_179 = lean_ctor_get(x_178, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_178, 1);
lean_inc(x_180);
lean_dec(x_178);
x_181 = lean_ctor_get(x_179, 1);
lean_inc(x_181);
x_182 = lean_ctor_get(x_179, 2);
lean_inc(x_182);
x_183 = lean_ctor_get(x_179, 3);
lean_inc(x_183);
x_184 = lean_ctor_get(x_179, 4);
lean_inc(x_184);
if (lean_is_exclusive(x_179)) {
 lean_ctor_release(x_179, 0);
 lean_ctor_release(x_179, 1);
 lean_ctor_release(x_179, 2);
 lean_ctor_release(x_179, 3);
 lean_ctor_release(x_179, 4);
 x_185 = x_179;
} else {
 lean_dec_ref(x_179);
 x_185 = lean_box(0);
}
if (lean_is_scalar(x_185)) {
 x_186 = lean_alloc_ctor(0, 5, 0);
} else {
 x_186 = x_185;
}
lean_ctor_set(x_186, 0, x_177);
lean_ctor_set(x_186, 1, x_181);
lean_ctor_set(x_186, 2, x_182);
lean_ctor_set(x_186, 3, x_183);
lean_ctor_set(x_186, 4, x_184);
x_187 = lean_st_ref_set(x_10, x_186, x_180);
x_188 = lean_ctor_get(x_187, 1);
lean_inc(x_188);
if (lean_is_exclusive(x_187)) {
 lean_ctor_release(x_187, 0);
 lean_ctor_release(x_187, 1);
 x_189 = x_187;
} else {
 lean_dec_ref(x_187);
 x_189 = lean_box(0);
}
if (lean_is_scalar(x_189)) {
 x_190 = lean_alloc_ctor(0, 2, 0);
} else {
 x_190 = x_189;
}
lean_ctor_set(x_190, 0, x_176);
lean_ctor_set(x_190, 1, x_188);
x_66 = x_190;
goto block_70;
}
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; 
lean_dec(x_154);
lean_inc(x_51);
x_191 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__12___at_Lean_Meta_getFVarSetToGeneralize___spec__20(x_51, x_72, x_156);
x_192 = lean_ctor_get(x_191, 1);
lean_inc(x_192);
x_193 = lean_ctor_get(x_191, 0);
lean_inc(x_193);
lean_dec(x_191);
x_194 = lean_ctor_get(x_192, 1);
lean_inc(x_194);
lean_dec(x_192);
x_195 = lean_st_ref_take(x_10, x_153);
x_196 = lean_ctor_get(x_195, 0);
lean_inc(x_196);
x_197 = lean_ctor_get(x_195, 1);
lean_inc(x_197);
lean_dec(x_195);
x_198 = lean_ctor_get(x_196, 1);
lean_inc(x_198);
x_199 = lean_ctor_get(x_196, 2);
lean_inc(x_199);
x_200 = lean_ctor_get(x_196, 3);
lean_inc(x_200);
x_201 = lean_ctor_get(x_196, 4);
lean_inc(x_201);
if (lean_is_exclusive(x_196)) {
 lean_ctor_release(x_196, 0);
 lean_ctor_release(x_196, 1);
 lean_ctor_release(x_196, 2);
 lean_ctor_release(x_196, 3);
 lean_ctor_release(x_196, 4);
 x_202 = x_196;
} else {
 lean_dec_ref(x_196);
 x_202 = lean_box(0);
}
if (lean_is_scalar(x_202)) {
 x_203 = lean_alloc_ctor(0, 5, 0);
} else {
 x_203 = x_202;
}
lean_ctor_set(x_203, 0, x_194);
lean_ctor_set(x_203, 1, x_198);
lean_ctor_set(x_203, 2, x_199);
lean_ctor_set(x_203, 3, x_200);
lean_ctor_set(x_203, 4, x_201);
x_204 = lean_st_ref_set(x_10, x_203, x_197);
x_205 = lean_ctor_get(x_204, 1);
lean_inc(x_205);
if (lean_is_exclusive(x_204)) {
 lean_ctor_release(x_204, 0);
 lean_ctor_release(x_204, 1);
 x_206 = x_204;
} else {
 lean_dec_ref(x_204);
 x_206 = lean_box(0);
}
if (lean_is_scalar(x_206)) {
 x_207 = lean_alloc_ctor(0, 2, 0);
} else {
 x_207 = x_206;
}
lean_ctor_set(x_207, 0, x_193);
lean_ctor_set(x_207, 1, x_205);
x_66 = x_207;
goto block_70;
}
}
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; uint8_t x_211; 
x_208 = lean_ctor_get(x_48, 3);
lean_inc(x_208);
x_209 = lean_ctor_get(x_48, 4);
lean_inc(x_209);
lean_dec(x_48);
x_210 = lean_st_ref_get(x_10, x_13);
x_211 = !lean_is_exclusive(x_210);
if (x_211 == 0)
{
lean_object* x_212; lean_object* x_213; uint8_t x_214; lean_object* x_215; uint8_t x_232; lean_object* x_233; lean_object* x_246; lean_object* x_247; uint8_t x_248; 
x_212 = lean_ctor_get(x_210, 0);
x_213 = lean_ctor_get(x_210, 1);
x_246 = lean_ctor_get(x_212, 0);
lean_inc(x_246);
lean_dec(x_212);
x_247 = l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__3;
lean_ctor_set(x_210, 1, x_246);
lean_ctor_set(x_210, 0, x_247);
x_248 = l_Lean_Expr_hasFVar(x_208);
if (x_248 == 0)
{
uint8_t x_249; 
x_249 = l_Lean_Expr_hasMVar(x_208);
if (x_249 == 0)
{
uint8_t x_250; 
lean_dec(x_208);
x_250 = 0;
x_232 = x_250;
x_233 = x_210;
goto block_245;
}
else
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; uint8_t x_254; 
lean_inc(x_51);
x_251 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__39___at_Lean_Meta_getFVarSetToGeneralize___spec__47(x_51, x_208, x_210);
x_252 = lean_ctor_get(x_251, 0);
lean_inc(x_252);
x_253 = lean_ctor_get(x_251, 1);
lean_inc(x_253);
lean_dec(x_251);
x_254 = lean_unbox(x_252);
lean_dec(x_252);
x_232 = x_254;
x_233 = x_253;
goto block_245;
}
}
else
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; uint8_t x_258; 
lean_inc(x_51);
x_255 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__50___at_Lean_Meta_getFVarSetToGeneralize___spec__58(x_51, x_208, x_210);
x_256 = lean_ctor_get(x_255, 0);
lean_inc(x_256);
x_257 = lean_ctor_get(x_255, 1);
lean_inc(x_257);
lean_dec(x_255);
x_258 = lean_unbox(x_256);
lean_dec(x_256);
x_232 = x_258;
x_233 = x_257;
goto block_245;
}
block_231:
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; uint8_t x_220; 
x_216 = lean_ctor_get(x_215, 1);
lean_inc(x_216);
lean_dec(x_215);
x_217 = lean_st_ref_take(x_10, x_213);
x_218 = lean_ctor_get(x_217, 0);
lean_inc(x_218);
x_219 = lean_ctor_get(x_217, 1);
lean_inc(x_219);
lean_dec(x_217);
x_220 = !lean_is_exclusive(x_218);
if (x_220 == 0)
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; 
x_221 = lean_ctor_get(x_218, 0);
lean_dec(x_221);
lean_ctor_set(x_218, 0, x_216);
x_222 = lean_st_ref_set(x_10, x_218, x_219);
x_223 = lean_ctor_get(x_222, 1);
lean_inc(x_223);
lean_dec(x_222);
x_54 = x_214;
x_55 = x_223;
goto block_65;
}
else
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; 
x_224 = lean_ctor_get(x_218, 1);
x_225 = lean_ctor_get(x_218, 2);
x_226 = lean_ctor_get(x_218, 3);
x_227 = lean_ctor_get(x_218, 4);
lean_inc(x_227);
lean_inc(x_226);
lean_inc(x_225);
lean_inc(x_224);
lean_dec(x_218);
x_228 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_228, 0, x_216);
lean_ctor_set(x_228, 1, x_224);
lean_ctor_set(x_228, 2, x_225);
lean_ctor_set(x_228, 3, x_226);
lean_ctor_set(x_228, 4, x_227);
x_229 = lean_st_ref_set(x_10, x_228, x_219);
x_230 = lean_ctor_get(x_229, 1);
lean_inc(x_230);
lean_dec(x_229);
x_54 = x_214;
x_55 = x_230;
goto block_65;
}
}
block_245:
{
if (x_232 == 0)
{
uint8_t x_234; 
x_234 = l_Lean_Expr_hasFVar(x_209);
if (x_234 == 0)
{
uint8_t x_235; 
x_235 = l_Lean_Expr_hasMVar(x_209);
if (x_235 == 0)
{
uint8_t x_236; 
lean_dec(x_209);
x_236 = 0;
x_214 = x_236;
x_215 = x_233;
goto block_231;
}
else
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; uint8_t x_240; 
lean_inc(x_51);
lean_inc(x_3);
x_237 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__23(x_3, x_51, x_209, x_233);
x_238 = lean_ctor_get(x_237, 0);
lean_inc(x_238);
x_239 = lean_ctor_get(x_237, 1);
lean_inc(x_239);
lean_dec(x_237);
x_240 = lean_unbox(x_238);
lean_dec(x_238);
x_214 = x_240;
x_215 = x_239;
goto block_231;
}
}
else
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; uint8_t x_244; 
lean_inc(x_51);
lean_inc(x_3);
x_241 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__31(x_3, x_51, x_209, x_233);
x_242 = lean_ctor_get(x_241, 0);
lean_inc(x_242);
x_243 = lean_ctor_get(x_241, 1);
lean_inc(x_243);
lean_dec(x_241);
x_244 = lean_unbox(x_242);
lean_dec(x_242);
x_214 = x_244;
x_215 = x_243;
goto block_231;
}
}
else
{
lean_dec(x_209);
x_214 = x_232;
x_215 = x_233;
goto block_231;
}
}
}
else
{
lean_object* x_259; lean_object* x_260; uint8_t x_261; lean_object* x_262; uint8_t x_276; lean_object* x_277; lean_object* x_290; lean_object* x_291; lean_object* x_292; uint8_t x_293; 
x_259 = lean_ctor_get(x_210, 0);
x_260 = lean_ctor_get(x_210, 1);
lean_inc(x_260);
lean_inc(x_259);
lean_dec(x_210);
x_290 = lean_ctor_get(x_259, 0);
lean_inc(x_290);
lean_dec(x_259);
x_291 = l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__3;
x_292 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_292, 0, x_291);
lean_ctor_set(x_292, 1, x_290);
x_293 = l_Lean_Expr_hasFVar(x_208);
if (x_293 == 0)
{
uint8_t x_294; 
x_294 = l_Lean_Expr_hasMVar(x_208);
if (x_294 == 0)
{
uint8_t x_295; 
lean_dec(x_208);
x_295 = 0;
x_276 = x_295;
x_277 = x_292;
goto block_289;
}
else
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; uint8_t x_299; 
lean_inc(x_51);
x_296 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__39___at_Lean_Meta_getFVarSetToGeneralize___spec__47(x_51, x_208, x_292);
x_297 = lean_ctor_get(x_296, 0);
lean_inc(x_297);
x_298 = lean_ctor_get(x_296, 1);
lean_inc(x_298);
lean_dec(x_296);
x_299 = lean_unbox(x_297);
lean_dec(x_297);
x_276 = x_299;
x_277 = x_298;
goto block_289;
}
}
else
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; uint8_t x_303; 
lean_inc(x_51);
x_300 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__50___at_Lean_Meta_getFVarSetToGeneralize___spec__58(x_51, x_208, x_292);
x_301 = lean_ctor_get(x_300, 0);
lean_inc(x_301);
x_302 = lean_ctor_get(x_300, 1);
lean_inc(x_302);
lean_dec(x_300);
x_303 = lean_unbox(x_301);
lean_dec(x_301);
x_276 = x_303;
x_277 = x_302;
goto block_289;
}
block_275:
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; 
x_263 = lean_ctor_get(x_262, 1);
lean_inc(x_263);
lean_dec(x_262);
x_264 = lean_st_ref_take(x_10, x_260);
x_265 = lean_ctor_get(x_264, 0);
lean_inc(x_265);
x_266 = lean_ctor_get(x_264, 1);
lean_inc(x_266);
lean_dec(x_264);
x_267 = lean_ctor_get(x_265, 1);
lean_inc(x_267);
x_268 = lean_ctor_get(x_265, 2);
lean_inc(x_268);
x_269 = lean_ctor_get(x_265, 3);
lean_inc(x_269);
x_270 = lean_ctor_get(x_265, 4);
lean_inc(x_270);
if (lean_is_exclusive(x_265)) {
 lean_ctor_release(x_265, 0);
 lean_ctor_release(x_265, 1);
 lean_ctor_release(x_265, 2);
 lean_ctor_release(x_265, 3);
 lean_ctor_release(x_265, 4);
 x_271 = x_265;
} else {
 lean_dec_ref(x_265);
 x_271 = lean_box(0);
}
if (lean_is_scalar(x_271)) {
 x_272 = lean_alloc_ctor(0, 5, 0);
} else {
 x_272 = x_271;
}
lean_ctor_set(x_272, 0, x_263);
lean_ctor_set(x_272, 1, x_267);
lean_ctor_set(x_272, 2, x_268);
lean_ctor_set(x_272, 3, x_269);
lean_ctor_set(x_272, 4, x_270);
x_273 = lean_st_ref_set(x_10, x_272, x_266);
x_274 = lean_ctor_get(x_273, 1);
lean_inc(x_274);
lean_dec(x_273);
x_54 = x_261;
x_55 = x_274;
goto block_65;
}
block_289:
{
if (x_276 == 0)
{
uint8_t x_278; 
x_278 = l_Lean_Expr_hasFVar(x_209);
if (x_278 == 0)
{
uint8_t x_279; 
x_279 = l_Lean_Expr_hasMVar(x_209);
if (x_279 == 0)
{
uint8_t x_280; 
lean_dec(x_209);
x_280 = 0;
x_261 = x_280;
x_262 = x_277;
goto block_275;
}
else
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; uint8_t x_284; 
lean_inc(x_51);
lean_inc(x_3);
x_281 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__23(x_3, x_51, x_209, x_277);
x_282 = lean_ctor_get(x_281, 0);
lean_inc(x_282);
x_283 = lean_ctor_get(x_281, 1);
lean_inc(x_283);
lean_dec(x_281);
x_284 = lean_unbox(x_282);
lean_dec(x_282);
x_261 = x_284;
x_262 = x_283;
goto block_275;
}
}
else
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; uint8_t x_288; 
lean_inc(x_51);
lean_inc(x_3);
x_285 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__31(x_3, x_51, x_209, x_277);
x_286 = lean_ctor_get(x_285, 0);
lean_inc(x_286);
x_287 = lean_ctor_get(x_285, 1);
lean_inc(x_287);
lean_dec(x_285);
x_288 = lean_unbox(x_286);
lean_dec(x_286);
x_261 = x_288;
x_262 = x_287;
goto block_275;
}
}
else
{
lean_dec(x_209);
x_261 = x_276;
x_262 = x_277;
goto block_275;
}
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
lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_ctor_get(x_5, 0);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_6);
x_15 = lean_array_size(x_12);
x_16 = 0;
x_17 = l_Array_forInUnsafe_loop___at_Lean_Meta_getFVarSetToGeneralize___spec__68(x_1, x_2, x_3, x_4, x_13, x_12, x_15, x_16, x_14, x_7, x_8, x_9, x_10, x_11);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_box(0);
x_23 = l_Lean_PersistentArray_forInAux___at_Lean_Meta_getFVarSetToGeneralize___spec__62___lambda__1(x_21, x_22, x_7, x_8, x_9, x_10, x_20);
return x_23;
}
else
{
uint8_t x_24; 
lean_dec(x_18);
x_24 = !lean_is_exclusive(x_17);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_17, 0);
lean_dec(x_25);
x_26 = lean_ctor_get(x_19, 0);
lean_inc(x_26);
lean_dec(x_19);
lean_ctor_set(x_17, 0, x_26);
return x_17;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_17, 1);
lean_inc(x_27);
lean_dec(x_17);
x_28 = lean_ctor_get(x_19, 0);
lean_inc(x_28);
lean_dec(x_19);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; size_t x_33; size_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_30 = lean_ctor_get(x_5, 0);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_6);
x_33 = lean_array_size(x_30);
x_34 = 0;
x_35 = l_Array_forInUnsafe_loop___at_Lean_Meta_getFVarSetToGeneralize___spec__69(x_1, x_2, x_3, x_31, x_30, x_33, x_34, x_32, x_7, x_8, x_9, x_10, x_11);
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
x_41 = l_Lean_PersistentArray_forInAux___at_Lean_Meta_getFVarSetToGeneralize___spec__62___lambda__1(x_39, x_40, x_7, x_8, x_9, x_10, x_38);
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
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; lean_object* x_66; lean_object* x_71; lean_object* x_305; 
x_48 = lean_ctor_get(x_16, 0);
lean_inc(x_48);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 x_49 = x_16;
} else {
 lean_dec_ref(x_16);
 x_49 = lean_box(0);
}
x_50 = lean_ctor_get(x_25, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_25, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_52 = x_25;
} else {
 lean_dec_ref(x_25);
 x_52 = lean_box(0);
}
x_53 = l_Lean_LocalDecl_fvarId(x_48);
x_305 = l_Lean_RBNode_findCore___at_Lean_Meta_mkGeneralizationForbiddenSet_visit___spec__1(x_1, x_53);
if (lean_obj_tag(x_305) == 0)
{
uint8_t x_306; 
x_306 = l_Lean_LocalDecl_isAuxDecl(x_48);
if (x_306 == 0)
{
uint8_t x_307; uint8_t x_308; 
x_307 = l_Lean_LocalDecl_binderInfo(x_48);
x_308 = l_Lean_BinderInfo_isInstImplicit(x_307);
if (x_308 == 0)
{
if (x_2 == 0)
{
lean_object* x_309; 
x_309 = lean_box(0);
x_71 = x_309;
goto block_304;
}
else
{
uint8_t x_310; 
x_310 = l_Lean_LocalDecl_isLet(x_48);
if (x_310 == 0)
{
lean_object* x_311; 
x_311 = lean_box(0);
x_71 = x_311;
goto block_304;
}
else
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; 
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_49);
lean_dec(x_48);
x_312 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_312, 0, x_50);
lean_ctor_set(x_312, 1, x_51);
x_313 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_313, 0, x_312);
x_314 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_314, 0, x_313);
lean_ctor_set(x_314, 1, x_13);
x_27 = x_314;
goto block_43;
}
}
}
else
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; 
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_49);
lean_dec(x_48);
x_315 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_315, 0, x_50);
lean_ctor_set(x_315, 1, x_51);
x_316 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_316, 0, x_315);
x_317 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_317, 0, x_316);
lean_ctor_set(x_317, 1, x_13);
x_27 = x_317;
goto block_43;
}
}
else
{
lean_object* x_318; lean_object* x_319; lean_object* x_320; 
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_49);
lean_dec(x_48);
x_318 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_318, 0, x_50);
lean_ctor_set(x_318, 1, x_51);
x_319 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_319, 0, x_318);
x_320 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_320, 0, x_319);
lean_ctor_set(x_320, 1, x_13);
x_27 = x_320;
goto block_43;
}
}
else
{
uint8_t x_321; 
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_49);
lean_dec(x_48);
x_321 = !lean_is_exclusive(x_305);
if (x_321 == 0)
{
lean_object* x_322; lean_object* x_323; lean_object* x_324; 
x_322 = lean_ctor_get(x_305, 0);
lean_dec(x_322);
x_323 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_323, 0, x_50);
lean_ctor_set(x_323, 1, x_51);
lean_ctor_set(x_305, 0, x_323);
x_324 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_324, 0, x_305);
lean_ctor_set(x_324, 1, x_13);
x_27 = x_324;
goto block_43;
}
else
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; 
lean_dec(x_305);
x_325 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_325, 0, x_50);
lean_ctor_set(x_325, 1, x_51);
x_326 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_326, 0, x_325);
x_327 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_327, 0, x_326);
lean_ctor_set(x_327, 1, x_13);
x_27 = x_327;
goto block_43;
}
}
block_65:
{
if (x_54 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_53);
if (lean_is_scalar(x_52)) {
 x_56 = lean_alloc_ctor(0, 2, 0);
} else {
 x_56 = x_52;
}
lean_ctor_set(x_56, 0, x_50);
lean_ctor_set(x_56, 1, x_51);
if (lean_is_scalar(x_49)) {
 x_57 = lean_alloc_ctor(1, 1, 0);
} else {
 x_57 = x_49;
}
lean_ctor_set(x_57, 0, x_56);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_55);
x_27 = x_58;
goto block_43;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_59 = lean_box(0);
lean_inc(x_53);
x_60 = l_Lean_RBNode_insert___at_Lean_FVarIdSet_insert___spec__1(x_50, x_53, x_59);
x_61 = l_Lean_RBNode_insert___at_Lean_FVarIdSet_insert___spec__1(x_51, x_53, x_59);
if (lean_is_scalar(x_52)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_52;
}
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
if (lean_is_scalar(x_49)) {
 x_63 = lean_alloc_ctor(1, 1, 0);
} else {
 x_63 = x_49;
}
lean_ctor_set(x_63, 0, x_62);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_55);
x_27 = x_64;
goto block_43;
}
}
block_70:
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = lean_unbox(x_67);
lean_dec(x_67);
x_54 = x_69;
x_55 = x_68;
goto block_65;
}
block_304:
{
lean_dec(x_71);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_72 = lean_ctor_get(x_48, 3);
lean_inc(x_72);
lean_dec(x_48);
x_73 = lean_st_ref_get(x_10, x_13);
x_74 = !lean_is_exclusive(x_73);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
x_75 = lean_ctor_get(x_73, 0);
x_76 = lean_ctor_get(x_73, 1);
x_77 = lean_ctor_get(x_75, 0);
lean_inc(x_77);
lean_dec(x_75);
x_78 = l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__3;
lean_inc(x_77);
lean_ctor_set(x_73, 1, x_77);
lean_ctor_set(x_73, 0, x_78);
x_79 = l_Lean_Expr_hasFVar(x_72);
if (x_79 == 0)
{
uint8_t x_80; 
x_80 = l_Lean_Expr_hasMVar(x_72);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; 
lean_dec(x_73);
lean_dec(x_72);
x_81 = lean_st_ref_take(x_10, x_76);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
x_84 = !lean_is_exclusive(x_82);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_85 = lean_ctor_get(x_82, 0);
lean_dec(x_85);
lean_ctor_set(x_82, 0, x_77);
x_86 = lean_st_ref_set(x_10, x_82, x_83);
x_87 = !lean_is_exclusive(x_86);
if (x_87 == 0)
{
lean_object* x_88; uint8_t x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_86, 0);
lean_dec(x_88);
x_89 = 0;
x_90 = lean_box(x_89);
lean_ctor_set(x_86, 0, x_90);
x_66 = x_86;
goto block_70;
}
else
{
lean_object* x_91; uint8_t x_92; lean_object* x_93; lean_object* x_94; 
x_91 = lean_ctor_get(x_86, 1);
lean_inc(x_91);
lean_dec(x_86);
x_92 = 0;
x_93 = lean_box(x_92);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_91);
x_66 = x_94;
goto block_70;
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; lean_object* x_104; lean_object* x_105; 
x_95 = lean_ctor_get(x_82, 1);
x_96 = lean_ctor_get(x_82, 2);
x_97 = lean_ctor_get(x_82, 3);
x_98 = lean_ctor_get(x_82, 4);
lean_inc(x_98);
lean_inc(x_97);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_82);
x_99 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_99, 0, x_77);
lean_ctor_set(x_99, 1, x_95);
lean_ctor_set(x_99, 2, x_96);
lean_ctor_set(x_99, 3, x_97);
lean_ctor_set(x_99, 4, x_98);
x_100 = lean_st_ref_set(x_10, x_99, x_83);
x_101 = lean_ctor_get(x_100, 1);
lean_inc(x_101);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 lean_ctor_release(x_100, 1);
 x_102 = x_100;
} else {
 lean_dec_ref(x_100);
 x_102 = lean_box(0);
}
x_103 = 0;
x_104 = lean_box(x_103);
if (lean_is_scalar(x_102)) {
 x_105 = lean_alloc_ctor(0, 2, 0);
} else {
 x_105 = x_102;
}
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_101);
x_66 = x_105;
goto block_70;
}
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; 
lean_dec(x_77);
lean_inc(x_51);
x_106 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__1___at_Lean_Meta_getFVarSetToGeneralize___spec__9(x_51, x_72, x_73);
x_107 = lean_ctor_get(x_106, 1);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 0);
lean_inc(x_108);
lean_dec(x_106);
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
lean_dec(x_107);
x_110 = lean_st_ref_take(x_10, x_76);
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_110, 1);
lean_inc(x_112);
lean_dec(x_110);
x_113 = !lean_is_exclusive(x_111);
if (x_113 == 0)
{
lean_object* x_114; lean_object* x_115; uint8_t x_116; 
x_114 = lean_ctor_get(x_111, 0);
lean_dec(x_114);
lean_ctor_set(x_111, 0, x_109);
x_115 = lean_st_ref_set(x_10, x_111, x_112);
x_116 = !lean_is_exclusive(x_115);
if (x_116 == 0)
{
lean_object* x_117; 
x_117 = lean_ctor_get(x_115, 0);
lean_dec(x_117);
lean_ctor_set(x_115, 0, x_108);
x_66 = x_115;
goto block_70;
}
else
{
lean_object* x_118; lean_object* x_119; 
x_118 = lean_ctor_get(x_115, 1);
lean_inc(x_118);
lean_dec(x_115);
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_108);
lean_ctor_set(x_119, 1, x_118);
x_66 = x_119;
goto block_70;
}
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_120 = lean_ctor_get(x_111, 1);
x_121 = lean_ctor_get(x_111, 2);
x_122 = lean_ctor_get(x_111, 3);
x_123 = lean_ctor_get(x_111, 4);
lean_inc(x_123);
lean_inc(x_122);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_111);
x_124 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_124, 0, x_109);
lean_ctor_set(x_124, 1, x_120);
lean_ctor_set(x_124, 2, x_121);
lean_ctor_set(x_124, 3, x_122);
lean_ctor_set(x_124, 4, x_123);
x_125 = lean_st_ref_set(x_10, x_124, x_112);
x_126 = lean_ctor_get(x_125, 1);
lean_inc(x_126);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 lean_ctor_release(x_125, 1);
 x_127 = x_125;
} else {
 lean_dec_ref(x_125);
 x_127 = lean_box(0);
}
if (lean_is_scalar(x_127)) {
 x_128 = lean_alloc_ctor(0, 2, 0);
} else {
 x_128 = x_127;
}
lean_ctor_set(x_128, 0, x_108);
lean_ctor_set(x_128, 1, x_126);
x_66 = x_128;
goto block_70;
}
}
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; uint8_t x_136; 
lean_dec(x_77);
lean_inc(x_51);
x_129 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__12___at_Lean_Meta_getFVarSetToGeneralize___spec__20(x_51, x_72, x_73);
x_130 = lean_ctor_get(x_129, 1);
lean_inc(x_130);
x_131 = lean_ctor_get(x_129, 0);
lean_inc(x_131);
lean_dec(x_129);
x_132 = lean_ctor_get(x_130, 1);
lean_inc(x_132);
lean_dec(x_130);
x_133 = lean_st_ref_take(x_10, x_76);
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_133, 1);
lean_inc(x_135);
lean_dec(x_133);
x_136 = !lean_is_exclusive(x_134);
if (x_136 == 0)
{
lean_object* x_137; lean_object* x_138; uint8_t x_139; 
x_137 = lean_ctor_get(x_134, 0);
lean_dec(x_137);
lean_ctor_set(x_134, 0, x_132);
x_138 = lean_st_ref_set(x_10, x_134, x_135);
x_139 = !lean_is_exclusive(x_138);
if (x_139 == 0)
{
lean_object* x_140; 
x_140 = lean_ctor_get(x_138, 0);
lean_dec(x_140);
lean_ctor_set(x_138, 0, x_131);
x_66 = x_138;
goto block_70;
}
else
{
lean_object* x_141; lean_object* x_142; 
x_141 = lean_ctor_get(x_138, 1);
lean_inc(x_141);
lean_dec(x_138);
x_142 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_142, 0, x_131);
lean_ctor_set(x_142, 1, x_141);
x_66 = x_142;
goto block_70;
}
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_143 = lean_ctor_get(x_134, 1);
x_144 = lean_ctor_get(x_134, 2);
x_145 = lean_ctor_get(x_134, 3);
x_146 = lean_ctor_get(x_134, 4);
lean_inc(x_146);
lean_inc(x_145);
lean_inc(x_144);
lean_inc(x_143);
lean_dec(x_134);
x_147 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_147, 0, x_132);
lean_ctor_set(x_147, 1, x_143);
lean_ctor_set(x_147, 2, x_144);
lean_ctor_set(x_147, 3, x_145);
lean_ctor_set(x_147, 4, x_146);
x_148 = lean_st_ref_set(x_10, x_147, x_135);
x_149 = lean_ctor_get(x_148, 1);
lean_inc(x_149);
if (lean_is_exclusive(x_148)) {
 lean_ctor_release(x_148, 0);
 lean_ctor_release(x_148, 1);
 x_150 = x_148;
} else {
 lean_dec_ref(x_148);
 x_150 = lean_box(0);
}
if (lean_is_scalar(x_150)) {
 x_151 = lean_alloc_ctor(0, 2, 0);
} else {
 x_151 = x_150;
}
lean_ctor_set(x_151, 0, x_131);
lean_ctor_set(x_151, 1, x_149);
x_66 = x_151;
goto block_70;
}
}
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; uint8_t x_157; 
x_152 = lean_ctor_get(x_73, 0);
x_153 = lean_ctor_get(x_73, 1);
lean_inc(x_153);
lean_inc(x_152);
lean_dec(x_73);
x_154 = lean_ctor_get(x_152, 0);
lean_inc(x_154);
lean_dec(x_152);
x_155 = l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__3;
lean_inc(x_154);
x_156 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_156, 0, x_155);
lean_ctor_set(x_156, 1, x_154);
x_157 = l_Lean_Expr_hasFVar(x_72);
if (x_157 == 0)
{
uint8_t x_158; 
x_158 = l_Lean_Expr_hasMVar(x_72);
if (x_158 == 0)
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; uint8_t x_171; lean_object* x_172; lean_object* x_173; 
lean_dec(x_156);
lean_dec(x_72);
x_159 = lean_st_ref_take(x_10, x_153);
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_159, 1);
lean_inc(x_161);
lean_dec(x_159);
x_162 = lean_ctor_get(x_160, 1);
lean_inc(x_162);
x_163 = lean_ctor_get(x_160, 2);
lean_inc(x_163);
x_164 = lean_ctor_get(x_160, 3);
lean_inc(x_164);
x_165 = lean_ctor_get(x_160, 4);
lean_inc(x_165);
if (lean_is_exclusive(x_160)) {
 lean_ctor_release(x_160, 0);
 lean_ctor_release(x_160, 1);
 lean_ctor_release(x_160, 2);
 lean_ctor_release(x_160, 3);
 lean_ctor_release(x_160, 4);
 x_166 = x_160;
} else {
 lean_dec_ref(x_160);
 x_166 = lean_box(0);
}
if (lean_is_scalar(x_166)) {
 x_167 = lean_alloc_ctor(0, 5, 0);
} else {
 x_167 = x_166;
}
lean_ctor_set(x_167, 0, x_154);
lean_ctor_set(x_167, 1, x_162);
lean_ctor_set(x_167, 2, x_163);
lean_ctor_set(x_167, 3, x_164);
lean_ctor_set(x_167, 4, x_165);
x_168 = lean_st_ref_set(x_10, x_167, x_161);
x_169 = lean_ctor_get(x_168, 1);
lean_inc(x_169);
if (lean_is_exclusive(x_168)) {
 lean_ctor_release(x_168, 0);
 lean_ctor_release(x_168, 1);
 x_170 = x_168;
} else {
 lean_dec_ref(x_168);
 x_170 = lean_box(0);
}
x_171 = 0;
x_172 = lean_box(x_171);
if (lean_is_scalar(x_170)) {
 x_173 = lean_alloc_ctor(0, 2, 0);
} else {
 x_173 = x_170;
}
lean_ctor_set(x_173, 0, x_172);
lean_ctor_set(x_173, 1, x_169);
x_66 = x_173;
goto block_70;
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
lean_dec(x_154);
lean_inc(x_51);
x_174 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__1___at_Lean_Meta_getFVarSetToGeneralize___spec__9(x_51, x_72, x_156);
x_175 = lean_ctor_get(x_174, 1);
lean_inc(x_175);
x_176 = lean_ctor_get(x_174, 0);
lean_inc(x_176);
lean_dec(x_174);
x_177 = lean_ctor_get(x_175, 1);
lean_inc(x_177);
lean_dec(x_175);
x_178 = lean_st_ref_take(x_10, x_153);
x_179 = lean_ctor_get(x_178, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_178, 1);
lean_inc(x_180);
lean_dec(x_178);
x_181 = lean_ctor_get(x_179, 1);
lean_inc(x_181);
x_182 = lean_ctor_get(x_179, 2);
lean_inc(x_182);
x_183 = lean_ctor_get(x_179, 3);
lean_inc(x_183);
x_184 = lean_ctor_get(x_179, 4);
lean_inc(x_184);
if (lean_is_exclusive(x_179)) {
 lean_ctor_release(x_179, 0);
 lean_ctor_release(x_179, 1);
 lean_ctor_release(x_179, 2);
 lean_ctor_release(x_179, 3);
 lean_ctor_release(x_179, 4);
 x_185 = x_179;
} else {
 lean_dec_ref(x_179);
 x_185 = lean_box(0);
}
if (lean_is_scalar(x_185)) {
 x_186 = lean_alloc_ctor(0, 5, 0);
} else {
 x_186 = x_185;
}
lean_ctor_set(x_186, 0, x_177);
lean_ctor_set(x_186, 1, x_181);
lean_ctor_set(x_186, 2, x_182);
lean_ctor_set(x_186, 3, x_183);
lean_ctor_set(x_186, 4, x_184);
x_187 = lean_st_ref_set(x_10, x_186, x_180);
x_188 = lean_ctor_get(x_187, 1);
lean_inc(x_188);
if (lean_is_exclusive(x_187)) {
 lean_ctor_release(x_187, 0);
 lean_ctor_release(x_187, 1);
 x_189 = x_187;
} else {
 lean_dec_ref(x_187);
 x_189 = lean_box(0);
}
if (lean_is_scalar(x_189)) {
 x_190 = lean_alloc_ctor(0, 2, 0);
} else {
 x_190 = x_189;
}
lean_ctor_set(x_190, 0, x_176);
lean_ctor_set(x_190, 1, x_188);
x_66 = x_190;
goto block_70;
}
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; 
lean_dec(x_154);
lean_inc(x_51);
x_191 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__12___at_Lean_Meta_getFVarSetToGeneralize___spec__20(x_51, x_72, x_156);
x_192 = lean_ctor_get(x_191, 1);
lean_inc(x_192);
x_193 = lean_ctor_get(x_191, 0);
lean_inc(x_193);
lean_dec(x_191);
x_194 = lean_ctor_get(x_192, 1);
lean_inc(x_194);
lean_dec(x_192);
x_195 = lean_st_ref_take(x_10, x_153);
x_196 = lean_ctor_get(x_195, 0);
lean_inc(x_196);
x_197 = lean_ctor_get(x_195, 1);
lean_inc(x_197);
lean_dec(x_195);
x_198 = lean_ctor_get(x_196, 1);
lean_inc(x_198);
x_199 = lean_ctor_get(x_196, 2);
lean_inc(x_199);
x_200 = lean_ctor_get(x_196, 3);
lean_inc(x_200);
x_201 = lean_ctor_get(x_196, 4);
lean_inc(x_201);
if (lean_is_exclusive(x_196)) {
 lean_ctor_release(x_196, 0);
 lean_ctor_release(x_196, 1);
 lean_ctor_release(x_196, 2);
 lean_ctor_release(x_196, 3);
 lean_ctor_release(x_196, 4);
 x_202 = x_196;
} else {
 lean_dec_ref(x_196);
 x_202 = lean_box(0);
}
if (lean_is_scalar(x_202)) {
 x_203 = lean_alloc_ctor(0, 5, 0);
} else {
 x_203 = x_202;
}
lean_ctor_set(x_203, 0, x_194);
lean_ctor_set(x_203, 1, x_198);
lean_ctor_set(x_203, 2, x_199);
lean_ctor_set(x_203, 3, x_200);
lean_ctor_set(x_203, 4, x_201);
x_204 = lean_st_ref_set(x_10, x_203, x_197);
x_205 = lean_ctor_get(x_204, 1);
lean_inc(x_205);
if (lean_is_exclusive(x_204)) {
 lean_ctor_release(x_204, 0);
 lean_ctor_release(x_204, 1);
 x_206 = x_204;
} else {
 lean_dec_ref(x_204);
 x_206 = lean_box(0);
}
if (lean_is_scalar(x_206)) {
 x_207 = lean_alloc_ctor(0, 2, 0);
} else {
 x_207 = x_206;
}
lean_ctor_set(x_207, 0, x_193);
lean_ctor_set(x_207, 1, x_205);
x_66 = x_207;
goto block_70;
}
}
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; uint8_t x_211; 
x_208 = lean_ctor_get(x_48, 3);
lean_inc(x_208);
x_209 = lean_ctor_get(x_48, 4);
lean_inc(x_209);
lean_dec(x_48);
x_210 = lean_st_ref_get(x_10, x_13);
x_211 = !lean_is_exclusive(x_210);
if (x_211 == 0)
{
lean_object* x_212; lean_object* x_213; uint8_t x_214; lean_object* x_215; uint8_t x_232; lean_object* x_233; lean_object* x_246; lean_object* x_247; uint8_t x_248; 
x_212 = lean_ctor_get(x_210, 0);
x_213 = lean_ctor_get(x_210, 1);
x_246 = lean_ctor_get(x_212, 0);
lean_inc(x_246);
lean_dec(x_212);
x_247 = l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__3;
lean_ctor_set(x_210, 1, x_246);
lean_ctor_set(x_210, 0, x_247);
x_248 = l_Lean_Expr_hasFVar(x_208);
if (x_248 == 0)
{
uint8_t x_249; 
x_249 = l_Lean_Expr_hasMVar(x_208);
if (x_249 == 0)
{
uint8_t x_250; 
lean_dec(x_208);
x_250 = 0;
x_232 = x_250;
x_233 = x_210;
goto block_245;
}
else
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; uint8_t x_254; 
lean_inc(x_51);
x_251 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__39___at_Lean_Meta_getFVarSetToGeneralize___spec__47(x_51, x_208, x_210);
x_252 = lean_ctor_get(x_251, 0);
lean_inc(x_252);
x_253 = lean_ctor_get(x_251, 1);
lean_inc(x_253);
lean_dec(x_251);
x_254 = lean_unbox(x_252);
lean_dec(x_252);
x_232 = x_254;
x_233 = x_253;
goto block_245;
}
}
else
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; uint8_t x_258; 
lean_inc(x_51);
x_255 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__50___at_Lean_Meta_getFVarSetToGeneralize___spec__58(x_51, x_208, x_210);
x_256 = lean_ctor_get(x_255, 0);
lean_inc(x_256);
x_257 = lean_ctor_get(x_255, 1);
lean_inc(x_257);
lean_dec(x_255);
x_258 = lean_unbox(x_256);
lean_dec(x_256);
x_232 = x_258;
x_233 = x_257;
goto block_245;
}
block_231:
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; uint8_t x_220; 
x_216 = lean_ctor_get(x_215, 1);
lean_inc(x_216);
lean_dec(x_215);
x_217 = lean_st_ref_take(x_10, x_213);
x_218 = lean_ctor_get(x_217, 0);
lean_inc(x_218);
x_219 = lean_ctor_get(x_217, 1);
lean_inc(x_219);
lean_dec(x_217);
x_220 = !lean_is_exclusive(x_218);
if (x_220 == 0)
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; 
x_221 = lean_ctor_get(x_218, 0);
lean_dec(x_221);
lean_ctor_set(x_218, 0, x_216);
x_222 = lean_st_ref_set(x_10, x_218, x_219);
x_223 = lean_ctor_get(x_222, 1);
lean_inc(x_223);
lean_dec(x_222);
x_54 = x_214;
x_55 = x_223;
goto block_65;
}
else
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; 
x_224 = lean_ctor_get(x_218, 1);
x_225 = lean_ctor_get(x_218, 2);
x_226 = lean_ctor_get(x_218, 3);
x_227 = lean_ctor_get(x_218, 4);
lean_inc(x_227);
lean_inc(x_226);
lean_inc(x_225);
lean_inc(x_224);
lean_dec(x_218);
x_228 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_228, 0, x_216);
lean_ctor_set(x_228, 1, x_224);
lean_ctor_set(x_228, 2, x_225);
lean_ctor_set(x_228, 3, x_226);
lean_ctor_set(x_228, 4, x_227);
x_229 = lean_st_ref_set(x_10, x_228, x_219);
x_230 = lean_ctor_get(x_229, 1);
lean_inc(x_230);
lean_dec(x_229);
x_54 = x_214;
x_55 = x_230;
goto block_65;
}
}
block_245:
{
if (x_232 == 0)
{
uint8_t x_234; 
x_234 = l_Lean_Expr_hasFVar(x_209);
if (x_234 == 0)
{
uint8_t x_235; 
x_235 = l_Lean_Expr_hasMVar(x_209);
if (x_235 == 0)
{
uint8_t x_236; 
lean_dec(x_209);
x_236 = 0;
x_214 = x_236;
x_215 = x_233;
goto block_231;
}
else
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; uint8_t x_240; 
lean_inc(x_51);
lean_inc(x_3);
x_237 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__23(x_3, x_51, x_209, x_233);
x_238 = lean_ctor_get(x_237, 0);
lean_inc(x_238);
x_239 = lean_ctor_get(x_237, 1);
lean_inc(x_239);
lean_dec(x_237);
x_240 = lean_unbox(x_238);
lean_dec(x_238);
x_214 = x_240;
x_215 = x_239;
goto block_231;
}
}
else
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; uint8_t x_244; 
lean_inc(x_51);
lean_inc(x_3);
x_241 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__31(x_3, x_51, x_209, x_233);
x_242 = lean_ctor_get(x_241, 0);
lean_inc(x_242);
x_243 = lean_ctor_get(x_241, 1);
lean_inc(x_243);
lean_dec(x_241);
x_244 = lean_unbox(x_242);
lean_dec(x_242);
x_214 = x_244;
x_215 = x_243;
goto block_231;
}
}
else
{
lean_dec(x_209);
x_214 = x_232;
x_215 = x_233;
goto block_231;
}
}
}
else
{
lean_object* x_259; lean_object* x_260; uint8_t x_261; lean_object* x_262; uint8_t x_276; lean_object* x_277; lean_object* x_290; lean_object* x_291; lean_object* x_292; uint8_t x_293; 
x_259 = lean_ctor_get(x_210, 0);
x_260 = lean_ctor_get(x_210, 1);
lean_inc(x_260);
lean_inc(x_259);
lean_dec(x_210);
x_290 = lean_ctor_get(x_259, 0);
lean_inc(x_290);
lean_dec(x_259);
x_291 = l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__3;
x_292 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_292, 0, x_291);
lean_ctor_set(x_292, 1, x_290);
x_293 = l_Lean_Expr_hasFVar(x_208);
if (x_293 == 0)
{
uint8_t x_294; 
x_294 = l_Lean_Expr_hasMVar(x_208);
if (x_294 == 0)
{
uint8_t x_295; 
lean_dec(x_208);
x_295 = 0;
x_276 = x_295;
x_277 = x_292;
goto block_289;
}
else
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; uint8_t x_299; 
lean_inc(x_51);
x_296 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__39___at_Lean_Meta_getFVarSetToGeneralize___spec__47(x_51, x_208, x_292);
x_297 = lean_ctor_get(x_296, 0);
lean_inc(x_297);
x_298 = lean_ctor_get(x_296, 1);
lean_inc(x_298);
lean_dec(x_296);
x_299 = lean_unbox(x_297);
lean_dec(x_297);
x_276 = x_299;
x_277 = x_298;
goto block_289;
}
}
else
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; uint8_t x_303; 
lean_inc(x_51);
x_300 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__50___at_Lean_Meta_getFVarSetToGeneralize___spec__58(x_51, x_208, x_292);
x_301 = lean_ctor_get(x_300, 0);
lean_inc(x_301);
x_302 = lean_ctor_get(x_300, 1);
lean_inc(x_302);
lean_dec(x_300);
x_303 = lean_unbox(x_301);
lean_dec(x_301);
x_276 = x_303;
x_277 = x_302;
goto block_289;
}
block_275:
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; 
x_263 = lean_ctor_get(x_262, 1);
lean_inc(x_263);
lean_dec(x_262);
x_264 = lean_st_ref_take(x_10, x_260);
x_265 = lean_ctor_get(x_264, 0);
lean_inc(x_265);
x_266 = lean_ctor_get(x_264, 1);
lean_inc(x_266);
lean_dec(x_264);
x_267 = lean_ctor_get(x_265, 1);
lean_inc(x_267);
x_268 = lean_ctor_get(x_265, 2);
lean_inc(x_268);
x_269 = lean_ctor_get(x_265, 3);
lean_inc(x_269);
x_270 = lean_ctor_get(x_265, 4);
lean_inc(x_270);
if (lean_is_exclusive(x_265)) {
 lean_ctor_release(x_265, 0);
 lean_ctor_release(x_265, 1);
 lean_ctor_release(x_265, 2);
 lean_ctor_release(x_265, 3);
 lean_ctor_release(x_265, 4);
 x_271 = x_265;
} else {
 lean_dec_ref(x_265);
 x_271 = lean_box(0);
}
if (lean_is_scalar(x_271)) {
 x_272 = lean_alloc_ctor(0, 5, 0);
} else {
 x_272 = x_271;
}
lean_ctor_set(x_272, 0, x_263);
lean_ctor_set(x_272, 1, x_267);
lean_ctor_set(x_272, 2, x_268);
lean_ctor_set(x_272, 3, x_269);
lean_ctor_set(x_272, 4, x_270);
x_273 = lean_st_ref_set(x_10, x_272, x_266);
x_274 = lean_ctor_get(x_273, 1);
lean_inc(x_274);
lean_dec(x_273);
x_54 = x_261;
x_55 = x_274;
goto block_65;
}
block_289:
{
if (x_276 == 0)
{
uint8_t x_278; 
x_278 = l_Lean_Expr_hasFVar(x_209);
if (x_278 == 0)
{
uint8_t x_279; 
x_279 = l_Lean_Expr_hasMVar(x_209);
if (x_279 == 0)
{
uint8_t x_280; 
lean_dec(x_209);
x_280 = 0;
x_261 = x_280;
x_262 = x_277;
goto block_275;
}
else
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; uint8_t x_284; 
lean_inc(x_51);
lean_inc(x_3);
x_281 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__23(x_3, x_51, x_209, x_277);
x_282 = lean_ctor_get(x_281, 0);
lean_inc(x_282);
x_283 = lean_ctor_get(x_281, 1);
lean_inc(x_283);
lean_dec(x_281);
x_284 = lean_unbox(x_282);
lean_dec(x_282);
x_261 = x_284;
x_262 = x_283;
goto block_275;
}
}
else
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; uint8_t x_288; 
lean_inc(x_51);
lean_inc(x_3);
x_285 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__31(x_3, x_51, x_209, x_277);
x_286 = lean_ctor_get(x_285, 0);
lean_inc(x_286);
x_287 = lean_ctor_get(x_285, 1);
lean_inc(x_287);
lean_dec(x_285);
x_288 = lean_unbox(x_286);
lean_dec(x_286);
x_261 = x_288;
x_262 = x_287;
goto block_275;
}
}
else
{
lean_dec(x_209);
x_261 = x_276;
x_262 = x_277;
goto block_275;
}
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
lean_inc(x_5);
lean_inc(x_3);
x_12 = l_Lean_PersistentArray_forInAux___at_Lean_Meta_getFVarSetToGeneralize___spec__67(x_1, x_2, x_3, x_5, x_11, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
lean_dec(x_3);
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
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; size_t x_25; size_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
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
x_25 = lean_array_size(x_22);
x_26 = 0;
x_27 = l_Array_forInUnsafe_loop___at_Lean_Meta_getFVarSetToGeneralize___spec__70(x_1, x_2, x_3, x_23, x_22, x_25, x_26, x_24, x_6, x_7, x_8, x_9, x_20);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_27);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_27, 0);
lean_dec(x_31);
x_32 = lean_ctor_get(x_28, 1);
lean_inc(x_32);
lean_dec(x_28);
lean_ctor_set(x_27, 0, x_32);
return x_27;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_27, 1);
lean_inc(x_33);
lean_dec(x_27);
x_34 = lean_ctor_get(x_28, 1);
lean_inc(x_34);
lean_dec(x_28);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
return x_35;
}
}
else
{
uint8_t x_36; 
lean_dec(x_28);
x_36 = !lean_is_exclusive(x_27);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_27, 0);
lean_dec(x_37);
x_38 = lean_ctor_get(x_29, 0);
lean_inc(x_38);
lean_dec(x_29);
lean_ctor_set(x_27, 0, x_38);
return x_27;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_27, 1);
lean_inc(x_39);
lean_dec(x_27);
x_40 = lean_ctor_get(x_29, 0);
lean_inc(x_40);
lean_dec(x_29);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
return x_41;
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
lean_dec(x_6);
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
lean_dec(x_5);
lean_dec(x_3);
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
lean_inc(x_19);
lean_inc(x_3);
x_21 = l_Lean_PersistentArray_forInAux___at_Lean_Meta_getFVarSetToGeneralize___spec__73(x_1, x_2, x_3, x_4, x_17, x_19, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_17);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
lean_dec(x_5);
lean_dec(x_3);
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
lean_inc(x_34);
lean_inc(x_3);
x_35 = l_Lean_PersistentArray_forInAux___at_Lean_Meta_getFVarSetToGeneralize___spec__73(x_1, x_2, x_3, x_4, x_17, x_34, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_17);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_5);
lean_dec(x_3);
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
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; lean_object* x_66; lean_object* x_71; lean_object* x_305; 
x_48 = lean_ctor_get(x_16, 0);
lean_inc(x_48);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 x_49 = x_16;
} else {
 lean_dec_ref(x_16);
 x_49 = lean_box(0);
}
x_50 = lean_ctor_get(x_25, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_25, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_52 = x_25;
} else {
 lean_dec_ref(x_25);
 x_52 = lean_box(0);
}
x_53 = l_Lean_LocalDecl_fvarId(x_48);
x_305 = l_Lean_RBNode_findCore___at_Lean_Meta_mkGeneralizationForbiddenSet_visit___spec__1(x_1, x_53);
if (lean_obj_tag(x_305) == 0)
{
uint8_t x_306; 
x_306 = l_Lean_LocalDecl_isAuxDecl(x_48);
if (x_306 == 0)
{
uint8_t x_307; uint8_t x_308; 
x_307 = l_Lean_LocalDecl_binderInfo(x_48);
x_308 = l_Lean_BinderInfo_isInstImplicit(x_307);
if (x_308 == 0)
{
if (x_2 == 0)
{
lean_object* x_309; 
x_309 = lean_box(0);
x_71 = x_309;
goto block_304;
}
else
{
uint8_t x_310; 
x_310 = l_Lean_LocalDecl_isLet(x_48);
if (x_310 == 0)
{
lean_object* x_311; 
x_311 = lean_box(0);
x_71 = x_311;
goto block_304;
}
else
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; 
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_49);
lean_dec(x_48);
x_312 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_312, 0, x_50);
lean_ctor_set(x_312, 1, x_51);
x_313 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_313, 0, x_312);
x_314 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_314, 0, x_313);
lean_ctor_set(x_314, 1, x_13);
x_27 = x_314;
goto block_43;
}
}
}
else
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; 
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_49);
lean_dec(x_48);
x_315 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_315, 0, x_50);
lean_ctor_set(x_315, 1, x_51);
x_316 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_316, 0, x_315);
x_317 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_317, 0, x_316);
lean_ctor_set(x_317, 1, x_13);
x_27 = x_317;
goto block_43;
}
}
else
{
lean_object* x_318; lean_object* x_319; lean_object* x_320; 
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_49);
lean_dec(x_48);
x_318 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_318, 0, x_50);
lean_ctor_set(x_318, 1, x_51);
x_319 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_319, 0, x_318);
x_320 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_320, 0, x_319);
lean_ctor_set(x_320, 1, x_13);
x_27 = x_320;
goto block_43;
}
}
else
{
uint8_t x_321; 
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_49);
lean_dec(x_48);
x_321 = !lean_is_exclusive(x_305);
if (x_321 == 0)
{
lean_object* x_322; lean_object* x_323; lean_object* x_324; 
x_322 = lean_ctor_get(x_305, 0);
lean_dec(x_322);
x_323 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_323, 0, x_50);
lean_ctor_set(x_323, 1, x_51);
lean_ctor_set(x_305, 0, x_323);
x_324 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_324, 0, x_305);
lean_ctor_set(x_324, 1, x_13);
x_27 = x_324;
goto block_43;
}
else
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; 
lean_dec(x_305);
x_325 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_325, 0, x_50);
lean_ctor_set(x_325, 1, x_51);
x_326 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_326, 0, x_325);
x_327 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_327, 0, x_326);
lean_ctor_set(x_327, 1, x_13);
x_27 = x_327;
goto block_43;
}
}
block_65:
{
if (x_54 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_53);
if (lean_is_scalar(x_52)) {
 x_56 = lean_alloc_ctor(0, 2, 0);
} else {
 x_56 = x_52;
}
lean_ctor_set(x_56, 0, x_50);
lean_ctor_set(x_56, 1, x_51);
if (lean_is_scalar(x_49)) {
 x_57 = lean_alloc_ctor(1, 1, 0);
} else {
 x_57 = x_49;
}
lean_ctor_set(x_57, 0, x_56);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_55);
x_27 = x_58;
goto block_43;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_59 = lean_box(0);
lean_inc(x_53);
x_60 = l_Lean_RBNode_insert___at_Lean_FVarIdSet_insert___spec__1(x_50, x_53, x_59);
x_61 = l_Lean_RBNode_insert___at_Lean_FVarIdSet_insert___spec__1(x_51, x_53, x_59);
if (lean_is_scalar(x_52)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_52;
}
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
if (lean_is_scalar(x_49)) {
 x_63 = lean_alloc_ctor(1, 1, 0);
} else {
 x_63 = x_49;
}
lean_ctor_set(x_63, 0, x_62);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_55);
x_27 = x_64;
goto block_43;
}
}
block_70:
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = lean_unbox(x_67);
lean_dec(x_67);
x_54 = x_69;
x_55 = x_68;
goto block_65;
}
block_304:
{
lean_dec(x_71);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_72 = lean_ctor_get(x_48, 3);
lean_inc(x_72);
lean_dec(x_48);
x_73 = lean_st_ref_get(x_10, x_13);
x_74 = !lean_is_exclusive(x_73);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
x_75 = lean_ctor_get(x_73, 0);
x_76 = lean_ctor_get(x_73, 1);
x_77 = lean_ctor_get(x_75, 0);
lean_inc(x_77);
lean_dec(x_75);
x_78 = l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__3;
lean_inc(x_77);
lean_ctor_set(x_73, 1, x_77);
lean_ctor_set(x_73, 0, x_78);
x_79 = l_Lean_Expr_hasFVar(x_72);
if (x_79 == 0)
{
uint8_t x_80; 
x_80 = l_Lean_Expr_hasMVar(x_72);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; 
lean_dec(x_73);
lean_dec(x_72);
x_81 = lean_st_ref_take(x_10, x_76);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
x_84 = !lean_is_exclusive(x_82);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_85 = lean_ctor_get(x_82, 0);
lean_dec(x_85);
lean_ctor_set(x_82, 0, x_77);
x_86 = lean_st_ref_set(x_10, x_82, x_83);
x_87 = !lean_is_exclusive(x_86);
if (x_87 == 0)
{
lean_object* x_88; uint8_t x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_86, 0);
lean_dec(x_88);
x_89 = 0;
x_90 = lean_box(x_89);
lean_ctor_set(x_86, 0, x_90);
x_66 = x_86;
goto block_70;
}
else
{
lean_object* x_91; uint8_t x_92; lean_object* x_93; lean_object* x_94; 
x_91 = lean_ctor_get(x_86, 1);
lean_inc(x_91);
lean_dec(x_86);
x_92 = 0;
x_93 = lean_box(x_92);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_91);
x_66 = x_94;
goto block_70;
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; lean_object* x_104; lean_object* x_105; 
x_95 = lean_ctor_get(x_82, 1);
x_96 = lean_ctor_get(x_82, 2);
x_97 = lean_ctor_get(x_82, 3);
x_98 = lean_ctor_get(x_82, 4);
lean_inc(x_98);
lean_inc(x_97);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_82);
x_99 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_99, 0, x_77);
lean_ctor_set(x_99, 1, x_95);
lean_ctor_set(x_99, 2, x_96);
lean_ctor_set(x_99, 3, x_97);
lean_ctor_set(x_99, 4, x_98);
x_100 = lean_st_ref_set(x_10, x_99, x_83);
x_101 = lean_ctor_get(x_100, 1);
lean_inc(x_101);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 lean_ctor_release(x_100, 1);
 x_102 = x_100;
} else {
 lean_dec_ref(x_100);
 x_102 = lean_box(0);
}
x_103 = 0;
x_104 = lean_box(x_103);
if (lean_is_scalar(x_102)) {
 x_105 = lean_alloc_ctor(0, 2, 0);
} else {
 x_105 = x_102;
}
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_101);
x_66 = x_105;
goto block_70;
}
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; 
lean_dec(x_77);
lean_inc(x_51);
x_106 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__1___at_Lean_Meta_getFVarSetToGeneralize___spec__9(x_51, x_72, x_73);
x_107 = lean_ctor_get(x_106, 1);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 0);
lean_inc(x_108);
lean_dec(x_106);
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
lean_dec(x_107);
x_110 = lean_st_ref_take(x_10, x_76);
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_110, 1);
lean_inc(x_112);
lean_dec(x_110);
x_113 = !lean_is_exclusive(x_111);
if (x_113 == 0)
{
lean_object* x_114; lean_object* x_115; uint8_t x_116; 
x_114 = lean_ctor_get(x_111, 0);
lean_dec(x_114);
lean_ctor_set(x_111, 0, x_109);
x_115 = lean_st_ref_set(x_10, x_111, x_112);
x_116 = !lean_is_exclusive(x_115);
if (x_116 == 0)
{
lean_object* x_117; 
x_117 = lean_ctor_get(x_115, 0);
lean_dec(x_117);
lean_ctor_set(x_115, 0, x_108);
x_66 = x_115;
goto block_70;
}
else
{
lean_object* x_118; lean_object* x_119; 
x_118 = lean_ctor_get(x_115, 1);
lean_inc(x_118);
lean_dec(x_115);
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_108);
lean_ctor_set(x_119, 1, x_118);
x_66 = x_119;
goto block_70;
}
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_120 = lean_ctor_get(x_111, 1);
x_121 = lean_ctor_get(x_111, 2);
x_122 = lean_ctor_get(x_111, 3);
x_123 = lean_ctor_get(x_111, 4);
lean_inc(x_123);
lean_inc(x_122);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_111);
x_124 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_124, 0, x_109);
lean_ctor_set(x_124, 1, x_120);
lean_ctor_set(x_124, 2, x_121);
lean_ctor_set(x_124, 3, x_122);
lean_ctor_set(x_124, 4, x_123);
x_125 = lean_st_ref_set(x_10, x_124, x_112);
x_126 = lean_ctor_get(x_125, 1);
lean_inc(x_126);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 lean_ctor_release(x_125, 1);
 x_127 = x_125;
} else {
 lean_dec_ref(x_125);
 x_127 = lean_box(0);
}
if (lean_is_scalar(x_127)) {
 x_128 = lean_alloc_ctor(0, 2, 0);
} else {
 x_128 = x_127;
}
lean_ctor_set(x_128, 0, x_108);
lean_ctor_set(x_128, 1, x_126);
x_66 = x_128;
goto block_70;
}
}
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; uint8_t x_136; 
lean_dec(x_77);
lean_inc(x_51);
x_129 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__12___at_Lean_Meta_getFVarSetToGeneralize___spec__20(x_51, x_72, x_73);
x_130 = lean_ctor_get(x_129, 1);
lean_inc(x_130);
x_131 = lean_ctor_get(x_129, 0);
lean_inc(x_131);
lean_dec(x_129);
x_132 = lean_ctor_get(x_130, 1);
lean_inc(x_132);
lean_dec(x_130);
x_133 = lean_st_ref_take(x_10, x_76);
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_133, 1);
lean_inc(x_135);
lean_dec(x_133);
x_136 = !lean_is_exclusive(x_134);
if (x_136 == 0)
{
lean_object* x_137; lean_object* x_138; uint8_t x_139; 
x_137 = lean_ctor_get(x_134, 0);
lean_dec(x_137);
lean_ctor_set(x_134, 0, x_132);
x_138 = lean_st_ref_set(x_10, x_134, x_135);
x_139 = !lean_is_exclusive(x_138);
if (x_139 == 0)
{
lean_object* x_140; 
x_140 = lean_ctor_get(x_138, 0);
lean_dec(x_140);
lean_ctor_set(x_138, 0, x_131);
x_66 = x_138;
goto block_70;
}
else
{
lean_object* x_141; lean_object* x_142; 
x_141 = lean_ctor_get(x_138, 1);
lean_inc(x_141);
lean_dec(x_138);
x_142 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_142, 0, x_131);
lean_ctor_set(x_142, 1, x_141);
x_66 = x_142;
goto block_70;
}
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_143 = lean_ctor_get(x_134, 1);
x_144 = lean_ctor_get(x_134, 2);
x_145 = lean_ctor_get(x_134, 3);
x_146 = lean_ctor_get(x_134, 4);
lean_inc(x_146);
lean_inc(x_145);
lean_inc(x_144);
lean_inc(x_143);
lean_dec(x_134);
x_147 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_147, 0, x_132);
lean_ctor_set(x_147, 1, x_143);
lean_ctor_set(x_147, 2, x_144);
lean_ctor_set(x_147, 3, x_145);
lean_ctor_set(x_147, 4, x_146);
x_148 = lean_st_ref_set(x_10, x_147, x_135);
x_149 = lean_ctor_get(x_148, 1);
lean_inc(x_149);
if (lean_is_exclusive(x_148)) {
 lean_ctor_release(x_148, 0);
 lean_ctor_release(x_148, 1);
 x_150 = x_148;
} else {
 lean_dec_ref(x_148);
 x_150 = lean_box(0);
}
if (lean_is_scalar(x_150)) {
 x_151 = lean_alloc_ctor(0, 2, 0);
} else {
 x_151 = x_150;
}
lean_ctor_set(x_151, 0, x_131);
lean_ctor_set(x_151, 1, x_149);
x_66 = x_151;
goto block_70;
}
}
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; uint8_t x_157; 
x_152 = lean_ctor_get(x_73, 0);
x_153 = lean_ctor_get(x_73, 1);
lean_inc(x_153);
lean_inc(x_152);
lean_dec(x_73);
x_154 = lean_ctor_get(x_152, 0);
lean_inc(x_154);
lean_dec(x_152);
x_155 = l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__3;
lean_inc(x_154);
x_156 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_156, 0, x_155);
lean_ctor_set(x_156, 1, x_154);
x_157 = l_Lean_Expr_hasFVar(x_72);
if (x_157 == 0)
{
uint8_t x_158; 
x_158 = l_Lean_Expr_hasMVar(x_72);
if (x_158 == 0)
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; uint8_t x_171; lean_object* x_172; lean_object* x_173; 
lean_dec(x_156);
lean_dec(x_72);
x_159 = lean_st_ref_take(x_10, x_153);
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_159, 1);
lean_inc(x_161);
lean_dec(x_159);
x_162 = lean_ctor_get(x_160, 1);
lean_inc(x_162);
x_163 = lean_ctor_get(x_160, 2);
lean_inc(x_163);
x_164 = lean_ctor_get(x_160, 3);
lean_inc(x_164);
x_165 = lean_ctor_get(x_160, 4);
lean_inc(x_165);
if (lean_is_exclusive(x_160)) {
 lean_ctor_release(x_160, 0);
 lean_ctor_release(x_160, 1);
 lean_ctor_release(x_160, 2);
 lean_ctor_release(x_160, 3);
 lean_ctor_release(x_160, 4);
 x_166 = x_160;
} else {
 lean_dec_ref(x_160);
 x_166 = lean_box(0);
}
if (lean_is_scalar(x_166)) {
 x_167 = lean_alloc_ctor(0, 5, 0);
} else {
 x_167 = x_166;
}
lean_ctor_set(x_167, 0, x_154);
lean_ctor_set(x_167, 1, x_162);
lean_ctor_set(x_167, 2, x_163);
lean_ctor_set(x_167, 3, x_164);
lean_ctor_set(x_167, 4, x_165);
x_168 = lean_st_ref_set(x_10, x_167, x_161);
x_169 = lean_ctor_get(x_168, 1);
lean_inc(x_169);
if (lean_is_exclusive(x_168)) {
 lean_ctor_release(x_168, 0);
 lean_ctor_release(x_168, 1);
 x_170 = x_168;
} else {
 lean_dec_ref(x_168);
 x_170 = lean_box(0);
}
x_171 = 0;
x_172 = lean_box(x_171);
if (lean_is_scalar(x_170)) {
 x_173 = lean_alloc_ctor(0, 2, 0);
} else {
 x_173 = x_170;
}
lean_ctor_set(x_173, 0, x_172);
lean_ctor_set(x_173, 1, x_169);
x_66 = x_173;
goto block_70;
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
lean_dec(x_154);
lean_inc(x_51);
x_174 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__1___at_Lean_Meta_getFVarSetToGeneralize___spec__9(x_51, x_72, x_156);
x_175 = lean_ctor_get(x_174, 1);
lean_inc(x_175);
x_176 = lean_ctor_get(x_174, 0);
lean_inc(x_176);
lean_dec(x_174);
x_177 = lean_ctor_get(x_175, 1);
lean_inc(x_177);
lean_dec(x_175);
x_178 = lean_st_ref_take(x_10, x_153);
x_179 = lean_ctor_get(x_178, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_178, 1);
lean_inc(x_180);
lean_dec(x_178);
x_181 = lean_ctor_get(x_179, 1);
lean_inc(x_181);
x_182 = lean_ctor_get(x_179, 2);
lean_inc(x_182);
x_183 = lean_ctor_get(x_179, 3);
lean_inc(x_183);
x_184 = lean_ctor_get(x_179, 4);
lean_inc(x_184);
if (lean_is_exclusive(x_179)) {
 lean_ctor_release(x_179, 0);
 lean_ctor_release(x_179, 1);
 lean_ctor_release(x_179, 2);
 lean_ctor_release(x_179, 3);
 lean_ctor_release(x_179, 4);
 x_185 = x_179;
} else {
 lean_dec_ref(x_179);
 x_185 = lean_box(0);
}
if (lean_is_scalar(x_185)) {
 x_186 = lean_alloc_ctor(0, 5, 0);
} else {
 x_186 = x_185;
}
lean_ctor_set(x_186, 0, x_177);
lean_ctor_set(x_186, 1, x_181);
lean_ctor_set(x_186, 2, x_182);
lean_ctor_set(x_186, 3, x_183);
lean_ctor_set(x_186, 4, x_184);
x_187 = lean_st_ref_set(x_10, x_186, x_180);
x_188 = lean_ctor_get(x_187, 1);
lean_inc(x_188);
if (lean_is_exclusive(x_187)) {
 lean_ctor_release(x_187, 0);
 lean_ctor_release(x_187, 1);
 x_189 = x_187;
} else {
 lean_dec_ref(x_187);
 x_189 = lean_box(0);
}
if (lean_is_scalar(x_189)) {
 x_190 = lean_alloc_ctor(0, 2, 0);
} else {
 x_190 = x_189;
}
lean_ctor_set(x_190, 0, x_176);
lean_ctor_set(x_190, 1, x_188);
x_66 = x_190;
goto block_70;
}
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; 
lean_dec(x_154);
lean_inc(x_51);
x_191 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__12___at_Lean_Meta_getFVarSetToGeneralize___spec__20(x_51, x_72, x_156);
x_192 = lean_ctor_get(x_191, 1);
lean_inc(x_192);
x_193 = lean_ctor_get(x_191, 0);
lean_inc(x_193);
lean_dec(x_191);
x_194 = lean_ctor_get(x_192, 1);
lean_inc(x_194);
lean_dec(x_192);
x_195 = lean_st_ref_take(x_10, x_153);
x_196 = lean_ctor_get(x_195, 0);
lean_inc(x_196);
x_197 = lean_ctor_get(x_195, 1);
lean_inc(x_197);
lean_dec(x_195);
x_198 = lean_ctor_get(x_196, 1);
lean_inc(x_198);
x_199 = lean_ctor_get(x_196, 2);
lean_inc(x_199);
x_200 = lean_ctor_get(x_196, 3);
lean_inc(x_200);
x_201 = lean_ctor_get(x_196, 4);
lean_inc(x_201);
if (lean_is_exclusive(x_196)) {
 lean_ctor_release(x_196, 0);
 lean_ctor_release(x_196, 1);
 lean_ctor_release(x_196, 2);
 lean_ctor_release(x_196, 3);
 lean_ctor_release(x_196, 4);
 x_202 = x_196;
} else {
 lean_dec_ref(x_196);
 x_202 = lean_box(0);
}
if (lean_is_scalar(x_202)) {
 x_203 = lean_alloc_ctor(0, 5, 0);
} else {
 x_203 = x_202;
}
lean_ctor_set(x_203, 0, x_194);
lean_ctor_set(x_203, 1, x_198);
lean_ctor_set(x_203, 2, x_199);
lean_ctor_set(x_203, 3, x_200);
lean_ctor_set(x_203, 4, x_201);
x_204 = lean_st_ref_set(x_10, x_203, x_197);
x_205 = lean_ctor_get(x_204, 1);
lean_inc(x_205);
if (lean_is_exclusive(x_204)) {
 lean_ctor_release(x_204, 0);
 lean_ctor_release(x_204, 1);
 x_206 = x_204;
} else {
 lean_dec_ref(x_204);
 x_206 = lean_box(0);
}
if (lean_is_scalar(x_206)) {
 x_207 = lean_alloc_ctor(0, 2, 0);
} else {
 x_207 = x_206;
}
lean_ctor_set(x_207, 0, x_193);
lean_ctor_set(x_207, 1, x_205);
x_66 = x_207;
goto block_70;
}
}
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; uint8_t x_211; 
x_208 = lean_ctor_get(x_48, 3);
lean_inc(x_208);
x_209 = lean_ctor_get(x_48, 4);
lean_inc(x_209);
lean_dec(x_48);
x_210 = lean_st_ref_get(x_10, x_13);
x_211 = !lean_is_exclusive(x_210);
if (x_211 == 0)
{
lean_object* x_212; lean_object* x_213; uint8_t x_214; lean_object* x_215; uint8_t x_232; lean_object* x_233; lean_object* x_246; lean_object* x_247; uint8_t x_248; 
x_212 = lean_ctor_get(x_210, 0);
x_213 = lean_ctor_get(x_210, 1);
x_246 = lean_ctor_get(x_212, 0);
lean_inc(x_246);
lean_dec(x_212);
x_247 = l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__3;
lean_ctor_set(x_210, 1, x_246);
lean_ctor_set(x_210, 0, x_247);
x_248 = l_Lean_Expr_hasFVar(x_208);
if (x_248 == 0)
{
uint8_t x_249; 
x_249 = l_Lean_Expr_hasMVar(x_208);
if (x_249 == 0)
{
uint8_t x_250; 
lean_dec(x_208);
x_250 = 0;
x_232 = x_250;
x_233 = x_210;
goto block_245;
}
else
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; uint8_t x_254; 
lean_inc(x_51);
x_251 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__39___at_Lean_Meta_getFVarSetToGeneralize___spec__47(x_51, x_208, x_210);
x_252 = lean_ctor_get(x_251, 0);
lean_inc(x_252);
x_253 = lean_ctor_get(x_251, 1);
lean_inc(x_253);
lean_dec(x_251);
x_254 = lean_unbox(x_252);
lean_dec(x_252);
x_232 = x_254;
x_233 = x_253;
goto block_245;
}
}
else
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; uint8_t x_258; 
lean_inc(x_51);
x_255 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__50___at_Lean_Meta_getFVarSetToGeneralize___spec__58(x_51, x_208, x_210);
x_256 = lean_ctor_get(x_255, 0);
lean_inc(x_256);
x_257 = lean_ctor_get(x_255, 1);
lean_inc(x_257);
lean_dec(x_255);
x_258 = lean_unbox(x_256);
lean_dec(x_256);
x_232 = x_258;
x_233 = x_257;
goto block_245;
}
block_231:
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; uint8_t x_220; 
x_216 = lean_ctor_get(x_215, 1);
lean_inc(x_216);
lean_dec(x_215);
x_217 = lean_st_ref_take(x_10, x_213);
x_218 = lean_ctor_get(x_217, 0);
lean_inc(x_218);
x_219 = lean_ctor_get(x_217, 1);
lean_inc(x_219);
lean_dec(x_217);
x_220 = !lean_is_exclusive(x_218);
if (x_220 == 0)
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; 
x_221 = lean_ctor_get(x_218, 0);
lean_dec(x_221);
lean_ctor_set(x_218, 0, x_216);
x_222 = lean_st_ref_set(x_10, x_218, x_219);
x_223 = lean_ctor_get(x_222, 1);
lean_inc(x_223);
lean_dec(x_222);
x_54 = x_214;
x_55 = x_223;
goto block_65;
}
else
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; 
x_224 = lean_ctor_get(x_218, 1);
x_225 = lean_ctor_get(x_218, 2);
x_226 = lean_ctor_get(x_218, 3);
x_227 = lean_ctor_get(x_218, 4);
lean_inc(x_227);
lean_inc(x_226);
lean_inc(x_225);
lean_inc(x_224);
lean_dec(x_218);
x_228 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_228, 0, x_216);
lean_ctor_set(x_228, 1, x_224);
lean_ctor_set(x_228, 2, x_225);
lean_ctor_set(x_228, 3, x_226);
lean_ctor_set(x_228, 4, x_227);
x_229 = lean_st_ref_set(x_10, x_228, x_219);
x_230 = lean_ctor_get(x_229, 1);
lean_inc(x_230);
lean_dec(x_229);
x_54 = x_214;
x_55 = x_230;
goto block_65;
}
}
block_245:
{
if (x_232 == 0)
{
uint8_t x_234; 
x_234 = l_Lean_Expr_hasFVar(x_209);
if (x_234 == 0)
{
uint8_t x_235; 
x_235 = l_Lean_Expr_hasMVar(x_209);
if (x_235 == 0)
{
uint8_t x_236; 
lean_dec(x_209);
x_236 = 0;
x_214 = x_236;
x_215 = x_233;
goto block_231;
}
else
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; uint8_t x_240; 
lean_inc(x_51);
lean_inc(x_3);
x_237 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__23(x_3, x_51, x_209, x_233);
x_238 = lean_ctor_get(x_237, 0);
lean_inc(x_238);
x_239 = lean_ctor_get(x_237, 1);
lean_inc(x_239);
lean_dec(x_237);
x_240 = lean_unbox(x_238);
lean_dec(x_238);
x_214 = x_240;
x_215 = x_239;
goto block_231;
}
}
else
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; uint8_t x_244; 
lean_inc(x_51);
lean_inc(x_3);
x_241 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__31(x_3, x_51, x_209, x_233);
x_242 = lean_ctor_get(x_241, 0);
lean_inc(x_242);
x_243 = lean_ctor_get(x_241, 1);
lean_inc(x_243);
lean_dec(x_241);
x_244 = lean_unbox(x_242);
lean_dec(x_242);
x_214 = x_244;
x_215 = x_243;
goto block_231;
}
}
else
{
lean_dec(x_209);
x_214 = x_232;
x_215 = x_233;
goto block_231;
}
}
}
else
{
lean_object* x_259; lean_object* x_260; uint8_t x_261; lean_object* x_262; uint8_t x_276; lean_object* x_277; lean_object* x_290; lean_object* x_291; lean_object* x_292; uint8_t x_293; 
x_259 = lean_ctor_get(x_210, 0);
x_260 = lean_ctor_get(x_210, 1);
lean_inc(x_260);
lean_inc(x_259);
lean_dec(x_210);
x_290 = lean_ctor_get(x_259, 0);
lean_inc(x_290);
lean_dec(x_259);
x_291 = l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__3;
x_292 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_292, 0, x_291);
lean_ctor_set(x_292, 1, x_290);
x_293 = l_Lean_Expr_hasFVar(x_208);
if (x_293 == 0)
{
uint8_t x_294; 
x_294 = l_Lean_Expr_hasMVar(x_208);
if (x_294 == 0)
{
uint8_t x_295; 
lean_dec(x_208);
x_295 = 0;
x_276 = x_295;
x_277 = x_292;
goto block_289;
}
else
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; uint8_t x_299; 
lean_inc(x_51);
x_296 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__39___at_Lean_Meta_getFVarSetToGeneralize___spec__47(x_51, x_208, x_292);
x_297 = lean_ctor_get(x_296, 0);
lean_inc(x_297);
x_298 = lean_ctor_get(x_296, 1);
lean_inc(x_298);
lean_dec(x_296);
x_299 = lean_unbox(x_297);
lean_dec(x_297);
x_276 = x_299;
x_277 = x_298;
goto block_289;
}
}
else
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; uint8_t x_303; 
lean_inc(x_51);
x_300 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__50___at_Lean_Meta_getFVarSetToGeneralize___spec__58(x_51, x_208, x_292);
x_301 = lean_ctor_get(x_300, 0);
lean_inc(x_301);
x_302 = lean_ctor_get(x_300, 1);
lean_inc(x_302);
lean_dec(x_300);
x_303 = lean_unbox(x_301);
lean_dec(x_301);
x_276 = x_303;
x_277 = x_302;
goto block_289;
}
block_275:
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; 
x_263 = lean_ctor_get(x_262, 1);
lean_inc(x_263);
lean_dec(x_262);
x_264 = lean_st_ref_take(x_10, x_260);
x_265 = lean_ctor_get(x_264, 0);
lean_inc(x_265);
x_266 = lean_ctor_get(x_264, 1);
lean_inc(x_266);
lean_dec(x_264);
x_267 = lean_ctor_get(x_265, 1);
lean_inc(x_267);
x_268 = lean_ctor_get(x_265, 2);
lean_inc(x_268);
x_269 = lean_ctor_get(x_265, 3);
lean_inc(x_269);
x_270 = lean_ctor_get(x_265, 4);
lean_inc(x_270);
if (lean_is_exclusive(x_265)) {
 lean_ctor_release(x_265, 0);
 lean_ctor_release(x_265, 1);
 lean_ctor_release(x_265, 2);
 lean_ctor_release(x_265, 3);
 lean_ctor_release(x_265, 4);
 x_271 = x_265;
} else {
 lean_dec_ref(x_265);
 x_271 = lean_box(0);
}
if (lean_is_scalar(x_271)) {
 x_272 = lean_alloc_ctor(0, 5, 0);
} else {
 x_272 = x_271;
}
lean_ctor_set(x_272, 0, x_263);
lean_ctor_set(x_272, 1, x_267);
lean_ctor_set(x_272, 2, x_268);
lean_ctor_set(x_272, 3, x_269);
lean_ctor_set(x_272, 4, x_270);
x_273 = lean_st_ref_set(x_10, x_272, x_266);
x_274 = lean_ctor_get(x_273, 1);
lean_inc(x_274);
lean_dec(x_273);
x_54 = x_261;
x_55 = x_274;
goto block_65;
}
block_289:
{
if (x_276 == 0)
{
uint8_t x_278; 
x_278 = l_Lean_Expr_hasFVar(x_209);
if (x_278 == 0)
{
uint8_t x_279; 
x_279 = l_Lean_Expr_hasMVar(x_209);
if (x_279 == 0)
{
uint8_t x_280; 
lean_dec(x_209);
x_280 = 0;
x_261 = x_280;
x_262 = x_277;
goto block_275;
}
else
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; uint8_t x_284; 
lean_inc(x_51);
lean_inc(x_3);
x_281 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__23(x_3, x_51, x_209, x_277);
x_282 = lean_ctor_get(x_281, 0);
lean_inc(x_282);
x_283 = lean_ctor_get(x_281, 1);
lean_inc(x_283);
lean_dec(x_281);
x_284 = lean_unbox(x_282);
lean_dec(x_282);
x_261 = x_284;
x_262 = x_283;
goto block_275;
}
}
else
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; uint8_t x_288; 
lean_inc(x_51);
lean_inc(x_3);
x_285 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__31(x_3, x_51, x_209, x_277);
x_286 = lean_ctor_get(x_285, 0);
lean_inc(x_286);
x_287 = lean_ctor_get(x_285, 1);
lean_inc(x_287);
lean_dec(x_285);
x_288 = lean_unbox(x_286);
lean_dec(x_286);
x_261 = x_288;
x_262 = x_287;
goto block_275;
}
}
else
{
lean_dec(x_209);
x_261 = x_276;
x_262 = x_277;
goto block_275;
}
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
lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_ctor_get(x_5, 0);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_6);
x_15 = lean_array_size(x_12);
x_16 = 0;
x_17 = l_Array_forInUnsafe_loop___at_Lean_Meta_getFVarSetToGeneralize___spec__74(x_1, x_2, x_3, x_4, x_13, x_12, x_15, x_16, x_14, x_7, x_8, x_9, x_10, x_11);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_box(0);
x_23 = l_Lean_PersistentArray_forInAux___at_Lean_Meta_getFVarSetToGeneralize___spec__62___lambda__1(x_21, x_22, x_7, x_8, x_9, x_10, x_20);
return x_23;
}
else
{
uint8_t x_24; 
lean_dec(x_18);
x_24 = !lean_is_exclusive(x_17);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_17, 0);
lean_dec(x_25);
x_26 = lean_ctor_get(x_19, 0);
lean_inc(x_26);
lean_dec(x_19);
lean_ctor_set(x_17, 0, x_26);
return x_17;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_17, 1);
lean_inc(x_27);
lean_dec(x_17);
x_28 = lean_ctor_get(x_19, 0);
lean_inc(x_28);
lean_dec(x_19);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; size_t x_33; size_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_30 = lean_ctor_get(x_5, 0);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_6);
x_33 = lean_array_size(x_30);
x_34 = 0;
x_35 = l_Array_forInUnsafe_loop___at_Lean_Meta_getFVarSetToGeneralize___spec__75(x_1, x_2, x_3, x_31, x_30, x_33, x_34, x_32, x_7, x_8, x_9, x_10, x_11);
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
x_41 = l_Lean_PersistentArray_forInAux___at_Lean_Meta_getFVarSetToGeneralize___spec__62___lambda__1(x_39, x_40, x_7, x_8, x_9, x_10, x_38);
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
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; lean_object* x_66; lean_object* x_71; lean_object* x_305; 
x_48 = lean_ctor_get(x_16, 0);
lean_inc(x_48);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 x_49 = x_16;
} else {
 lean_dec_ref(x_16);
 x_49 = lean_box(0);
}
x_50 = lean_ctor_get(x_25, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_25, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_52 = x_25;
} else {
 lean_dec_ref(x_25);
 x_52 = lean_box(0);
}
x_53 = l_Lean_LocalDecl_fvarId(x_48);
x_305 = l_Lean_RBNode_findCore___at_Lean_Meta_mkGeneralizationForbiddenSet_visit___spec__1(x_1, x_53);
if (lean_obj_tag(x_305) == 0)
{
uint8_t x_306; 
x_306 = l_Lean_LocalDecl_isAuxDecl(x_48);
if (x_306 == 0)
{
uint8_t x_307; uint8_t x_308; 
x_307 = l_Lean_LocalDecl_binderInfo(x_48);
x_308 = l_Lean_BinderInfo_isInstImplicit(x_307);
if (x_308 == 0)
{
if (x_2 == 0)
{
lean_object* x_309; 
x_309 = lean_box(0);
x_71 = x_309;
goto block_304;
}
else
{
uint8_t x_310; 
x_310 = l_Lean_LocalDecl_isLet(x_48);
if (x_310 == 0)
{
lean_object* x_311; 
x_311 = lean_box(0);
x_71 = x_311;
goto block_304;
}
else
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; 
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_49);
lean_dec(x_48);
x_312 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_312, 0, x_50);
lean_ctor_set(x_312, 1, x_51);
x_313 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_313, 0, x_312);
x_314 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_314, 0, x_313);
lean_ctor_set(x_314, 1, x_13);
x_27 = x_314;
goto block_43;
}
}
}
else
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; 
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_49);
lean_dec(x_48);
x_315 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_315, 0, x_50);
lean_ctor_set(x_315, 1, x_51);
x_316 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_316, 0, x_315);
x_317 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_317, 0, x_316);
lean_ctor_set(x_317, 1, x_13);
x_27 = x_317;
goto block_43;
}
}
else
{
lean_object* x_318; lean_object* x_319; lean_object* x_320; 
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_49);
lean_dec(x_48);
x_318 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_318, 0, x_50);
lean_ctor_set(x_318, 1, x_51);
x_319 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_319, 0, x_318);
x_320 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_320, 0, x_319);
lean_ctor_set(x_320, 1, x_13);
x_27 = x_320;
goto block_43;
}
}
else
{
uint8_t x_321; 
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_49);
lean_dec(x_48);
x_321 = !lean_is_exclusive(x_305);
if (x_321 == 0)
{
lean_object* x_322; lean_object* x_323; lean_object* x_324; 
x_322 = lean_ctor_get(x_305, 0);
lean_dec(x_322);
x_323 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_323, 0, x_50);
lean_ctor_set(x_323, 1, x_51);
lean_ctor_set(x_305, 0, x_323);
x_324 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_324, 0, x_305);
lean_ctor_set(x_324, 1, x_13);
x_27 = x_324;
goto block_43;
}
else
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; 
lean_dec(x_305);
x_325 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_325, 0, x_50);
lean_ctor_set(x_325, 1, x_51);
x_326 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_326, 0, x_325);
x_327 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_327, 0, x_326);
lean_ctor_set(x_327, 1, x_13);
x_27 = x_327;
goto block_43;
}
}
block_65:
{
if (x_54 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_53);
if (lean_is_scalar(x_52)) {
 x_56 = lean_alloc_ctor(0, 2, 0);
} else {
 x_56 = x_52;
}
lean_ctor_set(x_56, 0, x_50);
lean_ctor_set(x_56, 1, x_51);
if (lean_is_scalar(x_49)) {
 x_57 = lean_alloc_ctor(1, 1, 0);
} else {
 x_57 = x_49;
}
lean_ctor_set(x_57, 0, x_56);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_55);
x_27 = x_58;
goto block_43;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_59 = lean_box(0);
lean_inc(x_53);
x_60 = l_Lean_RBNode_insert___at_Lean_FVarIdSet_insert___spec__1(x_50, x_53, x_59);
x_61 = l_Lean_RBNode_insert___at_Lean_FVarIdSet_insert___spec__1(x_51, x_53, x_59);
if (lean_is_scalar(x_52)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_52;
}
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
if (lean_is_scalar(x_49)) {
 x_63 = lean_alloc_ctor(1, 1, 0);
} else {
 x_63 = x_49;
}
lean_ctor_set(x_63, 0, x_62);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_55);
x_27 = x_64;
goto block_43;
}
}
block_70:
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = lean_unbox(x_67);
lean_dec(x_67);
x_54 = x_69;
x_55 = x_68;
goto block_65;
}
block_304:
{
lean_dec(x_71);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_72 = lean_ctor_get(x_48, 3);
lean_inc(x_72);
lean_dec(x_48);
x_73 = lean_st_ref_get(x_10, x_13);
x_74 = !lean_is_exclusive(x_73);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
x_75 = lean_ctor_get(x_73, 0);
x_76 = lean_ctor_get(x_73, 1);
x_77 = lean_ctor_get(x_75, 0);
lean_inc(x_77);
lean_dec(x_75);
x_78 = l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__3;
lean_inc(x_77);
lean_ctor_set(x_73, 1, x_77);
lean_ctor_set(x_73, 0, x_78);
x_79 = l_Lean_Expr_hasFVar(x_72);
if (x_79 == 0)
{
uint8_t x_80; 
x_80 = l_Lean_Expr_hasMVar(x_72);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; 
lean_dec(x_73);
lean_dec(x_72);
x_81 = lean_st_ref_take(x_10, x_76);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
x_84 = !lean_is_exclusive(x_82);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_85 = lean_ctor_get(x_82, 0);
lean_dec(x_85);
lean_ctor_set(x_82, 0, x_77);
x_86 = lean_st_ref_set(x_10, x_82, x_83);
x_87 = !lean_is_exclusive(x_86);
if (x_87 == 0)
{
lean_object* x_88; uint8_t x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_86, 0);
lean_dec(x_88);
x_89 = 0;
x_90 = lean_box(x_89);
lean_ctor_set(x_86, 0, x_90);
x_66 = x_86;
goto block_70;
}
else
{
lean_object* x_91; uint8_t x_92; lean_object* x_93; lean_object* x_94; 
x_91 = lean_ctor_get(x_86, 1);
lean_inc(x_91);
lean_dec(x_86);
x_92 = 0;
x_93 = lean_box(x_92);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_91);
x_66 = x_94;
goto block_70;
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; lean_object* x_104; lean_object* x_105; 
x_95 = lean_ctor_get(x_82, 1);
x_96 = lean_ctor_get(x_82, 2);
x_97 = lean_ctor_get(x_82, 3);
x_98 = lean_ctor_get(x_82, 4);
lean_inc(x_98);
lean_inc(x_97);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_82);
x_99 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_99, 0, x_77);
lean_ctor_set(x_99, 1, x_95);
lean_ctor_set(x_99, 2, x_96);
lean_ctor_set(x_99, 3, x_97);
lean_ctor_set(x_99, 4, x_98);
x_100 = lean_st_ref_set(x_10, x_99, x_83);
x_101 = lean_ctor_get(x_100, 1);
lean_inc(x_101);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 lean_ctor_release(x_100, 1);
 x_102 = x_100;
} else {
 lean_dec_ref(x_100);
 x_102 = lean_box(0);
}
x_103 = 0;
x_104 = lean_box(x_103);
if (lean_is_scalar(x_102)) {
 x_105 = lean_alloc_ctor(0, 2, 0);
} else {
 x_105 = x_102;
}
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_101);
x_66 = x_105;
goto block_70;
}
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; 
lean_dec(x_77);
lean_inc(x_51);
x_106 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__1___at_Lean_Meta_getFVarSetToGeneralize___spec__9(x_51, x_72, x_73);
x_107 = lean_ctor_get(x_106, 1);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 0);
lean_inc(x_108);
lean_dec(x_106);
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
lean_dec(x_107);
x_110 = lean_st_ref_take(x_10, x_76);
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_110, 1);
lean_inc(x_112);
lean_dec(x_110);
x_113 = !lean_is_exclusive(x_111);
if (x_113 == 0)
{
lean_object* x_114; lean_object* x_115; uint8_t x_116; 
x_114 = lean_ctor_get(x_111, 0);
lean_dec(x_114);
lean_ctor_set(x_111, 0, x_109);
x_115 = lean_st_ref_set(x_10, x_111, x_112);
x_116 = !lean_is_exclusive(x_115);
if (x_116 == 0)
{
lean_object* x_117; 
x_117 = lean_ctor_get(x_115, 0);
lean_dec(x_117);
lean_ctor_set(x_115, 0, x_108);
x_66 = x_115;
goto block_70;
}
else
{
lean_object* x_118; lean_object* x_119; 
x_118 = lean_ctor_get(x_115, 1);
lean_inc(x_118);
lean_dec(x_115);
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_108);
lean_ctor_set(x_119, 1, x_118);
x_66 = x_119;
goto block_70;
}
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_120 = lean_ctor_get(x_111, 1);
x_121 = lean_ctor_get(x_111, 2);
x_122 = lean_ctor_get(x_111, 3);
x_123 = lean_ctor_get(x_111, 4);
lean_inc(x_123);
lean_inc(x_122);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_111);
x_124 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_124, 0, x_109);
lean_ctor_set(x_124, 1, x_120);
lean_ctor_set(x_124, 2, x_121);
lean_ctor_set(x_124, 3, x_122);
lean_ctor_set(x_124, 4, x_123);
x_125 = lean_st_ref_set(x_10, x_124, x_112);
x_126 = lean_ctor_get(x_125, 1);
lean_inc(x_126);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 lean_ctor_release(x_125, 1);
 x_127 = x_125;
} else {
 lean_dec_ref(x_125);
 x_127 = lean_box(0);
}
if (lean_is_scalar(x_127)) {
 x_128 = lean_alloc_ctor(0, 2, 0);
} else {
 x_128 = x_127;
}
lean_ctor_set(x_128, 0, x_108);
lean_ctor_set(x_128, 1, x_126);
x_66 = x_128;
goto block_70;
}
}
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; uint8_t x_136; 
lean_dec(x_77);
lean_inc(x_51);
x_129 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__12___at_Lean_Meta_getFVarSetToGeneralize___spec__20(x_51, x_72, x_73);
x_130 = lean_ctor_get(x_129, 1);
lean_inc(x_130);
x_131 = lean_ctor_get(x_129, 0);
lean_inc(x_131);
lean_dec(x_129);
x_132 = lean_ctor_get(x_130, 1);
lean_inc(x_132);
lean_dec(x_130);
x_133 = lean_st_ref_take(x_10, x_76);
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_133, 1);
lean_inc(x_135);
lean_dec(x_133);
x_136 = !lean_is_exclusive(x_134);
if (x_136 == 0)
{
lean_object* x_137; lean_object* x_138; uint8_t x_139; 
x_137 = lean_ctor_get(x_134, 0);
lean_dec(x_137);
lean_ctor_set(x_134, 0, x_132);
x_138 = lean_st_ref_set(x_10, x_134, x_135);
x_139 = !lean_is_exclusive(x_138);
if (x_139 == 0)
{
lean_object* x_140; 
x_140 = lean_ctor_get(x_138, 0);
lean_dec(x_140);
lean_ctor_set(x_138, 0, x_131);
x_66 = x_138;
goto block_70;
}
else
{
lean_object* x_141; lean_object* x_142; 
x_141 = lean_ctor_get(x_138, 1);
lean_inc(x_141);
lean_dec(x_138);
x_142 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_142, 0, x_131);
lean_ctor_set(x_142, 1, x_141);
x_66 = x_142;
goto block_70;
}
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_143 = lean_ctor_get(x_134, 1);
x_144 = lean_ctor_get(x_134, 2);
x_145 = lean_ctor_get(x_134, 3);
x_146 = lean_ctor_get(x_134, 4);
lean_inc(x_146);
lean_inc(x_145);
lean_inc(x_144);
lean_inc(x_143);
lean_dec(x_134);
x_147 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_147, 0, x_132);
lean_ctor_set(x_147, 1, x_143);
lean_ctor_set(x_147, 2, x_144);
lean_ctor_set(x_147, 3, x_145);
lean_ctor_set(x_147, 4, x_146);
x_148 = lean_st_ref_set(x_10, x_147, x_135);
x_149 = lean_ctor_get(x_148, 1);
lean_inc(x_149);
if (lean_is_exclusive(x_148)) {
 lean_ctor_release(x_148, 0);
 lean_ctor_release(x_148, 1);
 x_150 = x_148;
} else {
 lean_dec_ref(x_148);
 x_150 = lean_box(0);
}
if (lean_is_scalar(x_150)) {
 x_151 = lean_alloc_ctor(0, 2, 0);
} else {
 x_151 = x_150;
}
lean_ctor_set(x_151, 0, x_131);
lean_ctor_set(x_151, 1, x_149);
x_66 = x_151;
goto block_70;
}
}
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; uint8_t x_157; 
x_152 = lean_ctor_get(x_73, 0);
x_153 = lean_ctor_get(x_73, 1);
lean_inc(x_153);
lean_inc(x_152);
lean_dec(x_73);
x_154 = lean_ctor_get(x_152, 0);
lean_inc(x_154);
lean_dec(x_152);
x_155 = l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__3;
lean_inc(x_154);
x_156 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_156, 0, x_155);
lean_ctor_set(x_156, 1, x_154);
x_157 = l_Lean_Expr_hasFVar(x_72);
if (x_157 == 0)
{
uint8_t x_158; 
x_158 = l_Lean_Expr_hasMVar(x_72);
if (x_158 == 0)
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; uint8_t x_171; lean_object* x_172; lean_object* x_173; 
lean_dec(x_156);
lean_dec(x_72);
x_159 = lean_st_ref_take(x_10, x_153);
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_159, 1);
lean_inc(x_161);
lean_dec(x_159);
x_162 = lean_ctor_get(x_160, 1);
lean_inc(x_162);
x_163 = lean_ctor_get(x_160, 2);
lean_inc(x_163);
x_164 = lean_ctor_get(x_160, 3);
lean_inc(x_164);
x_165 = lean_ctor_get(x_160, 4);
lean_inc(x_165);
if (lean_is_exclusive(x_160)) {
 lean_ctor_release(x_160, 0);
 lean_ctor_release(x_160, 1);
 lean_ctor_release(x_160, 2);
 lean_ctor_release(x_160, 3);
 lean_ctor_release(x_160, 4);
 x_166 = x_160;
} else {
 lean_dec_ref(x_160);
 x_166 = lean_box(0);
}
if (lean_is_scalar(x_166)) {
 x_167 = lean_alloc_ctor(0, 5, 0);
} else {
 x_167 = x_166;
}
lean_ctor_set(x_167, 0, x_154);
lean_ctor_set(x_167, 1, x_162);
lean_ctor_set(x_167, 2, x_163);
lean_ctor_set(x_167, 3, x_164);
lean_ctor_set(x_167, 4, x_165);
x_168 = lean_st_ref_set(x_10, x_167, x_161);
x_169 = lean_ctor_get(x_168, 1);
lean_inc(x_169);
if (lean_is_exclusive(x_168)) {
 lean_ctor_release(x_168, 0);
 lean_ctor_release(x_168, 1);
 x_170 = x_168;
} else {
 lean_dec_ref(x_168);
 x_170 = lean_box(0);
}
x_171 = 0;
x_172 = lean_box(x_171);
if (lean_is_scalar(x_170)) {
 x_173 = lean_alloc_ctor(0, 2, 0);
} else {
 x_173 = x_170;
}
lean_ctor_set(x_173, 0, x_172);
lean_ctor_set(x_173, 1, x_169);
x_66 = x_173;
goto block_70;
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
lean_dec(x_154);
lean_inc(x_51);
x_174 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__1___at_Lean_Meta_getFVarSetToGeneralize___spec__9(x_51, x_72, x_156);
x_175 = lean_ctor_get(x_174, 1);
lean_inc(x_175);
x_176 = lean_ctor_get(x_174, 0);
lean_inc(x_176);
lean_dec(x_174);
x_177 = lean_ctor_get(x_175, 1);
lean_inc(x_177);
lean_dec(x_175);
x_178 = lean_st_ref_take(x_10, x_153);
x_179 = lean_ctor_get(x_178, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_178, 1);
lean_inc(x_180);
lean_dec(x_178);
x_181 = lean_ctor_get(x_179, 1);
lean_inc(x_181);
x_182 = lean_ctor_get(x_179, 2);
lean_inc(x_182);
x_183 = lean_ctor_get(x_179, 3);
lean_inc(x_183);
x_184 = lean_ctor_get(x_179, 4);
lean_inc(x_184);
if (lean_is_exclusive(x_179)) {
 lean_ctor_release(x_179, 0);
 lean_ctor_release(x_179, 1);
 lean_ctor_release(x_179, 2);
 lean_ctor_release(x_179, 3);
 lean_ctor_release(x_179, 4);
 x_185 = x_179;
} else {
 lean_dec_ref(x_179);
 x_185 = lean_box(0);
}
if (lean_is_scalar(x_185)) {
 x_186 = lean_alloc_ctor(0, 5, 0);
} else {
 x_186 = x_185;
}
lean_ctor_set(x_186, 0, x_177);
lean_ctor_set(x_186, 1, x_181);
lean_ctor_set(x_186, 2, x_182);
lean_ctor_set(x_186, 3, x_183);
lean_ctor_set(x_186, 4, x_184);
x_187 = lean_st_ref_set(x_10, x_186, x_180);
x_188 = lean_ctor_get(x_187, 1);
lean_inc(x_188);
if (lean_is_exclusive(x_187)) {
 lean_ctor_release(x_187, 0);
 lean_ctor_release(x_187, 1);
 x_189 = x_187;
} else {
 lean_dec_ref(x_187);
 x_189 = lean_box(0);
}
if (lean_is_scalar(x_189)) {
 x_190 = lean_alloc_ctor(0, 2, 0);
} else {
 x_190 = x_189;
}
lean_ctor_set(x_190, 0, x_176);
lean_ctor_set(x_190, 1, x_188);
x_66 = x_190;
goto block_70;
}
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; 
lean_dec(x_154);
lean_inc(x_51);
x_191 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__12___at_Lean_Meta_getFVarSetToGeneralize___spec__20(x_51, x_72, x_156);
x_192 = lean_ctor_get(x_191, 1);
lean_inc(x_192);
x_193 = lean_ctor_get(x_191, 0);
lean_inc(x_193);
lean_dec(x_191);
x_194 = lean_ctor_get(x_192, 1);
lean_inc(x_194);
lean_dec(x_192);
x_195 = lean_st_ref_take(x_10, x_153);
x_196 = lean_ctor_get(x_195, 0);
lean_inc(x_196);
x_197 = lean_ctor_get(x_195, 1);
lean_inc(x_197);
lean_dec(x_195);
x_198 = lean_ctor_get(x_196, 1);
lean_inc(x_198);
x_199 = lean_ctor_get(x_196, 2);
lean_inc(x_199);
x_200 = lean_ctor_get(x_196, 3);
lean_inc(x_200);
x_201 = lean_ctor_get(x_196, 4);
lean_inc(x_201);
if (lean_is_exclusive(x_196)) {
 lean_ctor_release(x_196, 0);
 lean_ctor_release(x_196, 1);
 lean_ctor_release(x_196, 2);
 lean_ctor_release(x_196, 3);
 lean_ctor_release(x_196, 4);
 x_202 = x_196;
} else {
 lean_dec_ref(x_196);
 x_202 = lean_box(0);
}
if (lean_is_scalar(x_202)) {
 x_203 = lean_alloc_ctor(0, 5, 0);
} else {
 x_203 = x_202;
}
lean_ctor_set(x_203, 0, x_194);
lean_ctor_set(x_203, 1, x_198);
lean_ctor_set(x_203, 2, x_199);
lean_ctor_set(x_203, 3, x_200);
lean_ctor_set(x_203, 4, x_201);
x_204 = lean_st_ref_set(x_10, x_203, x_197);
x_205 = lean_ctor_get(x_204, 1);
lean_inc(x_205);
if (lean_is_exclusive(x_204)) {
 lean_ctor_release(x_204, 0);
 lean_ctor_release(x_204, 1);
 x_206 = x_204;
} else {
 lean_dec_ref(x_204);
 x_206 = lean_box(0);
}
if (lean_is_scalar(x_206)) {
 x_207 = lean_alloc_ctor(0, 2, 0);
} else {
 x_207 = x_206;
}
lean_ctor_set(x_207, 0, x_193);
lean_ctor_set(x_207, 1, x_205);
x_66 = x_207;
goto block_70;
}
}
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; uint8_t x_211; 
x_208 = lean_ctor_get(x_48, 3);
lean_inc(x_208);
x_209 = lean_ctor_get(x_48, 4);
lean_inc(x_209);
lean_dec(x_48);
x_210 = lean_st_ref_get(x_10, x_13);
x_211 = !lean_is_exclusive(x_210);
if (x_211 == 0)
{
lean_object* x_212; lean_object* x_213; uint8_t x_214; lean_object* x_215; uint8_t x_232; lean_object* x_233; lean_object* x_246; lean_object* x_247; uint8_t x_248; 
x_212 = lean_ctor_get(x_210, 0);
x_213 = lean_ctor_get(x_210, 1);
x_246 = lean_ctor_get(x_212, 0);
lean_inc(x_246);
lean_dec(x_212);
x_247 = l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__3;
lean_ctor_set(x_210, 1, x_246);
lean_ctor_set(x_210, 0, x_247);
x_248 = l_Lean_Expr_hasFVar(x_208);
if (x_248 == 0)
{
uint8_t x_249; 
x_249 = l_Lean_Expr_hasMVar(x_208);
if (x_249 == 0)
{
uint8_t x_250; 
lean_dec(x_208);
x_250 = 0;
x_232 = x_250;
x_233 = x_210;
goto block_245;
}
else
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; uint8_t x_254; 
lean_inc(x_51);
x_251 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__39___at_Lean_Meta_getFVarSetToGeneralize___spec__47(x_51, x_208, x_210);
x_252 = lean_ctor_get(x_251, 0);
lean_inc(x_252);
x_253 = lean_ctor_get(x_251, 1);
lean_inc(x_253);
lean_dec(x_251);
x_254 = lean_unbox(x_252);
lean_dec(x_252);
x_232 = x_254;
x_233 = x_253;
goto block_245;
}
}
else
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; uint8_t x_258; 
lean_inc(x_51);
x_255 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__50___at_Lean_Meta_getFVarSetToGeneralize___spec__58(x_51, x_208, x_210);
x_256 = lean_ctor_get(x_255, 0);
lean_inc(x_256);
x_257 = lean_ctor_get(x_255, 1);
lean_inc(x_257);
lean_dec(x_255);
x_258 = lean_unbox(x_256);
lean_dec(x_256);
x_232 = x_258;
x_233 = x_257;
goto block_245;
}
block_231:
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; uint8_t x_220; 
x_216 = lean_ctor_get(x_215, 1);
lean_inc(x_216);
lean_dec(x_215);
x_217 = lean_st_ref_take(x_10, x_213);
x_218 = lean_ctor_get(x_217, 0);
lean_inc(x_218);
x_219 = lean_ctor_get(x_217, 1);
lean_inc(x_219);
lean_dec(x_217);
x_220 = !lean_is_exclusive(x_218);
if (x_220 == 0)
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; 
x_221 = lean_ctor_get(x_218, 0);
lean_dec(x_221);
lean_ctor_set(x_218, 0, x_216);
x_222 = lean_st_ref_set(x_10, x_218, x_219);
x_223 = lean_ctor_get(x_222, 1);
lean_inc(x_223);
lean_dec(x_222);
x_54 = x_214;
x_55 = x_223;
goto block_65;
}
else
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; 
x_224 = lean_ctor_get(x_218, 1);
x_225 = lean_ctor_get(x_218, 2);
x_226 = lean_ctor_get(x_218, 3);
x_227 = lean_ctor_get(x_218, 4);
lean_inc(x_227);
lean_inc(x_226);
lean_inc(x_225);
lean_inc(x_224);
lean_dec(x_218);
x_228 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_228, 0, x_216);
lean_ctor_set(x_228, 1, x_224);
lean_ctor_set(x_228, 2, x_225);
lean_ctor_set(x_228, 3, x_226);
lean_ctor_set(x_228, 4, x_227);
x_229 = lean_st_ref_set(x_10, x_228, x_219);
x_230 = lean_ctor_get(x_229, 1);
lean_inc(x_230);
lean_dec(x_229);
x_54 = x_214;
x_55 = x_230;
goto block_65;
}
}
block_245:
{
if (x_232 == 0)
{
uint8_t x_234; 
x_234 = l_Lean_Expr_hasFVar(x_209);
if (x_234 == 0)
{
uint8_t x_235; 
x_235 = l_Lean_Expr_hasMVar(x_209);
if (x_235 == 0)
{
uint8_t x_236; 
lean_dec(x_209);
x_236 = 0;
x_214 = x_236;
x_215 = x_233;
goto block_231;
}
else
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; uint8_t x_240; 
lean_inc(x_51);
lean_inc(x_3);
x_237 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__23(x_3, x_51, x_209, x_233);
x_238 = lean_ctor_get(x_237, 0);
lean_inc(x_238);
x_239 = lean_ctor_get(x_237, 1);
lean_inc(x_239);
lean_dec(x_237);
x_240 = lean_unbox(x_238);
lean_dec(x_238);
x_214 = x_240;
x_215 = x_239;
goto block_231;
}
}
else
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; uint8_t x_244; 
lean_inc(x_51);
lean_inc(x_3);
x_241 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__31(x_3, x_51, x_209, x_233);
x_242 = lean_ctor_get(x_241, 0);
lean_inc(x_242);
x_243 = lean_ctor_get(x_241, 1);
lean_inc(x_243);
lean_dec(x_241);
x_244 = lean_unbox(x_242);
lean_dec(x_242);
x_214 = x_244;
x_215 = x_243;
goto block_231;
}
}
else
{
lean_dec(x_209);
x_214 = x_232;
x_215 = x_233;
goto block_231;
}
}
}
else
{
lean_object* x_259; lean_object* x_260; uint8_t x_261; lean_object* x_262; uint8_t x_276; lean_object* x_277; lean_object* x_290; lean_object* x_291; lean_object* x_292; uint8_t x_293; 
x_259 = lean_ctor_get(x_210, 0);
x_260 = lean_ctor_get(x_210, 1);
lean_inc(x_260);
lean_inc(x_259);
lean_dec(x_210);
x_290 = lean_ctor_get(x_259, 0);
lean_inc(x_290);
lean_dec(x_259);
x_291 = l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__3;
x_292 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_292, 0, x_291);
lean_ctor_set(x_292, 1, x_290);
x_293 = l_Lean_Expr_hasFVar(x_208);
if (x_293 == 0)
{
uint8_t x_294; 
x_294 = l_Lean_Expr_hasMVar(x_208);
if (x_294 == 0)
{
uint8_t x_295; 
lean_dec(x_208);
x_295 = 0;
x_276 = x_295;
x_277 = x_292;
goto block_289;
}
else
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; uint8_t x_299; 
lean_inc(x_51);
x_296 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__39___at_Lean_Meta_getFVarSetToGeneralize___spec__47(x_51, x_208, x_292);
x_297 = lean_ctor_get(x_296, 0);
lean_inc(x_297);
x_298 = lean_ctor_get(x_296, 1);
lean_inc(x_298);
lean_dec(x_296);
x_299 = lean_unbox(x_297);
lean_dec(x_297);
x_276 = x_299;
x_277 = x_298;
goto block_289;
}
}
else
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; uint8_t x_303; 
lean_inc(x_51);
x_300 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__50___at_Lean_Meta_getFVarSetToGeneralize___spec__58(x_51, x_208, x_292);
x_301 = lean_ctor_get(x_300, 0);
lean_inc(x_301);
x_302 = lean_ctor_get(x_300, 1);
lean_inc(x_302);
lean_dec(x_300);
x_303 = lean_unbox(x_301);
lean_dec(x_301);
x_276 = x_303;
x_277 = x_302;
goto block_289;
}
block_275:
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; 
x_263 = lean_ctor_get(x_262, 1);
lean_inc(x_263);
lean_dec(x_262);
x_264 = lean_st_ref_take(x_10, x_260);
x_265 = lean_ctor_get(x_264, 0);
lean_inc(x_265);
x_266 = lean_ctor_get(x_264, 1);
lean_inc(x_266);
lean_dec(x_264);
x_267 = lean_ctor_get(x_265, 1);
lean_inc(x_267);
x_268 = lean_ctor_get(x_265, 2);
lean_inc(x_268);
x_269 = lean_ctor_get(x_265, 3);
lean_inc(x_269);
x_270 = lean_ctor_get(x_265, 4);
lean_inc(x_270);
if (lean_is_exclusive(x_265)) {
 lean_ctor_release(x_265, 0);
 lean_ctor_release(x_265, 1);
 lean_ctor_release(x_265, 2);
 lean_ctor_release(x_265, 3);
 lean_ctor_release(x_265, 4);
 x_271 = x_265;
} else {
 lean_dec_ref(x_265);
 x_271 = lean_box(0);
}
if (lean_is_scalar(x_271)) {
 x_272 = lean_alloc_ctor(0, 5, 0);
} else {
 x_272 = x_271;
}
lean_ctor_set(x_272, 0, x_263);
lean_ctor_set(x_272, 1, x_267);
lean_ctor_set(x_272, 2, x_268);
lean_ctor_set(x_272, 3, x_269);
lean_ctor_set(x_272, 4, x_270);
x_273 = lean_st_ref_set(x_10, x_272, x_266);
x_274 = lean_ctor_get(x_273, 1);
lean_inc(x_274);
lean_dec(x_273);
x_54 = x_261;
x_55 = x_274;
goto block_65;
}
block_289:
{
if (x_276 == 0)
{
uint8_t x_278; 
x_278 = l_Lean_Expr_hasFVar(x_209);
if (x_278 == 0)
{
uint8_t x_279; 
x_279 = l_Lean_Expr_hasMVar(x_209);
if (x_279 == 0)
{
uint8_t x_280; 
lean_dec(x_209);
x_280 = 0;
x_261 = x_280;
x_262 = x_277;
goto block_275;
}
else
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; uint8_t x_284; 
lean_inc(x_51);
lean_inc(x_3);
x_281 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__23(x_3, x_51, x_209, x_277);
x_282 = lean_ctor_get(x_281, 0);
lean_inc(x_282);
x_283 = lean_ctor_get(x_281, 1);
lean_inc(x_283);
lean_dec(x_281);
x_284 = lean_unbox(x_282);
lean_dec(x_282);
x_261 = x_284;
x_262 = x_283;
goto block_275;
}
}
else
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; uint8_t x_288; 
lean_inc(x_51);
lean_inc(x_3);
x_285 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at_Lean_Meta_getFVarSetToGeneralize___spec__31(x_3, x_51, x_209, x_277);
x_286 = lean_ctor_get(x_285, 0);
lean_inc(x_286);
x_287 = lean_ctor_get(x_285, 1);
lean_inc(x_287);
lean_dec(x_285);
x_288 = lean_unbox(x_286);
lean_dec(x_286);
x_261 = x_288;
x_262 = x_287;
goto block_275;
}
}
else
{
lean_dec(x_209);
x_261 = x_276;
x_262 = x_277;
goto block_275;
}
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
lean_inc(x_5);
lean_inc(x_3);
x_12 = l_Lean_PersistentArray_forInAux___at_Lean_Meta_getFVarSetToGeneralize___spec__73(x_1, x_2, x_3, x_5, x_11, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
lean_dec(x_3);
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
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; size_t x_25; size_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
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
x_25 = lean_array_size(x_22);
x_26 = 0;
x_27 = l_Array_forInUnsafe_loop___at_Lean_Meta_getFVarSetToGeneralize___spec__76(x_1, x_2, x_3, x_23, x_22, x_25, x_26, x_24, x_6, x_7, x_8, x_9, x_20);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_27);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_27, 0);
lean_dec(x_31);
x_32 = lean_ctor_get(x_28, 1);
lean_inc(x_32);
lean_dec(x_28);
lean_ctor_set(x_27, 0, x_32);
return x_27;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_27, 1);
lean_inc(x_33);
lean_dec(x_27);
x_34 = lean_ctor_get(x_28, 1);
lean_inc(x_34);
lean_dec(x_28);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
return x_35;
}
}
else
{
uint8_t x_36; 
lean_dec(x_28);
x_36 = !lean_is_exclusive(x_27);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_27, 0);
lean_dec(x_37);
x_38 = lean_ctor_get(x_29, 0);
lean_inc(x_38);
lean_dec(x_29);
lean_ctor_set(x_27, 0, x_38);
return x_27;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_27, 1);
lean_inc(x_39);
lean_dec(x_27);
x_40 = lean_ctor_get(x_29, 0);
lean_inc(x_40);
lean_dec(x_29);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
return x_41;
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
x_14 = lean_ctor_get(x_13, 1);
x_15 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at_Lean_Meta_getFVarSetToGeneralize___spec__2___at_Lean_Meta_getFVarSetToGeneralize___spec__10___closed__1;
x_16 = l_Lean_Meta_getFVarSetToGeneralize___closed__1;
x_17 = l_Lean_PersistentArray_forIn___at_Lean_Meta_getFVarSetToGeneralize___spec__61(x_2, x_3, x_15, x_14, x_16, x_4, x_5, x_6, x_7, x_8);
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
x_26 = lean_ctor_get(x_25, 1);
x_27 = lean_nat_dec_le(x_10, x_10);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
lean_dec(x_10);
x_28 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at_Lean_Meta_getFVarSetToGeneralize___spec__2___at_Lean_Meta_getFVarSetToGeneralize___spec__10___closed__1;
x_29 = l_Lean_Meta_getFVarSetToGeneralize___closed__1;
x_30 = l_Lean_PersistentArray_forIn___at_Lean_Meta_getFVarSetToGeneralize___spec__66(x_2, x_3, x_28, x_26, x_29, x_4, x_5, x_6, x_7, x_8);
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
lean_dec(x_3);
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
lean_dec(x_3);
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
lean_dec(x_3);
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
lean_dec(x_3);
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
lean_dec(x_3);
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
lean_dec(x_3);
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
lean_dec(x_3);
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
lean_dec(x_3);
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
lean_dec(x_3);
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
lean_dec(x_3);
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
lean_dec(x_3);
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
lean_dec(x_3);
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
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
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
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
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
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
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
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
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
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
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
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
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
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
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
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
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
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
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
lean_dec(x_4);
lean_dec(x_2);
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
x_2 = l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__4;
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
x_12 = l_Lean_Meta_getFVarSetToGeneralize(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_11);
lean_dec(x_10);
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
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_CollectFVars(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_GeneralizeVars(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
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
l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__4 = _init_l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__4();
lean_mark_persistent(l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__4);
l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__5 = _init_l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__5();
lean_mark_persistent(l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__5);
l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at_Lean_Meta_getFVarSetToGeneralize___spec__2___at_Lean_Meta_getFVarSetToGeneralize___spec__10___closed__1 = _init_l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at_Lean_Meta_getFVarSetToGeneralize___spec__2___at_Lean_Meta_getFVarSetToGeneralize___spec__10___closed__1();
lean_mark_persistent(l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at_Lean_Meta_getFVarSetToGeneralize___spec__2___at_Lean_Meta_getFVarSetToGeneralize___spec__10___closed__1);
l_Lean_Meta_getFVarSetToGeneralize___closed__1 = _init_l_Lean_Meta_getFVarSetToGeneralize___closed__1();
lean_mark_persistent(l_Lean_Meta_getFVarSetToGeneralize___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
