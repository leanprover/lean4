// Lean compiler output
// Module: Lean.Meta.Constructions.SparseCasesOnEq
// Imports: public import Lean.Meta.Basic import Lean.Meta.Constructions.SparseCasesOn import Lean.Meta.HasNotBit import Lean.Meta.Tactic.Cases import Lean.Meta.Tactic.Refl
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_MVarId_assertExt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_intro1Core(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_FVarSubst_apply(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_note(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addDecl(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_cases(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_refl(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_FVarSubst_get(lean_object*, lean_object*);
lean_object* l_Lean_refutableHasNotBit_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAbsurd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getSparseCasesOnInfoCore(lean_object*, lean_object*);
lean_object* l_Lean_Name_getPrefix(lean_object*);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Lean_Meta_getSparseCasesOnInfo___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Environment_findConstVal_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* l_Lean_Meta_realizeConst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instInhabitedCoreM___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerReservedNameAction(lean_object*);
lean_object* l_Lean_registerReservedNamePredicate(lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instInhabitedMetaM___redArg___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__2___closed__0 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__2___closed__0_value;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__7(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__10___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__10___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__10___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__10(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6_spec__12_spec__16_spec__20___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6_spec__12_spec__16___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6_spec__12___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6_spec__12___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6_spec__12___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6_spec__12_spec__17___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6_spec__12_spec__17___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__9___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "mkSparseCasesOnEq: not refutable "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__9___lam__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__9___lam__0___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__9___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__9___lam__0___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__9___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__9___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__5_spec__8(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__5___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__9___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "Lean.Meta.Constructions.SparseCasesOnEq"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__9___lam__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__9___lam__1___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__9___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 88, .m_capacity = 88, .m_length = 87, .m_data = "_private.Lean.Meta.Constructions.SparseCasesOnEq.0.Lean.Meta.getSparseCasesOnEq.realize"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__9___lam__1___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__9___lam__1___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__9___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 50, .m_capacity = 50, .m_length = 49, .m_data = "assertion violation: s.ctorName.isSome\n          "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__9___lam__1___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__9___lam__1___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__9___lam__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__9___lam__1___closed__3;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__9___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Init.Data.Option.BasicAux"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__9___lam__1___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__9___lam__1___closed__4_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__9___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Option.get!"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__9___lam__1___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__9___lam__1___closed__5_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__9___lam__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "value is none"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__9___lam__1___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__9___lam__1___closed__6_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__9___lam__1___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__9___lam__1___closed__7;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__9___lam__1(uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__9___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "h"};
static const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__0___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(176, 181, 207, 77, 197, 87, 68, 121)}};
static const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__0___boxed(lean_object**);
static const lean_string_object l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "assertion violation: hyps.size = 1\n        "};
static const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__1___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__1___closed__1;
static const lean_string_object l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "mkSparseCasesOnEq: unexpected hyp type "};
static const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__1___closed__2 = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__1___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__1___closed__3;
static const lean_string_object l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__1___closed__4 = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__1___closed__4_value;
static const lean_string_object l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "hasNotBit"};
static const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__1___closed__5 = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__1___closed__5_value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__1___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__1___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(117, 117, 142, 139, 222, 16, 37, 88)}};
static const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__1___closed__6 = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__1___closed__6_value;
static const lean_string_object l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "idx"};
static const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__1___closed__7 = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__1___closed__7_value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(84, 246, 160, 71, 192, 5, 128, 186)}};
static const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__1___closed__8 = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__1___closed__8_value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__1___closed__9 = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__1___closed__9_value;
static const lean_string_object l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hidx"};
static const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__1___closed__10 = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__1___closed__10_value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(133, 25, 203, 189, 219, 140, 152, 16)}};
static const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__1___closed__11 = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__1___closed__11_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__17___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__17___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__0;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__1;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__2;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__3;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__4;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__13;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__14 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__14_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__15;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "A declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "` exists in the private scope of `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__19;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 56, .m_capacity = 56, .m_length = 55, .m_data = "`, which is accessible here through `import all`, but `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__20 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__20_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__21;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 66, .m_capacity = 66, .m_length = 65, .m_data = "` does not export it, so it cannot be accessed in a public scope."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__22 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__22_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__23;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__24 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__24_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__25;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__26 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__26_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__27;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6___redArg___closed__1;
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6___redArg___closed__2 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__1(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "mkSparseCasesOnEq: "};
static const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___closed__0 = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___closed__1;
static const lean_string_object l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = " is not a sparse casesOn combinator"};
static const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___closed__2 = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6_spec__12(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6_spec__12_spec__16(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6_spec__12_spec__17(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6_spec__12_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6_spec__12_spec__16_spec__20(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_getSparseCasesOnEq___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "else_eq"};
static const lean_object* l_Lean_Meta_getSparseCasesOnEq___closed__0 = (const lean_object*)&l_Lean_Meta_getSparseCasesOnEq___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_getSparseCasesOnEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getSparseCasesOnEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_isName(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_isName___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_2164281220____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_2164281220____hygCtx___hyg_2____boxed(lean_object*);
static const lean_closure_object l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_2164281220____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_2164281220____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_2164281220____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_2164281220____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_2164281220____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_isName___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_2164281220____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_2164281220____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_2164281220____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_2164281220____hygCtx___hyg_2____boxed(lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2__spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instInhabitedCoreM___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2__spec__1___closed__0 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2__spec__1___closed__0_value;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2__spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2__spec__0_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_;
static const lean_array_object l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__3_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__3_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__6_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__6_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__7_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__7_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__8_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__8_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__9_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 137, .m_capacity = 137, .m_length = 136, .m_data = "_private.Lean.Meta.Constructions.SparseCasesOnEq.0.Lean.Meta.initFn._@.Lean.Meta.Constructions.SparseCasesOnEq.1213293720._hygCtx._hyg.2"};
static const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__9_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__9_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__10_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "assertion violation: name = name'\n    "};
static const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__10_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__10_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__11_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__11_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2____boxed, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))} };
static const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2__spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2__spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2__spec__0(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__2(lean_object* v_msg_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_){
_start:
{
lean_object* v___f_8_; lean_object* v___x_10753__overap_9_; lean_object* v___x_10_; 
v___f_8_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__2___closed__0));
v___x_10753__overap_9_ = lean_panic_fn_borrowed(v___f_8_, v_msg_2_);
lean_inc(v___y_6_);
lean_inc_ref(v___y_5_);
lean_inc(v___y_4_);
lean_inc_ref(v___y_3_);
v___x_10_ = lean_apply_5(v___x_10753__overap_9_, v___y_3_, v___y_4_, v___y_5_, v___y_6_, lean_box(0));
return v___x_10_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__2___boxed(lean_object* v_msg_11_, lean_object* v___y_12_, lean_object* v___y_13_, lean_object* v___y_14_, lean_object* v___y_15_, lean_object* v___y_16_){
_start:
{
lean_object* v_res_17_; 
v_res_17_ = l_panic___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__2(v_msg_11_, v___y_12_, v___y_13_, v___y_14_, v___y_15_);
lean_dec(v___y_15_);
lean_dec_ref(v___y_14_);
lean_dec(v___y_13_);
lean_dec_ref(v___y_12_);
return v_res_17_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__6___redArg(lean_object* v_mvarId_18_, lean_object* v_x_19_, lean_object* v___y_20_, lean_object* v___y_21_, lean_object* v___y_22_, lean_object* v___y_23_){
_start:
{
lean_object* v___x_25_; 
v___x_25_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_18_, v_x_19_, v___y_20_, v___y_21_, v___y_22_, v___y_23_);
if (lean_obj_tag(v___x_25_) == 0)
{
lean_object* v_a_26_; lean_object* v___x_28_; uint8_t v_isShared_29_; uint8_t v_isSharedCheck_33_; 
v_a_26_ = lean_ctor_get(v___x_25_, 0);
v_isSharedCheck_33_ = !lean_is_exclusive(v___x_25_);
if (v_isSharedCheck_33_ == 0)
{
v___x_28_ = v___x_25_;
v_isShared_29_ = v_isSharedCheck_33_;
goto v_resetjp_27_;
}
else
{
lean_inc(v_a_26_);
lean_dec(v___x_25_);
v___x_28_ = lean_box(0);
v_isShared_29_ = v_isSharedCheck_33_;
goto v_resetjp_27_;
}
v_resetjp_27_:
{
lean_object* v___x_31_; 
if (v_isShared_29_ == 0)
{
v___x_31_ = v___x_28_;
goto v_reusejp_30_;
}
else
{
lean_object* v_reuseFailAlloc_32_; 
v_reuseFailAlloc_32_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_32_, 0, v_a_26_);
v___x_31_ = v_reuseFailAlloc_32_;
goto v_reusejp_30_;
}
v_reusejp_30_:
{
return v___x_31_;
}
}
}
else
{
lean_object* v_a_34_; lean_object* v___x_36_; uint8_t v_isShared_37_; uint8_t v_isSharedCheck_41_; 
v_a_34_ = lean_ctor_get(v___x_25_, 0);
v_isSharedCheck_41_ = !lean_is_exclusive(v___x_25_);
if (v_isSharedCheck_41_ == 0)
{
v___x_36_ = v___x_25_;
v_isShared_37_ = v_isSharedCheck_41_;
goto v_resetjp_35_;
}
else
{
lean_inc(v_a_34_);
lean_dec(v___x_25_);
v___x_36_ = lean_box(0);
v_isShared_37_ = v_isSharedCheck_41_;
goto v_resetjp_35_;
}
v_resetjp_35_:
{
lean_object* v___x_39_; 
if (v_isShared_37_ == 0)
{
v___x_39_ = v___x_36_;
goto v_reusejp_38_;
}
else
{
lean_object* v_reuseFailAlloc_40_; 
v_reuseFailAlloc_40_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_40_, 0, v_a_34_);
v___x_39_ = v_reuseFailAlloc_40_;
goto v_reusejp_38_;
}
v_reusejp_38_:
{
return v___x_39_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__6___redArg___boxed(lean_object* v_mvarId_42_, lean_object* v_x_43_, lean_object* v___y_44_, lean_object* v___y_45_, lean_object* v___y_46_, lean_object* v___y_47_, lean_object* v___y_48_){
_start:
{
lean_object* v_res_49_; 
v_res_49_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__6___redArg(v_mvarId_42_, v_x_43_, v___y_44_, v___y_45_, v___y_46_, v___y_47_);
lean_dec(v___y_47_);
lean_dec_ref(v___y_46_);
lean_dec(v___y_45_);
lean_dec_ref(v___y_44_);
return v_res_49_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__6(lean_object* v_00_u03b1_50_, lean_object* v_mvarId_51_, lean_object* v_x_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_, lean_object* v___y_56_){
_start:
{
lean_object* v___x_58_; 
v___x_58_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__6___redArg(v_mvarId_51_, v_x_52_, v___y_53_, v___y_54_, v___y_55_, v___y_56_);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__6___boxed(lean_object* v_00_u03b1_59_, lean_object* v_mvarId_60_, lean_object* v_x_61_, lean_object* v___y_62_, lean_object* v___y_63_, lean_object* v___y_64_, lean_object* v___y_65_, lean_object* v___y_66_){
_start:
{
lean_object* v_res_67_; 
v_res_67_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__6(v_00_u03b1_59_, v_mvarId_60_, v_x_61_, v___y_62_, v___y_63_, v___y_64_, v___y_65_);
lean_dec(v___y_65_);
lean_dec_ref(v___y_64_);
lean_dec(v___y_63_);
lean_dec_ref(v___y_62_);
return v_res_67_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__7(lean_object* v_msg_68_){
_start:
{
lean_object* v___x_69_; lean_object* v___x_70_; 
v___x_69_ = lean_box(0);
v___x_70_ = lean_panic_fn_borrowed(v___x_69_, v_msg_68_);
return v___x_70_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8___redArg(lean_object* v_e_71_, lean_object* v___y_72_){
_start:
{
uint8_t v___x_74_; 
v___x_74_ = l_Lean_Expr_hasMVar(v_e_71_);
if (v___x_74_ == 0)
{
lean_object* v___x_75_; 
v___x_75_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_75_, 0, v_e_71_);
return v___x_75_;
}
else
{
lean_object* v___x_76_; lean_object* v_mctx_77_; lean_object* v___x_78_; lean_object* v_fst_79_; lean_object* v_snd_80_; lean_object* v___x_81_; lean_object* v_cache_82_; lean_object* v_zetaDeltaFVarIds_83_; lean_object* v_postponed_84_; lean_object* v_diag_85_; lean_object* v___x_87_; uint8_t v_isShared_88_; uint8_t v_isSharedCheck_94_; 
v___x_76_ = lean_st_ref_get(v___y_72_);
v_mctx_77_ = lean_ctor_get(v___x_76_, 0);
lean_inc_ref(v_mctx_77_);
lean_dec(v___x_76_);
v___x_78_ = l_Lean_instantiateMVarsCore(v_mctx_77_, v_e_71_);
v_fst_79_ = lean_ctor_get(v___x_78_, 0);
lean_inc(v_fst_79_);
v_snd_80_ = lean_ctor_get(v___x_78_, 1);
lean_inc(v_snd_80_);
lean_dec_ref(v___x_78_);
v___x_81_ = lean_st_ref_take(v___y_72_);
v_cache_82_ = lean_ctor_get(v___x_81_, 1);
v_zetaDeltaFVarIds_83_ = lean_ctor_get(v___x_81_, 2);
v_postponed_84_ = lean_ctor_get(v___x_81_, 3);
v_diag_85_ = lean_ctor_get(v___x_81_, 4);
v_isSharedCheck_94_ = !lean_is_exclusive(v___x_81_);
if (v_isSharedCheck_94_ == 0)
{
lean_object* v_unused_95_; 
v_unused_95_ = lean_ctor_get(v___x_81_, 0);
lean_dec(v_unused_95_);
v___x_87_ = v___x_81_;
v_isShared_88_ = v_isSharedCheck_94_;
goto v_resetjp_86_;
}
else
{
lean_inc(v_diag_85_);
lean_inc(v_postponed_84_);
lean_inc(v_zetaDeltaFVarIds_83_);
lean_inc(v_cache_82_);
lean_dec(v___x_81_);
v___x_87_ = lean_box(0);
v_isShared_88_ = v_isSharedCheck_94_;
goto v_resetjp_86_;
}
v_resetjp_86_:
{
lean_object* v___x_90_; 
if (v_isShared_88_ == 0)
{
lean_ctor_set(v___x_87_, 0, v_snd_80_);
v___x_90_ = v___x_87_;
goto v_reusejp_89_;
}
else
{
lean_object* v_reuseFailAlloc_93_; 
v_reuseFailAlloc_93_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_93_, 0, v_snd_80_);
lean_ctor_set(v_reuseFailAlloc_93_, 1, v_cache_82_);
lean_ctor_set(v_reuseFailAlloc_93_, 2, v_zetaDeltaFVarIds_83_);
lean_ctor_set(v_reuseFailAlloc_93_, 3, v_postponed_84_);
lean_ctor_set(v_reuseFailAlloc_93_, 4, v_diag_85_);
v___x_90_ = v_reuseFailAlloc_93_;
goto v_reusejp_89_;
}
v_reusejp_89_:
{
lean_object* v___x_91_; lean_object* v___x_92_; 
v___x_91_ = lean_st_ref_put(v___y_72_, v___x_90_);
v___x_92_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_92_, 0, v_fst_79_);
return v___x_92_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8___redArg___boxed(lean_object* v_e_96_, lean_object* v___y_97_, lean_object* v___y_98_){
_start:
{
lean_object* v_res_99_; 
v_res_99_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8___redArg(v_e_96_, v___y_97_);
lean_dec(v___y_97_);
return v_res_99_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8(lean_object* v_e_100_, lean_object* v___y_101_, lean_object* v___y_102_, lean_object* v___y_103_, lean_object* v___y_104_){
_start:
{
lean_object* v___x_106_; 
v___x_106_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8___redArg(v_e_100_, v___y_102_);
return v___x_106_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8___boxed(lean_object* v_e_107_, lean_object* v___y_108_, lean_object* v___y_109_, lean_object* v___y_110_, lean_object* v___y_111_, lean_object* v___y_112_){
_start:
{
lean_object* v_res_113_; 
v_res_113_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8(v_e_107_, v___y_108_, v___y_109_, v___y_110_, v___y_111_);
lean_dec(v___y_111_);
lean_dec_ref(v___y_110_);
lean_dec(v___y_109_);
lean_dec_ref(v___y_108_);
return v_res_113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__10___redArg___lam__0(lean_object* v_k_114_, lean_object* v_b_115_, lean_object* v_c_116_, lean_object* v___y_117_, lean_object* v___y_118_, lean_object* v___y_119_, lean_object* v___y_120_){
_start:
{
lean_object* v___x_122_; 
lean_inc(v___y_120_);
lean_inc_ref(v___y_119_);
lean_inc(v___y_118_);
lean_inc_ref(v___y_117_);
v___x_122_ = lean_apply_7(v_k_114_, v_b_115_, v_c_116_, v___y_117_, v___y_118_, v___y_119_, v___y_120_, lean_box(0));
return v___x_122_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__10___redArg___lam__0___boxed(lean_object* v_k_123_, lean_object* v_b_124_, lean_object* v_c_125_, lean_object* v___y_126_, lean_object* v___y_127_, lean_object* v___y_128_, lean_object* v___y_129_, lean_object* v___y_130_){
_start:
{
lean_object* v_res_131_; 
v_res_131_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__10___redArg___lam__0(v_k_123_, v_b_124_, v_c_125_, v___y_126_, v___y_127_, v___y_128_, v___y_129_);
lean_dec(v___y_129_);
lean_dec_ref(v___y_128_);
lean_dec(v___y_127_);
lean_dec_ref(v___y_126_);
return v_res_131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__10___redArg(lean_object* v_type_132_, lean_object* v_k_133_, uint8_t v_cleanupAnnotations_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_, lean_object* v___y_138_){
_start:
{
lean_object* v___f_140_; uint8_t v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; 
v___f_140_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__10___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_140_, 0, v_k_133_);
v___x_141_ = 0;
v___x_142_ = lean_box(0);
v___x_143_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_141_, v___x_142_, v_type_132_, v___f_140_, v_cleanupAnnotations_134_, v___x_141_, v___y_135_, v___y_136_, v___y_137_, v___y_138_);
if (lean_obj_tag(v___x_143_) == 0)
{
lean_object* v_a_144_; lean_object* v___x_146_; uint8_t v_isShared_147_; uint8_t v_isSharedCheck_151_; 
v_a_144_ = lean_ctor_get(v___x_143_, 0);
v_isSharedCheck_151_ = !lean_is_exclusive(v___x_143_);
if (v_isSharedCheck_151_ == 0)
{
v___x_146_ = v___x_143_;
v_isShared_147_ = v_isSharedCheck_151_;
goto v_resetjp_145_;
}
else
{
lean_inc(v_a_144_);
lean_dec(v___x_143_);
v___x_146_ = lean_box(0);
v_isShared_147_ = v_isSharedCheck_151_;
goto v_resetjp_145_;
}
v_resetjp_145_:
{
lean_object* v___x_149_; 
if (v_isShared_147_ == 0)
{
v___x_149_ = v___x_146_;
goto v_reusejp_148_;
}
else
{
lean_object* v_reuseFailAlloc_150_; 
v_reuseFailAlloc_150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_150_, 0, v_a_144_);
v___x_149_ = v_reuseFailAlloc_150_;
goto v_reusejp_148_;
}
v_reusejp_148_:
{
return v___x_149_;
}
}
}
else
{
lean_object* v_a_152_; lean_object* v___x_154_; uint8_t v_isShared_155_; uint8_t v_isSharedCheck_159_; 
v_a_152_ = lean_ctor_get(v___x_143_, 0);
v_isSharedCheck_159_ = !lean_is_exclusive(v___x_143_);
if (v_isSharedCheck_159_ == 0)
{
v___x_154_ = v___x_143_;
v_isShared_155_ = v_isSharedCheck_159_;
goto v_resetjp_153_;
}
else
{
lean_inc(v_a_152_);
lean_dec(v___x_143_);
v___x_154_ = lean_box(0);
v_isShared_155_ = v_isSharedCheck_159_;
goto v_resetjp_153_;
}
v_resetjp_153_:
{
lean_object* v___x_157_; 
if (v_isShared_155_ == 0)
{
v___x_157_ = v___x_154_;
goto v_reusejp_156_;
}
else
{
lean_object* v_reuseFailAlloc_158_; 
v_reuseFailAlloc_158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_158_, 0, v_a_152_);
v___x_157_ = v_reuseFailAlloc_158_;
goto v_reusejp_156_;
}
v_reusejp_156_:
{
return v___x_157_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__10___redArg___boxed(lean_object* v_type_160_, lean_object* v_k_161_, lean_object* v_cleanupAnnotations_162_, lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_, lean_object* v___y_167_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_168_; lean_object* v_res_169_; 
v_cleanupAnnotations_boxed_168_ = lean_unbox(v_cleanupAnnotations_162_);
v_res_169_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__10___redArg(v_type_160_, v_k_161_, v_cleanupAnnotations_boxed_168_, v___y_163_, v___y_164_, v___y_165_, v___y_166_);
lean_dec(v___y_166_);
lean_dec_ref(v___y_165_);
lean_dec(v___y_164_);
lean_dec_ref(v___y_163_);
return v_res_169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__10(lean_object* v_00_u03b1_170_, lean_object* v_type_171_, lean_object* v_k_172_, uint8_t v_cleanupAnnotations_173_, lean_object* v___y_174_, lean_object* v___y_175_, lean_object* v___y_176_, lean_object* v___y_177_){
_start:
{
lean_object* v___x_179_; 
v___x_179_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__10___redArg(v_type_171_, v_k_172_, v_cleanupAnnotations_173_, v___y_174_, v___y_175_, v___y_176_, v___y_177_);
return v___x_179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__10___boxed(lean_object* v_00_u03b1_180_, lean_object* v_type_181_, lean_object* v_k_182_, lean_object* v_cleanupAnnotations_183_, lean_object* v___y_184_, lean_object* v___y_185_, lean_object* v___y_186_, lean_object* v___y_187_, lean_object* v___y_188_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_189_; lean_object* v_res_190_; 
v_cleanupAnnotations_boxed_189_ = lean_unbox(v_cleanupAnnotations_183_);
v_res_190_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__10(v_00_u03b1_180_, v_type_181_, v_k_182_, v_cleanupAnnotations_boxed_189_, v___y_184_, v___y_185_, v___y_186_, v___y_187_);
lean_dec(v___y_187_);
lean_dec_ref(v___y_186_);
lean_dec(v___y_185_);
lean_dec_ref(v___y_184_);
return v_res_190_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6_spec__12_spec__16_spec__20___redArg(lean_object* v_x_191_, lean_object* v_x_192_, lean_object* v_x_193_, lean_object* v_x_194_){
_start:
{
lean_object* v_ks_195_; lean_object* v_vs_196_; lean_object* v___x_198_; uint8_t v_isShared_199_; uint8_t v_isSharedCheck_220_; 
v_ks_195_ = lean_ctor_get(v_x_191_, 0);
v_vs_196_ = lean_ctor_get(v_x_191_, 1);
v_isSharedCheck_220_ = !lean_is_exclusive(v_x_191_);
if (v_isSharedCheck_220_ == 0)
{
v___x_198_ = v_x_191_;
v_isShared_199_ = v_isSharedCheck_220_;
goto v_resetjp_197_;
}
else
{
lean_inc(v_vs_196_);
lean_inc(v_ks_195_);
lean_dec(v_x_191_);
v___x_198_ = lean_box(0);
v_isShared_199_ = v_isSharedCheck_220_;
goto v_resetjp_197_;
}
v_resetjp_197_:
{
lean_object* v___x_200_; uint8_t v___x_201_; 
v___x_200_ = lean_array_get_size(v_ks_195_);
v___x_201_ = lean_nat_dec_lt(v_x_192_, v___x_200_);
if (v___x_201_ == 0)
{
lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_205_; 
lean_dec(v_x_192_);
v___x_202_ = lean_array_push(v_ks_195_, v_x_193_);
v___x_203_ = lean_array_push(v_vs_196_, v_x_194_);
if (v_isShared_199_ == 0)
{
lean_ctor_set(v___x_198_, 1, v___x_203_);
lean_ctor_set(v___x_198_, 0, v___x_202_);
v___x_205_ = v___x_198_;
goto v_reusejp_204_;
}
else
{
lean_object* v_reuseFailAlloc_206_; 
v_reuseFailAlloc_206_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_206_, 0, v___x_202_);
lean_ctor_set(v_reuseFailAlloc_206_, 1, v___x_203_);
v___x_205_ = v_reuseFailAlloc_206_;
goto v_reusejp_204_;
}
v_reusejp_204_:
{
return v___x_205_;
}
}
else
{
lean_object* v_k_x27_207_; uint8_t v___x_208_; 
v_k_x27_207_ = lean_array_fget_borrowed(v_ks_195_, v_x_192_);
v___x_208_ = l_Lean_instBEqMVarId_beq(v_x_193_, v_k_x27_207_);
if (v___x_208_ == 0)
{
lean_object* v___x_210_; 
if (v_isShared_199_ == 0)
{
v___x_210_ = v___x_198_;
goto v_reusejp_209_;
}
else
{
lean_object* v_reuseFailAlloc_214_; 
v_reuseFailAlloc_214_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_214_, 0, v_ks_195_);
lean_ctor_set(v_reuseFailAlloc_214_, 1, v_vs_196_);
v___x_210_ = v_reuseFailAlloc_214_;
goto v_reusejp_209_;
}
v_reusejp_209_:
{
lean_object* v___x_211_; lean_object* v___x_212_; 
v___x_211_ = lean_unsigned_to_nat(1u);
v___x_212_ = lean_nat_add(v_x_192_, v___x_211_);
lean_dec(v_x_192_);
v_x_191_ = v___x_210_;
v_x_192_ = v___x_212_;
goto _start;
}
}
else
{
lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_218_; 
v___x_215_ = lean_array_fset(v_ks_195_, v_x_192_, v_x_193_);
v___x_216_ = lean_array_fset(v_vs_196_, v_x_192_, v_x_194_);
lean_dec(v_x_192_);
if (v_isShared_199_ == 0)
{
lean_ctor_set(v___x_198_, 1, v___x_216_);
lean_ctor_set(v___x_198_, 0, v___x_215_);
v___x_218_ = v___x_198_;
goto v_reusejp_217_;
}
else
{
lean_object* v_reuseFailAlloc_219_; 
v_reuseFailAlloc_219_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_219_, 0, v___x_215_);
lean_ctor_set(v_reuseFailAlloc_219_, 1, v___x_216_);
v___x_218_ = v_reuseFailAlloc_219_;
goto v_reusejp_217_;
}
v_reusejp_217_:
{
return v___x_218_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6_spec__12_spec__16___redArg(lean_object* v_n_221_, lean_object* v_k_222_, lean_object* v_v_223_){
_start:
{
lean_object* v___x_224_; lean_object* v___x_225_; 
v___x_224_ = lean_unsigned_to_nat(0u);
v___x_225_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6_spec__12_spec__16_spec__20___redArg(v_n_221_, v___x_224_, v_k_222_, v_v_223_);
return v___x_225_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6_spec__12___redArg___closed__0(void){
_start:
{
lean_object* v___x_226_; 
v___x_226_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_226_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6_spec__12___redArg(lean_object* v_x_227_, size_t v_x_228_, size_t v_x_229_, lean_object* v_x_230_, lean_object* v_x_231_){
_start:
{
if (lean_obj_tag(v_x_227_) == 0)
{
lean_object* v_es_232_; size_t v___x_233_; size_t v___x_234_; lean_object* v_j_235_; lean_object* v___x_236_; uint8_t v___x_237_; 
v_es_232_ = lean_ctor_get(v_x_227_, 0);
v___x_233_ = ((size_t)31ULL);
v___x_234_ = lean_usize_land(v_x_228_, v___x_233_);
v_j_235_ = lean_usize_to_nat(v___x_234_);
v___x_236_ = lean_array_get_size(v_es_232_);
v___x_237_ = lean_nat_dec_lt(v_j_235_, v___x_236_);
if (v___x_237_ == 0)
{
lean_dec(v_j_235_);
lean_dec(v_x_231_);
lean_dec(v_x_230_);
return v_x_227_;
}
else
{
lean_object* v___x_239_; uint8_t v_isShared_240_; uint8_t v_isSharedCheck_276_; 
lean_inc_ref(v_es_232_);
v_isSharedCheck_276_ = !lean_is_exclusive(v_x_227_);
if (v_isSharedCheck_276_ == 0)
{
lean_object* v_unused_277_; 
v_unused_277_ = lean_ctor_get(v_x_227_, 0);
lean_dec(v_unused_277_);
v___x_239_ = v_x_227_;
v_isShared_240_ = v_isSharedCheck_276_;
goto v_resetjp_238_;
}
else
{
lean_dec(v_x_227_);
v___x_239_ = lean_box(0);
v_isShared_240_ = v_isSharedCheck_276_;
goto v_resetjp_238_;
}
v_resetjp_238_:
{
lean_object* v_v_241_; lean_object* v___x_242_; lean_object* v_xs_x27_243_; lean_object* v___y_245_; 
v_v_241_ = lean_array_fget(v_es_232_, v_j_235_);
v___x_242_ = lean_box(0);
v_xs_x27_243_ = lean_array_fset(v_es_232_, v_j_235_, v___x_242_);
switch(lean_obj_tag(v_v_241_))
{
case 0:
{
lean_object* v_key_250_; lean_object* v_val_251_; lean_object* v___x_253_; uint8_t v_isShared_254_; uint8_t v_isSharedCheck_261_; 
v_key_250_ = lean_ctor_get(v_v_241_, 0);
v_val_251_ = lean_ctor_get(v_v_241_, 1);
v_isSharedCheck_261_ = !lean_is_exclusive(v_v_241_);
if (v_isSharedCheck_261_ == 0)
{
v___x_253_ = v_v_241_;
v_isShared_254_ = v_isSharedCheck_261_;
goto v_resetjp_252_;
}
else
{
lean_inc(v_val_251_);
lean_inc(v_key_250_);
lean_dec(v_v_241_);
v___x_253_ = lean_box(0);
v_isShared_254_ = v_isSharedCheck_261_;
goto v_resetjp_252_;
}
v_resetjp_252_:
{
uint8_t v___x_255_; 
v___x_255_ = l_Lean_instBEqMVarId_beq(v_x_230_, v_key_250_);
if (v___x_255_ == 0)
{
lean_object* v___x_256_; lean_object* v___x_257_; 
lean_del_object(v___x_253_);
v___x_256_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_250_, v_val_251_, v_x_230_, v_x_231_);
v___x_257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_257_, 0, v___x_256_);
v___y_245_ = v___x_257_;
goto v___jp_244_;
}
else
{
lean_object* v___x_259_; 
lean_dec(v_val_251_);
lean_dec(v_key_250_);
if (v_isShared_254_ == 0)
{
lean_ctor_set(v___x_253_, 1, v_x_231_);
lean_ctor_set(v___x_253_, 0, v_x_230_);
v___x_259_ = v___x_253_;
goto v_reusejp_258_;
}
else
{
lean_object* v_reuseFailAlloc_260_; 
v_reuseFailAlloc_260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_260_, 0, v_x_230_);
lean_ctor_set(v_reuseFailAlloc_260_, 1, v_x_231_);
v___x_259_ = v_reuseFailAlloc_260_;
goto v_reusejp_258_;
}
v_reusejp_258_:
{
v___y_245_ = v___x_259_;
goto v___jp_244_;
}
}
}
}
case 1:
{
lean_object* v_node_262_; lean_object* v___x_264_; uint8_t v_isShared_265_; uint8_t v_isSharedCheck_274_; 
v_node_262_ = lean_ctor_get(v_v_241_, 0);
v_isSharedCheck_274_ = !lean_is_exclusive(v_v_241_);
if (v_isSharedCheck_274_ == 0)
{
v___x_264_ = v_v_241_;
v_isShared_265_ = v_isSharedCheck_274_;
goto v_resetjp_263_;
}
else
{
lean_inc(v_node_262_);
lean_dec(v_v_241_);
v___x_264_ = lean_box(0);
v_isShared_265_ = v_isSharedCheck_274_;
goto v_resetjp_263_;
}
v_resetjp_263_:
{
size_t v___x_266_; size_t v___x_267_; size_t v___x_268_; size_t v___x_269_; lean_object* v___x_270_; lean_object* v___x_272_; 
v___x_266_ = ((size_t)5ULL);
v___x_267_ = lean_usize_shift_right(v_x_228_, v___x_266_);
v___x_268_ = ((size_t)1ULL);
v___x_269_ = lean_usize_add(v_x_229_, v___x_268_);
v___x_270_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6_spec__12___redArg(v_node_262_, v___x_267_, v___x_269_, v_x_230_, v_x_231_);
if (v_isShared_265_ == 0)
{
lean_ctor_set(v___x_264_, 0, v___x_270_);
v___x_272_ = v___x_264_;
goto v_reusejp_271_;
}
else
{
lean_object* v_reuseFailAlloc_273_; 
v_reuseFailAlloc_273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_273_, 0, v___x_270_);
v___x_272_ = v_reuseFailAlloc_273_;
goto v_reusejp_271_;
}
v_reusejp_271_:
{
v___y_245_ = v___x_272_;
goto v___jp_244_;
}
}
}
default: 
{
lean_object* v___x_275_; 
v___x_275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_275_, 0, v_x_230_);
lean_ctor_set(v___x_275_, 1, v_x_231_);
v___y_245_ = v___x_275_;
goto v___jp_244_;
}
}
v___jp_244_:
{
lean_object* v___x_246_; lean_object* v___x_248_; 
v___x_246_ = lean_array_fset(v_xs_x27_243_, v_j_235_, v___y_245_);
lean_dec(v_j_235_);
if (v_isShared_240_ == 0)
{
lean_ctor_set(v___x_239_, 0, v___x_246_);
v___x_248_ = v___x_239_;
goto v_reusejp_247_;
}
else
{
lean_object* v_reuseFailAlloc_249_; 
v_reuseFailAlloc_249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_249_, 0, v___x_246_);
v___x_248_ = v_reuseFailAlloc_249_;
goto v_reusejp_247_;
}
v_reusejp_247_:
{
return v___x_248_;
}
}
}
}
}
else
{
lean_object* v_ks_278_; lean_object* v_vs_279_; lean_object* v___x_281_; uint8_t v_isShared_282_; uint8_t v_isSharedCheck_297_; 
v_ks_278_ = lean_ctor_get(v_x_227_, 0);
v_vs_279_ = lean_ctor_get(v_x_227_, 1);
v_isSharedCheck_297_ = !lean_is_exclusive(v_x_227_);
if (v_isSharedCheck_297_ == 0)
{
v___x_281_ = v_x_227_;
v_isShared_282_ = v_isSharedCheck_297_;
goto v_resetjp_280_;
}
else
{
lean_inc(v_vs_279_);
lean_inc(v_ks_278_);
lean_dec(v_x_227_);
v___x_281_ = lean_box(0);
v_isShared_282_ = v_isSharedCheck_297_;
goto v_resetjp_280_;
}
v_resetjp_280_:
{
lean_object* v___x_284_; 
if (v_isShared_282_ == 0)
{
v___x_284_ = v___x_281_;
goto v_reusejp_283_;
}
else
{
lean_object* v_reuseFailAlloc_296_; 
v_reuseFailAlloc_296_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_296_, 0, v_ks_278_);
lean_ctor_set(v_reuseFailAlloc_296_, 1, v_vs_279_);
v___x_284_ = v_reuseFailAlloc_296_;
goto v_reusejp_283_;
}
v_reusejp_283_:
{
lean_object* v_newNode_285_; size_t v___x_286_; uint8_t v___x_287_; 
v_newNode_285_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6_spec__12_spec__16___redArg(v___x_284_, v_x_230_, v_x_231_);
v___x_286_ = ((size_t)7ULL);
v___x_287_ = lean_usize_dec_le(v___x_286_, v_x_229_);
if (v___x_287_ == 0)
{
lean_object* v___x_288_; lean_object* v___x_289_; uint8_t v___x_290_; 
v___x_288_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_285_);
v___x_289_ = lean_unsigned_to_nat(4u);
v___x_290_ = lean_nat_dec_lt(v___x_288_, v___x_289_);
lean_dec(v___x_288_);
if (v___x_290_ == 0)
{
lean_object* v_ks_291_; lean_object* v_vs_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; 
v_ks_291_ = lean_ctor_get(v_newNode_285_, 0);
lean_inc_ref(v_ks_291_);
v_vs_292_ = lean_ctor_get(v_newNode_285_, 1);
lean_inc_ref(v_vs_292_);
lean_dec_ref(v_newNode_285_);
v___x_293_ = lean_unsigned_to_nat(0u);
v___x_294_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6_spec__12___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6_spec__12___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6_spec__12___redArg___closed__0);
v___x_295_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6_spec__12_spec__17___redArg(v_x_229_, v_ks_291_, v_vs_292_, v___x_293_, v___x_294_);
lean_dec_ref(v_vs_292_);
lean_dec_ref(v_ks_291_);
return v___x_295_;
}
else
{
return v_newNode_285_;
}
}
else
{
return v_newNode_285_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6_spec__12_spec__17___redArg(size_t v_depth_298_, lean_object* v_keys_299_, lean_object* v_vals_300_, lean_object* v_i_301_, lean_object* v_entries_302_){
_start:
{
lean_object* v___x_303_; uint8_t v___x_304_; 
v___x_303_ = lean_array_get_size(v_keys_299_);
v___x_304_ = lean_nat_dec_lt(v_i_301_, v___x_303_);
if (v___x_304_ == 0)
{
lean_dec(v_i_301_);
return v_entries_302_;
}
else
{
lean_object* v_k_305_; lean_object* v_v_306_; uint64_t v___x_307_; size_t v_h_308_; size_t v___x_309_; lean_object* v___x_310_; size_t v___x_311_; size_t v___x_312_; size_t v___x_313_; size_t v_h_314_; lean_object* v___x_315_; lean_object* v___x_316_; 
v_k_305_ = lean_array_fget_borrowed(v_keys_299_, v_i_301_);
v_v_306_ = lean_array_fget_borrowed(v_vals_300_, v_i_301_);
v___x_307_ = l_Lean_instHashableMVarId_hash(v_k_305_);
v_h_308_ = lean_uint64_to_usize(v___x_307_);
v___x_309_ = ((size_t)5ULL);
v___x_310_ = lean_unsigned_to_nat(1u);
v___x_311_ = ((size_t)1ULL);
v___x_312_ = lean_usize_sub(v_depth_298_, v___x_311_);
v___x_313_ = lean_usize_mul(v___x_309_, v___x_312_);
v_h_314_ = lean_usize_shift_right(v_h_308_, v___x_313_);
v___x_315_ = lean_nat_add(v_i_301_, v___x_310_);
lean_dec(v_i_301_);
lean_inc(v_v_306_);
lean_inc(v_k_305_);
v___x_316_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6_spec__12___redArg(v_entries_302_, v_h_314_, v_depth_298_, v_k_305_, v_v_306_);
v_i_301_ = v___x_315_;
v_entries_302_ = v___x_316_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6_spec__12_spec__17___redArg___boxed(lean_object* v_depth_318_, lean_object* v_keys_319_, lean_object* v_vals_320_, lean_object* v_i_321_, lean_object* v_entries_322_){
_start:
{
size_t v_depth_boxed_323_; lean_object* v_res_324_; 
v_depth_boxed_323_ = lean_unbox_usize(v_depth_318_);
lean_dec(v_depth_318_);
v_res_324_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6_spec__12_spec__17___redArg(v_depth_boxed_323_, v_keys_319_, v_vals_320_, v_i_321_, v_entries_322_);
lean_dec_ref(v_vals_320_);
lean_dec_ref(v_keys_319_);
return v_res_324_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6_spec__12___redArg___boxed(lean_object* v_x_325_, lean_object* v_x_326_, lean_object* v_x_327_, lean_object* v_x_328_, lean_object* v_x_329_){
_start:
{
size_t v_x_16607__boxed_330_; size_t v_x_16608__boxed_331_; lean_object* v_res_332_; 
v_x_16607__boxed_330_ = lean_unbox_usize(v_x_326_);
lean_dec(v_x_326_);
v_x_16608__boxed_331_ = lean_unbox_usize(v_x_327_);
lean_dec(v_x_327_);
v_res_332_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6_spec__12___redArg(v_x_325_, v_x_16607__boxed_330_, v_x_16608__boxed_331_, v_x_328_, v_x_329_);
return v_res_332_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6___redArg(lean_object* v_x_333_, lean_object* v_x_334_, lean_object* v_x_335_){
_start:
{
uint64_t v___x_336_; size_t v___x_337_; size_t v___x_338_; lean_object* v___x_339_; 
v___x_336_ = l_Lean_instHashableMVarId_hash(v_x_334_);
v___x_337_ = lean_uint64_to_usize(v___x_336_);
v___x_338_ = ((size_t)1ULL);
v___x_339_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6_spec__12___redArg(v_x_333_, v___x_337_, v___x_338_, v_x_334_, v_x_335_);
return v___x_339_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4___redArg(lean_object* v_mvarId_340_, lean_object* v_val_341_, lean_object* v___y_342_){
_start:
{
lean_object* v___x_344_; lean_object* v_mctx_345_; lean_object* v_cache_346_; lean_object* v_zetaDeltaFVarIds_347_; lean_object* v_postponed_348_; lean_object* v_diag_349_; lean_object* v___x_351_; uint8_t v_isShared_352_; uint8_t v_isSharedCheck_378_; 
v___x_344_ = lean_st_ref_take(v___y_342_);
v_mctx_345_ = lean_ctor_get(v___x_344_, 0);
v_cache_346_ = lean_ctor_get(v___x_344_, 1);
v_zetaDeltaFVarIds_347_ = lean_ctor_get(v___x_344_, 2);
v_postponed_348_ = lean_ctor_get(v___x_344_, 3);
v_diag_349_ = lean_ctor_get(v___x_344_, 4);
v_isSharedCheck_378_ = !lean_is_exclusive(v___x_344_);
if (v_isSharedCheck_378_ == 0)
{
v___x_351_ = v___x_344_;
v_isShared_352_ = v_isSharedCheck_378_;
goto v_resetjp_350_;
}
else
{
lean_inc(v_diag_349_);
lean_inc(v_postponed_348_);
lean_inc(v_zetaDeltaFVarIds_347_);
lean_inc(v_cache_346_);
lean_inc(v_mctx_345_);
lean_dec(v___x_344_);
v___x_351_ = lean_box(0);
v_isShared_352_ = v_isSharedCheck_378_;
goto v_resetjp_350_;
}
v_resetjp_350_:
{
lean_object* v_depth_353_; lean_object* v_levelAssignDepth_354_; lean_object* v_lmvarCounter_355_; lean_object* v_mvarCounter_356_; lean_object* v_lDecls_357_; lean_object* v_decls_358_; lean_object* v_userNames_359_; lean_object* v_lAssignment_360_; lean_object* v_eAssignment_361_; lean_object* v_dAssignment_362_; lean_object* v_instanceTypedMVars_363_; lean_object* v___x_365_; uint8_t v_isShared_366_; uint8_t v_isSharedCheck_377_; 
v_depth_353_ = lean_ctor_get(v_mctx_345_, 0);
v_levelAssignDepth_354_ = lean_ctor_get(v_mctx_345_, 1);
v_lmvarCounter_355_ = lean_ctor_get(v_mctx_345_, 2);
v_mvarCounter_356_ = lean_ctor_get(v_mctx_345_, 3);
v_lDecls_357_ = lean_ctor_get(v_mctx_345_, 4);
v_decls_358_ = lean_ctor_get(v_mctx_345_, 5);
v_userNames_359_ = lean_ctor_get(v_mctx_345_, 6);
v_lAssignment_360_ = lean_ctor_get(v_mctx_345_, 7);
v_eAssignment_361_ = lean_ctor_get(v_mctx_345_, 8);
v_dAssignment_362_ = lean_ctor_get(v_mctx_345_, 9);
v_instanceTypedMVars_363_ = lean_ctor_get(v_mctx_345_, 10);
v_isSharedCheck_377_ = !lean_is_exclusive(v_mctx_345_);
if (v_isSharedCheck_377_ == 0)
{
v___x_365_ = v_mctx_345_;
v_isShared_366_ = v_isSharedCheck_377_;
goto v_resetjp_364_;
}
else
{
lean_inc(v_instanceTypedMVars_363_);
lean_inc(v_dAssignment_362_);
lean_inc(v_eAssignment_361_);
lean_inc(v_lAssignment_360_);
lean_inc(v_userNames_359_);
lean_inc(v_decls_358_);
lean_inc(v_lDecls_357_);
lean_inc(v_mvarCounter_356_);
lean_inc(v_lmvarCounter_355_);
lean_inc(v_levelAssignDepth_354_);
lean_inc(v_depth_353_);
lean_dec(v_mctx_345_);
v___x_365_ = lean_box(0);
v_isShared_366_ = v_isSharedCheck_377_;
goto v_resetjp_364_;
}
v_resetjp_364_:
{
lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_370_; 
v___x_367_ = lean_box(0);
v___x_368_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6___redArg(v_eAssignment_361_, v_mvarId_340_, v_val_341_);
if (v_isShared_366_ == 0)
{
lean_ctor_set(v___x_365_, 8, v___x_368_);
v___x_370_ = v___x_365_;
goto v_reusejp_369_;
}
else
{
lean_object* v_reuseFailAlloc_376_; 
v_reuseFailAlloc_376_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_376_, 0, v_depth_353_);
lean_ctor_set(v_reuseFailAlloc_376_, 1, v_levelAssignDepth_354_);
lean_ctor_set(v_reuseFailAlloc_376_, 2, v_lmvarCounter_355_);
lean_ctor_set(v_reuseFailAlloc_376_, 3, v_mvarCounter_356_);
lean_ctor_set(v_reuseFailAlloc_376_, 4, v_lDecls_357_);
lean_ctor_set(v_reuseFailAlloc_376_, 5, v_decls_358_);
lean_ctor_set(v_reuseFailAlloc_376_, 6, v_userNames_359_);
lean_ctor_set(v_reuseFailAlloc_376_, 7, v_lAssignment_360_);
lean_ctor_set(v_reuseFailAlloc_376_, 8, v___x_368_);
lean_ctor_set(v_reuseFailAlloc_376_, 9, v_dAssignment_362_);
lean_ctor_set(v_reuseFailAlloc_376_, 10, v_instanceTypedMVars_363_);
v___x_370_ = v_reuseFailAlloc_376_;
goto v_reusejp_369_;
}
v_reusejp_369_:
{
lean_object* v___x_372_; 
if (v_isShared_352_ == 0)
{
lean_ctor_set(v___x_351_, 0, v___x_370_);
v___x_372_ = v___x_351_;
goto v_reusejp_371_;
}
else
{
lean_object* v_reuseFailAlloc_375_; 
v_reuseFailAlloc_375_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_375_, 0, v___x_370_);
lean_ctor_set(v_reuseFailAlloc_375_, 1, v_cache_346_);
lean_ctor_set(v_reuseFailAlloc_375_, 2, v_zetaDeltaFVarIds_347_);
lean_ctor_set(v_reuseFailAlloc_375_, 3, v_postponed_348_);
lean_ctor_set(v_reuseFailAlloc_375_, 4, v_diag_349_);
v___x_372_ = v_reuseFailAlloc_375_;
goto v_reusejp_371_;
}
v_reusejp_371_:
{
lean_object* v___x_373_; lean_object* v___x_374_; 
v___x_373_ = lean_st_ref_put(v___y_342_, v___x_372_);
v___x_374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_374_, 0, v___x_367_);
return v___x_374_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4___redArg___boxed(lean_object* v_mvarId_379_, lean_object* v_val_380_, lean_object* v___y_381_, lean_object* v___y_382_){
_start:
{
lean_object* v_res_383_; 
v_res_383_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4___redArg(v_mvarId_379_, v_val_380_, v___y_381_);
lean_dec(v___y_381_);
return v_res_383_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__3_spec__4(lean_object* v_msgData_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_){
_start:
{
lean_object* v___x_390_; lean_object* v_env_391_; uint8_t v___x_392_; lean_object* v_env_393_; lean_object* v___x_394_; lean_object* v_toCold_395_; lean_object* v_mctx_396_; lean_object* v_lctx_397_; lean_object* v_options_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; 
v___x_390_ = lean_st_ref_get(v___y_388_);
v_env_391_ = lean_ctor_get(v___x_390_, 0);
lean_inc_ref(v_env_391_);
lean_dec(v___x_390_);
v___x_392_ = 0;
v_env_393_ = l_Lean_Environment_setRecordingDeps(v_env_391_, v___x_392_);
v___x_394_ = lean_st_ref_get(v___y_386_);
v_toCold_395_ = lean_ctor_get(v___y_387_, 0);
v_mctx_396_ = lean_ctor_get(v___x_394_, 0);
lean_inc_ref(v_mctx_396_);
lean_dec(v___x_394_);
v_lctx_397_ = lean_ctor_get(v___y_385_, 2);
v_options_398_ = lean_ctor_get(v_toCold_395_, 2);
lean_inc_ref(v_options_398_);
lean_inc_ref(v_lctx_397_);
v___x_399_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_399_, 0, v_env_393_);
lean_ctor_set(v___x_399_, 1, v_mctx_396_);
lean_ctor_set(v___x_399_, 2, v_lctx_397_);
lean_ctor_set(v___x_399_, 3, v_options_398_);
v___x_400_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_400_, 0, v___x_399_);
lean_ctor_set(v___x_400_, 1, v_msgData_384_);
v___x_401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_401_, 0, v___x_400_);
return v___x_401_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__3_spec__4___boxed(lean_object* v_msgData_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_){
_start:
{
lean_object* v_res_408_; 
v_res_408_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__3_spec__4(v_msgData_402_, v___y_403_, v___y_404_, v___y_405_, v___y_406_);
lean_dec(v___y_406_);
lean_dec_ref(v___y_405_);
lean_dec(v___y_404_);
lean_dec_ref(v___y_403_);
return v_res_408_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__3___redArg(lean_object* v_msg_409_, lean_object* v___y_410_, lean_object* v___y_411_, lean_object* v___y_412_, lean_object* v___y_413_){
_start:
{
lean_object* v_ref_415_; lean_object* v___x_416_; lean_object* v_a_417_; lean_object* v___x_419_; uint8_t v_isShared_420_; uint8_t v_isSharedCheck_425_; 
v_ref_415_ = lean_ctor_get(v___y_412_, 2);
v___x_416_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__3_spec__4(v_msg_409_, v___y_410_, v___y_411_, v___y_412_, v___y_413_);
v_a_417_ = lean_ctor_get(v___x_416_, 0);
v_isSharedCheck_425_ = !lean_is_exclusive(v___x_416_);
if (v_isSharedCheck_425_ == 0)
{
v___x_419_ = v___x_416_;
v_isShared_420_ = v_isSharedCheck_425_;
goto v_resetjp_418_;
}
else
{
lean_inc(v_a_417_);
lean_dec(v___x_416_);
v___x_419_ = lean_box(0);
v_isShared_420_ = v_isSharedCheck_425_;
goto v_resetjp_418_;
}
v_resetjp_418_:
{
lean_object* v___x_421_; lean_object* v___x_423_; 
lean_inc(v_ref_415_);
v___x_421_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_421_, 0, v_ref_415_);
lean_ctor_set(v___x_421_, 1, v_a_417_);
if (v_isShared_420_ == 0)
{
lean_ctor_set_tag(v___x_419_, 1);
lean_ctor_set(v___x_419_, 0, v___x_421_);
v___x_423_ = v___x_419_;
goto v_reusejp_422_;
}
else
{
lean_object* v_reuseFailAlloc_424_; 
v_reuseFailAlloc_424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_424_, 0, v___x_421_);
v___x_423_ = v_reuseFailAlloc_424_;
goto v_reusejp_422_;
}
v_reusejp_422_:
{
return v___x_423_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__3___redArg___boxed(lean_object* v_msg_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_){
_start:
{
lean_object* v_res_432_; 
v_res_432_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__3___redArg(v_msg_426_, v___y_427_, v___y_428_, v___y_429_, v___y_430_);
lean_dec(v___y_430_);
lean_dec_ref(v___y_429_);
lean_dec(v___y_428_);
lean_dec_ref(v___y_427_);
return v_res_432_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__9___lam__0___closed__1(void){
_start:
{
lean_object* v___x_434_; lean_object* v___x_435_; 
v___x_434_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__9___lam__0___closed__0));
v___x_435_ = l_Lean_stringToMessageData(v___x_434_);
return v___x_435_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__9___lam__0(lean_object* v___x_436_, lean_object* v_snd_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_){
_start:
{
lean_object* v___x_443_; 
lean_inc(v___y_441_);
lean_inc_ref(v___y_440_);
lean_inc(v___y_439_);
lean_inc_ref(v___y_438_);
lean_inc_ref(v___x_436_);
v___x_443_ = lean_infer_type(v___x_436_, v___y_438_, v___y_439_, v___y_440_, v___y_441_);
if (lean_obj_tag(v___x_443_) == 0)
{
lean_object* v_a_444_; lean_object* v___x_445_; 
v_a_444_ = lean_ctor_get(v___x_443_, 0);
lean_inc(v_a_444_);
lean_dec_ref_known(v___x_443_, 1);
v___x_445_ = l_Lean_refutableHasNotBit_x3f(v_a_444_, v___y_438_, v___y_439_, v___y_440_, v___y_441_);
if (lean_obj_tag(v___x_445_) == 0)
{
lean_object* v_a_446_; 
v_a_446_ = lean_ctor_get(v___x_445_, 0);
lean_inc(v_a_446_);
lean_dec_ref_known(v___x_445_, 1);
if (lean_obj_tag(v_a_446_) == 1)
{
lean_object* v_val_447_; lean_object* v___x_448_; 
v_val_447_ = lean_ctor_get(v_a_446_, 0);
lean_inc(v_val_447_);
lean_dec_ref_known(v_a_446_, 1);
lean_inc(v_snd_437_);
v___x_448_ = l_Lean_MVarId_getType(v_snd_437_, v___y_438_, v___y_439_, v___y_440_, v___y_441_);
if (lean_obj_tag(v___x_448_) == 0)
{
lean_object* v_a_449_; lean_object* v___x_450_; 
v_a_449_ = lean_ctor_get(v___x_448_, 0);
lean_inc(v_a_449_);
lean_dec_ref_known(v___x_448_, 1);
v___x_450_ = l_Lean_Meta_mkAbsurd(v_a_449_, v_val_447_, v___x_436_, v___y_438_, v___y_439_, v___y_440_, v___y_441_);
lean_dec(v___y_441_);
lean_dec_ref(v___y_440_);
lean_dec_ref(v___y_438_);
if (lean_obj_tag(v___x_450_) == 0)
{
lean_object* v_a_451_; lean_object* v___x_452_; 
v_a_451_ = lean_ctor_get(v___x_450_, 0);
lean_inc(v_a_451_);
lean_dec_ref_known(v___x_450_, 1);
v___x_452_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4___redArg(v_snd_437_, v_a_451_, v___y_439_);
lean_dec(v___y_439_);
return v___x_452_;
}
else
{
lean_object* v_a_453_; lean_object* v___x_455_; uint8_t v_isShared_456_; uint8_t v_isSharedCheck_460_; 
lean_dec(v___y_439_);
lean_dec(v_snd_437_);
v_a_453_ = lean_ctor_get(v___x_450_, 0);
v_isSharedCheck_460_ = !lean_is_exclusive(v___x_450_);
if (v_isSharedCheck_460_ == 0)
{
v___x_455_ = v___x_450_;
v_isShared_456_ = v_isSharedCheck_460_;
goto v_resetjp_454_;
}
else
{
lean_inc(v_a_453_);
lean_dec(v___x_450_);
v___x_455_ = lean_box(0);
v_isShared_456_ = v_isSharedCheck_460_;
goto v_resetjp_454_;
}
v_resetjp_454_:
{
lean_object* v___x_458_; 
if (v_isShared_456_ == 0)
{
v___x_458_ = v___x_455_;
goto v_reusejp_457_;
}
else
{
lean_object* v_reuseFailAlloc_459_; 
v_reuseFailAlloc_459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_459_, 0, v_a_453_);
v___x_458_ = v_reuseFailAlloc_459_;
goto v_reusejp_457_;
}
v_reusejp_457_:
{
return v___x_458_;
}
}
}
}
else
{
lean_object* v_a_461_; lean_object* v___x_463_; uint8_t v_isShared_464_; uint8_t v_isSharedCheck_468_; 
lean_dec(v_val_447_);
lean_dec(v___y_441_);
lean_dec_ref(v___y_440_);
lean_dec(v___y_439_);
lean_dec_ref(v___y_438_);
lean_dec(v_snd_437_);
lean_dec_ref(v___x_436_);
v_a_461_ = lean_ctor_get(v___x_448_, 0);
v_isSharedCheck_468_ = !lean_is_exclusive(v___x_448_);
if (v_isSharedCheck_468_ == 0)
{
v___x_463_ = v___x_448_;
v_isShared_464_ = v_isSharedCheck_468_;
goto v_resetjp_462_;
}
else
{
lean_inc(v_a_461_);
lean_dec(v___x_448_);
v___x_463_ = lean_box(0);
v_isShared_464_ = v_isSharedCheck_468_;
goto v_resetjp_462_;
}
v_resetjp_462_:
{
lean_object* v___x_466_; 
if (v_isShared_464_ == 0)
{
v___x_466_ = v___x_463_;
goto v_reusejp_465_;
}
else
{
lean_object* v_reuseFailAlloc_467_; 
v_reuseFailAlloc_467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_467_, 0, v_a_461_);
v___x_466_ = v_reuseFailAlloc_467_;
goto v_reusejp_465_;
}
v_reusejp_465_:
{
return v___x_466_;
}
}
}
}
else
{
lean_object* v___x_469_; 
lean_dec(v_a_446_);
lean_dec(v_snd_437_);
lean_inc(v___y_441_);
lean_inc_ref(v___y_440_);
lean_inc(v___y_439_);
lean_inc_ref(v___y_438_);
v___x_469_ = lean_infer_type(v___x_436_, v___y_438_, v___y_439_, v___y_440_, v___y_441_);
if (lean_obj_tag(v___x_469_) == 0)
{
lean_object* v_a_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; 
v_a_470_ = lean_ctor_get(v___x_469_, 0);
lean_inc(v_a_470_);
lean_dec_ref_known(v___x_469_, 1);
v___x_471_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__9___lam__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__9___lam__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__9___lam__0___closed__1);
v___x_472_ = l_Lean_MessageData_ofExpr(v_a_470_);
v___x_473_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_473_, 0, v___x_471_);
lean_ctor_set(v___x_473_, 1, v___x_472_);
v___x_474_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__3___redArg(v___x_473_, v___y_438_, v___y_439_, v___y_440_, v___y_441_);
lean_dec(v___y_441_);
lean_dec_ref(v___y_440_);
lean_dec(v___y_439_);
lean_dec_ref(v___y_438_);
return v___x_474_;
}
else
{
lean_object* v_a_475_; lean_object* v___x_477_; uint8_t v_isShared_478_; uint8_t v_isSharedCheck_482_; 
lean_dec(v___y_441_);
lean_dec_ref(v___y_440_);
lean_dec(v___y_439_);
lean_dec_ref(v___y_438_);
v_a_475_ = lean_ctor_get(v___x_469_, 0);
v_isSharedCheck_482_ = !lean_is_exclusive(v___x_469_);
if (v_isSharedCheck_482_ == 0)
{
v___x_477_ = v___x_469_;
v_isShared_478_ = v_isSharedCheck_482_;
goto v_resetjp_476_;
}
else
{
lean_inc(v_a_475_);
lean_dec(v___x_469_);
v___x_477_ = lean_box(0);
v_isShared_478_ = v_isSharedCheck_482_;
goto v_resetjp_476_;
}
v_resetjp_476_:
{
lean_object* v___x_480_; 
if (v_isShared_478_ == 0)
{
v___x_480_ = v___x_477_;
goto v_reusejp_479_;
}
else
{
lean_object* v_reuseFailAlloc_481_; 
v_reuseFailAlloc_481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_481_, 0, v_a_475_);
v___x_480_ = v_reuseFailAlloc_481_;
goto v_reusejp_479_;
}
v_reusejp_479_:
{
return v___x_480_;
}
}
}
}
}
else
{
lean_object* v_a_483_; lean_object* v___x_485_; uint8_t v_isShared_486_; uint8_t v_isSharedCheck_490_; 
lean_dec(v___y_441_);
lean_dec_ref(v___y_440_);
lean_dec(v___y_439_);
lean_dec_ref(v___y_438_);
lean_dec(v_snd_437_);
lean_dec_ref(v___x_436_);
v_a_483_ = lean_ctor_get(v___x_445_, 0);
v_isSharedCheck_490_ = !lean_is_exclusive(v___x_445_);
if (v_isSharedCheck_490_ == 0)
{
v___x_485_ = v___x_445_;
v_isShared_486_ = v_isSharedCheck_490_;
goto v_resetjp_484_;
}
else
{
lean_inc(v_a_483_);
lean_dec(v___x_445_);
v___x_485_ = lean_box(0);
v_isShared_486_ = v_isSharedCheck_490_;
goto v_resetjp_484_;
}
v_resetjp_484_:
{
lean_object* v___x_488_; 
if (v_isShared_486_ == 0)
{
v___x_488_ = v___x_485_;
goto v_reusejp_487_;
}
else
{
lean_object* v_reuseFailAlloc_489_; 
v_reuseFailAlloc_489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_489_, 0, v_a_483_);
v___x_488_ = v_reuseFailAlloc_489_;
goto v_reusejp_487_;
}
v_reusejp_487_:
{
return v___x_488_;
}
}
}
}
else
{
lean_object* v_a_491_; lean_object* v___x_493_; uint8_t v_isShared_494_; uint8_t v_isSharedCheck_498_; 
lean_dec(v___y_441_);
lean_dec_ref(v___y_440_);
lean_dec(v___y_439_);
lean_dec_ref(v___y_438_);
lean_dec(v_snd_437_);
lean_dec_ref(v___x_436_);
v_a_491_ = lean_ctor_get(v___x_443_, 0);
v_isSharedCheck_498_ = !lean_is_exclusive(v___x_443_);
if (v_isSharedCheck_498_ == 0)
{
v___x_493_ = v___x_443_;
v_isShared_494_ = v_isSharedCheck_498_;
goto v_resetjp_492_;
}
else
{
lean_inc(v_a_491_);
lean_dec(v___x_443_);
v___x_493_ = lean_box(0);
v_isShared_494_ = v_isSharedCheck_498_;
goto v_resetjp_492_;
}
v_resetjp_492_:
{
lean_object* v___x_496_; 
if (v_isShared_494_ == 0)
{
v___x_496_ = v___x_493_;
goto v_reusejp_495_;
}
else
{
lean_object* v_reuseFailAlloc_497_; 
v_reuseFailAlloc_497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_497_, 0, v_a_491_);
v___x_496_ = v_reuseFailAlloc_497_;
goto v_reusejp_495_;
}
v_reusejp_495_:
{
return v___x_496_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__9___lam__0___boxed(lean_object* v___x_499_, lean_object* v_snd_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_){
_start:
{
lean_object* v_res_506_; 
v_res_506_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__9___lam__0(v___x_499_, v_snd_500_, v___y_501_, v___y_502_, v___y_503_, v___y_504_);
return v_res_506_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__5_spec__8(lean_object* v_a_507_, lean_object* v_as_508_, size_t v_i_509_, size_t v_stop_510_){
_start:
{
uint8_t v___x_511_; 
v___x_511_ = lean_usize_dec_eq(v_i_509_, v_stop_510_);
if (v___x_511_ == 0)
{
lean_object* v___x_512_; uint8_t v___x_513_; 
v___x_512_ = lean_array_uget_borrowed(v_as_508_, v_i_509_);
v___x_513_ = lean_name_eq(v_a_507_, v___x_512_);
if (v___x_513_ == 0)
{
size_t v___x_514_; size_t v___x_515_; 
v___x_514_ = ((size_t)1ULL);
v___x_515_ = lean_usize_add(v_i_509_, v___x_514_);
v_i_509_ = v___x_515_;
goto _start;
}
else
{
return v___x_513_;
}
}
else
{
uint8_t v___x_517_; 
v___x_517_ = 0;
return v___x_517_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__5_spec__8___boxed(lean_object* v_a_518_, lean_object* v_as_519_, lean_object* v_i_520_, lean_object* v_stop_521_){
_start:
{
size_t v_i_boxed_522_; size_t v_stop_boxed_523_; uint8_t v_res_524_; lean_object* v_r_525_; 
v_i_boxed_522_ = lean_unbox_usize(v_i_520_);
lean_dec(v_i_520_);
v_stop_boxed_523_ = lean_unbox_usize(v_stop_521_);
lean_dec(v_stop_521_);
v_res_524_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__5_spec__8(v_a_518_, v_as_519_, v_i_boxed_522_, v_stop_boxed_523_);
lean_dec_ref(v_as_519_);
lean_dec(v_a_518_);
v_r_525_ = lean_box(v_res_524_);
return v_r_525_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__5(lean_object* v_as_526_, lean_object* v_a_527_){
_start:
{
lean_object* v___x_528_; lean_object* v___x_529_; uint8_t v___x_530_; 
v___x_528_ = lean_unsigned_to_nat(0u);
v___x_529_ = lean_array_get_size(v_as_526_);
v___x_530_ = lean_nat_dec_lt(v___x_528_, v___x_529_);
if (v___x_530_ == 0)
{
return v___x_530_;
}
else
{
size_t v___x_531_; size_t v___x_532_; uint8_t v___x_533_; 
v___x_531_ = ((size_t)0ULL);
v___x_532_ = lean_usize_of_nat(v___x_529_);
v___x_533_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__5_spec__8(v_a_527_, v_as_526_, v___x_531_, v___x_532_);
return v___x_533_;
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__5___boxed(lean_object* v_as_534_, lean_object* v_a_535_){
_start:
{
uint8_t v_res_536_; lean_object* v_r_537_; 
v_res_536_ = l_Array_contains___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__5(v_as_534_, v_a_535_);
lean_dec(v_a_535_);
lean_dec_ref(v_as_534_);
v_r_537_ = lean_box(v_res_536_);
return v_r_537_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__9___lam__1___closed__3(void){
_start:
{
lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; 
v___x_541_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__9___lam__1___closed__2));
v___x_542_ = lean_unsigned_to_nat(10u);
v___x_543_ = lean_unsigned_to_nat(63u);
v___x_544_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__9___lam__1___closed__1));
v___x_545_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__9___lam__1___closed__0));
v___x_546_ = l_mkPanicMessageWithDecl(v___x_545_, v___x_544_, v___x_543_, v___x_542_, v___x_541_);
return v___x_546_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__9___lam__1___closed__7(void){
_start:
{
lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; 
v___x_550_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__9___lam__1___closed__6));
v___x_551_ = lean_unsigned_to_nat(14u);
v___x_552_ = lean_unsigned_to_nat(22u);
v___x_553_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__9___lam__1___closed__5));
v___x_554_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__9___lam__1___closed__4));
v___x_555_ = l_mkPanicMessageWithDecl(v___x_554_, v___x_553_, v___x_552_, v___x_551_, v___x_550_);
return v___x_555_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__9___lam__1(uint8_t v___y_556_, lean_object* v_val_557_, lean_object* v_mvarId_558_, uint8_t v___x_559_, lean_object* v_subst_560_, lean_object* v_fst_561_, lean_object* v_fst_562_, lean_object* v___x_563_, lean_object* v_ctorName_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_){
_start:
{
lean_object* v___y_571_; 
if (v___y_556_ == 0)
{
lean_object* v___x_593_; lean_object* v___x_594_; 
lean_dec(v_ctorName_564_);
lean_dec(v___x_563_);
lean_dec(v_fst_562_);
lean_dec(v_fst_561_);
lean_dec(v_mvarId_558_);
v___x_593_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__9___lam__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__9___lam__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__9___lam__1___closed__3);
v___x_594_ = l_panic___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__2(v___x_593_, v___y_565_, v___y_566_, v___y_567_, v___y_568_);
return v___x_594_;
}
else
{
if (lean_obj_tag(v_ctorName_564_) == 0)
{
lean_object* v___x_595_; lean_object* v___x_596_; 
v___x_595_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__9___lam__1___closed__7, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__9___lam__1___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__9___lam__1___closed__7);
v___x_596_ = l_panic___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__7(v___x_595_);
v___y_571_ = v___x_596_;
goto v___jp_570_;
}
else
{
lean_object* v_val_597_; 
v_val_597_ = lean_ctor_get(v_ctorName_564_, 0);
lean_inc(v_val_597_);
lean_dec_ref_known(v_ctorName_564_, 1);
v___y_571_ = v_val_597_;
goto v___jp_570_;
}
}
v___jp_570_:
{
lean_object* v_insterestingCtors_572_; uint8_t v___x_573_; 
v_insterestingCtors_572_ = lean_ctor_get(v_val_557_, 3);
v___x_573_ = l_Array_contains___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__5(v_insterestingCtors_572_, v___y_571_);
lean_dec(v___y_571_);
if (v___x_573_ == 0)
{
lean_object* v___x_574_; 
lean_dec(v___x_563_);
lean_dec(v_fst_562_);
lean_dec(v_fst_561_);
v___x_574_ = l_Lean_MVarId_refl(v_mvarId_558_, v___x_559_, v___y_565_, v___y_566_, v___y_567_, v___y_568_);
return v___x_574_;
}
else
{
lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; 
v___x_575_ = l_Lean_Meta_FVarSubst_get(v_subst_560_, v_fst_561_);
v___x_576_ = l_Lean_Meta_FVarSubst_get(v_subst_560_, v_fst_562_);
v___x_577_ = l_Lean_Expr_fvarId_x21(v___x_576_);
lean_dec_ref(v___x_576_);
v___x_578_ = l_Lean_Meta_substEq(v_mvarId_558_, v___x_577_, v___x_563_, v___y_565_, v___y_566_, v___y_567_, v___y_568_);
if (lean_obj_tag(v___x_578_) == 0)
{
lean_object* v_a_579_; lean_object* v_fst_580_; lean_object* v_snd_581_; lean_object* v___x_582_; lean_object* v___f_583_; lean_object* v___x_584_; 
v_a_579_ = lean_ctor_get(v___x_578_, 0);
lean_inc(v_a_579_);
lean_dec_ref_known(v___x_578_, 1);
v_fst_580_ = lean_ctor_get(v_a_579_, 0);
lean_inc(v_fst_580_);
v_snd_581_ = lean_ctor_get(v_a_579_, 1);
lean_inc_n(v_snd_581_, 2);
lean_dec(v_a_579_);
v___x_582_ = l_Lean_Meta_FVarSubst_apply(v_fst_580_, v___x_575_);
lean_dec_ref(v___x_575_);
v___f_583_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__9___lam__0___boxed), 7, 2);
lean_closure_set(v___f_583_, 0, v___x_582_);
lean_closure_set(v___f_583_, 1, v_snd_581_);
v___x_584_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__6___redArg(v_snd_581_, v___f_583_, v___y_565_, v___y_566_, v___y_567_, v___y_568_);
return v___x_584_;
}
else
{
lean_object* v_a_585_; lean_object* v___x_587_; uint8_t v_isShared_588_; uint8_t v_isSharedCheck_592_; 
lean_dec_ref(v___x_575_);
v_a_585_ = lean_ctor_get(v___x_578_, 0);
v_isSharedCheck_592_ = !lean_is_exclusive(v___x_578_);
if (v_isSharedCheck_592_ == 0)
{
v___x_587_ = v___x_578_;
v_isShared_588_ = v_isSharedCheck_592_;
goto v_resetjp_586_;
}
else
{
lean_inc(v_a_585_);
lean_dec(v___x_578_);
v___x_587_ = lean_box(0);
v_isShared_588_ = v_isSharedCheck_592_;
goto v_resetjp_586_;
}
v_resetjp_586_:
{
lean_object* v___x_590_; 
if (v_isShared_588_ == 0)
{
v___x_590_ = v___x_587_;
goto v_reusejp_589_;
}
else
{
lean_object* v_reuseFailAlloc_591_; 
v_reuseFailAlloc_591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_591_, 0, v_a_585_);
v___x_590_ = v_reuseFailAlloc_591_;
goto v_reusejp_589_;
}
v_reusejp_589_:
{
return v___x_590_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__9___lam__1___boxed(lean_object* v___y_598_, lean_object* v_val_599_, lean_object* v_mvarId_600_, lean_object* v___x_601_, lean_object* v_subst_602_, lean_object* v_fst_603_, lean_object* v_fst_604_, lean_object* v___x_605_, lean_object* v_ctorName_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_){
_start:
{
uint8_t v___y_17083__boxed_612_; uint8_t v___x_17085__boxed_613_; lean_object* v_res_614_; 
v___y_17083__boxed_612_ = lean_unbox(v___y_598_);
v___x_17085__boxed_613_ = lean_unbox(v___x_601_);
v_res_614_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__9___lam__1(v___y_17083__boxed_612_, v_val_599_, v_mvarId_600_, v___x_17085__boxed_613_, v_subst_602_, v_fst_603_, v_fst_604_, v___x_605_, v_ctorName_606_, v___y_607_, v___y_608_, v___y_609_, v___y_610_);
lean_dec(v___y_610_);
lean_dec_ref(v___y_609_);
lean_dec(v___y_608_);
lean_dec_ref(v___y_607_);
lean_dec(v_subst_602_);
lean_dec_ref(v_val_599_);
return v_res_614_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__9(lean_object* v_val_615_, lean_object* v___x_616_, lean_object* v_fst_617_, lean_object* v_fst_618_, lean_object* v_as_619_, size_t v_i_620_, size_t v_stop_621_, lean_object* v_b_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_){
_start:
{
uint8_t v___x_628_; 
v___x_628_ = lean_usize_dec_eq(v_i_620_, v_stop_621_);
if (v___x_628_ == 0)
{
lean_object* v___x_629_; lean_object* v_toInductionSubgoal_630_; lean_object* v_ctorName_631_; lean_object* v_mvarId_632_; lean_object* v_subst_633_; lean_object* v___x_634_; uint8_t v___x_635_; lean_object* v___x_636_; uint8_t v___y_638_; 
v___x_629_ = lean_array_uget_borrowed(v_as_619_, v_i_620_);
v_toInductionSubgoal_630_ = lean_ctor_get(v___x_629_, 0);
v_ctorName_631_ = lean_ctor_get(v___x_629_, 1);
v_mvarId_632_ = lean_ctor_get(v_toInductionSubgoal_630_, 0);
v_subst_633_ = lean_ctor_get(v_toInductionSubgoal_630_, 2);
v___x_634_ = lean_unsigned_to_nat(1u);
v___x_635_ = lean_nat_dec_eq(v___x_616_, v___x_634_);
v___x_636_ = lean_box(0);
if (lean_obj_tag(v_ctorName_631_) == 0)
{
v___y_638_ = v___x_628_;
goto v___jp_637_;
}
else
{
v___y_638_ = v___x_635_;
goto v___jp_637_;
}
v___jp_637_:
{
lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___y_641_; lean_object* v___x_642_; 
v___x_639_ = lean_box(v___y_638_);
v___x_640_ = lean_box(v___x_635_);
lean_inc(v_ctorName_631_);
lean_inc(v_fst_618_);
lean_inc(v_fst_617_);
lean_inc(v_subst_633_);
lean_inc_n(v_mvarId_632_, 2);
lean_inc_ref(v_val_615_);
v___y_641_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__9___lam__1___boxed), 14, 9);
lean_closure_set(v___y_641_, 0, v___x_639_);
lean_closure_set(v___y_641_, 1, v_val_615_);
lean_closure_set(v___y_641_, 2, v_mvarId_632_);
lean_closure_set(v___y_641_, 3, v___x_640_);
lean_closure_set(v___y_641_, 4, v_subst_633_);
lean_closure_set(v___y_641_, 5, v_fst_617_);
lean_closure_set(v___y_641_, 6, v_fst_618_);
lean_closure_set(v___y_641_, 7, v___x_636_);
lean_closure_set(v___y_641_, 8, v_ctorName_631_);
v___x_642_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__6___redArg(v_mvarId_632_, v___y_641_, v___y_623_, v___y_624_, v___y_625_, v___y_626_);
if (lean_obj_tag(v___x_642_) == 0)
{
lean_object* v_a_643_; size_t v___x_644_; size_t v___x_645_; 
v_a_643_ = lean_ctor_get(v___x_642_, 0);
lean_inc(v_a_643_);
lean_dec_ref_known(v___x_642_, 1);
v___x_644_ = ((size_t)1ULL);
v___x_645_ = lean_usize_add(v_i_620_, v___x_644_);
v_i_620_ = v___x_645_;
v_b_622_ = v_a_643_;
goto _start;
}
else
{
lean_dec(v_fst_618_);
lean_dec(v_fst_617_);
lean_dec_ref(v_val_615_);
return v___x_642_;
}
}
}
else
{
lean_object* v___x_647_; 
lean_dec(v_fst_618_);
lean_dec(v_fst_617_);
lean_dec_ref(v_val_615_);
v___x_647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_647_, 0, v_b_622_);
return v___x_647_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__9___boxed(lean_object* v_val_648_, lean_object* v___x_649_, lean_object* v_fst_650_, lean_object* v_fst_651_, lean_object* v_as_652_, lean_object* v_i_653_, lean_object* v_stop_654_, lean_object* v_b_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_){
_start:
{
size_t v_i_boxed_661_; size_t v_stop_boxed_662_; lean_object* v_res_663_; 
v_i_boxed_661_ = lean_unbox_usize(v_i_653_);
lean_dec(v_i_653_);
v_stop_boxed_662_ = lean_unbox_usize(v_stop_654_);
lean_dec(v_stop_654_);
v_res_663_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__9(v_val_648_, v___x_649_, v_fst_650_, v_fst_651_, v_as_652_, v_i_boxed_661_, v_stop_boxed_662_, v_b_655_, v___y_656_, v___y_657_, v___y_658_, v___y_659_);
lean_dec(v___y_659_);
lean_dec_ref(v___y_658_);
lean_dec(v___y_657_);
lean_dec_ref(v___y_656_);
lean_dec_ref(v_as_652_);
lean_dec(v___x_649_);
return v_res_663_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__0(lean_object* v___x_667_, lean_object* v___x_668_, lean_object* v_fst_669_, lean_object* v___x_670_, lean_object* v_snd_671_, lean_object* v_val_672_, lean_object* v___x_673_, lean_object* v_xs_674_, lean_object* v___x_675_, lean_object* v_a_676_, lean_object* v_hyps_677_, lean_object* v_a_678_, uint8_t v___x_679_, lean_object* v_thmName_680_, lean_object* v_levelParams_681_, lean_object* v___x_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_){
_start:
{
lean_object* v___x_688_; 
lean_inc_ref(v___x_667_);
v___x_688_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_667_, v___x_668_, v___y_683_, v___y_684_, v___y_685_, v___y_686_);
if (lean_obj_tag(v___x_688_) == 0)
{
lean_object* v_a_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; 
v_a_689_ = lean_ctor_get(v___x_688_, 0);
lean_inc(v_a_689_);
lean_dec_ref_known(v___x_688_, 1);
v___x_690_ = l_Lean_Expr_mvarId_x21(v_a_689_);
v___x_691_ = lean_box(0);
lean_inc(v_fst_669_);
v___x_692_ = l_Lean_Meta_substEq(v___x_690_, v_fst_669_, v___x_691_, v___y_683_, v___y_684_, v___y_685_, v___y_686_);
if (lean_obj_tag(v___x_692_) == 0)
{
lean_object* v_a_693_; lean_object* v_fst_694_; lean_object* v_snd_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_699_; uint8_t v_isShared_700_; uint8_t v_isSharedCheck_782_; 
v_a_693_ = lean_ctor_get(v___x_692_, 0);
lean_inc(v_a_693_);
lean_dec_ref_known(v___x_692_, 1);
v_fst_694_ = lean_ctor_get(v_a_693_, 0);
lean_inc(v_fst_694_);
v_snd_695_ = lean_ctor_get(v_a_693_, 1);
lean_inc(v_snd_695_);
lean_dec(v_a_693_);
v___x_696_ = l_Lean_Meta_FVarSubst_apply(v_fst_694_, v___x_670_);
v___x_697_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4___redArg(v_snd_695_, v___x_696_, v___y_684_);
v_isSharedCheck_782_ = !lean_is_exclusive(v___x_697_);
if (v_isSharedCheck_782_ == 0)
{
lean_object* v_unused_783_; 
v_unused_783_ = lean_ctor_get(v___x_697_, 0);
lean_dec(v_unused_783_);
v___x_699_ = v___x_697_;
v_isShared_700_ = v_isSharedCheck_782_;
goto v_resetjp_698_;
}
else
{
lean_dec(v___x_697_);
v___x_699_ = lean_box(0);
v_isShared_700_ = v_isSharedCheck_782_;
goto v_resetjp_698_;
}
v_resetjp_698_:
{
lean_object* v___x_701_; lean_object* v___x_703_; 
v___x_701_ = ((lean_object*)(l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__0___closed__1));
if (v_isShared_700_ == 0)
{
lean_ctor_set_tag(v___x_699_, 1);
lean_ctor_set(v___x_699_, 0, v___x_667_);
v___x_703_ = v___x_699_;
goto v_reusejp_702_;
}
else
{
lean_object* v_reuseFailAlloc_781_; 
v_reuseFailAlloc_781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_781_, 0, v___x_667_);
v___x_703_ = v_reuseFailAlloc_781_;
goto v_reusejp_702_;
}
v_reusejp_702_:
{
lean_object* v___x_704_; 
v___x_704_ = l_Lean_MVarId_note(v_snd_671_, v___x_701_, v_a_689_, v___x_703_, v___y_683_, v___y_684_, v___y_685_, v___y_686_);
if (lean_obj_tag(v___x_704_) == 0)
{
lean_object* v_a_705_; lean_object* v_fst_706_; lean_object* v_snd_707_; lean_object* v___x_709_; uint8_t v_isShared_710_; uint8_t v_isSharedCheck_772_; 
v_a_705_ = lean_ctor_get(v___x_704_, 0);
lean_inc(v_a_705_);
lean_dec_ref_known(v___x_704_, 1);
v_fst_706_ = lean_ctor_get(v_a_705_, 0);
v_snd_707_ = lean_ctor_get(v_a_705_, 1);
v_isSharedCheck_772_ = !lean_is_exclusive(v_a_705_);
if (v_isSharedCheck_772_ == 0)
{
v___x_709_ = v_a_705_;
v_isShared_710_ = v_isSharedCheck_772_;
goto v_resetjp_708_;
}
else
{
lean_inc(v_snd_707_);
lean_inc(v_fst_706_);
lean_dec(v_a_705_);
v___x_709_ = lean_box(0);
v_isShared_710_ = v_isSharedCheck_772_;
goto v_resetjp_708_;
}
v_resetjp_708_:
{
lean_object* v_majorPos_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; uint8_t v___x_715_; lean_object* v___x_755_; lean_object* v___x_756_; 
v_majorPos_711_ = lean_ctor_get(v_val_672_, 1);
v___x_712_ = lean_array_get_borrowed(v___x_673_, v_xs_674_, v_majorPos_711_);
v___x_713_ = l_Lean_Expr_fvarId_x21(v___x_712_);
v___x_714_ = lean_mk_empty_array_with_capacity(v___x_675_);
v___x_715_ = 0;
v___x_755_ = lean_box(0);
v___x_756_ = l_Lean_MVarId_cases(v_snd_707_, v___x_713_, v___x_714_, v___x_715_, v___x_755_, v___y_683_, v___y_684_, v___y_685_, v___y_686_);
if (lean_obj_tag(v___x_756_) == 0)
{
lean_object* v_a_757_; lean_object* v___x_758_; uint8_t v___x_759_; 
v_a_757_ = lean_ctor_get(v___x_756_, 0);
lean_inc(v_a_757_);
lean_dec_ref_known(v___x_756_, 1);
v___x_758_ = lean_array_get_size(v_a_757_);
v___x_759_ = lean_nat_dec_lt(v___x_675_, v___x_758_);
if (v___x_759_ == 0)
{
lean_dec(v_a_757_);
lean_dec(v_fst_706_);
lean_dec_ref(v_val_672_);
lean_dec(v_fst_669_);
goto v___jp_716_;
}
else
{
lean_object* v___x_760_; size_t v___x_761_; size_t v___x_762_; lean_object* v___x_763_; 
v___x_760_ = lean_box(0);
v___x_761_ = ((size_t)0ULL);
v___x_762_ = lean_usize_of_nat(v___x_758_);
v___x_763_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__9(v_val_672_, v___x_682_, v_fst_706_, v_fst_669_, v_a_757_, v___x_761_, v___x_762_, v___x_760_, v___y_683_, v___y_684_, v___y_685_, v___y_686_);
lean_dec(v_a_757_);
if (lean_obj_tag(v___x_763_) == 0)
{
lean_dec_ref_known(v___x_763_, 1);
goto v___jp_716_;
}
else
{
lean_del_object(v___x_709_);
lean_dec(v_levelParams_681_);
lean_dec(v_thmName_680_);
lean_dec_ref(v_a_678_);
lean_dec_ref(v_a_676_);
lean_dec_ref(v_xs_674_);
return v___x_763_;
}
}
}
else
{
lean_object* v_a_764_; lean_object* v___x_766_; uint8_t v_isShared_767_; uint8_t v_isSharedCheck_771_; 
lean_del_object(v___x_709_);
lean_dec(v_fst_706_);
lean_dec(v_levelParams_681_);
lean_dec(v_thmName_680_);
lean_dec_ref(v_a_678_);
lean_dec_ref(v_a_676_);
lean_dec_ref(v_xs_674_);
lean_dec_ref(v_val_672_);
lean_dec(v_fst_669_);
v_a_764_ = lean_ctor_get(v___x_756_, 0);
v_isSharedCheck_771_ = !lean_is_exclusive(v___x_756_);
if (v_isSharedCheck_771_ == 0)
{
v___x_766_ = v___x_756_;
v_isShared_767_ = v_isSharedCheck_771_;
goto v_resetjp_765_;
}
else
{
lean_inc(v_a_764_);
lean_dec(v___x_756_);
v___x_766_ = lean_box(0);
v_isShared_767_ = v_isSharedCheck_771_;
goto v_resetjp_765_;
}
v_resetjp_765_:
{
lean_object* v___x_769_; 
if (v_isShared_767_ == 0)
{
v___x_769_ = v___x_766_;
goto v_reusejp_768_;
}
else
{
lean_object* v_reuseFailAlloc_770_; 
v_reuseFailAlloc_770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_770_, 0, v_a_764_);
v___x_769_ = v_reuseFailAlloc_770_;
goto v_reusejp_768_;
}
v_reusejp_768_:
{
return v___x_769_;
}
}
}
v___jp_716_:
{
lean_object* v___x_717_; lean_object* v_a_718_; lean_object* v___x_720_; uint8_t v_isShared_721_; uint8_t v_isSharedCheck_754_; 
v___x_717_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8___redArg(v_a_676_, v___y_684_);
v_a_718_ = lean_ctor_get(v___x_717_, 0);
v_isSharedCheck_754_ = !lean_is_exclusive(v___x_717_);
if (v_isSharedCheck_754_ == 0)
{
v___x_720_ = v___x_717_;
v_isShared_721_ = v_isSharedCheck_754_;
goto v_resetjp_719_;
}
else
{
lean_inc(v_a_718_);
lean_dec(v___x_717_);
v___x_720_ = lean_box(0);
v_isShared_721_ = v_isSharedCheck_754_;
goto v_resetjp_719_;
}
v_resetjp_719_:
{
lean_object* v___x_722_; uint8_t v___x_723_; lean_object* v___x_724_; 
v___x_722_ = l_Array_append___redArg(v_xs_674_, v_hyps_677_);
v___x_723_ = 1;
v___x_724_ = l_Lean_Meta_mkForallFVars(v___x_722_, v_a_678_, v___x_715_, v___x_679_, v___x_679_, v___x_723_, v___y_683_, v___y_684_, v___y_685_, v___y_686_);
if (lean_obj_tag(v___x_724_) == 0)
{
lean_object* v_a_725_; lean_object* v___x_726_; 
v_a_725_ = lean_ctor_get(v___x_724_, 0);
lean_inc(v_a_725_);
lean_dec_ref_known(v___x_724_, 1);
v___x_726_ = l_Lean_Meta_mkLambdaFVars(v___x_722_, v_a_718_, v___x_715_, v___x_679_, v___x_715_, v___x_679_, v___x_723_, v___y_683_, v___y_684_, v___y_685_, v___y_686_);
lean_dec_ref(v___x_722_);
if (lean_obj_tag(v___x_726_) == 0)
{
lean_object* v_a_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_731_; 
v_a_727_ = lean_ctor_get(v___x_726_, 0);
lean_inc(v_a_727_);
lean_dec_ref_known(v___x_726_, 1);
lean_inc(v_thmName_680_);
v___x_728_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_728_, 0, v_thmName_680_);
lean_ctor_set(v___x_728_, 1, v_levelParams_681_);
lean_ctor_set(v___x_728_, 2, v_a_725_);
v___x_729_ = lean_box(0);
if (v_isShared_710_ == 0)
{
lean_ctor_set_tag(v___x_709_, 1);
lean_ctor_set(v___x_709_, 1, v___x_729_);
lean_ctor_set(v___x_709_, 0, v_thmName_680_);
v___x_731_ = v___x_709_;
goto v_reusejp_730_;
}
else
{
lean_object* v_reuseFailAlloc_737_; 
v_reuseFailAlloc_737_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_737_, 0, v_thmName_680_);
lean_ctor_set(v_reuseFailAlloc_737_, 1, v___x_729_);
v___x_731_ = v_reuseFailAlloc_737_;
goto v_reusejp_730_;
}
v_reusejp_730_:
{
lean_object* v___x_732_; lean_object* v___x_734_; 
v___x_732_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_732_, 0, v___x_728_);
lean_ctor_set(v___x_732_, 1, v_a_727_);
lean_ctor_set(v___x_732_, 2, v___x_731_);
if (v_isShared_721_ == 0)
{
lean_ctor_set_tag(v___x_720_, 2);
lean_ctor_set(v___x_720_, 0, v___x_732_);
v___x_734_ = v___x_720_;
goto v_reusejp_733_;
}
else
{
lean_object* v_reuseFailAlloc_736_; 
v_reuseFailAlloc_736_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_736_, 0, v___x_732_);
v___x_734_ = v_reuseFailAlloc_736_;
goto v_reusejp_733_;
}
v_reusejp_733_:
{
lean_object* v___x_735_; 
v___x_735_ = l_Lean_addDecl(v___x_734_, v___x_715_, v___y_685_, v___y_686_);
return v___x_735_;
}
}
}
else
{
lean_object* v_a_738_; lean_object* v___x_740_; uint8_t v_isShared_741_; uint8_t v_isSharedCheck_745_; 
lean_dec(v_a_725_);
lean_del_object(v___x_720_);
lean_del_object(v___x_709_);
lean_dec(v_levelParams_681_);
lean_dec(v_thmName_680_);
v_a_738_ = lean_ctor_get(v___x_726_, 0);
v_isSharedCheck_745_ = !lean_is_exclusive(v___x_726_);
if (v_isSharedCheck_745_ == 0)
{
v___x_740_ = v___x_726_;
v_isShared_741_ = v_isSharedCheck_745_;
goto v_resetjp_739_;
}
else
{
lean_inc(v_a_738_);
lean_dec(v___x_726_);
v___x_740_ = lean_box(0);
v_isShared_741_ = v_isSharedCheck_745_;
goto v_resetjp_739_;
}
v_resetjp_739_:
{
lean_object* v___x_743_; 
if (v_isShared_741_ == 0)
{
v___x_743_ = v___x_740_;
goto v_reusejp_742_;
}
else
{
lean_object* v_reuseFailAlloc_744_; 
v_reuseFailAlloc_744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_744_, 0, v_a_738_);
v___x_743_ = v_reuseFailAlloc_744_;
goto v_reusejp_742_;
}
v_reusejp_742_:
{
return v___x_743_;
}
}
}
}
else
{
lean_object* v_a_746_; lean_object* v___x_748_; uint8_t v_isShared_749_; uint8_t v_isSharedCheck_753_; 
lean_dec_ref(v___x_722_);
lean_del_object(v___x_720_);
lean_dec(v_a_718_);
lean_del_object(v___x_709_);
lean_dec(v_levelParams_681_);
lean_dec(v_thmName_680_);
v_a_746_ = lean_ctor_get(v___x_724_, 0);
v_isSharedCheck_753_ = !lean_is_exclusive(v___x_724_);
if (v_isSharedCheck_753_ == 0)
{
v___x_748_ = v___x_724_;
v_isShared_749_ = v_isSharedCheck_753_;
goto v_resetjp_747_;
}
else
{
lean_inc(v_a_746_);
lean_dec(v___x_724_);
v___x_748_ = lean_box(0);
v_isShared_749_ = v_isSharedCheck_753_;
goto v_resetjp_747_;
}
v_resetjp_747_:
{
lean_object* v___x_751_; 
if (v_isShared_749_ == 0)
{
v___x_751_ = v___x_748_;
goto v_reusejp_750_;
}
else
{
lean_object* v_reuseFailAlloc_752_; 
v_reuseFailAlloc_752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_752_, 0, v_a_746_);
v___x_751_ = v_reuseFailAlloc_752_;
goto v_reusejp_750_;
}
v_reusejp_750_:
{
return v___x_751_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_773_; lean_object* v___x_775_; uint8_t v_isShared_776_; uint8_t v_isSharedCheck_780_; 
lean_dec(v_levelParams_681_);
lean_dec(v_thmName_680_);
lean_dec_ref(v_a_678_);
lean_dec_ref(v_a_676_);
lean_dec_ref(v_xs_674_);
lean_dec_ref(v_val_672_);
lean_dec(v_fst_669_);
v_a_773_ = lean_ctor_get(v___x_704_, 0);
v_isSharedCheck_780_ = !lean_is_exclusive(v___x_704_);
if (v_isSharedCheck_780_ == 0)
{
v___x_775_ = v___x_704_;
v_isShared_776_ = v_isSharedCheck_780_;
goto v_resetjp_774_;
}
else
{
lean_inc(v_a_773_);
lean_dec(v___x_704_);
v___x_775_ = lean_box(0);
v_isShared_776_ = v_isSharedCheck_780_;
goto v_resetjp_774_;
}
v_resetjp_774_:
{
lean_object* v___x_778_; 
if (v_isShared_776_ == 0)
{
v___x_778_ = v___x_775_;
goto v_reusejp_777_;
}
else
{
lean_object* v_reuseFailAlloc_779_; 
v_reuseFailAlloc_779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_779_, 0, v_a_773_);
v___x_778_ = v_reuseFailAlloc_779_;
goto v_reusejp_777_;
}
v_reusejp_777_:
{
return v___x_778_;
}
}
}
}
}
}
else
{
lean_object* v_a_784_; lean_object* v___x_786_; uint8_t v_isShared_787_; uint8_t v_isSharedCheck_791_; 
lean_dec(v_a_689_);
lean_dec(v_levelParams_681_);
lean_dec(v_thmName_680_);
lean_dec_ref(v_a_678_);
lean_dec_ref(v_a_676_);
lean_dec_ref(v_xs_674_);
lean_dec_ref(v_val_672_);
lean_dec(v_snd_671_);
lean_dec(v_fst_669_);
lean_dec_ref(v___x_667_);
v_a_784_ = lean_ctor_get(v___x_692_, 0);
v_isSharedCheck_791_ = !lean_is_exclusive(v___x_692_);
if (v_isSharedCheck_791_ == 0)
{
v___x_786_ = v___x_692_;
v_isShared_787_ = v_isSharedCheck_791_;
goto v_resetjp_785_;
}
else
{
lean_inc(v_a_784_);
lean_dec(v___x_692_);
v___x_786_ = lean_box(0);
v_isShared_787_ = v_isSharedCheck_791_;
goto v_resetjp_785_;
}
v_resetjp_785_:
{
lean_object* v___x_789_; 
if (v_isShared_787_ == 0)
{
v___x_789_ = v___x_786_;
goto v_reusejp_788_;
}
else
{
lean_object* v_reuseFailAlloc_790_; 
v_reuseFailAlloc_790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_790_, 0, v_a_784_);
v___x_789_ = v_reuseFailAlloc_790_;
goto v_reusejp_788_;
}
v_reusejp_788_:
{
return v___x_789_;
}
}
}
}
else
{
lean_object* v_a_792_; lean_object* v___x_794_; uint8_t v_isShared_795_; uint8_t v_isSharedCheck_799_; 
lean_dec(v_levelParams_681_);
lean_dec(v_thmName_680_);
lean_dec_ref(v_a_678_);
lean_dec_ref(v_a_676_);
lean_dec_ref(v_xs_674_);
lean_dec_ref(v_val_672_);
lean_dec(v_snd_671_);
lean_dec(v_fst_669_);
lean_dec_ref(v___x_667_);
v_a_792_ = lean_ctor_get(v___x_688_, 0);
v_isSharedCheck_799_ = !lean_is_exclusive(v___x_688_);
if (v_isSharedCheck_799_ == 0)
{
v___x_794_ = v___x_688_;
v_isShared_795_ = v_isSharedCheck_799_;
goto v_resetjp_793_;
}
else
{
lean_inc(v_a_792_);
lean_dec(v___x_688_);
v___x_794_ = lean_box(0);
v_isShared_795_ = v_isSharedCheck_799_;
goto v_resetjp_793_;
}
v_resetjp_793_:
{
lean_object* v___x_797_; 
if (v_isShared_795_ == 0)
{
v___x_797_ = v___x_794_;
goto v_reusejp_796_;
}
else
{
lean_object* v_reuseFailAlloc_798_; 
v_reuseFailAlloc_798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_798_, 0, v_a_792_);
v___x_797_ = v_reuseFailAlloc_798_;
goto v_reusejp_796_;
}
v_reusejp_796_:
{
return v___x_797_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__0___boxed(lean_object** _args){
lean_object* v___x_800_ = _args[0];
lean_object* v___x_801_ = _args[1];
lean_object* v_fst_802_ = _args[2];
lean_object* v___x_803_ = _args[3];
lean_object* v_snd_804_ = _args[4];
lean_object* v_val_805_ = _args[5];
lean_object* v___x_806_ = _args[6];
lean_object* v_xs_807_ = _args[7];
lean_object* v___x_808_ = _args[8];
lean_object* v_a_809_ = _args[9];
lean_object* v_hyps_810_ = _args[10];
lean_object* v_a_811_ = _args[11];
lean_object* v___x_812_ = _args[12];
lean_object* v_thmName_813_ = _args[13];
lean_object* v_levelParams_814_ = _args[14];
lean_object* v___x_815_ = _args[15];
lean_object* v___y_816_ = _args[16];
lean_object* v___y_817_ = _args[17];
lean_object* v___y_818_ = _args[18];
lean_object* v___y_819_ = _args[19];
lean_object* v___y_820_ = _args[20];
_start:
{
uint8_t v___x_17265__boxed_821_; lean_object* v_res_822_; 
v___x_17265__boxed_821_ = lean_unbox(v___x_812_);
v_res_822_ = l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__0(v___x_800_, v___x_801_, v_fst_802_, v___x_803_, v_snd_804_, v_val_805_, v___x_806_, v_xs_807_, v___x_808_, v_a_809_, v_hyps_810_, v_a_811_, v___x_17265__boxed_821_, v_thmName_813_, v_levelParams_814_, v___x_815_, v___y_816_, v___y_817_, v___y_818_, v___y_819_);
lean_dec(v___y_819_);
lean_dec_ref(v___y_818_);
lean_dec(v___y_817_);
lean_dec_ref(v___y_816_);
lean_dec(v___x_815_);
lean_dec_ref(v_hyps_810_);
lean_dec(v___x_808_);
lean_dec_ref(v___x_806_);
lean_dec_ref(v___x_803_);
return v_res_822_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__1___closed__1(void){
_start:
{
lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; 
v___x_824_ = ((lean_object*)(l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__1___closed__0));
v___x_825_ = lean_unsigned_to_nat(8u);
v___x_826_ = lean_unsigned_to_nat(34u);
v___x_827_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__9___lam__1___closed__1));
v___x_828_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__9___lam__1___closed__0));
v___x_829_ = l_mkPanicMessageWithDecl(v___x_828_, v___x_827_, v___x_826_, v___x_825_, v___x_824_);
return v___x_829_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__1___closed__3(void){
_start:
{
lean_object* v___x_831_; lean_object* v___x_832_; 
v___x_831_ = ((lean_object*)(l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__1___closed__2));
v___x_832_ = l_Lean_stringToMessageData(v___x_831_);
return v___x_832_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__1(lean_object* v___x_846_, lean_object* v___x_847_, lean_object* v_sparseCasesOnName_848_, lean_object* v___x_849_, lean_object* v_xs_850_, lean_object* v___x_851_, lean_object* v___x_852_, lean_object* v_val_853_, lean_object* v_thmName_854_, lean_object* v_levelParams_855_, lean_object* v_hyps_856_, lean_object* v_x_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_){
_start:
{
lean_object* v___x_863_; uint8_t v___x_864_; 
v___x_863_ = lean_array_get_size(v_hyps_856_);
v___x_864_ = lean_nat_dec_eq(v___x_863_, v___x_846_);
if (v___x_864_ == 0)
{
lean_object* v___x_865_; lean_object* v___x_866_; 
lean_dec_ref(v_hyps_856_);
lean_dec(v_levelParams_855_);
lean_dec(v_thmName_854_);
lean_dec_ref(v_val_853_);
lean_dec(v___x_852_);
lean_dec_ref(v___x_851_);
lean_dec_ref(v_xs_850_);
lean_dec(v___x_849_);
lean_dec(v_sparseCasesOnName_848_);
lean_dec_ref(v___x_847_);
v___x_865_ = lean_obj_once(&l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__1___closed__1, &l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__1___closed__1_once, _init_l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__1___closed__1);
v___x_866_ = l_panic___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__2(v___x_865_, v___y_858_, v___y_859_, v___y_860_, v___y_861_);
return v___x_866_;
}
else
{
lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___y_870_; lean_object* v___y_871_; lean_object* v___y_872_; lean_object* v___y_873_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; 
v___x_867_ = lean_unsigned_to_nat(0u);
v___x_868_ = lean_array_get(v___x_847_, v_hyps_856_, v___x_867_);
v___x_888_ = l_Lean_mkConst(v_sparseCasesOnName_848_, v___x_849_);
v___x_889_ = l_Lean_mkAppN(v___x_888_, v_xs_850_);
v___x_890_ = l_Lean_mkAppN(v___x_851_, v_hyps_856_);
v___x_891_ = l_Lean_Meta_mkEq(v___x_889_, v___x_890_, v___y_858_, v___y_859_, v___y_860_, v___y_861_);
if (lean_obj_tag(v___x_891_) == 0)
{
lean_object* v_a_892_; lean_object* v___x_893_; lean_object* v___x_894_; 
v_a_892_ = lean_ctor_get(v___x_891_, 0);
lean_inc_n(v_a_892_, 2);
lean_dec_ref_known(v___x_891_, 1);
v___x_893_ = lean_box(0);
v___x_894_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_892_, v___x_893_, v___y_858_, v___y_859_, v___y_860_, v___y_861_);
if (lean_obj_tag(v___x_894_) == 0)
{
lean_object* v_a_895_; lean_object* v___x_896_; lean_object* v___x_897_; 
v_a_895_ = lean_ctor_get(v___x_894_, 0);
lean_inc(v_a_895_);
lean_dec_ref_known(v___x_894_, 1);
v___x_896_ = l_Lean_Expr_mvarId_x21(v_a_895_);
lean_inc(v___y_861_);
lean_inc_ref(v___y_860_);
lean_inc(v___y_859_);
lean_inc_ref(v___y_858_);
lean_inc(v___x_868_);
v___x_897_ = lean_infer_type(v___x_868_, v___y_858_, v___y_859_, v___y_860_, v___y_861_);
if (lean_obj_tag(v___x_897_) == 0)
{
lean_object* v_a_898_; lean_object* v___x_899_; uint8_t v___x_900_; 
v_a_898_ = lean_ctor_get(v___x_897_, 0);
lean_inc(v_a_898_);
lean_dec_ref_known(v___x_897_, 1);
v___x_899_ = l_Lean_Expr_cleanupAnnotations(v_a_898_);
lean_dec(v_a_898_);
v___x_900_ = l_Lean_Expr_isApp(v___x_899_);
if (v___x_900_ == 0)
{
lean_dec_ref(v___x_899_);
lean_dec(v___x_896_);
lean_dec(v_a_895_);
lean_dec(v_a_892_);
lean_dec_ref(v_hyps_856_);
lean_dec(v_levelParams_855_);
lean_dec(v_thmName_854_);
lean_dec_ref(v_val_853_);
lean_dec(v___x_852_);
lean_dec_ref(v_xs_850_);
lean_dec_ref(v___x_847_);
v___y_870_ = v___y_858_;
v___y_871_ = v___y_859_;
v___y_872_ = v___y_860_;
v___y_873_ = v___y_861_;
goto v___jp_869_;
}
else
{
lean_object* v___x_901_; uint8_t v___x_902_; 
v___x_901_ = l_Lean_Expr_appFnCleanup___redArg(v___x_899_);
v___x_902_ = l_Lean_Expr_isApp(v___x_901_);
if (v___x_902_ == 0)
{
lean_dec_ref(v___x_901_);
lean_dec_ref(v___x_899_);
lean_dec(v___x_896_);
lean_dec(v_a_895_);
lean_dec(v_a_892_);
lean_dec_ref(v_hyps_856_);
lean_dec(v_levelParams_855_);
lean_dec(v_thmName_854_);
lean_dec_ref(v_val_853_);
lean_dec(v___x_852_);
lean_dec_ref(v_xs_850_);
lean_dec_ref(v___x_847_);
v___y_870_ = v___y_858_;
v___y_871_ = v___y_859_;
v___y_872_ = v___y_860_;
v___y_873_ = v___y_861_;
goto v___jp_869_;
}
else
{
lean_object* v___x_903_; lean_object* v___x_904_; uint8_t v___x_905_; 
v___x_903_ = l_Lean_Expr_appFnCleanup___redArg(v___x_901_);
v___x_904_ = ((lean_object*)(l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__1___closed__6));
v___x_905_ = l_Lean_Expr_isConstOf(v___x_903_, v___x_904_);
lean_dec_ref(v___x_903_);
if (v___x_905_ == 0)
{
lean_dec_ref(v___x_901_);
lean_dec_ref(v___x_899_);
lean_dec(v___x_896_);
lean_dec(v_a_895_);
lean_dec(v_a_892_);
lean_dec_ref(v_hyps_856_);
lean_dec(v_levelParams_855_);
lean_dec(v_thmName_854_);
lean_dec_ref(v_val_853_);
lean_dec(v___x_852_);
lean_dec_ref(v_xs_850_);
lean_dec_ref(v___x_847_);
v___y_870_ = v___y_858_;
v___y_871_ = v___y_859_;
v___y_872_ = v___y_860_;
v___y_873_ = v___y_861_;
goto v___jp_869_;
}
else
{
lean_object* v_arg_906_; lean_object* v_arg_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; 
v_arg_906_ = lean_ctor_get(v___x_899_, 1);
lean_inc_ref(v_arg_906_);
lean_dec_ref(v___x_899_);
v_arg_907_ = lean_ctor_get(v___x_901_, 1);
lean_inc_ref(v_arg_907_);
lean_dec_ref(v___x_901_);
v___x_908_ = ((lean_object*)(l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__1___closed__8));
v___x_909_ = ((lean_object*)(l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__1___closed__9));
lean_inc(v___x_852_);
v___x_910_ = l_Lean_mkConst(v___x_909_, v___x_852_);
v___x_911_ = ((lean_object*)(l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__1___closed__11));
v___x_912_ = l_Lean_MVarId_assertExt(v___x_896_, v___x_908_, v___x_910_, v_arg_906_, v___x_911_, v___y_858_, v___y_859_, v___y_860_, v___y_861_);
if (lean_obj_tag(v___x_912_) == 0)
{
lean_object* v_a_913_; lean_object* v___x_914_; 
v_a_913_ = lean_ctor_get(v___x_912_, 0);
lean_inc(v_a_913_);
lean_dec_ref_known(v___x_912_, 1);
v___x_914_ = l_Lean_Meta_intro1Core(v_a_913_, v___x_864_, v___y_858_, v___y_859_, v___y_860_, v___y_861_);
if (lean_obj_tag(v___x_914_) == 0)
{
lean_object* v_a_915_; lean_object* v_fst_916_; lean_object* v_snd_917_; lean_object* v___x_918_; 
v_a_915_ = lean_ctor_get(v___x_914_, 0);
lean_inc(v_a_915_);
lean_dec_ref_known(v___x_914_, 1);
v_fst_916_ = lean_ctor_get(v_a_915_, 0);
lean_inc(v_fst_916_);
v_snd_917_ = lean_ctor_get(v_a_915_, 1);
lean_inc(v_snd_917_);
lean_dec(v_a_915_);
v___x_918_ = l_Lean_Meta_intro1Core(v_snd_917_, v___x_864_, v___y_858_, v___y_859_, v___y_860_, v___y_861_);
if (lean_obj_tag(v___x_918_) == 0)
{
lean_object* v_a_919_; lean_object* v_fst_920_; lean_object* v_snd_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___f_926_; lean_object* v___x_927_; 
v_a_919_ = lean_ctor_get(v___x_918_, 0);
lean_inc(v_a_919_);
lean_dec_ref_known(v___x_918_, 1);
v_fst_920_ = lean_ctor_get(v_a_919_, 0);
lean_inc(v_fst_920_);
v_snd_921_ = lean_ctor_get(v_a_919_, 1);
lean_inc_n(v_snd_921_, 2);
lean_dec(v_a_919_);
v___x_922_ = l_Lean_mkConst(v___x_904_, v___x_852_);
v___x_923_ = l_Lean_mkFVar(v_fst_916_);
v___x_924_ = l_Lean_mkAppB(v___x_922_, v_arg_907_, v___x_923_);
v___x_925_ = lean_box(v___x_864_);
v___f_926_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__0___boxed), 21, 16);
lean_closure_set(v___f_926_, 0, v___x_924_);
lean_closure_set(v___f_926_, 1, v___x_893_);
lean_closure_set(v___f_926_, 2, v_fst_920_);
lean_closure_set(v___f_926_, 3, v___x_868_);
lean_closure_set(v___f_926_, 4, v_snd_921_);
lean_closure_set(v___f_926_, 5, v_val_853_);
lean_closure_set(v___f_926_, 6, v___x_847_);
lean_closure_set(v___f_926_, 7, v_xs_850_);
lean_closure_set(v___f_926_, 8, v___x_867_);
lean_closure_set(v___f_926_, 9, v_a_895_);
lean_closure_set(v___f_926_, 10, v_hyps_856_);
lean_closure_set(v___f_926_, 11, v_a_892_);
lean_closure_set(v___f_926_, 12, v___x_925_);
lean_closure_set(v___f_926_, 13, v_thmName_854_);
lean_closure_set(v___f_926_, 14, v_levelParams_855_);
lean_closure_set(v___f_926_, 15, v___x_863_);
v___x_927_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__6___redArg(v_snd_921_, v___f_926_, v___y_858_, v___y_859_, v___y_860_, v___y_861_);
return v___x_927_;
}
else
{
lean_object* v_a_928_; lean_object* v___x_930_; uint8_t v_isShared_931_; uint8_t v_isSharedCheck_935_; 
lean_dec(v_fst_916_);
lean_dec_ref(v_arg_907_);
lean_dec(v_a_895_);
lean_dec(v_a_892_);
lean_dec(v___x_868_);
lean_dec_ref(v_hyps_856_);
lean_dec(v_levelParams_855_);
lean_dec(v_thmName_854_);
lean_dec_ref(v_val_853_);
lean_dec(v___x_852_);
lean_dec_ref(v_xs_850_);
lean_dec_ref(v___x_847_);
v_a_928_ = lean_ctor_get(v___x_918_, 0);
v_isSharedCheck_935_ = !lean_is_exclusive(v___x_918_);
if (v_isSharedCheck_935_ == 0)
{
v___x_930_ = v___x_918_;
v_isShared_931_ = v_isSharedCheck_935_;
goto v_resetjp_929_;
}
else
{
lean_inc(v_a_928_);
lean_dec(v___x_918_);
v___x_930_ = lean_box(0);
v_isShared_931_ = v_isSharedCheck_935_;
goto v_resetjp_929_;
}
v_resetjp_929_:
{
lean_object* v___x_933_; 
if (v_isShared_931_ == 0)
{
v___x_933_ = v___x_930_;
goto v_reusejp_932_;
}
else
{
lean_object* v_reuseFailAlloc_934_; 
v_reuseFailAlloc_934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_934_, 0, v_a_928_);
v___x_933_ = v_reuseFailAlloc_934_;
goto v_reusejp_932_;
}
v_reusejp_932_:
{
return v___x_933_;
}
}
}
}
else
{
lean_object* v_a_936_; lean_object* v___x_938_; uint8_t v_isShared_939_; uint8_t v_isSharedCheck_943_; 
lean_dec_ref(v_arg_907_);
lean_dec(v_a_895_);
lean_dec(v_a_892_);
lean_dec(v___x_868_);
lean_dec_ref(v_hyps_856_);
lean_dec(v_levelParams_855_);
lean_dec(v_thmName_854_);
lean_dec_ref(v_val_853_);
lean_dec(v___x_852_);
lean_dec_ref(v_xs_850_);
lean_dec_ref(v___x_847_);
v_a_936_ = lean_ctor_get(v___x_914_, 0);
v_isSharedCheck_943_ = !lean_is_exclusive(v___x_914_);
if (v_isSharedCheck_943_ == 0)
{
v___x_938_ = v___x_914_;
v_isShared_939_ = v_isSharedCheck_943_;
goto v_resetjp_937_;
}
else
{
lean_inc(v_a_936_);
lean_dec(v___x_914_);
v___x_938_ = lean_box(0);
v_isShared_939_ = v_isSharedCheck_943_;
goto v_resetjp_937_;
}
v_resetjp_937_:
{
lean_object* v___x_941_; 
if (v_isShared_939_ == 0)
{
v___x_941_ = v___x_938_;
goto v_reusejp_940_;
}
else
{
lean_object* v_reuseFailAlloc_942_; 
v_reuseFailAlloc_942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_942_, 0, v_a_936_);
v___x_941_ = v_reuseFailAlloc_942_;
goto v_reusejp_940_;
}
v_reusejp_940_:
{
return v___x_941_;
}
}
}
}
else
{
lean_object* v_a_944_; lean_object* v___x_946_; uint8_t v_isShared_947_; uint8_t v_isSharedCheck_951_; 
lean_dec_ref(v_arg_907_);
lean_dec(v_a_895_);
lean_dec(v_a_892_);
lean_dec(v___x_868_);
lean_dec_ref(v_hyps_856_);
lean_dec(v_levelParams_855_);
lean_dec(v_thmName_854_);
lean_dec_ref(v_val_853_);
lean_dec(v___x_852_);
lean_dec_ref(v_xs_850_);
lean_dec_ref(v___x_847_);
v_a_944_ = lean_ctor_get(v___x_912_, 0);
v_isSharedCheck_951_ = !lean_is_exclusive(v___x_912_);
if (v_isSharedCheck_951_ == 0)
{
v___x_946_ = v___x_912_;
v_isShared_947_ = v_isSharedCheck_951_;
goto v_resetjp_945_;
}
else
{
lean_inc(v_a_944_);
lean_dec(v___x_912_);
v___x_946_ = lean_box(0);
v_isShared_947_ = v_isSharedCheck_951_;
goto v_resetjp_945_;
}
v_resetjp_945_:
{
lean_object* v___x_949_; 
if (v_isShared_947_ == 0)
{
v___x_949_ = v___x_946_;
goto v_reusejp_948_;
}
else
{
lean_object* v_reuseFailAlloc_950_; 
v_reuseFailAlloc_950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_950_, 0, v_a_944_);
v___x_949_ = v_reuseFailAlloc_950_;
goto v_reusejp_948_;
}
v_reusejp_948_:
{
return v___x_949_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_952_; lean_object* v___x_954_; uint8_t v_isShared_955_; uint8_t v_isSharedCheck_959_; 
lean_dec(v___x_896_);
lean_dec(v_a_895_);
lean_dec(v_a_892_);
lean_dec(v___x_868_);
lean_dec_ref(v_hyps_856_);
lean_dec(v_levelParams_855_);
lean_dec(v_thmName_854_);
lean_dec_ref(v_val_853_);
lean_dec(v___x_852_);
lean_dec_ref(v_xs_850_);
lean_dec_ref(v___x_847_);
v_a_952_ = lean_ctor_get(v___x_897_, 0);
v_isSharedCheck_959_ = !lean_is_exclusive(v___x_897_);
if (v_isSharedCheck_959_ == 0)
{
v___x_954_ = v___x_897_;
v_isShared_955_ = v_isSharedCheck_959_;
goto v_resetjp_953_;
}
else
{
lean_inc(v_a_952_);
lean_dec(v___x_897_);
v___x_954_ = lean_box(0);
v_isShared_955_ = v_isSharedCheck_959_;
goto v_resetjp_953_;
}
v_resetjp_953_:
{
lean_object* v___x_957_; 
if (v_isShared_955_ == 0)
{
v___x_957_ = v___x_954_;
goto v_reusejp_956_;
}
else
{
lean_object* v_reuseFailAlloc_958_; 
v_reuseFailAlloc_958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_958_, 0, v_a_952_);
v___x_957_ = v_reuseFailAlloc_958_;
goto v_reusejp_956_;
}
v_reusejp_956_:
{
return v___x_957_;
}
}
}
}
else
{
lean_object* v_a_960_; lean_object* v___x_962_; uint8_t v_isShared_963_; uint8_t v_isSharedCheck_967_; 
lean_dec(v_a_892_);
lean_dec(v___x_868_);
lean_dec_ref(v_hyps_856_);
lean_dec(v_levelParams_855_);
lean_dec(v_thmName_854_);
lean_dec_ref(v_val_853_);
lean_dec(v___x_852_);
lean_dec_ref(v_xs_850_);
lean_dec_ref(v___x_847_);
v_a_960_ = lean_ctor_get(v___x_894_, 0);
v_isSharedCheck_967_ = !lean_is_exclusive(v___x_894_);
if (v_isSharedCheck_967_ == 0)
{
v___x_962_ = v___x_894_;
v_isShared_963_ = v_isSharedCheck_967_;
goto v_resetjp_961_;
}
else
{
lean_inc(v_a_960_);
lean_dec(v___x_894_);
v___x_962_ = lean_box(0);
v_isShared_963_ = v_isSharedCheck_967_;
goto v_resetjp_961_;
}
v_resetjp_961_:
{
lean_object* v___x_965_; 
if (v_isShared_963_ == 0)
{
v___x_965_ = v___x_962_;
goto v_reusejp_964_;
}
else
{
lean_object* v_reuseFailAlloc_966_; 
v_reuseFailAlloc_966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_966_, 0, v_a_960_);
v___x_965_ = v_reuseFailAlloc_966_;
goto v_reusejp_964_;
}
v_reusejp_964_:
{
return v___x_965_;
}
}
}
}
else
{
lean_object* v_a_968_; lean_object* v___x_970_; uint8_t v_isShared_971_; uint8_t v_isSharedCheck_975_; 
lean_dec(v___x_868_);
lean_dec_ref(v_hyps_856_);
lean_dec(v_levelParams_855_);
lean_dec(v_thmName_854_);
lean_dec_ref(v_val_853_);
lean_dec(v___x_852_);
lean_dec_ref(v_xs_850_);
lean_dec_ref(v___x_847_);
v_a_968_ = lean_ctor_get(v___x_891_, 0);
v_isSharedCheck_975_ = !lean_is_exclusive(v___x_891_);
if (v_isSharedCheck_975_ == 0)
{
v___x_970_ = v___x_891_;
v_isShared_971_ = v_isSharedCheck_975_;
goto v_resetjp_969_;
}
else
{
lean_inc(v_a_968_);
lean_dec(v___x_891_);
v___x_970_ = lean_box(0);
v_isShared_971_ = v_isSharedCheck_975_;
goto v_resetjp_969_;
}
v_resetjp_969_:
{
lean_object* v___x_973_; 
if (v_isShared_971_ == 0)
{
v___x_973_ = v___x_970_;
goto v_reusejp_972_;
}
else
{
lean_object* v_reuseFailAlloc_974_; 
v_reuseFailAlloc_974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_974_, 0, v_a_968_);
v___x_973_ = v_reuseFailAlloc_974_;
goto v_reusejp_972_;
}
v_reusejp_972_:
{
return v___x_973_;
}
}
}
v___jp_869_:
{
lean_object* v___x_874_; 
lean_inc(v___y_873_);
lean_inc_ref(v___y_872_);
lean_inc(v___y_871_);
lean_inc_ref(v___y_870_);
v___x_874_ = lean_infer_type(v___x_868_, v___y_870_, v___y_871_, v___y_872_, v___y_873_);
if (lean_obj_tag(v___x_874_) == 0)
{
lean_object* v_a_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; 
v_a_875_ = lean_ctor_get(v___x_874_, 0);
lean_inc(v_a_875_);
lean_dec_ref_known(v___x_874_, 1);
v___x_876_ = lean_obj_once(&l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__1___closed__3, &l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__1___closed__3_once, _init_l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__1___closed__3);
v___x_877_ = l_Lean_MessageData_ofExpr(v_a_875_);
v___x_878_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_878_, 0, v___x_876_);
lean_ctor_set(v___x_878_, 1, v___x_877_);
v___x_879_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__3___redArg(v___x_878_, v___y_870_, v___y_871_, v___y_872_, v___y_873_);
return v___x_879_;
}
else
{
lean_object* v_a_880_; lean_object* v___x_882_; uint8_t v_isShared_883_; uint8_t v_isSharedCheck_887_; 
v_a_880_ = lean_ctor_get(v___x_874_, 0);
v_isSharedCheck_887_ = !lean_is_exclusive(v___x_874_);
if (v_isSharedCheck_887_ == 0)
{
v___x_882_ = v___x_874_;
v_isShared_883_ = v_isSharedCheck_887_;
goto v_resetjp_881_;
}
else
{
lean_inc(v_a_880_);
lean_dec(v___x_874_);
v___x_882_ = lean_box(0);
v_isShared_883_ = v_isSharedCheck_887_;
goto v_resetjp_881_;
}
v_resetjp_881_:
{
lean_object* v___x_885_; 
if (v_isShared_883_ == 0)
{
v___x_885_ = v___x_882_;
goto v_reusejp_884_;
}
else
{
lean_object* v_reuseFailAlloc_886_; 
v_reuseFailAlloc_886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_886_, 0, v_a_880_);
v___x_885_ = v_reuseFailAlloc_886_;
goto v_reusejp_884_;
}
v_reusejp_884_:
{
return v___x_885_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__1___boxed(lean_object** _args){
lean_object* v___x_976_ = _args[0];
lean_object* v___x_977_ = _args[1];
lean_object* v_sparseCasesOnName_978_ = _args[2];
lean_object* v___x_979_ = _args[3];
lean_object* v_xs_980_ = _args[4];
lean_object* v___x_981_ = _args[5];
lean_object* v___x_982_ = _args[6];
lean_object* v_val_983_ = _args[7];
lean_object* v_thmName_984_ = _args[8];
lean_object* v_levelParams_985_ = _args[9];
lean_object* v_hyps_986_ = _args[10];
lean_object* v_x_987_ = _args[11];
lean_object* v___y_988_ = _args[12];
lean_object* v___y_989_ = _args[13];
lean_object* v___y_990_ = _args[14];
lean_object* v___y_991_ = _args[15];
lean_object* v___y_992_ = _args[16];
_start:
{
lean_object* v_res_993_; 
v_res_993_ = l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__1(v___x_976_, v___x_977_, v_sparseCasesOnName_978_, v___x_979_, v_xs_980_, v___x_981_, v___x_982_, v_val_983_, v_thmName_984_, v_levelParams_985_, v_hyps_986_, v_x_987_, v___y_988_, v___y_989_, v___y_990_, v___y_991_);
lean_dec(v___y_991_);
lean_dec_ref(v___y_990_);
lean_dec(v___y_989_);
lean_dec_ref(v___y_988_);
lean_dec_ref(v_x_987_);
lean_dec(v___x_976_);
return v_res_993_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__2(lean_object* v___x_994_, lean_object* v_sparseCasesOnName_995_, lean_object* v___x_996_, lean_object* v___x_997_, lean_object* v_val_998_, lean_object* v_thmName_999_, lean_object* v_levelParams_1000_, lean_object* v_xs_1001_, lean_object* v_x_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_){
_start:
{
lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___f_1012_; lean_object* v___x_1013_; 
v___x_1008_ = lean_array_get_size(v_xs_1001_);
v___x_1009_ = lean_unsigned_to_nat(1u);
v___x_1010_ = lean_nat_sub(v___x_1008_, v___x_1009_);
v___x_1011_ = lean_array_get(v___x_994_, v_xs_1001_, v___x_1010_);
lean_dec(v___x_1010_);
lean_inc(v___x_1011_);
v___f_1012_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__1___boxed), 17, 10);
lean_closure_set(v___f_1012_, 0, v___x_1009_);
lean_closure_set(v___f_1012_, 1, v___x_994_);
lean_closure_set(v___f_1012_, 2, v_sparseCasesOnName_995_);
lean_closure_set(v___f_1012_, 3, v___x_996_);
lean_closure_set(v___f_1012_, 4, v_xs_1001_);
lean_closure_set(v___f_1012_, 5, v___x_1011_);
lean_closure_set(v___f_1012_, 6, v___x_997_);
lean_closure_set(v___f_1012_, 7, v_val_998_);
lean_closure_set(v___f_1012_, 8, v_thmName_999_);
lean_closure_set(v___f_1012_, 9, v_levelParams_1000_);
lean_inc(v___y_1006_);
lean_inc_ref(v___y_1005_);
lean_inc(v___y_1004_);
lean_inc_ref(v___y_1003_);
v___x_1013_ = lean_infer_type(v___x_1011_, v___y_1003_, v___y_1004_, v___y_1005_, v___y_1006_);
if (lean_obj_tag(v___x_1013_) == 0)
{
lean_object* v_a_1014_; uint8_t v___x_1015_; lean_object* v___x_1016_; 
v_a_1014_ = lean_ctor_get(v___x_1013_, 0);
lean_inc(v_a_1014_);
lean_dec_ref_known(v___x_1013_, 1);
v___x_1015_ = 0;
v___x_1016_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__10___redArg(v_a_1014_, v___f_1012_, v___x_1015_, v___y_1003_, v___y_1004_, v___y_1005_, v___y_1006_);
return v___x_1016_;
}
else
{
lean_object* v_a_1017_; lean_object* v___x_1019_; uint8_t v_isShared_1020_; uint8_t v_isSharedCheck_1024_; 
lean_dec_ref(v___f_1012_);
v_a_1017_ = lean_ctor_get(v___x_1013_, 0);
v_isSharedCheck_1024_ = !lean_is_exclusive(v___x_1013_);
if (v_isSharedCheck_1024_ == 0)
{
v___x_1019_ = v___x_1013_;
v_isShared_1020_ = v_isSharedCheck_1024_;
goto v_resetjp_1018_;
}
else
{
lean_inc(v_a_1017_);
lean_dec(v___x_1013_);
v___x_1019_ = lean_box(0);
v_isShared_1020_ = v_isSharedCheck_1024_;
goto v_resetjp_1018_;
}
v_resetjp_1018_:
{
lean_object* v___x_1022_; 
if (v_isShared_1020_ == 0)
{
v___x_1022_ = v___x_1019_;
goto v_reusejp_1021_;
}
else
{
lean_object* v_reuseFailAlloc_1023_; 
v_reuseFailAlloc_1023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1023_, 0, v_a_1017_);
v___x_1022_ = v_reuseFailAlloc_1023_;
goto v_reusejp_1021_;
}
v_reusejp_1021_:
{
return v___x_1022_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__2___boxed(lean_object* v___x_1025_, lean_object* v_sparseCasesOnName_1026_, lean_object* v___x_1027_, lean_object* v___x_1028_, lean_object* v_val_1029_, lean_object* v_thmName_1030_, lean_object* v_levelParams_1031_, lean_object* v_xs_1032_, lean_object* v_x_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_){
_start:
{
lean_object* v_res_1039_; 
v_res_1039_ = l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__2(v___x_1025_, v_sparseCasesOnName_1026_, v___x_1027_, v___x_1028_, v_val_1029_, v_thmName_1030_, v_levelParams_1031_, v_xs_1032_, v_x_1033_, v___y_1034_, v___y_1035_, v___y_1036_, v___y_1037_);
lean_dec(v___y_1037_);
lean_dec_ref(v___y_1036_);
lean_dec(v___y_1035_);
lean_dec_ref(v___y_1034_);
lean_dec_ref(v_x_1033_);
return v_res_1039_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__17___redArg(lean_object* v_ref_1040_, lean_object* v_msg_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_){
_start:
{
lean_object* v_toCold_1047_; lean_object* v_currRecDepth_1048_; lean_object* v_ref_1049_; uint16_t v_optionFlags_1050_; uint8_t v_suppressElabErrors_1051_; uint8_t v_checkDeprecated_1052_; uint8_t v_isRecordingDeps_1053_; lean_object* v_ref_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; 
v_toCold_1047_ = lean_ctor_get(v___y_1044_, 0);
v_currRecDepth_1048_ = lean_ctor_get(v___y_1044_, 1);
v_ref_1049_ = lean_ctor_get(v___y_1044_, 2);
v_optionFlags_1050_ = lean_ctor_get_uint16(v___y_1044_, sizeof(void*)*3);
v_suppressElabErrors_1051_ = lean_ctor_get_uint8(v___y_1044_, sizeof(void*)*3 + 2);
v_checkDeprecated_1052_ = lean_ctor_get_uint8(v___y_1044_, sizeof(void*)*3 + 3);
v_isRecordingDeps_1053_ = lean_ctor_get_uint8(v___y_1044_, sizeof(void*)*3 + 4);
v_ref_1054_ = l_Lean_replaceRef(v_ref_1040_, v_ref_1049_);
lean_inc(v_currRecDepth_1048_);
lean_inc_ref(v_toCold_1047_);
v___x_1055_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_1055_, 0, v_toCold_1047_);
lean_ctor_set(v___x_1055_, 1, v_currRecDepth_1048_);
lean_ctor_set(v___x_1055_, 2, v_ref_1054_);
lean_ctor_set_uint16(v___x_1055_, sizeof(void*)*3, v_optionFlags_1050_);
lean_ctor_set_uint8(v___x_1055_, sizeof(void*)*3 + 2, v_suppressElabErrors_1051_);
lean_ctor_set_uint8(v___x_1055_, sizeof(void*)*3 + 3, v_checkDeprecated_1052_);
lean_ctor_set_uint8(v___x_1055_, sizeof(void*)*3 + 4, v_isRecordingDeps_1053_);
v___x_1056_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__3___redArg(v_msg_1041_, v___y_1042_, v___y_1043_, v___x_1055_, v___y_1045_);
lean_dec_ref_known(v___x_1055_, 3);
return v___x_1056_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__17___redArg___boxed(lean_object* v_ref_1057_, lean_object* v_msg_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_){
_start:
{
lean_object* v_res_1064_; 
v_res_1064_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__17___redArg(v_ref_1057_, v_msg_1058_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_);
lean_dec(v___y_1062_);
lean_dec_ref(v___y_1061_);
lean_dec(v___y_1060_);
lean_dec_ref(v___y_1059_);
lean_dec(v_ref_1057_);
return v_res_1064_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__0(void){
_start:
{
lean_object* v___x_1065_; 
v___x_1065_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1065_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__1(void){
_start:
{
lean_object* v___x_1066_; lean_object* v___x_1067_; 
v___x_1066_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__0);
v___x_1067_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1067_, 0, v___x_1066_);
return v___x_1067_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__2(void){
_start:
{
lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; 
v___x_1068_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__1);
v___x_1069_ = lean_unsigned_to_nat(0u);
v___x_1070_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_1070_, 0, v___x_1069_);
lean_ctor_set(v___x_1070_, 1, v___x_1069_);
lean_ctor_set(v___x_1070_, 2, v___x_1069_);
lean_ctor_set(v___x_1070_, 3, v___x_1069_);
lean_ctor_set(v___x_1070_, 4, v___x_1068_);
lean_ctor_set(v___x_1070_, 5, v___x_1068_);
lean_ctor_set(v___x_1070_, 6, v___x_1068_);
lean_ctor_set(v___x_1070_, 7, v___x_1068_);
lean_ctor_set(v___x_1070_, 8, v___x_1068_);
lean_ctor_set(v___x_1070_, 9, v___x_1068_);
lean_ctor_set(v___x_1070_, 10, v___x_1068_);
return v___x_1070_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__3(void){
_start:
{
lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; 
v___x_1071_ = lean_unsigned_to_nat(32u);
v___x_1072_ = lean_mk_empty_array_with_capacity(v___x_1071_);
v___x_1073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1073_, 0, v___x_1072_);
return v___x_1073_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__4(void){
_start:
{
size_t v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; 
v___x_1074_ = ((size_t)5ULL);
v___x_1075_ = lean_unsigned_to_nat(0u);
v___x_1076_ = lean_unsigned_to_nat(32u);
v___x_1077_ = lean_mk_empty_array_with_capacity(v___x_1076_);
v___x_1078_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__3);
v___x_1079_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1079_, 0, v___x_1078_);
lean_ctor_set(v___x_1079_, 1, v___x_1077_);
lean_ctor_set(v___x_1079_, 2, v___x_1075_);
lean_ctor_set(v___x_1079_, 3, v___x_1075_);
lean_ctor_set_usize(v___x_1079_, 4, v___x_1074_);
return v___x_1079_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__5(void){
_start:
{
lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; 
v___x_1080_ = lean_box(1);
v___x_1081_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__4);
v___x_1082_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__1);
v___x_1083_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1083_, 0, v___x_1082_);
lean_ctor_set(v___x_1083_, 1, v___x_1081_);
lean_ctor_set(v___x_1083_, 2, v___x_1080_);
return v___x_1083_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__7(void){
_start:
{
lean_object* v___x_1085_; lean_object* v___x_1086_; 
v___x_1085_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__6));
v___x_1086_ = l_Lean_stringToMessageData(v___x_1085_);
return v___x_1086_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__9(void){
_start:
{
lean_object* v___x_1088_; lean_object* v___x_1089_; 
v___x_1088_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__8));
v___x_1089_ = l_Lean_stringToMessageData(v___x_1088_);
return v___x_1089_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__11(void){
_start:
{
lean_object* v___x_1091_; lean_object* v___x_1092_; 
v___x_1091_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__10));
v___x_1092_ = l_Lean_stringToMessageData(v___x_1091_);
return v___x_1092_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__13(void){
_start:
{
lean_object* v___x_1094_; lean_object* v___x_1095_; 
v___x_1094_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__12));
v___x_1095_ = l_Lean_stringToMessageData(v___x_1094_);
return v___x_1095_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__15(void){
_start:
{
lean_object* v___x_1097_; lean_object* v___x_1098_; 
v___x_1097_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__14));
v___x_1098_ = l_Lean_stringToMessageData(v___x_1097_);
return v___x_1098_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__17(void){
_start:
{
lean_object* v___x_1100_; lean_object* v___x_1101_; 
v___x_1100_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__16));
v___x_1101_ = l_Lean_stringToMessageData(v___x_1100_);
return v___x_1101_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__19(void){
_start:
{
lean_object* v___x_1103_; lean_object* v___x_1104_; 
v___x_1103_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__18));
v___x_1104_ = l_Lean_stringToMessageData(v___x_1103_);
return v___x_1104_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__21(void){
_start:
{
lean_object* v___x_1106_; lean_object* v___x_1107_; 
v___x_1106_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__20));
v___x_1107_ = l_Lean_stringToMessageData(v___x_1106_);
return v___x_1107_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__23(void){
_start:
{
lean_object* v___x_1109_; lean_object* v___x_1110_; 
v___x_1109_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__22));
v___x_1110_ = l_Lean_stringToMessageData(v___x_1109_);
return v___x_1110_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__25(void){
_start:
{
lean_object* v___x_1112_; lean_object* v___x_1113_; 
v___x_1112_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__24));
v___x_1113_ = l_Lean_stringToMessageData(v___x_1112_);
return v___x_1113_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__27(void){
_start:
{
lean_object* v___x_1115_; lean_object* v___x_1116_; 
v___x_1115_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__26));
v___x_1116_ = l_Lean_stringToMessageData(v___x_1115_);
return v___x_1116_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg(lean_object* v_msg_1117_, lean_object* v_declHint_1118_, lean_object* v___y_1119_){
_start:
{
lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v_env_1123_; uint8_t v___x_1124_; 
v___x_1121_ = lean_box(0);
v___x_1122_ = lean_st_ref_get(v___y_1119_);
v_env_1123_ = lean_ctor_get(v___x_1122_, 0);
lean_inc_ref(v_env_1123_);
lean_dec(v___x_1122_);
v___x_1124_ = l_Lean_Name_isAnonymous(v_declHint_1118_);
if (v___x_1124_ == 0)
{
uint8_t v_isExporting_1125_; 
v_isExporting_1125_ = lean_ctor_get_uint8(v_env_1123_, sizeof(void*)*13);
if (v_isExporting_1125_ == 0)
{
lean_object* v___x_1126_; 
lean_dec_ref(v_env_1123_);
lean_dec(v_declHint_1118_);
v___x_1126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1126_, 0, v_msg_1117_);
return v___x_1126_;
}
else
{
lean_object* v___x_1127_; uint8_t v___x_1128_; 
lean_inc_ref(v_env_1123_);
v___x_1127_ = l_Lean_Environment_setExporting(v_env_1123_, v___x_1124_);
lean_inc(v_declHint_1118_);
lean_inc_ref(v___x_1127_);
v___x_1128_ = l_Lean_Environment_contains(v___x_1127_, v_declHint_1118_, v_isExporting_1125_);
if (v___x_1128_ == 0)
{
lean_object* v___x_1129_; 
lean_dec_ref(v___x_1127_);
lean_dec_ref(v_env_1123_);
lean_dec(v_declHint_1118_);
v___x_1129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1129_, 0, v_msg_1117_);
return v___x_1129_;
}
else
{
lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v_c_1135_; lean_object* v___x_1136_; 
v___x_1130_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__2);
v___x_1131_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__5);
v___x_1132_ = l_Lean_Options_empty;
lean_inc_ref(v___x_1127_);
v___x_1133_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1133_, 0, v___x_1127_);
lean_ctor_set(v___x_1133_, 1, v___x_1130_);
lean_ctor_set(v___x_1133_, 2, v___x_1131_);
lean_ctor_set(v___x_1133_, 3, v___x_1132_);
lean_inc(v_declHint_1118_);
v___x_1134_ = l_Lean_MessageData_ofConstName(v_declHint_1118_, v___x_1124_);
v_c_1135_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1135_, 0, v___x_1133_);
lean_ctor_set(v_c_1135_, 1, v___x_1134_);
v___x_1136_ = l_Lean_Environment_getModuleIdxFor_x3f(v___x_1127_, v_declHint_1118_);
lean_dec_ref(v___x_1127_);
if (lean_obj_tag(v___x_1136_) == 0)
{
lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; 
lean_dec_ref(v_env_1123_);
lean_dec(v_declHint_1118_);
v___x_1137_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__7);
v___x_1138_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1138_, 0, v___x_1137_);
lean_ctor_set(v___x_1138_, 1, v_c_1135_);
v___x_1139_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__9);
v___x_1140_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1140_, 0, v___x_1138_);
lean_ctor_set(v___x_1140_, 1, v___x_1139_);
v___x_1141_ = l_Lean_MessageData_note(v___x_1140_);
v___x_1142_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1142_, 0, v_msg_1117_);
lean_ctor_set(v___x_1142_, 1, v___x_1141_);
v___x_1143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1143_, 0, v___x_1142_);
return v___x_1143_;
}
else
{
lean_object* v_val_1144_; lean_object* v___x_1146_; uint8_t v_isShared_1147_; uint8_t v_isSharedCheck_1197_; 
v_val_1144_ = lean_ctor_get(v___x_1136_, 0);
v_isSharedCheck_1197_ = !lean_is_exclusive(v___x_1136_);
if (v_isSharedCheck_1197_ == 0)
{
v___x_1146_ = v___x_1136_;
v_isShared_1147_ = v_isSharedCheck_1197_;
goto v_resetjp_1145_;
}
else
{
lean_inc(v_val_1144_);
lean_dec(v___x_1136_);
v___x_1146_ = lean_box(0);
v_isShared_1147_ = v_isSharedCheck_1197_;
goto v_resetjp_1145_;
}
v_resetjp_1145_:
{
lean_object* v___x_1148_; lean_object* v_modules_1149_; lean_object* v_moduleNames_1150_; lean_object* v_mod_1151_; uint8_t v___x_1166_; 
v___x_1148_ = l_Lean_Environment_header(v_env_1123_);
lean_dec_ref(v_env_1123_);
v_modules_1149_ = lean_ctor_get(v___x_1148_, 3);
lean_inc_ref(v_modules_1149_);
v_moduleNames_1150_ = lean_ctor_get(v___x_1148_, 4);
lean_inc_ref(v_moduleNames_1150_);
lean_dec_ref(v___x_1148_);
v_mod_1151_ = lean_array_get(v___x_1121_, v_moduleNames_1150_, v_val_1144_);
lean_dec_ref(v_moduleNames_1150_);
v___x_1166_ = l_Lean_isPrivateName(v_declHint_1118_);
lean_dec(v_declHint_1118_);
if (v___x_1166_ == 0)
{
lean_object* v___x_1167_; uint8_t v___x_1168_; 
v___x_1167_ = lean_array_get_size(v_modules_1149_);
v___x_1168_ = lean_nat_dec_lt(v_val_1144_, v___x_1167_);
if (v___x_1168_ == 0)
{
lean_dec_ref(v_modules_1149_);
lean_dec(v_val_1144_);
goto v___jp_1152_;
}
else
{
lean_object* v___x_1169_; lean_object* v_toImport_1170_; uint8_t v_isExported_1171_; 
v___x_1169_ = lean_array_fget(v_modules_1149_, v_val_1144_);
lean_dec(v_val_1144_);
lean_dec_ref(v_modules_1149_);
v_toImport_1170_ = lean_ctor_get(v___x_1169_, 0);
lean_inc_ref(v_toImport_1170_);
lean_dec(v___x_1169_);
v_isExported_1171_ = lean_ctor_get_uint8(v_toImport_1170_, sizeof(void*)*1 + 1);
lean_dec_ref(v_toImport_1170_);
if (v_isExported_1171_ == 0)
{
goto v___jp_1152_;
}
else
{
lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; 
lean_del_object(v___x_1146_);
v___x_1172_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__17);
v___x_1173_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1173_, 0, v___x_1172_);
lean_ctor_set(v___x_1173_, 1, v_c_1135_);
v___x_1174_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__19);
v___x_1175_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1175_, 0, v___x_1173_);
lean_ctor_set(v___x_1175_, 1, v___x_1174_);
v___x_1176_ = l_Lean_MessageData_ofName(v_mod_1151_);
lean_inc_ref(v___x_1176_);
v___x_1177_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1177_, 0, v___x_1175_);
lean_ctor_set(v___x_1177_, 1, v___x_1176_);
v___x_1178_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__21, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__21_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__21);
v___x_1179_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1179_, 0, v___x_1177_);
lean_ctor_set(v___x_1179_, 1, v___x_1178_);
v___x_1180_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1180_, 0, v___x_1179_);
lean_ctor_set(v___x_1180_, 1, v___x_1176_);
v___x_1181_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__23, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__23_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__23);
v___x_1182_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1182_, 0, v___x_1180_);
lean_ctor_set(v___x_1182_, 1, v___x_1181_);
v___x_1183_ = l_Lean_MessageData_note(v___x_1182_);
v___x_1184_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1184_, 0, v_msg_1117_);
lean_ctor_set(v___x_1184_, 1, v___x_1183_);
v___x_1185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1185_, 0, v___x_1184_);
return v___x_1185_;
}
}
}
else
{
lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; 
lean_dec_ref(v_modules_1149_);
lean_del_object(v___x_1146_);
lean_dec(v_val_1144_);
v___x_1186_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__7);
v___x_1187_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1187_, 0, v___x_1186_);
lean_ctor_set(v___x_1187_, 1, v_c_1135_);
v___x_1188_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__25, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__25_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__25);
v___x_1189_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1189_, 0, v___x_1187_);
lean_ctor_set(v___x_1189_, 1, v___x_1188_);
v___x_1190_ = l_Lean_MessageData_ofName(v_mod_1151_);
v___x_1191_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1191_, 0, v___x_1189_);
lean_ctor_set(v___x_1191_, 1, v___x_1190_);
v___x_1192_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__27, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__27_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__27);
v___x_1193_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1193_, 0, v___x_1191_);
lean_ctor_set(v___x_1193_, 1, v___x_1192_);
v___x_1194_ = l_Lean_MessageData_note(v___x_1193_);
v___x_1195_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1195_, 0, v_msg_1117_);
lean_ctor_set(v___x_1195_, 1, v___x_1194_);
v___x_1196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1196_, 0, v___x_1195_);
return v___x_1196_;
}
v___jp_1152_:
{
lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1164_; 
v___x_1153_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__11);
v___x_1154_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1154_, 0, v___x_1153_);
lean_ctor_set(v___x_1154_, 1, v_c_1135_);
v___x_1155_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__13);
v___x_1156_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1156_, 0, v___x_1154_);
lean_ctor_set(v___x_1156_, 1, v___x_1155_);
v___x_1157_ = l_Lean_MessageData_ofName(v_mod_1151_);
v___x_1158_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1158_, 0, v___x_1156_);
lean_ctor_set(v___x_1158_, 1, v___x_1157_);
v___x_1159_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__15);
v___x_1160_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1160_, 0, v___x_1158_);
lean_ctor_set(v___x_1160_, 1, v___x_1159_);
v___x_1161_ = l_Lean_MessageData_note(v___x_1160_);
v___x_1162_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1162_, 0, v_msg_1117_);
lean_ctor_set(v___x_1162_, 1, v___x_1161_);
if (v_isShared_1147_ == 0)
{
lean_ctor_set_tag(v___x_1146_, 0);
lean_ctor_set(v___x_1146_, 0, v___x_1162_);
v___x_1164_ = v___x_1146_;
goto v_reusejp_1163_;
}
else
{
lean_object* v_reuseFailAlloc_1165_; 
v_reuseFailAlloc_1165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1165_, 0, v___x_1162_);
v___x_1164_ = v_reuseFailAlloc_1165_;
goto v_reusejp_1163_;
}
v_reusejp_1163_:
{
return v___x_1164_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1198_; 
lean_dec_ref(v_env_1123_);
lean_dec(v_declHint_1118_);
v___x_1198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1198_, 0, v_msg_1117_);
return v___x_1198_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___boxed(lean_object* v_msg_1199_, lean_object* v_declHint_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_){
_start:
{
lean_object* v_res_1203_; 
v_res_1203_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg(v_msg_1199_, v_declHint_1200_, v___y_1201_);
lean_dec(v___y_1201_);
return v_res_1203_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16(lean_object* v_msg_1204_, lean_object* v_declHint_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_){
_start:
{
lean_object* v___x_1211_; lean_object* v_a_1212_; lean_object* v___x_1214_; uint8_t v_isShared_1215_; uint8_t v_isSharedCheck_1221_; 
v___x_1211_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg(v_msg_1204_, v_declHint_1205_, v___y_1209_);
v_a_1212_ = lean_ctor_get(v___x_1211_, 0);
v_isSharedCheck_1221_ = !lean_is_exclusive(v___x_1211_);
if (v_isSharedCheck_1221_ == 0)
{
v___x_1214_ = v___x_1211_;
v_isShared_1215_ = v_isSharedCheck_1221_;
goto v_resetjp_1213_;
}
else
{
lean_inc(v_a_1212_);
lean_dec(v___x_1211_);
v___x_1214_ = lean_box(0);
v_isShared_1215_ = v_isSharedCheck_1221_;
goto v_resetjp_1213_;
}
v_resetjp_1213_:
{
lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1219_; 
v___x_1216_ = l_Lean_unknownIdentifierMessageTag;
v___x_1217_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1217_, 0, v___x_1216_);
lean_ctor_set(v___x_1217_, 1, v_a_1212_);
if (v_isShared_1215_ == 0)
{
lean_ctor_set(v___x_1214_, 0, v___x_1217_);
v___x_1219_ = v___x_1214_;
goto v_reusejp_1218_;
}
else
{
lean_object* v_reuseFailAlloc_1220_; 
v_reuseFailAlloc_1220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1220_, 0, v___x_1217_);
v___x_1219_ = v_reuseFailAlloc_1220_;
goto v_reusejp_1218_;
}
v_reusejp_1218_:
{
return v___x_1219_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16___boxed(lean_object* v_msg_1222_, lean_object* v_declHint_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_){
_start:
{
lean_object* v_res_1229_; 
v_res_1229_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16(v_msg_1222_, v_declHint_1223_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_);
lean_dec(v___y_1227_);
lean_dec_ref(v___y_1226_);
lean_dec(v___y_1225_);
lean_dec_ref(v___y_1224_);
return v_res_1229_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13___redArg(lean_object* v_ref_1230_, lean_object* v_msg_1231_, lean_object* v_declHint_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_){
_start:
{
lean_object* v___x_1238_; lean_object* v_a_1239_; lean_object* v___x_1240_; 
v___x_1238_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16(v_msg_1231_, v_declHint_1232_, v___y_1233_, v___y_1234_, v___y_1235_, v___y_1236_);
v_a_1239_ = lean_ctor_get(v___x_1238_, 0);
lean_inc(v_a_1239_);
lean_dec_ref(v___x_1238_);
v___x_1240_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__17___redArg(v_ref_1230_, v_a_1239_, v___y_1233_, v___y_1234_, v___y_1235_, v___y_1236_);
return v___x_1240_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13___redArg___boxed(lean_object* v_ref_1241_, lean_object* v_msg_1242_, lean_object* v_declHint_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_){
_start:
{
lean_object* v_res_1249_; 
v_res_1249_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13___redArg(v_ref_1241_, v_msg_1242_, v_declHint_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_);
lean_dec(v___y_1247_);
lean_dec_ref(v___y_1246_);
lean_dec(v___y_1245_);
lean_dec_ref(v___y_1244_);
lean_dec(v_ref_1241_);
return v_res_1249_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_1251_; lean_object* v___x_1252_; 
v___x_1251_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6___redArg___closed__0));
v___x_1252_ = l_Lean_stringToMessageData(v___x_1251_);
return v___x_1252_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_1254_; lean_object* v___x_1255_; 
v___x_1254_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6___redArg___closed__2));
v___x_1255_ = l_Lean_stringToMessageData(v___x_1254_);
return v___x_1255_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6___redArg(lean_object* v_ref_1256_, lean_object* v_constName_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_){
_start:
{
lean_object* v___x_1263_; uint8_t v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; 
v___x_1263_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6___redArg___closed__1);
v___x_1264_ = 0;
lean_inc(v_constName_1257_);
v___x_1265_ = l_Lean_MessageData_ofConstName(v_constName_1257_, v___x_1264_);
v___x_1266_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1266_, 0, v___x_1263_);
lean_ctor_set(v___x_1266_, 1, v___x_1265_);
v___x_1267_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6___redArg___closed__3);
v___x_1268_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1268_, 0, v___x_1266_);
lean_ctor_set(v___x_1268_, 1, v___x_1267_);
v___x_1269_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13___redArg(v_ref_1256_, v___x_1268_, v_constName_1257_, v___y_1258_, v___y_1259_, v___y_1260_, v___y_1261_);
return v___x_1269_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6___redArg___boxed(lean_object* v_ref_1270_, lean_object* v_constName_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_){
_start:
{
lean_object* v_res_1277_; 
v_res_1277_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6___redArg(v_ref_1270_, v_constName_1271_, v___y_1272_, v___y_1273_, v___y_1274_, v___y_1275_);
lean_dec(v___y_1275_);
lean_dec_ref(v___y_1274_);
lean_dec(v___y_1273_);
lean_dec_ref(v___y_1272_);
lean_dec(v_ref_1270_);
return v_res_1277_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0___redArg(lean_object* v_constName_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_){
_start:
{
lean_object* v_ref_1284_; lean_object* v___x_1285_; 
v_ref_1284_ = lean_ctor_get(v___y_1281_, 2);
v___x_1285_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6___redArg(v_ref_1284_, v_constName_1278_, v___y_1279_, v___y_1280_, v___y_1281_, v___y_1282_);
return v___x_1285_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0___redArg___boxed(lean_object* v_constName_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_){
_start:
{
lean_object* v_res_1292_; 
v_res_1292_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0___redArg(v_constName_1286_, v___y_1287_, v___y_1288_, v___y_1289_, v___y_1290_);
lean_dec(v___y_1290_);
lean_dec_ref(v___y_1289_);
lean_dec(v___y_1288_);
lean_dec_ref(v___y_1287_);
return v_res_1292_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0(lean_object* v_constName_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_){
_start:
{
lean_object* v___x_1299_; lean_object* v_env_1300_; uint8_t v___x_1301_; lean_object* v___x_1302_; 
v___x_1299_ = lean_st_ref_get(v___y_1297_);
v_env_1300_ = lean_ctor_get(v___x_1299_, 0);
lean_inc_ref(v_env_1300_);
lean_dec(v___x_1299_);
v___x_1301_ = 0;
lean_inc(v_constName_1293_);
v___x_1302_ = l_Lean_Environment_findConstVal_x3f(v_env_1300_, v_constName_1293_, v___x_1301_);
if (lean_obj_tag(v___x_1302_) == 0)
{
lean_object* v___x_1303_; 
v___x_1303_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0___redArg(v_constName_1293_, v___y_1294_, v___y_1295_, v___y_1296_, v___y_1297_);
return v___x_1303_;
}
else
{
lean_object* v_val_1304_; lean_object* v___x_1306_; uint8_t v_isShared_1307_; uint8_t v_isSharedCheck_1311_; 
lean_dec(v_constName_1293_);
v_val_1304_ = lean_ctor_get(v___x_1302_, 0);
v_isSharedCheck_1311_ = !lean_is_exclusive(v___x_1302_);
if (v_isSharedCheck_1311_ == 0)
{
v___x_1306_ = v___x_1302_;
v_isShared_1307_ = v_isSharedCheck_1311_;
goto v_resetjp_1305_;
}
else
{
lean_inc(v_val_1304_);
lean_dec(v___x_1302_);
v___x_1306_ = lean_box(0);
v_isShared_1307_ = v_isSharedCheck_1311_;
goto v_resetjp_1305_;
}
v_resetjp_1305_:
{
lean_object* v___x_1309_; 
if (v_isShared_1307_ == 0)
{
lean_ctor_set_tag(v___x_1306_, 0);
v___x_1309_ = v___x_1306_;
goto v_reusejp_1308_;
}
else
{
lean_object* v_reuseFailAlloc_1310_; 
v_reuseFailAlloc_1310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1310_, 0, v_val_1304_);
v___x_1309_ = v_reuseFailAlloc_1310_;
goto v_reusejp_1308_;
}
v_reusejp_1308_:
{
return v___x_1309_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0___boxed(lean_object* v_constName_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_){
_start:
{
lean_object* v_res_1318_; 
v_res_1318_ = l_Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0(v_constName_1312_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_);
lean_dec(v___y_1316_);
lean_dec_ref(v___y_1315_);
lean_dec(v___y_1314_);
lean_dec_ref(v___y_1313_);
return v_res_1318_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__1(lean_object* v_a_1319_, lean_object* v_a_1320_){
_start:
{
if (lean_obj_tag(v_a_1319_) == 0)
{
lean_object* v___x_1321_; 
v___x_1321_ = l_List_reverse___redArg(v_a_1320_);
return v___x_1321_;
}
else
{
lean_object* v_head_1322_; lean_object* v_tail_1323_; lean_object* v___x_1325_; uint8_t v_isShared_1326_; uint8_t v_isSharedCheck_1332_; 
v_head_1322_ = lean_ctor_get(v_a_1319_, 0);
v_tail_1323_ = lean_ctor_get(v_a_1319_, 1);
v_isSharedCheck_1332_ = !lean_is_exclusive(v_a_1319_);
if (v_isSharedCheck_1332_ == 0)
{
v___x_1325_ = v_a_1319_;
v_isShared_1326_ = v_isSharedCheck_1332_;
goto v_resetjp_1324_;
}
else
{
lean_inc(v_tail_1323_);
lean_inc(v_head_1322_);
lean_dec(v_a_1319_);
v___x_1325_ = lean_box(0);
v_isShared_1326_ = v_isSharedCheck_1332_;
goto v_resetjp_1324_;
}
v_resetjp_1324_:
{
lean_object* v___x_1327_; lean_object* v___x_1329_; 
v___x_1327_ = l_Lean_mkLevelParam(v_head_1322_);
if (v_isShared_1326_ == 0)
{
lean_ctor_set(v___x_1325_, 1, v_a_1320_);
lean_ctor_set(v___x_1325_, 0, v___x_1327_);
v___x_1329_ = v___x_1325_;
goto v_reusejp_1328_;
}
else
{
lean_object* v_reuseFailAlloc_1331_; 
v_reuseFailAlloc_1331_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1331_, 0, v___x_1327_);
lean_ctor_set(v_reuseFailAlloc_1331_, 1, v_a_1320_);
v___x_1329_ = v_reuseFailAlloc_1331_;
goto v_reusejp_1328_;
}
v_reusejp_1328_:
{
v_a_1319_ = v_tail_1323_;
v_a_1320_ = v___x_1329_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___closed__1(void){
_start:
{
lean_object* v___x_1334_; lean_object* v___x_1335_; 
v___x_1334_ = ((lean_object*)(l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___closed__0));
v___x_1335_ = l_Lean_stringToMessageData(v___x_1334_);
return v___x_1335_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___closed__3(void){
_start:
{
lean_object* v___x_1337_; lean_object* v___x_1338_; 
v___x_1337_ = ((lean_object*)(l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___closed__2));
v___x_1338_ = l_Lean_stringToMessageData(v___x_1337_);
return v___x_1338_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize(lean_object* v_sparseCasesOnName_1339_, lean_object* v_thmName_1340_, lean_object* v_a_1341_, lean_object* v_a_1342_, lean_object* v_a_1343_, lean_object* v_a_1344_){
_start:
{
lean_object* v___x_1346_; lean_object* v___x_1347_; 
v___x_1346_ = l_Lean_instInhabitedExpr;
lean_inc(v_sparseCasesOnName_1339_);
v___x_1347_ = l_Lean_Meta_getSparseCasesOnInfo___redArg(v_sparseCasesOnName_1339_, v_a_1344_);
if (lean_obj_tag(v___x_1347_) == 0)
{
lean_object* v_a_1348_; 
v_a_1348_ = lean_ctor_get(v___x_1347_, 0);
lean_inc(v_a_1348_);
lean_dec_ref_known(v___x_1347_, 1);
if (lean_obj_tag(v_a_1348_) == 1)
{
lean_object* v_val_1349_; lean_object* v___x_1350_; 
v_val_1349_ = lean_ctor_get(v_a_1348_, 0);
lean_inc(v_val_1349_);
lean_dec_ref_known(v_a_1348_, 1);
lean_inc(v_sparseCasesOnName_1339_);
v___x_1350_ = l_Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0(v_sparseCasesOnName_1339_, v_a_1341_, v_a_1342_, v_a_1343_, v_a_1344_);
if (lean_obj_tag(v___x_1350_) == 0)
{
lean_object* v_a_1351_; lean_object* v_levelParams_1352_; lean_object* v_type_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___f_1356_; uint8_t v___x_1357_; lean_object* v___x_1358_; 
v_a_1351_ = lean_ctor_get(v___x_1350_, 0);
lean_inc(v_a_1351_);
lean_dec_ref_known(v___x_1350_, 1);
v_levelParams_1352_ = lean_ctor_get(v_a_1351_, 1);
lean_inc_n(v_levelParams_1352_, 2);
v_type_1353_ = lean_ctor_get(v_a_1351_, 2);
lean_inc_ref(v_type_1353_);
lean_dec(v_a_1351_);
v___x_1354_ = lean_box(0);
v___x_1355_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__1(v_levelParams_1352_, v___x_1354_);
v___f_1356_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__2___boxed), 14, 7);
lean_closure_set(v___f_1356_, 0, v___x_1346_);
lean_closure_set(v___f_1356_, 1, v_sparseCasesOnName_1339_);
lean_closure_set(v___f_1356_, 2, v___x_1355_);
lean_closure_set(v___f_1356_, 3, v___x_1354_);
lean_closure_set(v___f_1356_, 4, v_val_1349_);
lean_closure_set(v___f_1356_, 5, v_thmName_1340_);
lean_closure_set(v___f_1356_, 6, v_levelParams_1352_);
v___x_1357_ = 0;
v___x_1358_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__10___redArg(v_type_1353_, v___f_1356_, v___x_1357_, v_a_1341_, v_a_1342_, v_a_1343_, v_a_1344_);
return v___x_1358_;
}
else
{
lean_object* v_a_1359_; lean_object* v___x_1361_; uint8_t v_isShared_1362_; uint8_t v_isSharedCheck_1366_; 
lean_dec(v_val_1349_);
lean_dec(v_thmName_1340_);
lean_dec(v_sparseCasesOnName_1339_);
v_a_1359_ = lean_ctor_get(v___x_1350_, 0);
v_isSharedCheck_1366_ = !lean_is_exclusive(v___x_1350_);
if (v_isSharedCheck_1366_ == 0)
{
v___x_1361_ = v___x_1350_;
v_isShared_1362_ = v_isSharedCheck_1366_;
goto v_resetjp_1360_;
}
else
{
lean_inc(v_a_1359_);
lean_dec(v___x_1350_);
v___x_1361_ = lean_box(0);
v_isShared_1362_ = v_isSharedCheck_1366_;
goto v_resetjp_1360_;
}
v_resetjp_1360_:
{
lean_object* v___x_1364_; 
if (v_isShared_1362_ == 0)
{
v___x_1364_ = v___x_1361_;
goto v_reusejp_1363_;
}
else
{
lean_object* v_reuseFailAlloc_1365_; 
v_reuseFailAlloc_1365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1365_, 0, v_a_1359_);
v___x_1364_ = v_reuseFailAlloc_1365_;
goto v_reusejp_1363_;
}
v_reusejp_1363_:
{
return v___x_1364_;
}
}
}
}
else
{
lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; 
lean_dec(v_a_1348_);
lean_dec(v_thmName_1340_);
v___x_1367_ = lean_obj_once(&l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___closed__1, &l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___closed__1_once, _init_l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___closed__1);
v___x_1368_ = l_Lean_MessageData_ofName(v_sparseCasesOnName_1339_);
v___x_1369_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1369_, 0, v___x_1367_);
lean_ctor_set(v___x_1369_, 1, v___x_1368_);
v___x_1370_ = lean_obj_once(&l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___closed__3, &l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___closed__3_once, _init_l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___closed__3);
v___x_1371_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1371_, 0, v___x_1369_);
lean_ctor_set(v___x_1371_, 1, v___x_1370_);
v___x_1372_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__3___redArg(v___x_1371_, v_a_1341_, v_a_1342_, v_a_1343_, v_a_1344_);
return v___x_1372_;
}
}
else
{
lean_object* v_a_1373_; lean_object* v___x_1375_; uint8_t v_isShared_1376_; uint8_t v_isSharedCheck_1380_; 
lean_dec(v_thmName_1340_);
lean_dec(v_sparseCasesOnName_1339_);
v_a_1373_ = lean_ctor_get(v___x_1347_, 0);
v_isSharedCheck_1380_ = !lean_is_exclusive(v___x_1347_);
if (v_isSharedCheck_1380_ == 0)
{
v___x_1375_ = v___x_1347_;
v_isShared_1376_ = v_isSharedCheck_1380_;
goto v_resetjp_1374_;
}
else
{
lean_inc(v_a_1373_);
lean_dec(v___x_1347_);
v___x_1375_ = lean_box(0);
v_isShared_1376_ = v_isSharedCheck_1380_;
goto v_resetjp_1374_;
}
v_resetjp_1374_:
{
lean_object* v___x_1378_; 
if (v_isShared_1376_ == 0)
{
v___x_1378_ = v___x_1375_;
goto v_reusejp_1377_;
}
else
{
lean_object* v_reuseFailAlloc_1379_; 
v_reuseFailAlloc_1379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1379_, 0, v_a_1373_);
v___x_1378_ = v_reuseFailAlloc_1379_;
goto v_reusejp_1377_;
}
v_reusejp_1377_:
{
return v___x_1378_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___boxed(lean_object* v_sparseCasesOnName_1381_, lean_object* v_thmName_1382_, lean_object* v_a_1383_, lean_object* v_a_1384_, lean_object* v_a_1385_, lean_object* v_a_1386_, lean_object* v_a_1387_){
_start:
{
lean_object* v_res_1388_; 
v_res_1388_ = l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize(v_sparseCasesOnName_1381_, v_thmName_1382_, v_a_1383_, v_a_1384_, v_a_1385_, v_a_1386_);
lean_dec(v_a_1386_);
lean_dec_ref(v_a_1385_);
lean_dec(v_a_1384_);
lean_dec_ref(v_a_1383_);
return v_res_1388_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__3(lean_object* v_00_u03b1_1389_, lean_object* v_msg_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_){
_start:
{
lean_object* v___x_1396_; 
v___x_1396_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__3___redArg(v_msg_1390_, v___y_1391_, v___y_1392_, v___y_1393_, v___y_1394_);
return v___x_1396_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__3___boxed(lean_object* v_00_u03b1_1397_, lean_object* v_msg_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_){
_start:
{
lean_object* v_res_1404_; 
v_res_1404_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__3(v_00_u03b1_1397_, v_msg_1398_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_);
lean_dec(v___y_1402_);
lean_dec_ref(v___y_1401_);
lean_dec(v___y_1400_);
lean_dec_ref(v___y_1399_);
return v_res_1404_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4(lean_object* v_mvarId_1405_, lean_object* v_val_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_){
_start:
{
lean_object* v___x_1412_; 
v___x_1412_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4___redArg(v_mvarId_1405_, v_val_1406_, v___y_1408_);
return v___x_1412_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4___boxed(lean_object* v_mvarId_1413_, lean_object* v_val_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_){
_start:
{
lean_object* v_res_1420_; 
v_res_1420_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4(v_mvarId_1413_, v_val_1414_, v___y_1415_, v___y_1416_, v___y_1417_, v___y_1418_);
lean_dec(v___y_1418_);
lean_dec_ref(v___y_1417_);
lean_dec(v___y_1416_);
lean_dec_ref(v___y_1415_);
return v_res_1420_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0(lean_object* v_00_u03b1_1421_, lean_object* v_constName_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_){
_start:
{
lean_object* v___x_1428_; 
v___x_1428_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0___redArg(v_constName_1422_, v___y_1423_, v___y_1424_, v___y_1425_, v___y_1426_);
return v___x_1428_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1429_, lean_object* v_constName_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_){
_start:
{
lean_object* v_res_1436_; 
v_res_1436_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0(v_00_u03b1_1429_, v_constName_1430_, v___y_1431_, v___y_1432_, v___y_1433_, v___y_1434_);
lean_dec(v___y_1434_);
lean_dec_ref(v___y_1433_);
lean_dec(v___y_1432_);
lean_dec_ref(v___y_1431_);
return v_res_1436_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6(lean_object* v_00_u03b2_1437_, lean_object* v_x_1438_, lean_object* v_x_1439_, lean_object* v_x_1440_){
_start:
{
lean_object* v___x_1441_; 
v___x_1441_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6___redArg(v_x_1438_, v_x_1439_, v_x_1440_);
return v___x_1441_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6(lean_object* v_00_u03b1_1442_, lean_object* v_ref_1443_, lean_object* v_constName_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_){
_start:
{
lean_object* v___x_1450_; 
v___x_1450_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6___redArg(v_ref_1443_, v_constName_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_);
return v___x_1450_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6___boxed(lean_object* v_00_u03b1_1451_, lean_object* v_ref_1452_, lean_object* v_constName_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_){
_start:
{
lean_object* v_res_1459_; 
v_res_1459_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6(v_00_u03b1_1451_, v_ref_1452_, v_constName_1453_, v___y_1454_, v___y_1455_, v___y_1456_, v___y_1457_);
lean_dec(v___y_1457_);
lean_dec_ref(v___y_1456_);
lean_dec(v___y_1455_);
lean_dec_ref(v___y_1454_);
lean_dec(v_ref_1452_);
return v_res_1459_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6_spec__12(lean_object* v_00_u03b2_1460_, lean_object* v_x_1461_, size_t v_x_1462_, size_t v_x_1463_, lean_object* v_x_1464_, lean_object* v_x_1465_){
_start:
{
lean_object* v___x_1466_; 
v___x_1466_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6_spec__12___redArg(v_x_1461_, v_x_1462_, v_x_1463_, v_x_1464_, v_x_1465_);
return v___x_1466_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6_spec__12___boxed(lean_object* v_00_u03b2_1467_, lean_object* v_x_1468_, lean_object* v_x_1469_, lean_object* v_x_1470_, lean_object* v_x_1471_, lean_object* v_x_1472_){
_start:
{
size_t v_x_18633__boxed_1473_; size_t v_x_18634__boxed_1474_; lean_object* v_res_1475_; 
v_x_18633__boxed_1473_ = lean_unbox_usize(v_x_1469_);
lean_dec(v_x_1469_);
v_x_18634__boxed_1474_ = lean_unbox_usize(v_x_1470_);
lean_dec(v_x_1470_);
v_res_1475_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6_spec__12(v_00_u03b2_1467_, v_x_1468_, v_x_18633__boxed_1473_, v_x_18634__boxed_1474_, v_x_1471_, v_x_1472_);
return v_res_1475_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13(lean_object* v_00_u03b1_1476_, lean_object* v_ref_1477_, lean_object* v_msg_1478_, lean_object* v_declHint_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_){
_start:
{
lean_object* v___x_1485_; 
v___x_1485_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13___redArg(v_ref_1477_, v_msg_1478_, v_declHint_1479_, v___y_1480_, v___y_1481_, v___y_1482_, v___y_1483_);
return v___x_1485_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13___boxed(lean_object* v_00_u03b1_1486_, lean_object* v_ref_1487_, lean_object* v_msg_1488_, lean_object* v_declHint_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_){
_start:
{
lean_object* v_res_1495_; 
v_res_1495_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13(v_00_u03b1_1486_, v_ref_1487_, v_msg_1488_, v_declHint_1489_, v___y_1490_, v___y_1491_, v___y_1492_, v___y_1493_);
lean_dec(v___y_1493_);
lean_dec_ref(v___y_1492_);
lean_dec(v___y_1491_);
lean_dec_ref(v___y_1490_);
lean_dec(v_ref_1487_);
return v_res_1495_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6_spec__12_spec__16(lean_object* v_00_u03b2_1496_, lean_object* v_n_1497_, lean_object* v_k_1498_, lean_object* v_v_1499_){
_start:
{
lean_object* v___x_1500_; 
v___x_1500_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6_spec__12_spec__16___redArg(v_n_1497_, v_k_1498_, v_v_1499_);
return v___x_1500_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6_spec__12_spec__17(lean_object* v_00_u03b2_1501_, size_t v_depth_1502_, lean_object* v_keys_1503_, lean_object* v_vals_1504_, lean_object* v_heq_1505_, lean_object* v_i_1506_, lean_object* v_entries_1507_){
_start:
{
lean_object* v___x_1508_; 
v___x_1508_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6_spec__12_spec__17___redArg(v_depth_1502_, v_keys_1503_, v_vals_1504_, v_i_1506_, v_entries_1507_);
return v___x_1508_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6_spec__12_spec__17___boxed(lean_object* v_00_u03b2_1509_, lean_object* v_depth_1510_, lean_object* v_keys_1511_, lean_object* v_vals_1512_, lean_object* v_heq_1513_, lean_object* v_i_1514_, lean_object* v_entries_1515_){
_start:
{
size_t v_depth_boxed_1516_; lean_object* v_res_1517_; 
v_depth_boxed_1516_ = lean_unbox_usize(v_depth_1510_);
lean_dec(v_depth_1510_);
v_res_1517_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6_spec__12_spec__17(v_00_u03b2_1509_, v_depth_boxed_1516_, v_keys_1511_, v_vals_1512_, v_heq_1513_, v_i_1514_, v_entries_1515_);
lean_dec_ref(v_vals_1512_);
lean_dec_ref(v_keys_1511_);
return v_res_1517_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18(lean_object* v_msg_1518_, lean_object* v_declHint_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_){
_start:
{
lean_object* v___x_1525_; 
v___x_1525_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg(v_msg_1518_, v_declHint_1519_, v___y_1523_);
return v___x_1525_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___boxed(lean_object* v_msg_1526_, lean_object* v_declHint_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_){
_start:
{
lean_object* v_res_1533_; 
v_res_1533_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18(v_msg_1526_, v_declHint_1527_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_);
lean_dec(v___y_1531_);
lean_dec_ref(v___y_1530_);
lean_dec(v___y_1529_);
lean_dec_ref(v___y_1528_);
return v_res_1533_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__17(lean_object* v_00_u03b1_1534_, lean_object* v_ref_1535_, lean_object* v_msg_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_){
_start:
{
lean_object* v___x_1542_; 
v___x_1542_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__17___redArg(v_ref_1535_, v_msg_1536_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_);
return v___x_1542_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__17___boxed(lean_object* v_00_u03b1_1543_, lean_object* v_ref_1544_, lean_object* v_msg_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_){
_start:
{
lean_object* v_res_1551_; 
v_res_1551_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__17(v_00_u03b1_1543_, v_ref_1544_, v_msg_1545_, v___y_1546_, v___y_1547_, v___y_1548_, v___y_1549_);
lean_dec(v___y_1549_);
lean_dec_ref(v___y_1548_);
lean_dec(v___y_1547_);
lean_dec_ref(v___y_1546_);
lean_dec(v_ref_1544_);
return v_res_1551_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6_spec__12_spec__16_spec__20(lean_object* v_00_u03b2_1552_, lean_object* v_x_1553_, lean_object* v_x_1554_, lean_object* v_x_1555_, lean_object* v_x_1556_){
_start:
{
lean_object* v___x_1557_; 
v___x_1557_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6_spec__12_spec__16_spec__20___redArg(v_x_1553_, v_x_1554_, v_x_1555_, v_x_1556_);
return v___x_1557_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getSparseCasesOnEq(lean_object* v_sparseCasesOnName_1559_, lean_object* v_a_1560_, lean_object* v_a_1561_, lean_object* v_a_1562_, lean_object* v_a_1563_){
_start:
{
lean_object* v___x_1565_; lean_object* v_thmName_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; 
v___x_1565_ = ((lean_object*)(l_Lean_Meta_getSparseCasesOnEq___closed__0));
lean_inc_n(v_sparseCasesOnName_1559_, 2);
v_thmName_1566_ = l_Lean_Name_str___override(v_sparseCasesOnName_1559_, v___x_1565_);
lean_inc_n(v_thmName_1566_, 2);
v___x_1567_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___boxed), 7, 2);
lean_closure_set(v___x_1567_, 0, v_sparseCasesOnName_1559_);
lean_closure_set(v___x_1567_, 1, v_thmName_1566_);
v___x_1568_ = l_Lean_Meta_realizeConst(v_sparseCasesOnName_1559_, v_thmName_1566_, v___x_1567_, v_a_1560_, v_a_1561_, v_a_1562_, v_a_1563_);
if (lean_obj_tag(v___x_1568_) == 0)
{
lean_object* v___x_1570_; uint8_t v_isShared_1571_; uint8_t v_isSharedCheck_1575_; 
v_isSharedCheck_1575_ = !lean_is_exclusive(v___x_1568_);
if (v_isSharedCheck_1575_ == 0)
{
lean_object* v_unused_1576_; 
v_unused_1576_ = lean_ctor_get(v___x_1568_, 0);
lean_dec(v_unused_1576_);
v___x_1570_ = v___x_1568_;
v_isShared_1571_ = v_isSharedCheck_1575_;
goto v_resetjp_1569_;
}
else
{
lean_dec(v___x_1568_);
v___x_1570_ = lean_box(0);
v_isShared_1571_ = v_isSharedCheck_1575_;
goto v_resetjp_1569_;
}
v_resetjp_1569_:
{
lean_object* v___x_1573_; 
if (v_isShared_1571_ == 0)
{
lean_ctor_set(v___x_1570_, 0, v_thmName_1566_);
v___x_1573_ = v___x_1570_;
goto v_reusejp_1572_;
}
else
{
lean_object* v_reuseFailAlloc_1574_; 
v_reuseFailAlloc_1574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1574_, 0, v_thmName_1566_);
v___x_1573_ = v_reuseFailAlloc_1574_;
goto v_reusejp_1572_;
}
v_reusejp_1572_:
{
return v___x_1573_;
}
}
}
else
{
lean_object* v_a_1577_; lean_object* v___x_1579_; uint8_t v_isShared_1580_; uint8_t v_isSharedCheck_1584_; 
lean_dec(v_thmName_1566_);
v_a_1577_ = lean_ctor_get(v___x_1568_, 0);
v_isSharedCheck_1584_ = !lean_is_exclusive(v___x_1568_);
if (v_isSharedCheck_1584_ == 0)
{
v___x_1579_ = v___x_1568_;
v_isShared_1580_ = v_isSharedCheck_1584_;
goto v_resetjp_1578_;
}
else
{
lean_inc(v_a_1577_);
lean_dec(v___x_1568_);
v___x_1579_ = lean_box(0);
v_isShared_1580_ = v_isSharedCheck_1584_;
goto v_resetjp_1578_;
}
v_resetjp_1578_:
{
lean_object* v___x_1582_; 
if (v_isShared_1580_ == 0)
{
v___x_1582_ = v___x_1579_;
goto v_reusejp_1581_;
}
else
{
lean_object* v_reuseFailAlloc_1583_; 
v_reuseFailAlloc_1583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1583_, 0, v_a_1577_);
v___x_1582_ = v_reuseFailAlloc_1583_;
goto v_reusejp_1581_;
}
v_reusejp_1581_:
{
return v___x_1582_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getSparseCasesOnEq___boxed(lean_object* v_sparseCasesOnName_1585_, lean_object* v_a_1586_, lean_object* v_a_1587_, lean_object* v_a_1588_, lean_object* v_a_1589_, lean_object* v_a_1590_){
_start:
{
lean_object* v_res_1591_; 
v_res_1591_ = l_Lean_Meta_getSparseCasesOnEq(v_sparseCasesOnName_1585_, v_a_1586_, v_a_1587_, v_a_1588_, v_a_1589_);
lean_dec(v_a_1589_);
lean_dec_ref(v_a_1588_);
lean_dec(v_a_1587_);
lean_dec_ref(v_a_1586_);
return v_res_1591_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_isName(lean_object* v_env_1592_, lean_object* v_n_1593_){
_start:
{
if (lean_obj_tag(v_n_1593_) == 1)
{
lean_object* v_pre_1594_; lean_object* v_str_1595_; lean_object* v___x_1596_; uint8_t v___x_1597_; 
v_pre_1594_ = lean_ctor_get(v_n_1593_, 0);
lean_inc(v_pre_1594_);
v_str_1595_ = lean_ctor_get(v_n_1593_, 1);
lean_inc_ref(v_str_1595_);
lean_dec_ref_known(v_n_1593_, 2);
v___x_1596_ = ((lean_object*)(l_Lean_Meta_getSparseCasesOnEq___closed__0));
v___x_1597_ = lean_string_dec_eq(v_str_1595_, v___x_1596_);
lean_dec_ref(v_str_1595_);
if (v___x_1597_ == 0)
{
lean_dec(v_pre_1594_);
lean_dec_ref(v_env_1592_);
return v___x_1597_;
}
else
{
lean_object* v___x_1598_; 
v___x_1598_ = l_Lean_Meta_getSparseCasesOnInfoCore(v_env_1592_, v_pre_1594_);
if (lean_obj_tag(v___x_1598_) == 0)
{
uint8_t v___x_1599_; 
v___x_1599_ = 0;
return v___x_1599_;
}
else
{
lean_dec_ref_known(v___x_1598_, 1);
return v___x_1597_;
}
}
}
else
{
uint8_t v___x_1600_; 
lean_dec(v_n_1593_);
lean_dec_ref(v_env_1592_);
v___x_1600_ = 0;
return v___x_1600_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_isName___boxed(lean_object* v_env_1601_, lean_object* v_n_1602_){
_start:
{
uint8_t v_res_1603_; lean_object* v_r_1604_; 
v_res_1603_ = l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_isName(v_env_1601_, v_n_1602_);
v_r_1604_ = lean_box(v_res_1603_);
return v_r_1604_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_2164281220____hygCtx___hyg_2_(lean_object* v_x_1605_){
_start:
{
lean_object* v___x_1606_; uint8_t v___x_1607_; 
v___x_1606_ = ((lean_object*)(l_Lean_Meta_getSparseCasesOnEq___closed__0));
v___x_1607_ = lean_string_dec_eq(v_x_1605_, v___x_1606_);
return v___x_1607_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_2164281220____hygCtx___hyg_2____boxed(lean_object* v_x_1608_){
_start:
{
uint8_t v_res_1609_; lean_object* v_r_1610_; 
v_res_1609_ = l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_2164281220____hygCtx___hyg_2_(v_x_1608_);
lean_dec_ref(v_x_1608_);
v_r_1610_ = lean_box(v_res_1609_);
return v_r_1610_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_2164281220____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; 
v___f_1614_ = ((lean_object*)(l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_2164281220____hygCtx___hyg_2_));
v___x_1615_ = ((lean_object*)(l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_2164281220____hygCtx___hyg_2_));
v___x_1616_ = l_Lean_registerReservedNamePredicate(v___f_1614_, v___x_1615_);
return v___x_1616_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_2164281220____hygCtx___hyg_2____boxed(lean_object* v_a_1617_){
_start:
{
lean_object* v_res_1618_; 
v_res_1618_ = l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_2164281220____hygCtx___hyg_2_();
return v_res_1618_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2__spec__1(lean_object* v_msg_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_){
_start:
{
lean_object* v___f_1624_; lean_object* v___x_872__overap_1625_; lean_object* v___x_1626_; 
v___f_1624_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2__spec__1___closed__0));
v___x_872__overap_1625_ = lean_panic_fn_borrowed(v___f_1624_, v_msg_1620_);
lean_inc(v___y_1622_);
lean_inc_ref(v___y_1621_);
v___x_1626_ = lean_apply_3(v___x_872__overap_1625_, v___y_1621_, v___y_1622_, lean_box(0));
return v___x_1626_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2__spec__1___boxed(lean_object* v_msg_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_){
_start:
{
lean_object* v_res_1631_; 
v_res_1631_ = l_panic___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2__spec__1(v_msg_1627_, v___y_1628_, v___y_1629_);
lean_dec(v___y_1629_);
lean_dec_ref(v___y_1628_);
return v_res_1631_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1632_; lean_object* v___x_1633_; 
v___x_1632_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__0);
v___x_1633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1633_, 0, v___x_1632_);
return v___x_1633_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2__spec__0_spec__0___redArg(){
_start:
{
lean_object* v___x_1635_; 
v___x_1635_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__0);
return v___x_1635_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object* v___dummy_1636_){
_start:
{
lean_object* v_res_1637_; 
v_res_1637_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2__spec__0_spec__0___redArg();
return v_res_1637_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1638_; lean_object* v___x_1639_; 
v___x_1638_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__0);
v___x_1639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1639_, 0, v___x_1638_);
return v___x_1639_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; 
v___x_1640_ = lean_box(1);
v___x_1641_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__4);
v___x_1642_ = lean_obj_once(&l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_);
v___x_1643_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1643_, 0, v___x_1642_);
lean_ctor_set(v___x_1643_, 1, v___x_1641_);
lean_ctor_set(v___x_1643_, 2, v___x_1640_);
return v___x_1643_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__3_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; 
v___x_1646_ = lean_obj_once(&l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_);
v___x_1647_ = lean_unsigned_to_nat(0u);
v___x_1648_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_1648_, 0, v___x_1647_);
lean_ctor_set(v___x_1648_, 1, v___x_1647_);
lean_ctor_set(v___x_1648_, 2, v___x_1647_);
lean_ctor_set(v___x_1648_, 3, v___x_1647_);
lean_ctor_set(v___x_1648_, 4, v___x_1646_);
lean_ctor_set(v___x_1648_, 5, v___x_1646_);
lean_ctor_set(v___x_1648_, 6, v___x_1646_);
lean_ctor_set(v___x_1648_, 7, v___x_1646_);
lean_ctor_set(v___x_1648_, 8, v___x_1646_);
lean_ctor_set(v___x_1648_, 9, v___x_1646_);
lean_ctor_set(v___x_1648_, 10, v___x_1646_);
return v___x_1648_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1649_; 
v___x_1649_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2__spec__0_spec__0___redArg();
return v___x_1649_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1650_; lean_object* v___x_1651_; 
v___x_1650_ = lean_obj_once(&l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_);
v___x_1651_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1651_, 0, v___x_1650_);
lean_ctor_set(v___x_1651_, 1, v___x_1650_);
return v___x_1651_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__6_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; 
v___x_1652_ = lean_unsigned_to_nat(0u);
v___x_1653_ = lean_obj_once(&l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_);
v___x_1654_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1654_, 0, v___x_1653_);
lean_ctor_set(v___x_1654_, 1, v___x_1653_);
lean_ctor_set(v___x_1654_, 2, v___x_1652_);
return v___x_1654_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__7_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; 
v___x_1655_ = lean_obj_once(&l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__6_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__6_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__6_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_);
v___x_1656_ = lean_obj_once(&l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_);
v___x_1657_ = lean_obj_once(&l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_);
v___x_1658_ = lean_obj_once(&l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_);
v___x_1659_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_1659_, 0, v___x_1658_);
lean_ctor_set(v___x_1659_, 1, v___x_1657_);
lean_ctor_set(v___x_1659_, 2, v___x_1656_);
lean_ctor_set(v___x_1659_, 3, v___x_1657_);
lean_ctor_set(v___x_1659_, 4, v___x_1657_);
lean_ctor_set(v___x_1659_, 5, v___x_1657_);
lean_ctor_set(v___x_1659_, 6, v___x_1655_);
return v___x_1659_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__8_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1660_; lean_object* v___x_1661_; 
v___x_1660_ = lean_obj_once(&l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_);
v___x_1661_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1661_, 0, v___x_1660_);
lean_ctor_set(v___x_1661_, 1, v___x_1660_);
lean_ctor_set(v___x_1661_, 2, v___x_1660_);
lean_ctor_set(v___x_1661_, 3, v___x_1660_);
lean_ctor_set(v___x_1661_, 4, v___x_1660_);
return v___x_1661_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__11_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; 
v___x_1664_ = ((lean_object*)(l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__10_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_));
v___x_1665_ = lean_unsigned_to_nat(4u);
v___x_1666_ = lean_unsigned_to_nat(97u);
v___x_1667_ = ((lean_object*)(l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__9_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_));
v___x_1668_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__9___lam__1___closed__0));
v___x_1669_ = l_mkPanicMessageWithDecl(v___x_1668_, v___x_1667_, v___x_1666_, v___x_1665_, v___x_1664_);
return v___x_1669_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_(lean_object* v___x_1670_, lean_object* v_name_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_){
_start:
{
lean_object* v___x_1675_; lean_object* v_env_1676_; uint8_t v___x_1677_; 
v___x_1675_ = lean_st_ref_get(v___y_1673_);
v_env_1676_ = lean_ctor_get(v___x_1675_, 0);
lean_inc_ref(v_env_1676_);
lean_dec(v___x_1675_);
lean_inc(v_name_1671_);
v___x_1677_ = l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_isName(v_env_1676_, v_name_1671_);
if (v___x_1677_ == 0)
{
lean_object* v___x_1678_; lean_object* v___x_1679_; 
lean_dec(v_name_1671_);
lean_dec(v___x_1670_);
v___x_1678_ = lean_box(v___x_1677_);
v___x_1679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1679_, 0, v___x_1678_);
return v___x_1679_;
}
else
{
lean_object* v___x_1680_; uint8_t v___x_1681_; uint8_t v___x_1682_; uint8_t v___x_1683_; uint8_t v___x_1684_; lean_object* v___x_1685_; uint64_t v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; 
v___x_1680_ = l_Lean_Name_getPrefix(v_name_1671_);
v___x_1681_ = 0;
v___x_1682_ = 1;
v___x_1683_ = 0;
v___x_1684_ = 2;
v___x_1685_ = lean_alloc_ctor(0, 0, 21);
lean_ctor_set_uint8(v___x_1685_, 0, v___x_1681_);
lean_ctor_set_uint8(v___x_1685_, 1, v___x_1681_);
lean_ctor_set_uint8(v___x_1685_, 2, v___x_1681_);
lean_ctor_set_uint8(v___x_1685_, 3, v___x_1681_);
lean_ctor_set_uint8(v___x_1685_, 4, v___x_1681_);
lean_ctor_set_uint8(v___x_1685_, 5, v___x_1677_);
lean_ctor_set_uint8(v___x_1685_, 6, v___x_1677_);
lean_ctor_set_uint8(v___x_1685_, 7, v___x_1681_);
lean_ctor_set_uint8(v___x_1685_, 8, v___x_1677_);
lean_ctor_set_uint8(v___x_1685_, 9, v___x_1682_);
lean_ctor_set_uint8(v___x_1685_, 10, v___x_1683_);
lean_ctor_set_uint8(v___x_1685_, 11, v___x_1677_);
lean_ctor_set_uint8(v___x_1685_, 12, v___x_1677_);
lean_ctor_set_uint8(v___x_1685_, 13, v___x_1677_);
lean_ctor_set_uint8(v___x_1685_, 14, v___x_1684_);
lean_ctor_set_uint8(v___x_1685_, 15, v___x_1677_);
lean_ctor_set_uint8(v___x_1685_, 16, v___x_1677_);
lean_ctor_set_uint8(v___x_1685_, 17, v___x_1677_);
lean_ctor_set_uint8(v___x_1685_, 18, v___x_1677_);
lean_ctor_set_uint8(v___x_1685_, 19, v___x_1681_);
lean_ctor_set_uint8(v___x_1685_, 20, v___x_1677_);
v___x_1686_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_1685_);
v___x_1687_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1687_, 0, v___x_1685_);
lean_ctor_set_uint64(v___x_1687_, sizeof(void*)*1, v___x_1686_);
v___x_1688_ = lean_unsigned_to_nat(0u);
v___x_1689_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__13_spec__16_spec__18___redArg___closed__4);
v___x_1690_ = lean_obj_once(&l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_);
v___x_1691_ = ((lean_object*)(l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_));
v___x_1692_ = lean_box(0);
lean_inc(v___x_1670_);
v___x_1693_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1693_, 0, v___x_1687_);
lean_ctor_set(v___x_1693_, 1, v___x_1670_);
lean_ctor_set(v___x_1693_, 2, v___x_1690_);
lean_ctor_set(v___x_1693_, 3, v___x_1691_);
lean_ctor_set(v___x_1693_, 4, v___x_1692_);
lean_ctor_set(v___x_1693_, 5, v___x_1688_);
lean_ctor_set(v___x_1693_, 6, v___x_1692_);
lean_ctor_set_uint8(v___x_1693_, sizeof(void*)*7, v___x_1681_);
lean_ctor_set_uint8(v___x_1693_, sizeof(void*)*7 + 1, v___x_1681_);
lean_ctor_set_uint8(v___x_1693_, sizeof(void*)*7 + 2, v___x_1681_);
lean_ctor_set_uint8(v___x_1693_, sizeof(void*)*7 + 3, v___x_1677_);
v___x_1694_ = lean_obj_once(&l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__3_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__3_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__3_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_);
v___x_1695_ = lean_obj_once(&l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__7_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__7_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__7_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_);
v___x_1696_ = lean_obj_once(&l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__8_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__8_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__8_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_);
v___x_1697_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1697_, 0, v___x_1694_);
lean_ctor_set(v___x_1697_, 1, v___x_1695_);
lean_ctor_set(v___x_1697_, 2, v___x_1670_);
lean_ctor_set(v___x_1697_, 3, v___x_1689_);
lean_ctor_set(v___x_1697_, 4, v___x_1696_);
v___x_1698_ = lean_st_mk_ref(v___x_1697_);
v___x_1699_ = l_Lean_Meta_getSparseCasesOnEq(v___x_1680_, v___x_1693_, v___x_1698_, v___y_1672_, v___y_1673_);
lean_dec_ref_known(v___x_1693_, 7);
if (lean_obj_tag(v___x_1699_) == 0)
{
lean_object* v_a_1700_; lean_object* v___x_1702_; uint8_t v_isShared_1703_; uint8_t v_isSharedCheck_1712_; 
v_a_1700_ = lean_ctor_get(v___x_1699_, 0);
v_isSharedCheck_1712_ = !lean_is_exclusive(v___x_1699_);
if (v_isSharedCheck_1712_ == 0)
{
v___x_1702_ = v___x_1699_;
v_isShared_1703_ = v_isSharedCheck_1712_;
goto v_resetjp_1701_;
}
else
{
lean_inc(v_a_1700_);
lean_dec(v___x_1699_);
v___x_1702_ = lean_box(0);
v_isShared_1703_ = v_isSharedCheck_1712_;
goto v_resetjp_1701_;
}
v_resetjp_1701_:
{
lean_object* v___x_1704_; uint8_t v___x_1705_; 
v___x_1704_ = lean_st_ref_get(v___x_1698_);
lean_dec(v___x_1698_);
lean_dec(v___x_1704_);
v___x_1705_ = lean_name_eq(v_name_1671_, v_a_1700_);
lean_dec(v_a_1700_);
lean_dec(v_name_1671_);
if (v___x_1705_ == 0)
{
lean_object* v___x_1706_; lean_object* v___x_1707_; 
lean_del_object(v___x_1702_);
v___x_1706_ = lean_obj_once(&l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__11_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__11_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__11_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_);
v___x_1707_ = l_panic___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2__spec__1(v___x_1706_, v___y_1672_, v___y_1673_);
return v___x_1707_;
}
else
{
lean_object* v___x_1708_; lean_object* v___x_1710_; 
v___x_1708_ = lean_box(v___x_1677_);
if (v_isShared_1703_ == 0)
{
lean_ctor_set(v___x_1702_, 0, v___x_1708_);
v___x_1710_ = v___x_1702_;
goto v_reusejp_1709_;
}
else
{
lean_object* v_reuseFailAlloc_1711_; 
v_reuseFailAlloc_1711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1711_, 0, v___x_1708_);
v___x_1710_ = v_reuseFailAlloc_1711_;
goto v_reusejp_1709_;
}
v_reusejp_1709_:
{
return v___x_1710_;
}
}
}
}
else
{
lean_object* v_a_1713_; lean_object* v___x_1715_; uint8_t v_isShared_1716_; uint8_t v_isSharedCheck_1720_; 
lean_dec(v___x_1698_);
lean_dec(v_name_1671_);
v_a_1713_ = lean_ctor_get(v___x_1699_, 0);
v_isSharedCheck_1720_ = !lean_is_exclusive(v___x_1699_);
if (v_isSharedCheck_1720_ == 0)
{
v___x_1715_ = v___x_1699_;
v_isShared_1716_ = v_isSharedCheck_1720_;
goto v_resetjp_1714_;
}
else
{
lean_inc(v_a_1713_);
lean_dec(v___x_1699_);
v___x_1715_ = lean_box(0);
v_isShared_1716_ = v_isSharedCheck_1720_;
goto v_resetjp_1714_;
}
v_resetjp_1714_:
{
lean_object* v___x_1718_; 
if (v_isShared_1716_ == 0)
{
v___x_1718_ = v___x_1715_;
goto v_reusejp_1717_;
}
else
{
lean_object* v_reuseFailAlloc_1719_; 
v_reuseFailAlloc_1719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1719_, 0, v_a_1713_);
v___x_1718_ = v_reuseFailAlloc_1719_;
goto v_reusejp_1717_;
}
v_reusejp_1717_:
{
return v___x_1718_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2____boxed(lean_object* v___x_1721_, lean_object* v_name_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_){
_start:
{
lean_object* v_res_1726_; 
v_res_1726_ = l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_(v___x_1721_, v_name_1722_, v___y_1723_, v___y_1724_);
lean_dec(v___y_1724_);
lean_dec_ref(v___y_1723_);
return v_res_1726_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_1730_; lean_object* v___x_1731_; 
v___f_1730_ = ((lean_object*)(l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_));
v___x_1731_ = l_Lean_registerReservedNameAction(v___f_1730_);
return v___x_1731_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2____boxed(lean_object* v_a_1732_){
_start:
{
lean_object* v_res_1733_; 
v_res_1733_ = l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_();
return v_res_1733_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_00_u03b2_1734_){
_start:
{
lean_object* v___x_1735_; 
v___x_1735_ = lean_obj_once(&l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_);
return v___x_1735_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2__spec__0___redArg(){
_start:
{
lean_object* v___x_1737_; 
v___x_1737_ = lean_obj_once(&l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_);
return v___x_1737_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v___dummy_1738_){
_start:
{
lean_object* v_res_1739_; 
v_res_1739_ = l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2__spec__0___redArg();
return v_res_1739_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b2_1740_){
_start:
{
lean_object* v___x_1741_; 
v___x_1741_ = lean_obj_once(&l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_);
return v___x_1741_;
}
}
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Constructions_SparseCasesOn(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_HasNotBit(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Cases(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Refl(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Constructions_SparseCasesOnEq(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Constructions_SparseCasesOn(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_HasNotBit(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Cases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Refl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_2164281220____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Constructions_SparseCasesOnEq(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* initialize_Lean_Meta_Constructions_SparseCasesOn(uint8_t builtin);
lean_object* initialize_Lean_Meta_HasNotBit(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Cases(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Refl(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Constructions_SparseCasesOnEq(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Constructions_SparseCasesOn(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_HasNotBit(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Cases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Refl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Constructions_SparseCasesOnEq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Constructions_SparseCasesOnEq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Constructions_SparseCasesOnEq(builtin);
}
#ifdef __cplusplus
}
#endif
