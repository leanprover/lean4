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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
uint8_t l_Array_contains___redArg(lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getSparseCasesOnInfoCore(lean_object*, lean_object*);
lean_object* l_Lean_registerReservedNamePredicate(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Core_instInhabitedCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Name_getPrefix(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getSparseCasesOnInfo___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Environment_findConstVal_x3f(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* l_Lean_Meta_realizeConst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerReservedNameAction(lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instInhabitedMetaM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__2___closed__0 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__2___closed__0_value;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__6(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__7___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__9___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__9___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__9___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__9(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6_spec__12_spec__15_spec__18___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6_spec__12_spec__15___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6_spec__12___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6_spec__12___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6_spec__12___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6_spec__12_spec__16___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6_spec__12_spec__16___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "mkSparseCasesOnEq: not refutable "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8___lam__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8___lam__0___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8___lam__0___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "Lean.Meta.Constructions.SparseCasesOnEq"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8___lam__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8___lam__1___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 88, .m_capacity = 88, .m_length = 87, .m_data = "_private.Lean.Meta.Constructions.SparseCasesOnEq.0.Lean.Meta.getSparseCasesOnEq.realize"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8___lam__1___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8___lam__1___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 50, .m_capacity = 50, .m_length = 49, .m_data = "assertion violation: s.ctorName.isSome\n          "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8___lam__1___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8___lam__1___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8___lam__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8___lam__1___closed__3;
static const lean_closure_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8___lam__1___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8___lam__1___closed__4_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Init.Data.Option.BasicAux"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8___lam__1___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8___lam__1___closed__5_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8___lam__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Option.get!"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8___lam__1___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8___lam__1___closed__6_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8___lam__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "value is none"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8___lam__1___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8___lam__1___closed__7_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8___lam__1___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8___lam__1___closed__8;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8___lam__1(uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "h"};
static const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__0___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(176, 181, 207, 77, 197, 87, 68, 121)}};
static const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__15___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__0;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__1;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__2;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__3;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__4;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__13;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__14 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__14_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__15;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__19;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6_spec__12_spec__15(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6_spec__12_spec__16(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6_spec__12_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6_spec__12_spec__15_spec__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_getSparseCasesOnEq___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "else_eq"};
static const lean_object* l_Lean_Meta_getSparseCasesOnEq___closed__0 = (const lean_object*)&l_Lean_Meta_getSparseCasesOnEq___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_getSparseCasesOnEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getSparseCasesOnEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_isName(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_isName___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_3147303576____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_isName___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_3147303576____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_3147303576____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_3147303576____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_3147303576____hygCtx___hyg_2____boxed(lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2__spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instInhabitedCoreM___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2__spec__0___closed__0 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2__spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 137, .m_capacity = 137, .m_length = 136, .m_data = "_private.Lean.Meta.Constructions.SparseCasesOnEq.0.Lean.Meta.initFn._@.Lean.Meta.Constructions.SparseCasesOnEq.1213293720._hygCtx._hyg.2"};
static const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "assertion violation: name = name'\n    "};
static const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__3_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__3_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_;
static const lean_array_object l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__6_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__6_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__6_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__7_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__7_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__8_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__8_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__9_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__9_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__10_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__10_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2____boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__2(lean_object* v_msg_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_){
_start:
{
lean_object* v___f_8_; lean_object* v___x_13305__overap_9_; lean_object* v___x_10_; 
v___f_8_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__2___closed__0));
v___x_13305__overap_9_ = lean_panic_fn_borrowed(v___f_8_, v_msg_2_);
lean_inc(v___y_6_);
lean_inc_ref(v___y_5_);
lean_inc(v___y_4_);
lean_inc_ref(v___y_3_);
v___x_10_ = lean_apply_5(v___x_13305__overap_9_, v___y_3_, v___y_4_, v___y_5_, v___y_6_, lean_box(0));
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
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__5___redArg(lean_object* v_mvarId_18_, lean_object* v_x_19_, lean_object* v___y_20_, lean_object* v___y_21_, lean_object* v___y_22_, lean_object* v___y_23_){
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
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__5___redArg___boxed(lean_object* v_mvarId_42_, lean_object* v_x_43_, lean_object* v___y_44_, lean_object* v___y_45_, lean_object* v___y_46_, lean_object* v___y_47_, lean_object* v___y_48_){
_start:
{
lean_object* v_res_49_; 
v_res_49_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__5___redArg(v_mvarId_42_, v_x_43_, v___y_44_, v___y_45_, v___y_46_, v___y_47_);
lean_dec(v___y_47_);
lean_dec_ref(v___y_46_);
lean_dec(v___y_45_);
lean_dec_ref(v___y_44_);
return v_res_49_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__5(lean_object* v_00_u03b1_50_, lean_object* v_mvarId_51_, lean_object* v_x_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_, lean_object* v___y_56_){
_start:
{
lean_object* v___x_58_; 
v___x_58_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__5___redArg(v_mvarId_51_, v_x_52_, v___y_53_, v___y_54_, v___y_55_, v___y_56_);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__5___boxed(lean_object* v_00_u03b1_59_, lean_object* v_mvarId_60_, lean_object* v_x_61_, lean_object* v___y_62_, lean_object* v___y_63_, lean_object* v___y_64_, lean_object* v___y_65_, lean_object* v___y_66_){
_start:
{
lean_object* v_res_67_; 
v_res_67_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__5(v_00_u03b1_59_, v_mvarId_60_, v_x_61_, v___y_62_, v___y_63_, v___y_64_, v___y_65_);
lean_dec(v___y_65_);
lean_dec_ref(v___y_64_);
lean_dec(v___y_63_);
lean_dec_ref(v___y_62_);
return v_res_67_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__6(lean_object* v_msg_68_){
_start:
{
lean_object* v___x_69_; lean_object* v___x_70_; 
v___x_69_ = lean_box(0);
v___x_70_ = lean_panic_fn_borrowed(v___x_69_, v_msg_68_);
return v___x_70_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__7___redArg(lean_object* v_e_71_, lean_object* v___y_72_){
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
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__7___redArg___boxed(lean_object* v_e_96_, lean_object* v___y_97_, lean_object* v___y_98_){
_start:
{
lean_object* v_res_99_; 
v_res_99_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__7___redArg(v_e_96_, v___y_97_);
lean_dec(v___y_97_);
return v_res_99_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__7(lean_object* v_e_100_, lean_object* v___y_101_, lean_object* v___y_102_, lean_object* v___y_103_, lean_object* v___y_104_){
_start:
{
lean_object* v___x_106_; 
v___x_106_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__7___redArg(v_e_100_, v___y_102_);
return v___x_106_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__7___boxed(lean_object* v_e_107_, lean_object* v___y_108_, lean_object* v___y_109_, lean_object* v___y_110_, lean_object* v___y_111_, lean_object* v___y_112_){
_start:
{
lean_object* v_res_113_; 
v_res_113_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__7(v_e_107_, v___y_108_, v___y_109_, v___y_110_, v___y_111_);
lean_dec(v___y_111_);
lean_dec_ref(v___y_110_);
lean_dec(v___y_109_);
lean_dec_ref(v___y_108_);
return v_res_113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__9___redArg___lam__0(lean_object* v_k_114_, lean_object* v_b_115_, lean_object* v_c_116_, lean_object* v___y_117_, lean_object* v___y_118_, lean_object* v___y_119_, lean_object* v___y_120_){
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
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__9___redArg___lam__0___boxed(lean_object* v_k_123_, lean_object* v_b_124_, lean_object* v_c_125_, lean_object* v___y_126_, lean_object* v___y_127_, lean_object* v___y_128_, lean_object* v___y_129_, lean_object* v___y_130_){
_start:
{
lean_object* v_res_131_; 
v_res_131_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__9___redArg___lam__0(v_k_123_, v_b_124_, v_c_125_, v___y_126_, v___y_127_, v___y_128_, v___y_129_);
lean_dec(v___y_129_);
lean_dec_ref(v___y_128_);
lean_dec(v___y_127_);
lean_dec_ref(v___y_126_);
return v_res_131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__9___redArg(lean_object* v_type_132_, lean_object* v_k_133_, uint8_t v_cleanupAnnotations_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_, lean_object* v___y_138_){
_start:
{
lean_object* v___f_140_; uint8_t v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; 
v___f_140_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__9___redArg___lam__0___boxed), 8, 1);
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
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__9___redArg___boxed(lean_object* v_type_160_, lean_object* v_k_161_, lean_object* v_cleanupAnnotations_162_, lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_, lean_object* v___y_167_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_168_; lean_object* v_res_169_; 
v_cleanupAnnotations_boxed_168_ = lean_unbox(v_cleanupAnnotations_162_);
v_res_169_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__9___redArg(v_type_160_, v_k_161_, v_cleanupAnnotations_boxed_168_, v___y_163_, v___y_164_, v___y_165_, v___y_166_);
lean_dec(v___y_166_);
lean_dec_ref(v___y_165_);
lean_dec(v___y_164_);
lean_dec_ref(v___y_163_);
return v_res_169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__9(lean_object* v_00_u03b1_170_, lean_object* v_type_171_, lean_object* v_k_172_, uint8_t v_cleanupAnnotations_173_, lean_object* v___y_174_, lean_object* v___y_175_, lean_object* v___y_176_, lean_object* v___y_177_){
_start:
{
lean_object* v___x_179_; 
v___x_179_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__9___redArg(v_type_171_, v_k_172_, v_cleanupAnnotations_173_, v___y_174_, v___y_175_, v___y_176_, v___y_177_);
return v___x_179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__9___boxed(lean_object* v_00_u03b1_180_, lean_object* v_type_181_, lean_object* v_k_182_, lean_object* v_cleanupAnnotations_183_, lean_object* v___y_184_, lean_object* v___y_185_, lean_object* v___y_186_, lean_object* v___y_187_, lean_object* v___y_188_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_189_; lean_object* v_res_190_; 
v_cleanupAnnotations_boxed_189_ = lean_unbox(v_cleanupAnnotations_183_);
v_res_190_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__9(v_00_u03b1_180_, v_type_181_, v_k_182_, v_cleanupAnnotations_boxed_189_, v___y_184_, v___y_185_, v___y_186_, v___y_187_);
lean_dec(v___y_187_);
lean_dec_ref(v___y_186_);
lean_dec(v___y_185_);
lean_dec_ref(v___y_184_);
return v_res_190_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6_spec__12_spec__15_spec__18___redArg(lean_object* v_x_191_, lean_object* v_x_192_, lean_object* v_x_193_, lean_object* v_x_194_){
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6_spec__12_spec__15___redArg(lean_object* v_n_221_, lean_object* v_k_222_, lean_object* v_v_223_){
_start:
{
lean_object* v___x_224_; lean_object* v___x_225_; 
v___x_224_ = lean_unsigned_to_nat(0u);
v___x_225_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6_spec__12_spec__15_spec__18___redArg(v_n_221_, v___x_224_, v_k_222_, v_v_223_);
return v___x_225_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6_spec__12___redArg___closed__0(void){
_start:
{
lean_object* v___x_226_; 
v___x_226_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
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
lean_object* v_ks_278_; lean_object* v_vs_279_; lean_object* v___x_281_; uint8_t v_isShared_282_; uint8_t v_isSharedCheck_299_; 
v_ks_278_ = lean_ctor_get(v_x_227_, 0);
v_vs_279_ = lean_ctor_get(v_x_227_, 1);
v_isSharedCheck_299_ = !lean_is_exclusive(v_x_227_);
if (v_isSharedCheck_299_ == 0)
{
v___x_281_ = v_x_227_;
v_isShared_282_ = v_isSharedCheck_299_;
goto v_resetjp_280_;
}
else
{
lean_inc(v_vs_279_);
lean_inc(v_ks_278_);
lean_dec(v_x_227_);
v___x_281_ = lean_box(0);
v_isShared_282_ = v_isSharedCheck_299_;
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
lean_object* v_reuseFailAlloc_298_; 
v_reuseFailAlloc_298_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_298_, 0, v_ks_278_);
lean_ctor_set(v_reuseFailAlloc_298_, 1, v_vs_279_);
v___x_284_ = v_reuseFailAlloc_298_;
goto v_reusejp_283_;
}
v_reusejp_283_:
{
lean_object* v_newNode_285_; uint8_t v___y_287_; size_t v___x_293_; uint8_t v___x_294_; 
v_newNode_285_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6_spec__12_spec__15___redArg(v___x_284_, v_x_230_, v_x_231_);
v___x_293_ = ((size_t)7ULL);
v___x_294_ = lean_usize_dec_le(v___x_293_, v_x_229_);
if (v___x_294_ == 0)
{
lean_object* v___x_295_; lean_object* v___x_296_; uint8_t v___x_297_; 
v___x_295_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_285_);
v___x_296_ = lean_unsigned_to_nat(4u);
v___x_297_ = lean_nat_dec_lt(v___x_295_, v___x_296_);
lean_dec(v___x_295_);
v___y_287_ = v___x_297_;
goto v___jp_286_;
}
else
{
v___y_287_ = v___x_294_;
goto v___jp_286_;
}
v___jp_286_:
{
if (v___y_287_ == 0)
{
lean_object* v_ks_288_; lean_object* v_vs_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; 
v_ks_288_ = lean_ctor_get(v_newNode_285_, 0);
lean_inc_ref(v_ks_288_);
v_vs_289_ = lean_ctor_get(v_newNode_285_, 1);
lean_inc_ref(v_vs_289_);
lean_dec_ref(v_newNode_285_);
v___x_290_ = lean_unsigned_to_nat(0u);
v___x_291_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6_spec__12___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6_spec__12___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6_spec__12___redArg___closed__0);
v___x_292_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6_spec__12_spec__16___redArg(v_x_229_, v_ks_288_, v_vs_289_, v___x_290_, v___x_291_);
lean_dec_ref(v_vs_289_);
lean_dec_ref(v_ks_288_);
return v___x_292_;
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
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6_spec__12_spec__16___redArg(size_t v_depth_300_, lean_object* v_keys_301_, lean_object* v_vals_302_, lean_object* v_i_303_, lean_object* v_entries_304_){
_start:
{
lean_object* v___x_305_; uint8_t v___x_306_; 
v___x_305_ = lean_array_get_size(v_keys_301_);
v___x_306_ = lean_nat_dec_lt(v_i_303_, v___x_305_);
if (v___x_306_ == 0)
{
lean_dec(v_i_303_);
return v_entries_304_;
}
else
{
lean_object* v_k_307_; lean_object* v_v_308_; uint64_t v___x_309_; size_t v_h_310_; size_t v___x_311_; lean_object* v___x_312_; size_t v___x_313_; size_t v___x_314_; size_t v___x_315_; size_t v_h_316_; lean_object* v___x_317_; lean_object* v___x_318_; 
v_k_307_ = lean_array_fget_borrowed(v_keys_301_, v_i_303_);
v_v_308_ = lean_array_fget_borrowed(v_vals_302_, v_i_303_);
v___x_309_ = l_Lean_instHashableMVarId_hash(v_k_307_);
v_h_310_ = lean_uint64_to_usize(v___x_309_);
v___x_311_ = ((size_t)5ULL);
v___x_312_ = lean_unsigned_to_nat(1u);
v___x_313_ = ((size_t)1ULL);
v___x_314_ = lean_usize_sub(v_depth_300_, v___x_313_);
v___x_315_ = lean_usize_mul(v___x_311_, v___x_314_);
v_h_316_ = lean_usize_shift_right(v_h_310_, v___x_315_);
v___x_317_ = lean_nat_add(v_i_303_, v___x_312_);
lean_dec(v_i_303_);
lean_inc(v_v_308_);
lean_inc(v_k_307_);
v___x_318_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6_spec__12___redArg(v_entries_304_, v_h_316_, v_depth_300_, v_k_307_, v_v_308_);
v_i_303_ = v___x_317_;
v_entries_304_ = v___x_318_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6_spec__12_spec__16___redArg___boxed(lean_object* v_depth_320_, lean_object* v_keys_321_, lean_object* v_vals_322_, lean_object* v_i_323_, lean_object* v_entries_324_){
_start:
{
size_t v_depth_boxed_325_; lean_object* v_res_326_; 
v_depth_boxed_325_ = lean_unbox_usize(v_depth_320_);
lean_dec(v_depth_320_);
v_res_326_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6_spec__12_spec__16___redArg(v_depth_boxed_325_, v_keys_321_, v_vals_322_, v_i_323_, v_entries_324_);
lean_dec_ref(v_vals_322_);
lean_dec_ref(v_keys_321_);
return v_res_326_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6_spec__12___redArg___boxed(lean_object* v_x_327_, lean_object* v_x_328_, lean_object* v_x_329_, lean_object* v_x_330_, lean_object* v_x_331_){
_start:
{
size_t v_x_18882__boxed_332_; size_t v_x_18883__boxed_333_; lean_object* v_res_334_; 
v_x_18882__boxed_332_ = lean_unbox_usize(v_x_328_);
lean_dec(v_x_328_);
v_x_18883__boxed_333_ = lean_unbox_usize(v_x_329_);
lean_dec(v_x_329_);
v_res_334_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6_spec__12___redArg(v_x_327_, v_x_18882__boxed_332_, v_x_18883__boxed_333_, v_x_330_, v_x_331_);
return v_res_334_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6___redArg(lean_object* v_x_335_, lean_object* v_x_336_, lean_object* v_x_337_){
_start:
{
uint64_t v___x_338_; size_t v___x_339_; size_t v___x_340_; lean_object* v___x_341_; 
v___x_338_ = l_Lean_instHashableMVarId_hash(v_x_336_);
v___x_339_ = lean_uint64_to_usize(v___x_338_);
v___x_340_ = ((size_t)1ULL);
v___x_341_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6_spec__12___redArg(v_x_335_, v___x_339_, v___x_340_, v_x_336_, v_x_337_);
return v___x_341_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4___redArg(lean_object* v_mvarId_342_, lean_object* v_val_343_, lean_object* v___y_344_){
_start:
{
lean_object* v___x_346_; lean_object* v_mctx_347_; lean_object* v_cache_348_; lean_object* v_zetaDeltaFVarIds_349_; lean_object* v_postponed_350_; lean_object* v_diag_351_; lean_object* v___x_353_; uint8_t v_isShared_354_; uint8_t v_isSharedCheck_380_; 
v___x_346_ = lean_st_ref_take(v___y_344_);
v_mctx_347_ = lean_ctor_get(v___x_346_, 0);
v_cache_348_ = lean_ctor_get(v___x_346_, 1);
v_zetaDeltaFVarIds_349_ = lean_ctor_get(v___x_346_, 2);
v_postponed_350_ = lean_ctor_get(v___x_346_, 3);
v_diag_351_ = lean_ctor_get(v___x_346_, 4);
v_isSharedCheck_380_ = !lean_is_exclusive(v___x_346_);
if (v_isSharedCheck_380_ == 0)
{
v___x_353_ = v___x_346_;
v_isShared_354_ = v_isSharedCheck_380_;
goto v_resetjp_352_;
}
else
{
lean_inc(v_diag_351_);
lean_inc(v_postponed_350_);
lean_inc(v_zetaDeltaFVarIds_349_);
lean_inc(v_cache_348_);
lean_inc(v_mctx_347_);
lean_dec(v___x_346_);
v___x_353_ = lean_box(0);
v_isShared_354_ = v_isSharedCheck_380_;
goto v_resetjp_352_;
}
v_resetjp_352_:
{
lean_object* v_depth_355_; lean_object* v_levelAssignDepth_356_; lean_object* v_lmvarCounter_357_; lean_object* v_mvarCounter_358_; lean_object* v_lDecls_359_; lean_object* v_decls_360_; lean_object* v_userNames_361_; lean_object* v_lAssignment_362_; lean_object* v_eAssignment_363_; lean_object* v_dAssignment_364_; lean_object* v_instanceTypedMVars_365_; lean_object* v___x_367_; uint8_t v_isShared_368_; uint8_t v_isSharedCheck_379_; 
v_depth_355_ = lean_ctor_get(v_mctx_347_, 0);
v_levelAssignDepth_356_ = lean_ctor_get(v_mctx_347_, 1);
v_lmvarCounter_357_ = lean_ctor_get(v_mctx_347_, 2);
v_mvarCounter_358_ = lean_ctor_get(v_mctx_347_, 3);
v_lDecls_359_ = lean_ctor_get(v_mctx_347_, 4);
v_decls_360_ = lean_ctor_get(v_mctx_347_, 5);
v_userNames_361_ = lean_ctor_get(v_mctx_347_, 6);
v_lAssignment_362_ = lean_ctor_get(v_mctx_347_, 7);
v_eAssignment_363_ = lean_ctor_get(v_mctx_347_, 8);
v_dAssignment_364_ = lean_ctor_get(v_mctx_347_, 9);
v_instanceTypedMVars_365_ = lean_ctor_get(v_mctx_347_, 10);
v_isSharedCheck_379_ = !lean_is_exclusive(v_mctx_347_);
if (v_isSharedCheck_379_ == 0)
{
v___x_367_ = v_mctx_347_;
v_isShared_368_ = v_isSharedCheck_379_;
goto v_resetjp_366_;
}
else
{
lean_inc(v_instanceTypedMVars_365_);
lean_inc(v_dAssignment_364_);
lean_inc(v_eAssignment_363_);
lean_inc(v_lAssignment_362_);
lean_inc(v_userNames_361_);
lean_inc(v_decls_360_);
lean_inc(v_lDecls_359_);
lean_inc(v_mvarCounter_358_);
lean_inc(v_lmvarCounter_357_);
lean_inc(v_levelAssignDepth_356_);
lean_inc(v_depth_355_);
lean_dec(v_mctx_347_);
v___x_367_ = lean_box(0);
v_isShared_368_ = v_isSharedCheck_379_;
goto v_resetjp_366_;
}
v_resetjp_366_:
{
lean_object* v___x_369_; lean_object* v___x_371_; 
v___x_369_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6___redArg(v_eAssignment_363_, v_mvarId_342_, v_val_343_);
if (v_isShared_368_ == 0)
{
lean_ctor_set(v___x_367_, 8, v___x_369_);
v___x_371_ = v___x_367_;
goto v_reusejp_370_;
}
else
{
lean_object* v_reuseFailAlloc_378_; 
v_reuseFailAlloc_378_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_378_, 0, v_depth_355_);
lean_ctor_set(v_reuseFailAlloc_378_, 1, v_levelAssignDepth_356_);
lean_ctor_set(v_reuseFailAlloc_378_, 2, v_lmvarCounter_357_);
lean_ctor_set(v_reuseFailAlloc_378_, 3, v_mvarCounter_358_);
lean_ctor_set(v_reuseFailAlloc_378_, 4, v_lDecls_359_);
lean_ctor_set(v_reuseFailAlloc_378_, 5, v_decls_360_);
lean_ctor_set(v_reuseFailAlloc_378_, 6, v_userNames_361_);
lean_ctor_set(v_reuseFailAlloc_378_, 7, v_lAssignment_362_);
lean_ctor_set(v_reuseFailAlloc_378_, 8, v___x_369_);
lean_ctor_set(v_reuseFailAlloc_378_, 9, v_dAssignment_364_);
lean_ctor_set(v_reuseFailAlloc_378_, 10, v_instanceTypedMVars_365_);
v___x_371_ = v_reuseFailAlloc_378_;
goto v_reusejp_370_;
}
v_reusejp_370_:
{
lean_object* v___x_373_; 
if (v_isShared_354_ == 0)
{
lean_ctor_set(v___x_353_, 0, v___x_371_);
v___x_373_ = v___x_353_;
goto v_reusejp_372_;
}
else
{
lean_object* v_reuseFailAlloc_377_; 
v_reuseFailAlloc_377_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_377_, 0, v___x_371_);
lean_ctor_set(v_reuseFailAlloc_377_, 1, v_cache_348_);
lean_ctor_set(v_reuseFailAlloc_377_, 2, v_zetaDeltaFVarIds_349_);
lean_ctor_set(v_reuseFailAlloc_377_, 3, v_postponed_350_);
lean_ctor_set(v_reuseFailAlloc_377_, 4, v_diag_351_);
v___x_373_ = v_reuseFailAlloc_377_;
goto v_reusejp_372_;
}
v_reusejp_372_:
{
lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; 
v___x_374_ = lean_st_ref_put(v___y_344_, v___x_373_);
v___x_375_ = lean_box(0);
v___x_376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_376_, 0, v___x_375_);
return v___x_376_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4___redArg___boxed(lean_object* v_mvarId_381_, lean_object* v_val_382_, lean_object* v___y_383_, lean_object* v___y_384_){
_start:
{
lean_object* v_res_385_; 
v_res_385_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4___redArg(v_mvarId_381_, v_val_382_, v___y_383_);
lean_dec(v___y_383_);
return v_res_385_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__3_spec__4(lean_object* v_msgData_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_){
_start:
{
lean_object* v___x_392_; lean_object* v_env_393_; lean_object* v___x_394_; lean_object* v_mctx_395_; lean_object* v_lctx_396_; lean_object* v_options_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; 
v___x_392_ = lean_st_ref_get(v___y_390_);
v_env_393_ = lean_ctor_get(v___x_392_, 0);
lean_inc_ref(v_env_393_);
lean_dec(v___x_392_);
v___x_394_ = lean_st_ref_get(v___y_388_);
v_mctx_395_ = lean_ctor_get(v___x_394_, 0);
lean_inc_ref(v_mctx_395_);
lean_dec(v___x_394_);
v_lctx_396_ = lean_ctor_get(v___y_387_, 2);
v_options_397_ = lean_ctor_get(v___y_389_, 2);
lean_inc_ref(v_options_397_);
lean_inc_ref(v_lctx_396_);
v___x_398_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_398_, 0, v_env_393_);
lean_ctor_set(v___x_398_, 1, v_mctx_395_);
lean_ctor_set(v___x_398_, 2, v_lctx_396_);
lean_ctor_set(v___x_398_, 3, v_options_397_);
v___x_399_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_399_, 0, v___x_398_);
lean_ctor_set(v___x_399_, 1, v_msgData_386_);
v___x_400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_400_, 0, v___x_399_);
return v___x_400_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__3_spec__4___boxed(lean_object* v_msgData_401_, lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_){
_start:
{
lean_object* v_res_407_; 
v_res_407_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__3_spec__4(v_msgData_401_, v___y_402_, v___y_403_, v___y_404_, v___y_405_);
lean_dec(v___y_405_);
lean_dec_ref(v___y_404_);
lean_dec(v___y_403_);
lean_dec_ref(v___y_402_);
return v_res_407_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__3___redArg(lean_object* v_msg_408_, lean_object* v___y_409_, lean_object* v___y_410_, lean_object* v___y_411_, lean_object* v___y_412_){
_start:
{
lean_object* v_ref_414_; lean_object* v___x_415_; lean_object* v_a_416_; lean_object* v___x_418_; uint8_t v_isShared_419_; uint8_t v_isSharedCheck_424_; 
v_ref_414_ = lean_ctor_get(v___y_411_, 5);
v___x_415_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__3_spec__4(v_msg_408_, v___y_409_, v___y_410_, v___y_411_, v___y_412_);
v_a_416_ = lean_ctor_get(v___x_415_, 0);
v_isSharedCheck_424_ = !lean_is_exclusive(v___x_415_);
if (v_isSharedCheck_424_ == 0)
{
v___x_418_ = v___x_415_;
v_isShared_419_ = v_isSharedCheck_424_;
goto v_resetjp_417_;
}
else
{
lean_inc(v_a_416_);
lean_dec(v___x_415_);
v___x_418_ = lean_box(0);
v_isShared_419_ = v_isSharedCheck_424_;
goto v_resetjp_417_;
}
v_resetjp_417_:
{
lean_object* v___x_420_; lean_object* v___x_422_; 
lean_inc(v_ref_414_);
v___x_420_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_420_, 0, v_ref_414_);
lean_ctor_set(v___x_420_, 1, v_a_416_);
if (v_isShared_419_ == 0)
{
lean_ctor_set_tag(v___x_418_, 1);
lean_ctor_set(v___x_418_, 0, v___x_420_);
v___x_422_ = v___x_418_;
goto v_reusejp_421_;
}
else
{
lean_object* v_reuseFailAlloc_423_; 
v_reuseFailAlloc_423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_423_, 0, v___x_420_);
v___x_422_ = v_reuseFailAlloc_423_;
goto v_reusejp_421_;
}
v_reusejp_421_:
{
return v___x_422_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__3___redArg___boxed(lean_object* v_msg_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_){
_start:
{
lean_object* v_res_431_; 
v_res_431_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__3___redArg(v_msg_425_, v___y_426_, v___y_427_, v___y_428_, v___y_429_);
lean_dec(v___y_429_);
lean_dec_ref(v___y_428_);
lean_dec(v___y_427_);
lean_dec_ref(v___y_426_);
return v_res_431_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8___lam__0___closed__1(void){
_start:
{
lean_object* v___x_433_; lean_object* v___x_434_; 
v___x_433_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8___lam__0___closed__0));
v___x_434_ = l_Lean_stringToMessageData(v___x_433_);
return v___x_434_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8___lam__0(lean_object* v___x_435_, lean_object* v_snd_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_){
_start:
{
lean_object* v___x_442_; 
lean_inc(v___y_440_);
lean_inc_ref(v___y_439_);
lean_inc(v___y_438_);
lean_inc_ref(v___y_437_);
lean_inc_ref(v___x_435_);
v___x_442_ = lean_infer_type(v___x_435_, v___y_437_, v___y_438_, v___y_439_, v___y_440_);
if (lean_obj_tag(v___x_442_) == 0)
{
lean_object* v_a_443_; lean_object* v___x_444_; 
v_a_443_ = lean_ctor_get(v___x_442_, 0);
lean_inc(v_a_443_);
lean_dec_ref_known(v___x_442_, 1);
v___x_444_ = l_Lean_refutableHasNotBit_x3f(v_a_443_, v___y_437_, v___y_438_, v___y_439_, v___y_440_);
if (lean_obj_tag(v___x_444_) == 0)
{
lean_object* v_a_445_; 
v_a_445_ = lean_ctor_get(v___x_444_, 0);
lean_inc(v_a_445_);
lean_dec_ref_known(v___x_444_, 1);
if (lean_obj_tag(v_a_445_) == 1)
{
lean_object* v_val_446_; lean_object* v___x_447_; 
v_val_446_ = lean_ctor_get(v_a_445_, 0);
lean_inc(v_val_446_);
lean_dec_ref_known(v_a_445_, 1);
lean_inc(v_snd_436_);
v___x_447_ = l_Lean_MVarId_getType(v_snd_436_, v___y_437_, v___y_438_, v___y_439_, v___y_440_);
if (lean_obj_tag(v___x_447_) == 0)
{
lean_object* v_a_448_; lean_object* v___x_449_; 
v_a_448_ = lean_ctor_get(v___x_447_, 0);
lean_inc(v_a_448_);
lean_dec_ref_known(v___x_447_, 1);
v___x_449_ = l_Lean_Meta_mkAbsurd(v_a_448_, v_val_446_, v___x_435_, v___y_437_, v___y_438_, v___y_439_, v___y_440_);
lean_dec(v___y_440_);
lean_dec_ref(v___y_439_);
lean_dec_ref(v___y_437_);
if (lean_obj_tag(v___x_449_) == 0)
{
lean_object* v_a_450_; lean_object* v___x_451_; 
v_a_450_ = lean_ctor_get(v___x_449_, 0);
lean_inc(v_a_450_);
lean_dec_ref_known(v___x_449_, 1);
v___x_451_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4___redArg(v_snd_436_, v_a_450_, v___y_438_);
lean_dec(v___y_438_);
return v___x_451_;
}
else
{
lean_object* v_a_452_; lean_object* v___x_454_; uint8_t v_isShared_455_; uint8_t v_isSharedCheck_459_; 
lean_dec(v___y_438_);
lean_dec(v_snd_436_);
v_a_452_ = lean_ctor_get(v___x_449_, 0);
v_isSharedCheck_459_ = !lean_is_exclusive(v___x_449_);
if (v_isSharedCheck_459_ == 0)
{
v___x_454_ = v___x_449_;
v_isShared_455_ = v_isSharedCheck_459_;
goto v_resetjp_453_;
}
else
{
lean_inc(v_a_452_);
lean_dec(v___x_449_);
v___x_454_ = lean_box(0);
v_isShared_455_ = v_isSharedCheck_459_;
goto v_resetjp_453_;
}
v_resetjp_453_:
{
lean_object* v___x_457_; 
if (v_isShared_455_ == 0)
{
v___x_457_ = v___x_454_;
goto v_reusejp_456_;
}
else
{
lean_object* v_reuseFailAlloc_458_; 
v_reuseFailAlloc_458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_458_, 0, v_a_452_);
v___x_457_ = v_reuseFailAlloc_458_;
goto v_reusejp_456_;
}
v_reusejp_456_:
{
return v___x_457_;
}
}
}
}
else
{
lean_object* v_a_460_; lean_object* v___x_462_; uint8_t v_isShared_463_; uint8_t v_isSharedCheck_467_; 
lean_dec(v_val_446_);
lean_dec(v___y_440_);
lean_dec_ref(v___y_439_);
lean_dec(v___y_438_);
lean_dec_ref(v___y_437_);
lean_dec(v_snd_436_);
lean_dec_ref(v___x_435_);
v_a_460_ = lean_ctor_get(v___x_447_, 0);
v_isSharedCheck_467_ = !lean_is_exclusive(v___x_447_);
if (v_isSharedCheck_467_ == 0)
{
v___x_462_ = v___x_447_;
v_isShared_463_ = v_isSharedCheck_467_;
goto v_resetjp_461_;
}
else
{
lean_inc(v_a_460_);
lean_dec(v___x_447_);
v___x_462_ = lean_box(0);
v_isShared_463_ = v_isSharedCheck_467_;
goto v_resetjp_461_;
}
v_resetjp_461_:
{
lean_object* v___x_465_; 
if (v_isShared_463_ == 0)
{
v___x_465_ = v___x_462_;
goto v_reusejp_464_;
}
else
{
lean_object* v_reuseFailAlloc_466_; 
v_reuseFailAlloc_466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_466_, 0, v_a_460_);
v___x_465_ = v_reuseFailAlloc_466_;
goto v_reusejp_464_;
}
v_reusejp_464_:
{
return v___x_465_;
}
}
}
}
else
{
lean_object* v___x_468_; 
lean_dec(v_a_445_);
lean_dec(v_snd_436_);
lean_inc(v___y_440_);
lean_inc_ref(v___y_439_);
lean_inc(v___y_438_);
lean_inc_ref(v___y_437_);
v___x_468_ = lean_infer_type(v___x_435_, v___y_437_, v___y_438_, v___y_439_, v___y_440_);
if (lean_obj_tag(v___x_468_) == 0)
{
lean_object* v_a_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; 
v_a_469_ = lean_ctor_get(v___x_468_, 0);
lean_inc(v_a_469_);
lean_dec_ref_known(v___x_468_, 1);
v___x_470_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8___lam__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8___lam__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8___lam__0___closed__1);
v___x_471_ = l_Lean_MessageData_ofExpr(v_a_469_);
v___x_472_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_472_, 0, v___x_470_);
lean_ctor_set(v___x_472_, 1, v___x_471_);
v___x_473_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__3___redArg(v___x_472_, v___y_437_, v___y_438_, v___y_439_, v___y_440_);
lean_dec(v___y_440_);
lean_dec_ref(v___y_439_);
lean_dec(v___y_438_);
lean_dec_ref(v___y_437_);
return v___x_473_;
}
else
{
lean_object* v_a_474_; lean_object* v___x_476_; uint8_t v_isShared_477_; uint8_t v_isSharedCheck_481_; 
lean_dec(v___y_440_);
lean_dec_ref(v___y_439_);
lean_dec(v___y_438_);
lean_dec_ref(v___y_437_);
v_a_474_ = lean_ctor_get(v___x_468_, 0);
v_isSharedCheck_481_ = !lean_is_exclusive(v___x_468_);
if (v_isSharedCheck_481_ == 0)
{
v___x_476_ = v___x_468_;
v_isShared_477_ = v_isSharedCheck_481_;
goto v_resetjp_475_;
}
else
{
lean_inc(v_a_474_);
lean_dec(v___x_468_);
v___x_476_ = lean_box(0);
v_isShared_477_ = v_isSharedCheck_481_;
goto v_resetjp_475_;
}
v_resetjp_475_:
{
lean_object* v___x_479_; 
if (v_isShared_477_ == 0)
{
v___x_479_ = v___x_476_;
goto v_reusejp_478_;
}
else
{
lean_object* v_reuseFailAlloc_480_; 
v_reuseFailAlloc_480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_480_, 0, v_a_474_);
v___x_479_ = v_reuseFailAlloc_480_;
goto v_reusejp_478_;
}
v_reusejp_478_:
{
return v___x_479_;
}
}
}
}
}
else
{
lean_object* v_a_482_; lean_object* v___x_484_; uint8_t v_isShared_485_; uint8_t v_isSharedCheck_489_; 
lean_dec(v___y_440_);
lean_dec_ref(v___y_439_);
lean_dec(v___y_438_);
lean_dec_ref(v___y_437_);
lean_dec(v_snd_436_);
lean_dec_ref(v___x_435_);
v_a_482_ = lean_ctor_get(v___x_444_, 0);
v_isSharedCheck_489_ = !lean_is_exclusive(v___x_444_);
if (v_isSharedCheck_489_ == 0)
{
v___x_484_ = v___x_444_;
v_isShared_485_ = v_isSharedCheck_489_;
goto v_resetjp_483_;
}
else
{
lean_inc(v_a_482_);
lean_dec(v___x_444_);
v___x_484_ = lean_box(0);
v_isShared_485_ = v_isSharedCheck_489_;
goto v_resetjp_483_;
}
v_resetjp_483_:
{
lean_object* v___x_487_; 
if (v_isShared_485_ == 0)
{
v___x_487_ = v___x_484_;
goto v_reusejp_486_;
}
else
{
lean_object* v_reuseFailAlloc_488_; 
v_reuseFailAlloc_488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_488_, 0, v_a_482_);
v___x_487_ = v_reuseFailAlloc_488_;
goto v_reusejp_486_;
}
v_reusejp_486_:
{
return v___x_487_;
}
}
}
}
else
{
lean_object* v_a_490_; lean_object* v___x_492_; uint8_t v_isShared_493_; uint8_t v_isSharedCheck_497_; 
lean_dec(v___y_440_);
lean_dec_ref(v___y_439_);
lean_dec(v___y_438_);
lean_dec_ref(v___y_437_);
lean_dec(v_snd_436_);
lean_dec_ref(v___x_435_);
v_a_490_ = lean_ctor_get(v___x_442_, 0);
v_isSharedCheck_497_ = !lean_is_exclusive(v___x_442_);
if (v_isSharedCheck_497_ == 0)
{
v___x_492_ = v___x_442_;
v_isShared_493_ = v_isSharedCheck_497_;
goto v_resetjp_491_;
}
else
{
lean_inc(v_a_490_);
lean_dec(v___x_442_);
v___x_492_ = lean_box(0);
v_isShared_493_ = v_isSharedCheck_497_;
goto v_resetjp_491_;
}
v_resetjp_491_:
{
lean_object* v___x_495_; 
if (v_isShared_493_ == 0)
{
v___x_495_ = v___x_492_;
goto v_reusejp_494_;
}
else
{
lean_object* v_reuseFailAlloc_496_; 
v_reuseFailAlloc_496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_496_, 0, v_a_490_);
v___x_495_ = v_reuseFailAlloc_496_;
goto v_reusejp_494_;
}
v_reusejp_494_:
{
return v___x_495_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8___lam__0___boxed(lean_object* v___x_498_, lean_object* v_snd_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_){
_start:
{
lean_object* v_res_505_; 
v_res_505_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8___lam__0(v___x_498_, v_snd_499_, v___y_500_, v___y_501_, v___y_502_, v___y_503_);
return v_res_505_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8___lam__1___closed__3(void){
_start:
{
lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; 
v___x_509_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8___lam__1___closed__2));
v___x_510_ = lean_unsigned_to_nat(10u);
v___x_511_ = lean_unsigned_to_nat(63u);
v___x_512_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8___lam__1___closed__1));
v___x_513_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8___lam__1___closed__0));
v___x_514_ = l_mkPanicMessageWithDecl(v___x_513_, v___x_512_, v___x_511_, v___x_510_, v___x_509_);
return v___x_514_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8___lam__1___closed__8(void){
_start:
{
lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; 
v___x_519_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8___lam__1___closed__7));
v___x_520_ = lean_unsigned_to_nat(14u);
v___x_521_ = lean_unsigned_to_nat(22u);
v___x_522_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8___lam__1___closed__6));
v___x_523_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8___lam__1___closed__5));
v___x_524_ = l_mkPanicMessageWithDecl(v___x_523_, v___x_522_, v___x_521_, v___x_520_, v___x_519_);
return v___x_524_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8___lam__1(uint8_t v___y_525_, lean_object* v_val_526_, lean_object* v_mvarId_527_, uint8_t v___x_528_, lean_object* v_subst_529_, lean_object* v_fst_530_, lean_object* v___x_531_, lean_object* v_fst_532_, lean_object* v_ctorName_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_){
_start:
{
if (v___y_525_ == 0)
{
lean_object* v___x_539_; lean_object* v___x_540_; 
lean_dec(v_ctorName_533_);
lean_dec(v_fst_532_);
lean_dec(v___x_531_);
lean_dec(v_fst_530_);
lean_dec(v_mvarId_527_);
lean_dec_ref(v_val_526_);
v___x_539_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8___lam__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8___lam__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8___lam__1___closed__3);
v___x_540_ = l_panic___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__2(v___x_539_, v___y_534_, v___y_535_, v___y_536_, v___y_537_);
return v___x_540_;
}
else
{
lean_object* v___x_541_; lean_object* v___y_543_; 
v___x_541_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8___lam__1___closed__4));
if (lean_obj_tag(v_ctorName_533_) == 0)
{
lean_object* v___x_565_; lean_object* v___x_566_; 
v___x_565_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8___lam__1___closed__8, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8___lam__1___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8___lam__1___closed__8);
v___x_566_ = l_panic___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__6(v___x_565_);
v___y_543_ = v___x_566_;
goto v___jp_542_;
}
else
{
lean_object* v_val_567_; 
v_val_567_ = lean_ctor_get(v_ctorName_533_, 0);
lean_inc(v_val_567_);
lean_dec_ref_known(v_ctorName_533_, 1);
v___y_543_ = v_val_567_;
goto v___jp_542_;
}
v___jp_542_:
{
lean_object* v_insterestingCtors_544_; uint8_t v___x_545_; 
v_insterestingCtors_544_ = lean_ctor_get(v_val_526_, 3);
lean_inc_ref(v_insterestingCtors_544_);
lean_dec_ref(v_val_526_);
v___x_545_ = l_Array_contains___redArg(v___x_541_, v_insterestingCtors_544_, v___y_543_);
if (v___x_545_ == 0)
{
lean_object* v___x_546_; 
lean_dec(v_fst_532_);
lean_dec(v___x_531_);
lean_dec(v_fst_530_);
v___x_546_ = l_Lean_MVarId_refl(v_mvarId_527_, v___x_528_, v___y_534_, v___y_535_, v___y_536_, v___y_537_);
return v___x_546_;
}
else
{
lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; 
v___x_547_ = l_Lean_Meta_FVarSubst_get(v_subst_529_, v_fst_530_);
v___x_548_ = l_Lean_Expr_fvarId_x21(v___x_547_);
lean_dec_ref(v___x_547_);
v___x_549_ = l_Lean_Meta_substEq(v_mvarId_527_, v___x_548_, v___x_531_, v___y_534_, v___y_535_, v___y_536_, v___y_537_);
if (lean_obj_tag(v___x_549_) == 0)
{
lean_object* v_a_550_; lean_object* v_fst_551_; lean_object* v_snd_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___f_555_; lean_object* v___x_556_; 
v_a_550_ = lean_ctor_get(v___x_549_, 0);
lean_inc(v_a_550_);
lean_dec_ref_known(v___x_549_, 1);
v_fst_551_ = lean_ctor_get(v_a_550_, 0);
lean_inc(v_fst_551_);
v_snd_552_ = lean_ctor_get(v_a_550_, 1);
lean_inc_n(v_snd_552_, 2);
lean_dec(v_a_550_);
v___x_553_ = l_Lean_Meta_FVarSubst_get(v_subst_529_, v_fst_532_);
v___x_554_ = l_Lean_Meta_FVarSubst_apply(v_fst_551_, v___x_553_);
lean_dec_ref(v___x_553_);
v___f_555_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8___lam__0___boxed), 7, 2);
lean_closure_set(v___f_555_, 0, v___x_554_);
lean_closure_set(v___f_555_, 1, v_snd_552_);
v___x_556_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__5___redArg(v_snd_552_, v___f_555_, v___y_534_, v___y_535_, v___y_536_, v___y_537_);
return v___x_556_;
}
else
{
lean_object* v_a_557_; lean_object* v___x_559_; uint8_t v_isShared_560_; uint8_t v_isSharedCheck_564_; 
lean_dec(v_fst_532_);
v_a_557_ = lean_ctor_get(v___x_549_, 0);
v_isSharedCheck_564_ = !lean_is_exclusive(v___x_549_);
if (v_isSharedCheck_564_ == 0)
{
v___x_559_ = v___x_549_;
v_isShared_560_ = v_isSharedCheck_564_;
goto v_resetjp_558_;
}
else
{
lean_inc(v_a_557_);
lean_dec(v___x_549_);
v___x_559_ = lean_box(0);
v_isShared_560_ = v_isSharedCheck_564_;
goto v_resetjp_558_;
}
v_resetjp_558_:
{
lean_object* v___x_562_; 
if (v_isShared_560_ == 0)
{
v___x_562_ = v___x_559_;
goto v_reusejp_561_;
}
else
{
lean_object* v_reuseFailAlloc_563_; 
v_reuseFailAlloc_563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_563_, 0, v_a_557_);
v___x_562_ = v_reuseFailAlloc_563_;
goto v_reusejp_561_;
}
v_reusejp_561_:
{
return v___x_562_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8___lam__1___boxed(lean_object* v___y_568_, lean_object* v_val_569_, lean_object* v_mvarId_570_, lean_object* v___x_571_, lean_object* v_subst_572_, lean_object* v_fst_573_, lean_object* v___x_574_, lean_object* v_fst_575_, lean_object* v_ctorName_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_){
_start:
{
uint8_t v___y_19336__boxed_582_; uint8_t v___x_19338__boxed_583_; lean_object* v_res_584_; 
v___y_19336__boxed_582_ = lean_unbox(v___y_568_);
v___x_19338__boxed_583_ = lean_unbox(v___x_571_);
v_res_584_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8___lam__1(v___y_19336__boxed_582_, v_val_569_, v_mvarId_570_, v___x_19338__boxed_583_, v_subst_572_, v_fst_573_, v___x_574_, v_fst_575_, v_ctorName_576_, v___y_577_, v___y_578_, v___y_579_, v___y_580_);
lean_dec(v___y_580_);
lean_dec_ref(v___y_579_);
lean_dec(v___y_578_);
lean_dec_ref(v___y_577_);
lean_dec(v_subst_572_);
return v_res_584_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8(lean_object* v_val_585_, uint8_t v___x_586_, lean_object* v_fst_587_, lean_object* v_fst_588_, lean_object* v_as_589_, size_t v_i_590_, size_t v_stop_591_, lean_object* v_b_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_){
_start:
{
uint8_t v___x_598_; 
v___x_598_ = lean_usize_dec_eq(v_i_590_, v_stop_591_);
if (v___x_598_ == 0)
{
lean_object* v___x_599_; lean_object* v_toInductionSubgoal_600_; lean_object* v_ctorName_601_; lean_object* v_mvarId_602_; lean_object* v_subst_603_; lean_object* v___x_604_; uint8_t v___y_606_; 
v___x_599_ = lean_array_uget_borrowed(v_as_589_, v_i_590_);
v_toInductionSubgoal_600_ = lean_ctor_get(v___x_599_, 0);
v_ctorName_601_ = lean_ctor_get(v___x_599_, 1);
v_mvarId_602_ = lean_ctor_get(v_toInductionSubgoal_600_, 0);
v_subst_603_ = lean_ctor_get(v_toInductionSubgoal_600_, 2);
v___x_604_ = lean_box(0);
if (lean_obj_tag(v_ctorName_601_) == 0)
{
v___y_606_ = v___x_598_;
goto v___jp_605_;
}
else
{
if (v___x_586_ == 0)
{
v___y_606_ = v___x_598_;
goto v___jp_605_;
}
else
{
v___y_606_ = v___x_586_;
goto v___jp_605_;
}
}
v___jp_605_:
{
lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___y_609_; lean_object* v___x_610_; 
v___x_607_ = lean_box(v___y_606_);
v___x_608_ = lean_box(v___x_586_);
lean_inc(v_ctorName_601_);
lean_inc(v_fst_588_);
lean_inc(v_fst_587_);
lean_inc(v_subst_603_);
lean_inc_n(v_mvarId_602_, 2);
lean_inc_ref(v_val_585_);
v___y_609_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8___lam__1___boxed), 14, 9);
lean_closure_set(v___y_609_, 0, v___x_607_);
lean_closure_set(v___y_609_, 1, v_val_585_);
lean_closure_set(v___y_609_, 2, v_mvarId_602_);
lean_closure_set(v___y_609_, 3, v___x_608_);
lean_closure_set(v___y_609_, 4, v_subst_603_);
lean_closure_set(v___y_609_, 5, v_fst_587_);
lean_closure_set(v___y_609_, 6, v___x_604_);
lean_closure_set(v___y_609_, 7, v_fst_588_);
lean_closure_set(v___y_609_, 8, v_ctorName_601_);
v___x_610_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__5___redArg(v_mvarId_602_, v___y_609_, v___y_593_, v___y_594_, v___y_595_, v___y_596_);
if (lean_obj_tag(v___x_610_) == 0)
{
lean_object* v_a_611_; size_t v___x_612_; size_t v___x_613_; 
v_a_611_ = lean_ctor_get(v___x_610_, 0);
lean_inc(v_a_611_);
lean_dec_ref_known(v___x_610_, 1);
v___x_612_ = ((size_t)1ULL);
v___x_613_ = lean_usize_add(v_i_590_, v___x_612_);
v_i_590_ = v___x_613_;
v_b_592_ = v_a_611_;
goto _start;
}
else
{
lean_dec(v_fst_588_);
lean_dec(v_fst_587_);
lean_dec_ref(v_val_585_);
return v___x_610_;
}
}
}
else
{
lean_object* v___x_615_; 
lean_dec(v_fst_588_);
lean_dec(v_fst_587_);
lean_dec_ref(v_val_585_);
v___x_615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_615_, 0, v_b_592_);
return v___x_615_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8___boxed(lean_object* v_val_616_, lean_object* v___x_617_, lean_object* v_fst_618_, lean_object* v_fst_619_, lean_object* v_as_620_, lean_object* v_i_621_, lean_object* v_stop_622_, lean_object* v_b_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_){
_start:
{
uint8_t v___x_19445__boxed_629_; size_t v_i_boxed_630_; size_t v_stop_boxed_631_; lean_object* v_res_632_; 
v___x_19445__boxed_629_ = lean_unbox(v___x_617_);
v_i_boxed_630_ = lean_unbox_usize(v_i_621_);
lean_dec(v_i_621_);
v_stop_boxed_631_ = lean_unbox_usize(v_stop_622_);
lean_dec(v_stop_622_);
v_res_632_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8(v_val_616_, v___x_19445__boxed_629_, v_fst_618_, v_fst_619_, v_as_620_, v_i_boxed_630_, v_stop_boxed_631_, v_b_623_, v___y_624_, v___y_625_, v___y_626_, v___y_627_);
lean_dec(v___y_627_);
lean_dec_ref(v___y_626_);
lean_dec(v___y_625_);
lean_dec_ref(v___y_624_);
lean_dec_ref(v_as_620_);
return v_res_632_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__0(lean_object* v___x_636_, lean_object* v___x_637_, lean_object* v_fst_638_, lean_object* v___x_639_, lean_object* v_snd_640_, lean_object* v_val_641_, lean_object* v___x_642_, lean_object* v_xs_643_, lean_object* v___x_644_, lean_object* v_a_645_, lean_object* v_hyps_646_, lean_object* v_a_647_, uint8_t v___x_648_, lean_object* v_thmName_649_, lean_object* v_levelParams_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_){
_start:
{
lean_object* v___x_656_; 
lean_inc_ref(v___x_636_);
v___x_656_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_636_, v___x_637_, v___y_651_, v___y_652_, v___y_653_, v___y_654_);
if (lean_obj_tag(v___x_656_) == 0)
{
lean_object* v_a_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; 
v_a_657_ = lean_ctor_get(v___x_656_, 0);
lean_inc(v_a_657_);
lean_dec_ref_known(v___x_656_, 1);
v___x_658_ = l_Lean_Expr_mvarId_x21(v_a_657_);
v___x_659_ = lean_box(0);
lean_inc(v_fst_638_);
v___x_660_ = l_Lean_Meta_substEq(v___x_658_, v_fst_638_, v___x_659_, v___y_651_, v___y_652_, v___y_653_, v___y_654_);
if (lean_obj_tag(v___x_660_) == 0)
{
lean_object* v_a_661_; lean_object* v_fst_662_; lean_object* v_snd_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_667_; uint8_t v_isShared_668_; uint8_t v_isSharedCheck_756_; 
v_a_661_ = lean_ctor_get(v___x_660_, 0);
lean_inc(v_a_661_);
lean_dec_ref_known(v___x_660_, 1);
v_fst_662_ = lean_ctor_get(v_a_661_, 0);
lean_inc(v_fst_662_);
v_snd_663_ = lean_ctor_get(v_a_661_, 1);
lean_inc(v_snd_663_);
lean_dec(v_a_661_);
v___x_664_ = l_Lean_Meta_FVarSubst_apply(v_fst_662_, v___x_639_);
v___x_665_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4___redArg(v_snd_663_, v___x_664_, v___y_652_);
v_isSharedCheck_756_ = !lean_is_exclusive(v___x_665_);
if (v_isSharedCheck_756_ == 0)
{
lean_object* v_unused_757_; 
v_unused_757_ = lean_ctor_get(v___x_665_, 0);
lean_dec(v_unused_757_);
v___x_667_ = v___x_665_;
v_isShared_668_ = v_isSharedCheck_756_;
goto v_resetjp_666_;
}
else
{
lean_dec(v___x_665_);
v___x_667_ = lean_box(0);
v_isShared_668_ = v_isSharedCheck_756_;
goto v_resetjp_666_;
}
v_resetjp_666_:
{
lean_object* v___x_669_; lean_object* v___x_671_; 
v___x_669_ = ((lean_object*)(l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__0___closed__1));
if (v_isShared_668_ == 0)
{
lean_ctor_set_tag(v___x_667_, 1);
lean_ctor_set(v___x_667_, 0, v___x_636_);
v___x_671_ = v___x_667_;
goto v_reusejp_670_;
}
else
{
lean_object* v_reuseFailAlloc_755_; 
v_reuseFailAlloc_755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_755_, 0, v___x_636_);
v___x_671_ = v_reuseFailAlloc_755_;
goto v_reusejp_670_;
}
v_reusejp_670_:
{
lean_object* v___x_672_; 
v___x_672_ = l_Lean_MVarId_note(v_snd_640_, v___x_669_, v_a_657_, v___x_671_, v___y_651_, v___y_652_, v___y_653_, v___y_654_);
if (lean_obj_tag(v___x_672_) == 0)
{
lean_object* v_a_673_; lean_object* v_fst_674_; lean_object* v_snd_675_; lean_object* v___x_677_; uint8_t v_isShared_678_; uint8_t v_isSharedCheck_746_; 
v_a_673_ = lean_ctor_get(v___x_672_, 0);
lean_inc(v_a_673_);
lean_dec_ref_known(v___x_672_, 1);
v_fst_674_ = lean_ctor_get(v_a_673_, 0);
v_snd_675_ = lean_ctor_get(v_a_673_, 1);
v_isSharedCheck_746_ = !lean_is_exclusive(v_a_673_);
if (v_isSharedCheck_746_ == 0)
{
v___x_677_ = v_a_673_;
v_isShared_678_ = v_isSharedCheck_746_;
goto v_resetjp_676_;
}
else
{
lean_inc(v_snd_675_);
lean_inc(v_fst_674_);
lean_dec(v_a_673_);
v___x_677_ = lean_box(0);
v_isShared_678_ = v_isSharedCheck_746_;
goto v_resetjp_676_;
}
v_resetjp_676_:
{
lean_object* v_majorPos_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; uint8_t v___x_683_; lean_object* v___y_724_; lean_object* v___x_725_; lean_object* v___x_726_; 
v_majorPos_679_ = lean_ctor_get(v_val_641_, 1);
v___x_680_ = lean_array_get_borrowed(v___x_642_, v_xs_643_, v_majorPos_679_);
v___x_681_ = l_Lean_Expr_fvarId_x21(v___x_680_);
v___x_682_ = lean_mk_empty_array_with_capacity(v___x_644_);
v___x_683_ = 0;
v___x_725_ = lean_box(0);
v___x_726_ = l_Lean_MVarId_cases(v_snd_675_, v___x_681_, v___x_682_, v___x_683_, v___x_725_, v___y_651_, v___y_652_, v___y_653_, v___y_654_);
if (lean_obj_tag(v___x_726_) == 0)
{
lean_object* v_a_727_; lean_object* v___x_728_; uint8_t v___x_729_; 
v_a_727_ = lean_ctor_get(v___x_726_, 0);
lean_inc(v_a_727_);
lean_dec_ref_known(v___x_726_, 1);
v___x_728_ = lean_array_get_size(v_a_727_);
v___x_729_ = lean_nat_dec_lt(v___x_644_, v___x_728_);
if (v___x_729_ == 0)
{
lean_dec(v_a_727_);
lean_dec(v_fst_674_);
lean_dec_ref(v_val_641_);
lean_dec(v_fst_638_);
goto v___jp_684_;
}
else
{
lean_object* v___x_730_; uint8_t v___x_731_; 
v___x_730_ = lean_box(0);
v___x_731_ = lean_nat_dec_le(v___x_728_, v___x_728_);
if (v___x_731_ == 0)
{
if (v___x_729_ == 0)
{
lean_dec(v_a_727_);
lean_dec(v_fst_674_);
lean_dec_ref(v_val_641_);
lean_dec(v_fst_638_);
goto v___jp_684_;
}
else
{
size_t v___x_732_; size_t v___x_733_; lean_object* v___x_734_; 
v___x_732_ = ((size_t)0ULL);
v___x_733_ = lean_usize_of_nat(v___x_728_);
v___x_734_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8(v_val_641_, v___x_648_, v_fst_638_, v_fst_674_, v_a_727_, v___x_732_, v___x_733_, v___x_730_, v___y_651_, v___y_652_, v___y_653_, v___y_654_);
lean_dec(v_a_727_);
v___y_724_ = v___x_734_;
goto v___jp_723_;
}
}
else
{
size_t v___x_735_; size_t v___x_736_; lean_object* v___x_737_; 
v___x_735_ = ((size_t)0ULL);
v___x_736_ = lean_usize_of_nat(v___x_728_);
v___x_737_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8(v_val_641_, v___x_648_, v_fst_638_, v_fst_674_, v_a_727_, v___x_735_, v___x_736_, v___x_730_, v___y_651_, v___y_652_, v___y_653_, v___y_654_);
lean_dec(v_a_727_);
v___y_724_ = v___x_737_;
goto v___jp_723_;
}
}
}
else
{
lean_object* v_a_738_; lean_object* v___x_740_; uint8_t v_isShared_741_; uint8_t v_isSharedCheck_745_; 
lean_del_object(v___x_677_);
lean_dec(v_fst_674_);
lean_dec(v_levelParams_650_);
lean_dec(v_thmName_649_);
lean_dec_ref(v_a_647_);
lean_dec_ref(v_a_645_);
lean_dec_ref(v_xs_643_);
lean_dec_ref(v_val_641_);
lean_dec(v_fst_638_);
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
v___jp_684_:
{
lean_object* v___x_685_; lean_object* v_a_686_; lean_object* v___x_688_; uint8_t v_isShared_689_; uint8_t v_isSharedCheck_722_; 
v___x_685_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__7___redArg(v_a_645_, v___y_652_);
v_a_686_ = lean_ctor_get(v___x_685_, 0);
v_isSharedCheck_722_ = !lean_is_exclusive(v___x_685_);
if (v_isSharedCheck_722_ == 0)
{
v___x_688_ = v___x_685_;
v_isShared_689_ = v_isSharedCheck_722_;
goto v_resetjp_687_;
}
else
{
lean_inc(v_a_686_);
lean_dec(v___x_685_);
v___x_688_ = lean_box(0);
v_isShared_689_ = v_isSharedCheck_722_;
goto v_resetjp_687_;
}
v_resetjp_687_:
{
lean_object* v___x_690_; uint8_t v___x_691_; lean_object* v___x_692_; 
v___x_690_ = l_Array_append___redArg(v_xs_643_, v_hyps_646_);
v___x_691_ = 1;
v___x_692_ = l_Lean_Meta_mkForallFVars(v___x_690_, v_a_647_, v___x_683_, v___x_648_, v___x_648_, v___x_691_, v___y_651_, v___y_652_, v___y_653_, v___y_654_);
if (lean_obj_tag(v___x_692_) == 0)
{
lean_object* v_a_693_; lean_object* v___x_694_; 
v_a_693_ = lean_ctor_get(v___x_692_, 0);
lean_inc(v_a_693_);
lean_dec_ref_known(v___x_692_, 1);
v___x_694_ = l_Lean_Meta_mkLambdaFVars(v___x_690_, v_a_686_, v___x_683_, v___x_648_, v___x_683_, v___x_648_, v___x_691_, v___y_651_, v___y_652_, v___y_653_, v___y_654_);
lean_dec_ref(v___x_690_);
if (lean_obj_tag(v___x_694_) == 0)
{
lean_object* v_a_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_699_; 
v_a_695_ = lean_ctor_get(v___x_694_, 0);
lean_inc(v_a_695_);
lean_dec_ref_known(v___x_694_, 1);
lean_inc(v_thmName_649_);
v___x_696_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_696_, 0, v_thmName_649_);
lean_ctor_set(v___x_696_, 1, v_levelParams_650_);
lean_ctor_set(v___x_696_, 2, v_a_693_);
v___x_697_ = lean_box(0);
if (v_isShared_678_ == 0)
{
lean_ctor_set_tag(v___x_677_, 1);
lean_ctor_set(v___x_677_, 1, v___x_697_);
lean_ctor_set(v___x_677_, 0, v_thmName_649_);
v___x_699_ = v___x_677_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_705_; 
v_reuseFailAlloc_705_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_705_, 0, v_thmName_649_);
lean_ctor_set(v_reuseFailAlloc_705_, 1, v___x_697_);
v___x_699_ = v_reuseFailAlloc_705_;
goto v_reusejp_698_;
}
v_reusejp_698_:
{
lean_object* v___x_700_; lean_object* v___x_702_; 
v___x_700_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_700_, 0, v___x_696_);
lean_ctor_set(v___x_700_, 1, v_a_695_);
lean_ctor_set(v___x_700_, 2, v___x_699_);
if (v_isShared_689_ == 0)
{
lean_ctor_set_tag(v___x_688_, 2);
lean_ctor_set(v___x_688_, 0, v___x_700_);
v___x_702_ = v___x_688_;
goto v_reusejp_701_;
}
else
{
lean_object* v_reuseFailAlloc_704_; 
v_reuseFailAlloc_704_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_704_, 0, v___x_700_);
v___x_702_ = v_reuseFailAlloc_704_;
goto v_reusejp_701_;
}
v_reusejp_701_:
{
lean_object* v___x_703_; 
v___x_703_ = l_Lean_addDecl(v___x_702_, v___x_683_, v___y_653_, v___y_654_);
return v___x_703_;
}
}
}
else
{
lean_object* v_a_706_; lean_object* v___x_708_; uint8_t v_isShared_709_; uint8_t v_isSharedCheck_713_; 
lean_dec(v_a_693_);
lean_del_object(v___x_688_);
lean_del_object(v___x_677_);
lean_dec(v_levelParams_650_);
lean_dec(v_thmName_649_);
v_a_706_ = lean_ctor_get(v___x_694_, 0);
v_isSharedCheck_713_ = !lean_is_exclusive(v___x_694_);
if (v_isSharedCheck_713_ == 0)
{
v___x_708_ = v___x_694_;
v_isShared_709_ = v_isSharedCheck_713_;
goto v_resetjp_707_;
}
else
{
lean_inc(v_a_706_);
lean_dec(v___x_694_);
v___x_708_ = lean_box(0);
v_isShared_709_ = v_isSharedCheck_713_;
goto v_resetjp_707_;
}
v_resetjp_707_:
{
lean_object* v___x_711_; 
if (v_isShared_709_ == 0)
{
v___x_711_ = v___x_708_;
goto v_reusejp_710_;
}
else
{
lean_object* v_reuseFailAlloc_712_; 
v_reuseFailAlloc_712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_712_, 0, v_a_706_);
v___x_711_ = v_reuseFailAlloc_712_;
goto v_reusejp_710_;
}
v_reusejp_710_:
{
return v___x_711_;
}
}
}
}
else
{
lean_object* v_a_714_; lean_object* v___x_716_; uint8_t v_isShared_717_; uint8_t v_isSharedCheck_721_; 
lean_dec_ref(v___x_690_);
lean_del_object(v___x_688_);
lean_dec(v_a_686_);
lean_del_object(v___x_677_);
lean_dec(v_levelParams_650_);
lean_dec(v_thmName_649_);
v_a_714_ = lean_ctor_get(v___x_692_, 0);
v_isSharedCheck_721_ = !lean_is_exclusive(v___x_692_);
if (v_isSharedCheck_721_ == 0)
{
v___x_716_ = v___x_692_;
v_isShared_717_ = v_isSharedCheck_721_;
goto v_resetjp_715_;
}
else
{
lean_inc(v_a_714_);
lean_dec(v___x_692_);
v___x_716_ = lean_box(0);
v_isShared_717_ = v_isSharedCheck_721_;
goto v_resetjp_715_;
}
v_resetjp_715_:
{
lean_object* v___x_719_; 
if (v_isShared_717_ == 0)
{
v___x_719_ = v___x_716_;
goto v_reusejp_718_;
}
else
{
lean_object* v_reuseFailAlloc_720_; 
v_reuseFailAlloc_720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_720_, 0, v_a_714_);
v___x_719_ = v_reuseFailAlloc_720_;
goto v_reusejp_718_;
}
v_reusejp_718_:
{
return v___x_719_;
}
}
}
}
}
v___jp_723_:
{
if (lean_obj_tag(v___y_724_) == 0)
{
lean_dec_ref_known(v___y_724_, 1);
goto v___jp_684_;
}
else
{
lean_del_object(v___x_677_);
lean_dec(v_levelParams_650_);
lean_dec(v_thmName_649_);
lean_dec_ref(v_a_647_);
lean_dec_ref(v_a_645_);
lean_dec_ref(v_xs_643_);
return v___y_724_;
}
}
}
}
else
{
lean_object* v_a_747_; lean_object* v___x_749_; uint8_t v_isShared_750_; uint8_t v_isSharedCheck_754_; 
lean_dec(v_levelParams_650_);
lean_dec(v_thmName_649_);
lean_dec_ref(v_a_647_);
lean_dec_ref(v_a_645_);
lean_dec_ref(v_xs_643_);
lean_dec_ref(v_val_641_);
lean_dec(v_fst_638_);
v_a_747_ = lean_ctor_get(v___x_672_, 0);
v_isSharedCheck_754_ = !lean_is_exclusive(v___x_672_);
if (v_isSharedCheck_754_ == 0)
{
v___x_749_ = v___x_672_;
v_isShared_750_ = v_isSharedCheck_754_;
goto v_resetjp_748_;
}
else
{
lean_inc(v_a_747_);
lean_dec(v___x_672_);
v___x_749_ = lean_box(0);
v_isShared_750_ = v_isSharedCheck_754_;
goto v_resetjp_748_;
}
v_resetjp_748_:
{
lean_object* v___x_752_; 
if (v_isShared_750_ == 0)
{
v___x_752_ = v___x_749_;
goto v_reusejp_751_;
}
else
{
lean_object* v_reuseFailAlloc_753_; 
v_reuseFailAlloc_753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_753_, 0, v_a_747_);
v___x_752_ = v_reuseFailAlloc_753_;
goto v_reusejp_751_;
}
v_reusejp_751_:
{
return v___x_752_;
}
}
}
}
}
}
else
{
lean_object* v_a_758_; lean_object* v___x_760_; uint8_t v_isShared_761_; uint8_t v_isSharedCheck_765_; 
lean_dec(v_a_657_);
lean_dec(v_levelParams_650_);
lean_dec(v_thmName_649_);
lean_dec_ref(v_a_647_);
lean_dec_ref(v_a_645_);
lean_dec_ref(v_xs_643_);
lean_dec_ref(v_val_641_);
lean_dec(v_snd_640_);
lean_dec(v_fst_638_);
lean_dec_ref(v___x_636_);
v_a_758_ = lean_ctor_get(v___x_660_, 0);
v_isSharedCheck_765_ = !lean_is_exclusive(v___x_660_);
if (v_isSharedCheck_765_ == 0)
{
v___x_760_ = v___x_660_;
v_isShared_761_ = v_isSharedCheck_765_;
goto v_resetjp_759_;
}
else
{
lean_inc(v_a_758_);
lean_dec(v___x_660_);
v___x_760_ = lean_box(0);
v_isShared_761_ = v_isSharedCheck_765_;
goto v_resetjp_759_;
}
v_resetjp_759_:
{
lean_object* v___x_763_; 
if (v_isShared_761_ == 0)
{
v___x_763_ = v___x_760_;
goto v_reusejp_762_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v_a_758_);
v___x_763_ = v_reuseFailAlloc_764_;
goto v_reusejp_762_;
}
v_reusejp_762_:
{
return v___x_763_;
}
}
}
}
else
{
lean_object* v_a_766_; lean_object* v___x_768_; uint8_t v_isShared_769_; uint8_t v_isSharedCheck_773_; 
lean_dec(v_levelParams_650_);
lean_dec(v_thmName_649_);
lean_dec_ref(v_a_647_);
lean_dec_ref(v_a_645_);
lean_dec_ref(v_xs_643_);
lean_dec_ref(v_val_641_);
lean_dec(v_snd_640_);
lean_dec(v_fst_638_);
lean_dec_ref(v___x_636_);
v_a_766_ = lean_ctor_get(v___x_656_, 0);
v_isSharedCheck_773_ = !lean_is_exclusive(v___x_656_);
if (v_isSharedCheck_773_ == 0)
{
v___x_768_ = v___x_656_;
v_isShared_769_ = v_isSharedCheck_773_;
goto v_resetjp_767_;
}
else
{
lean_inc(v_a_766_);
lean_dec(v___x_656_);
v___x_768_ = lean_box(0);
v_isShared_769_ = v_isSharedCheck_773_;
goto v_resetjp_767_;
}
v_resetjp_767_:
{
lean_object* v___x_771_; 
if (v_isShared_769_ == 0)
{
v___x_771_ = v___x_768_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v_a_766_);
v___x_771_ = v_reuseFailAlloc_772_;
goto v_reusejp_770_;
}
v_reusejp_770_:
{
return v___x_771_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__0___boxed(lean_object** _args){
lean_object* v___x_774_ = _args[0];
lean_object* v___x_775_ = _args[1];
lean_object* v_fst_776_ = _args[2];
lean_object* v___x_777_ = _args[3];
lean_object* v_snd_778_ = _args[4];
lean_object* v_val_779_ = _args[5];
lean_object* v___x_780_ = _args[6];
lean_object* v_xs_781_ = _args[7];
lean_object* v___x_782_ = _args[8];
lean_object* v_a_783_ = _args[9];
lean_object* v_hyps_784_ = _args[10];
lean_object* v_a_785_ = _args[11];
lean_object* v___x_786_ = _args[12];
lean_object* v_thmName_787_ = _args[13];
lean_object* v_levelParams_788_ = _args[14];
lean_object* v___y_789_ = _args[15];
lean_object* v___y_790_ = _args[16];
lean_object* v___y_791_ = _args[17];
lean_object* v___y_792_ = _args[18];
lean_object* v___y_793_ = _args[19];
_start:
{
uint8_t v___x_19516__boxed_794_; lean_object* v_res_795_; 
v___x_19516__boxed_794_ = lean_unbox(v___x_786_);
v_res_795_ = l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__0(v___x_774_, v___x_775_, v_fst_776_, v___x_777_, v_snd_778_, v_val_779_, v___x_780_, v_xs_781_, v___x_782_, v_a_783_, v_hyps_784_, v_a_785_, v___x_19516__boxed_794_, v_thmName_787_, v_levelParams_788_, v___y_789_, v___y_790_, v___y_791_, v___y_792_);
lean_dec(v___y_792_);
lean_dec_ref(v___y_791_);
lean_dec(v___y_790_);
lean_dec_ref(v___y_789_);
lean_dec_ref(v_hyps_784_);
lean_dec(v___x_782_);
lean_dec_ref(v___x_780_);
lean_dec_ref(v___x_777_);
return v_res_795_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__1___closed__1(void){
_start:
{
lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; 
v___x_797_ = ((lean_object*)(l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__1___closed__0));
v___x_798_ = lean_unsigned_to_nat(8u);
v___x_799_ = lean_unsigned_to_nat(34u);
v___x_800_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8___lam__1___closed__1));
v___x_801_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8___lam__1___closed__0));
v___x_802_ = l_mkPanicMessageWithDecl(v___x_801_, v___x_800_, v___x_799_, v___x_798_, v___x_797_);
return v___x_802_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__1___closed__3(void){
_start:
{
lean_object* v___x_804_; lean_object* v___x_805_; 
v___x_804_ = ((lean_object*)(l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__1___closed__2));
v___x_805_ = l_Lean_stringToMessageData(v___x_804_);
return v___x_805_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__1(lean_object* v___x_819_, lean_object* v_sparseCasesOnName_820_, lean_object* v___x_821_, lean_object* v_xs_822_, lean_object* v___x_823_, lean_object* v___x_824_, lean_object* v___x_825_, lean_object* v_val_826_, lean_object* v_thmName_827_, lean_object* v_levelParams_828_, lean_object* v_hyps_829_, lean_object* v_x_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_){
_start:
{
lean_object* v___x_836_; uint8_t v___x_837_; 
v___x_836_ = lean_array_get_size(v_hyps_829_);
v___x_837_ = lean_nat_dec_eq(v___x_836_, v___x_819_);
if (v___x_837_ == 0)
{
lean_object* v___x_838_; lean_object* v___x_839_; 
lean_dec_ref(v_hyps_829_);
lean_dec(v_levelParams_828_);
lean_dec(v_thmName_827_);
lean_dec_ref(v_val_826_);
lean_dec(v___x_825_);
lean_dec_ref(v___x_824_);
lean_dec_ref(v___x_823_);
lean_dec_ref(v_xs_822_);
lean_dec(v___x_821_);
lean_dec(v_sparseCasesOnName_820_);
v___x_838_ = lean_obj_once(&l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__1___closed__1, &l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__1___closed__1_once, _init_l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__1___closed__1);
v___x_839_ = l_panic___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__2(v___x_838_, v___y_831_, v___y_832_, v___y_833_, v___y_834_);
return v___x_839_;
}
else
{
lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; 
v___x_840_ = l_Lean_mkConst(v_sparseCasesOnName_820_, v___x_821_);
v___x_841_ = l_Lean_mkAppN(v___x_840_, v_xs_822_);
v___x_842_ = l_Lean_mkAppN(v___x_823_, v_hyps_829_);
v___x_843_ = l_Lean_Meta_mkEq(v___x_841_, v___x_842_, v___y_831_, v___y_832_, v___y_833_, v___y_834_);
if (lean_obj_tag(v___x_843_) == 0)
{
lean_object* v_a_844_; lean_object* v___x_845_; lean_object* v___x_846_; 
v_a_844_ = lean_ctor_get(v___x_843_, 0);
lean_inc_n(v_a_844_, 2);
lean_dec_ref_known(v___x_843_, 1);
v___x_845_ = lean_box(0);
v___x_846_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_844_, v___x_845_, v___y_831_, v___y_832_, v___y_833_, v___y_834_);
if (lean_obj_tag(v___x_846_) == 0)
{
lean_object* v_a_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; 
v_a_847_ = lean_ctor_get(v___x_846_, 0);
lean_inc(v_a_847_);
lean_dec_ref_known(v___x_846_, 1);
v___x_848_ = lean_unsigned_to_nat(0u);
v___x_849_ = lean_array_get(v___x_824_, v_hyps_829_, v___x_848_);
lean_inc(v___y_834_);
lean_inc_ref(v___y_833_);
lean_inc(v___y_832_);
lean_inc_ref(v___y_831_);
lean_inc(v___x_849_);
v___x_850_ = lean_infer_type(v___x_849_, v___y_831_, v___y_832_, v___y_833_, v___y_834_);
if (lean_obj_tag(v___x_850_) == 0)
{
lean_object* v_a_851_; lean_object* v___y_853_; lean_object* v___y_854_; lean_object* v___y_855_; lean_object* v___y_856_; lean_object* v___x_871_; uint8_t v___x_872_; 
v_a_851_ = lean_ctor_get(v___x_850_, 0);
lean_inc(v_a_851_);
lean_dec_ref_known(v___x_850_, 1);
v___x_871_ = l_Lean_Expr_cleanupAnnotations(v_a_851_);
v___x_872_ = l_Lean_Expr_isApp(v___x_871_);
if (v___x_872_ == 0)
{
lean_dec_ref(v___x_871_);
lean_dec(v_a_847_);
lean_dec(v_a_844_);
lean_dec_ref(v_hyps_829_);
lean_dec(v_levelParams_828_);
lean_dec(v_thmName_827_);
lean_dec_ref(v_val_826_);
lean_dec(v___x_825_);
lean_dec_ref(v___x_824_);
lean_dec_ref(v_xs_822_);
v___y_853_ = v___y_831_;
v___y_854_ = v___y_832_;
v___y_855_ = v___y_833_;
v___y_856_ = v___y_834_;
goto v___jp_852_;
}
else
{
lean_object* v_arg_873_; lean_object* v___x_874_; uint8_t v___x_875_; 
v_arg_873_ = lean_ctor_get(v___x_871_, 1);
lean_inc_ref(v_arg_873_);
v___x_874_ = l_Lean_Expr_appFnCleanup___redArg(v___x_871_);
v___x_875_ = l_Lean_Expr_isApp(v___x_874_);
if (v___x_875_ == 0)
{
lean_dec_ref(v___x_874_);
lean_dec_ref(v_arg_873_);
lean_dec(v_a_847_);
lean_dec(v_a_844_);
lean_dec_ref(v_hyps_829_);
lean_dec(v_levelParams_828_);
lean_dec(v_thmName_827_);
lean_dec_ref(v_val_826_);
lean_dec(v___x_825_);
lean_dec_ref(v___x_824_);
lean_dec_ref(v_xs_822_);
v___y_853_ = v___y_831_;
v___y_854_ = v___y_832_;
v___y_855_ = v___y_833_;
v___y_856_ = v___y_834_;
goto v___jp_852_;
}
else
{
lean_object* v_arg_876_; lean_object* v___x_877_; lean_object* v___x_878_; uint8_t v___x_879_; 
v_arg_876_ = lean_ctor_get(v___x_874_, 1);
lean_inc_ref(v_arg_876_);
v___x_877_ = l_Lean_Expr_appFnCleanup___redArg(v___x_874_);
v___x_878_ = ((lean_object*)(l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__1___closed__6));
v___x_879_ = l_Lean_Expr_isConstOf(v___x_877_, v___x_878_);
lean_dec_ref(v___x_877_);
if (v___x_879_ == 0)
{
lean_dec_ref(v_arg_876_);
lean_dec_ref(v_arg_873_);
lean_dec(v_a_847_);
lean_dec(v_a_844_);
lean_dec_ref(v_hyps_829_);
lean_dec(v_levelParams_828_);
lean_dec(v_thmName_827_);
lean_dec_ref(v_val_826_);
lean_dec(v___x_825_);
lean_dec_ref(v___x_824_);
lean_dec_ref(v_xs_822_);
v___y_853_ = v___y_831_;
v___y_854_ = v___y_832_;
v___y_855_ = v___y_833_;
v___y_856_ = v___y_834_;
goto v___jp_852_;
}
else
{
lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; 
v___x_880_ = l_Lean_Expr_mvarId_x21(v_a_847_);
v___x_881_ = ((lean_object*)(l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__1___closed__8));
v___x_882_ = ((lean_object*)(l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__1___closed__9));
lean_inc(v___x_825_);
v___x_883_ = l_Lean_mkConst(v___x_882_, v___x_825_);
v___x_884_ = ((lean_object*)(l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__1___closed__11));
v___x_885_ = l_Lean_MVarId_assertExt(v___x_880_, v___x_881_, v___x_883_, v_arg_873_, v___x_884_, v___y_831_, v___y_832_, v___y_833_, v___y_834_);
if (lean_obj_tag(v___x_885_) == 0)
{
lean_object* v_a_886_; lean_object* v___x_887_; 
v_a_886_ = lean_ctor_get(v___x_885_, 0);
lean_inc(v_a_886_);
lean_dec_ref_known(v___x_885_, 1);
v___x_887_ = l_Lean_Meta_intro1Core(v_a_886_, v___x_879_, v___y_831_, v___y_832_, v___y_833_, v___y_834_);
if (lean_obj_tag(v___x_887_) == 0)
{
lean_object* v_a_888_; lean_object* v_fst_889_; lean_object* v_snd_890_; lean_object* v___x_891_; 
v_a_888_ = lean_ctor_get(v___x_887_, 0);
lean_inc(v_a_888_);
lean_dec_ref_known(v___x_887_, 1);
v_fst_889_ = lean_ctor_get(v_a_888_, 0);
lean_inc(v_fst_889_);
v_snd_890_ = lean_ctor_get(v_a_888_, 1);
lean_inc(v_snd_890_);
lean_dec(v_a_888_);
v___x_891_ = l_Lean_Meta_intro1Core(v_snd_890_, v___x_879_, v___y_831_, v___y_832_, v___y_833_, v___y_834_);
if (lean_obj_tag(v___x_891_) == 0)
{
lean_object* v_a_892_; lean_object* v_fst_893_; lean_object* v_snd_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___f_899_; lean_object* v___x_900_; 
v_a_892_ = lean_ctor_get(v___x_891_, 0);
lean_inc(v_a_892_);
lean_dec_ref_known(v___x_891_, 1);
v_fst_893_ = lean_ctor_get(v_a_892_, 0);
lean_inc(v_fst_893_);
v_snd_894_ = lean_ctor_get(v_a_892_, 1);
lean_inc_n(v_snd_894_, 2);
lean_dec(v_a_892_);
v___x_895_ = l_Lean_mkConst(v___x_878_, v___x_825_);
v___x_896_ = l_Lean_mkFVar(v_fst_889_);
v___x_897_ = l_Lean_mkAppB(v___x_895_, v_arg_876_, v___x_896_);
v___x_898_ = lean_box(v___x_879_);
v___f_899_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__0___boxed), 20, 15);
lean_closure_set(v___f_899_, 0, v___x_897_);
lean_closure_set(v___f_899_, 1, v___x_845_);
lean_closure_set(v___f_899_, 2, v_fst_893_);
lean_closure_set(v___f_899_, 3, v___x_849_);
lean_closure_set(v___f_899_, 4, v_snd_894_);
lean_closure_set(v___f_899_, 5, v_val_826_);
lean_closure_set(v___f_899_, 6, v___x_824_);
lean_closure_set(v___f_899_, 7, v_xs_822_);
lean_closure_set(v___f_899_, 8, v___x_848_);
lean_closure_set(v___f_899_, 9, v_a_847_);
lean_closure_set(v___f_899_, 10, v_hyps_829_);
lean_closure_set(v___f_899_, 11, v_a_844_);
lean_closure_set(v___f_899_, 12, v___x_898_);
lean_closure_set(v___f_899_, 13, v_thmName_827_);
lean_closure_set(v___f_899_, 14, v_levelParams_828_);
v___x_900_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__5___redArg(v_snd_894_, v___f_899_, v___y_831_, v___y_832_, v___y_833_, v___y_834_);
return v___x_900_;
}
else
{
lean_object* v_a_901_; lean_object* v___x_903_; uint8_t v_isShared_904_; uint8_t v_isSharedCheck_908_; 
lean_dec(v_fst_889_);
lean_dec_ref(v_arg_876_);
lean_dec(v___x_849_);
lean_dec(v_a_847_);
lean_dec(v_a_844_);
lean_dec_ref(v_hyps_829_);
lean_dec(v_levelParams_828_);
lean_dec(v_thmName_827_);
lean_dec_ref(v_val_826_);
lean_dec(v___x_825_);
lean_dec_ref(v___x_824_);
lean_dec_ref(v_xs_822_);
v_a_901_ = lean_ctor_get(v___x_891_, 0);
v_isSharedCheck_908_ = !lean_is_exclusive(v___x_891_);
if (v_isSharedCheck_908_ == 0)
{
v___x_903_ = v___x_891_;
v_isShared_904_ = v_isSharedCheck_908_;
goto v_resetjp_902_;
}
else
{
lean_inc(v_a_901_);
lean_dec(v___x_891_);
v___x_903_ = lean_box(0);
v_isShared_904_ = v_isSharedCheck_908_;
goto v_resetjp_902_;
}
v_resetjp_902_:
{
lean_object* v___x_906_; 
if (v_isShared_904_ == 0)
{
v___x_906_ = v___x_903_;
goto v_reusejp_905_;
}
else
{
lean_object* v_reuseFailAlloc_907_; 
v_reuseFailAlloc_907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_907_, 0, v_a_901_);
v___x_906_ = v_reuseFailAlloc_907_;
goto v_reusejp_905_;
}
v_reusejp_905_:
{
return v___x_906_;
}
}
}
}
else
{
lean_object* v_a_909_; lean_object* v___x_911_; uint8_t v_isShared_912_; uint8_t v_isSharedCheck_916_; 
lean_dec_ref(v_arg_876_);
lean_dec(v___x_849_);
lean_dec(v_a_847_);
lean_dec(v_a_844_);
lean_dec_ref(v_hyps_829_);
lean_dec(v_levelParams_828_);
lean_dec(v_thmName_827_);
lean_dec_ref(v_val_826_);
lean_dec(v___x_825_);
lean_dec_ref(v___x_824_);
lean_dec_ref(v_xs_822_);
v_a_909_ = lean_ctor_get(v___x_887_, 0);
v_isSharedCheck_916_ = !lean_is_exclusive(v___x_887_);
if (v_isSharedCheck_916_ == 0)
{
v___x_911_ = v___x_887_;
v_isShared_912_ = v_isSharedCheck_916_;
goto v_resetjp_910_;
}
else
{
lean_inc(v_a_909_);
lean_dec(v___x_887_);
v___x_911_ = lean_box(0);
v_isShared_912_ = v_isSharedCheck_916_;
goto v_resetjp_910_;
}
v_resetjp_910_:
{
lean_object* v___x_914_; 
if (v_isShared_912_ == 0)
{
v___x_914_ = v___x_911_;
goto v_reusejp_913_;
}
else
{
lean_object* v_reuseFailAlloc_915_; 
v_reuseFailAlloc_915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_915_, 0, v_a_909_);
v___x_914_ = v_reuseFailAlloc_915_;
goto v_reusejp_913_;
}
v_reusejp_913_:
{
return v___x_914_;
}
}
}
}
else
{
lean_object* v_a_917_; lean_object* v___x_919_; uint8_t v_isShared_920_; uint8_t v_isSharedCheck_924_; 
lean_dec_ref(v_arg_876_);
lean_dec(v___x_849_);
lean_dec(v_a_847_);
lean_dec(v_a_844_);
lean_dec_ref(v_hyps_829_);
lean_dec(v_levelParams_828_);
lean_dec(v_thmName_827_);
lean_dec_ref(v_val_826_);
lean_dec(v___x_825_);
lean_dec_ref(v___x_824_);
lean_dec_ref(v_xs_822_);
v_a_917_ = lean_ctor_get(v___x_885_, 0);
v_isSharedCheck_924_ = !lean_is_exclusive(v___x_885_);
if (v_isSharedCheck_924_ == 0)
{
v___x_919_ = v___x_885_;
v_isShared_920_ = v_isSharedCheck_924_;
goto v_resetjp_918_;
}
else
{
lean_inc(v_a_917_);
lean_dec(v___x_885_);
v___x_919_ = lean_box(0);
v_isShared_920_ = v_isSharedCheck_924_;
goto v_resetjp_918_;
}
v_resetjp_918_:
{
lean_object* v___x_922_; 
if (v_isShared_920_ == 0)
{
v___x_922_ = v___x_919_;
goto v_reusejp_921_;
}
else
{
lean_object* v_reuseFailAlloc_923_; 
v_reuseFailAlloc_923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_923_, 0, v_a_917_);
v___x_922_ = v_reuseFailAlloc_923_;
goto v_reusejp_921_;
}
v_reusejp_921_:
{
return v___x_922_;
}
}
}
}
}
}
v___jp_852_:
{
lean_object* v___x_857_; 
lean_inc(v___y_856_);
lean_inc_ref(v___y_855_);
lean_inc(v___y_854_);
lean_inc_ref(v___y_853_);
v___x_857_ = lean_infer_type(v___x_849_, v___y_853_, v___y_854_, v___y_855_, v___y_856_);
if (lean_obj_tag(v___x_857_) == 0)
{
lean_object* v_a_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; 
v_a_858_ = lean_ctor_get(v___x_857_, 0);
lean_inc(v_a_858_);
lean_dec_ref_known(v___x_857_, 1);
v___x_859_ = lean_obj_once(&l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__1___closed__3, &l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__1___closed__3_once, _init_l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__1___closed__3);
v___x_860_ = l_Lean_MessageData_ofExpr(v_a_858_);
v___x_861_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_861_, 0, v___x_859_);
lean_ctor_set(v___x_861_, 1, v___x_860_);
v___x_862_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__3___redArg(v___x_861_, v___y_853_, v___y_854_, v___y_855_, v___y_856_);
return v___x_862_;
}
else
{
lean_object* v_a_863_; lean_object* v___x_865_; uint8_t v_isShared_866_; uint8_t v_isSharedCheck_870_; 
v_a_863_ = lean_ctor_get(v___x_857_, 0);
v_isSharedCheck_870_ = !lean_is_exclusive(v___x_857_);
if (v_isSharedCheck_870_ == 0)
{
v___x_865_ = v___x_857_;
v_isShared_866_ = v_isSharedCheck_870_;
goto v_resetjp_864_;
}
else
{
lean_inc(v_a_863_);
lean_dec(v___x_857_);
v___x_865_ = lean_box(0);
v_isShared_866_ = v_isSharedCheck_870_;
goto v_resetjp_864_;
}
v_resetjp_864_:
{
lean_object* v___x_868_; 
if (v_isShared_866_ == 0)
{
v___x_868_ = v___x_865_;
goto v_reusejp_867_;
}
else
{
lean_object* v_reuseFailAlloc_869_; 
v_reuseFailAlloc_869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_869_, 0, v_a_863_);
v___x_868_ = v_reuseFailAlloc_869_;
goto v_reusejp_867_;
}
v_reusejp_867_:
{
return v___x_868_;
}
}
}
}
}
else
{
lean_object* v_a_925_; lean_object* v___x_927_; uint8_t v_isShared_928_; uint8_t v_isSharedCheck_932_; 
lean_dec(v___x_849_);
lean_dec(v_a_847_);
lean_dec(v_a_844_);
lean_dec_ref(v_hyps_829_);
lean_dec(v_levelParams_828_);
lean_dec(v_thmName_827_);
lean_dec_ref(v_val_826_);
lean_dec(v___x_825_);
lean_dec_ref(v___x_824_);
lean_dec_ref(v_xs_822_);
v_a_925_ = lean_ctor_get(v___x_850_, 0);
v_isSharedCheck_932_ = !lean_is_exclusive(v___x_850_);
if (v_isSharedCheck_932_ == 0)
{
v___x_927_ = v___x_850_;
v_isShared_928_ = v_isSharedCheck_932_;
goto v_resetjp_926_;
}
else
{
lean_inc(v_a_925_);
lean_dec(v___x_850_);
v___x_927_ = lean_box(0);
v_isShared_928_ = v_isSharedCheck_932_;
goto v_resetjp_926_;
}
v_resetjp_926_:
{
lean_object* v___x_930_; 
if (v_isShared_928_ == 0)
{
v___x_930_ = v___x_927_;
goto v_reusejp_929_;
}
else
{
lean_object* v_reuseFailAlloc_931_; 
v_reuseFailAlloc_931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_931_, 0, v_a_925_);
v___x_930_ = v_reuseFailAlloc_931_;
goto v_reusejp_929_;
}
v_reusejp_929_:
{
return v___x_930_;
}
}
}
}
else
{
lean_object* v_a_933_; lean_object* v___x_935_; uint8_t v_isShared_936_; uint8_t v_isSharedCheck_940_; 
lean_dec(v_a_844_);
lean_dec_ref(v_hyps_829_);
lean_dec(v_levelParams_828_);
lean_dec(v_thmName_827_);
lean_dec_ref(v_val_826_);
lean_dec(v___x_825_);
lean_dec_ref(v___x_824_);
lean_dec_ref(v_xs_822_);
v_a_933_ = lean_ctor_get(v___x_846_, 0);
v_isSharedCheck_940_ = !lean_is_exclusive(v___x_846_);
if (v_isSharedCheck_940_ == 0)
{
v___x_935_ = v___x_846_;
v_isShared_936_ = v_isSharedCheck_940_;
goto v_resetjp_934_;
}
else
{
lean_inc(v_a_933_);
lean_dec(v___x_846_);
v___x_935_ = lean_box(0);
v_isShared_936_ = v_isSharedCheck_940_;
goto v_resetjp_934_;
}
v_resetjp_934_:
{
lean_object* v___x_938_; 
if (v_isShared_936_ == 0)
{
v___x_938_ = v___x_935_;
goto v_reusejp_937_;
}
else
{
lean_object* v_reuseFailAlloc_939_; 
v_reuseFailAlloc_939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_939_, 0, v_a_933_);
v___x_938_ = v_reuseFailAlloc_939_;
goto v_reusejp_937_;
}
v_reusejp_937_:
{
return v___x_938_;
}
}
}
}
else
{
lean_object* v_a_941_; lean_object* v___x_943_; uint8_t v_isShared_944_; uint8_t v_isSharedCheck_948_; 
lean_dec_ref(v_hyps_829_);
lean_dec(v_levelParams_828_);
lean_dec(v_thmName_827_);
lean_dec_ref(v_val_826_);
lean_dec(v___x_825_);
lean_dec_ref(v___x_824_);
lean_dec_ref(v_xs_822_);
v_a_941_ = lean_ctor_get(v___x_843_, 0);
v_isSharedCheck_948_ = !lean_is_exclusive(v___x_843_);
if (v_isSharedCheck_948_ == 0)
{
v___x_943_ = v___x_843_;
v_isShared_944_ = v_isSharedCheck_948_;
goto v_resetjp_942_;
}
else
{
lean_inc(v_a_941_);
lean_dec(v___x_843_);
v___x_943_ = lean_box(0);
v_isShared_944_ = v_isSharedCheck_948_;
goto v_resetjp_942_;
}
v_resetjp_942_:
{
lean_object* v___x_946_; 
if (v_isShared_944_ == 0)
{
v___x_946_ = v___x_943_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v_a_941_);
v___x_946_ = v_reuseFailAlloc_947_;
goto v_reusejp_945_;
}
v_reusejp_945_:
{
return v___x_946_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__1___boxed(lean_object** _args){
lean_object* v___x_949_ = _args[0];
lean_object* v_sparseCasesOnName_950_ = _args[1];
lean_object* v___x_951_ = _args[2];
lean_object* v_xs_952_ = _args[3];
lean_object* v___x_953_ = _args[4];
lean_object* v___x_954_ = _args[5];
lean_object* v___x_955_ = _args[6];
lean_object* v_val_956_ = _args[7];
lean_object* v_thmName_957_ = _args[8];
lean_object* v_levelParams_958_ = _args[9];
lean_object* v_hyps_959_ = _args[10];
lean_object* v_x_960_ = _args[11];
lean_object* v___y_961_ = _args[12];
lean_object* v___y_962_ = _args[13];
lean_object* v___y_963_ = _args[14];
lean_object* v___y_964_ = _args[15];
lean_object* v___y_965_ = _args[16];
_start:
{
lean_object* v_res_966_; 
v_res_966_ = l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__1(v___x_949_, v_sparseCasesOnName_950_, v___x_951_, v_xs_952_, v___x_953_, v___x_954_, v___x_955_, v_val_956_, v_thmName_957_, v_levelParams_958_, v_hyps_959_, v_x_960_, v___y_961_, v___y_962_, v___y_963_, v___y_964_);
lean_dec(v___y_964_);
lean_dec_ref(v___y_963_);
lean_dec(v___y_962_);
lean_dec_ref(v___y_961_);
lean_dec_ref(v_x_960_);
lean_dec(v___x_949_);
return v_res_966_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__2(lean_object* v___x_967_, lean_object* v_sparseCasesOnName_968_, lean_object* v___x_969_, lean_object* v___x_970_, lean_object* v_val_971_, lean_object* v_thmName_972_, lean_object* v_levelParams_973_, lean_object* v_xs_974_, lean_object* v_x_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_){
_start:
{
lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; 
v___x_981_ = lean_array_get_size(v_xs_974_);
v___x_982_ = lean_unsigned_to_nat(1u);
v___x_983_ = lean_nat_sub(v___x_981_, v___x_982_);
v___x_984_ = lean_array_get(v___x_967_, v_xs_974_, v___x_983_);
lean_dec(v___x_983_);
lean_inc(v___y_979_);
lean_inc_ref(v___y_978_);
lean_inc(v___y_977_);
lean_inc_ref(v___y_976_);
lean_inc(v___x_984_);
v___x_985_ = lean_infer_type(v___x_984_, v___y_976_, v___y_977_, v___y_978_, v___y_979_);
if (lean_obj_tag(v___x_985_) == 0)
{
lean_object* v_a_986_; lean_object* v___f_987_; uint8_t v___x_988_; lean_object* v___x_989_; 
v_a_986_ = lean_ctor_get(v___x_985_, 0);
lean_inc(v_a_986_);
lean_dec_ref_known(v___x_985_, 1);
v___f_987_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__1___boxed), 17, 10);
lean_closure_set(v___f_987_, 0, v___x_982_);
lean_closure_set(v___f_987_, 1, v_sparseCasesOnName_968_);
lean_closure_set(v___f_987_, 2, v___x_969_);
lean_closure_set(v___f_987_, 3, v_xs_974_);
lean_closure_set(v___f_987_, 4, v___x_984_);
lean_closure_set(v___f_987_, 5, v___x_967_);
lean_closure_set(v___f_987_, 6, v___x_970_);
lean_closure_set(v___f_987_, 7, v_val_971_);
lean_closure_set(v___f_987_, 8, v_thmName_972_);
lean_closure_set(v___f_987_, 9, v_levelParams_973_);
v___x_988_ = 0;
v___x_989_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__9___redArg(v_a_986_, v___f_987_, v___x_988_, v___y_976_, v___y_977_, v___y_978_, v___y_979_);
return v___x_989_;
}
else
{
lean_object* v_a_990_; lean_object* v___x_992_; uint8_t v_isShared_993_; uint8_t v_isSharedCheck_997_; 
lean_dec(v___x_984_);
lean_dec_ref(v_xs_974_);
lean_dec(v_levelParams_973_);
lean_dec(v_thmName_972_);
lean_dec_ref(v_val_971_);
lean_dec(v___x_970_);
lean_dec(v___x_969_);
lean_dec(v_sparseCasesOnName_968_);
lean_dec_ref(v___x_967_);
v_a_990_ = lean_ctor_get(v___x_985_, 0);
v_isSharedCheck_997_ = !lean_is_exclusive(v___x_985_);
if (v_isSharedCheck_997_ == 0)
{
v___x_992_ = v___x_985_;
v_isShared_993_ = v_isSharedCheck_997_;
goto v_resetjp_991_;
}
else
{
lean_inc(v_a_990_);
lean_dec(v___x_985_);
v___x_992_ = lean_box(0);
v_isShared_993_ = v_isSharedCheck_997_;
goto v_resetjp_991_;
}
v_resetjp_991_:
{
lean_object* v___x_995_; 
if (v_isShared_993_ == 0)
{
v___x_995_ = v___x_992_;
goto v_reusejp_994_;
}
else
{
lean_object* v_reuseFailAlloc_996_; 
v_reuseFailAlloc_996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_996_, 0, v_a_990_);
v___x_995_ = v_reuseFailAlloc_996_;
goto v_reusejp_994_;
}
v_reusejp_994_:
{
return v___x_995_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__2___boxed(lean_object* v___x_998_, lean_object* v_sparseCasesOnName_999_, lean_object* v___x_1000_, lean_object* v___x_1001_, lean_object* v_val_1002_, lean_object* v_thmName_1003_, lean_object* v_levelParams_1004_, lean_object* v_xs_1005_, lean_object* v_x_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_){
_start:
{
lean_object* v_res_1012_; 
v_res_1012_ = l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__2(v___x_998_, v_sparseCasesOnName_999_, v___x_1000_, v___x_1001_, v_val_1002_, v_thmName_1003_, v_levelParams_1004_, v_xs_1005_, v_x_1006_, v___y_1007_, v___y_1008_, v___y_1009_, v___y_1010_);
lean_dec(v___y_1010_);
lean_dec_ref(v___y_1009_);
lean_dec(v___y_1008_);
lean_dec_ref(v___y_1007_);
lean_dec_ref(v_x_1006_);
return v_res_1012_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__15___redArg(lean_object* v_ref_1013_, lean_object* v_msg_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_){
_start:
{
lean_object* v_fileName_1020_; lean_object* v_fileMap_1021_; lean_object* v_options_1022_; lean_object* v_currRecDepth_1023_; lean_object* v_maxRecDepth_1024_; lean_object* v_ref_1025_; lean_object* v_currNamespace_1026_; lean_object* v_openDecls_1027_; lean_object* v_initHeartbeats_1028_; lean_object* v_maxHeartbeats_1029_; lean_object* v_quotContext_1030_; lean_object* v_currMacroScope_1031_; uint8_t v_diag_1032_; lean_object* v_cancelTk_x3f_1033_; uint8_t v_suppressElabErrors_1034_; lean_object* v_inheritedTraceOptions_1035_; lean_object* v_ref_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; 
v_fileName_1020_ = lean_ctor_get(v___y_1017_, 0);
v_fileMap_1021_ = lean_ctor_get(v___y_1017_, 1);
v_options_1022_ = lean_ctor_get(v___y_1017_, 2);
v_currRecDepth_1023_ = lean_ctor_get(v___y_1017_, 3);
v_maxRecDepth_1024_ = lean_ctor_get(v___y_1017_, 4);
v_ref_1025_ = lean_ctor_get(v___y_1017_, 5);
v_currNamespace_1026_ = lean_ctor_get(v___y_1017_, 6);
v_openDecls_1027_ = lean_ctor_get(v___y_1017_, 7);
v_initHeartbeats_1028_ = lean_ctor_get(v___y_1017_, 8);
v_maxHeartbeats_1029_ = lean_ctor_get(v___y_1017_, 9);
v_quotContext_1030_ = lean_ctor_get(v___y_1017_, 10);
v_currMacroScope_1031_ = lean_ctor_get(v___y_1017_, 11);
v_diag_1032_ = lean_ctor_get_uint8(v___y_1017_, sizeof(void*)*14);
v_cancelTk_x3f_1033_ = lean_ctor_get(v___y_1017_, 12);
v_suppressElabErrors_1034_ = lean_ctor_get_uint8(v___y_1017_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1035_ = lean_ctor_get(v___y_1017_, 13);
v_ref_1036_ = l_Lean_replaceRef(v_ref_1013_, v_ref_1025_);
lean_inc_ref(v_inheritedTraceOptions_1035_);
lean_inc(v_cancelTk_x3f_1033_);
lean_inc(v_currMacroScope_1031_);
lean_inc(v_quotContext_1030_);
lean_inc(v_maxHeartbeats_1029_);
lean_inc(v_initHeartbeats_1028_);
lean_inc(v_openDecls_1027_);
lean_inc(v_currNamespace_1026_);
lean_inc(v_maxRecDepth_1024_);
lean_inc(v_currRecDepth_1023_);
lean_inc_ref(v_options_1022_);
lean_inc_ref(v_fileMap_1021_);
lean_inc_ref(v_fileName_1020_);
v___x_1037_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1037_, 0, v_fileName_1020_);
lean_ctor_set(v___x_1037_, 1, v_fileMap_1021_);
lean_ctor_set(v___x_1037_, 2, v_options_1022_);
lean_ctor_set(v___x_1037_, 3, v_currRecDepth_1023_);
lean_ctor_set(v___x_1037_, 4, v_maxRecDepth_1024_);
lean_ctor_set(v___x_1037_, 5, v_ref_1036_);
lean_ctor_set(v___x_1037_, 6, v_currNamespace_1026_);
lean_ctor_set(v___x_1037_, 7, v_openDecls_1027_);
lean_ctor_set(v___x_1037_, 8, v_initHeartbeats_1028_);
lean_ctor_set(v___x_1037_, 9, v_maxHeartbeats_1029_);
lean_ctor_set(v___x_1037_, 10, v_quotContext_1030_);
lean_ctor_set(v___x_1037_, 11, v_currMacroScope_1031_);
lean_ctor_set(v___x_1037_, 12, v_cancelTk_x3f_1033_);
lean_ctor_set(v___x_1037_, 13, v_inheritedTraceOptions_1035_);
lean_ctor_set_uint8(v___x_1037_, sizeof(void*)*14, v_diag_1032_);
lean_ctor_set_uint8(v___x_1037_, sizeof(void*)*14 + 1, v_suppressElabErrors_1034_);
v___x_1038_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__3___redArg(v_msg_1014_, v___y_1015_, v___y_1016_, v___x_1037_, v___y_1018_);
lean_dec_ref_known(v___x_1037_, 14);
return v___x_1038_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__15___redArg___boxed(lean_object* v_ref_1039_, lean_object* v_msg_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_){
_start:
{
lean_object* v_res_1046_; 
v_res_1046_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__15___redArg(v_ref_1039_, v_msg_1040_, v___y_1041_, v___y_1042_, v___y_1043_, v___y_1044_);
lean_dec(v___y_1044_);
lean_dec_ref(v___y_1043_);
lean_dec(v___y_1042_);
lean_dec_ref(v___y_1041_);
lean_dec(v_ref_1039_);
return v_res_1046_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__0(void){
_start:
{
lean_object* v___x_1047_; 
v___x_1047_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1047_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__1(void){
_start:
{
lean_object* v___x_1048_; lean_object* v___x_1049_; 
v___x_1048_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__0);
v___x_1049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1049_, 0, v___x_1048_);
return v___x_1049_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__2(void){
_start:
{
lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; 
v___x_1050_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__1);
v___x_1051_ = lean_unsigned_to_nat(0u);
v___x_1052_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_1052_, 0, v___x_1051_);
lean_ctor_set(v___x_1052_, 1, v___x_1051_);
lean_ctor_set(v___x_1052_, 2, v___x_1051_);
lean_ctor_set(v___x_1052_, 3, v___x_1051_);
lean_ctor_set(v___x_1052_, 4, v___x_1050_);
lean_ctor_set(v___x_1052_, 5, v___x_1050_);
lean_ctor_set(v___x_1052_, 6, v___x_1050_);
lean_ctor_set(v___x_1052_, 7, v___x_1050_);
lean_ctor_set(v___x_1052_, 8, v___x_1050_);
lean_ctor_set(v___x_1052_, 9, v___x_1050_);
lean_ctor_set(v___x_1052_, 10, v___x_1050_);
return v___x_1052_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__3(void){
_start:
{
lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; 
v___x_1053_ = lean_unsigned_to_nat(32u);
v___x_1054_ = lean_mk_empty_array_with_capacity(v___x_1053_);
v___x_1055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1055_, 0, v___x_1054_);
return v___x_1055_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__4(void){
_start:
{
size_t v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; 
v___x_1056_ = ((size_t)5ULL);
v___x_1057_ = lean_unsigned_to_nat(0u);
v___x_1058_ = lean_unsigned_to_nat(32u);
v___x_1059_ = lean_mk_empty_array_with_capacity(v___x_1058_);
v___x_1060_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__3);
v___x_1061_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1061_, 0, v___x_1060_);
lean_ctor_set(v___x_1061_, 1, v___x_1059_);
lean_ctor_set(v___x_1061_, 2, v___x_1057_);
lean_ctor_set(v___x_1061_, 3, v___x_1057_);
lean_ctor_set_usize(v___x_1061_, 4, v___x_1056_);
return v___x_1061_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__5(void){
_start:
{
lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; 
v___x_1062_ = lean_box(1);
v___x_1063_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__4);
v___x_1064_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__1);
v___x_1065_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1065_, 0, v___x_1064_);
lean_ctor_set(v___x_1065_, 1, v___x_1063_);
lean_ctor_set(v___x_1065_, 2, v___x_1062_);
return v___x_1065_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__7(void){
_start:
{
lean_object* v___x_1067_; lean_object* v___x_1068_; 
v___x_1067_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__6));
v___x_1068_ = l_Lean_stringToMessageData(v___x_1067_);
return v___x_1068_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__9(void){
_start:
{
lean_object* v___x_1070_; lean_object* v___x_1071_; 
v___x_1070_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__8));
v___x_1071_ = l_Lean_stringToMessageData(v___x_1070_);
return v___x_1071_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__11(void){
_start:
{
lean_object* v___x_1073_; lean_object* v___x_1074_; 
v___x_1073_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__10));
v___x_1074_ = l_Lean_stringToMessageData(v___x_1073_);
return v___x_1074_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__13(void){
_start:
{
lean_object* v___x_1076_; lean_object* v___x_1077_; 
v___x_1076_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__12));
v___x_1077_ = l_Lean_stringToMessageData(v___x_1076_);
return v___x_1077_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__15(void){
_start:
{
lean_object* v___x_1079_; lean_object* v___x_1080_; 
v___x_1079_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__14));
v___x_1080_ = l_Lean_stringToMessageData(v___x_1079_);
return v___x_1080_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__17(void){
_start:
{
lean_object* v___x_1082_; lean_object* v___x_1083_; 
v___x_1082_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__16));
v___x_1083_ = l_Lean_stringToMessageData(v___x_1082_);
return v___x_1083_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__19(void){
_start:
{
lean_object* v___x_1085_; lean_object* v___x_1086_; 
v___x_1085_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__18));
v___x_1086_ = l_Lean_stringToMessageData(v___x_1085_);
return v___x_1086_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg(lean_object* v_msg_1087_, lean_object* v_declHint_1088_, lean_object* v___y_1089_){
_start:
{
lean_object* v___x_1091_; lean_object* v_env_1092_; uint8_t v___x_1093_; 
v___x_1091_ = lean_st_ref_get(v___y_1089_);
v_env_1092_ = lean_ctor_get(v___x_1091_, 0);
lean_inc_ref(v_env_1092_);
lean_dec(v___x_1091_);
v___x_1093_ = l_Lean_Name_isAnonymous(v_declHint_1088_);
if (v___x_1093_ == 0)
{
uint8_t v_isExporting_1094_; 
v_isExporting_1094_ = lean_ctor_get_uint8(v_env_1092_, sizeof(void*)*8);
if (v_isExporting_1094_ == 0)
{
lean_object* v___x_1095_; 
lean_dec_ref(v_env_1092_);
lean_dec(v_declHint_1088_);
v___x_1095_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1095_, 0, v_msg_1087_);
return v___x_1095_;
}
else
{
lean_object* v___x_1096_; uint8_t v___x_1097_; 
lean_inc_ref(v_env_1092_);
v___x_1096_ = l_Lean_Environment_setExporting(v_env_1092_, v___x_1093_);
lean_inc(v_declHint_1088_);
lean_inc_ref(v___x_1096_);
v___x_1097_ = l_Lean_Environment_contains(v___x_1096_, v_declHint_1088_, v_isExporting_1094_);
if (v___x_1097_ == 0)
{
lean_object* v___x_1098_; 
lean_dec_ref(v___x_1096_);
lean_dec_ref(v_env_1092_);
lean_dec(v_declHint_1088_);
v___x_1098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1098_, 0, v_msg_1087_);
return v___x_1098_;
}
else
{
lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v_c_1104_; lean_object* v___x_1105_; 
v___x_1099_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__2);
v___x_1100_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__5);
v___x_1101_ = l_Lean_Options_empty;
v___x_1102_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1102_, 0, v___x_1096_);
lean_ctor_set(v___x_1102_, 1, v___x_1099_);
lean_ctor_set(v___x_1102_, 2, v___x_1100_);
lean_ctor_set(v___x_1102_, 3, v___x_1101_);
lean_inc(v_declHint_1088_);
v___x_1103_ = l_Lean_MessageData_ofConstName(v_declHint_1088_, v___x_1093_);
v_c_1104_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1104_, 0, v___x_1102_);
lean_ctor_set(v_c_1104_, 1, v___x_1103_);
v___x_1105_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1092_, v_declHint_1088_);
if (lean_obj_tag(v___x_1105_) == 0)
{
lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; 
lean_dec_ref(v_env_1092_);
lean_dec(v_declHint_1088_);
v___x_1106_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__7);
v___x_1107_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1107_, 0, v___x_1106_);
lean_ctor_set(v___x_1107_, 1, v_c_1104_);
v___x_1108_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__9);
v___x_1109_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1109_, 0, v___x_1107_);
lean_ctor_set(v___x_1109_, 1, v___x_1108_);
v___x_1110_ = l_Lean_MessageData_note(v___x_1109_);
v___x_1111_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1111_, 0, v_msg_1087_);
lean_ctor_set(v___x_1111_, 1, v___x_1110_);
v___x_1112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1112_, 0, v___x_1111_);
return v___x_1112_;
}
else
{
lean_object* v_val_1113_; lean_object* v___x_1115_; uint8_t v_isShared_1116_; uint8_t v_isSharedCheck_1148_; 
v_val_1113_ = lean_ctor_get(v___x_1105_, 0);
v_isSharedCheck_1148_ = !lean_is_exclusive(v___x_1105_);
if (v_isSharedCheck_1148_ == 0)
{
v___x_1115_ = v___x_1105_;
v_isShared_1116_ = v_isSharedCheck_1148_;
goto v_resetjp_1114_;
}
else
{
lean_inc(v_val_1113_);
lean_dec(v___x_1105_);
v___x_1115_ = lean_box(0);
v_isShared_1116_ = v_isSharedCheck_1148_;
goto v_resetjp_1114_;
}
v_resetjp_1114_:
{
lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v_mod_1120_; uint8_t v___x_1121_; 
v___x_1117_ = lean_box(0);
v___x_1118_ = l_Lean_Environment_header(v_env_1092_);
lean_dec_ref(v_env_1092_);
v___x_1119_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1118_);
v_mod_1120_ = lean_array_get(v___x_1117_, v___x_1119_, v_val_1113_);
lean_dec(v_val_1113_);
lean_dec_ref(v___x_1119_);
v___x_1121_ = l_Lean_isPrivateName(v_declHint_1088_);
lean_dec(v_declHint_1088_);
if (v___x_1121_ == 0)
{
lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1133_; 
v___x_1122_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__11);
v___x_1123_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1123_, 0, v___x_1122_);
lean_ctor_set(v___x_1123_, 1, v_c_1104_);
v___x_1124_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__13);
v___x_1125_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1125_, 0, v___x_1123_);
lean_ctor_set(v___x_1125_, 1, v___x_1124_);
v___x_1126_ = l_Lean_MessageData_ofName(v_mod_1120_);
v___x_1127_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1127_, 0, v___x_1125_);
lean_ctor_set(v___x_1127_, 1, v___x_1126_);
v___x_1128_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__15);
v___x_1129_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1129_, 0, v___x_1127_);
lean_ctor_set(v___x_1129_, 1, v___x_1128_);
v___x_1130_ = l_Lean_MessageData_note(v___x_1129_);
v___x_1131_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1131_, 0, v_msg_1087_);
lean_ctor_set(v___x_1131_, 1, v___x_1130_);
if (v_isShared_1116_ == 0)
{
lean_ctor_set_tag(v___x_1115_, 0);
lean_ctor_set(v___x_1115_, 0, v___x_1131_);
v___x_1133_ = v___x_1115_;
goto v_reusejp_1132_;
}
else
{
lean_object* v_reuseFailAlloc_1134_; 
v_reuseFailAlloc_1134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1134_, 0, v___x_1131_);
v___x_1133_ = v_reuseFailAlloc_1134_;
goto v_reusejp_1132_;
}
v_reusejp_1132_:
{
return v___x_1133_;
}
}
else
{
lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1146_; 
v___x_1135_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__7);
v___x_1136_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1136_, 0, v___x_1135_);
lean_ctor_set(v___x_1136_, 1, v_c_1104_);
v___x_1137_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__17);
v___x_1138_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1138_, 0, v___x_1136_);
lean_ctor_set(v___x_1138_, 1, v___x_1137_);
v___x_1139_ = l_Lean_MessageData_ofName(v_mod_1120_);
v___x_1140_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1140_, 0, v___x_1138_);
lean_ctor_set(v___x_1140_, 1, v___x_1139_);
v___x_1141_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__19);
v___x_1142_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1142_, 0, v___x_1140_);
lean_ctor_set(v___x_1142_, 1, v___x_1141_);
v___x_1143_ = l_Lean_MessageData_note(v___x_1142_);
v___x_1144_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1144_, 0, v_msg_1087_);
lean_ctor_set(v___x_1144_, 1, v___x_1143_);
if (v_isShared_1116_ == 0)
{
lean_ctor_set_tag(v___x_1115_, 0);
lean_ctor_set(v___x_1115_, 0, v___x_1144_);
v___x_1146_ = v___x_1115_;
goto v_reusejp_1145_;
}
else
{
lean_object* v_reuseFailAlloc_1147_; 
v_reuseFailAlloc_1147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1147_, 0, v___x_1144_);
v___x_1146_ = v_reuseFailAlloc_1147_;
goto v_reusejp_1145_;
}
v_reusejp_1145_:
{
return v___x_1146_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1149_; 
lean_dec_ref(v_env_1092_);
lean_dec(v_declHint_1088_);
v___x_1149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1149_, 0, v_msg_1087_);
return v___x_1149_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___boxed(lean_object* v_msg_1150_, lean_object* v_declHint_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_){
_start:
{
lean_object* v_res_1154_; 
v_res_1154_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg(v_msg_1150_, v_declHint_1151_, v___y_1152_);
lean_dec(v___y_1152_);
return v_res_1154_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14(lean_object* v_msg_1155_, lean_object* v_declHint_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_){
_start:
{
lean_object* v___x_1162_; lean_object* v_a_1163_; lean_object* v___x_1165_; uint8_t v_isShared_1166_; uint8_t v_isSharedCheck_1172_; 
v___x_1162_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg(v_msg_1155_, v_declHint_1156_, v___y_1160_);
v_a_1163_ = lean_ctor_get(v___x_1162_, 0);
v_isSharedCheck_1172_ = !lean_is_exclusive(v___x_1162_);
if (v_isSharedCheck_1172_ == 0)
{
v___x_1165_ = v___x_1162_;
v_isShared_1166_ = v_isSharedCheck_1172_;
goto v_resetjp_1164_;
}
else
{
lean_inc(v_a_1163_);
lean_dec(v___x_1162_);
v___x_1165_ = lean_box(0);
v_isShared_1166_ = v_isSharedCheck_1172_;
goto v_resetjp_1164_;
}
v_resetjp_1164_:
{
lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1170_; 
v___x_1167_ = l_Lean_unknownIdentifierMessageTag;
v___x_1168_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1168_, 0, v___x_1167_);
lean_ctor_set(v___x_1168_, 1, v_a_1163_);
if (v_isShared_1166_ == 0)
{
lean_ctor_set(v___x_1165_, 0, v___x_1168_);
v___x_1170_ = v___x_1165_;
goto v_reusejp_1169_;
}
else
{
lean_object* v_reuseFailAlloc_1171_; 
v_reuseFailAlloc_1171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1171_, 0, v___x_1168_);
v___x_1170_ = v_reuseFailAlloc_1171_;
goto v_reusejp_1169_;
}
v_reusejp_1169_:
{
return v___x_1170_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14___boxed(lean_object* v_msg_1173_, lean_object* v_declHint_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_){
_start:
{
lean_object* v_res_1180_; 
v_res_1180_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14(v_msg_1173_, v_declHint_1174_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_);
lean_dec(v___y_1178_);
lean_dec_ref(v___y_1177_);
lean_dec(v___y_1176_);
lean_dec_ref(v___y_1175_);
return v_res_1180_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12___redArg(lean_object* v_ref_1181_, lean_object* v_msg_1182_, lean_object* v_declHint_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_){
_start:
{
lean_object* v___x_1189_; lean_object* v_a_1190_; lean_object* v___x_1191_; 
v___x_1189_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14(v_msg_1182_, v_declHint_1183_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_);
v_a_1190_ = lean_ctor_get(v___x_1189_, 0);
lean_inc(v_a_1190_);
lean_dec_ref(v___x_1189_);
v___x_1191_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__15___redArg(v_ref_1181_, v_a_1190_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_);
return v___x_1191_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12___redArg___boxed(lean_object* v_ref_1192_, lean_object* v_msg_1193_, lean_object* v_declHint_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_){
_start:
{
lean_object* v_res_1200_; 
v_res_1200_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12___redArg(v_ref_1192_, v_msg_1193_, v_declHint_1194_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_);
lean_dec(v___y_1198_);
lean_dec_ref(v___y_1197_);
lean_dec(v___y_1196_);
lean_dec_ref(v___y_1195_);
lean_dec(v_ref_1192_);
return v_res_1200_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_1202_; lean_object* v___x_1203_; 
v___x_1202_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6___redArg___closed__0));
v___x_1203_ = l_Lean_stringToMessageData(v___x_1202_);
return v___x_1203_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_1205_; lean_object* v___x_1206_; 
v___x_1205_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6___redArg___closed__2));
v___x_1206_ = l_Lean_stringToMessageData(v___x_1205_);
return v___x_1206_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6___redArg(lean_object* v_ref_1207_, lean_object* v_constName_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_){
_start:
{
lean_object* v___x_1214_; uint8_t v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; 
v___x_1214_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6___redArg___closed__1);
v___x_1215_ = 0;
lean_inc(v_constName_1208_);
v___x_1216_ = l_Lean_MessageData_ofConstName(v_constName_1208_, v___x_1215_);
v___x_1217_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1217_, 0, v___x_1214_);
lean_ctor_set(v___x_1217_, 1, v___x_1216_);
v___x_1218_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6___redArg___closed__3);
v___x_1219_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1219_, 0, v___x_1217_);
lean_ctor_set(v___x_1219_, 1, v___x_1218_);
v___x_1220_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12___redArg(v_ref_1207_, v___x_1219_, v_constName_1208_, v___y_1209_, v___y_1210_, v___y_1211_, v___y_1212_);
return v___x_1220_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6___redArg___boxed(lean_object* v_ref_1221_, lean_object* v_constName_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_){
_start:
{
lean_object* v_res_1228_; 
v_res_1228_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6___redArg(v_ref_1221_, v_constName_1222_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_);
lean_dec(v___y_1226_);
lean_dec_ref(v___y_1225_);
lean_dec(v___y_1224_);
lean_dec_ref(v___y_1223_);
lean_dec(v_ref_1221_);
return v_res_1228_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0___redArg(lean_object* v_constName_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_){
_start:
{
lean_object* v_ref_1235_; lean_object* v___x_1236_; 
v_ref_1235_ = lean_ctor_get(v___y_1232_, 5);
v___x_1236_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6___redArg(v_ref_1235_, v_constName_1229_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_);
return v___x_1236_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0___redArg___boxed(lean_object* v_constName_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_){
_start:
{
lean_object* v_res_1243_; 
v_res_1243_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0___redArg(v_constName_1237_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_);
lean_dec(v___y_1241_);
lean_dec_ref(v___y_1240_);
lean_dec(v___y_1239_);
lean_dec_ref(v___y_1238_);
return v_res_1243_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0(lean_object* v_constName_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_){
_start:
{
lean_object* v___x_1250_; lean_object* v_env_1251_; uint8_t v___x_1252_; lean_object* v___x_1253_; 
v___x_1250_ = lean_st_ref_get(v___y_1248_);
v_env_1251_ = lean_ctor_get(v___x_1250_, 0);
lean_inc_ref(v_env_1251_);
lean_dec(v___x_1250_);
v___x_1252_ = 0;
lean_inc(v_constName_1244_);
v___x_1253_ = l_Lean_Environment_findConstVal_x3f(v_env_1251_, v_constName_1244_, v___x_1252_);
if (lean_obj_tag(v___x_1253_) == 0)
{
lean_object* v___x_1254_; 
v___x_1254_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0___redArg(v_constName_1244_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_);
return v___x_1254_;
}
else
{
lean_object* v_val_1255_; lean_object* v___x_1257_; uint8_t v_isShared_1258_; uint8_t v_isSharedCheck_1262_; 
lean_dec(v_constName_1244_);
v_val_1255_ = lean_ctor_get(v___x_1253_, 0);
v_isSharedCheck_1262_ = !lean_is_exclusive(v___x_1253_);
if (v_isSharedCheck_1262_ == 0)
{
v___x_1257_ = v___x_1253_;
v_isShared_1258_ = v_isSharedCheck_1262_;
goto v_resetjp_1256_;
}
else
{
lean_inc(v_val_1255_);
lean_dec(v___x_1253_);
v___x_1257_ = lean_box(0);
v_isShared_1258_ = v_isSharedCheck_1262_;
goto v_resetjp_1256_;
}
v_resetjp_1256_:
{
lean_object* v___x_1260_; 
if (v_isShared_1258_ == 0)
{
lean_ctor_set_tag(v___x_1257_, 0);
v___x_1260_ = v___x_1257_;
goto v_reusejp_1259_;
}
else
{
lean_object* v_reuseFailAlloc_1261_; 
v_reuseFailAlloc_1261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1261_, 0, v_val_1255_);
v___x_1260_ = v_reuseFailAlloc_1261_;
goto v_reusejp_1259_;
}
v_reusejp_1259_:
{
return v___x_1260_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0___boxed(lean_object* v_constName_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_){
_start:
{
lean_object* v_res_1269_; 
v_res_1269_ = l_Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0(v_constName_1263_, v___y_1264_, v___y_1265_, v___y_1266_, v___y_1267_);
lean_dec(v___y_1267_);
lean_dec_ref(v___y_1266_);
lean_dec(v___y_1265_);
lean_dec_ref(v___y_1264_);
return v_res_1269_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__1(lean_object* v_a_1270_, lean_object* v_a_1271_){
_start:
{
if (lean_obj_tag(v_a_1270_) == 0)
{
lean_object* v___x_1272_; 
v___x_1272_ = l_List_reverse___redArg(v_a_1271_);
return v___x_1272_;
}
else
{
lean_object* v_head_1273_; lean_object* v_tail_1274_; lean_object* v___x_1276_; uint8_t v_isShared_1277_; uint8_t v_isSharedCheck_1283_; 
v_head_1273_ = lean_ctor_get(v_a_1270_, 0);
v_tail_1274_ = lean_ctor_get(v_a_1270_, 1);
v_isSharedCheck_1283_ = !lean_is_exclusive(v_a_1270_);
if (v_isSharedCheck_1283_ == 0)
{
v___x_1276_ = v_a_1270_;
v_isShared_1277_ = v_isSharedCheck_1283_;
goto v_resetjp_1275_;
}
else
{
lean_inc(v_tail_1274_);
lean_inc(v_head_1273_);
lean_dec(v_a_1270_);
v___x_1276_ = lean_box(0);
v_isShared_1277_ = v_isSharedCheck_1283_;
goto v_resetjp_1275_;
}
v_resetjp_1275_:
{
lean_object* v___x_1278_; lean_object* v___x_1280_; 
v___x_1278_ = l_Lean_mkLevelParam(v_head_1273_);
if (v_isShared_1277_ == 0)
{
lean_ctor_set(v___x_1276_, 1, v_a_1271_);
lean_ctor_set(v___x_1276_, 0, v___x_1278_);
v___x_1280_ = v___x_1276_;
goto v_reusejp_1279_;
}
else
{
lean_object* v_reuseFailAlloc_1282_; 
v_reuseFailAlloc_1282_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1282_, 0, v___x_1278_);
lean_ctor_set(v_reuseFailAlloc_1282_, 1, v_a_1271_);
v___x_1280_ = v_reuseFailAlloc_1282_;
goto v_reusejp_1279_;
}
v_reusejp_1279_:
{
v_a_1270_ = v_tail_1274_;
v_a_1271_ = v___x_1280_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___closed__1(void){
_start:
{
lean_object* v___x_1285_; lean_object* v___x_1286_; 
v___x_1285_ = ((lean_object*)(l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___closed__0));
v___x_1286_ = l_Lean_stringToMessageData(v___x_1285_);
return v___x_1286_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___closed__3(void){
_start:
{
lean_object* v___x_1288_; lean_object* v___x_1289_; 
v___x_1288_ = ((lean_object*)(l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___closed__2));
v___x_1289_ = l_Lean_stringToMessageData(v___x_1288_);
return v___x_1289_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize(lean_object* v_sparseCasesOnName_1290_, lean_object* v_thmName_1291_, lean_object* v_a_1292_, lean_object* v_a_1293_, lean_object* v_a_1294_, lean_object* v_a_1295_){
_start:
{
lean_object* v___x_1297_; 
lean_inc(v_sparseCasesOnName_1290_);
v___x_1297_ = l_Lean_Meta_getSparseCasesOnInfo___redArg(v_sparseCasesOnName_1290_, v_a_1295_);
if (lean_obj_tag(v___x_1297_) == 0)
{
lean_object* v_a_1298_; 
v_a_1298_ = lean_ctor_get(v___x_1297_, 0);
lean_inc(v_a_1298_);
lean_dec_ref_known(v___x_1297_, 1);
if (lean_obj_tag(v_a_1298_) == 1)
{
lean_object* v_val_1299_; lean_object* v___x_1300_; 
v_val_1299_ = lean_ctor_get(v_a_1298_, 0);
lean_inc(v_val_1299_);
lean_dec_ref_known(v_a_1298_, 1);
lean_inc(v_sparseCasesOnName_1290_);
v___x_1300_ = l_Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0(v_sparseCasesOnName_1290_, v_a_1292_, v_a_1293_, v_a_1294_, v_a_1295_);
if (lean_obj_tag(v___x_1300_) == 0)
{
lean_object* v_a_1301_; lean_object* v_levelParams_1302_; lean_object* v_type_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___f_1307_; uint8_t v___x_1308_; lean_object* v___x_1309_; 
v_a_1301_ = lean_ctor_get(v___x_1300_, 0);
lean_inc(v_a_1301_);
lean_dec_ref_known(v___x_1300_, 1);
v_levelParams_1302_ = lean_ctor_get(v_a_1301_, 1);
lean_inc_n(v_levelParams_1302_, 2);
v_type_1303_ = lean_ctor_get(v_a_1301_, 2);
lean_inc_ref(v_type_1303_);
lean_dec(v_a_1301_);
v___x_1304_ = l_Lean_instInhabitedExpr;
v___x_1305_ = lean_box(0);
v___x_1306_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__1(v_levelParams_1302_, v___x_1305_);
v___f_1307_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___lam__2___boxed), 14, 7);
lean_closure_set(v___f_1307_, 0, v___x_1304_);
lean_closure_set(v___f_1307_, 1, v_sparseCasesOnName_1290_);
lean_closure_set(v___f_1307_, 2, v___x_1306_);
lean_closure_set(v___f_1307_, 3, v___x_1305_);
lean_closure_set(v___f_1307_, 4, v_val_1299_);
lean_closure_set(v___f_1307_, 5, v_thmName_1291_);
lean_closure_set(v___f_1307_, 6, v_levelParams_1302_);
v___x_1308_ = 0;
v___x_1309_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__9___redArg(v_type_1303_, v___f_1307_, v___x_1308_, v_a_1292_, v_a_1293_, v_a_1294_, v_a_1295_);
return v___x_1309_;
}
else
{
lean_object* v_a_1310_; lean_object* v___x_1312_; uint8_t v_isShared_1313_; uint8_t v_isSharedCheck_1317_; 
lean_dec(v_val_1299_);
lean_dec(v_thmName_1291_);
lean_dec(v_sparseCasesOnName_1290_);
v_a_1310_ = lean_ctor_get(v___x_1300_, 0);
v_isSharedCheck_1317_ = !lean_is_exclusive(v___x_1300_);
if (v_isSharedCheck_1317_ == 0)
{
v___x_1312_ = v___x_1300_;
v_isShared_1313_ = v_isSharedCheck_1317_;
goto v_resetjp_1311_;
}
else
{
lean_inc(v_a_1310_);
lean_dec(v___x_1300_);
v___x_1312_ = lean_box(0);
v_isShared_1313_ = v_isSharedCheck_1317_;
goto v_resetjp_1311_;
}
v_resetjp_1311_:
{
lean_object* v___x_1315_; 
if (v_isShared_1313_ == 0)
{
v___x_1315_ = v___x_1312_;
goto v_reusejp_1314_;
}
else
{
lean_object* v_reuseFailAlloc_1316_; 
v_reuseFailAlloc_1316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1316_, 0, v_a_1310_);
v___x_1315_ = v_reuseFailAlloc_1316_;
goto v_reusejp_1314_;
}
v_reusejp_1314_:
{
return v___x_1315_;
}
}
}
}
else
{
lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; 
lean_dec(v_a_1298_);
lean_dec(v_thmName_1291_);
v___x_1318_ = lean_obj_once(&l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___closed__1, &l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___closed__1_once, _init_l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___closed__1);
v___x_1319_ = l_Lean_MessageData_ofName(v_sparseCasesOnName_1290_);
v___x_1320_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1320_, 0, v___x_1318_);
lean_ctor_set(v___x_1320_, 1, v___x_1319_);
v___x_1321_ = lean_obj_once(&l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___closed__3, &l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___closed__3_once, _init_l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___closed__3);
v___x_1322_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1322_, 0, v___x_1320_);
lean_ctor_set(v___x_1322_, 1, v___x_1321_);
v___x_1323_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__3___redArg(v___x_1322_, v_a_1292_, v_a_1293_, v_a_1294_, v_a_1295_);
return v___x_1323_;
}
}
else
{
lean_object* v_a_1324_; lean_object* v___x_1326_; uint8_t v_isShared_1327_; uint8_t v_isSharedCheck_1331_; 
lean_dec(v_thmName_1291_);
lean_dec(v_sparseCasesOnName_1290_);
v_a_1324_ = lean_ctor_get(v___x_1297_, 0);
v_isSharedCheck_1331_ = !lean_is_exclusive(v___x_1297_);
if (v_isSharedCheck_1331_ == 0)
{
v___x_1326_ = v___x_1297_;
v_isShared_1327_ = v_isSharedCheck_1331_;
goto v_resetjp_1325_;
}
else
{
lean_inc(v_a_1324_);
lean_dec(v___x_1297_);
v___x_1326_ = lean_box(0);
v_isShared_1327_ = v_isSharedCheck_1331_;
goto v_resetjp_1325_;
}
v_resetjp_1325_:
{
lean_object* v___x_1329_; 
if (v_isShared_1327_ == 0)
{
v___x_1329_ = v___x_1326_;
goto v_reusejp_1328_;
}
else
{
lean_object* v_reuseFailAlloc_1330_; 
v_reuseFailAlloc_1330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1330_, 0, v_a_1324_);
v___x_1329_ = v_reuseFailAlloc_1330_;
goto v_reusejp_1328_;
}
v_reusejp_1328_:
{
return v___x_1329_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___boxed(lean_object* v_sparseCasesOnName_1332_, lean_object* v_thmName_1333_, lean_object* v_a_1334_, lean_object* v_a_1335_, lean_object* v_a_1336_, lean_object* v_a_1337_, lean_object* v_a_1338_){
_start:
{
lean_object* v_res_1339_; 
v_res_1339_ = l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize(v_sparseCasesOnName_1332_, v_thmName_1333_, v_a_1334_, v_a_1335_, v_a_1336_, v_a_1337_);
lean_dec(v_a_1337_);
lean_dec_ref(v_a_1336_);
lean_dec(v_a_1335_);
lean_dec_ref(v_a_1334_);
return v_res_1339_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__3(lean_object* v_00_u03b1_1340_, lean_object* v_msg_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_){
_start:
{
lean_object* v___x_1347_; 
v___x_1347_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__3___redArg(v_msg_1341_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_);
return v___x_1347_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__3___boxed(lean_object* v_00_u03b1_1348_, lean_object* v_msg_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_){
_start:
{
lean_object* v_res_1355_; 
v_res_1355_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__3(v_00_u03b1_1348_, v_msg_1349_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_);
lean_dec(v___y_1353_);
lean_dec_ref(v___y_1352_);
lean_dec(v___y_1351_);
lean_dec_ref(v___y_1350_);
return v_res_1355_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4(lean_object* v_mvarId_1356_, lean_object* v_val_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_){
_start:
{
lean_object* v___x_1363_; 
v___x_1363_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4___redArg(v_mvarId_1356_, v_val_1357_, v___y_1359_);
return v___x_1363_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4___boxed(lean_object* v_mvarId_1364_, lean_object* v_val_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_){
_start:
{
lean_object* v_res_1371_; 
v_res_1371_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4(v_mvarId_1364_, v_val_1365_, v___y_1366_, v___y_1367_, v___y_1368_, v___y_1369_);
lean_dec(v___y_1369_);
lean_dec_ref(v___y_1368_);
lean_dec(v___y_1367_);
lean_dec_ref(v___y_1366_);
return v_res_1371_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0(lean_object* v_00_u03b1_1372_, lean_object* v_constName_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_){
_start:
{
lean_object* v___x_1379_; 
v___x_1379_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0___redArg(v_constName_1373_, v___y_1374_, v___y_1375_, v___y_1376_, v___y_1377_);
return v___x_1379_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1380_, lean_object* v_constName_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_){
_start:
{
lean_object* v_res_1387_; 
v_res_1387_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0(v_00_u03b1_1380_, v_constName_1381_, v___y_1382_, v___y_1383_, v___y_1384_, v___y_1385_);
lean_dec(v___y_1385_);
lean_dec_ref(v___y_1384_);
lean_dec(v___y_1383_);
lean_dec_ref(v___y_1382_);
return v_res_1387_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6(lean_object* v_00_u03b2_1388_, lean_object* v_x_1389_, lean_object* v_x_1390_, lean_object* v_x_1391_){
_start:
{
lean_object* v___x_1392_; 
v___x_1392_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6___redArg(v_x_1389_, v_x_1390_, v_x_1391_);
return v___x_1392_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6(lean_object* v_00_u03b1_1393_, lean_object* v_ref_1394_, lean_object* v_constName_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_){
_start:
{
lean_object* v___x_1401_; 
v___x_1401_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6___redArg(v_ref_1394_, v_constName_1395_, v___y_1396_, v___y_1397_, v___y_1398_, v___y_1399_);
return v___x_1401_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6___boxed(lean_object* v_00_u03b1_1402_, lean_object* v_ref_1403_, lean_object* v_constName_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_){
_start:
{
lean_object* v_res_1410_; 
v_res_1410_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6(v_00_u03b1_1402_, v_ref_1403_, v_constName_1404_, v___y_1405_, v___y_1406_, v___y_1407_, v___y_1408_);
lean_dec(v___y_1408_);
lean_dec_ref(v___y_1407_);
lean_dec(v___y_1406_);
lean_dec_ref(v___y_1405_);
lean_dec(v_ref_1403_);
return v_res_1410_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6_spec__12(lean_object* v_00_u03b2_1411_, lean_object* v_x_1412_, size_t v_x_1413_, size_t v_x_1414_, lean_object* v_x_1415_, lean_object* v_x_1416_){
_start:
{
lean_object* v___x_1417_; 
v___x_1417_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6_spec__12___redArg(v_x_1412_, v_x_1413_, v_x_1414_, v_x_1415_, v_x_1416_);
return v___x_1417_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6_spec__12___boxed(lean_object* v_00_u03b2_1418_, lean_object* v_x_1419_, lean_object* v_x_1420_, lean_object* v_x_1421_, lean_object* v_x_1422_, lean_object* v_x_1423_){
_start:
{
size_t v_x_20828__boxed_1424_; size_t v_x_20829__boxed_1425_; lean_object* v_res_1426_; 
v_x_20828__boxed_1424_ = lean_unbox_usize(v_x_1420_);
lean_dec(v_x_1420_);
v_x_20829__boxed_1425_ = lean_unbox_usize(v_x_1421_);
lean_dec(v_x_1421_);
v_res_1426_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6_spec__12(v_00_u03b2_1418_, v_x_1419_, v_x_20828__boxed_1424_, v_x_20829__boxed_1425_, v_x_1422_, v_x_1423_);
return v_res_1426_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12(lean_object* v_00_u03b1_1427_, lean_object* v_ref_1428_, lean_object* v_msg_1429_, lean_object* v_declHint_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_){
_start:
{
lean_object* v___x_1436_; 
v___x_1436_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12___redArg(v_ref_1428_, v_msg_1429_, v_declHint_1430_, v___y_1431_, v___y_1432_, v___y_1433_, v___y_1434_);
return v___x_1436_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12___boxed(lean_object* v_00_u03b1_1437_, lean_object* v_ref_1438_, lean_object* v_msg_1439_, lean_object* v_declHint_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_){
_start:
{
lean_object* v_res_1446_; 
v_res_1446_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12(v_00_u03b1_1437_, v_ref_1438_, v_msg_1439_, v_declHint_1440_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_);
lean_dec(v___y_1444_);
lean_dec_ref(v___y_1443_);
lean_dec(v___y_1442_);
lean_dec_ref(v___y_1441_);
lean_dec(v_ref_1438_);
return v_res_1446_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6_spec__12_spec__15(lean_object* v_00_u03b2_1447_, lean_object* v_n_1448_, lean_object* v_k_1449_, lean_object* v_v_1450_){
_start:
{
lean_object* v___x_1451_; 
v___x_1451_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6_spec__12_spec__15___redArg(v_n_1448_, v_k_1449_, v_v_1450_);
return v___x_1451_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6_spec__12_spec__16(lean_object* v_00_u03b2_1452_, size_t v_depth_1453_, lean_object* v_keys_1454_, lean_object* v_vals_1455_, lean_object* v_heq_1456_, lean_object* v_i_1457_, lean_object* v_entries_1458_){
_start:
{
lean_object* v___x_1459_; 
v___x_1459_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6_spec__12_spec__16___redArg(v_depth_1453_, v_keys_1454_, v_vals_1455_, v_i_1457_, v_entries_1458_);
return v___x_1459_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6_spec__12_spec__16___boxed(lean_object* v_00_u03b2_1460_, lean_object* v_depth_1461_, lean_object* v_keys_1462_, lean_object* v_vals_1463_, lean_object* v_heq_1464_, lean_object* v_i_1465_, lean_object* v_entries_1466_){
_start:
{
size_t v_depth_boxed_1467_; lean_object* v_res_1468_; 
v_depth_boxed_1467_ = lean_unbox_usize(v_depth_1461_);
lean_dec(v_depth_1461_);
v_res_1468_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6_spec__12_spec__16(v_00_u03b2_1460_, v_depth_boxed_1467_, v_keys_1462_, v_vals_1463_, v_heq_1464_, v_i_1465_, v_entries_1466_);
lean_dec_ref(v_vals_1463_);
lean_dec_ref(v_keys_1462_);
return v_res_1468_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16(lean_object* v_msg_1469_, lean_object* v_declHint_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_){
_start:
{
lean_object* v___x_1476_; 
v___x_1476_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg(v_msg_1469_, v_declHint_1470_, v___y_1474_);
return v___x_1476_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___boxed(lean_object* v_msg_1477_, lean_object* v_declHint_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_){
_start:
{
lean_object* v_res_1484_; 
v_res_1484_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16(v_msg_1477_, v_declHint_1478_, v___y_1479_, v___y_1480_, v___y_1481_, v___y_1482_);
lean_dec(v___y_1482_);
lean_dec_ref(v___y_1481_);
lean_dec(v___y_1480_);
lean_dec_ref(v___y_1479_);
return v_res_1484_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__15(lean_object* v_00_u03b1_1485_, lean_object* v_ref_1486_, lean_object* v_msg_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_){
_start:
{
lean_object* v___x_1493_; 
v___x_1493_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__15___redArg(v_ref_1486_, v_msg_1487_, v___y_1488_, v___y_1489_, v___y_1490_, v___y_1491_);
return v___x_1493_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__15___boxed(lean_object* v_00_u03b1_1494_, lean_object* v_ref_1495_, lean_object* v_msg_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_){
_start:
{
lean_object* v_res_1502_; 
v_res_1502_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__15(v_00_u03b1_1494_, v_ref_1495_, v_msg_1496_, v___y_1497_, v___y_1498_, v___y_1499_, v___y_1500_);
lean_dec(v___y_1500_);
lean_dec_ref(v___y_1499_);
lean_dec(v___y_1498_);
lean_dec_ref(v___y_1497_);
lean_dec(v_ref_1495_);
return v_res_1502_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6_spec__12_spec__15_spec__18(lean_object* v_00_u03b2_1503_, lean_object* v_x_1504_, lean_object* v_x_1505_, lean_object* v_x_1506_, lean_object* v_x_1507_){
_start:
{
lean_object* v___x_1508_; 
v___x_1508_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__4_spec__6_spec__12_spec__15_spec__18___redArg(v_x_1504_, v_x_1505_, v_x_1506_, v_x_1507_);
return v___x_1508_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getSparseCasesOnEq(lean_object* v_sparseCasesOnName_1510_, lean_object* v_a_1511_, lean_object* v_a_1512_, lean_object* v_a_1513_, lean_object* v_a_1514_){
_start:
{
lean_object* v___x_1516_; lean_object* v_thmName_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; 
v___x_1516_ = ((lean_object*)(l_Lean_Meta_getSparseCasesOnEq___closed__0));
lean_inc_n(v_sparseCasesOnName_1510_, 2);
v_thmName_1517_ = l_Lean_Name_str___override(v_sparseCasesOnName_1510_, v___x_1516_);
lean_inc_n(v_thmName_1517_, 2);
v___x_1518_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize___boxed), 7, 2);
lean_closure_set(v___x_1518_, 0, v_sparseCasesOnName_1510_);
lean_closure_set(v___x_1518_, 1, v_thmName_1517_);
v___x_1519_ = l_Lean_Meta_realizeConst(v_sparseCasesOnName_1510_, v_thmName_1517_, v___x_1518_, v_a_1511_, v_a_1512_, v_a_1513_, v_a_1514_);
if (lean_obj_tag(v___x_1519_) == 0)
{
lean_object* v___x_1521_; uint8_t v_isShared_1522_; uint8_t v_isSharedCheck_1526_; 
v_isSharedCheck_1526_ = !lean_is_exclusive(v___x_1519_);
if (v_isSharedCheck_1526_ == 0)
{
lean_object* v_unused_1527_; 
v_unused_1527_ = lean_ctor_get(v___x_1519_, 0);
lean_dec(v_unused_1527_);
v___x_1521_ = v___x_1519_;
v_isShared_1522_ = v_isSharedCheck_1526_;
goto v_resetjp_1520_;
}
else
{
lean_dec(v___x_1519_);
v___x_1521_ = lean_box(0);
v_isShared_1522_ = v_isSharedCheck_1526_;
goto v_resetjp_1520_;
}
v_resetjp_1520_:
{
lean_object* v___x_1524_; 
if (v_isShared_1522_ == 0)
{
lean_ctor_set(v___x_1521_, 0, v_thmName_1517_);
v___x_1524_ = v___x_1521_;
goto v_reusejp_1523_;
}
else
{
lean_object* v_reuseFailAlloc_1525_; 
v_reuseFailAlloc_1525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1525_, 0, v_thmName_1517_);
v___x_1524_ = v_reuseFailAlloc_1525_;
goto v_reusejp_1523_;
}
v_reusejp_1523_:
{
return v___x_1524_;
}
}
}
else
{
lean_object* v_a_1528_; lean_object* v___x_1530_; uint8_t v_isShared_1531_; uint8_t v_isSharedCheck_1535_; 
lean_dec(v_thmName_1517_);
v_a_1528_ = lean_ctor_get(v___x_1519_, 0);
v_isSharedCheck_1535_ = !lean_is_exclusive(v___x_1519_);
if (v_isSharedCheck_1535_ == 0)
{
v___x_1530_ = v___x_1519_;
v_isShared_1531_ = v_isSharedCheck_1535_;
goto v_resetjp_1529_;
}
else
{
lean_inc(v_a_1528_);
lean_dec(v___x_1519_);
v___x_1530_ = lean_box(0);
v_isShared_1531_ = v_isSharedCheck_1535_;
goto v_resetjp_1529_;
}
v_resetjp_1529_:
{
lean_object* v___x_1533_; 
if (v_isShared_1531_ == 0)
{
v___x_1533_ = v___x_1530_;
goto v_reusejp_1532_;
}
else
{
lean_object* v_reuseFailAlloc_1534_; 
v_reuseFailAlloc_1534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1534_, 0, v_a_1528_);
v___x_1533_ = v_reuseFailAlloc_1534_;
goto v_reusejp_1532_;
}
v_reusejp_1532_:
{
return v___x_1533_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getSparseCasesOnEq___boxed(lean_object* v_sparseCasesOnName_1536_, lean_object* v_a_1537_, lean_object* v_a_1538_, lean_object* v_a_1539_, lean_object* v_a_1540_, lean_object* v_a_1541_){
_start:
{
lean_object* v_res_1542_; 
v_res_1542_ = l_Lean_Meta_getSparseCasesOnEq(v_sparseCasesOnName_1536_, v_a_1537_, v_a_1538_, v_a_1539_, v_a_1540_);
lean_dec(v_a_1540_);
lean_dec_ref(v_a_1539_);
lean_dec(v_a_1538_);
lean_dec_ref(v_a_1537_);
return v_res_1542_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_isName(lean_object* v_env_1543_, lean_object* v_n_1544_){
_start:
{
if (lean_obj_tag(v_n_1544_) == 1)
{
lean_object* v_pre_1545_; lean_object* v_str_1546_; lean_object* v___x_1547_; uint8_t v___x_1548_; 
v_pre_1545_ = lean_ctor_get(v_n_1544_, 0);
lean_inc(v_pre_1545_);
v_str_1546_ = lean_ctor_get(v_n_1544_, 1);
lean_inc_ref(v_str_1546_);
lean_dec_ref_known(v_n_1544_, 2);
v___x_1547_ = ((lean_object*)(l_Lean_Meta_getSparseCasesOnEq___closed__0));
v___x_1548_ = lean_string_dec_eq(v_str_1546_, v___x_1547_);
lean_dec_ref(v_str_1546_);
if (v___x_1548_ == 0)
{
lean_dec(v_pre_1545_);
lean_dec_ref(v_env_1543_);
return v___x_1548_;
}
else
{
lean_object* v___x_1549_; 
v___x_1549_ = l_Lean_Meta_getSparseCasesOnInfoCore(v_env_1543_, v_pre_1545_);
if (lean_obj_tag(v___x_1549_) == 0)
{
uint8_t v___x_1550_; 
v___x_1550_ = 0;
return v___x_1550_;
}
else
{
lean_dec_ref_known(v___x_1549_, 1);
return v___x_1548_;
}
}
}
else
{
uint8_t v___x_1551_; 
lean_dec(v_n_1544_);
lean_dec_ref(v_env_1543_);
v___x_1551_ = 0;
return v___x_1551_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_isName___boxed(lean_object* v_env_1552_, lean_object* v_n_1553_){
_start:
{
uint8_t v_res_1554_; lean_object* v_r_1555_; 
v_res_1554_ = l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_isName(v_env_1552_, v_n_1553_);
v_r_1555_ = lean_box(v_res_1554_);
return v_r_1555_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_3147303576____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1558_; lean_object* v___x_1559_; 
v___x_1558_ = ((lean_object*)(l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_3147303576____hygCtx___hyg_2_));
v___x_1559_ = l_Lean_registerReservedNamePredicate(v___x_1558_);
return v___x_1559_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_3147303576____hygCtx___hyg_2____boxed(lean_object* v_a_1560_){
_start:
{
lean_object* v_res_1561_; 
v_res_1561_ = l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_3147303576____hygCtx___hyg_2_();
return v_res_1561_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2__spec__0(lean_object* v_msg_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_){
_start:
{
lean_object* v___f_1567_; lean_object* v___x_1144__overap_1568_; lean_object* v___x_1569_; 
v___f_1567_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2__spec__0___closed__0));
v___x_1144__overap_1568_ = lean_panic_fn_borrowed(v___f_1567_, v_msg_1563_);
lean_inc(v___y_1565_);
lean_inc_ref(v___y_1564_);
v___x_1569_ = lean_apply_3(v___x_1144__overap_1568_, v___y_1564_, v___y_1565_, lean_box(0));
return v___x_1569_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2__spec__0___boxed(lean_object* v_msg_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_){
_start:
{
lean_object* v_res_1574_; 
v_res_1574_ = l_panic___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2__spec__0(v_msg_1570_, v___y_1571_, v___y_1572_);
lean_dec(v___y_1572_);
lean_dec_ref(v___y_1571_);
return v_res_1574_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; 
v___x_1577_ = ((lean_object*)(l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_));
v___x_1578_ = lean_unsigned_to_nat(4u);
v___x_1579_ = lean_unsigned_to_nat(97u);
v___x_1580_ = ((lean_object*)(l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_));
v___x_1581_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__8___lam__1___closed__0));
v___x_1582_ = l_mkPanicMessageWithDecl(v___x_1581_, v___x_1580_, v___x_1579_, v___x_1578_, v___x_1577_);
return v___x_1582_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__3_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1583_; 
v___x_1583_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1583_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1584_; lean_object* v___x_1585_; 
v___x_1584_ = lean_obj_once(&l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__3_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__3_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__3_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_);
v___x_1585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1585_, 0, v___x_1584_);
return v___x_1585_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; 
v___x_1586_ = lean_box(1);
v___x_1587_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__4);
v___x_1588_ = lean_obj_once(&l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_);
v___x_1589_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1589_, 0, v___x_1588_);
lean_ctor_set(v___x_1589_, 1, v___x_1587_);
lean_ctor_set(v___x_1589_, 2, v___x_1586_);
return v___x_1589_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__7_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; 
v___x_1592_ = lean_obj_once(&l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_);
v___x_1593_ = lean_unsigned_to_nat(0u);
v___x_1594_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_1594_, 0, v___x_1593_);
lean_ctor_set(v___x_1594_, 1, v___x_1593_);
lean_ctor_set(v___x_1594_, 2, v___x_1593_);
lean_ctor_set(v___x_1594_, 3, v___x_1593_);
lean_ctor_set(v___x_1594_, 4, v___x_1592_);
lean_ctor_set(v___x_1594_, 5, v___x_1592_);
lean_ctor_set(v___x_1594_, 6, v___x_1592_);
lean_ctor_set(v___x_1594_, 7, v___x_1592_);
lean_ctor_set(v___x_1594_, 8, v___x_1592_);
lean_ctor_set(v___x_1594_, 9, v___x_1592_);
lean_ctor_set(v___x_1594_, 10, v___x_1592_);
return v___x_1594_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__8_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1595_; lean_object* v___x_1596_; 
v___x_1595_ = lean_obj_once(&l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_);
v___x_1596_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1596_, 0, v___x_1595_);
lean_ctor_set(v___x_1596_, 1, v___x_1595_);
lean_ctor_set(v___x_1596_, 2, v___x_1595_);
lean_ctor_set(v___x_1596_, 3, v___x_1595_);
lean_ctor_set(v___x_1596_, 4, v___x_1595_);
lean_ctor_set(v___x_1596_, 5, v___x_1595_);
return v___x_1596_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__9_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1597_; lean_object* v___x_1598_; 
v___x_1597_ = lean_obj_once(&l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__4_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_);
v___x_1598_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1598_, 0, v___x_1597_);
lean_ctor_set(v___x_1598_, 1, v___x_1597_);
lean_ctor_set(v___x_1598_, 2, v___x_1597_);
lean_ctor_set(v___x_1598_, 3, v___x_1597_);
lean_ctor_set(v___x_1598_, 4, v___x_1597_);
return v___x_1598_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__10_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; 
v___x_1599_ = lean_obj_once(&l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__9_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__9_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__9_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_);
v___x_1600_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_getSparseCasesOnEq_realize_spec__0_spec__0_spec__6_spec__12_spec__14_spec__16___redArg___closed__4);
v___x_1601_ = lean_box(1);
v___x_1602_ = lean_obj_once(&l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__8_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__8_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__8_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_);
v___x_1603_ = lean_obj_once(&l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__7_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__7_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__7_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_);
v___x_1604_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1604_, 0, v___x_1603_);
lean_ctor_set(v___x_1604_, 1, v___x_1602_);
lean_ctor_set(v___x_1604_, 2, v___x_1601_);
lean_ctor_set(v___x_1604_, 3, v___x_1600_);
lean_ctor_set(v___x_1604_, 4, v___x_1599_);
return v___x_1604_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_(lean_object* v_name_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_){
_start:
{
lean_object* v___x_1609_; lean_object* v_env_1610_; uint8_t v___x_1611_; lean_object* v_a_1613_; 
v___x_1609_ = lean_st_ref_get(v___y_1607_);
v_env_1610_ = lean_ctor_get(v___x_1609_, 0);
lean_inc_ref(v_env_1610_);
lean_dec(v___x_1609_);
lean_inc(v_name_1605_);
v___x_1611_ = l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_isName(v_env_1610_, v_name_1605_);
if (v___x_1611_ == 0)
{
lean_object* v___x_1619_; lean_object* v___x_1620_; 
lean_dec(v_name_1605_);
v___x_1619_ = lean_box(v___x_1611_);
v___x_1620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1620_, 0, v___x_1619_);
return v___x_1620_;
}
else
{
uint8_t v___x_1621_; uint8_t v___x_1622_; uint8_t v___x_1623_; uint8_t v___x_1624_; lean_object* v___x_1625_; uint64_t v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; 
v___x_1621_ = 0;
v___x_1622_ = 1;
v___x_1623_ = 0;
v___x_1624_ = 2;
v___x_1625_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_1625_, 0, v___x_1621_);
lean_ctor_set_uint8(v___x_1625_, 1, v___x_1621_);
lean_ctor_set_uint8(v___x_1625_, 2, v___x_1621_);
lean_ctor_set_uint8(v___x_1625_, 3, v___x_1621_);
lean_ctor_set_uint8(v___x_1625_, 4, v___x_1621_);
lean_ctor_set_uint8(v___x_1625_, 5, v___x_1611_);
lean_ctor_set_uint8(v___x_1625_, 6, v___x_1611_);
lean_ctor_set_uint8(v___x_1625_, 7, v___x_1621_);
lean_ctor_set_uint8(v___x_1625_, 8, v___x_1611_);
lean_ctor_set_uint8(v___x_1625_, 9, v___x_1622_);
lean_ctor_set_uint8(v___x_1625_, 10, v___x_1623_);
lean_ctor_set_uint8(v___x_1625_, 11, v___x_1611_);
lean_ctor_set_uint8(v___x_1625_, 12, v___x_1611_);
lean_ctor_set_uint8(v___x_1625_, 13, v___x_1611_);
lean_ctor_set_uint8(v___x_1625_, 14, v___x_1624_);
lean_ctor_set_uint8(v___x_1625_, 15, v___x_1611_);
lean_ctor_set_uint8(v___x_1625_, 16, v___x_1611_);
lean_ctor_set_uint8(v___x_1625_, 17, v___x_1611_);
lean_ctor_set_uint8(v___x_1625_, 18, v___x_1611_);
lean_ctor_set_uint8(v___x_1625_, 19, v___x_1621_);
v___x_1626_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_1625_);
v___x_1627_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1627_, 0, v___x_1625_);
lean_ctor_set_uint64(v___x_1627_, sizeof(void*)*1, v___x_1626_);
v___x_1628_ = lean_box(1);
v___x_1629_ = lean_unsigned_to_nat(0u);
v___x_1630_ = lean_obj_once(&l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__5_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_);
v___x_1631_ = ((lean_object*)(l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__6_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_));
v___x_1632_ = lean_box(0);
v___x_1633_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1633_, 0, v___x_1627_);
lean_ctor_set(v___x_1633_, 1, v___x_1628_);
lean_ctor_set(v___x_1633_, 2, v___x_1630_);
lean_ctor_set(v___x_1633_, 3, v___x_1631_);
lean_ctor_set(v___x_1633_, 4, v___x_1632_);
lean_ctor_set(v___x_1633_, 5, v___x_1629_);
lean_ctor_set(v___x_1633_, 6, v___x_1632_);
lean_ctor_set_uint8(v___x_1633_, sizeof(void*)*7, v___x_1621_);
lean_ctor_set_uint8(v___x_1633_, sizeof(void*)*7 + 1, v___x_1621_);
lean_ctor_set_uint8(v___x_1633_, sizeof(void*)*7 + 2, v___x_1621_);
lean_ctor_set_uint8(v___x_1633_, sizeof(void*)*7 + 3, v___x_1611_);
v___x_1634_ = lean_obj_once(&l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__10_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__10_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__10_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_);
v___x_1635_ = lean_st_mk_ref(v___x_1634_);
v___x_1636_ = l_Lean_Name_getPrefix(v_name_1605_);
v___x_1637_ = l_Lean_Meta_getSparseCasesOnEq(v___x_1636_, v___x_1633_, v___x_1635_, v___y_1606_, v___y_1607_);
lean_dec_ref_known(v___x_1633_, 7);
if (lean_obj_tag(v___x_1637_) == 0)
{
lean_object* v_a_1638_; lean_object* v___x_1639_; 
v_a_1638_ = lean_ctor_get(v___x_1637_, 0);
lean_inc(v_a_1638_);
lean_dec_ref_known(v___x_1637_, 1);
v___x_1639_ = lean_st_ref_get(v___x_1635_);
lean_dec(v___x_1635_);
lean_dec(v___x_1639_);
v_a_1613_ = v_a_1638_;
goto v___jp_1612_;
}
else
{
lean_dec(v___x_1635_);
if (lean_obj_tag(v___x_1637_) == 0)
{
lean_object* v_a_1640_; 
v_a_1640_ = lean_ctor_get(v___x_1637_, 0);
lean_inc(v_a_1640_);
lean_dec_ref_known(v___x_1637_, 1);
v_a_1613_ = v_a_1640_;
goto v___jp_1612_;
}
else
{
lean_object* v_a_1641_; lean_object* v___x_1643_; uint8_t v_isShared_1644_; uint8_t v_isSharedCheck_1648_; 
lean_dec(v_name_1605_);
v_a_1641_ = lean_ctor_get(v___x_1637_, 0);
v_isSharedCheck_1648_ = !lean_is_exclusive(v___x_1637_);
if (v_isSharedCheck_1648_ == 0)
{
v___x_1643_ = v___x_1637_;
v_isShared_1644_ = v_isSharedCheck_1648_;
goto v_resetjp_1642_;
}
else
{
lean_inc(v_a_1641_);
lean_dec(v___x_1637_);
v___x_1643_ = lean_box(0);
v_isShared_1644_ = v_isSharedCheck_1648_;
goto v_resetjp_1642_;
}
v_resetjp_1642_:
{
lean_object* v___x_1646_; 
if (v_isShared_1644_ == 0)
{
v___x_1646_ = v___x_1643_;
goto v_reusejp_1645_;
}
else
{
lean_object* v_reuseFailAlloc_1647_; 
v_reuseFailAlloc_1647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1647_, 0, v_a_1641_);
v___x_1646_ = v_reuseFailAlloc_1647_;
goto v_reusejp_1645_;
}
v_reusejp_1645_:
{
return v___x_1646_;
}
}
}
}
}
v___jp_1612_:
{
uint8_t v___x_1614_; 
v___x_1614_ = lean_name_eq(v_name_1605_, v_a_1613_);
lean_dec(v_a_1613_);
lean_dec(v_name_1605_);
if (v___x_1614_ == 0)
{
lean_object* v___x_1615_; lean_object* v___x_1616_; 
v___x_1615_ = lean_obj_once(&l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_);
v___x_1616_ = l_panic___at___00__private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2__spec__0(v___x_1615_, v___y_1606_, v___y_1607_);
return v___x_1616_;
}
else
{
lean_object* v___x_1617_; lean_object* v___x_1618_; 
v___x_1617_ = lean_box(v___x_1611_);
v___x_1618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1618_, 0, v___x_1617_);
return v___x_1618_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2____boxed(lean_object* v_name_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_){
_start:
{
lean_object* v_res_1653_; 
v_res_1653_ = l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_(v_name_1649_, v___y_1650_, v___y_1651_);
lean_dec(v___y_1651_);
lean_dec_ref(v___y_1650_);
return v_res_1653_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_1656_; lean_object* v___x_1657_; 
v___f_1656_ = ((lean_object*)(l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_));
v___x_1657_ = l_Lean_registerReservedNameAction(v___f_1656_);
return v___x_1657_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2____boxed(lean_object* v_a_1658_){
_start:
{
lean_object* v_res_1659_; 
v_res_1659_ = l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_1213293720____hygCtx___hyg_2_();
return v_res_1659_;
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
res = l___private_Lean_Meta_Constructions_SparseCasesOnEq_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOnEq_3147303576____hygCtx___hyg_2_();
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
