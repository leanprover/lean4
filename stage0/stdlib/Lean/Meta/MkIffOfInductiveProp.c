// Lean compiler output
// Module: Lean.Meta.MkIffOfInductiveProp
// Imports: public import Lean.Meta.Basic import Lean.Elab.Tactic.Basic import Lean.Meta.Tactic.Apply import Lean.Meta.Tactic.Cases
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
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_drop___redArg(lean_object*, lean_object*);
lean_object* l_List_zipWith___at___00List_zip_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_Expr_replaceFVar(lean_object*, lean_object*, lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_FVarId_getType___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sortLevel_x21(lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_Expr_occurs(lean_object*, lean_object*);
uint8_t lean_level_eq(lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* l_List_getLast_x21___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_cases(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray0___redArg();
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalTactic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Meta_throwTacticEx___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_checkNotAssigned(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_List_get___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_apply(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
lean_object* l_Lean_LocalContext_getFVarIds(lean_object*);
lean_object* l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVar(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l_Lean_Environment_findConstVal_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_tryClear(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_revert(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_intro1Core(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_List_zipIdxTR___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_TermElabM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Environment_hasUnsafe(lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_Expr_replaceFVars(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_instantiateTypeLevelParams(lean_object*, lean_object*);
lean_object* l_List_unzipTR___redArg(lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isProp(lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_MVarId_intros(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* l_Lean_addDecl(lean_object*, uint8_t, lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT uint8_t l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3_spec__5_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3_spec__5___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3_spec__6___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__0 = (const lean_object*)&l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__0_value;
static const lean_string_object l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__1 = (const lean_object*)&l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__1_value;
static const lean_string_object l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__2 = (const lean_object*)&l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__2_value;
static const lean_string_object l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "refine"};
static const lean_object* l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__3 = (const lean_object*)&l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__3_value;
static const lean_ctor_object l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__4_value_aux_0),((lean_object*)&l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__4_value_aux_1),((lean_object*)&l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__4_value_aux_2),((lean_object*)&l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(49, 130, 130, 160, 131, 48, 178, 245)}};
static const lean_object* l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__4 = (const lean_object*)&l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__4_value;
static const lean_string_object l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__5 = (const lean_object*)&l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__5_value;
static const lean_string_object l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "anonymousCtor"};
static const lean_object* l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__6 = (const lean_object*)&l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__6_value;
static const lean_ctor_object l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__7_value_aux_0),((lean_object*)&l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__7_value_aux_1),((lean_object*)&l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__7_value_aux_2),((lean_object*)&l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(56, 53, 154, 97, 179, 232, 94, 186)}};
static const lean_object* l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__7 = (const lean_object*)&l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__7_value;
static const lean_string_object l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "⟨"};
static const lean_object* l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__8 = (const lean_object*)&l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__8_value;
static const lean_string_object l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__9 = (const lean_object*)&l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__9_value;
static const lean_ctor_object l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__9_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__10 = (const lean_object*)&l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__10_value;
static const lean_string_object l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "syntheticHole"};
static const lean_object* l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__11 = (const lean_object*)&l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__11_value;
static const lean_ctor_object l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__12_value_aux_0),((lean_object*)&l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__12_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__12_value_aux_1),((lean_object*)&l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__12_value_aux_2),((lean_object*)&l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__11_value),LEAN_SCALAR_PTR_LITERAL(218, 189, 67, 60, 211, 196, 112, 165)}};
static const lean_object* l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__12 = (const lean_object*)&l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__12_value;
static const lean_string_object l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\?"};
static const lean_object* l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__13 = (const lean_object*)&l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__13_value;
static const lean_string_object l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__14 = (const lean_object*)&l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__14_value;
static const lean_string_object l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__15 = (const lean_object*)&l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__15_value;
static const lean_string_object l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "⟩"};
static const lean_object* l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__16 = (const lean_object*)&l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__16_value;
LEAN_EXPORT lean_object* l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "expected two subgoals"};
static const lean_object* l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___closed__0 = (const lean_object*)&l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___closed__0_value;
static lean_once_cell_t l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___closed__1;
static const lean_closure_object l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___closed__2 = (const lean_object*)&l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___closed__2_value;
static const lean_closure_object l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___closed__3 = (const lean_object*)&l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___closed__3_value;
static const lean_array_object l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___closed__4 = (const lean_object*)&l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___closed__4_value;
static const lean_ctor_object l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*8 + 16, .m_other = 8, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___closed__2_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___closed__4_value),LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 1, 0, 0, 0, 0),LEAN_SCALAR_PTR_LITERAL(1, 0, 1, 0, 0, 0, 0, 0)}};
static const lean_object* l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___closed__5 = (const lean_object*)&l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___closed__5_value;
static const lean_ctor_object l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*7 + 0, .m_other = 7, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___closed__6 = (const lean_object*)&l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___closed__6_value;
LEAN_EXPORT lean_object* l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3_spec__6(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3_spec__5_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "target is not an inductive datatype"};
static const lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0___closed__0_value)}};
static const lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0___closed__2;
static lean_once_cell_t l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0___closed__3;
static const lean_string_object l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "index "};
static const lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0___closed__4 = (const lean_object*)&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0___closed__4_value;
static const lean_string_object l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = " out of bounds, only "};
static const lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0___closed__5 = (const lean_object*)&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0___closed__5_value;
static const lean_string_object l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = " constructors"};
static const lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0___closed__6 = (const lean_object*)&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0___closed__6_value;
static const lean_string_object l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 48, .m_capacity = 48, .m_length = 47, .m_data = " tactic works for inductive types with exactly "};
static const lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0___closed__7 = (const lean_object*)&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0___closed__7_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "expected only one new goal"};
static const lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__0 = (const lean_object*)&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__1;
static const lean_string_object l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "left"};
static const lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__2 = (const lean_object*)&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__2_value),LEAN_SCALAR_PTR_LITERAL(14, 26, 230, 200, 188, 33, 106, 9)}};
static const lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__3 = (const lean_object*)&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__4 = (const lean_object*)&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__4_value;
static const lean_string_object l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "right"};
static const lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__5 = (const lean_object*)&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__5_value;
static const lean_ctor_object l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__5_value),LEAN_SCALAR_PTR_LITERAL(192, 52, 10, 58, 87, 38, 120, 247)}};
static const lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__6 = (const lean_object*)&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__6_value;
static const lean_string_object l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "failed"};
static const lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__7 = (const lean_object*)&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__7_value;
static lean_once_cell_t l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__8;
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_compactRelation___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_compactRelation___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_compactRelation___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_compactRelation___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_span_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_compactRelation_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_span_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_compactRelation_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_compactRelation_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_compactRelation_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_compactRelation_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_compactRelation_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_compactRelation___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_compactRelation___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_compactRelation___closed__0 = (const lean_object*)&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_compactRelation___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_compactRelation(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_updateLambdaBinderInfoD_x21_spec__0(lean_object*);
static const lean_string_object l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_updateLambdaBinderInfoD_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "Lean.Meta.MkIffOfInductiveProp"};
static const lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_updateLambdaBinderInfoD_x21___closed__0 = (const lean_object*)&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_updateLambdaBinderInfoD_x21___closed__0_value;
static const lean_string_object l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_updateLambdaBinderInfoD_x21___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 77, .m_capacity = 77, .m_length = 76, .m_data = "_private.Lean.Meta.MkIffOfInductiveProp.0.Lean.Meta.updateLambdaBinderInfoD!"};
static const lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_updateLambdaBinderInfoD_x21___closed__1 = (const lean_object*)&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_updateLambdaBinderInfoD_x21___closed__1_value;
static const lean_string_object l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_updateLambdaBinderInfoD_x21___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "lambda expected"};
static const lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_updateLambdaBinderInfoD_x21___closed__2 = (const lean_object*)&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_updateLambdaBinderInfoD_x21___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_updateLambdaBinderInfoD_x21___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_updateLambdaBinderInfoD_x21___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_updateLambdaBinderInfoD_x21(lean_object*);
static const lean_string_object l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkExistsList_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Exists"};
static const lean_object* l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkExistsList_spec__0___closed__0 = (const lean_object*)&l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkExistsList_spec__0___closed__0_value;
static const lean_ctor_object l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkExistsList_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkExistsList_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(65, 29, 48, 135, 199, 176, 149, 70)}};
static const lean_object* l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkExistsList_spec__0___closed__1 = (const lean_object*)&l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkExistsList_spec__0___closed__1_value;
static const lean_string_object l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkExistsList_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "And"};
static const lean_object* l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkExistsList_spec__0___closed__2 = (const lean_object*)&l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkExistsList_spec__0___closed__2_value;
static const lean_ctor_object l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkExistsList_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkExistsList_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(49, 220, 212, 156, 122, 214, 55, 135)}};
static const lean_object* l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkExistsList_spec__0___closed__3 = (const lean_object*)&l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkExistsList_spec__0___closed__3_value;
static lean_once_cell_t l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkExistsList_spec__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkExistsList_spec__0___closed__4;
LEAN_EXPORT lean_object* l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkExistsList_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkExistsList_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkExistsList(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkExistsList___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkOpList(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkOpList___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkAndList___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "True"};
static const lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkAndList___closed__0 = (const lean_object*)&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkAndList___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkAndList___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkAndList___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 21, 103, 131, 118, 13, 187, 164)}};
static const lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkAndList___closed__1 = (const lean_object*)&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkAndList___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkAndList___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkAndList___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkAndList(lean_object*);
static const lean_string_object l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkOrList___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Or"};
static const lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkOrList___closed__0 = (const lean_object*)&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkOrList___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkOrList___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkOrList___closed__0_value),LEAN_SCALAR_PTR_LITERAL(34, 237, 162, 225, 217, 98, 205, 196)}};
static const lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkOrList___closed__1 = (const lean_object*)&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkOrList___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkOrList___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkOrList___closed__2;
static const lean_string_object l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkOrList___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "False"};
static const lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkOrList___closed__3 = (const lean_object*)&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkOrList___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkOrList___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkOrList___closed__3_value),LEAN_SCALAR_PTR_LITERAL(227, 122, 176, 177, 50, 175, 152, 12)}};
static const lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkOrList___closed__4 = (const lean_object*)&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkOrList___closed__4_value;
static lean_once_cell_t l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkOrList___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkOrList___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkOrList(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_List_init___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_List_init(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__4___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__4___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__4___redArg(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__5___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__5(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "HEq"};
static const lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__2___closed__0 = (const lean_object*)&l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__2___closed__0_value;
static const lean_ctor_object l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(67, 180, 169, 191, 74, 196, 152, 188)}};
static const lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__2___closed__1 = (const lean_object*)&l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__2___closed__1_value;
static const lean_string_object l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__2___closed__2 = (const lean_object*)&l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__2___closed__2_value;
static const lean_ctor_object l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__2___closed__2_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__2___closed__3 = (const lean_object*)&l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__2___closed__3_value;
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__1(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__1___closed__0;
static const lean_array_object l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__1___closed__1 = (const lean_object*)&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__1___closed__2 = (const lean_object*)&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__1___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__1___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__0;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__1;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__2;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__3;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__4;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__13;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__14 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__14_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__15;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__19;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3___redArg___closed__1;
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3___redArg___closed__2 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "constructorBang"};
static const lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__1___closed__1_value_aux_0),((lean_object*)&l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__1___closed__1_value_aux_1),((lean_object*)&l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(117, 242, 106, 139, 253, 153, 73, 212)}};
static const lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__1___closed__1 = (const lean_object*)&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__1___closed__1_value;
static const lean_string_object l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "constructor!"};
static const lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__1___closed__2 = (const lean_object*)&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__1___closed__2_value;
static const lean_string_object l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "optConfig"};
static const lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__1___closed__3 = (const lean_object*)&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__1___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__1___closed__4_value_aux_0),((lean_object*)&l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__1___closed__4_value_aux_1),((lean_object*)&l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__1___closed__4_value_aux_2),((lean_object*)&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(137, 208, 10, 74, 108, 50, 106, 48)}};
static const lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__1___closed__4 = (const lean_object*)&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__1___closed__4_value;
static lean_once_cell_t l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__1___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__2(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__3(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___closed__0 = (const lean_object*)&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___closed__0_value;
static const lean_string_object l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "expected no subgoals"};
static const lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___closed__1 = (const lean_object*)&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toCases_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toCases_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toCases_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toCases___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toCases___closed__0 = (const lean_object*)&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toCases___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toCases(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toCases___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesSum___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "expected fvar"};
static const lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesSum___closed__0 = (const lean_object*)&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesSum___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesSum___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesSum___closed__1;
static const lean_string_object l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesSum___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "expected two case subgoals"};
static const lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesSum___closed__2 = (const lean_object*)&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesSum___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesSum___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesSum___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesSum(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesSum___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesProd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "expected one case subgoals"};
static const lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesProd___closed__0 = (const lean_object*)&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesProd___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesProd___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesProd___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesProd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesProd___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_listBoolMerge___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_listBoolMerge(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__2_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__0(lean_object*, lean_object*);
static const lean_array_object l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__5___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__5___lam__0___closed__0 = (const lean_object*)&l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__5___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__5___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__5___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "expected one case subgoal"};
static const lean_object* l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__4___closed__0 = (const lean_object*)&l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__4___closed__0_value;
static lean_once_cell_t l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__4___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__4___closed__1;
LEAN_EXPORT lean_object* l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__1___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__1(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Iff"};
static const lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___lam__0___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(19, 54, 203, 28, 77, 25, 163, 137)}};
static const lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___lam__0___closed__1_value;
static const lean_string_object l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 48, .m_capacity = 48, .m_length = 47, .m_data = "mk_iff only applies to prop-valued declarations"};
static const lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___lam__0___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___lam__0___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__2(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__6___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__6___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__6___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__6___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__6___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__6___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__6___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__6___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "failed to split goal"};
static const lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__0 = (const lean_object*)&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__1;
static const lean_string_object l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "intro"};
static const lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__2 = (const lean_object*)&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(19, 54, 203, 28, 77, 25, 163, 137)}};
static const lean_ctor_object l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__2_value),LEAN_SCALAR_PTR_LITERAL(176, 155, 85, 49, 105, 137, 67, 168)}};
static const lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__3 = (const lean_object*)&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__3_value;
static lean_once_cell_t l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__4;
static const lean_ctor_object l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 1, 0, 1, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__5 = (const lean_object*)&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__5_value;
static const lean_string_object l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "existential"};
static const lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__6 = (const lean_object*)&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__6_value;
static const lean_ctor_object l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__6_value),LEAN_SCALAR_PTR_LITERAL(130, 178, 56, 87, 59, 132, 244, 77)}};
static const lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__7 = (const lean_object*)&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__7_value;
static const lean_string_object l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__8 = (const lean_object*)&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__8_value;
static const lean_string_object l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "MkIffOfInductiveProp"};
static const lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__9 = (const lean_object*)&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__9_value;
static const lean_ctor_object l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__8_value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__10_value_aux_0),((lean_object*)&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__9_value),LEAN_SCALAR_PTR_LITERAL(173, 12, 60, 150, 142, 232, 25, 242)}};
static const lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__10 = (const lean_object*)&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__10_value;
static const lean_string_object l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__11 = (const lean_object*)&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__11_value;
static const lean_ctor_object l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__11_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__12 = (const lean_object*)&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__12_value;
static lean_once_cell_t l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__13;
static const lean_string_object l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "The type of proof of equivalence: "};
static const lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__14 = (const lean_object*)&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__14_value;
static lean_once_cell_t l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__15;
static const lean_string_object l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Existential form is: "};
static const lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__16 = (const lean_object*)&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__16_value;
static lean_once_cell_t l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__17;
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_mkSumOfProducts___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "existential_equiv"};
static const lean_object* l_Lean_Meta_mkSumOfProducts___closed__0 = (const lean_object*)&l_Lean_Meta_mkSumOfProducts___closed__0_value;
static const lean_ctor_object l_Lean_Meta_mkSumOfProducts___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkSumOfProducts___closed__0_value),LEAN_SCALAR_PTR_LITERAL(3, 65, 32, 87, 61, 118, 240, 105)}};
static const lean_object* l_Lean_Meta_mkSumOfProducts___closed__1 = (const lean_object*)&l_Lean_Meta_mkSumOfProducts___closed__1_value;
static const lean_string_object l_Lean_Meta_mkSumOfProducts___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Needs to be a definition"};
static const lean_object* l_Lean_Meta_mkSumOfProducts___closed__2 = (const lean_object*)&l_Lean_Meta_mkSumOfProducts___closed__2_value;
static lean_once_cell_t l_Lean_Meta_mkSumOfProducts___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkSumOfProducts___closed__3;
static const lean_string_object l_Lean_Meta_mkSumOfProducts___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Generating existential form of "};
static const lean_object* l_Lean_Meta_mkSumOfProducts___closed__4 = (const lean_object*)&l_Lean_Meta_mkSumOfProducts___closed__4_value;
static lean_once_cell_t l_Lean_Meta_mkSumOfProducts___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkSumOfProducts___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_mkSumOfProducts(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkSumOfProducts___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2__value),((lean_object*)&l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__8_value),LEAN_SCALAR_PTR_LITERAL(30, 196, 118, 96, 111, 225, 34, 188)}};
static const lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__9_value),LEAN_SCALAR_PTR_LITERAL(132, 73, 62, 100, 200, 255, 192, 106)}};
static const lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(229, 162, 8, 8, 152, 219, 243, 245)}};
static const lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2__value),((lean_object*)&l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(176, 197, 219, 31, 109, 114, 254, 56)}};
static const lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__8_value),LEAN_SCALAR_PTR_LITERAL(188, 189, 239, 58, 235, 121, 199, 1)}};
static const lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(73, 253, 198, 165, 62, 190, 213, 202)}};
static const lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(228, 104, 7, 130, 82, 187, 57, 46)}};
static const lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2__value),((lean_object*)&l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(69, 237, 155, 40, 27, 32, 226, 100)}};
static const lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__8_value),LEAN_SCALAR_PTR_LITERAL(45, 85, 167, 72, 140, 5, 4, 212)}};
static const lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__9_value),LEAN_SCALAR_PTR_LITERAL(83, 159, 170, 93, 251, 126, 230, 96)}};
static const lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT uint8_t l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__0(lean_object* v_x_1_){
_start:
{
uint8_t v___x_2_; 
v___x_2_ = 0;
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__0___boxed(lean_object* v_x_3_){
_start:
{
uint8_t v_res_4_; lean_object* v_r_5_; 
v_res_4_ = l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__0(v_x_3_);
lean_dec(v_x_3_);
v_r_5_ = lean_box(v_res_4_);
return v_r_5_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3_spec__5_spec__6___redArg(lean_object* v_x_6_, lean_object* v_x_7_, lean_object* v_x_8_, lean_object* v_x_9_){
_start:
{
lean_object* v_ks_10_; lean_object* v_vs_11_; lean_object* v___x_13_; uint8_t v_isShared_14_; uint8_t v_isSharedCheck_35_; 
v_ks_10_ = lean_ctor_get(v_x_6_, 0);
v_vs_11_ = lean_ctor_get(v_x_6_, 1);
v_isSharedCheck_35_ = !lean_is_exclusive(v_x_6_);
if (v_isSharedCheck_35_ == 0)
{
v___x_13_ = v_x_6_;
v_isShared_14_ = v_isSharedCheck_35_;
goto v_resetjp_12_;
}
else
{
lean_inc(v_vs_11_);
lean_inc(v_ks_10_);
lean_dec(v_x_6_);
v___x_13_ = lean_box(0);
v_isShared_14_ = v_isSharedCheck_35_;
goto v_resetjp_12_;
}
v_resetjp_12_:
{
lean_object* v___x_15_; uint8_t v___x_16_; 
v___x_15_ = lean_array_get_size(v_ks_10_);
v___x_16_ = lean_nat_dec_lt(v_x_7_, v___x_15_);
if (v___x_16_ == 0)
{
lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_20_; 
lean_dec(v_x_7_);
v___x_17_ = lean_array_push(v_ks_10_, v_x_8_);
v___x_18_ = lean_array_push(v_vs_11_, v_x_9_);
if (v_isShared_14_ == 0)
{
lean_ctor_set(v___x_13_, 1, v___x_18_);
lean_ctor_set(v___x_13_, 0, v___x_17_);
v___x_20_ = v___x_13_;
goto v_reusejp_19_;
}
else
{
lean_object* v_reuseFailAlloc_21_; 
v_reuseFailAlloc_21_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_21_, 0, v___x_17_);
lean_ctor_set(v_reuseFailAlloc_21_, 1, v___x_18_);
v___x_20_ = v_reuseFailAlloc_21_;
goto v_reusejp_19_;
}
v_reusejp_19_:
{
return v___x_20_;
}
}
else
{
lean_object* v_k_x27_22_; uint8_t v___x_23_; 
v_k_x27_22_ = lean_array_fget_borrowed(v_ks_10_, v_x_7_);
v___x_23_ = l_Lean_instBEqMVarId_beq(v_x_8_, v_k_x27_22_);
if (v___x_23_ == 0)
{
lean_object* v___x_25_; 
if (v_isShared_14_ == 0)
{
v___x_25_ = v___x_13_;
goto v_reusejp_24_;
}
else
{
lean_object* v_reuseFailAlloc_29_; 
v_reuseFailAlloc_29_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_29_, 0, v_ks_10_);
lean_ctor_set(v_reuseFailAlloc_29_, 1, v_vs_11_);
v___x_25_ = v_reuseFailAlloc_29_;
goto v_reusejp_24_;
}
v_reusejp_24_:
{
lean_object* v___x_26_; lean_object* v___x_27_; 
v___x_26_ = lean_unsigned_to_nat(1u);
v___x_27_ = lean_nat_add(v_x_7_, v___x_26_);
lean_dec(v_x_7_);
v_x_6_ = v___x_25_;
v_x_7_ = v___x_27_;
goto _start;
}
}
else
{
lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_33_; 
v___x_30_ = lean_array_fset(v_ks_10_, v_x_7_, v_x_8_);
v___x_31_ = lean_array_fset(v_vs_11_, v_x_7_, v_x_9_);
lean_dec(v_x_7_);
if (v_isShared_14_ == 0)
{
lean_ctor_set(v___x_13_, 1, v___x_31_);
lean_ctor_set(v___x_13_, 0, v___x_30_);
v___x_33_ = v___x_13_;
goto v_reusejp_32_;
}
else
{
lean_object* v_reuseFailAlloc_34_; 
v_reuseFailAlloc_34_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_34_, 0, v___x_30_);
lean_ctor_set(v_reuseFailAlloc_34_, 1, v___x_31_);
v___x_33_ = v_reuseFailAlloc_34_;
goto v_reusejp_32_;
}
v_reusejp_32_:
{
return v___x_33_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3_spec__5___redArg(lean_object* v_n_36_, lean_object* v_k_37_, lean_object* v_v_38_){
_start:
{
lean_object* v___x_39_; lean_object* v___x_40_; 
v___x_39_ = lean_unsigned_to_nat(0u);
v___x_40_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3_spec__5_spec__6___redArg(v_n_36_, v___x_39_, v_k_37_, v_v_38_);
return v___x_40_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_41_; 
v___x_41_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3___redArg(lean_object* v_x_42_, size_t v_x_43_, size_t v_x_44_, lean_object* v_x_45_, lean_object* v_x_46_){
_start:
{
if (lean_obj_tag(v_x_42_) == 0)
{
lean_object* v_es_47_; size_t v___x_48_; size_t v___x_49_; lean_object* v_j_50_; lean_object* v___x_51_; uint8_t v___x_52_; 
v_es_47_ = lean_ctor_get(v_x_42_, 0);
v___x_48_ = ((size_t)31ULL);
v___x_49_ = lean_usize_land(v_x_43_, v___x_48_);
v_j_50_ = lean_usize_to_nat(v___x_49_);
v___x_51_ = lean_array_get_size(v_es_47_);
v___x_52_ = lean_nat_dec_lt(v_j_50_, v___x_51_);
if (v___x_52_ == 0)
{
lean_dec(v_j_50_);
lean_dec(v_x_46_);
lean_dec(v_x_45_);
return v_x_42_;
}
else
{
lean_object* v___x_54_; uint8_t v_isShared_55_; uint8_t v_isSharedCheck_91_; 
lean_inc_ref(v_es_47_);
v_isSharedCheck_91_ = !lean_is_exclusive(v_x_42_);
if (v_isSharedCheck_91_ == 0)
{
lean_object* v_unused_92_; 
v_unused_92_ = lean_ctor_get(v_x_42_, 0);
lean_dec(v_unused_92_);
v___x_54_ = v_x_42_;
v_isShared_55_ = v_isSharedCheck_91_;
goto v_resetjp_53_;
}
else
{
lean_dec(v_x_42_);
v___x_54_ = lean_box(0);
v_isShared_55_ = v_isSharedCheck_91_;
goto v_resetjp_53_;
}
v_resetjp_53_:
{
lean_object* v_v_56_; lean_object* v___x_57_; lean_object* v_xs_x27_58_; lean_object* v___y_60_; 
v_v_56_ = lean_array_fget(v_es_47_, v_j_50_);
v___x_57_ = lean_box(0);
v_xs_x27_58_ = lean_array_fset(v_es_47_, v_j_50_, v___x_57_);
switch(lean_obj_tag(v_v_56_))
{
case 0:
{
lean_object* v_key_65_; lean_object* v_val_66_; lean_object* v___x_68_; uint8_t v_isShared_69_; uint8_t v_isSharedCheck_76_; 
v_key_65_ = lean_ctor_get(v_v_56_, 0);
v_val_66_ = lean_ctor_get(v_v_56_, 1);
v_isSharedCheck_76_ = !lean_is_exclusive(v_v_56_);
if (v_isSharedCheck_76_ == 0)
{
v___x_68_ = v_v_56_;
v_isShared_69_ = v_isSharedCheck_76_;
goto v_resetjp_67_;
}
else
{
lean_inc(v_val_66_);
lean_inc(v_key_65_);
lean_dec(v_v_56_);
v___x_68_ = lean_box(0);
v_isShared_69_ = v_isSharedCheck_76_;
goto v_resetjp_67_;
}
v_resetjp_67_:
{
uint8_t v___x_70_; 
v___x_70_ = l_Lean_instBEqMVarId_beq(v_x_45_, v_key_65_);
if (v___x_70_ == 0)
{
lean_object* v___x_71_; lean_object* v___x_72_; 
lean_del_object(v___x_68_);
v___x_71_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_65_, v_val_66_, v_x_45_, v_x_46_);
v___x_72_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_72_, 0, v___x_71_);
v___y_60_ = v___x_72_;
goto v___jp_59_;
}
else
{
lean_object* v___x_74_; 
lean_dec(v_val_66_);
lean_dec(v_key_65_);
if (v_isShared_69_ == 0)
{
lean_ctor_set(v___x_68_, 1, v_x_46_);
lean_ctor_set(v___x_68_, 0, v_x_45_);
v___x_74_ = v___x_68_;
goto v_reusejp_73_;
}
else
{
lean_object* v_reuseFailAlloc_75_; 
v_reuseFailAlloc_75_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_75_, 0, v_x_45_);
lean_ctor_set(v_reuseFailAlloc_75_, 1, v_x_46_);
v___x_74_ = v_reuseFailAlloc_75_;
goto v_reusejp_73_;
}
v_reusejp_73_:
{
v___y_60_ = v___x_74_;
goto v___jp_59_;
}
}
}
}
case 1:
{
lean_object* v_node_77_; lean_object* v___x_79_; uint8_t v_isShared_80_; uint8_t v_isSharedCheck_89_; 
v_node_77_ = lean_ctor_get(v_v_56_, 0);
v_isSharedCheck_89_ = !lean_is_exclusive(v_v_56_);
if (v_isSharedCheck_89_ == 0)
{
v___x_79_ = v_v_56_;
v_isShared_80_ = v_isSharedCheck_89_;
goto v_resetjp_78_;
}
else
{
lean_inc(v_node_77_);
lean_dec(v_v_56_);
v___x_79_ = lean_box(0);
v_isShared_80_ = v_isSharedCheck_89_;
goto v_resetjp_78_;
}
v_resetjp_78_:
{
size_t v___x_81_; size_t v___x_82_; size_t v___x_83_; size_t v___x_84_; lean_object* v___x_85_; lean_object* v___x_87_; 
v___x_81_ = ((size_t)5ULL);
v___x_82_ = lean_usize_shift_right(v_x_43_, v___x_81_);
v___x_83_ = ((size_t)1ULL);
v___x_84_ = lean_usize_add(v_x_44_, v___x_83_);
v___x_85_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3___redArg(v_node_77_, v___x_82_, v___x_84_, v_x_45_, v_x_46_);
if (v_isShared_80_ == 0)
{
lean_ctor_set(v___x_79_, 0, v___x_85_);
v___x_87_ = v___x_79_;
goto v_reusejp_86_;
}
else
{
lean_object* v_reuseFailAlloc_88_; 
v_reuseFailAlloc_88_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_88_, 0, v___x_85_);
v___x_87_ = v_reuseFailAlloc_88_;
goto v_reusejp_86_;
}
v_reusejp_86_:
{
v___y_60_ = v___x_87_;
goto v___jp_59_;
}
}
}
default: 
{
lean_object* v___x_90_; 
v___x_90_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_90_, 0, v_x_45_);
lean_ctor_set(v___x_90_, 1, v_x_46_);
v___y_60_ = v___x_90_;
goto v___jp_59_;
}
}
v___jp_59_:
{
lean_object* v___x_61_; lean_object* v___x_63_; 
v___x_61_ = lean_array_fset(v_xs_x27_58_, v_j_50_, v___y_60_);
lean_dec(v_j_50_);
if (v_isShared_55_ == 0)
{
lean_ctor_set(v___x_54_, 0, v___x_61_);
v___x_63_ = v___x_54_;
goto v_reusejp_62_;
}
else
{
lean_object* v_reuseFailAlloc_64_; 
v_reuseFailAlloc_64_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_64_, 0, v___x_61_);
v___x_63_ = v_reuseFailAlloc_64_;
goto v_reusejp_62_;
}
v_reusejp_62_:
{
return v___x_63_;
}
}
}
}
}
else
{
lean_object* v_ks_93_; lean_object* v_vs_94_; lean_object* v___x_96_; uint8_t v_isShared_97_; uint8_t v_isSharedCheck_112_; 
v_ks_93_ = lean_ctor_get(v_x_42_, 0);
v_vs_94_ = lean_ctor_get(v_x_42_, 1);
v_isSharedCheck_112_ = !lean_is_exclusive(v_x_42_);
if (v_isSharedCheck_112_ == 0)
{
v___x_96_ = v_x_42_;
v_isShared_97_ = v_isSharedCheck_112_;
goto v_resetjp_95_;
}
else
{
lean_inc(v_vs_94_);
lean_inc(v_ks_93_);
lean_dec(v_x_42_);
v___x_96_ = lean_box(0);
v_isShared_97_ = v_isSharedCheck_112_;
goto v_resetjp_95_;
}
v_resetjp_95_:
{
lean_object* v___x_99_; 
if (v_isShared_97_ == 0)
{
v___x_99_ = v___x_96_;
goto v_reusejp_98_;
}
else
{
lean_object* v_reuseFailAlloc_111_; 
v_reuseFailAlloc_111_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_111_, 0, v_ks_93_);
lean_ctor_set(v_reuseFailAlloc_111_, 1, v_vs_94_);
v___x_99_ = v_reuseFailAlloc_111_;
goto v_reusejp_98_;
}
v_reusejp_98_:
{
lean_object* v_newNode_100_; size_t v___x_101_; uint8_t v___x_102_; 
v_newNode_100_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3_spec__5___redArg(v___x_99_, v_x_45_, v_x_46_);
v___x_101_ = ((size_t)7ULL);
v___x_102_ = lean_usize_dec_le(v___x_101_, v_x_44_);
if (v___x_102_ == 0)
{
lean_object* v___x_103_; lean_object* v___x_104_; uint8_t v___x_105_; 
v___x_103_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_100_);
v___x_104_ = lean_unsigned_to_nat(4u);
v___x_105_ = lean_nat_dec_lt(v___x_103_, v___x_104_);
lean_dec(v___x_103_);
if (v___x_105_ == 0)
{
lean_object* v_ks_106_; lean_object* v_vs_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; 
v_ks_106_ = lean_ctor_get(v_newNode_100_, 0);
lean_inc_ref(v_ks_106_);
v_vs_107_ = lean_ctor_get(v_newNode_100_, 1);
lean_inc_ref(v_vs_107_);
lean_dec_ref(v_newNode_100_);
v___x_108_ = lean_unsigned_to_nat(0u);
v___x_109_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3___redArg___closed__0);
v___x_110_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3_spec__6___redArg(v_x_44_, v_ks_106_, v_vs_107_, v___x_108_, v___x_109_);
lean_dec_ref(v_vs_107_);
lean_dec_ref(v_ks_106_);
return v___x_110_;
}
else
{
return v_newNode_100_;
}
}
else
{
return v_newNode_100_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3_spec__6___redArg(size_t v_depth_113_, lean_object* v_keys_114_, lean_object* v_vals_115_, lean_object* v_i_116_, lean_object* v_entries_117_){
_start:
{
lean_object* v___x_118_; uint8_t v___x_119_; 
v___x_118_ = lean_array_get_size(v_keys_114_);
v___x_119_ = lean_nat_dec_lt(v_i_116_, v___x_118_);
if (v___x_119_ == 0)
{
lean_dec(v_i_116_);
return v_entries_117_;
}
else
{
lean_object* v_k_120_; lean_object* v_v_121_; uint64_t v___x_122_; size_t v_h_123_; size_t v___x_124_; lean_object* v___x_125_; size_t v___x_126_; size_t v___x_127_; size_t v___x_128_; size_t v_h_129_; lean_object* v___x_130_; lean_object* v___x_131_; 
v_k_120_ = lean_array_fget_borrowed(v_keys_114_, v_i_116_);
v_v_121_ = lean_array_fget_borrowed(v_vals_115_, v_i_116_);
v___x_122_ = l_Lean_instHashableMVarId_hash(v_k_120_);
v_h_123_ = lean_uint64_to_usize(v___x_122_);
v___x_124_ = ((size_t)5ULL);
v___x_125_ = lean_unsigned_to_nat(1u);
v___x_126_ = ((size_t)1ULL);
v___x_127_ = lean_usize_sub(v_depth_113_, v___x_126_);
v___x_128_ = lean_usize_mul(v___x_124_, v___x_127_);
v_h_129_ = lean_usize_shift_right(v_h_123_, v___x_128_);
v___x_130_ = lean_nat_add(v_i_116_, v___x_125_);
lean_dec(v_i_116_);
lean_inc(v_v_121_);
lean_inc(v_k_120_);
v___x_131_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3___redArg(v_entries_117_, v_h_129_, v_depth_113_, v_k_120_, v_v_121_);
v_i_116_ = v___x_130_;
v_entries_117_ = v___x_131_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3_spec__6___redArg___boxed(lean_object* v_depth_133_, lean_object* v_keys_134_, lean_object* v_vals_135_, lean_object* v_i_136_, lean_object* v_entries_137_){
_start:
{
size_t v_depth_boxed_138_; lean_object* v_res_139_; 
v_depth_boxed_138_ = lean_unbox_usize(v_depth_133_);
lean_dec(v_depth_133_);
v_res_139_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3_spec__6___redArg(v_depth_boxed_138_, v_keys_134_, v_vals_135_, v_i_136_, v_entries_137_);
lean_dec_ref(v_vals_135_);
lean_dec_ref(v_keys_134_);
return v_res_139_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_x_140_, lean_object* v_x_141_, lean_object* v_x_142_, lean_object* v_x_143_, lean_object* v_x_144_){
_start:
{
size_t v_x_4202__boxed_145_; size_t v_x_4203__boxed_146_; lean_object* v_res_147_; 
v_x_4202__boxed_145_ = lean_unbox_usize(v_x_141_);
lean_dec(v_x_141_);
v_x_4203__boxed_146_ = lean_unbox_usize(v_x_142_);
lean_dec(v_x_142_);
v_res_147_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3___redArg(v_x_140_, v_x_4202__boxed_145_, v_x_4203__boxed_146_, v_x_143_, v_x_144_);
return v_res_147_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2___redArg(lean_object* v_x_148_, lean_object* v_x_149_, lean_object* v_x_150_){
_start:
{
uint64_t v___x_151_; size_t v___x_152_; size_t v___x_153_; lean_object* v___x_154_; 
v___x_151_ = l_Lean_instHashableMVarId_hash(v_x_149_);
v___x_152_ = lean_uint64_to_usize(v___x_151_);
v___x_153_ = ((size_t)1ULL);
v___x_154_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3___redArg(v_x_148_, v___x_152_, v___x_153_, v_x_149_, v_x_150_);
return v___x_154_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1___redArg(lean_object* v_mvarId_155_, lean_object* v_val_156_, lean_object* v___y_157_){
_start:
{
lean_object* v___x_159_; lean_object* v_mctx_160_; lean_object* v_cache_161_; lean_object* v_zetaDeltaFVarIds_162_; lean_object* v_postponed_163_; lean_object* v_diag_164_; lean_object* v___x_166_; uint8_t v_isShared_167_; uint8_t v_isSharedCheck_194_; 
v___x_159_ = lean_st_ref_take(v___y_157_);
v_mctx_160_ = lean_ctor_get(v___x_159_, 0);
v_cache_161_ = lean_ctor_get(v___x_159_, 1);
v_zetaDeltaFVarIds_162_ = lean_ctor_get(v___x_159_, 2);
v_postponed_163_ = lean_ctor_get(v___x_159_, 3);
v_diag_164_ = lean_ctor_get(v___x_159_, 4);
v_isSharedCheck_194_ = !lean_is_exclusive(v___x_159_);
if (v_isSharedCheck_194_ == 0)
{
v___x_166_ = v___x_159_;
v_isShared_167_ = v_isSharedCheck_194_;
goto v_resetjp_165_;
}
else
{
lean_inc(v_diag_164_);
lean_inc(v_postponed_163_);
lean_inc(v_zetaDeltaFVarIds_162_);
lean_inc(v_cache_161_);
lean_inc(v_mctx_160_);
lean_dec(v___x_159_);
v___x_166_ = lean_box(0);
v_isShared_167_ = v_isSharedCheck_194_;
goto v_resetjp_165_;
}
v_resetjp_165_:
{
lean_object* v_depth_168_; lean_object* v_levelAssignDepth_169_; lean_object* v_lmvarCounter_170_; lean_object* v_mvarCounter_171_; lean_object* v_lDecls_172_; lean_object* v_decls_173_; lean_object* v_userNames_174_; lean_object* v_lAssignment_175_; lean_object* v_eAssignment_176_; lean_object* v_dAssignment_177_; lean_object* v_instanceTypedMVars_178_; lean_object* v_synthNormMemo_179_; lean_object* v___x_181_; uint8_t v_isShared_182_; uint8_t v_isSharedCheck_193_; 
v_depth_168_ = lean_ctor_get(v_mctx_160_, 0);
v_levelAssignDepth_169_ = lean_ctor_get(v_mctx_160_, 1);
v_lmvarCounter_170_ = lean_ctor_get(v_mctx_160_, 2);
v_mvarCounter_171_ = lean_ctor_get(v_mctx_160_, 3);
v_lDecls_172_ = lean_ctor_get(v_mctx_160_, 4);
v_decls_173_ = lean_ctor_get(v_mctx_160_, 5);
v_userNames_174_ = lean_ctor_get(v_mctx_160_, 6);
v_lAssignment_175_ = lean_ctor_get(v_mctx_160_, 7);
v_eAssignment_176_ = lean_ctor_get(v_mctx_160_, 8);
v_dAssignment_177_ = lean_ctor_get(v_mctx_160_, 9);
v_instanceTypedMVars_178_ = lean_ctor_get(v_mctx_160_, 10);
v_synthNormMemo_179_ = lean_ctor_get(v_mctx_160_, 11);
v_isSharedCheck_193_ = !lean_is_exclusive(v_mctx_160_);
if (v_isSharedCheck_193_ == 0)
{
v___x_181_ = v_mctx_160_;
v_isShared_182_ = v_isSharedCheck_193_;
goto v_resetjp_180_;
}
else
{
lean_inc(v_synthNormMemo_179_);
lean_inc(v_instanceTypedMVars_178_);
lean_inc(v_dAssignment_177_);
lean_inc(v_eAssignment_176_);
lean_inc(v_lAssignment_175_);
lean_inc(v_userNames_174_);
lean_inc(v_decls_173_);
lean_inc(v_lDecls_172_);
lean_inc(v_mvarCounter_171_);
lean_inc(v_lmvarCounter_170_);
lean_inc(v_levelAssignDepth_169_);
lean_inc(v_depth_168_);
lean_dec(v_mctx_160_);
v___x_181_ = lean_box(0);
v_isShared_182_ = v_isSharedCheck_193_;
goto v_resetjp_180_;
}
v_resetjp_180_:
{
lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_186_; 
v___x_183_ = lean_box(0);
v___x_184_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2___redArg(v_eAssignment_176_, v_mvarId_155_, v_val_156_);
if (v_isShared_182_ == 0)
{
lean_ctor_set(v___x_181_, 8, v___x_184_);
v___x_186_ = v___x_181_;
goto v_reusejp_185_;
}
else
{
lean_object* v_reuseFailAlloc_192_; 
v_reuseFailAlloc_192_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_192_, 0, v_depth_168_);
lean_ctor_set(v_reuseFailAlloc_192_, 1, v_levelAssignDepth_169_);
lean_ctor_set(v_reuseFailAlloc_192_, 2, v_lmvarCounter_170_);
lean_ctor_set(v_reuseFailAlloc_192_, 3, v_mvarCounter_171_);
lean_ctor_set(v_reuseFailAlloc_192_, 4, v_lDecls_172_);
lean_ctor_set(v_reuseFailAlloc_192_, 5, v_decls_173_);
lean_ctor_set(v_reuseFailAlloc_192_, 6, v_userNames_174_);
lean_ctor_set(v_reuseFailAlloc_192_, 7, v_lAssignment_175_);
lean_ctor_set(v_reuseFailAlloc_192_, 8, v___x_184_);
lean_ctor_set(v_reuseFailAlloc_192_, 9, v_dAssignment_177_);
lean_ctor_set(v_reuseFailAlloc_192_, 10, v_instanceTypedMVars_178_);
lean_ctor_set(v_reuseFailAlloc_192_, 11, v_synthNormMemo_179_);
v___x_186_ = v_reuseFailAlloc_192_;
goto v_reusejp_185_;
}
v_reusejp_185_:
{
lean_object* v___x_188_; 
if (v_isShared_167_ == 0)
{
lean_ctor_set(v___x_166_, 0, v___x_186_);
v___x_188_ = v___x_166_;
goto v_reusejp_187_;
}
else
{
lean_object* v_reuseFailAlloc_191_; 
v_reuseFailAlloc_191_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_191_, 0, v___x_186_);
lean_ctor_set(v_reuseFailAlloc_191_, 1, v_cache_161_);
lean_ctor_set(v_reuseFailAlloc_191_, 2, v_zetaDeltaFVarIds_162_);
lean_ctor_set(v_reuseFailAlloc_191_, 3, v_postponed_163_);
lean_ctor_set(v_reuseFailAlloc_191_, 4, v_diag_164_);
v___x_188_ = v_reuseFailAlloc_191_;
goto v_reusejp_187_;
}
v_reusejp_187_:
{
lean_object* v___x_189_; lean_object* v___x_190_; 
v___x_189_ = lean_st_ref_put(v___y_157_, v___x_188_);
v___x_190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_190_, 0, v___x_183_);
return v___x_190_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1___redArg___boxed(lean_object* v_mvarId_195_, lean_object* v_val_196_, lean_object* v___y_197_, lean_object* v___y_198_){
_start:
{
lean_object* v_res_199_; 
v_res_199_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1___redArg(v_mvarId_195_, v_val_196_, v___y_197_);
lean_dec(v___y_197_);
return v_res_199_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1(lean_object* v___y_230_, lean_object* v___y_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_, lean_object* v___y_236_, lean_object* v___y_237_){
_start:
{
lean_object* v_ref_239_; uint8_t v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; 
v_ref_239_ = lean_ctor_get(v___y_236_, 2);
v___x_240_ = 0;
v___x_241_ = l_Lean_SourceInfo_fromRef(v_ref_239_, v___x_240_);
v___x_242_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__3));
v___x_243_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__4));
lean_inc_n(v___x_241_, 9);
v___x_244_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_244_, 0, v___x_241_);
lean_ctor_set(v___x_244_, 1, v___x_242_);
v___x_245_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__7));
v___x_246_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__8));
v___x_247_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_247_, 0, v___x_241_);
lean_ctor_set(v___x_247_, 1, v___x_246_);
v___x_248_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__10));
v___x_249_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__12));
v___x_250_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__13));
v___x_251_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_251_, 0, v___x_241_);
lean_ctor_set(v___x_251_, 1, v___x_250_);
v___x_252_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__14));
v___x_253_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_253_, 0, v___x_241_);
lean_ctor_set(v___x_253_, 1, v___x_252_);
v___x_254_ = l_Lean_Syntax_node2(v___x_241_, v___x_249_, v___x_251_, v___x_253_);
v___x_255_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__15));
v___x_256_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_256_, 0, v___x_241_);
lean_ctor_set(v___x_256_, 1, v___x_255_);
lean_inc(v___x_254_);
v___x_257_ = l_Lean_Syntax_node3(v___x_241_, v___x_248_, v___x_254_, v___x_256_, v___x_254_);
v___x_258_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__16));
v___x_259_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_259_, 0, v___x_241_);
lean_ctor_set(v___x_259_, 1, v___x_258_);
v___x_260_ = l_Lean_Syntax_node3(v___x_241_, v___x_245_, v___x_247_, v___x_257_, v___x_259_);
v___x_261_ = l_Lean_Syntax_node2(v___x_241_, v___x_243_, v___x_244_, v___x_260_);
v___x_262_ = l_Lean_Elab_Tactic_evalTactic(v___x_261_, v___y_230_, v___y_231_, v___y_232_, v___y_233_, v___y_234_, v___y_235_, v___y_236_, v___y_237_);
return v___x_262_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___boxed(lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_, lean_object* v___y_271_){
_start:
{
lean_object* v_res_272_; 
v_res_272_ = l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1(v___y_263_, v___y_264_, v___y_265_, v___y_266_, v___y_267_, v___y_268_, v___y_269_, v___y_270_);
lean_dec(v___y_270_);
lean_dec_ref(v___y_269_);
lean_dec(v___y_268_);
lean_dec_ref(v___y_267_);
lean_dec(v___y_266_);
lean_dec_ref(v___y_265_);
lean_dec(v___y_264_);
lean_dec_ref(v___y_263_);
return v_res_272_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0_spec__0(lean_object* v_msgData_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_){
_start:
{
lean_object* v___x_279_; lean_object* v_env_280_; uint8_t v___x_281_; lean_object* v_env_282_; lean_object* v___x_283_; lean_object* v_toCold_284_; lean_object* v_mctx_285_; lean_object* v_lctx_286_; lean_object* v_options_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; 
v___x_279_ = lean_st_ref_get(v___y_277_);
v_env_280_ = lean_ctor_get(v___x_279_, 0);
lean_inc_ref(v_env_280_);
lean_dec(v___x_279_);
v___x_281_ = 0;
v_env_282_ = l_Lean_Environment_setRecordingDeps(v_env_280_, v___x_281_);
v___x_283_ = lean_st_ref_get(v___y_275_);
v_toCold_284_ = lean_ctor_get(v___y_276_, 0);
v_mctx_285_ = lean_ctor_get(v___x_283_, 0);
lean_inc_ref(v_mctx_285_);
lean_dec(v___x_283_);
v_lctx_286_ = lean_ctor_get(v___y_274_, 2);
v_options_287_ = lean_ctor_get(v_toCold_284_, 2);
lean_inc_ref(v_options_287_);
lean_inc_ref(v_lctx_286_);
v___x_288_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_288_, 0, v_env_282_);
lean_ctor_set(v___x_288_, 1, v_mctx_285_);
lean_ctor_set(v___x_288_, 2, v_lctx_286_);
lean_ctor_set(v___x_288_, 3, v_options_287_);
v___x_289_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_289_, 0, v___x_288_);
lean_ctor_set(v___x_289_, 1, v_msgData_273_);
v___x_290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_290_, 0, v___x_289_);
return v___x_290_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0_spec__0___boxed(lean_object* v_msgData_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_){
_start:
{
lean_object* v_res_297_; 
v_res_297_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0_spec__0(v_msgData_291_, v___y_292_, v___y_293_, v___y_294_, v___y_295_);
lean_dec(v___y_295_);
lean_dec_ref(v___y_294_);
lean_dec(v___y_293_);
lean_dec_ref(v___y_292_);
return v_res_297_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0___redArg(lean_object* v_msg_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_){
_start:
{
lean_object* v_ref_304_; lean_object* v___x_305_; lean_object* v_a_306_; lean_object* v___x_308_; uint8_t v_isShared_309_; uint8_t v_isSharedCheck_314_; 
v_ref_304_ = lean_ctor_get(v___y_301_, 2);
v___x_305_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0_spec__0(v_msg_298_, v___y_299_, v___y_300_, v___y_301_, v___y_302_);
v_a_306_ = lean_ctor_get(v___x_305_, 0);
v_isSharedCheck_314_ = !lean_is_exclusive(v___x_305_);
if (v_isSharedCheck_314_ == 0)
{
v___x_308_ = v___x_305_;
v_isShared_309_ = v_isSharedCheck_314_;
goto v_resetjp_307_;
}
else
{
lean_inc(v_a_306_);
lean_dec(v___x_305_);
v___x_308_ = lean_box(0);
v_isShared_309_ = v_isSharedCheck_314_;
goto v_resetjp_307_;
}
v_resetjp_307_:
{
lean_object* v___x_310_; lean_object* v___x_312_; 
lean_inc(v_ref_304_);
v___x_310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_310_, 0, v_ref_304_);
lean_ctor_set(v___x_310_, 1, v_a_306_);
if (v_isShared_309_ == 0)
{
lean_ctor_set_tag(v___x_308_, 1);
lean_ctor_set(v___x_308_, 0, v___x_310_);
v___x_312_ = v___x_308_;
goto v_reusejp_311_;
}
else
{
lean_object* v_reuseFailAlloc_313_; 
v_reuseFailAlloc_313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_313_, 0, v___x_310_);
v___x_312_ = v_reuseFailAlloc_313_;
goto v_reusejp_311_;
}
v_reusejp_311_:
{
return v___x_312_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0___redArg___boxed(lean_object* v_msg_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_, lean_object* v___y_319_, lean_object* v___y_320_){
_start:
{
lean_object* v_res_321_; 
v_res_321_ = l_Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0___redArg(v_msg_315_, v___y_316_, v___y_317_, v___y_318_, v___y_319_);
lean_dec(v___y_319_);
lean_dec_ref(v___y_318_);
lean_dec(v___y_317_);
lean_dec_ref(v___y_316_);
return v_res_321_;
}
}
static lean_object* _init_l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___closed__1(void){
_start:
{
lean_object* v___x_323_; lean_object* v___x_324_; 
v___x_323_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___closed__0));
v___x_324_ = l_Lean_stringToMessageData(v___x_323_);
return v___x_324_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2(lean_object* v_x_340_, lean_object* v_x_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_){
_start:
{
if (lean_obj_tag(v_x_341_) == 0)
{
lean_object* v___x_347_; 
v___x_347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_347_, 0, v_x_340_);
return v___x_347_;
}
else
{
lean_object* v_head_348_; lean_object* v_tail_349_; lean_object* v___y_351_; lean_object* v___y_352_; lean_object* v___y_353_; lean_object* v___y_354_; lean_object* v___f_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; 
v_head_348_ = lean_ctor_get(v_x_341_, 0);
lean_inc(v_head_348_);
v_tail_349_ = lean_ctor_get(v_x_341_, 1);
lean_inc(v_tail_349_);
lean_dec_ref_known(v_x_341_, 2);
v___f_357_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___closed__3));
v___x_358_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_run___boxed), 9, 2);
lean_closure_set(v___x_358_, 0, v_x_340_);
lean_closure_set(v___x_358_, 1, v___f_357_);
v___x_359_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___closed__5));
v___x_360_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___closed__6));
v___x_361_ = l_Lean_Elab_Term_TermElabM_run___redArg(v___x_358_, v___x_359_, v___x_360_, v___y_342_, v___y_343_, v___y_344_, v___y_345_);
if (lean_obj_tag(v___x_361_) == 0)
{
lean_object* v_a_362_; lean_object* v_fst_363_; 
v_a_362_ = lean_ctor_get(v___x_361_, 0);
lean_inc(v_a_362_);
lean_dec_ref_known(v___x_361_, 1);
v_fst_363_ = lean_ctor_get(v_a_362_, 0);
lean_inc(v_fst_363_);
lean_dec(v_a_362_);
if (lean_obj_tag(v_fst_363_) == 1)
{
lean_object* v_tail_364_; 
v_tail_364_ = lean_ctor_get(v_fst_363_, 1);
lean_inc(v_tail_364_);
if (lean_obj_tag(v_tail_364_) == 1)
{
lean_object* v_tail_365_; 
v_tail_365_ = lean_ctor_get(v_tail_364_, 1);
if (lean_obj_tag(v_tail_365_) == 0)
{
lean_object* v_head_366_; lean_object* v_head_367_; lean_object* v___x_368_; 
v_head_366_ = lean_ctor_get(v_fst_363_, 0);
lean_inc(v_head_366_);
lean_dec_ref_known(v_fst_363_, 2);
v_head_367_ = lean_ctor_get(v_tail_364_, 0);
lean_inc(v_head_367_);
lean_dec_ref_known(v_tail_364_, 2);
v___x_368_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1___redArg(v_head_366_, v_head_348_, v___y_343_);
lean_dec_ref(v___x_368_);
v_x_340_ = v_head_367_;
v_x_341_ = v_tail_349_;
goto _start;
}
else
{
lean_dec_ref_known(v_tail_364_, 2);
lean_dec_ref_known(v_fst_363_, 2);
lean_dec(v_tail_349_);
lean_dec(v_head_348_);
v___y_351_ = v___y_342_;
v___y_352_ = v___y_343_;
v___y_353_ = v___y_344_;
v___y_354_ = v___y_345_;
goto v___jp_350_;
}
}
else
{
lean_dec(v_tail_364_);
lean_dec_ref_known(v_fst_363_, 2);
lean_dec(v_tail_349_);
lean_dec(v_head_348_);
v___y_351_ = v___y_342_;
v___y_352_ = v___y_343_;
v___y_353_ = v___y_344_;
v___y_354_ = v___y_345_;
goto v___jp_350_;
}
}
else
{
lean_dec(v_fst_363_);
lean_dec(v_tail_349_);
lean_dec(v_head_348_);
v___y_351_ = v___y_342_;
v___y_352_ = v___y_343_;
v___y_353_ = v___y_344_;
v___y_354_ = v___y_345_;
goto v___jp_350_;
}
}
else
{
lean_object* v_a_370_; lean_object* v___x_372_; uint8_t v_isShared_373_; uint8_t v_isSharedCheck_377_; 
lean_dec(v_tail_349_);
lean_dec(v_head_348_);
v_a_370_ = lean_ctor_get(v___x_361_, 0);
v_isSharedCheck_377_ = !lean_is_exclusive(v___x_361_);
if (v_isSharedCheck_377_ == 0)
{
v___x_372_ = v___x_361_;
v_isShared_373_ = v_isSharedCheck_377_;
goto v_resetjp_371_;
}
else
{
lean_inc(v_a_370_);
lean_dec(v___x_361_);
v___x_372_ = lean_box(0);
v_isShared_373_ = v_isSharedCheck_377_;
goto v_resetjp_371_;
}
v_resetjp_371_:
{
lean_object* v___x_375_; 
if (v_isShared_373_ == 0)
{
v___x_375_ = v___x_372_;
goto v_reusejp_374_;
}
else
{
lean_object* v_reuseFailAlloc_376_; 
v_reuseFailAlloc_376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_376_, 0, v_a_370_);
v___x_375_ = v_reuseFailAlloc_376_;
goto v_reusejp_374_;
}
v_reusejp_374_:
{
return v___x_375_;
}
}
}
v___jp_350_:
{
lean_object* v___x_355_; lean_object* v___x_356_; 
v___x_355_ = lean_obj_once(&l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___closed__1, &l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___closed__1_once, _init_l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___closed__1);
v___x_356_ = l_Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0___redArg(v___x_355_, v___y_351_, v___y_352_, v___y_353_, v___y_354_);
return v___x_356_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___boxed(lean_object* v_x_378_, lean_object* v_x_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_){
_start:
{
lean_object* v_res_385_; 
v_res_385_ = l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2(v_x_378_, v_x_379_, v___y_380_, v___y_381_, v___y_382_, v___y_383_);
lean_dec(v___y_383_);
lean_dec_ref(v___y_382_);
lean_dec(v___y_381_);
lean_dec_ref(v___y_380_);
return v_res_385_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi(lean_object* v_mvar_386_, lean_object* v_es_387_, lean_object* v_a_388_, lean_object* v_a_389_, lean_object* v_a_390_, lean_object* v_a_391_){
_start:
{
lean_object* v___x_393_; 
v___x_393_ = l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2(v_mvar_386_, v_es_387_, v_a_388_, v_a_389_, v_a_390_, v_a_391_);
return v___x_393_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi___boxed(lean_object* v_mvar_394_, lean_object* v_es_395_, lean_object* v_a_396_, lean_object* v_a_397_, lean_object* v_a_398_, lean_object* v_a_399_, lean_object* v_a_400_){
_start:
{
lean_object* v_res_401_; 
v_res_401_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi(v_mvar_394_, v_es_395_, v_a_396_, v_a_397_, v_a_398_, v_a_399_);
lean_dec(v_a_399_);
lean_dec_ref(v_a_398_);
lean_dec(v_a_397_);
lean_dec_ref(v_a_396_);
return v_res_401_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0(lean_object* v_00_u03b1_402_, lean_object* v_msg_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_){
_start:
{
lean_object* v___x_409_; 
v___x_409_ = l_Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0___redArg(v_msg_403_, v___y_404_, v___y_405_, v___y_406_, v___y_407_);
return v___x_409_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0___boxed(lean_object* v_00_u03b1_410_, lean_object* v_msg_411_, lean_object* v___y_412_, lean_object* v___y_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_){
_start:
{
lean_object* v_res_417_; 
v_res_417_ = l_Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0(v_00_u03b1_410_, v_msg_411_, v___y_412_, v___y_413_, v___y_414_, v___y_415_);
lean_dec(v___y_415_);
lean_dec_ref(v___y_414_);
lean_dec(v___y_413_);
lean_dec_ref(v___y_412_);
return v_res_417_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1(lean_object* v_mvarId_418_, lean_object* v_val_419_, lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_, lean_object* v___y_423_){
_start:
{
lean_object* v___x_425_; 
v___x_425_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1___redArg(v_mvarId_418_, v_val_419_, v___y_421_);
return v___x_425_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1___boxed(lean_object* v_mvarId_426_, lean_object* v_val_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_){
_start:
{
lean_object* v_res_433_; 
v_res_433_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1(v_mvarId_426_, v_val_427_, v___y_428_, v___y_429_, v___y_430_, v___y_431_);
lean_dec(v___y_431_);
lean_dec_ref(v___y_430_);
lean_dec(v___y_429_);
lean_dec_ref(v___y_428_);
return v_res_433_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2(lean_object* v_00_u03b2_434_, lean_object* v_x_435_, lean_object* v_x_436_, lean_object* v_x_437_){
_start:
{
lean_object* v___x_438_; 
v___x_438_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2___redArg(v_x_435_, v_x_436_, v_x_437_);
return v___x_438_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_439_, lean_object* v_x_440_, size_t v_x_441_, size_t v_x_442_, lean_object* v_x_443_, lean_object* v_x_444_){
_start:
{
lean_object* v___x_445_; 
v___x_445_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3___redArg(v_x_440_, v_x_441_, v_x_442_, v_x_443_, v_x_444_);
return v___x_445_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03b2_446_, lean_object* v_x_447_, lean_object* v_x_448_, lean_object* v_x_449_, lean_object* v_x_450_, lean_object* v_x_451_){
_start:
{
size_t v_x_4860__boxed_452_; size_t v_x_4861__boxed_453_; lean_object* v_res_454_; 
v_x_4860__boxed_452_ = lean_unbox_usize(v_x_448_);
lean_dec(v_x_448_);
v_x_4861__boxed_453_ = lean_unbox_usize(v_x_449_);
lean_dec(v_x_449_);
v_res_454_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3(v_00_u03b2_446_, v_x_447_, v_x_4860__boxed_452_, v_x_4861__boxed_453_, v_x_450_, v_x_451_);
return v_res_454_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3_spec__5(lean_object* v_00_u03b2_455_, lean_object* v_n_456_, lean_object* v_k_457_, lean_object* v_v_458_){
_start:
{
lean_object* v___x_459_; 
v___x_459_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3_spec__5___redArg(v_n_456_, v_k_457_, v_v_458_);
return v___x_459_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3_spec__6(lean_object* v_00_u03b2_460_, size_t v_depth_461_, lean_object* v_keys_462_, lean_object* v_vals_463_, lean_object* v_heq_464_, lean_object* v_i_465_, lean_object* v_entries_466_){
_start:
{
lean_object* v___x_467_; 
v___x_467_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3_spec__6___redArg(v_depth_461_, v_keys_462_, v_vals_463_, v_i_465_, v_entries_466_);
return v___x_467_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3_spec__6___boxed(lean_object* v_00_u03b2_468_, lean_object* v_depth_469_, lean_object* v_keys_470_, lean_object* v_vals_471_, lean_object* v_heq_472_, lean_object* v_i_473_, lean_object* v_entries_474_){
_start:
{
size_t v_depth_boxed_475_; lean_object* v_res_476_; 
v_depth_boxed_475_ = lean_unbox_usize(v_depth_469_);
lean_dec(v_depth_469_);
v_res_476_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3_spec__6(v_00_u03b2_468_, v_depth_boxed_475_, v_keys_470_, v_vals_471_, v_heq_472_, v_i_473_, v_entries_474_);
lean_dec_ref(v_vals_471_);
lean_dec_ref(v_keys_470_);
return v_res_476_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3_spec__5_spec__6(lean_object* v_00_u03b2_477_, lean_object* v_x_478_, lean_object* v_x_479_, lean_object* v_x_480_, lean_object* v_x_481_){
_start:
{
lean_object* v___x_482_; 
v___x_482_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3_spec__5_spec__6___redArg(v_x_478_, v_x_479_, v_x_480_, v_x_481_);
return v___x_482_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor_spec__0___redArg(lean_object* v_mvarId_483_, lean_object* v_x_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_){
_start:
{
lean_object* v___x_490_; 
v___x_490_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_483_, v_x_484_, v___y_485_, v___y_486_, v___y_487_, v___y_488_);
if (lean_obj_tag(v___x_490_) == 0)
{
lean_object* v_a_491_; lean_object* v___x_493_; uint8_t v_isShared_494_; uint8_t v_isSharedCheck_498_; 
v_a_491_ = lean_ctor_get(v___x_490_, 0);
v_isSharedCheck_498_ = !lean_is_exclusive(v___x_490_);
if (v_isSharedCheck_498_ == 0)
{
v___x_493_ = v___x_490_;
v_isShared_494_ = v_isSharedCheck_498_;
goto v_resetjp_492_;
}
else
{
lean_inc(v_a_491_);
lean_dec(v___x_490_);
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
v_reuseFailAlloc_497_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_499_; lean_object* v___x_501_; uint8_t v_isShared_502_; uint8_t v_isSharedCheck_506_; 
v_a_499_ = lean_ctor_get(v___x_490_, 0);
v_isSharedCheck_506_ = !lean_is_exclusive(v___x_490_);
if (v_isSharedCheck_506_ == 0)
{
v___x_501_ = v___x_490_;
v_isShared_502_ = v_isSharedCheck_506_;
goto v_resetjp_500_;
}
else
{
lean_inc(v_a_499_);
lean_dec(v___x_490_);
v___x_501_ = lean_box(0);
v_isShared_502_ = v_isSharedCheck_506_;
goto v_resetjp_500_;
}
v_resetjp_500_:
{
lean_object* v___x_504_; 
if (v_isShared_502_ == 0)
{
v___x_504_ = v___x_501_;
goto v_reusejp_503_;
}
else
{
lean_object* v_reuseFailAlloc_505_; 
v_reuseFailAlloc_505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_505_, 0, v_a_499_);
v___x_504_ = v_reuseFailAlloc_505_;
goto v_reusejp_503_;
}
v_reusejp_503_:
{
return v___x_504_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor_spec__0___redArg___boxed(lean_object* v_mvarId_507_, lean_object* v_x_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_){
_start:
{
lean_object* v_res_514_; 
v_res_514_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor_spec__0___redArg(v_mvarId_507_, v_x_508_, v___y_509_, v___y_510_, v___y_511_, v___y_512_);
lean_dec(v___y_512_);
lean_dec_ref(v___y_511_);
lean_dec(v___y_510_);
lean_dec_ref(v___y_509_);
return v_res_514_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor_spec__0(lean_object* v_00_u03b1_515_, lean_object* v_mvarId_516_, lean_object* v_x_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_){
_start:
{
lean_object* v___x_523_; 
v___x_523_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor_spec__0___redArg(v_mvarId_516_, v_x_517_, v___y_518_, v___y_519_, v___y_520_, v___y_521_);
return v___x_523_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor_spec__0___boxed(lean_object* v_00_u03b1_524_, lean_object* v_mvarId_525_, lean_object* v_x_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_){
_start:
{
lean_object* v_res_532_; 
v_res_532_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor_spec__0(v_00_u03b1_524_, v_mvarId_525_, v_x_526_, v___y_527_, v___y_528_, v___y_529_, v___y_530_);
lean_dec(v___y_530_);
lean_dec_ref(v___y_529_);
lean_dec(v___y_528_);
lean_dec_ref(v___y_527_);
return v_res_532_;
}
}
static lean_object* _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0___closed__2(void){
_start:
{
lean_object* v___x_536_; lean_object* v___x_537_; 
v___x_536_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0___closed__1));
v___x_537_ = l_Lean_MessageData_ofFormat(v___x_536_);
return v___x_537_;
}
}
static lean_object* _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0___closed__3(void){
_start:
{
lean_object* v___x_538_; lean_object* v___x_539_; 
v___x_538_ = lean_obj_once(&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0___closed__2, &l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0___closed__2_once, _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0___closed__2);
v___x_539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_539_, 0, v___x_538_);
return v___x_539_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0(lean_object* v_name_544_, lean_object* v_goal_545_, lean_object* v_idx_546_, lean_object* v_expected_x3f_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_){
_start:
{
lean_object* v___x_556_; 
lean_inc(v_name_544_);
lean_inc(v_goal_545_);
v___x_556_ = l_Lean_MVarId_checkNotAssigned(v_goal_545_, v_name_544_, v___y_548_, v___y_549_, v___y_550_, v___y_551_);
if (lean_obj_tag(v___x_556_) == 0)
{
lean_object* v___x_557_; 
lean_dec_ref_known(v___x_556_, 1);
lean_inc(v_goal_545_);
v___x_557_ = l_Lean_MVarId_getType_x27(v_goal_545_, v___y_548_, v___y_549_, v___y_550_, v___y_551_);
if (lean_obj_tag(v___x_557_) == 0)
{
lean_object* v_a_558_; lean_object* v___x_559_; 
v_a_558_ = lean_ctor_get(v___x_557_, 0);
lean_inc(v_a_558_);
lean_dec_ref_known(v___x_557_, 1);
v___x_559_ = l_Lean_Expr_getAppFn(v_a_558_);
lean_dec(v_a_558_);
if (lean_obj_tag(v___x_559_) == 4)
{
lean_object* v_declName_560_; lean_object* v_us_561_; lean_object* v___x_562_; lean_object* v_env_563_; uint8_t v___x_564_; lean_object* v___x_565_; 
v_declName_560_ = lean_ctor_get(v___x_559_, 0);
lean_inc(v_declName_560_);
v_us_561_ = lean_ctor_get(v___x_559_, 1);
lean_inc(v_us_561_);
lean_dec_ref_known(v___x_559_, 2);
v___x_562_ = lean_st_ref_get(v___y_551_);
v_env_563_ = lean_ctor_get(v___x_562_, 0);
lean_inc_ref(v_env_563_);
lean_dec(v___x_562_);
v___x_564_ = 0;
v___x_565_ = l_Lean_Environment_find_x3f(v_env_563_, v_declName_560_, v___x_564_);
if (lean_obj_tag(v___x_565_) == 0)
{
lean_dec(v_us_561_);
lean_dec(v_expected_x3f_547_);
lean_dec(v_idx_546_);
goto v___jp_553_;
}
else
{
lean_object* v_val_566_; lean_object* v___x_568_; uint8_t v_isShared_569_; uint8_t v_isSharedCheck_636_; 
v_val_566_ = lean_ctor_get(v___x_565_, 0);
v_isSharedCheck_636_ = !lean_is_exclusive(v___x_565_);
if (v_isSharedCheck_636_ == 0)
{
v___x_568_ = v___x_565_;
v_isShared_569_ = v_isSharedCheck_636_;
goto v_resetjp_567_;
}
else
{
lean_inc(v_val_566_);
lean_dec(v___x_565_);
v___x_568_ = lean_box(0);
v_isShared_569_ = v_isSharedCheck_636_;
goto v_resetjp_567_;
}
v_resetjp_567_:
{
if (lean_obj_tag(v_val_566_) == 5)
{
lean_object* v_val_570_; lean_object* v___x_572_; uint8_t v_isShared_573_; uint8_t v_isSharedCheck_635_; 
v_val_570_ = lean_ctor_get(v_val_566_, 0);
v_isSharedCheck_635_ = !lean_is_exclusive(v_val_566_);
if (v_isSharedCheck_635_ == 0)
{
v___x_572_ = v_val_566_;
v_isShared_573_ = v_isSharedCheck_635_;
goto v_resetjp_571_;
}
else
{
lean_inc(v_val_570_);
lean_dec(v_val_566_);
v___x_572_ = lean_box(0);
v_isShared_573_ = v_isSharedCheck_635_;
goto v_resetjp_571_;
}
v_resetjp_571_:
{
lean_object* v___y_575_; lean_object* v___y_576_; lean_object* v___y_577_; lean_object* v___y_578_; 
if (lean_obj_tag(v_expected_x3f_547_) == 1)
{
lean_object* v_val_605_; lean_object* v___x_607_; uint8_t v_isShared_608_; uint8_t v_isSharedCheck_634_; 
v_val_605_ = lean_ctor_get(v_expected_x3f_547_, 0);
v_isSharedCheck_634_ = !lean_is_exclusive(v_expected_x3f_547_);
if (v_isSharedCheck_634_ == 0)
{
v___x_607_ = v_expected_x3f_547_;
v_isShared_608_ = v_isSharedCheck_634_;
goto v_resetjp_606_;
}
else
{
lean_inc(v_val_605_);
lean_dec(v_expected_x3f_547_);
v___x_607_ = lean_box(0);
v_isShared_608_ = v_isSharedCheck_634_;
goto v_resetjp_606_;
}
v_resetjp_606_:
{
lean_object* v_ctors_609_; lean_object* v___x_610_; uint8_t v___x_611_; 
v_ctors_609_ = lean_ctor_get(v_val_570_, 4);
v___x_610_ = l_List_lengthTR___redArg(v_ctors_609_);
v___x_611_ = lean_nat_dec_eq(v___x_610_, v_val_605_);
lean_dec(v___x_610_);
if (v___x_611_ == 0)
{
uint8_t v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_623_; 
v___x_612_ = 1;
lean_inc(v_name_544_);
v___x_613_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_544_, v___x_612_);
v___x_614_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0___closed__7));
v___x_615_ = lean_string_append(v___x_613_, v___x_614_);
v___x_616_ = l_Nat_reprFast(v_val_605_);
v___x_617_ = lean_string_append(v___x_615_, v___x_616_);
lean_dec_ref(v___x_616_);
v___x_618_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0___closed__6));
v___x_619_ = lean_string_append(v___x_617_, v___x_618_);
v___x_620_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_620_, 0, v___x_619_);
v___x_621_ = l_Lean_MessageData_ofFormat(v___x_620_);
if (v_isShared_608_ == 0)
{
lean_ctor_set(v___x_607_, 0, v___x_621_);
v___x_623_ = v___x_607_;
goto v_reusejp_622_;
}
else
{
lean_object* v_reuseFailAlloc_633_; 
v_reuseFailAlloc_633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_633_, 0, v___x_621_);
v___x_623_ = v_reuseFailAlloc_633_;
goto v_reusejp_622_;
}
v_reusejp_622_:
{
lean_object* v___x_624_; 
lean_inc(v_goal_545_);
lean_inc(v_name_544_);
v___x_624_ = l_Lean_Meta_throwTacticEx___redArg(v_name_544_, v_goal_545_, v___x_623_, v___y_548_, v___y_549_, v___y_550_, v___y_551_);
if (lean_obj_tag(v___x_624_) == 0)
{
lean_dec_ref_known(v___x_624_, 1);
v___y_575_ = v___y_548_;
v___y_576_ = v___y_549_;
v___y_577_ = v___y_550_;
v___y_578_ = v___y_551_;
goto v___jp_574_;
}
else
{
lean_object* v_a_625_; lean_object* v___x_627_; uint8_t v_isShared_628_; uint8_t v_isSharedCheck_632_; 
lean_del_object(v___x_572_);
lean_dec_ref(v_val_570_);
lean_del_object(v___x_568_);
lean_dec(v_us_561_);
lean_dec(v_idx_546_);
lean_dec(v_goal_545_);
lean_dec(v_name_544_);
v_a_625_ = lean_ctor_get(v___x_624_, 0);
v_isSharedCheck_632_ = !lean_is_exclusive(v___x_624_);
if (v_isSharedCheck_632_ == 0)
{
v___x_627_ = v___x_624_;
v_isShared_628_ = v_isSharedCheck_632_;
goto v_resetjp_626_;
}
else
{
lean_inc(v_a_625_);
lean_dec(v___x_624_);
v___x_627_ = lean_box(0);
v_isShared_628_ = v_isSharedCheck_632_;
goto v_resetjp_626_;
}
v_resetjp_626_:
{
lean_object* v___x_630_; 
if (v_isShared_628_ == 0)
{
v___x_630_ = v___x_627_;
goto v_reusejp_629_;
}
else
{
lean_object* v_reuseFailAlloc_631_; 
v_reuseFailAlloc_631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_631_, 0, v_a_625_);
v___x_630_ = v_reuseFailAlloc_631_;
goto v_reusejp_629_;
}
v_reusejp_629_:
{
return v___x_630_;
}
}
}
}
}
else
{
lean_del_object(v___x_607_);
lean_dec(v_val_605_);
v___y_575_ = v___y_548_;
v___y_576_ = v___y_549_;
v___y_577_ = v___y_550_;
v___y_578_ = v___y_551_;
goto v___jp_574_;
}
}
}
else
{
lean_dec(v_expected_x3f_547_);
v___y_575_ = v___y_548_;
v___y_576_ = v___y_549_;
v___y_577_ = v___y_550_;
v___y_578_ = v___y_551_;
goto v___jp_574_;
}
v___jp_574_:
{
lean_object* v_ctors_579_; lean_object* v___x_580_; uint8_t v___x_581_; 
v_ctors_579_ = lean_ctor_get(v_val_570_, 4);
lean_inc(v_ctors_579_);
lean_dec_ref(v_val_570_);
v___x_580_ = l_List_lengthTR___redArg(v_ctors_579_);
v___x_581_ = lean_nat_dec_lt(v_idx_546_, v___x_580_);
if (v___x_581_ == 0)
{
lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_592_; 
lean_dec(v_ctors_579_);
lean_dec(v_us_561_);
v___x_582_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0___closed__4));
v___x_583_ = l_Nat_reprFast(v_idx_546_);
v___x_584_ = lean_string_append(v___x_582_, v___x_583_);
lean_dec_ref(v___x_583_);
v___x_585_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0___closed__5));
v___x_586_ = lean_string_append(v___x_584_, v___x_585_);
v___x_587_ = l_Nat_reprFast(v___x_580_);
v___x_588_ = lean_string_append(v___x_586_, v___x_587_);
lean_dec_ref(v___x_587_);
v___x_589_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0___closed__6));
v___x_590_ = lean_string_append(v___x_588_, v___x_589_);
if (v_isShared_573_ == 0)
{
lean_ctor_set_tag(v___x_572_, 3);
lean_ctor_set(v___x_572_, 0, v___x_590_);
v___x_592_ = v___x_572_;
goto v_reusejp_591_;
}
else
{
lean_object* v_reuseFailAlloc_598_; 
v_reuseFailAlloc_598_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_598_, 0, v___x_590_);
v___x_592_ = v_reuseFailAlloc_598_;
goto v_reusejp_591_;
}
v_reusejp_591_:
{
lean_object* v___x_593_; lean_object* v___x_595_; 
v___x_593_ = l_Lean_MessageData_ofFormat(v___x_592_);
if (v_isShared_569_ == 0)
{
lean_ctor_set(v___x_568_, 0, v___x_593_);
v___x_595_ = v___x_568_;
goto v_reusejp_594_;
}
else
{
lean_object* v_reuseFailAlloc_597_; 
v_reuseFailAlloc_597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_597_, 0, v___x_593_);
v___x_595_ = v_reuseFailAlloc_597_;
goto v_reusejp_594_;
}
v_reusejp_594_:
{
lean_object* v___x_596_; 
v___x_596_ = l_Lean_Meta_throwTacticEx___redArg(v_name_544_, v_goal_545_, v___x_595_, v___y_575_, v___y_576_, v___y_577_, v___y_578_);
return v___x_596_;
}
}
}
else
{
lean_object* v___x_599_; lean_object* v___x_600_; uint8_t v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; 
lean_dec(v___x_580_);
lean_del_object(v___x_572_);
lean_del_object(v___x_568_);
lean_dec(v_name_544_);
v___x_599_ = l_List_get___redArg(v_ctors_579_, v_idx_546_);
lean_dec(v_ctors_579_);
v___x_600_ = l_Lean_mkConst(v___x_599_, v_us_561_);
v___x_601_ = 0;
v___x_602_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_602_, 0, v___x_601_);
lean_ctor_set_uint8(v___x_602_, 1, v___x_581_);
lean_ctor_set_uint8(v___x_602_, 2, v___x_564_);
lean_ctor_set_uint8(v___x_602_, 3, v___x_581_);
v___x_603_ = lean_box(0);
v___x_604_ = l_Lean_MVarId_apply(v_goal_545_, v___x_600_, v___x_602_, v___x_603_, v___y_575_, v___y_576_, v___y_577_, v___y_578_);
return v___x_604_;
}
}
}
}
else
{
lean_del_object(v___x_568_);
lean_dec(v_val_566_);
lean_dec(v_us_561_);
lean_dec(v_expected_x3f_547_);
lean_dec(v_idx_546_);
goto v___jp_553_;
}
}
}
}
else
{
lean_dec_ref(v___x_559_);
lean_dec(v_expected_x3f_547_);
lean_dec(v_idx_546_);
goto v___jp_553_;
}
}
else
{
lean_object* v_a_637_; lean_object* v___x_639_; uint8_t v_isShared_640_; uint8_t v_isSharedCheck_644_; 
lean_dec(v_expected_x3f_547_);
lean_dec(v_idx_546_);
lean_dec(v_goal_545_);
lean_dec(v_name_544_);
v_a_637_ = lean_ctor_get(v___x_557_, 0);
v_isSharedCheck_644_ = !lean_is_exclusive(v___x_557_);
if (v_isSharedCheck_644_ == 0)
{
v___x_639_ = v___x_557_;
v_isShared_640_ = v_isSharedCheck_644_;
goto v_resetjp_638_;
}
else
{
lean_inc(v_a_637_);
lean_dec(v___x_557_);
v___x_639_ = lean_box(0);
v_isShared_640_ = v_isSharedCheck_644_;
goto v_resetjp_638_;
}
v_resetjp_638_:
{
lean_object* v___x_642_; 
if (v_isShared_640_ == 0)
{
v___x_642_ = v___x_639_;
goto v_reusejp_641_;
}
else
{
lean_object* v_reuseFailAlloc_643_; 
v_reuseFailAlloc_643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_643_, 0, v_a_637_);
v___x_642_ = v_reuseFailAlloc_643_;
goto v_reusejp_641_;
}
v_reusejp_641_:
{
return v___x_642_;
}
}
}
}
else
{
lean_object* v_a_645_; lean_object* v___x_647_; uint8_t v_isShared_648_; uint8_t v_isSharedCheck_652_; 
lean_dec(v_expected_x3f_547_);
lean_dec(v_idx_546_);
lean_dec(v_goal_545_);
lean_dec(v_name_544_);
v_a_645_ = lean_ctor_get(v___x_556_, 0);
v_isSharedCheck_652_ = !lean_is_exclusive(v___x_556_);
if (v_isSharedCheck_652_ == 0)
{
v___x_647_ = v___x_556_;
v_isShared_648_ = v_isSharedCheck_652_;
goto v_resetjp_646_;
}
else
{
lean_inc(v_a_645_);
lean_dec(v___x_556_);
v___x_647_ = lean_box(0);
v_isShared_648_ = v_isSharedCheck_652_;
goto v_resetjp_646_;
}
v_resetjp_646_:
{
lean_object* v___x_650_; 
if (v_isShared_648_ == 0)
{
v___x_650_ = v___x_647_;
goto v_reusejp_649_;
}
else
{
lean_object* v_reuseFailAlloc_651_; 
v_reuseFailAlloc_651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_651_, 0, v_a_645_);
v___x_650_ = v_reuseFailAlloc_651_;
goto v_reusejp_649_;
}
v_reusejp_649_:
{
return v___x_650_;
}
}
}
v___jp_553_:
{
lean_object* v___x_554_; lean_object* v___x_555_; 
v___x_554_ = lean_obj_once(&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0___closed__3, &l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0___closed__3_once, _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0___closed__3);
v___x_555_ = l_Lean_Meta_throwTacticEx___redArg(v_name_544_, v_goal_545_, v___x_554_, v___y_548_, v___y_549_, v___y_550_, v___y_551_);
return v___x_555_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0___boxed(lean_object* v_name_653_, lean_object* v_goal_654_, lean_object* v_idx_655_, lean_object* v_expected_x3f_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_){
_start:
{
lean_object* v_res_662_; 
v_res_662_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0(v_name_653_, v_goal_654_, v_idx_655_, v_expected_x3f_656_, v___y_657_, v___y_658_, v___y_659_, v___y_660_);
lean_dec(v___y_660_);
lean_dec_ref(v___y_659_);
lean_dec(v___y_658_);
lean_dec_ref(v___y_657_);
return v_res_662_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor(lean_object* v_name_663_, lean_object* v_idx_664_, lean_object* v_expected_x3f_665_, lean_object* v_goal_666_, lean_object* v_a_667_, lean_object* v_a_668_, lean_object* v_a_669_, lean_object* v_a_670_){
_start:
{
lean_object* v___f_672_; lean_object* v___x_673_; 
lean_inc(v_goal_666_);
v___f_672_ = lean_alloc_closure((void*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0___boxed), 9, 4);
lean_closure_set(v___f_672_, 0, v_name_663_);
lean_closure_set(v___f_672_, 1, v_goal_666_);
lean_closure_set(v___f_672_, 2, v_idx_664_);
lean_closure_set(v___f_672_, 3, v_expected_x3f_665_);
v___x_673_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor_spec__0___redArg(v_goal_666_, v___f_672_, v_a_667_, v_a_668_, v_a_669_, v_a_670_);
return v___x_673_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___boxed(lean_object* v_name_674_, lean_object* v_idx_675_, lean_object* v_expected_x3f_676_, lean_object* v_goal_677_, lean_object* v_a_678_, lean_object* v_a_679_, lean_object* v_a_680_, lean_object* v_a_681_, lean_object* v_a_682_){
_start:
{
lean_object* v_res_683_; 
v_res_683_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor(v_name_674_, v_idx_675_, v_expected_x3f_676_, v_goal_677_, v_a_678_, v_a_679_, v_a_680_, v_a_681_);
lean_dec(v_a_681_);
lean_dec_ref(v_a_680_);
lean_dec(v_a_679_);
lean_dec_ref(v_a_678_);
return v_res_683_;
}
}
static lean_object* _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__1(void){
_start:
{
lean_object* v___x_685_; lean_object* v___x_686_; 
v___x_685_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__0));
v___x_686_ = l_Lean_stringToMessageData(v___x_685_);
return v___x_686_;
}
}
static lean_object* _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__8(void){
_start:
{
lean_object* v___x_696_; lean_object* v___x_697_; 
v___x_696_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__7));
v___x_697_ = l_Lean_stringToMessageData(v___x_696_);
return v___x_697_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select(lean_object* v_m_698_, lean_object* v_n_699_, lean_object* v_goal_700_, lean_object* v_a_701_, lean_object* v_a_702_, lean_object* v_a_703_, lean_object* v_a_704_){
_start:
{
lean_object* v___y_707_; lean_object* v___y_708_; lean_object* v___y_709_; lean_object* v___y_710_; lean_object* v___y_714_; lean_object* v___y_715_; lean_object* v___y_716_; lean_object* v___y_717_; lean_object* v_zero_720_; uint8_t v_isZero_721_; 
v_zero_720_ = lean_unsigned_to_nat(0u);
v_isZero_721_ = lean_nat_dec_eq(v_m_698_, v_zero_720_);
if (v_isZero_721_ == 1)
{
uint8_t v_isZero_722_; 
lean_dec(v_m_698_);
v_isZero_722_ = lean_nat_dec_eq(v_n_699_, v_zero_720_);
lean_dec(v_n_699_);
if (v_isZero_722_ == 1)
{
lean_object* v___x_723_; 
v___x_723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_723_, 0, v_goal_700_);
return v___x_723_;
}
else
{
lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; 
v___x_724_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__3));
v___x_725_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__4));
v___x_726_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor(v___x_724_, v_zero_720_, v___x_725_, v_goal_700_, v_a_701_, v_a_702_, v_a_703_, v_a_704_);
if (lean_obj_tag(v___x_726_) == 0)
{
lean_object* v_a_727_; lean_object* v___x_729_; uint8_t v_isShared_730_; uint8_t v_isSharedCheck_736_; 
v_a_727_ = lean_ctor_get(v___x_726_, 0);
v_isSharedCheck_736_ = !lean_is_exclusive(v___x_726_);
if (v_isSharedCheck_736_ == 0)
{
v___x_729_ = v___x_726_;
v_isShared_730_ = v_isSharedCheck_736_;
goto v_resetjp_728_;
}
else
{
lean_inc(v_a_727_);
lean_dec(v___x_726_);
v___x_729_ = lean_box(0);
v_isShared_730_ = v_isSharedCheck_736_;
goto v_resetjp_728_;
}
v_resetjp_728_:
{
if (lean_obj_tag(v_a_727_) == 1)
{
lean_object* v_tail_731_; 
v_tail_731_ = lean_ctor_get(v_a_727_, 1);
if (lean_obj_tag(v_tail_731_) == 0)
{
lean_object* v_head_732_; lean_object* v___x_734_; 
v_head_732_ = lean_ctor_get(v_a_727_, 0);
lean_inc(v_head_732_);
lean_dec_ref_known(v_a_727_, 2);
if (v_isShared_730_ == 0)
{
lean_ctor_set(v___x_729_, 0, v_head_732_);
v___x_734_ = v___x_729_;
goto v_reusejp_733_;
}
else
{
lean_object* v_reuseFailAlloc_735_; 
v_reuseFailAlloc_735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_735_, 0, v_head_732_);
v___x_734_ = v_reuseFailAlloc_735_;
goto v_reusejp_733_;
}
v_reusejp_733_:
{
return v___x_734_;
}
}
else
{
lean_dec_ref_known(v_a_727_, 2);
lean_del_object(v___x_729_);
v___y_707_ = v_a_701_;
v___y_708_ = v_a_702_;
v___y_709_ = v_a_703_;
v___y_710_ = v_a_704_;
goto v___jp_706_;
}
}
else
{
lean_del_object(v___x_729_);
lean_dec(v_a_727_);
v___y_707_ = v_a_701_;
v___y_708_ = v_a_702_;
v___y_709_ = v_a_703_;
v___y_710_ = v_a_704_;
goto v___jp_706_;
}
}
}
else
{
lean_object* v_a_737_; lean_object* v___x_739_; uint8_t v_isShared_740_; uint8_t v_isSharedCheck_744_; 
v_a_737_ = lean_ctor_get(v___x_726_, 0);
v_isSharedCheck_744_ = !lean_is_exclusive(v___x_726_);
if (v_isSharedCheck_744_ == 0)
{
v___x_739_ = v___x_726_;
v_isShared_740_ = v_isSharedCheck_744_;
goto v_resetjp_738_;
}
else
{
lean_inc(v_a_737_);
lean_dec(v___x_726_);
v___x_739_ = lean_box(0);
v_isShared_740_ = v_isSharedCheck_744_;
goto v_resetjp_738_;
}
v_resetjp_738_:
{
lean_object* v___x_742_; 
if (v_isShared_740_ == 0)
{
v___x_742_ = v___x_739_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_743_; 
v_reuseFailAlloc_743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_743_, 0, v_a_737_);
v___x_742_ = v_reuseFailAlloc_743_;
goto v_reusejp_741_;
}
v_reusejp_741_:
{
return v___x_742_;
}
}
}
}
}
else
{
uint8_t v_isZero_745_; 
v_isZero_745_ = lean_nat_dec_eq(v_n_699_, v_zero_720_);
if (v_isZero_745_ == 0)
{
lean_object* v_one_746_; lean_object* v_n_747_; lean_object* v_n_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; 
v_one_746_ = lean_unsigned_to_nat(1u);
v_n_747_ = lean_nat_sub(v_m_698_, v_one_746_);
lean_dec(v_m_698_);
v_n_748_ = lean_nat_sub(v_n_699_, v_one_746_);
lean_dec(v_n_699_);
v___x_749_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__6));
v___x_750_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__4));
v___x_751_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor(v___x_749_, v_one_746_, v___x_750_, v_goal_700_, v_a_701_, v_a_702_, v_a_703_, v_a_704_);
if (lean_obj_tag(v___x_751_) == 0)
{
lean_object* v_a_752_; 
v_a_752_ = lean_ctor_get(v___x_751_, 0);
lean_inc(v_a_752_);
lean_dec_ref_known(v___x_751_, 1);
if (lean_obj_tag(v_a_752_) == 1)
{
lean_object* v_tail_753_; 
v_tail_753_ = lean_ctor_get(v_a_752_, 1);
if (lean_obj_tag(v_tail_753_) == 0)
{
lean_object* v_head_754_; 
v_head_754_ = lean_ctor_get(v_a_752_, 0);
lean_inc(v_head_754_);
lean_dec_ref_known(v_a_752_, 2);
v_m_698_ = v_n_747_;
v_n_699_ = v_n_748_;
v_goal_700_ = v_head_754_;
goto _start;
}
else
{
lean_dec_ref_known(v_a_752_, 2);
lean_dec(v_n_748_);
lean_dec(v_n_747_);
v___y_714_ = v_a_701_;
v___y_715_ = v_a_702_;
v___y_716_ = v_a_703_;
v___y_717_ = v_a_704_;
goto v___jp_713_;
}
}
else
{
lean_dec(v_a_752_);
lean_dec(v_n_748_);
lean_dec(v_n_747_);
v___y_714_ = v_a_701_;
v___y_715_ = v_a_702_;
v___y_716_ = v_a_703_;
v___y_717_ = v_a_704_;
goto v___jp_713_;
}
}
else
{
lean_object* v_a_756_; lean_object* v___x_758_; uint8_t v_isShared_759_; uint8_t v_isSharedCheck_763_; 
lean_dec(v_n_748_);
lean_dec(v_n_747_);
v_a_756_ = lean_ctor_get(v___x_751_, 0);
v_isSharedCheck_763_ = !lean_is_exclusive(v___x_751_);
if (v_isSharedCheck_763_ == 0)
{
v___x_758_ = v___x_751_;
v_isShared_759_ = v_isSharedCheck_763_;
goto v_resetjp_757_;
}
else
{
lean_inc(v_a_756_);
lean_dec(v___x_751_);
v___x_758_ = lean_box(0);
v_isShared_759_ = v_isSharedCheck_763_;
goto v_resetjp_757_;
}
v_resetjp_757_:
{
lean_object* v___x_761_; 
if (v_isShared_759_ == 0)
{
v___x_761_ = v___x_758_;
goto v_reusejp_760_;
}
else
{
lean_object* v_reuseFailAlloc_762_; 
v_reuseFailAlloc_762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_762_, 0, v_a_756_);
v___x_761_ = v_reuseFailAlloc_762_;
goto v_reusejp_760_;
}
v_reusejp_760_:
{
return v___x_761_;
}
}
}
}
else
{
lean_object* v___x_764_; lean_object* v___x_765_; 
lean_dec(v_goal_700_);
lean_dec(v_n_699_);
lean_dec(v_m_698_);
v___x_764_ = lean_obj_once(&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__8, &l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__8_once, _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__8);
v___x_765_ = l_Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0___redArg(v___x_764_, v_a_701_, v_a_702_, v_a_703_, v_a_704_);
return v___x_765_;
}
}
v___jp_706_:
{
lean_object* v___x_711_; lean_object* v___x_712_; 
v___x_711_ = lean_obj_once(&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__1, &l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__1_once, _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__1);
v___x_712_ = l_Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0___redArg(v___x_711_, v___y_707_, v___y_708_, v___y_709_, v___y_710_);
return v___x_712_;
}
v___jp_713_:
{
lean_object* v___x_718_; lean_object* v___x_719_; 
v___x_718_ = lean_obj_once(&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__1, &l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__1_once, _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__1);
v___x_719_ = l_Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0___redArg(v___x_718_, v___y_714_, v___y_715_, v___y_716_, v___y_717_);
return v___x_719_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___boxed(lean_object* v_m_766_, lean_object* v_n_767_, lean_object* v_goal_768_, lean_object* v_a_769_, lean_object* v_a_770_, lean_object* v_a_771_, lean_object* v_a_772_, lean_object* v_a_773_){
_start:
{
lean_object* v_res_774_; 
v_res_774_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select(v_m_766_, v_n_767_, v_goal_768_, v_a_769_, v_a_770_, v_a_771_, v_a_772_);
lean_dec(v_a_772_);
lean_dec_ref(v_a_771_);
lean_dec(v_a_770_);
lean_dec_ref(v_a_769_);
return v_res_774_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_compactRelation___lam__0(lean_object* v___y_775_){
_start:
{
lean_inc_ref(v___y_775_);
return v___y_775_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_compactRelation___lam__0___boxed(lean_object* v___y_776_){
_start:
{
lean_object* v_res_777_; 
v_res_777_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_compactRelation___lam__0(v___y_776_);
lean_dec_ref(v___y_776_);
return v_res_777_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_compactRelation___lam__1(lean_object* v_snd_778_, lean_object* v_head_779_, lean_object* v_fst_780_, lean_object* v___y_781_){
_start:
{
lean_object* v___x_782_; lean_object* v___x_783_; 
v___x_782_ = lean_apply_1(v_snd_778_, v___y_781_);
v___x_783_ = l_Lean_Expr_replaceFVar(v___x_782_, v_head_779_, v_fst_780_);
lean_dec_ref(v___x_782_);
return v___x_783_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_compactRelation___lam__1___boxed(lean_object* v_snd_784_, lean_object* v_head_785_, lean_object* v_fst_786_, lean_object* v___y_787_){
_start:
{
lean_object* v_res_788_; 
v_res_788_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_compactRelation___lam__1(v_snd_784_, v_head_785_, v_fst_786_, v___y_787_);
lean_dec_ref(v_fst_786_);
return v_res_788_;
}
}
LEAN_EXPORT lean_object* l_List_span_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_compactRelation_spec__0(lean_object* v_head_789_, lean_object* v_a_790_, lean_object* v_a_791_){
_start:
{
if (lean_obj_tag(v_a_790_) == 0)
{
lean_object* v___x_792_; lean_object* v___x_793_; 
v___x_792_ = l_List_reverse___redArg(v_a_791_);
v___x_793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_793_, 0, v___x_792_);
lean_ctor_set(v___x_793_, 1, v_a_790_);
return v___x_793_;
}
else
{
lean_object* v_head_794_; lean_object* v_tail_795_; lean_object* v_snd_796_; uint8_t v___x_797_; 
v_head_794_ = lean_ctor_get(v_a_790_, 0);
lean_inc(v_head_794_);
v_tail_795_ = lean_ctor_get(v_a_790_, 1);
v_snd_796_ = lean_ctor_get(v_head_794_, 1);
v___x_797_ = lean_expr_eqv(v_snd_796_, v_head_789_);
if (v___x_797_ == 0)
{
lean_object* v___x_799_; uint8_t v_isShared_800_; uint8_t v_isSharedCheck_805_; 
lean_inc(v_tail_795_);
v_isSharedCheck_805_ = !lean_is_exclusive(v_a_790_);
if (v_isSharedCheck_805_ == 0)
{
lean_object* v_unused_806_; lean_object* v_unused_807_; 
v_unused_806_ = lean_ctor_get(v_a_790_, 1);
lean_dec(v_unused_806_);
v_unused_807_ = lean_ctor_get(v_a_790_, 0);
lean_dec(v_unused_807_);
v___x_799_ = v_a_790_;
v_isShared_800_ = v_isSharedCheck_805_;
goto v_resetjp_798_;
}
else
{
lean_dec(v_a_790_);
v___x_799_ = lean_box(0);
v_isShared_800_ = v_isSharedCheck_805_;
goto v_resetjp_798_;
}
v_resetjp_798_:
{
lean_object* v___x_802_; 
if (v_isShared_800_ == 0)
{
lean_ctor_set(v___x_799_, 1, v_a_791_);
v___x_802_ = v___x_799_;
goto v_reusejp_801_;
}
else
{
lean_object* v_reuseFailAlloc_804_; 
v_reuseFailAlloc_804_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_804_, 0, v_head_794_);
lean_ctor_set(v_reuseFailAlloc_804_, 1, v_a_791_);
v___x_802_ = v_reuseFailAlloc_804_;
goto v_reusejp_801_;
}
v_reusejp_801_:
{
v_a_790_ = v_tail_795_;
v_a_791_ = v___x_802_;
goto _start;
}
}
}
else
{
lean_object* v___x_809_; uint8_t v_isShared_810_; uint8_t v_isSharedCheck_815_; 
v_isSharedCheck_815_ = !lean_is_exclusive(v_head_794_);
if (v_isSharedCheck_815_ == 0)
{
lean_object* v_unused_816_; lean_object* v_unused_817_; 
v_unused_816_ = lean_ctor_get(v_head_794_, 1);
lean_dec(v_unused_816_);
v_unused_817_ = lean_ctor_get(v_head_794_, 0);
lean_dec(v_unused_817_);
v___x_809_ = v_head_794_;
v_isShared_810_ = v_isSharedCheck_815_;
goto v_resetjp_808_;
}
else
{
lean_dec(v_head_794_);
v___x_809_ = lean_box(0);
v_isShared_810_ = v_isSharedCheck_815_;
goto v_resetjp_808_;
}
v_resetjp_808_:
{
lean_object* v___x_811_; lean_object* v___x_813_; 
v___x_811_ = l_List_reverse___redArg(v_a_791_);
if (v_isShared_810_ == 0)
{
lean_ctor_set(v___x_809_, 1, v_a_790_);
lean_ctor_set(v___x_809_, 0, v___x_811_);
v___x_813_ = v___x_809_;
goto v_reusejp_812_;
}
else
{
lean_object* v_reuseFailAlloc_814_; 
v_reuseFailAlloc_814_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_814_, 0, v___x_811_);
lean_ctor_set(v_reuseFailAlloc_814_, 1, v_a_790_);
v___x_813_ = v_reuseFailAlloc_814_;
goto v_reusejp_812_;
}
v_reusejp_812_:
{
return v___x_813_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_span_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_compactRelation_spec__0___boxed(lean_object* v_head_818_, lean_object* v_a_819_, lean_object* v_a_820_){
_start:
{
lean_object* v_res_821_; 
v_res_821_ = l_List_span_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_compactRelation_spec__0(v_head_818_, v_a_819_, v_a_820_);
lean_dec_ref(v_head_818_);
return v_res_821_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_compactRelation_spec__2(lean_object* v_head_822_, lean_object* v_fst_823_, lean_object* v_a_824_, lean_object* v_a_825_){
_start:
{
if (lean_obj_tag(v_a_824_) == 0)
{
lean_object* v___x_826_; 
lean_dec_ref(v_head_822_);
v___x_826_ = l_List_reverse___redArg(v_a_825_);
return v___x_826_;
}
else
{
lean_object* v_head_827_; lean_object* v_tail_828_; lean_object* v___x_830_; uint8_t v_isShared_831_; uint8_t v_isSharedCheck_846_; 
v_head_827_ = lean_ctor_get(v_a_824_, 0);
v_tail_828_ = lean_ctor_get(v_a_824_, 1);
v_isSharedCheck_846_ = !lean_is_exclusive(v_a_824_);
if (v_isSharedCheck_846_ == 0)
{
v___x_830_ = v_a_824_;
v_isShared_831_ = v_isSharedCheck_846_;
goto v_resetjp_829_;
}
else
{
lean_inc(v_tail_828_);
lean_inc(v_head_827_);
lean_dec(v_a_824_);
v___x_830_ = lean_box(0);
v_isShared_831_ = v_isSharedCheck_846_;
goto v_resetjp_829_;
}
v_resetjp_829_:
{
lean_object* v_fst_832_; lean_object* v_snd_833_; lean_object* v___x_835_; uint8_t v_isShared_836_; uint8_t v_isSharedCheck_845_; 
v_fst_832_ = lean_ctor_get(v_head_827_, 0);
v_snd_833_ = lean_ctor_get(v_head_827_, 1);
v_isSharedCheck_845_ = !lean_is_exclusive(v_head_827_);
if (v_isSharedCheck_845_ == 0)
{
v___x_835_ = v_head_827_;
v_isShared_836_ = v_isSharedCheck_845_;
goto v_resetjp_834_;
}
else
{
lean_inc(v_snd_833_);
lean_inc(v_fst_832_);
lean_dec(v_head_827_);
v___x_835_ = lean_box(0);
v_isShared_836_ = v_isSharedCheck_845_;
goto v_resetjp_834_;
}
v_resetjp_834_:
{
lean_object* v___x_837_; lean_object* v___x_839_; 
lean_inc_ref(v_head_822_);
v___x_837_ = l_Lean_Expr_replaceFVar(v_snd_833_, v_head_822_, v_fst_823_);
lean_dec(v_snd_833_);
if (v_isShared_836_ == 0)
{
lean_ctor_set(v___x_835_, 1, v___x_837_);
v___x_839_ = v___x_835_;
goto v_reusejp_838_;
}
else
{
lean_object* v_reuseFailAlloc_844_; 
v_reuseFailAlloc_844_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_844_, 0, v_fst_832_);
lean_ctor_set(v_reuseFailAlloc_844_, 1, v___x_837_);
v___x_839_ = v_reuseFailAlloc_844_;
goto v_reusejp_838_;
}
v_reusejp_838_:
{
lean_object* v___x_841_; 
if (v_isShared_831_ == 0)
{
lean_ctor_set(v___x_830_, 1, v_a_825_);
lean_ctor_set(v___x_830_, 0, v___x_839_);
v___x_841_ = v___x_830_;
goto v_reusejp_840_;
}
else
{
lean_object* v_reuseFailAlloc_843_; 
v_reuseFailAlloc_843_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_843_, 0, v___x_839_);
lean_ctor_set(v_reuseFailAlloc_843_, 1, v_a_825_);
v___x_841_ = v_reuseFailAlloc_843_;
goto v_reusejp_840_;
}
v_reusejp_840_:
{
v_a_824_ = v_tail_828_;
v_a_825_ = v___x_841_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_compactRelation_spec__2___boxed(lean_object* v_head_847_, lean_object* v_fst_848_, lean_object* v_a_849_, lean_object* v_a_850_){
_start:
{
lean_object* v_res_851_; 
v_res_851_ = l_List_mapTR_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_compactRelation_spec__2(v_head_847_, v_fst_848_, v_a_849_, v_a_850_);
lean_dec_ref(v_fst_848_);
return v_res_851_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_compactRelation_spec__1(lean_object* v_head_852_, lean_object* v_fst_853_, lean_object* v_a_854_, lean_object* v_a_855_){
_start:
{
if (lean_obj_tag(v_a_854_) == 0)
{
lean_object* v___x_856_; 
lean_dec_ref(v_head_852_);
v___x_856_ = l_List_reverse___redArg(v_a_855_);
return v___x_856_;
}
else
{
lean_object* v_head_857_; lean_object* v_tail_858_; lean_object* v___x_860_; uint8_t v_isShared_861_; uint8_t v_isSharedCheck_867_; 
v_head_857_ = lean_ctor_get(v_a_854_, 0);
v_tail_858_ = lean_ctor_get(v_a_854_, 1);
v_isSharedCheck_867_ = !lean_is_exclusive(v_a_854_);
if (v_isSharedCheck_867_ == 0)
{
v___x_860_ = v_a_854_;
v_isShared_861_ = v_isSharedCheck_867_;
goto v_resetjp_859_;
}
else
{
lean_inc(v_tail_858_);
lean_inc(v_head_857_);
lean_dec(v_a_854_);
v___x_860_ = lean_box(0);
v_isShared_861_ = v_isSharedCheck_867_;
goto v_resetjp_859_;
}
v_resetjp_859_:
{
lean_object* v___x_862_; lean_object* v___x_864_; 
lean_inc_ref(v_head_852_);
v___x_862_ = l_Lean_Expr_replaceFVar(v_head_857_, v_head_852_, v_fst_853_);
lean_dec(v_head_857_);
if (v_isShared_861_ == 0)
{
lean_ctor_set(v___x_860_, 1, v_a_855_);
lean_ctor_set(v___x_860_, 0, v___x_862_);
v___x_864_ = v___x_860_;
goto v_reusejp_863_;
}
else
{
lean_object* v_reuseFailAlloc_866_; 
v_reuseFailAlloc_866_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_866_, 0, v___x_862_);
lean_ctor_set(v_reuseFailAlloc_866_, 1, v_a_855_);
v___x_864_ = v_reuseFailAlloc_866_;
goto v_reusejp_863_;
}
v_reusejp_863_:
{
v_a_854_ = v_tail_858_;
v_a_855_ = v___x_864_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_compactRelation_spec__1___boxed(lean_object* v_head_868_, lean_object* v_fst_869_, lean_object* v_a_870_, lean_object* v_a_871_){
_start:
{
lean_object* v_res_872_; 
v_res_872_ = l_List_mapTR_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_compactRelation_spec__1(v_head_868_, v_fst_869_, v_a_870_, v_a_871_);
lean_dec_ref(v_fst_869_);
return v_res_872_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_compactRelation(lean_object* v_x_874_, lean_object* v_x_875_){
_start:
{
if (lean_obj_tag(v_x_874_) == 0)
{
lean_object* v___f_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; 
v___f_876_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_compactRelation___closed__0));
v___x_877_ = lean_box(0);
v___x_878_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_878_, 0, v_x_875_);
lean_ctor_set(v___x_878_, 1, v___f_876_);
v___x_879_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_879_, 0, v___x_877_);
lean_ctor_set(v___x_879_, 1, v___x_878_);
return v___x_879_;
}
else
{
lean_object* v_head_880_; lean_object* v_tail_881_; lean_object* v___x_883_; uint8_t v_isShared_884_; uint8_t v_isSharedCheck_938_; 
v_head_880_ = lean_ctor_get(v_x_874_, 0);
v_tail_881_ = lean_ctor_get(v_x_874_, 1);
v_isSharedCheck_938_ = !lean_is_exclusive(v_x_874_);
if (v_isSharedCheck_938_ == 0)
{
v___x_883_ = v_x_874_;
v_isShared_884_ = v_isSharedCheck_938_;
goto v_resetjp_882_;
}
else
{
lean_inc(v_tail_881_);
lean_inc(v_head_880_);
lean_dec(v_x_874_);
v___x_883_ = lean_box(0);
v_isShared_884_ = v_isSharedCheck_938_;
goto v_resetjp_882_;
}
v_resetjp_882_:
{
lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v_snd_887_; 
v___x_885_ = lean_box(0);
lean_inc(v_x_875_);
v___x_886_ = l_List_span_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_compactRelation_spec__0(v_head_880_, v_x_875_, v___x_885_);
v_snd_887_ = lean_ctor_get(v___x_886_, 1);
lean_inc(v_snd_887_);
if (lean_obj_tag(v_snd_887_) == 0)
{
lean_object* v___x_888_; lean_object* v_fst_889_; lean_object* v_snd_890_; lean_object* v___x_892_; uint8_t v_isShared_893_; uint8_t v_isSharedCheck_901_; 
lean_dec_ref(v___x_886_);
v___x_888_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_compactRelation(v_tail_881_, v_x_875_);
v_fst_889_ = lean_ctor_get(v___x_888_, 0);
v_snd_890_ = lean_ctor_get(v___x_888_, 1);
v_isSharedCheck_901_ = !lean_is_exclusive(v___x_888_);
if (v_isSharedCheck_901_ == 0)
{
v___x_892_ = v___x_888_;
v_isShared_893_ = v_isSharedCheck_901_;
goto v_resetjp_891_;
}
else
{
lean_inc(v_snd_890_);
lean_inc(v_fst_889_);
lean_dec(v___x_888_);
v___x_892_ = lean_box(0);
v_isShared_893_ = v_isSharedCheck_901_;
goto v_resetjp_891_;
}
v_resetjp_891_:
{
lean_object* v___x_894_; lean_object* v___x_896_; 
v___x_894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_894_, 0, v_head_880_);
if (v_isShared_884_ == 0)
{
lean_ctor_set(v___x_883_, 1, v_fst_889_);
lean_ctor_set(v___x_883_, 0, v___x_894_);
v___x_896_ = v___x_883_;
goto v_reusejp_895_;
}
else
{
lean_object* v_reuseFailAlloc_900_; 
v_reuseFailAlloc_900_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_900_, 0, v___x_894_);
lean_ctor_set(v_reuseFailAlloc_900_, 1, v_fst_889_);
v___x_896_ = v_reuseFailAlloc_900_;
goto v_reusejp_895_;
}
v_reusejp_895_:
{
lean_object* v___x_898_; 
if (v_isShared_893_ == 0)
{
lean_ctor_set(v___x_892_, 0, v___x_896_);
v___x_898_ = v___x_892_;
goto v_reusejp_897_;
}
else
{
lean_object* v_reuseFailAlloc_899_; 
v_reuseFailAlloc_899_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_899_, 0, v___x_896_);
lean_ctor_set(v_reuseFailAlloc_899_, 1, v_snd_890_);
v___x_898_ = v_reuseFailAlloc_899_;
goto v_reusejp_897_;
}
v_reusejp_897_:
{
return v___x_898_;
}
}
}
}
else
{
lean_object* v_head_902_; lean_object* v_fst_903_; lean_object* v_tail_904_; lean_object* v___x_906_; uint8_t v_isShared_907_; uint8_t v_isSharedCheck_936_; 
lean_del_object(v___x_883_);
lean_dec(v_x_875_);
v_head_902_ = lean_ctor_get(v_snd_887_, 0);
lean_inc(v_head_902_);
v_fst_903_ = lean_ctor_get(v___x_886_, 0);
lean_inc(v_fst_903_);
lean_dec_ref(v___x_886_);
v_tail_904_ = lean_ctor_get(v_snd_887_, 1);
v_isSharedCheck_936_ = !lean_is_exclusive(v_snd_887_);
if (v_isSharedCheck_936_ == 0)
{
lean_object* v_unused_937_; 
v_unused_937_ = lean_ctor_get(v_snd_887_, 0);
lean_dec(v_unused_937_);
v___x_906_ = v_snd_887_;
v_isShared_907_ = v_isSharedCheck_936_;
goto v_resetjp_905_;
}
else
{
lean_inc(v_tail_904_);
lean_dec(v_snd_887_);
v___x_906_ = lean_box(0);
v_isShared_907_ = v_isSharedCheck_936_;
goto v_resetjp_905_;
}
v_resetjp_905_:
{
lean_object* v_fst_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v_snd_913_; lean_object* v_fst_914_; lean_object* v___x_916_; uint8_t v_isShared_917_; uint8_t v_isSharedCheck_935_; 
v_fst_908_ = lean_ctor_get(v_head_902_, 0);
lean_inc(v_fst_908_);
lean_dec(v_head_902_);
lean_inc_n(v_head_880_, 2);
v___x_909_ = l_List_mapTR_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_compactRelation_spec__1(v_head_880_, v_fst_908_, v_tail_881_, v___x_885_);
v___x_910_ = l_List_appendTR___redArg(v_fst_903_, v_tail_904_);
v___x_911_ = l_List_mapTR_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_compactRelation_spec__2(v_head_880_, v_fst_908_, v___x_910_, v___x_885_);
v___x_912_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_compactRelation(v___x_909_, v___x_911_);
v_snd_913_ = lean_ctor_get(v___x_912_, 1);
v_fst_914_ = lean_ctor_get(v___x_912_, 0);
v_isSharedCheck_935_ = !lean_is_exclusive(v___x_912_);
if (v_isSharedCheck_935_ == 0)
{
v___x_916_ = v___x_912_;
v_isShared_917_ = v_isSharedCheck_935_;
goto v_resetjp_915_;
}
else
{
lean_inc(v_snd_913_);
lean_inc(v_fst_914_);
lean_dec(v___x_912_);
v___x_916_ = lean_box(0);
v_isShared_917_ = v_isSharedCheck_935_;
goto v_resetjp_915_;
}
v_resetjp_915_:
{
lean_object* v_fst_918_; lean_object* v_snd_919_; lean_object* v___x_921_; uint8_t v_isShared_922_; uint8_t v_isSharedCheck_934_; 
v_fst_918_ = lean_ctor_get(v_snd_913_, 0);
v_snd_919_ = lean_ctor_get(v_snd_913_, 1);
v_isSharedCheck_934_ = !lean_is_exclusive(v_snd_913_);
if (v_isSharedCheck_934_ == 0)
{
v___x_921_ = v_snd_913_;
v_isShared_922_ = v_isSharedCheck_934_;
goto v_resetjp_920_;
}
else
{
lean_inc(v_snd_919_);
lean_inc(v_fst_918_);
lean_dec(v_snd_913_);
v___x_921_ = lean_box(0);
v_isShared_922_ = v_isSharedCheck_934_;
goto v_resetjp_920_;
}
v_resetjp_920_:
{
lean_object* v___f_923_; lean_object* v___x_924_; lean_object* v___x_926_; 
v___f_923_ = lean_alloc_closure((void*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_compactRelation___lam__1___boxed), 4, 3);
lean_closure_set(v___f_923_, 0, v_snd_919_);
lean_closure_set(v___f_923_, 1, v_head_880_);
lean_closure_set(v___f_923_, 2, v_fst_908_);
v___x_924_ = lean_box(0);
if (v_isShared_907_ == 0)
{
lean_ctor_set(v___x_906_, 1, v_fst_914_);
lean_ctor_set(v___x_906_, 0, v___x_924_);
v___x_926_ = v___x_906_;
goto v_reusejp_925_;
}
else
{
lean_object* v_reuseFailAlloc_933_; 
v_reuseFailAlloc_933_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_933_, 0, v___x_924_);
lean_ctor_set(v_reuseFailAlloc_933_, 1, v_fst_914_);
v___x_926_ = v_reuseFailAlloc_933_;
goto v_reusejp_925_;
}
v_reusejp_925_:
{
lean_object* v___x_928_; 
if (v_isShared_922_ == 0)
{
lean_ctor_set(v___x_921_, 1, v___f_923_);
v___x_928_ = v___x_921_;
goto v_reusejp_927_;
}
else
{
lean_object* v_reuseFailAlloc_932_; 
v_reuseFailAlloc_932_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_932_, 0, v_fst_918_);
lean_ctor_set(v_reuseFailAlloc_932_, 1, v___f_923_);
v___x_928_ = v_reuseFailAlloc_932_;
goto v_reusejp_927_;
}
v_reusejp_927_:
{
lean_object* v___x_930_; 
if (v_isShared_917_ == 0)
{
lean_ctor_set(v___x_916_, 1, v___x_928_);
lean_ctor_set(v___x_916_, 0, v___x_926_);
v___x_930_ = v___x_916_;
goto v_reusejp_929_;
}
else
{
lean_object* v_reuseFailAlloc_931_; 
v_reuseFailAlloc_931_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_931_, 0, v___x_926_);
lean_ctor_set(v_reuseFailAlloc_931_, 1, v___x_928_);
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
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_updateLambdaBinderInfoD_x21_spec__0(lean_object* v_msg_939_){
_start:
{
lean_object* v___x_940_; lean_object* v___x_941_; 
v___x_940_ = l_Lean_instInhabitedExpr;
v___x_941_ = lean_panic_fn_borrowed(v___x_940_, v_msg_939_);
return v___x_941_;
}
}
static lean_object* _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_updateLambdaBinderInfoD_x21___closed__3(void){
_start:
{
lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; 
v___x_945_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_updateLambdaBinderInfoD_x21___closed__2));
v___x_946_ = lean_unsigned_to_nat(19u);
v___x_947_ = lean_unsigned_to_nat(96u);
v___x_948_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_updateLambdaBinderInfoD_x21___closed__1));
v___x_949_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_updateLambdaBinderInfoD_x21___closed__0));
v___x_950_ = l_mkPanicMessageWithDecl(v___x_949_, v___x_948_, v___x_947_, v___x_946_, v___x_945_);
return v___x_950_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_updateLambdaBinderInfoD_x21(lean_object* v_e_951_){
_start:
{
if (lean_obj_tag(v_e_951_) == 6)
{
lean_object* v_binderName_952_; lean_object* v_binderType_953_; lean_object* v_body_954_; uint8_t v___x_955_; lean_object* v___x_956_; 
v_binderName_952_ = lean_ctor_get(v_e_951_, 0);
lean_inc(v_binderName_952_);
v_binderType_953_ = lean_ctor_get(v_e_951_, 1);
lean_inc_ref(v_binderType_953_);
v_body_954_ = lean_ctor_get(v_e_951_, 2);
lean_inc_ref(v_body_954_);
lean_dec_ref_known(v_e_951_, 3);
v___x_955_ = 0;
v___x_956_ = l_Lean_Expr_lam___override(v_binderName_952_, v_binderType_953_, v_body_954_, v___x_955_);
return v___x_956_;
}
else
{
lean_object* v___x_957_; lean_object* v___x_958_; 
lean_dec_ref(v_e_951_);
v___x_957_ = lean_obj_once(&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_updateLambdaBinderInfoD_x21___closed__3, &l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_updateLambdaBinderInfoD_x21___closed__3_once, _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_updateLambdaBinderInfoD_x21___closed__3);
v___x_958_ = l_panic___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_updateLambdaBinderInfoD_x21_spec__0(v___x_957_);
return v___x_958_;
}
}
}
static lean_object* _init_l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkExistsList_spec__0___closed__4(void){
_start:
{
lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; 
v___x_965_ = lean_box(0);
v___x_966_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkExistsList_spec__0___closed__3));
v___x_967_ = l_Lean_mkConst(v___x_966_, v___x_965_);
return v___x_967_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkExistsList_spec__0(lean_object* v_x_968_, lean_object* v_x_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_){
_start:
{
if (lean_obj_tag(v_x_969_) == 0)
{
lean_object* v___x_975_; 
v___x_975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_975_, 0, v_x_968_);
return v___x_975_;
}
else
{
lean_object* v_head_976_; lean_object* v_tail_977_; lean_object* v___x_979_; uint8_t v_isShared_980_; uint8_t v_isSharedCheck_1016_; 
v_head_976_ = lean_ctor_get(v_x_969_, 0);
v_tail_977_ = lean_ctor_get(v_x_969_, 1);
v_isSharedCheck_1016_ = !lean_is_exclusive(v_x_969_);
if (v_isSharedCheck_1016_ == 0)
{
v___x_979_ = v_x_969_;
v_isShared_980_ = v_isSharedCheck_1016_;
goto v_resetjp_978_;
}
else
{
lean_inc(v_tail_977_);
lean_inc(v_head_976_);
lean_dec(v_x_969_);
v___x_979_ = lean_box(0);
v_isShared_980_ = v_isSharedCheck_1016_;
goto v_resetjp_978_;
}
v_resetjp_978_:
{
lean_object* v___y_982_; lean_object* v___x_985_; 
lean_inc(v___y_973_);
lean_inc_ref(v___y_972_);
lean_inc(v___y_971_);
lean_inc_ref(v___y_970_);
lean_inc(v_head_976_);
v___x_985_ = lean_infer_type(v_head_976_, v___y_970_, v___y_971_, v___y_972_, v___y_973_);
if (lean_obj_tag(v___x_985_) == 0)
{
lean_object* v_a_986_; lean_object* v___x_987_; 
v_a_986_ = lean_ctor_get(v___x_985_, 0);
lean_inc_n(v_a_986_, 2);
lean_dec_ref_known(v___x_985_, 1);
lean_inc(v___y_973_);
lean_inc_ref(v___y_972_);
lean_inc(v___y_971_);
lean_inc_ref(v___y_970_);
v___x_987_ = lean_infer_type(v_a_986_, v___y_970_, v___y_971_, v___y_972_, v___y_973_);
if (lean_obj_tag(v___x_987_) == 0)
{
lean_object* v_a_988_; lean_object* v___x_989_; uint8_t v___y_1009_; uint8_t v___x_1013_; 
v_a_988_ = lean_ctor_get(v___x_987_, 0);
lean_inc(v_a_988_);
lean_dec_ref_known(v___x_987_, 1);
v___x_989_ = l_Lean_Expr_sortLevel_x21(v_a_988_);
lean_dec(v_a_988_);
lean_inc(v_head_976_);
v___x_1013_ = l_Lean_Expr_occurs(v_head_976_, v_x_968_);
if (v___x_1013_ == 0)
{
lean_object* v___x_1014_; uint8_t v___x_1015_; 
v___x_1014_ = lean_box(0);
v___x_1015_ = lean_level_eq(v___x_989_, v___x_1014_);
if (v___x_1015_ == 0)
{
goto v___jp_990_;
}
else
{
v___y_1009_ = v___x_1013_;
goto v___jp_1008_;
}
}
else
{
v___y_1009_ = v___x_1013_;
goto v___jp_1008_;
}
v___jp_990_:
{
uint8_t v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; uint8_t v___x_995_; uint8_t v___x_996_; lean_object* v___x_997_; 
v___x_991_ = 1;
v___x_992_ = lean_unsigned_to_nat(1u);
v___x_993_ = lean_mk_empty_array_with_capacity(v___x_992_);
v___x_994_ = lean_array_push(v___x_993_, v_head_976_);
v___x_995_ = 0;
v___x_996_ = 1;
v___x_997_ = l_Lean_Meta_mkLambdaFVars(v___x_994_, v_x_968_, v___x_995_, v___x_991_, v___x_995_, v___x_991_, v___x_996_, v___y_970_, v___y_971_, v___y_972_, v___y_973_);
lean_dec_ref(v___x_994_);
if (lean_obj_tag(v___x_997_) == 0)
{
lean_object* v_a_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1002_; 
v_a_998_ = lean_ctor_get(v___x_997_, 0);
lean_inc(v_a_998_);
lean_dec_ref_known(v___x_997_, 1);
v___x_999_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkExistsList_spec__0___closed__1));
v___x_1000_ = lean_box(0);
if (v_isShared_980_ == 0)
{
lean_ctor_set(v___x_979_, 1, v___x_1000_);
lean_ctor_set(v___x_979_, 0, v___x_989_);
v___x_1002_ = v___x_979_;
goto v_reusejp_1001_;
}
else
{
lean_object* v_reuseFailAlloc_1007_; 
v_reuseFailAlloc_1007_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1007_, 0, v___x_989_);
lean_ctor_set(v_reuseFailAlloc_1007_, 1, v___x_1000_);
v___x_1002_ = v_reuseFailAlloc_1007_;
goto v_reusejp_1001_;
}
v_reusejp_1001_:
{
lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; 
v___x_1003_ = l_Lean_Expr_const___override(v___x_999_, v___x_1002_);
v___x_1004_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_updateLambdaBinderInfoD_x21(v_a_998_);
v___x_1005_ = l_Lean_mkAppB(v___x_1003_, v_a_986_, v___x_1004_);
v_x_968_ = v___x_1005_;
v_x_969_ = v_tail_977_;
goto _start;
}
}
else
{
lean_dec(v___x_989_);
lean_dec(v_a_986_);
lean_del_object(v___x_979_);
v___y_982_ = v___x_997_;
goto v___jp_981_;
}
}
v___jp_1008_:
{
if (v___y_1009_ == 0)
{
lean_object* v___x_1010_; lean_object* v___x_1011_; 
lean_dec(v___x_989_);
lean_del_object(v___x_979_);
lean_dec(v_head_976_);
v___x_1010_ = lean_obj_once(&l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkExistsList_spec__0___closed__4, &l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkExistsList_spec__0___closed__4_once, _init_l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkExistsList_spec__0___closed__4);
v___x_1011_ = l_Lean_mkAppB(v___x_1010_, v_a_986_, v_x_968_);
v_x_968_ = v___x_1011_;
v_x_969_ = v_tail_977_;
goto _start;
}
else
{
goto v___jp_990_;
}
}
}
else
{
lean_dec(v_a_986_);
lean_del_object(v___x_979_);
lean_dec(v_head_976_);
lean_dec_ref(v_x_968_);
v___y_982_ = v___x_987_;
goto v___jp_981_;
}
}
else
{
lean_del_object(v___x_979_);
lean_dec(v_head_976_);
lean_dec_ref(v_x_968_);
v___y_982_ = v___x_985_;
goto v___jp_981_;
}
v___jp_981_:
{
if (lean_obj_tag(v___y_982_) == 0)
{
lean_object* v_a_983_; 
v_a_983_ = lean_ctor_get(v___y_982_, 0);
lean_inc(v_a_983_);
lean_dec_ref_known(v___y_982_, 1);
v_x_968_ = v_a_983_;
v_x_969_ = v_tail_977_;
goto _start;
}
else
{
lean_dec(v_tail_977_);
return v___y_982_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkExistsList_spec__0___boxed(lean_object* v_x_1017_, lean_object* v_x_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_){
_start:
{
lean_object* v_res_1024_; 
v_res_1024_ = l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkExistsList_spec__0(v_x_1017_, v_x_1018_, v___y_1019_, v___y_1020_, v___y_1021_, v___y_1022_);
lean_dec(v___y_1022_);
lean_dec_ref(v___y_1021_);
lean_dec(v___y_1020_);
lean_dec_ref(v___y_1019_);
return v_res_1024_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkExistsList(lean_object* v_args_1025_, lean_object* v_inner_1026_, lean_object* v_a_1027_, lean_object* v_a_1028_, lean_object* v_a_1029_, lean_object* v_a_1030_){
_start:
{
lean_object* v___x_1032_; lean_object* v___x_1033_; 
v___x_1032_ = l_List_reverse___redArg(v_args_1025_);
v___x_1033_ = l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkExistsList_spec__0(v_inner_1026_, v___x_1032_, v_a_1027_, v_a_1028_, v_a_1029_, v_a_1030_);
return v___x_1033_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkExistsList___boxed(lean_object* v_args_1034_, lean_object* v_inner_1035_, lean_object* v_a_1036_, lean_object* v_a_1037_, lean_object* v_a_1038_, lean_object* v_a_1039_, lean_object* v_a_1040_){
_start:
{
lean_object* v_res_1041_; 
v_res_1041_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkExistsList(v_args_1034_, v_inner_1035_, v_a_1036_, v_a_1037_, v_a_1038_, v_a_1039_);
lean_dec(v_a_1039_);
lean_dec_ref(v_a_1038_);
lean_dec(v_a_1037_);
lean_dec_ref(v_a_1036_);
return v_res_1041_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkOpList(lean_object* v_op_1042_, lean_object* v_empty_1043_, lean_object* v_x_1044_){
_start:
{
if (lean_obj_tag(v_x_1044_) == 0)
{
lean_dec_ref(v_op_1042_);
lean_inc_ref(v_empty_1043_);
return v_empty_1043_;
}
else
{
lean_object* v_tail_1045_; 
v_tail_1045_ = lean_ctor_get(v_x_1044_, 1);
if (lean_obj_tag(v_tail_1045_) == 0)
{
lean_object* v_head_1046_; 
lean_dec_ref(v_op_1042_);
v_head_1046_ = lean_ctor_get(v_x_1044_, 0);
lean_inc(v_head_1046_);
lean_dec_ref_known(v_x_1044_, 2);
return v_head_1046_;
}
else
{
lean_object* v_head_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; 
lean_inc(v_tail_1045_);
v_head_1047_ = lean_ctor_get(v_x_1044_, 0);
lean_inc(v_head_1047_);
lean_dec_ref_known(v_x_1044_, 2);
lean_inc_ref(v_op_1042_);
v___x_1048_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkOpList(v_op_1042_, v_empty_1043_, v_tail_1045_);
v___x_1049_ = l_Lean_mkAppB(v_op_1042_, v_head_1047_, v___x_1048_);
return v___x_1049_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkOpList___boxed(lean_object* v_op_1050_, lean_object* v_empty_1051_, lean_object* v_x_1052_){
_start:
{
lean_object* v_res_1053_; 
v_res_1053_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkOpList(v_op_1050_, v_empty_1051_, v_x_1052_);
lean_dec_ref(v_empty_1051_);
return v_res_1053_;
}
}
static lean_object* _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkAndList___closed__2(void){
_start:
{
lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; 
v___x_1057_ = lean_box(0);
v___x_1058_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkAndList___closed__1));
v___x_1059_ = l_Lean_mkConst(v___x_1058_, v___x_1057_);
return v___x_1059_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkAndList(lean_object* v_a_1060_){
_start:
{
lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; 
v___x_1061_ = lean_obj_once(&l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkExistsList_spec__0___closed__4, &l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkExistsList_spec__0___closed__4_once, _init_l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkExistsList_spec__0___closed__4);
v___x_1062_ = lean_obj_once(&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkAndList___closed__2, &l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkAndList___closed__2_once, _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkAndList___closed__2);
v___x_1063_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkOpList(v___x_1061_, v___x_1062_, v_a_1060_);
return v___x_1063_;
}
}
static lean_object* _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkOrList___closed__2(void){
_start:
{
lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; 
v___x_1067_ = lean_box(0);
v___x_1068_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkOrList___closed__1));
v___x_1069_ = l_Lean_mkConst(v___x_1068_, v___x_1067_);
return v___x_1069_;
}
}
static lean_object* _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkOrList___closed__5(void){
_start:
{
lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; 
v___x_1073_ = lean_box(0);
v___x_1074_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkOrList___closed__4));
v___x_1075_ = l_Lean_mkConst(v___x_1074_, v___x_1073_);
return v___x_1075_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkOrList(lean_object* v_a_1076_){
_start:
{
lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; 
v___x_1077_ = lean_obj_once(&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkOrList___closed__2, &l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkOrList___closed__2_once, _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkOrList___closed__2);
v___x_1078_ = lean_obj_once(&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkOrList___closed__5, &l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkOrList___closed__5_once, _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkOrList___closed__5);
v___x_1079_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkOpList(v___x_1077_, v___x_1078_, v_a_1076_);
return v___x_1079_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_List_init___redArg(lean_object* v_x_1080_){
_start:
{
if (lean_obj_tag(v_x_1080_) == 0)
{
return v_x_1080_;
}
else
{
lean_object* v_tail_1081_; 
v_tail_1081_ = lean_ctor_get(v_x_1080_, 1);
lean_inc(v_tail_1081_);
if (lean_obj_tag(v_tail_1081_) == 0)
{
lean_dec_ref_known(v_x_1080_, 2);
return v_tail_1081_;
}
else
{
lean_object* v_head_1082_; lean_object* v___x_1084_; uint8_t v_isShared_1085_; uint8_t v_isSharedCheck_1090_; 
v_head_1082_ = lean_ctor_get(v_x_1080_, 0);
v_isSharedCheck_1090_ = !lean_is_exclusive(v_x_1080_);
if (v_isSharedCheck_1090_ == 0)
{
lean_object* v_unused_1091_; 
v_unused_1091_ = lean_ctor_get(v_x_1080_, 1);
lean_dec(v_unused_1091_);
v___x_1084_ = v_x_1080_;
v_isShared_1085_ = v_isSharedCheck_1090_;
goto v_resetjp_1083_;
}
else
{
lean_inc(v_head_1082_);
lean_dec(v_x_1080_);
v___x_1084_ = lean_box(0);
v_isShared_1085_ = v_isSharedCheck_1090_;
goto v_resetjp_1083_;
}
v_resetjp_1083_:
{
lean_object* v___x_1086_; lean_object* v___x_1088_; 
v___x_1086_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_List_init___redArg(v_tail_1081_);
if (v_isShared_1085_ == 0)
{
lean_ctor_set(v___x_1084_, 1, v___x_1086_);
v___x_1088_ = v___x_1084_;
goto v_reusejp_1087_;
}
else
{
lean_object* v_reuseFailAlloc_1089_; 
v_reuseFailAlloc_1089_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1089_, 0, v_head_1082_);
lean_ctor_set(v_reuseFailAlloc_1089_, 1, v___x_1086_);
v___x_1088_ = v_reuseFailAlloc_1089_;
goto v_reusejp_1087_;
}
v_reusejp_1087_:
{
return v___x_1088_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_List_init(lean_object* v_00_u03b1_1092_, lean_object* v_x_1093_){
_start:
{
lean_object* v___x_1094_; 
v___x_1094_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_List_init___redArg(v_x_1093_);
return v___x_1094_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__4___redArg___lam__0(lean_object* v_k_1095_, lean_object* v_b_1096_, lean_object* v_c_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_){
_start:
{
lean_object* v___x_1103_; 
lean_inc(v___y_1101_);
lean_inc_ref(v___y_1100_);
lean_inc(v___y_1099_);
lean_inc_ref(v___y_1098_);
v___x_1103_ = lean_apply_7(v_k_1095_, v_b_1096_, v_c_1097_, v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_, lean_box(0));
return v___x_1103_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__4___redArg___lam__0___boxed(lean_object* v_k_1104_, lean_object* v_b_1105_, lean_object* v_c_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_){
_start:
{
lean_object* v_res_1112_; 
v_res_1112_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__4___redArg___lam__0(v_k_1104_, v_b_1105_, v_c_1106_, v___y_1107_, v___y_1108_, v___y_1109_, v___y_1110_);
lean_dec(v___y_1110_);
lean_dec_ref(v___y_1109_);
lean_dec(v___y_1108_);
lean_dec_ref(v___y_1107_);
return v_res_1112_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__4___redArg(lean_object* v_type_1113_, lean_object* v_maxFVars_x3f_1114_, lean_object* v_k_1115_, uint8_t v_cleanupAnnotations_1116_, uint8_t v_whnfType_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_){
_start:
{
lean_object* v___f_1123_; lean_object* v___x_1124_; 
v___f_1123_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__4___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1123_, 0, v_k_1115_);
v___x_1124_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_1113_, v_maxFVars_x3f_1114_, v___f_1123_, v_cleanupAnnotations_1116_, v_whnfType_1117_, v___y_1118_, v___y_1119_, v___y_1120_, v___y_1121_);
if (lean_obj_tag(v___x_1124_) == 0)
{
lean_object* v_a_1125_; lean_object* v___x_1127_; uint8_t v_isShared_1128_; uint8_t v_isSharedCheck_1132_; 
v_a_1125_ = lean_ctor_get(v___x_1124_, 0);
v_isSharedCheck_1132_ = !lean_is_exclusive(v___x_1124_);
if (v_isSharedCheck_1132_ == 0)
{
v___x_1127_ = v___x_1124_;
v_isShared_1128_ = v_isSharedCheck_1132_;
goto v_resetjp_1126_;
}
else
{
lean_inc(v_a_1125_);
lean_dec(v___x_1124_);
v___x_1127_ = lean_box(0);
v_isShared_1128_ = v_isSharedCheck_1132_;
goto v_resetjp_1126_;
}
v_resetjp_1126_:
{
lean_object* v___x_1130_; 
if (v_isShared_1128_ == 0)
{
v___x_1130_ = v___x_1127_;
goto v_reusejp_1129_;
}
else
{
lean_object* v_reuseFailAlloc_1131_; 
v_reuseFailAlloc_1131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1131_, 0, v_a_1125_);
v___x_1130_ = v_reuseFailAlloc_1131_;
goto v_reusejp_1129_;
}
v_reusejp_1129_:
{
return v___x_1130_;
}
}
}
else
{
lean_object* v_a_1133_; lean_object* v___x_1135_; uint8_t v_isShared_1136_; uint8_t v_isSharedCheck_1140_; 
v_a_1133_ = lean_ctor_get(v___x_1124_, 0);
v_isSharedCheck_1140_ = !lean_is_exclusive(v___x_1124_);
if (v_isSharedCheck_1140_ == 0)
{
v___x_1135_ = v___x_1124_;
v_isShared_1136_ = v_isSharedCheck_1140_;
goto v_resetjp_1134_;
}
else
{
lean_inc(v_a_1133_);
lean_dec(v___x_1124_);
v___x_1135_ = lean_box(0);
v_isShared_1136_ = v_isSharedCheck_1140_;
goto v_resetjp_1134_;
}
v_resetjp_1134_:
{
lean_object* v___x_1138_; 
if (v_isShared_1136_ == 0)
{
v___x_1138_ = v___x_1135_;
goto v_reusejp_1137_;
}
else
{
lean_object* v_reuseFailAlloc_1139_; 
v_reuseFailAlloc_1139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1139_, 0, v_a_1133_);
v___x_1138_ = v_reuseFailAlloc_1139_;
goto v_reusejp_1137_;
}
v_reusejp_1137_:
{
return v___x_1138_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__4___redArg___boxed(lean_object* v_type_1141_, lean_object* v_maxFVars_x3f_1142_, lean_object* v_k_1143_, lean_object* v_cleanupAnnotations_1144_, lean_object* v_whnfType_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1151_; uint8_t v_whnfType_boxed_1152_; lean_object* v_res_1153_; 
v_cleanupAnnotations_boxed_1151_ = lean_unbox(v_cleanupAnnotations_1144_);
v_whnfType_boxed_1152_ = lean_unbox(v_whnfType_1145_);
v_res_1153_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__4___redArg(v_type_1141_, v_maxFVars_x3f_1142_, v_k_1143_, v_cleanupAnnotations_boxed_1151_, v_whnfType_boxed_1152_, v___y_1146_, v___y_1147_, v___y_1148_, v___y_1149_);
lean_dec(v___y_1149_);
lean_dec_ref(v___y_1148_);
lean_dec(v___y_1147_);
lean_dec_ref(v___y_1146_);
return v_res_1153_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__4(lean_object* v_00_u03b1_1154_, lean_object* v_type_1155_, lean_object* v_maxFVars_x3f_1156_, lean_object* v_k_1157_, uint8_t v_cleanupAnnotations_1158_, uint8_t v_whnfType_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_){
_start:
{
lean_object* v___x_1165_; 
v___x_1165_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__4___redArg(v_type_1155_, v_maxFVars_x3f_1156_, v_k_1157_, v_cleanupAnnotations_1158_, v_whnfType_1159_, v___y_1160_, v___y_1161_, v___y_1162_, v___y_1163_);
return v___x_1165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__4___boxed(lean_object* v_00_u03b1_1166_, lean_object* v_type_1167_, lean_object* v_maxFVars_x3f_1168_, lean_object* v_k_1169_, lean_object* v_cleanupAnnotations_1170_, lean_object* v_whnfType_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1177_; uint8_t v_whnfType_boxed_1178_; lean_object* v_res_1179_; 
v_cleanupAnnotations_boxed_1177_ = lean_unbox(v_cleanupAnnotations_1170_);
v_whnfType_boxed_1178_ = lean_unbox(v_whnfType_1171_);
v_res_1179_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__4(v_00_u03b1_1166_, v_type_1167_, v_maxFVars_x3f_1168_, v_k_1169_, v_cleanupAnnotations_boxed_1177_, v_whnfType_boxed_1178_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_);
lean_dec(v___y_1175_);
lean_dec_ref(v___y_1174_);
lean_dec(v___y_1173_);
lean_dec_ref(v___y_1172_);
return v_res_1179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__5___redArg(lean_object* v_type_1180_, lean_object* v_k_1181_, uint8_t v_cleanupAnnotations_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_){
_start:
{
lean_object* v___f_1188_; uint8_t v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; 
v___f_1188_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__4___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1188_, 0, v_k_1181_);
v___x_1189_ = 0;
v___x_1190_ = lean_box(0);
v___x_1191_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_1189_, v___x_1190_, v_type_1180_, v___f_1188_, v_cleanupAnnotations_1182_, v___x_1189_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_);
if (lean_obj_tag(v___x_1191_) == 0)
{
lean_object* v_a_1192_; lean_object* v___x_1194_; uint8_t v_isShared_1195_; uint8_t v_isSharedCheck_1199_; 
v_a_1192_ = lean_ctor_get(v___x_1191_, 0);
v_isSharedCheck_1199_ = !lean_is_exclusive(v___x_1191_);
if (v_isSharedCheck_1199_ == 0)
{
v___x_1194_ = v___x_1191_;
v_isShared_1195_ = v_isSharedCheck_1199_;
goto v_resetjp_1193_;
}
else
{
lean_inc(v_a_1192_);
lean_dec(v___x_1191_);
v___x_1194_ = lean_box(0);
v_isShared_1195_ = v_isSharedCheck_1199_;
goto v_resetjp_1193_;
}
v_resetjp_1193_:
{
lean_object* v___x_1197_; 
if (v_isShared_1195_ == 0)
{
v___x_1197_ = v___x_1194_;
goto v_reusejp_1196_;
}
else
{
lean_object* v_reuseFailAlloc_1198_; 
v_reuseFailAlloc_1198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1198_, 0, v_a_1192_);
v___x_1197_ = v_reuseFailAlloc_1198_;
goto v_reusejp_1196_;
}
v_reusejp_1196_:
{
return v___x_1197_;
}
}
}
else
{
lean_object* v_a_1200_; lean_object* v___x_1202_; uint8_t v_isShared_1203_; uint8_t v_isSharedCheck_1207_; 
v_a_1200_ = lean_ctor_get(v___x_1191_, 0);
v_isSharedCheck_1207_ = !lean_is_exclusive(v___x_1191_);
if (v_isSharedCheck_1207_ == 0)
{
v___x_1202_ = v___x_1191_;
v_isShared_1203_ = v_isSharedCheck_1207_;
goto v_resetjp_1201_;
}
else
{
lean_inc(v_a_1200_);
lean_dec(v___x_1191_);
v___x_1202_ = lean_box(0);
v_isShared_1203_ = v_isSharedCheck_1207_;
goto v_resetjp_1201_;
}
v_resetjp_1201_:
{
lean_object* v___x_1205_; 
if (v_isShared_1203_ == 0)
{
v___x_1205_ = v___x_1202_;
goto v_reusejp_1204_;
}
else
{
lean_object* v_reuseFailAlloc_1206_; 
v_reuseFailAlloc_1206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1206_, 0, v_a_1200_);
v___x_1205_ = v_reuseFailAlloc_1206_;
goto v_reusejp_1204_;
}
v_reusejp_1204_:
{
return v___x_1205_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__5___redArg___boxed(lean_object* v_type_1208_, lean_object* v_k_1209_, lean_object* v_cleanupAnnotations_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1216_; lean_object* v_res_1217_; 
v_cleanupAnnotations_boxed_1216_ = lean_unbox(v_cleanupAnnotations_1210_);
v_res_1217_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__5___redArg(v_type_1208_, v_k_1209_, v_cleanupAnnotations_boxed_1216_, v___y_1211_, v___y_1212_, v___y_1213_, v___y_1214_);
lean_dec(v___y_1214_);
lean_dec_ref(v___y_1213_);
lean_dec(v___y_1212_);
lean_dec_ref(v___y_1211_);
return v_res_1217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__5(lean_object* v_00_u03b1_1218_, lean_object* v_type_1219_, lean_object* v_k_1220_, uint8_t v_cleanupAnnotations_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_){
_start:
{
lean_object* v___x_1227_; 
v___x_1227_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__5___redArg(v_type_1219_, v_k_1220_, v_cleanupAnnotations_1221_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_);
return v___x_1227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__5___boxed(lean_object* v_00_u03b1_1228_, lean_object* v_type_1229_, lean_object* v_k_1230_, lean_object* v_cleanupAnnotations_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1237_; lean_object* v_res_1238_; 
v_cleanupAnnotations_boxed_1237_ = lean_unbox(v_cleanupAnnotations_1231_);
v_res_1238_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__5(v_00_u03b1_1228_, v_type_1229_, v_k_1230_, v_cleanupAnnotations_boxed_1237_, v___y_1232_, v___y_1233_, v___y_1234_, v___y_1235_);
lean_dec(v___y_1235_);
lean_dec_ref(v___y_1234_);
lean_dec(v___y_1233_);
lean_dec_ref(v___y_1232_);
return v_res_1238_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__0(lean_object* v_params_1239_, lean_object* v_fvars_1240_, lean_object* v_ty_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_){
_start:
{
lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; 
v___x_1247_ = lean_array_mk(v_params_1239_);
v___x_1248_ = l_Lean_Expr_replaceFVars(v_ty_1241_, v_fvars_1240_, v___x_1247_);
lean_dec_ref(v___x_1247_);
v___x_1249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1249_, 0, v___x_1248_);
return v___x_1249_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__0___boxed(lean_object* v_params_1250_, lean_object* v_fvars_1251_, lean_object* v_ty_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_){
_start:
{
lean_object* v_res_1258_; 
v_res_1258_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__0(v_params_1250_, v_fvars_1251_, v_ty_1252_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_);
lean_dec(v___y_1256_);
lean_dec_ref(v___y_1255_);
lean_dec(v___y_1254_);
lean_dec_ref(v___y_1253_);
lean_dec_ref(v_ty_1252_);
lean_dec_ref(v_fvars_1251_);
return v_res_1258_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__2(lean_object* v_x_1265_, lean_object* v_x_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_){
_start:
{
if (lean_obj_tag(v_x_1265_) == 0)
{
lean_object* v___x_1272_; lean_object* v___x_1273_; 
v___x_1272_ = l_List_reverse___redArg(v_x_1266_);
v___x_1273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1273_, 0, v___x_1272_);
return v___x_1273_;
}
else
{
lean_object* v_head_1274_; lean_object* v_tail_1275_; lean_object* v___x_1277_; uint8_t v_isShared_1278_; uint8_t v_isSharedCheck_1335_; 
v_head_1274_ = lean_ctor_get(v_x_1265_, 0);
v_tail_1275_ = lean_ctor_get(v_x_1265_, 1);
v_isSharedCheck_1335_ = !lean_is_exclusive(v_x_1265_);
if (v_isSharedCheck_1335_ == 0)
{
v___x_1277_ = v_x_1265_;
v_isShared_1278_ = v_isSharedCheck_1335_;
goto v_resetjp_1276_;
}
else
{
lean_inc(v_tail_1275_);
lean_inc(v_head_1274_);
lean_dec(v_x_1265_);
v___x_1277_ = lean_box(0);
v_isShared_1278_ = v_isSharedCheck_1335_;
goto v_resetjp_1276_;
}
v_resetjp_1276_:
{
lean_object* v_a_1280_; lean_object* v___y_1286_; lean_object* v_fst_1296_; lean_object* v_snd_1297_; lean_object* v___x_1299_; uint8_t v_isShared_1300_; uint8_t v_isSharedCheck_1334_; 
v_fst_1296_ = lean_ctor_get(v_head_1274_, 0);
v_snd_1297_ = lean_ctor_get(v_head_1274_, 1);
v_isSharedCheck_1334_ = !lean_is_exclusive(v_head_1274_);
if (v_isSharedCheck_1334_ == 0)
{
v___x_1299_ = v_head_1274_;
v_isShared_1300_ = v_isSharedCheck_1334_;
goto v_resetjp_1298_;
}
else
{
lean_inc(v_snd_1297_);
lean_inc(v_fst_1296_);
lean_dec(v_head_1274_);
v___x_1299_ = lean_box(0);
v_isShared_1300_ = v_isSharedCheck_1334_;
goto v_resetjp_1298_;
}
v___jp_1279_:
{
lean_object* v___x_1282_; 
if (v_isShared_1278_ == 0)
{
lean_ctor_set(v___x_1277_, 1, v_x_1266_);
lean_ctor_set(v___x_1277_, 0, v_a_1280_);
v___x_1282_ = v___x_1277_;
goto v_reusejp_1281_;
}
else
{
lean_object* v_reuseFailAlloc_1284_; 
v_reuseFailAlloc_1284_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1284_, 0, v_a_1280_);
lean_ctor_set(v_reuseFailAlloc_1284_, 1, v_x_1266_);
v___x_1282_ = v_reuseFailAlloc_1284_;
goto v_reusejp_1281_;
}
v_reusejp_1281_:
{
v_x_1265_ = v_tail_1275_;
v_x_1266_ = v___x_1282_;
goto _start;
}
}
v___jp_1285_:
{
if (lean_obj_tag(v___y_1286_) == 0)
{
lean_object* v_a_1287_; 
v_a_1287_ = lean_ctor_get(v___y_1286_, 0);
lean_inc(v_a_1287_);
lean_dec_ref_known(v___y_1286_, 1);
v_a_1280_ = v_a_1287_;
goto v___jp_1279_;
}
else
{
lean_object* v_a_1288_; lean_object* v___x_1290_; uint8_t v_isShared_1291_; uint8_t v_isSharedCheck_1295_; 
lean_del_object(v___x_1277_);
lean_dec(v_tail_1275_);
lean_dec(v_x_1266_);
v_a_1288_ = lean_ctor_get(v___y_1286_, 0);
v_isSharedCheck_1295_ = !lean_is_exclusive(v___y_1286_);
if (v_isSharedCheck_1295_ == 0)
{
v___x_1290_ = v___y_1286_;
v_isShared_1291_ = v_isSharedCheck_1295_;
goto v_resetjp_1289_;
}
else
{
lean_inc(v_a_1288_);
lean_dec(v___y_1286_);
v___x_1290_ = lean_box(0);
v_isShared_1291_ = v_isSharedCheck_1295_;
goto v_resetjp_1289_;
}
v_resetjp_1289_:
{
lean_object* v___x_1293_; 
if (v_isShared_1291_ == 0)
{
v___x_1293_ = v___x_1290_;
goto v_reusejp_1292_;
}
else
{
lean_object* v_reuseFailAlloc_1294_; 
v_reuseFailAlloc_1294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1294_, 0, v_a_1288_);
v___x_1293_ = v_reuseFailAlloc_1294_;
goto v_reusejp_1292_;
}
v_reusejp_1292_:
{
return v___x_1293_;
}
}
}
}
v_resetjp_1298_:
{
lean_object* v___x_1301_; lean_object* v___x_1302_; 
v___x_1301_ = l_Lean_Expr_fvarId_x21(v_fst_1296_);
v___x_1302_ = l_Lean_FVarId_getType___redArg(v___x_1301_, v___y_1267_, v___y_1269_, v___y_1270_);
if (lean_obj_tag(v___x_1302_) == 0)
{
lean_object* v_a_1303_; lean_object* v___x_1304_; 
v_a_1303_ = lean_ctor_get(v___x_1302_, 0);
lean_inc(v_a_1303_);
lean_dec_ref_known(v___x_1302_, 1);
lean_inc(v___y_1270_);
lean_inc_ref(v___y_1269_);
lean_inc(v___y_1268_);
lean_inc_ref(v___y_1267_);
lean_inc(v_snd_1297_);
v___x_1304_ = lean_infer_type(v_snd_1297_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_);
if (lean_obj_tag(v___x_1304_) == 0)
{
lean_object* v_a_1305_; lean_object* v___x_1306_; 
v_a_1305_ = lean_ctor_get(v___x_1304_, 0);
lean_inc(v_a_1305_);
lean_dec_ref_known(v___x_1304_, 1);
lean_inc(v___y_1270_);
lean_inc_ref(v___y_1269_);
lean_inc(v___y_1268_);
lean_inc_ref(v___y_1267_);
lean_inc(v_a_1303_);
v___x_1306_ = lean_infer_type(v_a_1303_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_);
if (lean_obj_tag(v___x_1306_) == 0)
{
lean_object* v_a_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; 
v_a_1307_ = lean_ctor_get(v___x_1306_, 0);
lean_inc(v_a_1307_);
lean_dec_ref_known(v___x_1306_, 1);
v___x_1308_ = l_Lean_Expr_sortLevel_x21(v_a_1307_);
lean_dec(v_a_1307_);
lean_inc(v_a_1305_);
lean_inc(v_a_1303_);
v___x_1309_ = l_Lean_Meta_isExprDefEq(v_a_1303_, v_a_1305_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_);
if (lean_obj_tag(v___x_1309_) == 0)
{
lean_object* v_a_1310_; uint8_t v___x_1311_; 
v_a_1310_ = lean_ctor_get(v___x_1309_, 0);
lean_inc(v_a_1310_);
lean_dec_ref_known(v___x_1309_, 1);
v___x_1311_ = lean_unbox(v_a_1310_);
lean_dec(v_a_1310_);
if (v___x_1311_ == 0)
{
lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1315_; 
v___x_1312_ = ((lean_object*)(l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__2___closed__1));
v___x_1313_ = lean_box(0);
if (v_isShared_1300_ == 0)
{
lean_ctor_set_tag(v___x_1299_, 1);
lean_ctor_set(v___x_1299_, 1, v___x_1313_);
lean_ctor_set(v___x_1299_, 0, v___x_1308_);
v___x_1315_ = v___x_1299_;
goto v_reusejp_1314_;
}
else
{
lean_object* v_reuseFailAlloc_1318_; 
v_reuseFailAlloc_1318_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1318_, 0, v___x_1308_);
lean_ctor_set(v_reuseFailAlloc_1318_, 1, v___x_1313_);
v___x_1315_ = v_reuseFailAlloc_1318_;
goto v_reusejp_1314_;
}
v_reusejp_1314_:
{
lean_object* v___x_1316_; lean_object* v___x_1317_; 
v___x_1316_ = l_Lean_Expr_const___override(v___x_1312_, v___x_1315_);
v___x_1317_ = l_Lean_mkApp4(v___x_1316_, v_a_1303_, v_fst_1296_, v_a_1305_, v_snd_1297_);
v_a_1280_ = v___x_1317_;
goto v___jp_1279_;
}
}
else
{
lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1322_; 
lean_dec(v_a_1305_);
v___x_1319_ = ((lean_object*)(l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__2___closed__3));
v___x_1320_ = lean_box(0);
if (v_isShared_1300_ == 0)
{
lean_ctor_set_tag(v___x_1299_, 1);
lean_ctor_set(v___x_1299_, 1, v___x_1320_);
lean_ctor_set(v___x_1299_, 0, v___x_1308_);
v___x_1322_ = v___x_1299_;
goto v_reusejp_1321_;
}
else
{
lean_object* v_reuseFailAlloc_1325_; 
v_reuseFailAlloc_1325_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1325_, 0, v___x_1308_);
lean_ctor_set(v_reuseFailAlloc_1325_, 1, v___x_1320_);
v___x_1322_ = v_reuseFailAlloc_1325_;
goto v_reusejp_1321_;
}
v_reusejp_1321_:
{
lean_object* v___x_1323_; lean_object* v___x_1324_; 
v___x_1323_ = l_Lean_Expr_const___override(v___x_1319_, v___x_1322_);
v___x_1324_ = l_Lean_mkApp3(v___x_1323_, v_a_1303_, v_fst_1296_, v_snd_1297_);
v_a_1280_ = v___x_1324_;
goto v___jp_1279_;
}
}
}
else
{
lean_object* v_a_1326_; lean_object* v___x_1328_; uint8_t v_isShared_1329_; uint8_t v_isSharedCheck_1333_; 
lean_dec(v___x_1308_);
lean_dec(v_a_1305_);
lean_dec(v_a_1303_);
lean_del_object(v___x_1299_);
lean_dec(v_snd_1297_);
lean_dec(v_fst_1296_);
lean_del_object(v___x_1277_);
lean_dec(v_tail_1275_);
lean_dec(v_x_1266_);
v_a_1326_ = lean_ctor_get(v___x_1309_, 0);
v_isSharedCheck_1333_ = !lean_is_exclusive(v___x_1309_);
if (v_isSharedCheck_1333_ == 0)
{
v___x_1328_ = v___x_1309_;
v_isShared_1329_ = v_isSharedCheck_1333_;
goto v_resetjp_1327_;
}
else
{
lean_inc(v_a_1326_);
lean_dec(v___x_1309_);
v___x_1328_ = lean_box(0);
v_isShared_1329_ = v_isSharedCheck_1333_;
goto v_resetjp_1327_;
}
v_resetjp_1327_:
{
lean_object* v___x_1331_; 
if (v_isShared_1329_ == 0)
{
v___x_1331_ = v___x_1328_;
goto v_reusejp_1330_;
}
else
{
lean_object* v_reuseFailAlloc_1332_; 
v_reuseFailAlloc_1332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1332_, 0, v_a_1326_);
v___x_1331_ = v_reuseFailAlloc_1332_;
goto v_reusejp_1330_;
}
v_reusejp_1330_:
{
return v___x_1331_;
}
}
}
}
else
{
lean_dec(v_a_1305_);
lean_dec(v_a_1303_);
lean_del_object(v___x_1299_);
lean_dec(v_snd_1297_);
lean_dec(v_fst_1296_);
v___y_1286_ = v___x_1306_;
goto v___jp_1285_;
}
}
else
{
lean_dec(v_a_1303_);
lean_del_object(v___x_1299_);
lean_dec(v_snd_1297_);
lean_dec(v_fst_1296_);
v___y_1286_ = v___x_1304_;
goto v___jp_1285_;
}
}
else
{
lean_del_object(v___x_1299_);
lean_dec(v_snd_1297_);
lean_dec(v_fst_1296_);
v___y_1286_ = v___x_1302_;
goto v___jp_1285_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__2___boxed(lean_object* v_x_1336_, lean_object* v_x_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_){
_start:
{
lean_object* v_res_1343_; 
v_res_1343_ = l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__2(v_x_1336_, v_x_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_);
lean_dec(v___y_1341_);
lean_dec_ref(v___y_1340_);
lean_dec(v___y_1339_);
lean_dec_ref(v___y_1338_);
return v_res_1343_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__3(lean_object* v_a_1344_, lean_object* v_a_1345_){
_start:
{
if (lean_obj_tag(v_a_1344_) == 0)
{
lean_object* v___x_1346_; 
v___x_1346_ = lean_array_to_list(v_a_1345_);
return v___x_1346_;
}
else
{
lean_object* v_head_1347_; 
v_head_1347_ = lean_ctor_get(v_a_1344_, 0);
if (lean_obj_tag(v_head_1347_) == 0)
{
lean_object* v_tail_1348_; 
v_tail_1348_ = lean_ctor_get(v_a_1344_, 1);
lean_inc(v_tail_1348_);
lean_dec_ref_known(v_a_1344_, 2);
v_a_1344_ = v_tail_1348_;
goto _start;
}
else
{
lean_object* v_tail_1350_; lean_object* v_val_1351_; lean_object* v___x_1352_; 
lean_inc_ref(v_head_1347_);
v_tail_1350_ = lean_ctor_get(v_a_1344_, 1);
lean_inc(v_tail_1350_);
lean_dec_ref_known(v_a_1344_, 2);
v_val_1351_ = lean_ctor_get(v_head_1347_, 0);
lean_inc(v_val_1351_);
lean_dec_ref_known(v_head_1347_, 1);
v___x_1352_ = lean_array_push(v_a_1345_, v_val_1351_);
v_a_1344_ = v_tail_1350_;
v_a_1345_ = v___x_1352_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__1(lean_object* v_a_1354_, lean_object* v_a_1355_){
_start:
{
if (lean_obj_tag(v_a_1354_) == 0)
{
lean_object* v___x_1356_; 
v___x_1356_ = l_List_reverse___redArg(v_a_1355_);
return v___x_1356_;
}
else
{
lean_object* v_head_1357_; lean_object* v_tail_1358_; lean_object* v___x_1360_; uint8_t v_isShared_1361_; uint8_t v_isSharedCheck_1371_; 
v_head_1357_ = lean_ctor_get(v_a_1354_, 0);
v_tail_1358_ = lean_ctor_get(v_a_1354_, 1);
v_isSharedCheck_1371_ = !lean_is_exclusive(v_a_1354_);
if (v_isSharedCheck_1371_ == 0)
{
v___x_1360_ = v_a_1354_;
v_isShared_1361_ = v_isSharedCheck_1371_;
goto v_resetjp_1359_;
}
else
{
lean_inc(v_tail_1358_);
lean_inc(v_head_1357_);
lean_dec(v_a_1354_);
v___x_1360_ = lean_box(0);
v_isShared_1361_ = v_isSharedCheck_1371_;
goto v_resetjp_1359_;
}
v_resetjp_1359_:
{
uint8_t v___y_1363_; 
if (lean_obj_tag(v_head_1357_) == 0)
{
uint8_t v___x_1369_; 
v___x_1369_ = 0;
v___y_1363_ = v___x_1369_;
goto v___jp_1362_;
}
else
{
uint8_t v___x_1370_; 
lean_dec_ref_known(v_head_1357_, 1);
v___x_1370_ = 1;
v___y_1363_ = v___x_1370_;
goto v___jp_1362_;
}
v___jp_1362_:
{
lean_object* v___x_1364_; lean_object* v___x_1366_; 
v___x_1364_ = lean_box(v___y_1363_);
if (v_isShared_1361_ == 0)
{
lean_ctor_set(v___x_1360_, 1, v_a_1355_);
lean_ctor_set(v___x_1360_, 0, v___x_1364_);
v___x_1366_ = v___x_1360_;
goto v_reusejp_1365_;
}
else
{
lean_object* v_reuseFailAlloc_1368_; 
v_reuseFailAlloc_1368_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1368_, 0, v___x_1364_);
lean_ctor_set(v_reuseFailAlloc_1368_, 1, v_a_1355_);
v___x_1366_ = v_reuseFailAlloc_1368_;
goto v_reusejp_1365_;
}
v_reusejp_1365_:
{
v_a_1354_ = v_tail_1358_;
v_a_1355_ = v___x_1366_;
goto _start;
}
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__1___closed__0(void){
_start:
{
lean_object* v___x_1372_; lean_object* v_dummy_1373_; 
v___x_1372_ = lean_box(0);
v_dummy_1373_ = l_Lean_Expr_sort___override(v___x_1372_);
return v_dummy_1373_;
}
}
static lean_object* _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__1___closed__3(void){
_start:
{
lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; 
v___x_1378_ = lean_box(0);
v___x_1379_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkAndList___closed__1));
v___x_1380_ = l_Lean_mkConst(v___x_1379_, v___x_1378_);
return v___x_1380_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__1(lean_object* v___x_1381_, lean_object* v_idxs_1382_, lean_object* v___x_1383_, lean_object* v_fvars_1384_, lean_object* v_ty_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_){
_start:
{
lean_object* v___x_1391_; lean_object* v_dummy_1392_; lean_object* v_nargs_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v_fst_1403_; lean_object* v_snd_1404_; lean_object* v___x_1406_; uint8_t v_isShared_1407_; uint8_t v_isSharedCheck_1505_; 
v___x_1391_ = lean_box(0);
v_dummy_1392_ = lean_obj_once(&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__1___closed__0, &l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__1___closed__0_once, _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__1___closed__0);
v_nargs_1393_ = l_Lean_Expr_getAppNumArgs(v_ty_1385_);
lean_inc(v_nargs_1393_);
v___x_1394_ = lean_mk_array(v_nargs_1393_, v_dummy_1392_);
v___x_1395_ = lean_unsigned_to_nat(1u);
v___x_1396_ = lean_nat_sub(v_nargs_1393_, v___x_1395_);
lean_dec(v_nargs_1393_);
v___x_1397_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_ty_1385_, v___x_1394_, v___x_1396_);
v___x_1398_ = lean_array_to_list(v___x_1397_);
v___x_1399_ = l_List_drop___redArg(v___x_1381_, v___x_1398_);
lean_dec(v___x_1398_);
v___x_1400_ = lean_array_to_list(v_fvars_1384_);
v___x_1401_ = l_List_zipWith___at___00List_zip_spec__0(lean_box(0), lean_box(0), v_idxs_1382_, v___x_1399_);
v___x_1402_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_compactRelation(v___x_1400_, v___x_1401_);
v_fst_1403_ = lean_ctor_get(v___x_1402_, 0);
v_snd_1404_ = lean_ctor_get(v___x_1402_, 1);
v_isSharedCheck_1505_ = !lean_is_exclusive(v___x_1402_);
if (v_isSharedCheck_1505_ == 0)
{
v___x_1406_ = v___x_1402_;
v_isShared_1407_ = v_isSharedCheck_1505_;
goto v_resetjp_1405_;
}
else
{
lean_inc(v_snd_1404_);
lean_inc(v_fst_1403_);
lean_dec(v___x_1402_);
v___x_1406_ = lean_box(0);
v_isShared_1407_ = v_isSharedCheck_1505_;
goto v_resetjp_1405_;
}
v_resetjp_1405_:
{
lean_object* v_fst_1409_; lean_object* v_snd_1410_; lean_object* v_fst_1418_; lean_object* v_snd_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; 
v_fst_1418_ = lean_ctor_get(v_snd_1404_, 0);
lean_inc(v_fst_1418_);
v_snd_1419_ = lean_ctor_get(v_snd_1404_, 1);
lean_inc(v_snd_1419_);
lean_dec(v_snd_1404_);
v___x_1420_ = lean_box(0);
v___x_1421_ = l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__2(v_fst_1418_, v___x_1420_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_);
if (lean_obj_tag(v___x_1421_) == 0)
{
lean_object* v_a_1422_; lean_object* v_bs_x27_1424_; lean_object* v___y_1425_; lean_object* v___y_1426_; lean_object* v___y_1427_; lean_object* v___y_1428_; lean_object* v___x_1443_; lean_object* v___x_1444_; 
v_a_1422_ = lean_ctor_get(v___x_1421_, 0);
lean_inc(v_a_1422_);
lean_dec_ref_known(v___x_1421_, 1);
v___x_1443_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__1___closed__1));
lean_inc(v_fst_1403_);
v___x_1444_ = l_List_filterMapTR_go___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__3(v_fst_1403_, v___x_1443_);
if (lean_obj_tag(v___x_1444_) == 0)
{
if (lean_obj_tag(v_a_1422_) == 0)
{
lean_object* v___x_1445_; lean_object* v___x_1446_; 
lean_dec(v_snd_1419_);
v___x_1445_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__1___closed__2));
v___x_1446_ = lean_obj_once(&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__1___closed__3, &l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__1___closed__3_once, _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__1___closed__3);
v_fst_1409_ = v___x_1445_;
v_snd_1410_ = v___x_1446_;
goto v___jp_1408_;
}
else
{
v_bs_x27_1424_ = v___x_1444_;
v___y_1425_ = v___y_1386_;
v___y_1426_ = v___y_1387_;
v___y_1427_ = v___y_1388_;
v___y_1428_ = v___y_1389_;
goto v___jp_1423_;
}
}
else
{
if (lean_obj_tag(v_a_1422_) == 0)
{
lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; 
v___x_1447_ = l_List_getLast_x21___redArg(v___x_1383_, v___x_1444_);
v___x_1448_ = l_Lean_Expr_fvarId_x21(v___x_1447_);
lean_dec(v___x_1447_);
v___x_1449_ = l_Lean_FVarId_getType___redArg(v___x_1448_, v___y_1386_, v___y_1388_, v___y_1389_);
if (lean_obj_tag(v___x_1449_) == 0)
{
lean_object* v_a_1450_; lean_object* v___x_1451_; 
v_a_1450_ = lean_ctor_get(v___x_1449_, 0);
lean_inc_n(v_a_1450_, 2);
lean_dec_ref_known(v___x_1449_, 1);
lean_inc(v___y_1389_);
lean_inc_ref(v___y_1388_);
lean_inc(v___y_1387_);
lean_inc_ref(v___y_1386_);
v___x_1451_ = lean_infer_type(v_a_1450_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_);
if (lean_obj_tag(v___x_1451_) == 0)
{
lean_object* v_a_1452_; lean_object* v___x_1453_; uint8_t v___x_1454_; 
v_a_1452_ = lean_ctor_get(v___x_1451_, 0);
lean_inc(v_a_1452_);
lean_dec_ref_known(v___x_1451_, 1);
v___x_1453_ = l_Lean_Expr_sortLevel_x21(v_a_1452_);
lean_dec(v_a_1452_);
v___x_1454_ = lean_level_eq(v___x_1453_, v___x_1391_);
lean_dec(v___x_1453_);
if (v___x_1454_ == 0)
{
lean_object* v___x_1455_; lean_object* v___x_1456_; 
lean_dec(v_a_1450_);
v___x_1455_ = lean_obj_once(&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__1___closed__3, &l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__1___closed__3_once, _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__1___closed__3);
v___x_1456_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkExistsList(v___x_1444_, v___x_1455_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_);
if (lean_obj_tag(v___x_1456_) == 0)
{
lean_object* v_a_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; 
v_a_1457_ = lean_ctor_get(v___x_1456_, 0);
lean_inc(v_a_1457_);
lean_dec_ref_known(v___x_1456_, 1);
v___x_1458_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__1___closed__2));
v___x_1459_ = lean_apply_1(v_snd_1419_, v_a_1457_);
v_fst_1409_ = v___x_1458_;
v_snd_1410_ = v___x_1459_;
goto v___jp_1408_;
}
else
{
lean_object* v_a_1460_; lean_object* v___x_1462_; uint8_t v_isShared_1463_; uint8_t v_isSharedCheck_1467_; 
lean_dec(v_snd_1419_);
lean_del_object(v___x_1406_);
lean_dec(v_fst_1403_);
v_a_1460_ = lean_ctor_get(v___x_1456_, 0);
v_isSharedCheck_1467_ = !lean_is_exclusive(v___x_1456_);
if (v_isSharedCheck_1467_ == 0)
{
v___x_1462_ = v___x_1456_;
v_isShared_1463_ = v_isSharedCheck_1467_;
goto v_resetjp_1461_;
}
else
{
lean_inc(v_a_1460_);
lean_dec(v___x_1456_);
v___x_1462_ = lean_box(0);
v_isShared_1463_ = v_isSharedCheck_1467_;
goto v_resetjp_1461_;
}
v_resetjp_1461_:
{
lean_object* v___x_1465_; 
if (v_isShared_1463_ == 0)
{
v___x_1465_ = v___x_1462_;
goto v_reusejp_1464_;
}
else
{
lean_object* v_reuseFailAlloc_1466_; 
v_reuseFailAlloc_1466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1466_, 0, v_a_1460_);
v___x_1465_ = v_reuseFailAlloc_1466_;
goto v_reusejp_1464_;
}
v_reusejp_1464_:
{
return v___x_1465_;
}
}
}
}
else
{
lean_object* v___x_1468_; lean_object* v___x_1469_; 
v___x_1468_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_List_init___redArg(v___x_1444_);
v___x_1469_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkExistsList(v___x_1468_, v_a_1450_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_);
if (lean_obj_tag(v___x_1469_) == 0)
{
lean_object* v_a_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; 
v_a_1470_ = lean_ctor_get(v___x_1469_, 0);
lean_inc(v_a_1470_);
lean_dec_ref_known(v___x_1469_, 1);
v___x_1471_ = lean_box(0);
v___x_1472_ = lean_apply_1(v_snd_1419_, v_a_1470_);
v_fst_1409_ = v___x_1471_;
v_snd_1410_ = v___x_1472_;
goto v___jp_1408_;
}
else
{
lean_object* v_a_1473_; lean_object* v___x_1475_; uint8_t v_isShared_1476_; uint8_t v_isSharedCheck_1480_; 
lean_dec(v_snd_1419_);
lean_del_object(v___x_1406_);
lean_dec(v_fst_1403_);
v_a_1473_ = lean_ctor_get(v___x_1469_, 0);
v_isSharedCheck_1480_ = !lean_is_exclusive(v___x_1469_);
if (v_isSharedCheck_1480_ == 0)
{
v___x_1475_ = v___x_1469_;
v_isShared_1476_ = v_isSharedCheck_1480_;
goto v_resetjp_1474_;
}
else
{
lean_inc(v_a_1473_);
lean_dec(v___x_1469_);
v___x_1475_ = lean_box(0);
v_isShared_1476_ = v_isSharedCheck_1480_;
goto v_resetjp_1474_;
}
v_resetjp_1474_:
{
lean_object* v___x_1478_; 
if (v_isShared_1476_ == 0)
{
v___x_1478_ = v___x_1475_;
goto v_reusejp_1477_;
}
else
{
lean_object* v_reuseFailAlloc_1479_; 
v_reuseFailAlloc_1479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1479_, 0, v_a_1473_);
v___x_1478_ = v_reuseFailAlloc_1479_;
goto v_reusejp_1477_;
}
v_reusejp_1477_:
{
return v___x_1478_;
}
}
}
}
}
else
{
lean_object* v_a_1481_; lean_object* v___x_1483_; uint8_t v_isShared_1484_; uint8_t v_isSharedCheck_1488_; 
lean_dec(v_a_1450_);
lean_dec(v___x_1444_);
lean_dec(v_snd_1419_);
lean_del_object(v___x_1406_);
lean_dec(v_fst_1403_);
v_a_1481_ = lean_ctor_get(v___x_1451_, 0);
v_isSharedCheck_1488_ = !lean_is_exclusive(v___x_1451_);
if (v_isSharedCheck_1488_ == 0)
{
v___x_1483_ = v___x_1451_;
v_isShared_1484_ = v_isSharedCheck_1488_;
goto v_resetjp_1482_;
}
else
{
lean_inc(v_a_1481_);
lean_dec(v___x_1451_);
v___x_1483_ = lean_box(0);
v_isShared_1484_ = v_isSharedCheck_1488_;
goto v_resetjp_1482_;
}
v_resetjp_1482_:
{
lean_object* v___x_1486_; 
if (v_isShared_1484_ == 0)
{
v___x_1486_ = v___x_1483_;
goto v_reusejp_1485_;
}
else
{
lean_object* v_reuseFailAlloc_1487_; 
v_reuseFailAlloc_1487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1487_, 0, v_a_1481_);
v___x_1486_ = v_reuseFailAlloc_1487_;
goto v_reusejp_1485_;
}
v_reusejp_1485_:
{
return v___x_1486_;
}
}
}
}
else
{
lean_object* v_a_1489_; lean_object* v___x_1491_; uint8_t v_isShared_1492_; uint8_t v_isSharedCheck_1496_; 
lean_dec(v___x_1444_);
lean_dec(v_snd_1419_);
lean_del_object(v___x_1406_);
lean_dec(v_fst_1403_);
v_a_1489_ = lean_ctor_get(v___x_1449_, 0);
v_isSharedCheck_1496_ = !lean_is_exclusive(v___x_1449_);
if (v_isSharedCheck_1496_ == 0)
{
v___x_1491_ = v___x_1449_;
v_isShared_1492_ = v_isSharedCheck_1496_;
goto v_resetjp_1490_;
}
else
{
lean_inc(v_a_1489_);
lean_dec(v___x_1449_);
v___x_1491_ = lean_box(0);
v_isShared_1492_ = v_isSharedCheck_1496_;
goto v_resetjp_1490_;
}
v_resetjp_1490_:
{
lean_object* v___x_1494_; 
if (v_isShared_1492_ == 0)
{
v___x_1494_ = v___x_1491_;
goto v_reusejp_1493_;
}
else
{
lean_object* v_reuseFailAlloc_1495_; 
v_reuseFailAlloc_1495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1495_, 0, v_a_1489_);
v___x_1494_ = v_reuseFailAlloc_1495_;
goto v_reusejp_1493_;
}
v_reusejp_1493_:
{
return v___x_1494_;
}
}
}
}
else
{
v_bs_x27_1424_ = v___x_1444_;
v___y_1425_ = v___y_1386_;
v___y_1426_ = v___y_1387_;
v___y_1427_ = v___y_1388_;
v___y_1428_ = v___y_1389_;
goto v___jp_1423_;
}
}
v___jp_1423_:
{
lean_object* v___x_1429_; lean_object* v___x_1430_; 
lean_inc(v_a_1422_);
v___x_1429_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkAndList(v_a_1422_);
v___x_1430_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkExistsList(v_bs_x27_1424_, v___x_1429_, v___y_1425_, v___y_1426_, v___y_1427_, v___y_1428_);
if (lean_obj_tag(v___x_1430_) == 0)
{
lean_object* v_a_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; 
v_a_1431_ = lean_ctor_get(v___x_1430_, 0);
lean_inc(v_a_1431_);
lean_dec_ref_known(v___x_1430_, 1);
v___x_1432_ = l_List_lengthTR___redArg(v_a_1422_);
lean_dec(v_a_1422_);
v___x_1433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1433_, 0, v___x_1432_);
v___x_1434_ = lean_apply_1(v_snd_1419_, v_a_1431_);
v_fst_1409_ = v___x_1433_;
v_snd_1410_ = v___x_1434_;
goto v___jp_1408_;
}
else
{
lean_object* v_a_1435_; lean_object* v___x_1437_; uint8_t v_isShared_1438_; uint8_t v_isSharedCheck_1442_; 
lean_dec(v_a_1422_);
lean_dec(v_snd_1419_);
lean_del_object(v___x_1406_);
lean_dec(v_fst_1403_);
v_a_1435_ = lean_ctor_get(v___x_1430_, 0);
v_isSharedCheck_1442_ = !lean_is_exclusive(v___x_1430_);
if (v_isSharedCheck_1442_ == 0)
{
v___x_1437_ = v___x_1430_;
v_isShared_1438_ = v_isSharedCheck_1442_;
goto v_resetjp_1436_;
}
else
{
lean_inc(v_a_1435_);
lean_dec(v___x_1430_);
v___x_1437_ = lean_box(0);
v_isShared_1438_ = v_isSharedCheck_1442_;
goto v_resetjp_1436_;
}
v_resetjp_1436_:
{
lean_object* v___x_1440_; 
if (v_isShared_1438_ == 0)
{
v___x_1440_ = v___x_1437_;
goto v_reusejp_1439_;
}
else
{
lean_object* v_reuseFailAlloc_1441_; 
v_reuseFailAlloc_1441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1441_, 0, v_a_1435_);
v___x_1440_ = v_reuseFailAlloc_1441_;
goto v_reusejp_1439_;
}
v_reusejp_1439_:
{
return v___x_1440_;
}
}
}
}
}
else
{
lean_object* v_a_1497_; lean_object* v___x_1499_; uint8_t v_isShared_1500_; uint8_t v_isSharedCheck_1504_; 
lean_dec(v_snd_1419_);
lean_del_object(v___x_1406_);
lean_dec(v_fst_1403_);
v_a_1497_ = lean_ctor_get(v___x_1421_, 0);
v_isSharedCheck_1504_ = !lean_is_exclusive(v___x_1421_);
if (v_isSharedCheck_1504_ == 0)
{
v___x_1499_ = v___x_1421_;
v_isShared_1500_ = v_isSharedCheck_1504_;
goto v_resetjp_1498_;
}
else
{
lean_inc(v_a_1497_);
lean_dec(v___x_1421_);
v___x_1499_ = lean_box(0);
v_isShared_1500_ = v_isSharedCheck_1504_;
goto v_resetjp_1498_;
}
v_resetjp_1498_:
{
lean_object* v___x_1502_; 
if (v_isShared_1500_ == 0)
{
v___x_1502_ = v___x_1499_;
goto v_reusejp_1501_;
}
else
{
lean_object* v_reuseFailAlloc_1503_; 
v_reuseFailAlloc_1503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1503_, 0, v_a_1497_);
v___x_1502_ = v_reuseFailAlloc_1503_;
goto v_reusejp_1501_;
}
v_reusejp_1501_:
{
return v___x_1502_;
}
}
}
v___jp_1408_:
{
lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1415_; 
v___x_1411_ = lean_box(0);
v___x_1412_ = l_List_mapTR_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__1(v_fst_1403_, v___x_1411_);
v___x_1413_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1413_, 0, v___x_1412_);
lean_ctor_set(v___x_1413_, 1, v_fst_1409_);
if (v_isShared_1407_ == 0)
{
lean_ctor_set(v___x_1406_, 1, v_snd_1410_);
lean_ctor_set(v___x_1406_, 0, v___x_1413_);
v___x_1415_ = v___x_1406_;
goto v_reusejp_1414_;
}
else
{
lean_object* v_reuseFailAlloc_1417_; 
v_reuseFailAlloc_1417_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1417_, 0, v___x_1413_);
lean_ctor_set(v_reuseFailAlloc_1417_, 1, v_snd_1410_);
v___x_1415_ = v_reuseFailAlloc_1417_;
goto v_reusejp_1414_;
}
v_reusejp_1414_:
{
lean_object* v___x_1416_; 
v___x_1416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1416_, 0, v___x_1415_);
return v___x_1416_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__1___boxed(lean_object* v___x_1506_, lean_object* v_idxs_1507_, lean_object* v___x_1508_, lean_object* v_fvars_1509_, lean_object* v_ty_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_){
_start:
{
lean_object* v_res_1516_; 
v_res_1516_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__1(v___x_1506_, v_idxs_1507_, v___x_1508_, v_fvars_1509_, v_ty_1510_, v___y_1511_, v___y_1512_, v___y_1513_, v___y_1514_);
lean_dec(v___y_1514_);
lean_dec_ref(v___y_1513_);
lean_dec(v___y_1512_);
lean_dec_ref(v___y_1511_);
lean_dec_ref(v___x_1508_);
return v_res_1516_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__9___redArg(lean_object* v_ref_1517_, lean_object* v_msg_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_){
_start:
{
lean_object* v_toCold_1524_; lean_object* v_currRecDepth_1525_; lean_object* v_ref_1526_; uint16_t v_optionFlags_1527_; uint8_t v_suppressElabErrors_1528_; uint8_t v_isRecordingDeps_1529_; lean_object* v_ref_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; 
v_toCold_1524_ = lean_ctor_get(v___y_1521_, 0);
v_currRecDepth_1525_ = lean_ctor_get(v___y_1521_, 1);
v_ref_1526_ = lean_ctor_get(v___y_1521_, 2);
v_optionFlags_1527_ = lean_ctor_get_uint16(v___y_1521_, sizeof(void*)*3);
v_suppressElabErrors_1528_ = lean_ctor_get_uint8(v___y_1521_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1529_ = lean_ctor_get_uint8(v___y_1521_, sizeof(void*)*3 + 3);
v_ref_1530_ = l_Lean_replaceRef(v_ref_1517_, v_ref_1526_);
lean_inc(v_currRecDepth_1525_);
lean_inc_ref(v_toCold_1524_);
v___x_1531_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1531_, 0, v_toCold_1524_);
lean_ctor_set(v___x_1531_, 1, v_currRecDepth_1525_);
lean_ctor_set(v___x_1531_, 2, v_ref_1530_);
lean_ctor_set_uint16(v___x_1531_, sizeof(void*)*3, v_optionFlags_1527_);
lean_ctor_set_uint8(v___x_1531_, sizeof(void*)*3 + 2, v_suppressElabErrors_1528_);
lean_ctor_set_uint8(v___x_1531_, sizeof(void*)*3 + 3, v_isRecordingDeps_1529_);
v___x_1532_ = l_Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0___redArg(v_msg_1518_, v___y_1519_, v___y_1520_, v___x_1531_, v___y_1522_);
lean_dec_ref_known(v___x_1531_, 3);
return v___x_1532_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__9___redArg___boxed(lean_object* v_ref_1533_, lean_object* v_msg_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_){
_start:
{
lean_object* v_res_1540_; 
v_res_1540_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__9___redArg(v_ref_1533_, v_msg_1534_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_);
lean_dec(v___y_1538_);
lean_dec_ref(v___y_1537_);
lean_dec(v___y_1536_);
lean_dec_ref(v___y_1535_);
lean_dec(v_ref_1533_);
return v_res_1540_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__0(void){
_start:
{
lean_object* v___x_1541_; 
v___x_1541_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1541_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__1(void){
_start:
{
lean_object* v___x_1542_; lean_object* v___x_1543_; 
v___x_1542_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__0);
v___x_1543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1543_, 0, v___x_1542_);
return v___x_1543_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__2(void){
_start:
{
lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; 
v___x_1544_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_1545_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__1);
v___x_1546_ = lean_unsigned_to_nat(0u);
v___x_1547_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_1547_, 0, v___x_1546_);
lean_ctor_set(v___x_1547_, 1, v___x_1546_);
lean_ctor_set(v___x_1547_, 2, v___x_1546_);
lean_ctor_set(v___x_1547_, 3, v___x_1546_);
lean_ctor_set(v___x_1547_, 4, v___x_1545_);
lean_ctor_set(v___x_1547_, 5, v___x_1545_);
lean_ctor_set(v___x_1547_, 6, v___x_1545_);
lean_ctor_set(v___x_1547_, 7, v___x_1545_);
lean_ctor_set(v___x_1547_, 8, v___x_1545_);
lean_ctor_set(v___x_1547_, 9, v___x_1545_);
lean_ctor_set(v___x_1547_, 10, v___x_1545_);
lean_ctor_set(v___x_1547_, 11, v___x_1544_);
return v___x_1547_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__3(void){
_start:
{
lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; 
v___x_1548_ = lean_unsigned_to_nat(32u);
v___x_1549_ = lean_mk_empty_array_with_capacity(v___x_1548_);
v___x_1550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1550_, 0, v___x_1549_);
return v___x_1550_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__4(void){
_start:
{
size_t v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; 
v___x_1551_ = ((size_t)5ULL);
v___x_1552_ = lean_unsigned_to_nat(0u);
v___x_1553_ = lean_unsigned_to_nat(32u);
v___x_1554_ = lean_mk_empty_array_with_capacity(v___x_1553_);
v___x_1555_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__3);
v___x_1556_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1556_, 0, v___x_1555_);
lean_ctor_set(v___x_1556_, 1, v___x_1554_);
lean_ctor_set(v___x_1556_, 2, v___x_1552_);
lean_ctor_set(v___x_1556_, 3, v___x_1552_);
lean_ctor_set_usize(v___x_1556_, 4, v___x_1551_);
return v___x_1556_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__5(void){
_start:
{
lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; 
v___x_1557_ = lean_box(1);
v___x_1558_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__4);
v___x_1559_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__1);
v___x_1560_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1560_, 0, v___x_1559_);
lean_ctor_set(v___x_1560_, 1, v___x_1558_);
lean_ctor_set(v___x_1560_, 2, v___x_1557_);
return v___x_1560_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__7(void){
_start:
{
lean_object* v___x_1562_; lean_object* v___x_1563_; 
v___x_1562_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__6));
v___x_1563_ = l_Lean_stringToMessageData(v___x_1562_);
return v___x_1563_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__9(void){
_start:
{
lean_object* v___x_1565_; lean_object* v___x_1566_; 
v___x_1565_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__8));
v___x_1566_ = l_Lean_stringToMessageData(v___x_1565_);
return v___x_1566_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__11(void){
_start:
{
lean_object* v___x_1568_; lean_object* v___x_1569_; 
v___x_1568_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__10));
v___x_1569_ = l_Lean_stringToMessageData(v___x_1568_);
return v___x_1569_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__13(void){
_start:
{
lean_object* v___x_1571_; lean_object* v___x_1572_; 
v___x_1571_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__12));
v___x_1572_ = l_Lean_stringToMessageData(v___x_1571_);
return v___x_1572_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__15(void){
_start:
{
lean_object* v___x_1574_; lean_object* v___x_1575_; 
v___x_1574_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__14));
v___x_1575_ = l_Lean_stringToMessageData(v___x_1574_);
return v___x_1575_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__17(void){
_start:
{
lean_object* v___x_1577_; lean_object* v___x_1578_; 
v___x_1577_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__16));
v___x_1578_ = l_Lean_stringToMessageData(v___x_1577_);
return v___x_1578_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__19(void){
_start:
{
lean_object* v___x_1580_; lean_object* v___x_1581_; 
v___x_1580_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__18));
v___x_1581_ = l_Lean_stringToMessageData(v___x_1580_);
return v___x_1581_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg(lean_object* v_msg_1582_, lean_object* v_declHint_1583_, lean_object* v___y_1584_){
_start:
{
lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v_env_1588_; uint8_t v___x_1589_; 
v___x_1586_ = lean_box(0);
v___x_1587_ = lean_st_ref_get(v___y_1584_);
v_env_1588_ = lean_ctor_get(v___x_1587_, 0);
lean_inc_ref(v_env_1588_);
lean_dec(v___x_1587_);
v___x_1589_ = l_Lean_Name_isAnonymous(v_declHint_1583_);
if (v___x_1589_ == 0)
{
uint8_t v_isExporting_1590_; 
v_isExporting_1590_ = lean_ctor_get_uint8(v_env_1588_, sizeof(void*)*13);
if (v_isExporting_1590_ == 0)
{
lean_object* v___x_1591_; 
lean_dec_ref(v_env_1588_);
lean_dec(v_declHint_1583_);
v___x_1591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1591_, 0, v_msg_1582_);
return v___x_1591_;
}
else
{
lean_object* v___x_1592_; uint8_t v___x_1593_; 
lean_inc_ref(v_env_1588_);
v___x_1592_ = l_Lean_Environment_setExporting(v_env_1588_, v___x_1589_);
lean_inc(v_declHint_1583_);
lean_inc_ref(v___x_1592_);
v___x_1593_ = l_Lean_Environment_contains(v___x_1592_, v_declHint_1583_, v_isExporting_1590_);
if (v___x_1593_ == 0)
{
lean_object* v___x_1594_; 
lean_dec_ref(v___x_1592_);
lean_dec_ref(v_env_1588_);
lean_dec(v_declHint_1583_);
v___x_1594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1594_, 0, v_msg_1582_);
return v___x_1594_;
}
else
{
lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v_c_1600_; lean_object* v___x_1601_; 
v___x_1595_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__2);
v___x_1596_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__5);
v___x_1597_ = l_Lean_Options_empty;
v___x_1598_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1598_, 0, v___x_1592_);
lean_ctor_set(v___x_1598_, 1, v___x_1595_);
lean_ctor_set(v___x_1598_, 2, v___x_1596_);
lean_ctor_set(v___x_1598_, 3, v___x_1597_);
lean_inc(v_declHint_1583_);
v___x_1599_ = l_Lean_MessageData_ofConstName(v_declHint_1583_, v___x_1589_);
v_c_1600_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1600_, 0, v___x_1598_);
lean_ctor_set(v_c_1600_, 1, v___x_1599_);
v___x_1601_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1588_, v_declHint_1583_);
if (lean_obj_tag(v___x_1601_) == 0)
{
lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; 
lean_dec_ref(v_env_1588_);
lean_dec(v_declHint_1583_);
v___x_1602_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__7);
v___x_1603_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1603_, 0, v___x_1602_);
lean_ctor_set(v___x_1603_, 1, v_c_1600_);
v___x_1604_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__9);
v___x_1605_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1605_, 0, v___x_1603_);
lean_ctor_set(v___x_1605_, 1, v___x_1604_);
v___x_1606_ = l_Lean_MessageData_note(v___x_1605_);
v___x_1607_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1607_, 0, v_msg_1582_);
lean_ctor_set(v___x_1607_, 1, v___x_1606_);
v___x_1608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1608_, 0, v___x_1607_);
return v___x_1608_;
}
else
{
lean_object* v_val_1609_; lean_object* v___x_1611_; uint8_t v_isShared_1612_; uint8_t v_isSharedCheck_1643_; 
v_val_1609_ = lean_ctor_get(v___x_1601_, 0);
v_isSharedCheck_1643_ = !lean_is_exclusive(v___x_1601_);
if (v_isSharedCheck_1643_ == 0)
{
v___x_1611_ = v___x_1601_;
v_isShared_1612_ = v_isSharedCheck_1643_;
goto v_resetjp_1610_;
}
else
{
lean_inc(v_val_1609_);
lean_dec(v___x_1601_);
v___x_1611_ = lean_box(0);
v_isShared_1612_ = v_isSharedCheck_1643_;
goto v_resetjp_1610_;
}
v_resetjp_1610_:
{
lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v_mod_1615_; uint8_t v___x_1616_; 
v___x_1613_ = l_Lean_Environment_header(v_env_1588_);
lean_dec_ref(v_env_1588_);
v___x_1614_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1613_);
v_mod_1615_ = lean_array_get(v___x_1586_, v___x_1614_, v_val_1609_);
lean_dec(v_val_1609_);
lean_dec_ref(v___x_1614_);
v___x_1616_ = l_Lean_isPrivateName(v_declHint_1583_);
lean_dec(v_declHint_1583_);
if (v___x_1616_ == 0)
{
lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1628_; 
v___x_1617_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__11);
v___x_1618_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1618_, 0, v___x_1617_);
lean_ctor_set(v___x_1618_, 1, v_c_1600_);
v___x_1619_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__13);
v___x_1620_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1620_, 0, v___x_1618_);
lean_ctor_set(v___x_1620_, 1, v___x_1619_);
v___x_1621_ = l_Lean_MessageData_ofName(v_mod_1615_);
v___x_1622_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1622_, 0, v___x_1620_);
lean_ctor_set(v___x_1622_, 1, v___x_1621_);
v___x_1623_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__15);
v___x_1624_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1624_, 0, v___x_1622_);
lean_ctor_set(v___x_1624_, 1, v___x_1623_);
v___x_1625_ = l_Lean_MessageData_note(v___x_1624_);
v___x_1626_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1626_, 0, v_msg_1582_);
lean_ctor_set(v___x_1626_, 1, v___x_1625_);
if (v_isShared_1612_ == 0)
{
lean_ctor_set_tag(v___x_1611_, 0);
lean_ctor_set(v___x_1611_, 0, v___x_1626_);
v___x_1628_ = v___x_1611_;
goto v_reusejp_1627_;
}
else
{
lean_object* v_reuseFailAlloc_1629_; 
v_reuseFailAlloc_1629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1629_, 0, v___x_1626_);
v___x_1628_ = v_reuseFailAlloc_1629_;
goto v_reusejp_1627_;
}
v_reusejp_1627_:
{
return v___x_1628_;
}
}
else
{
lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1641_; 
v___x_1630_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__7);
v___x_1631_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1631_, 0, v___x_1630_);
lean_ctor_set(v___x_1631_, 1, v_c_1600_);
v___x_1632_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__17);
v___x_1633_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1633_, 0, v___x_1631_);
lean_ctor_set(v___x_1633_, 1, v___x_1632_);
v___x_1634_ = l_Lean_MessageData_ofName(v_mod_1615_);
v___x_1635_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1635_, 0, v___x_1633_);
lean_ctor_set(v___x_1635_, 1, v___x_1634_);
v___x_1636_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__19);
v___x_1637_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1637_, 0, v___x_1635_);
lean_ctor_set(v___x_1637_, 1, v___x_1636_);
v___x_1638_ = l_Lean_MessageData_note(v___x_1637_);
v___x_1639_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1639_, 0, v_msg_1582_);
lean_ctor_set(v___x_1639_, 1, v___x_1638_);
if (v_isShared_1612_ == 0)
{
lean_ctor_set_tag(v___x_1611_, 0);
lean_ctor_set(v___x_1611_, 0, v___x_1639_);
v___x_1641_ = v___x_1611_;
goto v_reusejp_1640_;
}
else
{
lean_object* v_reuseFailAlloc_1642_; 
v_reuseFailAlloc_1642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1642_, 0, v___x_1639_);
v___x_1641_ = v_reuseFailAlloc_1642_;
goto v_reusejp_1640_;
}
v_reusejp_1640_:
{
return v___x_1641_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1644_; 
lean_dec_ref(v_env_1588_);
lean_dec(v_declHint_1583_);
v___x_1644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1644_, 0, v_msg_1582_);
return v___x_1644_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___boxed(lean_object* v_msg_1645_, lean_object* v_declHint_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_){
_start:
{
lean_object* v_res_1649_; 
v_res_1649_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg(v_msg_1645_, v_declHint_1646_, v___y_1647_);
lean_dec(v___y_1647_);
return v_res_1649_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8(lean_object* v_msg_1650_, lean_object* v_declHint_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_){
_start:
{
lean_object* v___x_1657_; lean_object* v_a_1658_; lean_object* v___x_1660_; uint8_t v_isShared_1661_; uint8_t v_isSharedCheck_1667_; 
v___x_1657_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg(v_msg_1650_, v_declHint_1651_, v___y_1655_);
v_a_1658_ = lean_ctor_get(v___x_1657_, 0);
v_isSharedCheck_1667_ = !lean_is_exclusive(v___x_1657_);
if (v_isSharedCheck_1667_ == 0)
{
v___x_1660_ = v___x_1657_;
v_isShared_1661_ = v_isSharedCheck_1667_;
goto v_resetjp_1659_;
}
else
{
lean_inc(v_a_1658_);
lean_dec(v___x_1657_);
v___x_1660_ = lean_box(0);
v_isShared_1661_ = v_isSharedCheck_1667_;
goto v_resetjp_1659_;
}
v_resetjp_1659_:
{
lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1665_; 
v___x_1662_ = l_Lean_unknownIdentifierMessageTag;
v___x_1663_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1663_, 0, v___x_1662_);
lean_ctor_set(v___x_1663_, 1, v_a_1658_);
if (v_isShared_1661_ == 0)
{
lean_ctor_set(v___x_1660_, 0, v___x_1663_);
v___x_1665_ = v___x_1660_;
goto v_reusejp_1664_;
}
else
{
lean_object* v_reuseFailAlloc_1666_; 
v_reuseFailAlloc_1666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1666_, 0, v___x_1663_);
v___x_1665_ = v_reuseFailAlloc_1666_;
goto v_reusejp_1664_;
}
v_reusejp_1664_:
{
return v___x_1665_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8___boxed(lean_object* v_msg_1668_, lean_object* v_declHint_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_){
_start:
{
lean_object* v_res_1675_; 
v_res_1675_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8(v_msg_1668_, v_declHint_1669_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_);
lean_dec(v___y_1673_);
lean_dec_ref(v___y_1672_);
lean_dec(v___y_1671_);
lean_dec_ref(v___y_1670_);
return v_res_1675_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7___redArg(lean_object* v_ref_1676_, lean_object* v_msg_1677_, lean_object* v_declHint_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_){
_start:
{
lean_object* v___x_1684_; lean_object* v_a_1685_; lean_object* v___x_1686_; 
v___x_1684_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8(v_msg_1677_, v_declHint_1678_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_);
v_a_1685_ = lean_ctor_get(v___x_1684_, 0);
lean_inc(v_a_1685_);
lean_dec_ref(v___x_1684_);
v___x_1686_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__9___redArg(v_ref_1676_, v_a_1685_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_);
return v___x_1686_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7___redArg___boxed(lean_object* v_ref_1687_, lean_object* v_msg_1688_, lean_object* v_declHint_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_){
_start:
{
lean_object* v_res_1695_; 
v_res_1695_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7___redArg(v_ref_1687_, v_msg_1688_, v_declHint_1689_, v___y_1690_, v___y_1691_, v___y_1692_, v___y_1693_);
lean_dec(v___y_1693_);
lean_dec_ref(v___y_1692_);
lean_dec(v___y_1691_);
lean_dec_ref(v___y_1690_);
lean_dec(v_ref_1687_);
return v_res_1695_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_1697_; lean_object* v___x_1698_; 
v___x_1697_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3___redArg___closed__0));
v___x_1698_ = l_Lean_stringToMessageData(v___x_1697_);
return v___x_1698_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_1700_; lean_object* v___x_1701_; 
v___x_1700_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3___redArg___closed__2));
v___x_1701_ = l_Lean_stringToMessageData(v___x_1700_);
return v___x_1701_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3___redArg(lean_object* v_ref_1702_, lean_object* v_constName_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_){
_start:
{
lean_object* v___x_1709_; uint8_t v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; 
v___x_1709_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3___redArg___closed__1);
v___x_1710_ = 0;
lean_inc(v_constName_1703_);
v___x_1711_ = l_Lean_MessageData_ofConstName(v_constName_1703_, v___x_1710_);
v___x_1712_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1712_, 0, v___x_1709_);
lean_ctor_set(v___x_1712_, 1, v___x_1711_);
v___x_1713_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3___redArg___closed__3);
v___x_1714_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1714_, 0, v___x_1712_);
lean_ctor_set(v___x_1714_, 1, v___x_1713_);
v___x_1715_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7___redArg(v_ref_1702_, v___x_1714_, v_constName_1703_, v___y_1704_, v___y_1705_, v___y_1706_, v___y_1707_);
return v___x_1715_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_ref_1716_, lean_object* v_constName_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_){
_start:
{
lean_object* v_res_1723_; 
v_res_1723_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3___redArg(v_ref_1716_, v_constName_1717_, v___y_1718_, v___y_1719_, v___y_1720_, v___y_1721_);
lean_dec(v___y_1721_);
lean_dec_ref(v___y_1720_);
lean_dec(v___y_1719_);
lean_dec_ref(v___y_1718_);
lean_dec(v_ref_1716_);
return v_res_1723_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0___redArg(lean_object* v_constName_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_){
_start:
{
lean_object* v_ref_1730_; lean_object* v___x_1731_; 
v_ref_1730_ = lean_ctor_get(v___y_1727_, 2);
v___x_1731_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3___redArg(v_ref_1730_, v_constName_1724_, v___y_1725_, v___y_1726_, v___y_1727_, v___y_1728_);
return v___x_1731_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0___redArg___boxed(lean_object* v_constName_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_){
_start:
{
lean_object* v_res_1738_; 
v_res_1738_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0___redArg(v_constName_1732_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_);
lean_dec(v___y_1736_);
lean_dec_ref(v___y_1735_);
lean_dec(v___y_1734_);
lean_dec_ref(v___y_1733_);
return v_res_1738_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0(lean_object* v_constName_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_){
_start:
{
lean_object* v___x_1745_; lean_object* v_env_1746_; uint8_t v___x_1747_; lean_object* v___x_1748_; 
v___x_1745_ = lean_st_ref_get(v___y_1743_);
v_env_1746_ = lean_ctor_get(v___x_1745_, 0);
lean_inc_ref(v_env_1746_);
lean_dec(v___x_1745_);
v___x_1747_ = 0;
lean_inc(v_constName_1739_);
v___x_1748_ = l_Lean_Environment_find_x3f(v_env_1746_, v_constName_1739_, v___x_1747_);
if (lean_obj_tag(v___x_1748_) == 0)
{
lean_object* v___x_1749_; 
v___x_1749_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0___redArg(v_constName_1739_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_);
return v___x_1749_;
}
else
{
lean_object* v_val_1750_; lean_object* v___x_1752_; uint8_t v_isShared_1753_; uint8_t v_isSharedCheck_1757_; 
lean_dec(v_constName_1739_);
v_val_1750_ = lean_ctor_get(v___x_1748_, 0);
v_isSharedCheck_1757_ = !lean_is_exclusive(v___x_1748_);
if (v_isSharedCheck_1757_ == 0)
{
v___x_1752_ = v___x_1748_;
v_isShared_1753_ = v_isSharedCheck_1757_;
goto v_resetjp_1751_;
}
else
{
lean_inc(v_val_1750_);
lean_dec(v___x_1748_);
v___x_1752_ = lean_box(0);
v_isShared_1753_ = v_isSharedCheck_1757_;
goto v_resetjp_1751_;
}
v_resetjp_1751_:
{
lean_object* v___x_1755_; 
if (v_isShared_1753_ == 0)
{
lean_ctor_set_tag(v___x_1752_, 0);
v___x_1755_ = v___x_1752_;
goto v_reusejp_1754_;
}
else
{
lean_object* v_reuseFailAlloc_1756_; 
v_reuseFailAlloc_1756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1756_, 0, v_val_1750_);
v___x_1755_ = v_reuseFailAlloc_1756_;
goto v_reusejp_1754_;
}
v_reusejp_1754_:
{
return v___x_1755_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0___boxed(lean_object* v_constName_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_){
_start:
{
lean_object* v_res_1764_; 
v_res_1764_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0(v_constName_1758_, v___y_1759_, v___y_1760_, v___y_1761_, v___y_1762_);
lean_dec(v___y_1762_);
lean_dec_ref(v___y_1761_);
lean_dec(v___y_1760_);
lean_dec_ref(v___y_1759_);
return v_res_1764_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp(lean_object* v_univs_1765_, lean_object* v_params_1766_, lean_object* v_idxs_1767_, lean_object* v_c_1768_, lean_object* v_a_1769_, lean_object* v_a_1770_, lean_object* v_a_1771_, lean_object* v_a_1772_){
_start:
{
lean_object* v___f_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; 
lean_inc(v_params_1766_);
v___f_1774_ = lean_alloc_closure((void*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1774_, 0, v_params_1766_);
v___x_1775_ = l_Lean_instInhabitedExpr;
v___x_1776_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0(v_c_1768_, v_a_1769_, v_a_1770_, v_a_1771_, v_a_1772_);
if (lean_obj_tag(v___x_1776_) == 0)
{
lean_object* v_a_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___f_1780_; lean_object* v___x_1781_; uint8_t v___x_1782_; lean_object* v___x_1783_; 
v_a_1777_ = lean_ctor_get(v___x_1776_, 0);
lean_inc(v_a_1777_);
lean_dec_ref_known(v___x_1776_, 1);
v___x_1778_ = l_Lean_ConstantInfo_instantiateTypeLevelParams(v_a_1777_, v_univs_1765_);
lean_dec(v_a_1777_);
v___x_1779_ = l_List_lengthTR___redArg(v_params_1766_);
lean_dec(v_params_1766_);
lean_inc(v___x_1779_);
v___f_1780_ = lean_alloc_closure((void*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__1___boxed), 10, 3);
lean_closure_set(v___f_1780_, 0, v___x_1779_);
lean_closure_set(v___f_1780_, 1, v_idxs_1767_);
lean_closure_set(v___f_1780_, 2, v___x_1775_);
v___x_1781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1781_, 0, v___x_1779_);
v___x_1782_ = 0;
v___x_1783_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__4___redArg(v___x_1778_, v___x_1781_, v___f_1774_, v___x_1782_, v___x_1782_, v_a_1769_, v_a_1770_, v_a_1771_, v_a_1772_);
if (lean_obj_tag(v___x_1783_) == 0)
{
lean_object* v_a_1784_; lean_object* v___x_1785_; 
v_a_1784_ = lean_ctor_get(v___x_1783_, 0);
lean_inc(v_a_1784_);
lean_dec_ref_known(v___x_1783_, 1);
v___x_1785_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__5___redArg(v_a_1784_, v___f_1780_, v___x_1782_, v_a_1769_, v_a_1770_, v_a_1771_, v_a_1772_);
return v___x_1785_;
}
else
{
lean_object* v_a_1786_; lean_object* v___x_1788_; uint8_t v_isShared_1789_; uint8_t v_isSharedCheck_1793_; 
lean_dec_ref(v___f_1780_);
v_a_1786_ = lean_ctor_get(v___x_1783_, 0);
v_isSharedCheck_1793_ = !lean_is_exclusive(v___x_1783_);
if (v_isSharedCheck_1793_ == 0)
{
v___x_1788_ = v___x_1783_;
v_isShared_1789_ = v_isSharedCheck_1793_;
goto v_resetjp_1787_;
}
else
{
lean_inc(v_a_1786_);
lean_dec(v___x_1783_);
v___x_1788_ = lean_box(0);
v_isShared_1789_ = v_isSharedCheck_1793_;
goto v_resetjp_1787_;
}
v_resetjp_1787_:
{
lean_object* v___x_1791_; 
if (v_isShared_1789_ == 0)
{
v___x_1791_ = v___x_1788_;
goto v_reusejp_1790_;
}
else
{
lean_object* v_reuseFailAlloc_1792_; 
v_reuseFailAlloc_1792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1792_, 0, v_a_1786_);
v___x_1791_ = v_reuseFailAlloc_1792_;
goto v_reusejp_1790_;
}
v_reusejp_1790_:
{
return v___x_1791_;
}
}
}
}
else
{
lean_object* v_a_1794_; lean_object* v___x_1796_; uint8_t v_isShared_1797_; uint8_t v_isSharedCheck_1801_; 
lean_dec_ref(v___f_1774_);
lean_dec(v_idxs_1767_);
lean_dec(v_params_1766_);
lean_dec(v_univs_1765_);
v_a_1794_ = lean_ctor_get(v___x_1776_, 0);
v_isSharedCheck_1801_ = !lean_is_exclusive(v___x_1776_);
if (v_isSharedCheck_1801_ == 0)
{
v___x_1796_ = v___x_1776_;
v_isShared_1797_ = v_isSharedCheck_1801_;
goto v_resetjp_1795_;
}
else
{
lean_inc(v_a_1794_);
lean_dec(v___x_1776_);
v___x_1796_ = lean_box(0);
v_isShared_1797_ = v_isSharedCheck_1801_;
goto v_resetjp_1795_;
}
v_resetjp_1795_:
{
lean_object* v___x_1799_; 
if (v_isShared_1797_ == 0)
{
v___x_1799_ = v___x_1796_;
goto v_reusejp_1798_;
}
else
{
lean_object* v_reuseFailAlloc_1800_; 
v_reuseFailAlloc_1800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1800_, 0, v_a_1794_);
v___x_1799_ = v_reuseFailAlloc_1800_;
goto v_reusejp_1798_;
}
v_reusejp_1798_:
{
return v___x_1799_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___boxed(lean_object* v_univs_1802_, lean_object* v_params_1803_, lean_object* v_idxs_1804_, lean_object* v_c_1805_, lean_object* v_a_1806_, lean_object* v_a_1807_, lean_object* v_a_1808_, lean_object* v_a_1809_, lean_object* v_a_1810_){
_start:
{
lean_object* v_res_1811_; 
v_res_1811_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp(v_univs_1802_, v_params_1803_, v_idxs_1804_, v_c_1805_, v_a_1806_, v_a_1807_, v_a_1808_, v_a_1809_);
lean_dec(v_a_1809_);
lean_dec_ref(v_a_1808_);
lean_dec(v_a_1807_);
lean_dec_ref(v_a_1806_);
return v_res_1811_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0(lean_object* v_00_u03b1_1812_, lean_object* v_constName_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_){
_start:
{
lean_object* v___x_1819_; 
v___x_1819_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0___redArg(v_constName_1813_, v___y_1814_, v___y_1815_, v___y_1816_, v___y_1817_);
return v___x_1819_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1820_, lean_object* v_constName_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_){
_start:
{
lean_object* v_res_1827_; 
v_res_1827_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0(v_00_u03b1_1820_, v_constName_1821_, v___y_1822_, v___y_1823_, v___y_1824_, v___y_1825_);
lean_dec(v___y_1825_);
lean_dec_ref(v___y_1824_);
lean_dec(v___y_1823_);
lean_dec_ref(v___y_1822_);
return v_res_1827_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3(lean_object* v_00_u03b1_1828_, lean_object* v_ref_1829_, lean_object* v_constName_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_){
_start:
{
lean_object* v___x_1836_; 
v___x_1836_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3___redArg(v_ref_1829_, v_constName_1830_, v___y_1831_, v___y_1832_, v___y_1833_, v___y_1834_);
return v___x_1836_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b1_1837_, lean_object* v_ref_1838_, lean_object* v_constName_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_){
_start:
{
lean_object* v_res_1845_; 
v_res_1845_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3(v_00_u03b1_1837_, v_ref_1838_, v_constName_1839_, v___y_1840_, v___y_1841_, v___y_1842_, v___y_1843_);
lean_dec(v___y_1843_);
lean_dec_ref(v___y_1842_);
lean_dec(v___y_1841_);
lean_dec_ref(v___y_1840_);
lean_dec(v_ref_1838_);
return v_res_1845_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7(lean_object* v_00_u03b1_1846_, lean_object* v_ref_1847_, lean_object* v_msg_1848_, lean_object* v_declHint_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_){
_start:
{
lean_object* v___x_1855_; 
v___x_1855_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7___redArg(v_ref_1847_, v_msg_1848_, v_declHint_1849_, v___y_1850_, v___y_1851_, v___y_1852_, v___y_1853_);
return v___x_1855_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7___boxed(lean_object* v_00_u03b1_1856_, lean_object* v_ref_1857_, lean_object* v_msg_1858_, lean_object* v_declHint_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_){
_start:
{
lean_object* v_res_1865_; 
v_res_1865_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7(v_00_u03b1_1856_, v_ref_1857_, v_msg_1858_, v_declHint_1859_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_);
lean_dec(v___y_1863_);
lean_dec_ref(v___y_1862_);
lean_dec(v___y_1861_);
lean_dec_ref(v___y_1860_);
lean_dec(v_ref_1857_);
return v_res_1865_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9(lean_object* v_msg_1866_, lean_object* v_declHint_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_){
_start:
{
lean_object* v___x_1873_; 
v___x_1873_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg(v_msg_1866_, v_declHint_1867_, v___y_1871_);
return v___x_1873_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___boxed(lean_object* v_msg_1874_, lean_object* v_declHint_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_){
_start:
{
lean_object* v_res_1881_; 
v_res_1881_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9(v_msg_1874_, v_declHint_1875_, v___y_1876_, v___y_1877_, v___y_1878_, v___y_1879_);
lean_dec(v___y_1879_);
lean_dec_ref(v___y_1878_);
lean_dec(v___y_1877_);
lean_dec_ref(v___y_1876_);
return v_res_1881_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__9(lean_object* v_00_u03b1_1882_, lean_object* v_ref_1883_, lean_object* v_msg_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_){
_start:
{
lean_object* v___x_1890_; 
v___x_1890_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__9___redArg(v_ref_1883_, v_msg_1884_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1888_);
return v___x_1890_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__9___boxed(lean_object* v_00_u03b1_1891_, lean_object* v_ref_1892_, lean_object* v_msg_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_){
_start:
{
lean_object* v_res_1899_; 
v_res_1899_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__9(v_00_u03b1_1891_, v_ref_1892_, v_msg_1893_, v___y_1894_, v___y_1895_, v___y_1896_, v___y_1897_);
lean_dec(v___y_1897_);
lean_dec_ref(v___y_1896_);
lean_dec(v___y_1895_);
lean_dec_ref(v___y_1894_);
lean_dec(v_ref_1892_);
return v_res_1899_;
}
}
static lean_object* _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__1___closed__5(void){
_start:
{
lean_object* v___x_1913_; 
v___x_1913_ = l_Array_mkArray0___redArg();
return v___x_1913_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__1(lean_object* v___y_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_){
_start:
{
lean_object* v_ref_1923_; uint8_t v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; 
v_ref_1923_ = lean_ctor_get(v___y_1920_, 2);
v___x_1924_ = 0;
v___x_1925_ = l_Lean_SourceInfo_fromRef(v_ref_1923_, v___x_1924_);
v___x_1926_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__1___closed__1));
v___x_1927_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__1___closed__2));
lean_inc_n(v___x_1925_, 3);
v___x_1928_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1928_, 0, v___x_1925_);
lean_ctor_set(v___x_1928_, 1, v___x_1927_);
v___x_1929_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__1___closed__4));
v___x_1930_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__10));
v___x_1931_ = lean_obj_once(&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__1___closed__5, &l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__1___closed__5_once, _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__1___closed__5);
v___x_1932_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1932_, 0, v___x_1925_);
lean_ctor_set(v___x_1932_, 1, v___x_1930_);
lean_ctor_set(v___x_1932_, 2, v___x_1931_);
v___x_1933_ = l_Lean_Syntax_node1(v___x_1925_, v___x_1929_, v___x_1932_);
v___x_1934_ = l_Lean_Syntax_node2(v___x_1925_, v___x_1926_, v___x_1928_, v___x_1933_);
v___x_1935_ = l_Lean_Elab_Tactic_evalTactic(v___x_1934_, v___y_1914_, v___y_1915_, v___y_1916_, v___y_1917_, v___y_1918_, v___y_1919_, v___y_1920_, v___y_1921_);
return v___x_1935_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__1___boxed(lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_){
_start:
{
lean_object* v_res_1945_; 
v_res_1945_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__1(v___y_1936_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_, v___y_1943_);
lean_dec(v___y_1943_);
lean_dec_ref(v___y_1942_);
lean_dec(v___y_1941_);
lean_dec_ref(v___y_1940_);
lean_dec(v___y_1939_);
lean_dec_ref(v___y_1938_);
lean_dec(v___y_1937_);
lean_dec_ref(v___y_1936_);
return v_res_1945_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__0(uint8_t v_isZero_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_){
_start:
{
lean_object* v_ref_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; 
v_ref_1956_ = lean_ctor_get(v___y_1953_, 2);
v___x_1957_ = l_Lean_SourceInfo_fromRef(v_ref_1956_, v_isZero_1946_);
v___x_1958_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__1___closed__1));
v___x_1959_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__1___closed__2));
lean_inc_n(v___x_1957_, 3);
v___x_1960_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1960_, 0, v___x_1957_);
lean_ctor_set(v___x_1960_, 1, v___x_1959_);
v___x_1961_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__1___closed__4));
v___x_1962_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__10));
v___x_1963_ = lean_obj_once(&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__1___closed__5, &l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__1___closed__5_once, _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__1___closed__5);
v___x_1964_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1964_, 0, v___x_1957_);
lean_ctor_set(v___x_1964_, 1, v___x_1962_);
lean_ctor_set(v___x_1964_, 2, v___x_1963_);
v___x_1965_ = l_Lean_Syntax_node1(v___x_1957_, v___x_1961_, v___x_1964_);
v___x_1966_ = l_Lean_Syntax_node2(v___x_1957_, v___x_1958_, v___x_1960_, v___x_1965_);
v___x_1967_ = l_Lean_Elab_Tactic_evalTactic(v___x_1966_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_);
return v___x_1967_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__0___boxed(lean_object* v_isZero_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_){
_start:
{
uint8_t v_isZero_boxed_1978_; lean_object* v_res_1979_; 
v_isZero_boxed_1978_ = lean_unbox(v_isZero_1968_);
v_res_1979_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__0(v_isZero_boxed_1978_, v___y_1969_, v___y_1970_, v___y_1971_, v___y_1972_, v___y_1973_, v___y_1974_, v___y_1975_, v___y_1976_);
lean_dec(v___y_1976_);
lean_dec_ref(v___y_1975_);
lean_dec(v___y_1974_);
lean_dec_ref(v___y_1973_);
lean_dec(v___y_1972_);
lean_dec_ref(v___y_1971_);
lean_dec(v___y_1970_);
lean_dec_ref(v___y_1969_);
return v_res_1979_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__2(uint8_t v_isZero_1980_, lean_object* v_x_1981_){
_start:
{
return v_isZero_1980_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__2___boxed(lean_object* v_isZero_1982_, lean_object* v_x_1983_){
_start:
{
uint8_t v_isZero_boxed_1984_; uint8_t v_res_1985_; lean_object* v_r_1986_; 
v_isZero_boxed_1984_ = lean_unbox(v_isZero_1982_);
v_res_1985_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__2(v_isZero_boxed_1984_, v_x_1983_);
lean_dec(v_x_1983_);
v_r_1986_ = lean_box(v_res_1985_);
return v_r_1986_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__3(uint8_t v_isZero_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_){
_start:
{
lean_object* v_ref_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; 
v_ref_1997_ = lean_ctor_get(v___y_1994_, 2);
v___x_1998_ = l_Lean_SourceInfo_fromRef(v_ref_1997_, v_isZero_1987_);
v___x_1999_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__3));
v___x_2000_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__4));
lean_inc_n(v___x_1998_, 9);
v___x_2001_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2001_, 0, v___x_1998_);
lean_ctor_set(v___x_2001_, 1, v___x_1999_);
v___x_2002_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__7));
v___x_2003_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__8));
v___x_2004_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2004_, 0, v___x_1998_);
lean_ctor_set(v___x_2004_, 1, v___x_2003_);
v___x_2005_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__10));
v___x_2006_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__12));
v___x_2007_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__13));
v___x_2008_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2008_, 0, v___x_1998_);
lean_ctor_set(v___x_2008_, 1, v___x_2007_);
v___x_2009_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__14));
v___x_2010_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2010_, 0, v___x_1998_);
lean_ctor_set(v___x_2010_, 1, v___x_2009_);
v___x_2011_ = l_Lean_Syntax_node2(v___x_1998_, v___x_2006_, v___x_2008_, v___x_2010_);
v___x_2012_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__15));
v___x_2013_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2013_, 0, v___x_1998_);
lean_ctor_set(v___x_2013_, 1, v___x_2012_);
lean_inc(v___x_2011_);
v___x_2014_ = l_Lean_Syntax_node3(v___x_1998_, v___x_2005_, v___x_2011_, v___x_2013_, v___x_2011_);
v___x_2015_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__16));
v___x_2016_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2016_, 0, v___x_1998_);
lean_ctor_set(v___x_2016_, 1, v___x_2015_);
v___x_2017_ = l_Lean_Syntax_node3(v___x_1998_, v___x_2002_, v___x_2004_, v___x_2014_, v___x_2016_);
v___x_2018_ = l_Lean_Syntax_node2(v___x_1998_, v___x_2000_, v___x_2001_, v___x_2017_);
v___x_2019_ = l_Lean_Elab_Tactic_evalTactic(v___x_2018_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_, v___y_1994_, v___y_1995_);
return v___x_2019_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__3___boxed(lean_object* v_isZero_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_){
_start:
{
uint8_t v_isZero_boxed_2030_; lean_object* v_res_2031_; 
v_isZero_boxed_2030_ = lean_unbox(v_isZero_2020_);
v_res_2031_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__3(v_isZero_boxed_2030_, v___y_2021_, v___y_2022_, v___y_2023_, v___y_2024_, v___y_2025_, v___y_2026_, v___y_2027_, v___y_2028_);
lean_dec(v___y_2028_);
lean_dec_ref(v___y_2027_);
lean_dec(v___y_2026_);
lean_dec_ref(v___y_2025_);
lean_dec(v___y_2024_);
lean_dec_ref(v___y_2023_);
lean_dec(v___y_2022_);
lean_dec_ref(v___y_2021_);
return v_res_2031_;
}
}
static lean_object* _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___closed__2(void){
_start:
{
lean_object* v___x_2034_; lean_object* v___x_2035_; 
v___x_2034_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___closed__1));
v___x_2035_ = l_Lean_stringToMessageData(v___x_2034_);
return v___x_2035_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor(lean_object* v_mvar_2036_, lean_object* v_n_2037_, lean_object* v_a_2038_, lean_object* v_a_2039_, lean_object* v_a_2040_, lean_object* v_a_2041_){
_start:
{
lean_object* v___y_2044_; lean_object* v___y_2045_; lean_object* v___y_2046_; lean_object* v___y_2047_; lean_object* v_zero_2050_; uint8_t v_isZero_2051_; 
v_zero_2050_ = lean_unsigned_to_nat(0u);
v_isZero_2051_ = lean_nat_dec_eq(v_n_2037_, v_zero_2050_);
if (v_isZero_2051_ == 1)
{
lean_object* v___f_2052_; lean_object* v___f_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; uint8_t v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; 
lean_dec(v_n_2037_);
v___f_2052_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___closed__2));
v___f_2053_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___closed__0));
v___x_2054_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_run___boxed), 9, 2);
lean_closure_set(v___x_2054_, 0, v_mvar_2036_);
lean_closure_set(v___x_2054_, 1, v___f_2053_);
v___x_2055_ = lean_box(0);
v___x_2056_ = lean_box(0);
v___x_2057_ = lean_box(1);
v___x_2058_ = 0;
v___x_2059_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___closed__4));
v___x_2060_ = lean_alloc_ctor(0, 8, 11);
lean_ctor_set(v___x_2060_, 0, v___x_2055_);
lean_ctor_set(v___x_2060_, 1, v___x_2056_);
lean_ctor_set(v___x_2060_, 2, v___x_2055_);
lean_ctor_set(v___x_2060_, 3, v___f_2052_);
lean_ctor_set(v___x_2060_, 4, v___x_2057_);
lean_ctor_set(v___x_2060_, 5, v___x_2057_);
lean_ctor_set(v___x_2060_, 6, v___x_2055_);
lean_ctor_set(v___x_2060_, 7, v___x_2059_);
lean_ctor_set_uint8(v___x_2060_, sizeof(void*)*8, v_isZero_2051_);
lean_ctor_set_uint8(v___x_2060_, sizeof(void*)*8 + 1, v_isZero_2051_);
lean_ctor_set_uint8(v___x_2060_, sizeof(void*)*8 + 2, v_isZero_2051_);
lean_ctor_set_uint8(v___x_2060_, sizeof(void*)*8 + 3, v_isZero_2051_);
lean_ctor_set_uint8(v___x_2060_, sizeof(void*)*8 + 4, v___x_2058_);
lean_ctor_set_uint8(v___x_2060_, sizeof(void*)*8 + 5, v___x_2058_);
lean_ctor_set_uint8(v___x_2060_, sizeof(void*)*8 + 6, v___x_2058_);
lean_ctor_set_uint8(v___x_2060_, sizeof(void*)*8 + 7, v___x_2058_);
lean_ctor_set_uint8(v___x_2060_, sizeof(void*)*8 + 8, v_isZero_2051_);
lean_ctor_set_uint8(v___x_2060_, sizeof(void*)*8 + 9, v___x_2058_);
lean_ctor_set_uint8(v___x_2060_, sizeof(void*)*8 + 10, v_isZero_2051_);
v___x_2061_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___closed__6));
v___x_2062_ = l_Lean_Elab_Term_TermElabM_run___redArg(v___x_2054_, v___x_2060_, v___x_2061_, v_a_2038_, v_a_2039_, v_a_2040_, v_a_2041_);
if (lean_obj_tag(v___x_2062_) == 0)
{
lean_object* v_a_2063_; lean_object* v___x_2065_; uint8_t v_isShared_2066_; uint8_t v_isSharedCheck_2074_; 
v_a_2063_ = lean_ctor_get(v___x_2062_, 0);
v_isSharedCheck_2074_ = !lean_is_exclusive(v___x_2062_);
if (v_isSharedCheck_2074_ == 0)
{
v___x_2065_ = v___x_2062_;
v_isShared_2066_ = v_isSharedCheck_2074_;
goto v_resetjp_2064_;
}
else
{
lean_inc(v_a_2063_);
lean_dec(v___x_2062_);
v___x_2065_ = lean_box(0);
v_isShared_2066_ = v_isSharedCheck_2074_;
goto v_resetjp_2064_;
}
v_resetjp_2064_:
{
lean_object* v_fst_2067_; 
v_fst_2067_ = lean_ctor_get(v_a_2063_, 0);
lean_inc(v_fst_2067_);
lean_dec(v_a_2063_);
if (lean_obj_tag(v_fst_2067_) == 0)
{
lean_object* v___x_2068_; lean_object* v___x_2070_; 
v___x_2068_ = lean_box(0);
if (v_isShared_2066_ == 0)
{
lean_ctor_set(v___x_2065_, 0, v___x_2068_);
v___x_2070_ = v___x_2065_;
goto v_reusejp_2069_;
}
else
{
lean_object* v_reuseFailAlloc_2071_; 
v_reuseFailAlloc_2071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2071_, 0, v___x_2068_);
v___x_2070_ = v_reuseFailAlloc_2071_;
goto v_reusejp_2069_;
}
v_reusejp_2069_:
{
return v___x_2070_;
}
}
else
{
lean_object* v___x_2072_; lean_object* v___x_2073_; 
lean_dec(v_fst_2067_);
lean_del_object(v___x_2065_);
v___x_2072_ = lean_obj_once(&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___closed__2, &l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___closed__2_once, _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___closed__2);
v___x_2073_ = l_Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0___redArg(v___x_2072_, v_a_2038_, v_a_2039_, v_a_2040_, v_a_2041_);
return v___x_2073_;
}
}
}
else
{
lean_object* v_a_2075_; lean_object* v___x_2077_; uint8_t v_isShared_2078_; uint8_t v_isSharedCheck_2082_; 
v_a_2075_ = lean_ctor_get(v___x_2062_, 0);
v_isSharedCheck_2082_ = !lean_is_exclusive(v___x_2062_);
if (v_isSharedCheck_2082_ == 0)
{
v___x_2077_ = v___x_2062_;
v_isShared_2078_ = v_isSharedCheck_2082_;
goto v_resetjp_2076_;
}
else
{
lean_inc(v_a_2075_);
lean_dec(v___x_2062_);
v___x_2077_ = lean_box(0);
v_isShared_2078_ = v_isSharedCheck_2082_;
goto v_resetjp_2076_;
}
v_resetjp_2076_:
{
lean_object* v___x_2080_; 
if (v_isShared_2078_ == 0)
{
v___x_2080_ = v___x_2077_;
goto v_reusejp_2079_;
}
else
{
lean_object* v_reuseFailAlloc_2081_; 
v_reuseFailAlloc_2081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2081_, 0, v_a_2075_);
v___x_2080_ = v_reuseFailAlloc_2081_;
goto v_reusejp_2079_;
}
v_reusejp_2079_:
{
return v___x_2080_;
}
}
}
}
else
{
lean_object* v___x_2083_; lean_object* v___f_2084_; lean_object* v___x_2085_; lean_object* v___f_2086_; lean_object* v___x_2087_; lean_object* v___f_2088_; lean_object* v_one_2089_; lean_object* v_n_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; uint8_t v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; 
v___x_2083_ = lean_box(v_isZero_2051_);
v___f_2084_ = lean_alloc_closure((void*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__0___boxed), 10, 1);
lean_closure_set(v___f_2084_, 0, v___x_2083_);
v___x_2085_ = lean_box(v_isZero_2051_);
v___f_2086_ = lean_alloc_closure((void*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__2___boxed), 2, 1);
lean_closure_set(v___f_2086_, 0, v___x_2085_);
v___x_2087_ = lean_box(v_isZero_2051_);
v___f_2088_ = lean_alloc_closure((void*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__3___boxed), 10, 1);
lean_closure_set(v___f_2088_, 0, v___x_2087_);
v_one_2089_ = lean_unsigned_to_nat(1u);
v_n_2090_ = lean_nat_sub(v_n_2037_, v_one_2089_);
lean_dec(v_n_2037_);
v___x_2091_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_run___boxed), 9, 2);
lean_closure_set(v___x_2091_, 0, v_mvar_2036_);
lean_closure_set(v___x_2091_, 1, v___f_2088_);
v___x_2092_ = lean_box(0);
v___x_2093_ = lean_box(0);
v___x_2094_ = 1;
v___x_2095_ = lean_box(1);
v___x_2096_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___closed__4));
v___x_2097_ = lean_alloc_ctor(0, 8, 11);
lean_ctor_set(v___x_2097_, 0, v___x_2092_);
lean_ctor_set(v___x_2097_, 1, v___x_2093_);
lean_ctor_set(v___x_2097_, 2, v___x_2092_);
lean_ctor_set(v___x_2097_, 3, v___f_2086_);
lean_ctor_set(v___x_2097_, 4, v___x_2095_);
lean_ctor_set(v___x_2097_, 5, v___x_2095_);
lean_ctor_set(v___x_2097_, 6, v___x_2092_);
lean_ctor_set(v___x_2097_, 7, v___x_2096_);
lean_ctor_set_uint8(v___x_2097_, sizeof(void*)*8, v___x_2094_);
lean_ctor_set_uint8(v___x_2097_, sizeof(void*)*8 + 1, v___x_2094_);
lean_ctor_set_uint8(v___x_2097_, sizeof(void*)*8 + 2, v___x_2094_);
lean_ctor_set_uint8(v___x_2097_, sizeof(void*)*8 + 3, v___x_2094_);
lean_ctor_set_uint8(v___x_2097_, sizeof(void*)*8 + 4, v_isZero_2051_);
lean_ctor_set_uint8(v___x_2097_, sizeof(void*)*8 + 5, v_isZero_2051_);
lean_ctor_set_uint8(v___x_2097_, sizeof(void*)*8 + 6, v_isZero_2051_);
lean_ctor_set_uint8(v___x_2097_, sizeof(void*)*8 + 7, v_isZero_2051_);
lean_ctor_set_uint8(v___x_2097_, sizeof(void*)*8 + 8, v___x_2094_);
lean_ctor_set_uint8(v___x_2097_, sizeof(void*)*8 + 9, v_isZero_2051_);
lean_ctor_set_uint8(v___x_2097_, sizeof(void*)*8 + 10, v___x_2094_);
v___x_2098_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___closed__6));
lean_inc_ref(v___x_2097_);
v___x_2099_ = l_Lean_Elab_Term_TermElabM_run___redArg(v___x_2091_, v___x_2097_, v___x_2098_, v_a_2038_, v_a_2039_, v_a_2040_, v_a_2041_);
if (lean_obj_tag(v___x_2099_) == 0)
{
lean_object* v_a_2100_; lean_object* v_fst_2101_; 
v_a_2100_ = lean_ctor_get(v___x_2099_, 0);
lean_inc(v_a_2100_);
lean_dec_ref_known(v___x_2099_, 1);
v_fst_2101_ = lean_ctor_get(v_a_2100_, 0);
lean_inc(v_fst_2101_);
lean_dec(v_a_2100_);
if (lean_obj_tag(v_fst_2101_) == 1)
{
lean_object* v_tail_2102_; 
v_tail_2102_ = lean_ctor_get(v_fst_2101_, 1);
lean_inc(v_tail_2102_);
if (lean_obj_tag(v_tail_2102_) == 1)
{
lean_object* v_tail_2103_; 
v_tail_2103_ = lean_ctor_get(v_tail_2102_, 1);
if (lean_obj_tag(v_tail_2103_) == 0)
{
lean_object* v_head_2104_; lean_object* v_head_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; 
v_head_2104_ = lean_ctor_get(v_fst_2101_, 0);
lean_inc(v_head_2104_);
lean_dec_ref_known(v_fst_2101_, 2);
v_head_2105_ = lean_ctor_get(v_tail_2102_, 0);
lean_inc(v_head_2105_);
lean_dec_ref_known(v_tail_2102_, 2);
v___x_2106_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_run___boxed), 9, 2);
lean_closure_set(v___x_2106_, 0, v_head_2104_);
lean_closure_set(v___x_2106_, 1, v___f_2084_);
v___x_2107_ = l_Lean_Elab_Term_TermElabM_run___redArg(v___x_2106_, v___x_2097_, v___x_2098_, v_a_2038_, v_a_2039_, v_a_2040_, v_a_2041_);
if (lean_obj_tag(v___x_2107_) == 0)
{
lean_object* v_a_2108_; lean_object* v_fst_2109_; 
v_a_2108_ = lean_ctor_get(v___x_2107_, 0);
lean_inc(v_a_2108_);
lean_dec_ref_known(v___x_2107_, 1);
v_fst_2109_ = lean_ctor_get(v_a_2108_, 0);
lean_inc(v_fst_2109_);
lean_dec(v_a_2108_);
if (lean_obj_tag(v_fst_2109_) == 0)
{
v_mvar_2036_ = v_head_2105_;
v_n_2037_ = v_n_2090_;
goto _start;
}
else
{
lean_object* v___x_2111_; lean_object* v___x_2112_; 
lean_dec(v_fst_2109_);
lean_dec(v_head_2105_);
lean_dec(v_n_2090_);
v___x_2111_ = lean_obj_once(&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___closed__2, &l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___closed__2_once, _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___closed__2);
v___x_2112_ = l_Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0___redArg(v___x_2111_, v_a_2038_, v_a_2039_, v_a_2040_, v_a_2041_);
return v___x_2112_;
}
}
else
{
lean_object* v_a_2113_; lean_object* v___x_2115_; uint8_t v_isShared_2116_; uint8_t v_isSharedCheck_2120_; 
lean_dec(v_head_2105_);
lean_dec(v_n_2090_);
v_a_2113_ = lean_ctor_get(v___x_2107_, 0);
v_isSharedCheck_2120_ = !lean_is_exclusive(v___x_2107_);
if (v_isSharedCheck_2120_ == 0)
{
v___x_2115_ = v___x_2107_;
v_isShared_2116_ = v_isSharedCheck_2120_;
goto v_resetjp_2114_;
}
else
{
lean_inc(v_a_2113_);
lean_dec(v___x_2107_);
v___x_2115_ = lean_box(0);
v_isShared_2116_ = v_isSharedCheck_2120_;
goto v_resetjp_2114_;
}
v_resetjp_2114_:
{
lean_object* v___x_2118_; 
if (v_isShared_2116_ == 0)
{
v___x_2118_ = v___x_2115_;
goto v_reusejp_2117_;
}
else
{
lean_object* v_reuseFailAlloc_2119_; 
v_reuseFailAlloc_2119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2119_, 0, v_a_2113_);
v___x_2118_ = v_reuseFailAlloc_2119_;
goto v_reusejp_2117_;
}
v_reusejp_2117_:
{
return v___x_2118_;
}
}
}
}
else
{
lean_dec_ref_known(v_tail_2102_, 2);
lean_dec_ref_known(v_fst_2101_, 2);
lean_dec_ref_known(v___x_2097_, 8);
lean_dec(v_n_2090_);
lean_dec_ref(v___f_2084_);
v___y_2044_ = v_a_2038_;
v___y_2045_ = v_a_2039_;
v___y_2046_ = v_a_2040_;
v___y_2047_ = v_a_2041_;
goto v___jp_2043_;
}
}
else
{
lean_dec_ref_known(v_fst_2101_, 2);
lean_dec(v_tail_2102_);
lean_dec_ref_known(v___x_2097_, 8);
lean_dec(v_n_2090_);
lean_dec_ref(v___f_2084_);
v___y_2044_ = v_a_2038_;
v___y_2045_ = v_a_2039_;
v___y_2046_ = v_a_2040_;
v___y_2047_ = v_a_2041_;
goto v___jp_2043_;
}
}
else
{
lean_dec(v_fst_2101_);
lean_dec_ref_known(v___x_2097_, 8);
lean_dec(v_n_2090_);
lean_dec_ref(v___f_2084_);
v___y_2044_ = v_a_2038_;
v___y_2045_ = v_a_2039_;
v___y_2046_ = v_a_2040_;
v___y_2047_ = v_a_2041_;
goto v___jp_2043_;
}
}
else
{
lean_object* v_a_2121_; lean_object* v___x_2123_; uint8_t v_isShared_2124_; uint8_t v_isSharedCheck_2128_; 
lean_dec_ref_known(v___x_2097_, 8);
lean_dec(v_n_2090_);
lean_dec_ref(v___f_2084_);
v_a_2121_ = lean_ctor_get(v___x_2099_, 0);
v_isSharedCheck_2128_ = !lean_is_exclusive(v___x_2099_);
if (v_isSharedCheck_2128_ == 0)
{
v___x_2123_ = v___x_2099_;
v_isShared_2124_ = v_isSharedCheck_2128_;
goto v_resetjp_2122_;
}
else
{
lean_inc(v_a_2121_);
lean_dec(v___x_2099_);
v___x_2123_ = lean_box(0);
v_isShared_2124_ = v_isSharedCheck_2128_;
goto v_resetjp_2122_;
}
v_resetjp_2122_:
{
lean_object* v___x_2126_; 
if (v_isShared_2124_ == 0)
{
v___x_2126_ = v___x_2123_;
goto v_reusejp_2125_;
}
else
{
lean_object* v_reuseFailAlloc_2127_; 
v_reuseFailAlloc_2127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2127_, 0, v_a_2121_);
v___x_2126_ = v_reuseFailAlloc_2127_;
goto v_reusejp_2125_;
}
v_reusejp_2125_:
{
return v___x_2126_;
}
}
}
}
v___jp_2043_:
{
lean_object* v___x_2048_; lean_object* v___x_2049_; 
v___x_2048_ = lean_obj_once(&l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___closed__1, &l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___closed__1_once, _init_l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___closed__1);
v___x_2049_ = l_Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0___redArg(v___x_2048_, v___y_2044_, v___y_2045_, v___y_2046_, v___y_2047_);
return v___x_2049_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___boxed(lean_object* v_mvar_2129_, lean_object* v_n_2130_, lean_object* v_a_2131_, lean_object* v_a_2132_, lean_object* v_a_2133_, lean_object* v_a_2134_, lean_object* v_a_2135_){
_start:
{
lean_object* v_res_2136_; 
v_res_2136_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor(v_mvar_2129_, v_n_2130_, v_a_2131_, v_a_2132_, v_a_2133_, v_a_2134_);
lean_dec(v_a_2134_);
lean_dec_ref(v_a_2133_);
lean_dec(v_a_2132_);
lean_dec_ref(v_a_2131_);
return v_res_2136_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toCases_spec__0(lean_object* v_a_2137_, lean_object* v_a_2138_){
_start:
{
if (lean_obj_tag(v_a_2137_) == 0)
{
lean_object* v___x_2139_; 
v___x_2139_ = lean_array_to_list(v_a_2138_);
return v___x_2139_;
}
else
{
lean_object* v_head_2140_; lean_object* v_fst_2141_; uint8_t v___x_2142_; 
v_head_2140_ = lean_ctor_get(v_a_2137_, 0);
v_fst_2141_ = lean_ctor_get(v_head_2140_, 0);
v___x_2142_ = lean_unbox(v_fst_2141_);
if (v___x_2142_ == 0)
{
lean_object* v_tail_2143_; 
v_tail_2143_ = lean_ctor_get(v_a_2137_, 1);
lean_inc(v_tail_2143_);
lean_dec_ref_known(v_a_2137_, 2);
v_a_2137_ = v_tail_2143_;
goto _start;
}
else
{
lean_object* v_tail_2145_; lean_object* v_snd_2146_; lean_object* v___x_2147_; 
lean_inc(v_head_2140_);
v_tail_2145_ = lean_ctor_get(v_a_2137_, 1);
lean_inc(v_tail_2145_);
lean_dec_ref_known(v_a_2137_, 2);
v_snd_2146_ = lean_ctor_get(v_head_2140_, 1);
lean_inc(v_snd_2146_);
lean_dec(v_head_2140_);
v___x_2147_ = lean_array_push(v_a_2138_, v_snd_2146_);
v_a_2137_ = v_tail_2145_;
v_a_2138_ = v___x_2147_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toCases_spec__1(lean_object* v_a_2149_, lean_object* v_x_2150_, lean_object* v_x_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_){
_start:
{
if (lean_obj_tag(v_x_2150_) == 0)
{
lean_object* v___x_2157_; lean_object* v___x_2158_; 
v___x_2157_ = l_List_reverse___redArg(v_x_2151_);
v___x_2158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2158_, 0, v___x_2157_);
return v___x_2158_;
}
else
{
lean_object* v_head_2159_; lean_object* v_tail_2160_; lean_object* v___x_2162_; uint8_t v_isShared_2163_; uint8_t v_isSharedCheck_2235_; 
v_head_2159_ = lean_ctor_get(v_x_2150_, 0);
v_tail_2160_ = lean_ctor_get(v_x_2150_, 1);
v_isSharedCheck_2235_ = !lean_is_exclusive(v_x_2150_);
if (v_isSharedCheck_2235_ == 0)
{
v___x_2162_ = v_x_2150_;
v_isShared_2163_ = v_isSharedCheck_2235_;
goto v_resetjp_2161_;
}
else
{
lean_inc(v_tail_2160_);
lean_inc(v_head_2159_);
lean_dec(v_x_2150_);
v___x_2162_ = lean_box(0);
v_isShared_2163_ = v_isSharedCheck_2235_;
goto v_resetjp_2161_;
}
v_resetjp_2161_:
{
lean_object* v___y_2165_; lean_object* v_fst_2179_; lean_object* v_fst_2180_; lean_object* v_snd_2181_; lean_object* v_toInductionSubgoal_2182_; lean_object* v_snd_2183_; lean_object* v_variablesKept_2184_; lean_object* v_neqs_2185_; lean_object* v_mvarId_2186_; lean_object* v_fields_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; 
v_fst_2179_ = lean_ctor_get(v_head_2159_, 0);
v_fst_2180_ = lean_ctor_get(v_fst_2179_, 0);
lean_inc(v_fst_2180_);
v_snd_2181_ = lean_ctor_get(v_fst_2179_, 1);
v_toInductionSubgoal_2182_ = lean_ctor_get(v_snd_2181_, 0);
lean_inc_ref(v_toInductionSubgoal_2182_);
v_snd_2183_ = lean_ctor_get(v_head_2159_, 1);
lean_inc(v_snd_2183_);
lean_dec(v_head_2159_);
v_variablesKept_2184_ = lean_ctor_get(v_fst_2180_, 0);
lean_inc_n(v_variablesKept_2184_, 2);
v_neqs_2185_ = lean_ctor_get(v_fst_2180_, 1);
lean_inc(v_neqs_2185_);
lean_dec(v_fst_2180_);
v_mvarId_2186_ = lean_ctor_get(v_toInductionSubgoal_2182_, 0);
lean_inc(v_mvarId_2186_);
v_fields_2187_ = lean_ctor_get(v_toInductionSubgoal_2182_, 1);
lean_inc_ref_n(v_fields_2187_, 2);
lean_dec_ref(v_toInductionSubgoal_2182_);
v___x_2188_ = l_Lean_instInhabitedExpr;
v___x_2189_ = lean_array_to_list(v_fields_2187_);
v___x_2190_ = l_List_zipWith___at___00List_zip_spec__0(lean_box(0), lean_box(0), v_variablesKept_2184_, v___x_2189_);
v___x_2191_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__1___closed__1));
v___x_2192_ = l_List_filterMapTR_go___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toCases_spec__0(v___x_2190_, v___x_2191_);
v___x_2193_ = lean_array_get_size(v_a_2149_);
v___x_2194_ = lean_unsigned_to_nat(1u);
v___x_2195_ = lean_nat_sub(v___x_2193_, v___x_2194_);
v___x_2196_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select(v_snd_2183_, v___x_2195_, v_mvarId_2186_, v___y_2152_, v___y_2153_, v___y_2154_, v___y_2155_);
if (lean_obj_tag(v___x_2196_) == 0)
{
if (lean_obj_tag(v_neqs_2185_) == 0)
{
lean_object* v_a_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; 
v_a_2197_ = lean_ctor_get(v___x_2196_, 0);
lean_inc(v_a_2197_);
lean_dec_ref_known(v___x_2196_, 1);
v___x_2198_ = l_List_lengthTR___redArg(v_variablesKept_2184_);
lean_dec(v_variablesKept_2184_);
v___x_2199_ = lean_nat_sub(v___x_2198_, v___x_2194_);
lean_dec(v___x_2198_);
v___x_2200_ = lean_array_get(v___x_2188_, v_fields_2187_, v___x_2199_);
lean_dec(v___x_2199_);
lean_dec_ref(v_fields_2187_);
v___x_2201_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_List_init___redArg(v___x_2192_);
v___x_2202_ = l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2(v_a_2197_, v___x_2201_, v___y_2152_, v___y_2153_, v___y_2154_, v___y_2155_);
if (lean_obj_tag(v___x_2202_) == 0)
{
lean_object* v_a_2203_; lean_object* v___x_2204_; 
v_a_2203_ = lean_ctor_get(v___x_2202_, 0);
lean_inc(v_a_2203_);
lean_dec_ref_known(v___x_2202_, 1);
v___x_2204_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1___redArg(v_a_2203_, v___x_2200_, v___y_2153_);
v___y_2165_ = v___x_2204_;
goto v___jp_2164_;
}
else
{
lean_object* v_a_2205_; lean_object* v___x_2207_; uint8_t v_isShared_2208_; uint8_t v_isSharedCheck_2212_; 
lean_dec(v___x_2200_);
lean_del_object(v___x_2162_);
lean_dec(v_tail_2160_);
lean_dec(v_x_2151_);
v_a_2205_ = lean_ctor_get(v___x_2202_, 0);
v_isSharedCheck_2212_ = !lean_is_exclusive(v___x_2202_);
if (v_isSharedCheck_2212_ == 0)
{
v___x_2207_ = v___x_2202_;
v_isShared_2208_ = v_isSharedCheck_2212_;
goto v_resetjp_2206_;
}
else
{
lean_inc(v_a_2205_);
lean_dec(v___x_2202_);
v___x_2207_ = lean_box(0);
v_isShared_2208_ = v_isSharedCheck_2212_;
goto v_resetjp_2206_;
}
v_resetjp_2206_:
{
lean_object* v___x_2210_; 
if (v_isShared_2208_ == 0)
{
v___x_2210_ = v___x_2207_;
goto v_reusejp_2209_;
}
else
{
lean_object* v_reuseFailAlloc_2211_; 
v_reuseFailAlloc_2211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2211_, 0, v_a_2205_);
v___x_2210_ = v_reuseFailAlloc_2211_;
goto v_reusejp_2209_;
}
v_reusejp_2209_:
{
return v___x_2210_;
}
}
}
}
else
{
lean_object* v_a_2213_; lean_object* v_val_2214_; lean_object* v___x_2215_; 
lean_dec_ref(v_fields_2187_);
lean_dec(v_variablesKept_2184_);
v_a_2213_ = lean_ctor_get(v___x_2196_, 0);
lean_inc(v_a_2213_);
lean_dec_ref_known(v___x_2196_, 1);
v_val_2214_ = lean_ctor_get(v_neqs_2185_, 0);
lean_inc(v_val_2214_);
lean_dec_ref_known(v_neqs_2185_, 1);
v___x_2215_ = l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2(v_a_2213_, v___x_2192_, v___y_2152_, v___y_2153_, v___y_2154_, v___y_2155_);
if (lean_obj_tag(v___x_2215_) == 0)
{
lean_object* v_a_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; 
v_a_2216_ = lean_ctor_get(v___x_2215_, 0);
lean_inc(v_a_2216_);
lean_dec_ref_known(v___x_2215_, 1);
v___x_2217_ = lean_nat_sub(v_val_2214_, v___x_2194_);
lean_dec(v_val_2214_);
v___x_2218_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor(v_a_2216_, v___x_2217_, v___y_2152_, v___y_2153_, v___y_2154_, v___y_2155_);
v___y_2165_ = v___x_2218_;
goto v___jp_2164_;
}
else
{
lean_object* v_a_2219_; lean_object* v___x_2221_; uint8_t v_isShared_2222_; uint8_t v_isSharedCheck_2226_; 
lean_dec(v_val_2214_);
lean_del_object(v___x_2162_);
lean_dec(v_tail_2160_);
lean_dec(v_x_2151_);
v_a_2219_ = lean_ctor_get(v___x_2215_, 0);
v_isSharedCheck_2226_ = !lean_is_exclusive(v___x_2215_);
if (v_isSharedCheck_2226_ == 0)
{
v___x_2221_ = v___x_2215_;
v_isShared_2222_ = v_isSharedCheck_2226_;
goto v_resetjp_2220_;
}
else
{
lean_inc(v_a_2219_);
lean_dec(v___x_2215_);
v___x_2221_ = lean_box(0);
v_isShared_2222_ = v_isSharedCheck_2226_;
goto v_resetjp_2220_;
}
v_resetjp_2220_:
{
lean_object* v___x_2224_; 
if (v_isShared_2222_ == 0)
{
v___x_2224_ = v___x_2221_;
goto v_reusejp_2223_;
}
else
{
lean_object* v_reuseFailAlloc_2225_; 
v_reuseFailAlloc_2225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2225_, 0, v_a_2219_);
v___x_2224_ = v_reuseFailAlloc_2225_;
goto v_reusejp_2223_;
}
v_reusejp_2223_:
{
return v___x_2224_;
}
}
}
}
}
else
{
lean_object* v_a_2227_; lean_object* v___x_2229_; uint8_t v_isShared_2230_; uint8_t v_isSharedCheck_2234_; 
lean_dec(v___x_2192_);
lean_dec_ref(v_fields_2187_);
lean_dec(v_neqs_2185_);
lean_dec(v_variablesKept_2184_);
lean_del_object(v___x_2162_);
lean_dec(v_tail_2160_);
lean_dec(v_x_2151_);
v_a_2227_ = lean_ctor_get(v___x_2196_, 0);
v_isSharedCheck_2234_ = !lean_is_exclusive(v___x_2196_);
if (v_isSharedCheck_2234_ == 0)
{
v___x_2229_ = v___x_2196_;
v_isShared_2230_ = v_isSharedCheck_2234_;
goto v_resetjp_2228_;
}
else
{
lean_inc(v_a_2227_);
lean_dec(v___x_2196_);
v___x_2229_ = lean_box(0);
v_isShared_2230_ = v_isSharedCheck_2234_;
goto v_resetjp_2228_;
}
v_resetjp_2228_:
{
lean_object* v___x_2232_; 
if (v_isShared_2230_ == 0)
{
v___x_2232_ = v___x_2229_;
goto v_reusejp_2231_;
}
else
{
lean_object* v_reuseFailAlloc_2233_; 
v_reuseFailAlloc_2233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2233_, 0, v_a_2227_);
v___x_2232_ = v_reuseFailAlloc_2233_;
goto v_reusejp_2231_;
}
v_reusejp_2231_:
{
return v___x_2232_;
}
}
}
v___jp_2164_:
{
if (lean_obj_tag(v___y_2165_) == 0)
{
lean_object* v_a_2166_; lean_object* v___x_2168_; 
v_a_2166_ = lean_ctor_get(v___y_2165_, 0);
lean_inc(v_a_2166_);
lean_dec_ref_known(v___y_2165_, 1);
if (v_isShared_2163_ == 0)
{
lean_ctor_set(v___x_2162_, 1, v_x_2151_);
lean_ctor_set(v___x_2162_, 0, v_a_2166_);
v___x_2168_ = v___x_2162_;
goto v_reusejp_2167_;
}
else
{
lean_object* v_reuseFailAlloc_2170_; 
v_reuseFailAlloc_2170_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2170_, 0, v_a_2166_);
lean_ctor_set(v_reuseFailAlloc_2170_, 1, v_x_2151_);
v___x_2168_ = v_reuseFailAlloc_2170_;
goto v_reusejp_2167_;
}
v_reusejp_2167_:
{
v_x_2150_ = v_tail_2160_;
v_x_2151_ = v___x_2168_;
goto _start;
}
}
else
{
lean_object* v_a_2171_; lean_object* v___x_2173_; uint8_t v_isShared_2174_; uint8_t v_isSharedCheck_2178_; 
lean_del_object(v___x_2162_);
lean_dec(v_tail_2160_);
lean_dec(v_x_2151_);
v_a_2171_ = lean_ctor_get(v___y_2165_, 0);
v_isSharedCheck_2178_ = !lean_is_exclusive(v___y_2165_);
if (v_isSharedCheck_2178_ == 0)
{
v___x_2173_ = v___y_2165_;
v_isShared_2174_ = v_isSharedCheck_2178_;
goto v_resetjp_2172_;
}
else
{
lean_inc(v_a_2171_);
lean_dec(v___y_2165_);
v___x_2173_ = lean_box(0);
v_isShared_2174_ = v_isSharedCheck_2178_;
goto v_resetjp_2172_;
}
v_resetjp_2172_:
{
lean_object* v___x_2176_; 
if (v_isShared_2174_ == 0)
{
v___x_2176_ = v___x_2173_;
goto v_reusejp_2175_;
}
else
{
lean_object* v_reuseFailAlloc_2177_; 
v_reuseFailAlloc_2177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2177_, 0, v_a_2171_);
v___x_2176_ = v_reuseFailAlloc_2177_;
goto v_reusejp_2175_;
}
v_reusejp_2175_:
{
return v___x_2176_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toCases_spec__1___boxed(lean_object* v_a_2236_, lean_object* v_x_2237_, lean_object* v_x_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_){
_start:
{
lean_object* v_res_2244_; 
v_res_2244_ = l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toCases_spec__1(v_a_2236_, v_x_2237_, v_x_2238_, v___y_2239_, v___y_2240_, v___y_2241_, v___y_2242_);
lean_dec(v___y_2242_);
lean_dec_ref(v___y_2241_);
lean_dec(v___y_2240_);
lean_dec_ref(v___y_2239_);
lean_dec_ref(v_a_2236_);
return v_res_2244_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toCases(lean_object* v_mvar_2247_, lean_object* v_shape_2248_, lean_object* v_a_2249_, lean_object* v_a_2250_, lean_object* v_a_2251_, lean_object* v_a_2252_){
_start:
{
uint8_t v___x_2254_; lean_object* v___x_2255_; 
v___x_2254_ = 0;
v___x_2255_ = l_Lean_Meta_intro1Core(v_mvar_2247_, v___x_2254_, v_a_2249_, v_a_2250_, v_a_2251_, v_a_2252_);
if (lean_obj_tag(v___x_2255_) == 0)
{
lean_object* v_a_2256_; lean_object* v_fst_2257_; lean_object* v_snd_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; 
v_a_2256_ = lean_ctor_get(v___x_2255_, 0);
lean_inc(v_a_2256_);
lean_dec_ref_known(v___x_2255_, 1);
v_fst_2257_ = lean_ctor_get(v_a_2256_, 0);
lean_inc(v_fst_2257_);
v_snd_2258_ = lean_ctor_get(v_a_2256_, 1);
lean_inc(v_snd_2258_);
lean_dec(v_a_2256_);
v___x_2259_ = lean_unsigned_to_nat(0u);
v___x_2260_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toCases___closed__0));
v___x_2261_ = lean_box(0);
v___x_2262_ = l_Lean_MVarId_cases(v_snd_2258_, v_fst_2257_, v___x_2260_, v___x_2254_, v___x_2261_, v_a_2249_, v_a_2250_, v_a_2251_, v_a_2252_);
if (lean_obj_tag(v___x_2262_) == 0)
{
lean_object* v_a_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; 
v_a_2263_ = lean_ctor_get(v___x_2262_, 0);
lean_inc_n(v_a_2263_, 2);
lean_dec_ref_known(v___x_2262_, 1);
v___x_2264_ = lean_array_to_list(v_a_2263_);
v___x_2265_ = l_List_zipWith___at___00List_zip_spec__0(lean_box(0), lean_box(0), v_shape_2248_, v___x_2264_);
v___x_2266_ = l_List_zipIdxTR___redArg(v___x_2265_, v___x_2259_);
v___x_2267_ = lean_box(0);
v___x_2268_ = l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toCases_spec__1(v_a_2263_, v___x_2266_, v___x_2267_, v_a_2249_, v_a_2250_, v_a_2251_, v_a_2252_);
lean_dec(v_a_2263_);
if (lean_obj_tag(v___x_2268_) == 0)
{
lean_object* v___x_2270_; uint8_t v_isShared_2271_; uint8_t v_isSharedCheck_2276_; 
v_isSharedCheck_2276_ = !lean_is_exclusive(v___x_2268_);
if (v_isSharedCheck_2276_ == 0)
{
lean_object* v_unused_2277_; 
v_unused_2277_ = lean_ctor_get(v___x_2268_, 0);
lean_dec(v_unused_2277_);
v___x_2270_ = v___x_2268_;
v_isShared_2271_ = v_isSharedCheck_2276_;
goto v_resetjp_2269_;
}
else
{
lean_dec(v___x_2268_);
v___x_2270_ = lean_box(0);
v_isShared_2271_ = v_isSharedCheck_2276_;
goto v_resetjp_2269_;
}
v_resetjp_2269_:
{
lean_object* v___x_2272_; lean_object* v___x_2274_; 
v___x_2272_ = lean_box(0);
if (v_isShared_2271_ == 0)
{
lean_ctor_set(v___x_2270_, 0, v___x_2272_);
v___x_2274_ = v___x_2270_;
goto v_reusejp_2273_;
}
else
{
lean_object* v_reuseFailAlloc_2275_; 
v_reuseFailAlloc_2275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2275_, 0, v___x_2272_);
v___x_2274_ = v_reuseFailAlloc_2275_;
goto v_reusejp_2273_;
}
v_reusejp_2273_:
{
return v___x_2274_;
}
}
}
else
{
lean_object* v_a_2278_; lean_object* v___x_2280_; uint8_t v_isShared_2281_; uint8_t v_isSharedCheck_2285_; 
v_a_2278_ = lean_ctor_get(v___x_2268_, 0);
v_isSharedCheck_2285_ = !lean_is_exclusive(v___x_2268_);
if (v_isSharedCheck_2285_ == 0)
{
v___x_2280_ = v___x_2268_;
v_isShared_2281_ = v_isSharedCheck_2285_;
goto v_resetjp_2279_;
}
else
{
lean_inc(v_a_2278_);
lean_dec(v___x_2268_);
v___x_2280_ = lean_box(0);
v_isShared_2281_ = v_isSharedCheck_2285_;
goto v_resetjp_2279_;
}
v_resetjp_2279_:
{
lean_object* v___x_2283_; 
if (v_isShared_2281_ == 0)
{
v___x_2283_ = v___x_2280_;
goto v_reusejp_2282_;
}
else
{
lean_object* v_reuseFailAlloc_2284_; 
v_reuseFailAlloc_2284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2284_, 0, v_a_2278_);
v___x_2283_ = v_reuseFailAlloc_2284_;
goto v_reusejp_2282_;
}
v_reusejp_2282_:
{
return v___x_2283_;
}
}
}
}
else
{
lean_object* v_a_2286_; lean_object* v___x_2288_; uint8_t v_isShared_2289_; uint8_t v_isSharedCheck_2293_; 
lean_dec(v_shape_2248_);
v_a_2286_ = lean_ctor_get(v___x_2262_, 0);
v_isSharedCheck_2293_ = !lean_is_exclusive(v___x_2262_);
if (v_isSharedCheck_2293_ == 0)
{
v___x_2288_ = v___x_2262_;
v_isShared_2289_ = v_isSharedCheck_2293_;
goto v_resetjp_2287_;
}
else
{
lean_inc(v_a_2286_);
lean_dec(v___x_2262_);
v___x_2288_ = lean_box(0);
v_isShared_2289_ = v_isSharedCheck_2293_;
goto v_resetjp_2287_;
}
v_resetjp_2287_:
{
lean_object* v___x_2291_; 
if (v_isShared_2289_ == 0)
{
v___x_2291_ = v___x_2288_;
goto v_reusejp_2290_;
}
else
{
lean_object* v_reuseFailAlloc_2292_; 
v_reuseFailAlloc_2292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2292_, 0, v_a_2286_);
v___x_2291_ = v_reuseFailAlloc_2292_;
goto v_reusejp_2290_;
}
v_reusejp_2290_:
{
return v___x_2291_;
}
}
}
}
else
{
lean_object* v_a_2294_; lean_object* v___x_2296_; uint8_t v_isShared_2297_; uint8_t v_isSharedCheck_2301_; 
lean_dec(v_shape_2248_);
v_a_2294_ = lean_ctor_get(v___x_2255_, 0);
v_isSharedCheck_2301_ = !lean_is_exclusive(v___x_2255_);
if (v_isSharedCheck_2301_ == 0)
{
v___x_2296_ = v___x_2255_;
v_isShared_2297_ = v_isSharedCheck_2301_;
goto v_resetjp_2295_;
}
else
{
lean_inc(v_a_2294_);
lean_dec(v___x_2255_);
v___x_2296_ = lean_box(0);
v_isShared_2297_ = v_isSharedCheck_2301_;
goto v_resetjp_2295_;
}
v_resetjp_2295_:
{
lean_object* v___x_2299_; 
if (v_isShared_2297_ == 0)
{
v___x_2299_ = v___x_2296_;
goto v_reusejp_2298_;
}
else
{
lean_object* v_reuseFailAlloc_2300_; 
v_reuseFailAlloc_2300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2300_, 0, v_a_2294_);
v___x_2299_ = v_reuseFailAlloc_2300_;
goto v_reusejp_2298_;
}
v_reusejp_2298_:
{
return v___x_2299_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toCases___boxed(lean_object* v_mvar_2302_, lean_object* v_shape_2303_, lean_object* v_a_2304_, lean_object* v_a_2305_, lean_object* v_a_2306_, lean_object* v_a_2307_, lean_object* v_a_2308_){
_start:
{
lean_object* v_res_2309_; 
v_res_2309_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toCases(v_mvar_2302_, v_shape_2303_, v_a_2304_, v_a_2305_, v_a_2306_, v_a_2307_);
lean_dec(v_a_2307_);
lean_dec_ref(v_a_2306_);
lean_dec(v_a_2305_);
lean_dec_ref(v_a_2304_);
return v_res_2309_;
}
}
static lean_object* _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesSum___closed__1(void){
_start:
{
lean_object* v___x_2311_; lean_object* v___x_2312_; 
v___x_2311_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesSum___closed__0));
v___x_2312_ = l_Lean_stringToMessageData(v___x_2311_);
return v___x_2312_;
}
}
static lean_object* _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesSum___closed__3(void){
_start:
{
lean_object* v___x_2314_; lean_object* v___x_2315_; 
v___x_2314_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesSum___closed__2));
v___x_2315_ = l_Lean_stringToMessageData(v___x_2314_);
return v___x_2315_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesSum(lean_object* v_n_2316_, lean_object* v_mvar_2317_, lean_object* v_h_2318_, lean_object* v_a_2319_, lean_object* v_a_2320_, lean_object* v_a_2321_, lean_object* v_a_2322_){
_start:
{
lean_object* v___y_2325_; lean_object* v___y_2326_; lean_object* v___y_2327_; lean_object* v___y_2328_; lean_object* v___y_2332_; lean_object* v___y_2333_; lean_object* v___y_2334_; lean_object* v___y_2335_; lean_object* v_zero_2338_; uint8_t v_isZero_2339_; 
v_zero_2338_ = lean_unsigned_to_nat(0u);
v_isZero_2339_ = lean_nat_dec_eq(v_n_2316_, v_zero_2338_);
if (v_isZero_2339_ == 1)
{
lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; 
v___x_2340_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2340_, 0, v_h_2318_);
lean_ctor_set(v___x_2340_, 1, v_mvar_2317_);
v___x_2341_ = lean_box(0);
v___x_2342_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2342_, 0, v___x_2340_);
lean_ctor_set(v___x_2342_, 1, v___x_2341_);
v___x_2343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2343_, 0, v___x_2342_);
return v___x_2343_;
}
else
{
lean_object* v_one_2344_; lean_object* v_n_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; 
v_one_2344_ = lean_unsigned_to_nat(1u);
v_n_2345_ = lean_nat_sub(v_n_2316_, v_one_2344_);
v___x_2346_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toCases___closed__0));
v___x_2347_ = lean_box(0);
v___x_2348_ = l_Lean_MVarId_cases(v_mvar_2317_, v_h_2318_, v___x_2346_, v_isZero_2339_, v___x_2347_, v_a_2319_, v_a_2320_, v_a_2321_, v_a_2322_);
if (lean_obj_tag(v___x_2348_) == 0)
{
lean_object* v_a_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; uint8_t v___x_2352_; 
v_a_2349_ = lean_ctor_get(v___x_2348_, 0);
lean_inc(v_a_2349_);
lean_dec_ref_known(v___x_2348_, 1);
v___x_2350_ = lean_array_get_size(v_a_2349_);
v___x_2351_ = lean_unsigned_to_nat(2u);
v___x_2352_ = lean_nat_dec_eq(v___x_2350_, v___x_2351_);
if (v___x_2352_ == 0)
{
lean_object* v___x_2353_; lean_object* v___x_2354_; 
lean_dec(v_a_2349_);
lean_dec(v_n_2345_);
v___x_2353_ = lean_obj_once(&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesSum___closed__3, &l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesSum___closed__3_once, _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesSum___closed__3);
v___x_2354_ = l_Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0___redArg(v___x_2353_, v_a_2319_, v_a_2320_, v_a_2321_, v_a_2322_);
return v___x_2354_;
}
else
{
lean_object* v___x_2355_; lean_object* v_toInductionSubgoal_2356_; lean_object* v___x_2358_; uint8_t v_isShared_2359_; uint8_t v_isSharedCheck_2394_; 
v___x_2355_ = lean_array_fget(v_a_2349_, v_zero_2338_);
v_toInductionSubgoal_2356_ = lean_ctor_get(v___x_2355_, 0);
v_isSharedCheck_2394_ = !lean_is_exclusive(v___x_2355_);
if (v_isSharedCheck_2394_ == 0)
{
lean_object* v_unused_2395_; 
v_unused_2395_ = lean_ctor_get(v___x_2355_, 1);
lean_dec(v_unused_2395_);
v___x_2358_ = v___x_2355_;
v_isShared_2359_ = v_isSharedCheck_2394_;
goto v_resetjp_2357_;
}
else
{
lean_inc(v_toInductionSubgoal_2356_);
lean_dec(v___x_2355_);
v___x_2358_ = lean_box(0);
v_isShared_2359_ = v_isSharedCheck_2394_;
goto v_resetjp_2357_;
}
v_resetjp_2357_:
{
lean_object* v_mvarId_2360_; lean_object* v_fields_2361_; lean_object* v___x_2362_; uint8_t v___x_2363_; 
v_mvarId_2360_ = lean_ctor_get(v_toInductionSubgoal_2356_, 0);
lean_inc(v_mvarId_2360_);
v_fields_2361_ = lean_ctor_get(v_toInductionSubgoal_2356_, 1);
lean_inc_ref(v_fields_2361_);
lean_dec_ref(v_toInductionSubgoal_2356_);
v___x_2362_ = lean_array_get_size(v_fields_2361_);
v___x_2363_ = lean_nat_dec_eq(v___x_2362_, v_one_2344_);
if (v___x_2363_ == 0)
{
lean_dec_ref(v_fields_2361_);
lean_dec(v_mvarId_2360_);
lean_del_object(v___x_2358_);
lean_dec(v_a_2349_);
lean_dec(v_n_2345_);
v___y_2332_ = v_a_2319_;
v___y_2333_ = v_a_2320_;
v___y_2334_ = v_a_2321_;
v___y_2335_ = v_a_2322_;
goto v___jp_2331_;
}
else
{
lean_object* v___x_2364_; 
v___x_2364_ = lean_array_fget(v_fields_2361_, v_zero_2338_);
lean_dec_ref(v_fields_2361_);
if (lean_obj_tag(v___x_2364_) == 1)
{
lean_object* v_fvarId_2365_; lean_object* v___x_2366_; lean_object* v_toInductionSubgoal_2367_; lean_object* v___x_2369_; uint8_t v_isShared_2370_; uint8_t v_isSharedCheck_2392_; 
v_fvarId_2365_ = lean_ctor_get(v___x_2364_, 0);
lean_inc(v_fvarId_2365_);
lean_dec_ref_known(v___x_2364_, 1);
v___x_2366_ = lean_array_fget(v_a_2349_, v_one_2344_);
lean_dec(v_a_2349_);
v_toInductionSubgoal_2367_ = lean_ctor_get(v___x_2366_, 0);
v_isSharedCheck_2392_ = !lean_is_exclusive(v___x_2366_);
if (v_isSharedCheck_2392_ == 0)
{
lean_object* v_unused_2393_; 
v_unused_2393_ = lean_ctor_get(v___x_2366_, 1);
lean_dec(v_unused_2393_);
v___x_2369_ = v___x_2366_;
v_isShared_2370_ = v_isSharedCheck_2392_;
goto v_resetjp_2368_;
}
else
{
lean_inc(v_toInductionSubgoal_2367_);
lean_dec(v___x_2366_);
v___x_2369_ = lean_box(0);
v_isShared_2370_ = v_isSharedCheck_2392_;
goto v_resetjp_2368_;
}
v_resetjp_2368_:
{
lean_object* v_mvarId_2371_; lean_object* v_fields_2372_; lean_object* v___x_2373_; uint8_t v___x_2374_; 
v_mvarId_2371_ = lean_ctor_get(v_toInductionSubgoal_2367_, 0);
lean_inc(v_mvarId_2371_);
v_fields_2372_ = lean_ctor_get(v_toInductionSubgoal_2367_, 1);
lean_inc_ref(v_fields_2372_);
lean_dec_ref(v_toInductionSubgoal_2367_);
v___x_2373_ = lean_array_get_size(v_fields_2372_);
v___x_2374_ = lean_nat_dec_eq(v___x_2373_, v_one_2344_);
if (v___x_2374_ == 0)
{
lean_dec_ref(v_fields_2372_);
lean_dec(v_mvarId_2371_);
lean_del_object(v___x_2369_);
lean_dec(v_fvarId_2365_);
lean_dec(v_mvarId_2360_);
lean_del_object(v___x_2358_);
lean_dec(v_n_2345_);
v___y_2325_ = v_a_2319_;
v___y_2326_ = v_a_2320_;
v___y_2327_ = v_a_2321_;
v___y_2328_ = v_a_2322_;
goto v___jp_2324_;
}
else
{
lean_object* v___x_2375_; 
v___x_2375_ = lean_array_fget(v_fields_2372_, v_zero_2338_);
lean_dec_ref(v_fields_2372_);
if (lean_obj_tag(v___x_2375_) == 1)
{
lean_object* v_fvarId_2376_; lean_object* v___x_2377_; 
v_fvarId_2376_ = lean_ctor_get(v___x_2375_, 0);
lean_inc(v_fvarId_2376_);
lean_dec_ref_known(v___x_2375_, 1);
v___x_2377_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesSum(v_n_2345_, v_mvarId_2371_, v_fvarId_2376_, v_a_2319_, v_a_2320_, v_a_2321_, v_a_2322_);
lean_dec(v_n_2345_);
if (lean_obj_tag(v___x_2377_) == 0)
{
lean_object* v_a_2378_; lean_object* v___x_2380_; uint8_t v_isShared_2381_; uint8_t v_isSharedCheck_2391_; 
v_a_2378_ = lean_ctor_get(v___x_2377_, 0);
v_isSharedCheck_2391_ = !lean_is_exclusive(v___x_2377_);
if (v_isSharedCheck_2391_ == 0)
{
v___x_2380_ = v___x_2377_;
v_isShared_2381_ = v_isSharedCheck_2391_;
goto v_resetjp_2379_;
}
else
{
lean_inc(v_a_2378_);
lean_dec(v___x_2377_);
v___x_2380_ = lean_box(0);
v_isShared_2381_ = v_isSharedCheck_2391_;
goto v_resetjp_2379_;
}
v_resetjp_2379_:
{
lean_object* v___x_2383_; 
if (v_isShared_2370_ == 0)
{
lean_ctor_set(v___x_2369_, 1, v_mvarId_2360_);
lean_ctor_set(v___x_2369_, 0, v_fvarId_2365_);
v___x_2383_ = v___x_2369_;
goto v_reusejp_2382_;
}
else
{
lean_object* v_reuseFailAlloc_2390_; 
v_reuseFailAlloc_2390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2390_, 0, v_fvarId_2365_);
lean_ctor_set(v_reuseFailAlloc_2390_, 1, v_mvarId_2360_);
v___x_2383_ = v_reuseFailAlloc_2390_;
goto v_reusejp_2382_;
}
v_reusejp_2382_:
{
lean_object* v___x_2385_; 
if (v_isShared_2359_ == 0)
{
lean_ctor_set_tag(v___x_2358_, 1);
lean_ctor_set(v___x_2358_, 1, v_a_2378_);
lean_ctor_set(v___x_2358_, 0, v___x_2383_);
v___x_2385_ = v___x_2358_;
goto v_reusejp_2384_;
}
else
{
lean_object* v_reuseFailAlloc_2389_; 
v_reuseFailAlloc_2389_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2389_, 0, v___x_2383_);
lean_ctor_set(v_reuseFailAlloc_2389_, 1, v_a_2378_);
v___x_2385_ = v_reuseFailAlloc_2389_;
goto v_reusejp_2384_;
}
v_reusejp_2384_:
{
lean_object* v___x_2387_; 
if (v_isShared_2381_ == 0)
{
lean_ctor_set(v___x_2380_, 0, v___x_2385_);
v___x_2387_ = v___x_2380_;
goto v_reusejp_2386_;
}
else
{
lean_object* v_reuseFailAlloc_2388_; 
v_reuseFailAlloc_2388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2388_, 0, v___x_2385_);
v___x_2387_ = v_reuseFailAlloc_2388_;
goto v_reusejp_2386_;
}
v_reusejp_2386_:
{
return v___x_2387_;
}
}
}
}
}
else
{
lean_del_object(v___x_2369_);
lean_dec(v_fvarId_2365_);
lean_dec(v_mvarId_2360_);
lean_del_object(v___x_2358_);
return v___x_2377_;
}
}
else
{
lean_dec(v___x_2375_);
lean_dec(v_mvarId_2371_);
lean_del_object(v___x_2369_);
lean_dec(v_fvarId_2365_);
lean_dec(v_mvarId_2360_);
lean_del_object(v___x_2358_);
lean_dec(v_n_2345_);
v___y_2325_ = v_a_2319_;
v___y_2326_ = v_a_2320_;
v___y_2327_ = v_a_2321_;
v___y_2328_ = v_a_2322_;
goto v___jp_2324_;
}
}
}
}
else
{
lean_dec(v___x_2364_);
lean_dec(v_mvarId_2360_);
lean_del_object(v___x_2358_);
lean_dec(v_a_2349_);
lean_dec(v_n_2345_);
v___y_2332_ = v_a_2319_;
v___y_2333_ = v_a_2320_;
v___y_2334_ = v_a_2321_;
v___y_2335_ = v_a_2322_;
goto v___jp_2331_;
}
}
}
}
}
else
{
lean_object* v_a_2396_; lean_object* v___x_2398_; uint8_t v_isShared_2399_; uint8_t v_isSharedCheck_2403_; 
lean_dec(v_n_2345_);
v_a_2396_ = lean_ctor_get(v___x_2348_, 0);
v_isSharedCheck_2403_ = !lean_is_exclusive(v___x_2348_);
if (v_isSharedCheck_2403_ == 0)
{
v___x_2398_ = v___x_2348_;
v_isShared_2399_ = v_isSharedCheck_2403_;
goto v_resetjp_2397_;
}
else
{
lean_inc(v_a_2396_);
lean_dec(v___x_2348_);
v___x_2398_ = lean_box(0);
v_isShared_2399_ = v_isSharedCheck_2403_;
goto v_resetjp_2397_;
}
v_resetjp_2397_:
{
lean_object* v___x_2401_; 
if (v_isShared_2399_ == 0)
{
v___x_2401_ = v___x_2398_;
goto v_reusejp_2400_;
}
else
{
lean_object* v_reuseFailAlloc_2402_; 
v_reuseFailAlloc_2402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2402_, 0, v_a_2396_);
v___x_2401_ = v_reuseFailAlloc_2402_;
goto v_reusejp_2400_;
}
v_reusejp_2400_:
{
return v___x_2401_;
}
}
}
}
v___jp_2324_:
{
lean_object* v___x_2329_; lean_object* v___x_2330_; 
v___x_2329_ = lean_obj_once(&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesSum___closed__1, &l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesSum___closed__1_once, _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesSum___closed__1);
v___x_2330_ = l_Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0___redArg(v___x_2329_, v___y_2325_, v___y_2326_, v___y_2327_, v___y_2328_);
return v___x_2330_;
}
v___jp_2331_:
{
lean_object* v___x_2336_; lean_object* v___x_2337_; 
v___x_2336_ = lean_obj_once(&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesSum___closed__1, &l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesSum___closed__1_once, _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesSum___closed__1);
v___x_2337_ = l_Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0___redArg(v___x_2336_, v___y_2332_, v___y_2333_, v___y_2334_, v___y_2335_);
return v___x_2337_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesSum___boxed(lean_object* v_n_2404_, lean_object* v_mvar_2405_, lean_object* v_h_2406_, lean_object* v_a_2407_, lean_object* v_a_2408_, lean_object* v_a_2409_, lean_object* v_a_2410_, lean_object* v_a_2411_){
_start:
{
lean_object* v_res_2412_; 
v_res_2412_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesSum(v_n_2404_, v_mvar_2405_, v_h_2406_, v_a_2407_, v_a_2408_, v_a_2409_, v_a_2410_);
lean_dec(v_a_2410_);
lean_dec_ref(v_a_2409_);
lean_dec(v_a_2408_);
lean_dec_ref(v_a_2407_);
lean_dec(v_n_2404_);
return v_res_2412_;
}
}
static lean_object* _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesProd___closed__1(void){
_start:
{
lean_object* v___x_2414_; lean_object* v___x_2415_; 
v___x_2414_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesProd___closed__0));
v___x_2415_ = l_Lean_stringToMessageData(v___x_2414_);
return v___x_2415_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesProd(lean_object* v_n_2416_, lean_object* v_mvar_2417_, lean_object* v_h_2418_, lean_object* v_a_2419_, lean_object* v_a_2420_, lean_object* v_a_2421_, lean_object* v_a_2422_){
_start:
{
lean_object* v___y_2425_; lean_object* v___y_2426_; lean_object* v___y_2427_; lean_object* v___y_2428_; lean_object* v_zero_2431_; uint8_t v_isZero_2432_; 
v_zero_2431_ = lean_unsigned_to_nat(0u);
v_isZero_2432_ = lean_nat_dec_eq(v_n_2416_, v_zero_2431_);
if (v_isZero_2432_ == 1)
{
lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; 
v___x_2433_ = lean_box(0);
v___x_2434_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2434_, 0, v_h_2418_);
lean_ctor_set(v___x_2434_, 1, v___x_2433_);
v___x_2435_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2435_, 0, v_mvar_2417_);
lean_ctor_set(v___x_2435_, 1, v___x_2434_);
v___x_2436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2436_, 0, v___x_2435_);
return v___x_2436_;
}
else
{
lean_object* v_one_2437_; lean_object* v_n_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; 
v_one_2437_ = lean_unsigned_to_nat(1u);
v_n_2438_ = lean_nat_sub(v_n_2416_, v_one_2437_);
v___x_2439_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toCases___closed__0));
v___x_2440_ = lean_box(0);
v___x_2441_ = l_Lean_MVarId_cases(v_mvar_2417_, v_h_2418_, v___x_2439_, v_isZero_2432_, v___x_2440_, v_a_2419_, v_a_2420_, v_a_2421_, v_a_2422_);
if (lean_obj_tag(v___x_2441_) == 0)
{
lean_object* v_a_2442_; lean_object* v___x_2443_; uint8_t v___x_2444_; 
v_a_2442_ = lean_ctor_get(v___x_2441_, 0);
lean_inc(v_a_2442_);
lean_dec_ref_known(v___x_2441_, 1);
v___x_2443_ = lean_array_get_size(v_a_2442_);
v___x_2444_ = lean_nat_dec_eq(v___x_2443_, v_one_2437_);
if (v___x_2444_ == 0)
{
lean_object* v___x_2445_; lean_object* v___x_2446_; 
lean_dec(v_a_2442_);
lean_dec(v_n_2438_);
v___x_2445_ = lean_obj_once(&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesProd___closed__1, &l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesProd___closed__1_once, _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesProd___closed__1);
v___x_2446_ = l_Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0___redArg(v___x_2445_, v_a_2419_, v_a_2420_, v_a_2421_, v_a_2422_);
return v___x_2446_;
}
else
{
lean_object* v___x_2447_; lean_object* v_toInductionSubgoal_2448_; lean_object* v___x_2450_; uint8_t v_isShared_2451_; uint8_t v_isSharedCheck_2482_; 
v___x_2447_ = lean_array_fget(v_a_2442_, v_zero_2431_);
lean_dec(v_a_2442_);
v_toInductionSubgoal_2448_ = lean_ctor_get(v___x_2447_, 0);
v_isSharedCheck_2482_ = !lean_is_exclusive(v___x_2447_);
if (v_isSharedCheck_2482_ == 0)
{
lean_object* v_unused_2483_; 
v_unused_2483_ = lean_ctor_get(v___x_2447_, 1);
lean_dec(v_unused_2483_);
v___x_2450_ = v___x_2447_;
v_isShared_2451_ = v_isSharedCheck_2482_;
goto v_resetjp_2449_;
}
else
{
lean_inc(v_toInductionSubgoal_2448_);
lean_dec(v___x_2447_);
v___x_2450_ = lean_box(0);
v_isShared_2451_ = v_isSharedCheck_2482_;
goto v_resetjp_2449_;
}
v_resetjp_2449_:
{
lean_object* v_mvarId_2452_; lean_object* v_fields_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; uint8_t v___x_2456_; 
v_mvarId_2452_ = lean_ctor_get(v_toInductionSubgoal_2448_, 0);
lean_inc(v_mvarId_2452_);
v_fields_2453_ = lean_ctor_get(v_toInductionSubgoal_2448_, 1);
lean_inc_ref(v_fields_2453_);
lean_dec_ref(v_toInductionSubgoal_2448_);
v___x_2454_ = lean_array_get_size(v_fields_2453_);
v___x_2455_ = lean_unsigned_to_nat(2u);
v___x_2456_ = lean_nat_dec_eq(v___x_2454_, v___x_2455_);
if (v___x_2456_ == 0)
{
lean_dec_ref(v_fields_2453_);
lean_dec(v_mvarId_2452_);
lean_del_object(v___x_2450_);
lean_dec(v_n_2438_);
v___y_2425_ = v_a_2419_;
v___y_2426_ = v_a_2420_;
v___y_2427_ = v_a_2421_;
v___y_2428_ = v_a_2422_;
goto v___jp_2424_;
}
else
{
lean_object* v___x_2457_; 
v___x_2457_ = lean_array_fget_borrowed(v_fields_2453_, v_zero_2431_);
if (lean_obj_tag(v___x_2457_) == 1)
{
lean_object* v_fvarId_2458_; lean_object* v___x_2459_; 
v_fvarId_2458_ = lean_ctor_get(v___x_2457_, 0);
lean_inc(v_fvarId_2458_);
v___x_2459_ = lean_array_fget(v_fields_2453_, v_one_2437_);
lean_dec_ref(v_fields_2453_);
if (lean_obj_tag(v___x_2459_) == 1)
{
lean_object* v_fvarId_2460_; lean_object* v___x_2461_; 
v_fvarId_2460_ = lean_ctor_get(v___x_2459_, 0);
lean_inc(v_fvarId_2460_);
lean_dec_ref_known(v___x_2459_, 1);
v___x_2461_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesProd(v_n_2438_, v_mvarId_2452_, v_fvarId_2460_, v_a_2419_, v_a_2420_, v_a_2421_, v_a_2422_);
lean_dec(v_n_2438_);
if (lean_obj_tag(v___x_2461_) == 0)
{
lean_object* v_a_2462_; lean_object* v___x_2464_; uint8_t v_isShared_2465_; uint8_t v_isSharedCheck_2481_; 
v_a_2462_ = lean_ctor_get(v___x_2461_, 0);
v_isSharedCheck_2481_ = !lean_is_exclusive(v___x_2461_);
if (v_isSharedCheck_2481_ == 0)
{
v___x_2464_ = v___x_2461_;
v_isShared_2465_ = v_isSharedCheck_2481_;
goto v_resetjp_2463_;
}
else
{
lean_inc(v_a_2462_);
lean_dec(v___x_2461_);
v___x_2464_ = lean_box(0);
v_isShared_2465_ = v_isSharedCheck_2481_;
goto v_resetjp_2463_;
}
v_resetjp_2463_:
{
lean_object* v_fst_2466_; lean_object* v_snd_2467_; lean_object* v___x_2469_; uint8_t v_isShared_2470_; uint8_t v_isSharedCheck_2480_; 
v_fst_2466_ = lean_ctor_get(v_a_2462_, 0);
v_snd_2467_ = lean_ctor_get(v_a_2462_, 1);
v_isSharedCheck_2480_ = !lean_is_exclusive(v_a_2462_);
if (v_isSharedCheck_2480_ == 0)
{
v___x_2469_ = v_a_2462_;
v_isShared_2470_ = v_isSharedCheck_2480_;
goto v_resetjp_2468_;
}
else
{
lean_inc(v_snd_2467_);
lean_inc(v_fst_2466_);
lean_dec(v_a_2462_);
v___x_2469_ = lean_box(0);
v_isShared_2470_ = v_isSharedCheck_2480_;
goto v_resetjp_2468_;
}
v_resetjp_2468_:
{
lean_object* v___x_2472_; 
if (v_isShared_2451_ == 0)
{
lean_ctor_set_tag(v___x_2450_, 1);
lean_ctor_set(v___x_2450_, 1, v_snd_2467_);
lean_ctor_set(v___x_2450_, 0, v_fvarId_2458_);
v___x_2472_ = v___x_2450_;
goto v_reusejp_2471_;
}
else
{
lean_object* v_reuseFailAlloc_2479_; 
v_reuseFailAlloc_2479_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2479_, 0, v_fvarId_2458_);
lean_ctor_set(v_reuseFailAlloc_2479_, 1, v_snd_2467_);
v___x_2472_ = v_reuseFailAlloc_2479_;
goto v_reusejp_2471_;
}
v_reusejp_2471_:
{
lean_object* v___x_2474_; 
if (v_isShared_2470_ == 0)
{
lean_ctor_set(v___x_2469_, 1, v___x_2472_);
v___x_2474_ = v___x_2469_;
goto v_reusejp_2473_;
}
else
{
lean_object* v_reuseFailAlloc_2478_; 
v_reuseFailAlloc_2478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2478_, 0, v_fst_2466_);
lean_ctor_set(v_reuseFailAlloc_2478_, 1, v___x_2472_);
v___x_2474_ = v_reuseFailAlloc_2478_;
goto v_reusejp_2473_;
}
v_reusejp_2473_:
{
lean_object* v___x_2476_; 
if (v_isShared_2465_ == 0)
{
lean_ctor_set(v___x_2464_, 0, v___x_2474_);
v___x_2476_ = v___x_2464_;
goto v_reusejp_2475_;
}
else
{
lean_object* v_reuseFailAlloc_2477_; 
v_reuseFailAlloc_2477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2477_, 0, v___x_2474_);
v___x_2476_ = v_reuseFailAlloc_2477_;
goto v_reusejp_2475_;
}
v_reusejp_2475_:
{
return v___x_2476_;
}
}
}
}
}
}
else
{
lean_dec(v_fvarId_2458_);
lean_del_object(v___x_2450_);
return v___x_2461_;
}
}
else
{
lean_dec(v___x_2459_);
lean_dec(v_fvarId_2458_);
lean_dec(v_mvarId_2452_);
lean_del_object(v___x_2450_);
lean_dec(v_n_2438_);
v___y_2425_ = v_a_2419_;
v___y_2426_ = v_a_2420_;
v___y_2427_ = v_a_2421_;
v___y_2428_ = v_a_2422_;
goto v___jp_2424_;
}
}
else
{
lean_dec_ref(v_fields_2453_);
lean_dec(v_mvarId_2452_);
lean_del_object(v___x_2450_);
lean_dec(v_n_2438_);
v___y_2425_ = v_a_2419_;
v___y_2426_ = v_a_2420_;
v___y_2427_ = v_a_2421_;
v___y_2428_ = v_a_2422_;
goto v___jp_2424_;
}
}
}
}
}
else
{
lean_object* v_a_2484_; lean_object* v___x_2486_; uint8_t v_isShared_2487_; uint8_t v_isSharedCheck_2491_; 
lean_dec(v_n_2438_);
v_a_2484_ = lean_ctor_get(v___x_2441_, 0);
v_isSharedCheck_2491_ = !lean_is_exclusive(v___x_2441_);
if (v_isSharedCheck_2491_ == 0)
{
v___x_2486_ = v___x_2441_;
v_isShared_2487_ = v_isSharedCheck_2491_;
goto v_resetjp_2485_;
}
else
{
lean_inc(v_a_2484_);
lean_dec(v___x_2441_);
v___x_2486_ = lean_box(0);
v_isShared_2487_ = v_isSharedCheck_2491_;
goto v_resetjp_2485_;
}
v_resetjp_2485_:
{
lean_object* v___x_2489_; 
if (v_isShared_2487_ == 0)
{
v___x_2489_ = v___x_2486_;
goto v_reusejp_2488_;
}
else
{
lean_object* v_reuseFailAlloc_2490_; 
v_reuseFailAlloc_2490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2490_, 0, v_a_2484_);
v___x_2489_ = v_reuseFailAlloc_2490_;
goto v_reusejp_2488_;
}
v_reusejp_2488_:
{
return v___x_2489_;
}
}
}
}
v___jp_2424_:
{
lean_object* v___x_2429_; lean_object* v___x_2430_; 
v___x_2429_ = lean_obj_once(&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesSum___closed__1, &l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesSum___closed__1_once, _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesSum___closed__1);
v___x_2430_ = l_Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0___redArg(v___x_2429_, v___y_2425_, v___y_2426_, v___y_2427_, v___y_2428_);
return v___x_2430_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesProd___boxed(lean_object* v_n_2492_, lean_object* v_mvar_2493_, lean_object* v_h_2494_, lean_object* v_a_2495_, lean_object* v_a_2496_, lean_object* v_a_2497_, lean_object* v_a_2498_, lean_object* v_a_2499_){
_start:
{
lean_object* v_res_2500_; 
v_res_2500_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesProd(v_n_2492_, v_mvar_2493_, v_h_2494_, v_a_2495_, v_a_2496_, v_a_2497_, v_a_2498_);
lean_dec(v_a_2498_);
lean_dec_ref(v_a_2497_);
lean_dec(v_a_2496_);
lean_dec_ref(v_a_2495_);
lean_dec(v_n_2492_);
return v_res_2500_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_listBoolMerge___redArg(lean_object* v_x_2501_, lean_object* v_x_2502_){
_start:
{
if (lean_obj_tag(v_x_2501_) == 0)
{
lean_object* v___x_2503_; 
lean_dec(v_x_2502_);
v___x_2503_ = lean_box(0);
return v___x_2503_;
}
else
{
lean_object* v_head_2504_; uint8_t v___x_2505_; 
v_head_2504_ = lean_ctor_get(v_x_2501_, 0);
v___x_2505_ = lean_unbox(v_head_2504_);
if (v___x_2505_ == 0)
{
lean_object* v_tail_2506_; lean_object* v___x_2508_; uint8_t v_isShared_2509_; uint8_t v_isSharedCheck_2515_; 
v_tail_2506_ = lean_ctor_get(v_x_2501_, 1);
v_isSharedCheck_2515_ = !lean_is_exclusive(v_x_2501_);
if (v_isSharedCheck_2515_ == 0)
{
lean_object* v_unused_2516_; 
v_unused_2516_ = lean_ctor_get(v_x_2501_, 0);
lean_dec(v_unused_2516_);
v___x_2508_ = v_x_2501_;
v_isShared_2509_ = v_isSharedCheck_2515_;
goto v_resetjp_2507_;
}
else
{
lean_inc(v_tail_2506_);
lean_dec(v_x_2501_);
v___x_2508_ = lean_box(0);
v_isShared_2509_ = v_isSharedCheck_2515_;
goto v_resetjp_2507_;
}
v_resetjp_2507_:
{
lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2513_; 
v___x_2510_ = lean_box(0);
v___x_2511_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_listBoolMerge___redArg(v_tail_2506_, v_x_2502_);
if (v_isShared_2509_ == 0)
{
lean_ctor_set(v___x_2508_, 1, v___x_2511_);
lean_ctor_set(v___x_2508_, 0, v___x_2510_);
v___x_2513_ = v___x_2508_;
goto v_reusejp_2512_;
}
else
{
lean_object* v_reuseFailAlloc_2514_; 
v_reuseFailAlloc_2514_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2514_, 0, v___x_2510_);
lean_ctor_set(v_reuseFailAlloc_2514_, 1, v___x_2511_);
v___x_2513_ = v_reuseFailAlloc_2514_;
goto v_reusejp_2512_;
}
v_reusejp_2512_:
{
return v___x_2513_;
}
}
}
else
{
if (lean_obj_tag(v_x_2502_) == 0)
{
lean_object* v___x_2517_; 
lean_dec_ref_known(v_x_2501_, 2);
v___x_2517_ = lean_box(0);
return v___x_2517_;
}
else
{
lean_object* v_tail_2518_; lean_object* v_head_2519_; lean_object* v_tail_2520_; lean_object* v___x_2522_; uint8_t v_isShared_2523_; uint8_t v_isSharedCheck_2529_; 
v_tail_2518_ = lean_ctor_get(v_x_2501_, 1);
lean_inc(v_tail_2518_);
lean_dec_ref_known(v_x_2501_, 2);
v_head_2519_ = lean_ctor_get(v_x_2502_, 0);
v_tail_2520_ = lean_ctor_get(v_x_2502_, 1);
v_isSharedCheck_2529_ = !lean_is_exclusive(v_x_2502_);
if (v_isSharedCheck_2529_ == 0)
{
v___x_2522_ = v_x_2502_;
v_isShared_2523_ = v_isSharedCheck_2529_;
goto v_resetjp_2521_;
}
else
{
lean_inc(v_tail_2520_);
lean_inc(v_head_2519_);
lean_dec(v_x_2502_);
v___x_2522_ = lean_box(0);
v_isShared_2523_ = v_isSharedCheck_2529_;
goto v_resetjp_2521_;
}
v_resetjp_2521_:
{
lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2527_; 
v___x_2524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2524_, 0, v_head_2519_);
v___x_2525_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_listBoolMerge___redArg(v_tail_2518_, v_tail_2520_);
if (v_isShared_2523_ == 0)
{
lean_ctor_set(v___x_2522_, 1, v___x_2525_);
lean_ctor_set(v___x_2522_, 0, v___x_2524_);
v___x_2527_ = v___x_2522_;
goto v_reusejp_2526_;
}
else
{
lean_object* v_reuseFailAlloc_2528_; 
v_reuseFailAlloc_2528_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2528_, 0, v___x_2524_);
lean_ctor_set(v_reuseFailAlloc_2528_, 1, v___x_2525_);
v___x_2527_ = v_reuseFailAlloc_2528_;
goto v_reusejp_2526_;
}
v_reusejp_2526_:
{
return v___x_2527_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_listBoolMerge(lean_object* v_00_u03b1_2530_, lean_object* v_x_2531_, lean_object* v_x_2532_){
_start:
{
lean_object* v___x_2533_; 
v___x_2533_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_listBoolMerge___redArg(v_x_2531_, v_x_2532_);
return v___x_2533_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__2_spec__3(lean_object* v_a_2534_, lean_object* v_a_2535_){
_start:
{
if (lean_obj_tag(v_a_2534_) == 0)
{
lean_object* v___x_2536_; 
v___x_2536_ = l_List_reverse___redArg(v_a_2535_);
return v___x_2536_;
}
else
{
lean_object* v_head_2537_; lean_object* v_tail_2538_; lean_object* v___x_2540_; uint8_t v_isShared_2541_; uint8_t v_isSharedCheck_2547_; 
v_head_2537_ = lean_ctor_get(v_a_2534_, 0);
v_tail_2538_ = lean_ctor_get(v_a_2534_, 1);
v_isSharedCheck_2547_ = !lean_is_exclusive(v_a_2534_);
if (v_isSharedCheck_2547_ == 0)
{
v___x_2540_ = v_a_2534_;
v_isShared_2541_ = v_isSharedCheck_2547_;
goto v_resetjp_2539_;
}
else
{
lean_inc(v_tail_2538_);
lean_inc(v_head_2537_);
lean_dec(v_a_2534_);
v___x_2540_ = lean_box(0);
v_isShared_2541_ = v_isSharedCheck_2547_;
goto v_resetjp_2539_;
}
v_resetjp_2539_:
{
lean_object* v___x_2542_; lean_object* v___x_2544_; 
v___x_2542_ = l_Lean_mkLevelParam(v_head_2537_);
if (v_isShared_2541_ == 0)
{
lean_ctor_set(v___x_2540_, 1, v_a_2535_);
lean_ctor_set(v___x_2540_, 0, v___x_2542_);
v___x_2544_ = v___x_2540_;
goto v_reusejp_2543_;
}
else
{
lean_object* v_reuseFailAlloc_2546_; 
v_reuseFailAlloc_2546_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2546_, 0, v___x_2542_);
lean_ctor_set(v_reuseFailAlloc_2546_, 1, v_a_2535_);
v___x_2544_ = v_reuseFailAlloc_2546_;
goto v_reusejp_2543_;
}
v_reusejp_2543_:
{
v_a_2534_ = v_tail_2538_;
v_a_2535_ = v___x_2544_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__2_spec__2(lean_object* v_constName_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_){
_start:
{
lean_object* v___x_2554_; lean_object* v_env_2555_; uint8_t v___x_2556_; lean_object* v___x_2557_; 
v___x_2554_ = lean_st_ref_get(v___y_2552_);
v_env_2555_ = lean_ctor_get(v___x_2554_, 0);
lean_inc_ref(v_env_2555_);
lean_dec(v___x_2554_);
v___x_2556_ = 0;
lean_inc(v_constName_2548_);
v___x_2557_ = l_Lean_Environment_findConstVal_x3f(v_env_2555_, v_constName_2548_, v___x_2556_);
if (lean_obj_tag(v___x_2557_) == 0)
{
lean_object* v___x_2558_; 
v___x_2558_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0___redArg(v_constName_2548_, v___y_2549_, v___y_2550_, v___y_2551_, v___y_2552_);
return v___x_2558_;
}
else
{
lean_object* v_val_2559_; lean_object* v___x_2561_; uint8_t v_isShared_2562_; uint8_t v_isSharedCheck_2566_; 
lean_dec(v_constName_2548_);
v_val_2559_ = lean_ctor_get(v___x_2557_, 0);
v_isSharedCheck_2566_ = !lean_is_exclusive(v___x_2557_);
if (v_isSharedCheck_2566_ == 0)
{
v___x_2561_ = v___x_2557_;
v_isShared_2562_ = v_isSharedCheck_2566_;
goto v_resetjp_2560_;
}
else
{
lean_inc(v_val_2559_);
lean_dec(v___x_2557_);
v___x_2561_ = lean_box(0);
v_isShared_2562_ = v_isSharedCheck_2566_;
goto v_resetjp_2560_;
}
v_resetjp_2560_:
{
lean_object* v___x_2564_; 
if (v_isShared_2562_ == 0)
{
lean_ctor_set_tag(v___x_2561_, 0);
v___x_2564_ = v___x_2561_;
goto v_reusejp_2563_;
}
else
{
lean_object* v_reuseFailAlloc_2565_; 
v_reuseFailAlloc_2565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2565_, 0, v_val_2559_);
v___x_2564_ = v_reuseFailAlloc_2565_;
goto v_reusejp_2563_;
}
v_reusejp_2563_:
{
return v___x_2564_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__2_spec__2___boxed(lean_object* v_constName_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_){
_start:
{
lean_object* v_res_2573_; 
v_res_2573_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__2_spec__2(v_constName_2567_, v___y_2568_, v___y_2569_, v___y_2570_, v___y_2571_);
lean_dec(v___y_2571_);
lean_dec_ref(v___y_2570_);
lean_dec(v___y_2569_);
lean_dec_ref(v___y_2568_);
return v_res_2573_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__2(lean_object* v_constName_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_){
_start:
{
lean_object* v___x_2580_; 
lean_inc(v_constName_2574_);
v___x_2580_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__2_spec__2(v_constName_2574_, v___y_2575_, v___y_2576_, v___y_2577_, v___y_2578_);
if (lean_obj_tag(v___x_2580_) == 0)
{
lean_object* v_a_2581_; lean_object* v___x_2583_; uint8_t v_isShared_2584_; uint8_t v_isSharedCheck_2592_; 
v_a_2581_ = lean_ctor_get(v___x_2580_, 0);
v_isSharedCheck_2592_ = !lean_is_exclusive(v___x_2580_);
if (v_isSharedCheck_2592_ == 0)
{
v___x_2583_ = v___x_2580_;
v_isShared_2584_ = v_isSharedCheck_2592_;
goto v_resetjp_2582_;
}
else
{
lean_inc(v_a_2581_);
lean_dec(v___x_2580_);
v___x_2583_ = lean_box(0);
v_isShared_2584_ = v_isSharedCheck_2592_;
goto v_resetjp_2582_;
}
v_resetjp_2582_:
{
lean_object* v_levelParams_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2590_; 
v_levelParams_2585_ = lean_ctor_get(v_a_2581_, 1);
lean_inc(v_levelParams_2585_);
lean_dec(v_a_2581_);
v___x_2586_ = lean_box(0);
v___x_2587_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__2_spec__3(v_levelParams_2585_, v___x_2586_);
v___x_2588_ = l_Lean_mkConst(v_constName_2574_, v___x_2587_);
if (v_isShared_2584_ == 0)
{
lean_ctor_set(v___x_2583_, 0, v___x_2588_);
v___x_2590_ = v___x_2583_;
goto v_reusejp_2589_;
}
else
{
lean_object* v_reuseFailAlloc_2591_; 
v_reuseFailAlloc_2591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2591_, 0, v___x_2588_);
v___x_2590_ = v_reuseFailAlloc_2591_;
goto v_reusejp_2589_;
}
v_reusejp_2589_:
{
return v___x_2590_;
}
}
}
else
{
lean_object* v_a_2593_; lean_object* v___x_2595_; uint8_t v_isShared_2596_; uint8_t v_isSharedCheck_2600_; 
lean_dec(v_constName_2574_);
v_a_2593_ = lean_ctor_get(v___x_2580_, 0);
v_isSharedCheck_2600_ = !lean_is_exclusive(v___x_2580_);
if (v_isSharedCheck_2600_ == 0)
{
v___x_2595_ = v___x_2580_;
v_isShared_2596_ = v_isSharedCheck_2600_;
goto v_resetjp_2594_;
}
else
{
lean_inc(v_a_2593_);
lean_dec(v___x_2580_);
v___x_2595_ = lean_box(0);
v_isShared_2596_ = v_isSharedCheck_2600_;
goto v_resetjp_2594_;
}
v_resetjp_2594_:
{
lean_object* v___x_2598_; 
if (v_isShared_2596_ == 0)
{
v___x_2598_ = v___x_2595_;
goto v_reusejp_2597_;
}
else
{
lean_object* v_reuseFailAlloc_2599_; 
v_reuseFailAlloc_2599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2599_, 0, v_a_2593_);
v___x_2598_ = v_reuseFailAlloc_2599_;
goto v_reusejp_2597_;
}
v_reusejp_2597_:
{
return v___x_2598_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__2___boxed(lean_object* v_constName_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_){
_start:
{
lean_object* v_res_2607_; 
v_res_2607_ = l_Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__2(v_constName_2601_, v___y_2602_, v___y_2603_, v___y_2604_, v___y_2605_);
lean_dec(v___y_2605_);
lean_dec_ref(v___y_2604_);
lean_dec(v___y_2603_);
lean_dec_ref(v___y_2602_);
return v_res_2607_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__1(lean_object* v_x_2608_, lean_object* v_x_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_, lean_object* v___y_2612_, lean_object* v___y_2613_){
_start:
{
if (lean_obj_tag(v_x_2608_) == 0)
{
lean_object* v___x_2615_; lean_object* v___x_2616_; 
v___x_2615_ = l_List_reverse___redArg(v_x_2609_);
v___x_2616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2616_, 0, v___x_2615_);
return v___x_2616_;
}
else
{
lean_object* v_head_2617_; lean_object* v_tail_2618_; lean_object* v___x_2620_; uint8_t v_isShared_2621_; uint8_t v_isSharedCheck_2643_; 
v_head_2617_ = lean_ctor_get(v_x_2608_, 0);
v_tail_2618_ = lean_ctor_get(v_x_2608_, 1);
v_isSharedCheck_2643_ = !lean_is_exclusive(v_x_2608_);
if (v_isSharedCheck_2643_ == 0)
{
v___x_2620_ = v_x_2608_;
v_isShared_2621_ = v_isSharedCheck_2643_;
goto v_resetjp_2619_;
}
else
{
lean_inc(v_tail_2618_);
lean_inc(v_head_2617_);
lean_dec(v_x_2608_);
v___x_2620_ = lean_box(0);
v_isShared_2621_ = v_isSharedCheck_2643_;
goto v_resetjp_2619_;
}
v_resetjp_2619_:
{
lean_object* v_a_2623_; 
if (lean_obj_tag(v_head_2617_) == 0)
{
lean_object* v___x_2628_; uint8_t v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; 
v___x_2628_ = lean_box(0);
v___x_2629_ = 0;
v___x_2630_ = lean_box(0);
v___x_2631_ = l_Lean_Meta_mkFreshExprMVar(v___x_2628_, v___x_2629_, v___x_2630_, v___y_2610_, v___y_2611_, v___y_2612_, v___y_2613_);
if (lean_obj_tag(v___x_2631_) == 0)
{
lean_object* v_a_2632_; 
v_a_2632_ = lean_ctor_get(v___x_2631_, 0);
lean_inc(v_a_2632_);
lean_dec_ref_known(v___x_2631_, 1);
v_a_2623_ = v_a_2632_;
goto v___jp_2622_;
}
else
{
lean_object* v_a_2633_; lean_object* v___x_2635_; uint8_t v_isShared_2636_; uint8_t v_isSharedCheck_2640_; 
lean_del_object(v___x_2620_);
lean_dec(v_tail_2618_);
lean_dec(v_x_2609_);
v_a_2633_ = lean_ctor_get(v___x_2631_, 0);
v_isSharedCheck_2640_ = !lean_is_exclusive(v___x_2631_);
if (v_isSharedCheck_2640_ == 0)
{
v___x_2635_ = v___x_2631_;
v_isShared_2636_ = v_isSharedCheck_2640_;
goto v_resetjp_2634_;
}
else
{
lean_inc(v_a_2633_);
lean_dec(v___x_2631_);
v___x_2635_ = lean_box(0);
v_isShared_2636_ = v_isSharedCheck_2640_;
goto v_resetjp_2634_;
}
v_resetjp_2634_:
{
lean_object* v___x_2638_; 
if (v_isShared_2636_ == 0)
{
v___x_2638_ = v___x_2635_;
goto v_reusejp_2637_;
}
else
{
lean_object* v_reuseFailAlloc_2639_; 
v_reuseFailAlloc_2639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2639_, 0, v_a_2633_);
v___x_2638_ = v_reuseFailAlloc_2639_;
goto v_reusejp_2637_;
}
v_reusejp_2637_:
{
return v___x_2638_;
}
}
}
}
else
{
lean_object* v_val_2641_; lean_object* v___x_2642_; 
v_val_2641_ = lean_ctor_get(v_head_2617_, 0);
lean_inc(v_val_2641_);
lean_dec_ref_known(v_head_2617_, 1);
v___x_2642_ = l_Lean_mkFVar(v_val_2641_);
v_a_2623_ = v___x_2642_;
goto v___jp_2622_;
}
v___jp_2622_:
{
lean_object* v___x_2625_; 
if (v_isShared_2621_ == 0)
{
lean_ctor_set(v___x_2620_, 1, v_x_2609_);
lean_ctor_set(v___x_2620_, 0, v_a_2623_);
v___x_2625_ = v___x_2620_;
goto v_reusejp_2624_;
}
else
{
lean_object* v_reuseFailAlloc_2627_; 
v_reuseFailAlloc_2627_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2627_, 0, v_a_2623_);
lean_ctor_set(v_reuseFailAlloc_2627_, 1, v_x_2609_);
v___x_2625_ = v_reuseFailAlloc_2627_;
goto v_reusejp_2624_;
}
v_reusejp_2624_:
{
v_x_2608_ = v_tail_2618_;
v_x_2609_ = v___x_2625_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__1___boxed(lean_object* v_x_2644_, lean_object* v_x_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_){
_start:
{
lean_object* v_res_2651_; 
v_res_2651_ = l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__1(v_x_2644_, v_x_2645_, v___y_2646_, v___y_2647_, v___y_2648_, v___y_2649_);
lean_dec(v___y_2649_);
lean_dec_ref(v___y_2648_);
lean_dec(v___y_2647_);
lean_dec_ref(v___y_2646_);
return v_res_2651_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__0(lean_object* v_a_2652_, lean_object* v_a_2653_){
_start:
{
if (lean_obj_tag(v_a_2652_) == 0)
{
lean_object* v___x_2654_; 
v___x_2654_ = l_List_reverse___redArg(v_a_2653_);
return v___x_2654_;
}
else
{
lean_object* v_head_2655_; lean_object* v_tail_2656_; lean_object* v___x_2658_; uint8_t v_isShared_2659_; uint8_t v_isSharedCheck_2665_; 
v_head_2655_ = lean_ctor_get(v_a_2652_, 0);
v_tail_2656_ = lean_ctor_get(v_a_2652_, 1);
v_isSharedCheck_2665_ = !lean_is_exclusive(v_a_2652_);
if (v_isSharedCheck_2665_ == 0)
{
v___x_2658_ = v_a_2652_;
v_isShared_2659_ = v_isSharedCheck_2665_;
goto v_resetjp_2657_;
}
else
{
lean_inc(v_tail_2656_);
lean_inc(v_head_2655_);
lean_dec(v_a_2652_);
v___x_2658_ = lean_box(0);
v_isShared_2659_ = v_isSharedCheck_2665_;
goto v_resetjp_2657_;
}
v_resetjp_2657_:
{
lean_object* v___x_2660_; lean_object* v___x_2662_; 
v___x_2660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2660_, 0, v_head_2655_);
if (v_isShared_2659_ == 0)
{
lean_ctor_set(v___x_2658_, 1, v_a_2653_);
lean_ctor_set(v___x_2658_, 0, v___x_2660_);
v___x_2662_ = v___x_2658_;
goto v_reusejp_2661_;
}
else
{
lean_object* v_reuseFailAlloc_2664_; 
v_reuseFailAlloc_2664_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2664_, 0, v___x_2660_);
lean_ctor_set(v_reuseFailAlloc_2664_, 1, v_a_2653_);
v___x_2662_ = v_reuseFailAlloc_2664_;
goto v_reusejp_2661_;
}
v_reusejp_2661_:
{
v_a_2652_ = v_tail_2656_;
v_a_2653_ = v___x_2662_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__5___lam__0(lean_object* v_gs_2668_, lean_object* v_variablesKept_2669_, lean_object* v_snd_2670_, lean_object* v_fst_2671_, lean_object* v_fst_2672_, lean_object* v___y_2673_, lean_object* v___y_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_){
_start:
{
lean_object* v_lctx_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; 
v_lctx_2678_ = lean_ctor_get(v___y_2673_, 2);
v___x_2679_ = l_Lean_LocalContext_getFVarIds(v_lctx_2678_);
v___x_2680_ = lean_array_to_list(v___x_2679_);
v___x_2681_ = l_List_lengthTR___redArg(v_gs_2668_);
v___x_2682_ = ((lean_object*)(l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__5___lam__0___closed__0));
lean_inc(v___x_2680_);
v___x_2683_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), v___x_2680_, v___x_2680_, v___x_2681_, v___x_2682_);
lean_dec(v___x_2680_);
v___x_2684_ = lean_box(0);
v___x_2685_ = l_List_mapTR_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__0(v___x_2683_, v___x_2684_);
v___x_2686_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_listBoolMerge___redArg(v_variablesKept_2669_, v_snd_2670_);
v___x_2687_ = l_List_appendTR___redArg(v___x_2685_, v___x_2686_);
v___x_2688_ = l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__1(v___x_2687_, v___x_2684_, v___y_2673_, v___y_2674_, v___y_2675_, v___y_2676_);
if (lean_obj_tag(v___x_2688_) == 0)
{
lean_object* v_a_2689_; lean_object* v___x_2690_; 
v_a_2689_ = lean_ctor_get(v___x_2688_, 0);
lean_inc(v_a_2689_);
lean_dec_ref_known(v___x_2688_, 1);
v___x_2690_ = l_Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__2(v_fst_2671_, v___y_2673_, v___y_2674_, v___y_2675_, v___y_2676_);
if (lean_obj_tag(v___x_2690_) == 0)
{
lean_object* v_a_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; 
v_a_2691_ = lean_ctor_get(v___x_2690_, 0);
lean_inc(v_a_2691_);
lean_dec_ref_known(v___x_2690_, 1);
v___x_2692_ = lean_array_mk(v_a_2689_);
v___x_2693_ = l_Lean_mkAppN(v_a_2691_, v___x_2692_);
lean_dec_ref(v___x_2692_);
lean_inc(v___y_2676_);
lean_inc_ref(v___y_2675_);
lean_inc(v___y_2674_);
lean_inc_ref(v___y_2673_);
lean_inc_ref(v___x_2693_);
v___x_2694_ = lean_infer_type(v___x_2693_, v___y_2673_, v___y_2674_, v___y_2675_, v___y_2676_);
if (lean_obj_tag(v___x_2694_) == 0)
{
lean_object* v_a_2695_; lean_object* v___x_2696_; 
v_a_2695_ = lean_ctor_get(v___x_2694_, 0);
lean_inc(v_a_2695_);
lean_dec_ref_known(v___x_2694_, 1);
lean_inc(v_fst_2672_);
v___x_2696_ = l_Lean_MVarId_getType(v_fst_2672_, v___y_2673_, v___y_2674_, v___y_2675_, v___y_2676_);
if (lean_obj_tag(v___x_2696_) == 0)
{
lean_object* v_a_2697_; lean_object* v___x_2698_; 
v_a_2697_ = lean_ctor_get(v___x_2696_, 0);
lean_inc(v_a_2697_);
lean_dec_ref_known(v___x_2696_, 1);
v___x_2698_ = l_Lean_Meta_isExprDefEq(v_a_2695_, v_a_2697_, v___y_2673_, v___y_2674_, v___y_2675_, v___y_2676_);
lean_dec(v___y_2676_);
lean_dec_ref(v___y_2675_);
lean_dec_ref(v___y_2673_);
if (lean_obj_tag(v___x_2698_) == 0)
{
lean_object* v___x_2699_; 
lean_dec_ref_known(v___x_2698_, 1);
v___x_2699_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1___redArg(v_fst_2672_, v___x_2693_, v___y_2674_);
lean_dec(v___y_2674_);
return v___x_2699_;
}
else
{
lean_object* v_a_2700_; lean_object* v___x_2702_; uint8_t v_isShared_2703_; uint8_t v_isSharedCheck_2707_; 
lean_dec_ref(v___x_2693_);
lean_dec(v___y_2674_);
lean_dec(v_fst_2672_);
v_a_2700_ = lean_ctor_get(v___x_2698_, 0);
v_isSharedCheck_2707_ = !lean_is_exclusive(v___x_2698_);
if (v_isSharedCheck_2707_ == 0)
{
v___x_2702_ = v___x_2698_;
v_isShared_2703_ = v_isSharedCheck_2707_;
goto v_resetjp_2701_;
}
else
{
lean_inc(v_a_2700_);
lean_dec(v___x_2698_);
v___x_2702_ = lean_box(0);
v_isShared_2703_ = v_isSharedCheck_2707_;
goto v_resetjp_2701_;
}
v_resetjp_2701_:
{
lean_object* v___x_2705_; 
if (v_isShared_2703_ == 0)
{
v___x_2705_ = v___x_2702_;
goto v_reusejp_2704_;
}
else
{
lean_object* v_reuseFailAlloc_2706_; 
v_reuseFailAlloc_2706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2706_, 0, v_a_2700_);
v___x_2705_ = v_reuseFailAlloc_2706_;
goto v_reusejp_2704_;
}
v_reusejp_2704_:
{
return v___x_2705_;
}
}
}
}
else
{
lean_object* v_a_2708_; lean_object* v___x_2710_; uint8_t v_isShared_2711_; uint8_t v_isSharedCheck_2715_; 
lean_dec(v_a_2695_);
lean_dec_ref(v___x_2693_);
lean_dec(v___y_2676_);
lean_dec_ref(v___y_2675_);
lean_dec(v___y_2674_);
lean_dec_ref(v___y_2673_);
lean_dec(v_fst_2672_);
v_a_2708_ = lean_ctor_get(v___x_2696_, 0);
v_isSharedCheck_2715_ = !lean_is_exclusive(v___x_2696_);
if (v_isSharedCheck_2715_ == 0)
{
v___x_2710_ = v___x_2696_;
v_isShared_2711_ = v_isSharedCheck_2715_;
goto v_resetjp_2709_;
}
else
{
lean_inc(v_a_2708_);
lean_dec(v___x_2696_);
v___x_2710_ = lean_box(0);
v_isShared_2711_ = v_isSharedCheck_2715_;
goto v_resetjp_2709_;
}
v_resetjp_2709_:
{
lean_object* v___x_2713_; 
if (v_isShared_2711_ == 0)
{
v___x_2713_ = v___x_2710_;
goto v_reusejp_2712_;
}
else
{
lean_object* v_reuseFailAlloc_2714_; 
v_reuseFailAlloc_2714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2714_, 0, v_a_2708_);
v___x_2713_ = v_reuseFailAlloc_2714_;
goto v_reusejp_2712_;
}
v_reusejp_2712_:
{
return v___x_2713_;
}
}
}
}
else
{
lean_object* v_a_2716_; lean_object* v___x_2718_; uint8_t v_isShared_2719_; uint8_t v_isSharedCheck_2723_; 
lean_dec_ref(v___x_2693_);
lean_dec(v___y_2676_);
lean_dec_ref(v___y_2675_);
lean_dec(v___y_2674_);
lean_dec_ref(v___y_2673_);
lean_dec(v_fst_2672_);
v_a_2716_ = lean_ctor_get(v___x_2694_, 0);
v_isSharedCheck_2723_ = !lean_is_exclusive(v___x_2694_);
if (v_isSharedCheck_2723_ == 0)
{
v___x_2718_ = v___x_2694_;
v_isShared_2719_ = v_isSharedCheck_2723_;
goto v_resetjp_2717_;
}
else
{
lean_inc(v_a_2716_);
lean_dec(v___x_2694_);
v___x_2718_ = lean_box(0);
v_isShared_2719_ = v_isSharedCheck_2723_;
goto v_resetjp_2717_;
}
v_resetjp_2717_:
{
lean_object* v___x_2721_; 
if (v_isShared_2719_ == 0)
{
v___x_2721_ = v___x_2718_;
goto v_reusejp_2720_;
}
else
{
lean_object* v_reuseFailAlloc_2722_; 
v_reuseFailAlloc_2722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2722_, 0, v_a_2716_);
v___x_2721_ = v_reuseFailAlloc_2722_;
goto v_reusejp_2720_;
}
v_reusejp_2720_:
{
return v___x_2721_;
}
}
}
}
else
{
lean_object* v_a_2724_; lean_object* v___x_2726_; uint8_t v_isShared_2727_; uint8_t v_isSharedCheck_2731_; 
lean_dec(v_a_2689_);
lean_dec(v___y_2676_);
lean_dec_ref(v___y_2675_);
lean_dec(v___y_2674_);
lean_dec_ref(v___y_2673_);
lean_dec(v_fst_2672_);
v_a_2724_ = lean_ctor_get(v___x_2690_, 0);
v_isSharedCheck_2731_ = !lean_is_exclusive(v___x_2690_);
if (v_isSharedCheck_2731_ == 0)
{
v___x_2726_ = v___x_2690_;
v_isShared_2727_ = v_isSharedCheck_2731_;
goto v_resetjp_2725_;
}
else
{
lean_inc(v_a_2724_);
lean_dec(v___x_2690_);
v___x_2726_ = lean_box(0);
v_isShared_2727_ = v_isSharedCheck_2731_;
goto v_resetjp_2725_;
}
v_resetjp_2725_:
{
lean_object* v___x_2729_; 
if (v_isShared_2727_ == 0)
{
v___x_2729_ = v___x_2726_;
goto v_reusejp_2728_;
}
else
{
lean_object* v_reuseFailAlloc_2730_; 
v_reuseFailAlloc_2730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2730_, 0, v_a_2724_);
v___x_2729_ = v_reuseFailAlloc_2730_;
goto v_reusejp_2728_;
}
v_reusejp_2728_:
{
return v___x_2729_;
}
}
}
}
else
{
lean_object* v_a_2732_; lean_object* v___x_2734_; uint8_t v_isShared_2735_; uint8_t v_isSharedCheck_2739_; 
lean_dec(v___y_2676_);
lean_dec_ref(v___y_2675_);
lean_dec(v___y_2674_);
lean_dec_ref(v___y_2673_);
lean_dec(v_fst_2672_);
lean_dec(v_fst_2671_);
v_a_2732_ = lean_ctor_get(v___x_2688_, 0);
v_isSharedCheck_2739_ = !lean_is_exclusive(v___x_2688_);
if (v_isSharedCheck_2739_ == 0)
{
v___x_2734_ = v___x_2688_;
v_isShared_2735_ = v_isSharedCheck_2739_;
goto v_resetjp_2733_;
}
else
{
lean_inc(v_a_2732_);
lean_dec(v___x_2688_);
v___x_2734_ = lean_box(0);
v_isShared_2735_ = v_isSharedCheck_2739_;
goto v_resetjp_2733_;
}
v_resetjp_2733_:
{
lean_object* v___x_2737_; 
if (v_isShared_2735_ == 0)
{
v___x_2737_ = v___x_2734_;
goto v_reusejp_2736_;
}
else
{
lean_object* v_reuseFailAlloc_2738_; 
v_reuseFailAlloc_2738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2738_, 0, v_a_2732_);
v___x_2737_ = v_reuseFailAlloc_2738_;
goto v_reusejp_2736_;
}
v_reusejp_2736_:
{
return v___x_2737_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__5___lam__0___boxed(lean_object* v_gs_2740_, lean_object* v_variablesKept_2741_, lean_object* v_snd_2742_, lean_object* v_fst_2743_, lean_object* v_fst_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_){
_start:
{
lean_object* v_res_2750_; 
v_res_2750_ = l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__5___lam__0(v_gs_2740_, v_variablesKept_2741_, v_snd_2742_, v_fst_2743_, v_fst_2744_, v___y_2745_, v___y_2746_, v___y_2747_, v___y_2748_);
lean_dec(v_gs_2740_);
return v_res_2750_;
}
}
static lean_object* _init_l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__4___closed__1(void){
_start:
{
lean_object* v___x_2752_; lean_object* v___x_2753_; 
v___x_2752_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__4___closed__0));
v___x_2753_ = l_Lean_stringToMessageData(v___x_2752_);
return v___x_2753_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__4(lean_object* v_x_2754_, lean_object* v_x_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_){
_start:
{
if (lean_obj_tag(v_x_2755_) == 0)
{
lean_object* v___x_2761_; 
v___x_2761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2761_, 0, v_x_2754_);
return v___x_2761_;
}
else
{
lean_object* v_tail_2762_; uint8_t v___x_2763_; lean_object* v___x_2764_; 
v_tail_2762_ = lean_ctor_get(v_x_2755_, 1);
v___x_2763_ = 0;
v___x_2764_ = l_Lean_Meta_intro1Core(v_x_2754_, v___x_2763_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_);
if (lean_obj_tag(v___x_2764_) == 0)
{
lean_object* v_a_2765_; lean_object* v_fst_2766_; lean_object* v_snd_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; 
v_a_2765_ = lean_ctor_get(v___x_2764_, 0);
lean_inc(v_a_2765_);
lean_dec_ref_known(v___x_2764_, 1);
v_fst_2766_ = lean_ctor_get(v_a_2765_, 0);
lean_inc(v_fst_2766_);
v_snd_2767_ = lean_ctor_get(v_a_2765_, 1);
lean_inc(v_snd_2767_);
lean_dec(v_a_2765_);
v___x_2768_ = lean_unsigned_to_nat(0u);
v___x_2769_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toCases___closed__0));
v___x_2770_ = lean_box(0);
v___x_2771_ = l_Lean_MVarId_cases(v_snd_2767_, v_fst_2766_, v___x_2769_, v___x_2763_, v___x_2770_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_);
if (lean_obj_tag(v___x_2771_) == 0)
{
lean_object* v_a_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; uint8_t v___x_2775_; 
v_a_2772_ = lean_ctor_get(v___x_2771_, 0);
lean_inc(v_a_2772_);
lean_dec_ref_known(v___x_2771_, 1);
v___x_2773_ = lean_array_get_size(v_a_2772_);
v___x_2774_ = lean_unsigned_to_nat(1u);
v___x_2775_ = lean_nat_dec_eq(v___x_2773_, v___x_2774_);
if (v___x_2775_ == 0)
{
lean_object* v___x_2776_; lean_object* v___x_2777_; 
lean_dec(v_a_2772_);
v___x_2776_ = lean_obj_once(&l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__4___closed__1, &l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__4___closed__1_once, _init_l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__4___closed__1);
v___x_2777_ = l_Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0___redArg(v___x_2776_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_);
return v___x_2777_;
}
else
{
lean_object* v___x_2778_; lean_object* v_toInductionSubgoal_2779_; lean_object* v_mvarId_2780_; 
v___x_2778_ = lean_array_fget(v_a_2772_, v___x_2768_);
lean_dec(v_a_2772_);
v_toInductionSubgoal_2779_ = lean_ctor_get(v___x_2778_, 0);
lean_inc_ref(v_toInductionSubgoal_2779_);
lean_dec(v___x_2778_);
v_mvarId_2780_ = lean_ctor_get(v_toInductionSubgoal_2779_, 0);
lean_inc(v_mvarId_2780_);
lean_dec_ref(v_toInductionSubgoal_2779_);
v_x_2754_ = v_mvarId_2780_;
v_x_2755_ = v_tail_2762_;
goto _start;
}
}
else
{
lean_object* v_a_2782_; lean_object* v___x_2784_; uint8_t v_isShared_2785_; uint8_t v_isSharedCheck_2789_; 
v_a_2782_ = lean_ctor_get(v___x_2771_, 0);
v_isSharedCheck_2789_ = !lean_is_exclusive(v___x_2771_);
if (v_isSharedCheck_2789_ == 0)
{
v___x_2784_ = v___x_2771_;
v_isShared_2785_ = v_isSharedCheck_2789_;
goto v_resetjp_2783_;
}
else
{
lean_inc(v_a_2782_);
lean_dec(v___x_2771_);
v___x_2784_ = lean_box(0);
v_isShared_2785_ = v_isSharedCheck_2789_;
goto v_resetjp_2783_;
}
v_resetjp_2783_:
{
lean_object* v___x_2787_; 
if (v_isShared_2785_ == 0)
{
v___x_2787_ = v___x_2784_;
goto v_reusejp_2786_;
}
else
{
lean_object* v_reuseFailAlloc_2788_; 
v_reuseFailAlloc_2788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2788_, 0, v_a_2782_);
v___x_2787_ = v_reuseFailAlloc_2788_;
goto v_reusejp_2786_;
}
v_reusejp_2786_:
{
return v___x_2787_;
}
}
}
}
else
{
lean_object* v_a_2790_; lean_object* v___x_2792_; uint8_t v_isShared_2793_; uint8_t v_isSharedCheck_2797_; 
v_a_2790_ = lean_ctor_get(v___x_2764_, 0);
v_isSharedCheck_2797_ = !lean_is_exclusive(v___x_2764_);
if (v_isSharedCheck_2797_ == 0)
{
v___x_2792_ = v___x_2764_;
v_isShared_2793_ = v_isSharedCheck_2797_;
goto v_resetjp_2791_;
}
else
{
lean_inc(v_a_2790_);
lean_dec(v___x_2764_);
v___x_2792_ = lean_box(0);
v_isShared_2793_ = v_isSharedCheck_2797_;
goto v_resetjp_2791_;
}
v_resetjp_2791_:
{
lean_object* v___x_2795_; 
if (v_isShared_2793_ == 0)
{
v___x_2795_ = v___x_2792_;
goto v_reusejp_2794_;
}
else
{
lean_object* v_reuseFailAlloc_2796_; 
v_reuseFailAlloc_2796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2796_, 0, v_a_2790_);
v___x_2795_ = v_reuseFailAlloc_2796_;
goto v_reusejp_2794_;
}
v_reusejp_2794_:
{
return v___x_2795_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__4___boxed(lean_object* v_x_2798_, lean_object* v_x_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_, lean_object* v___y_2803_, lean_object* v___y_2804_){
_start:
{
lean_object* v_res_2805_; 
v_res_2805_ = l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__4(v_x_2798_, v_x_2799_, v___y_2800_, v___y_2801_, v___y_2802_, v___y_2803_);
lean_dec(v___y_2803_);
lean_dec_ref(v___y_2802_);
lean_dec(v___y_2801_);
lean_dec_ref(v___y_2800_);
lean_dec(v_x_2799_);
return v_res_2805_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__3(lean_object* v_a_2806_, lean_object* v_a_2807_){
_start:
{
if (lean_obj_tag(v_a_2806_) == 0)
{
lean_object* v___x_2808_; 
v___x_2808_ = l_List_reverse___redArg(v_a_2807_);
return v___x_2808_;
}
else
{
lean_object* v_head_2809_; uint8_t v___x_2810_; 
v_head_2809_ = lean_ctor_get(v_a_2806_, 0);
v___x_2810_ = lean_unbox(v_head_2809_);
if (v___x_2810_ == 0)
{
lean_object* v_tail_2811_; 
v_tail_2811_ = lean_ctor_get(v_a_2806_, 1);
lean_inc(v_tail_2811_);
lean_dec_ref_known(v_a_2806_, 2);
v_a_2806_ = v_tail_2811_;
goto _start;
}
else
{
lean_object* v_tail_2813_; lean_object* v___x_2815_; uint8_t v_isShared_2816_; uint8_t v_isSharedCheck_2821_; 
lean_inc(v_head_2809_);
v_tail_2813_ = lean_ctor_get(v_a_2806_, 1);
v_isSharedCheck_2821_ = !lean_is_exclusive(v_a_2806_);
if (v_isSharedCheck_2821_ == 0)
{
lean_object* v_unused_2822_; 
v_unused_2822_ = lean_ctor_get(v_a_2806_, 0);
lean_dec(v_unused_2822_);
v___x_2815_ = v_a_2806_;
v_isShared_2816_ = v_isSharedCheck_2821_;
goto v_resetjp_2814_;
}
else
{
lean_inc(v_tail_2813_);
lean_dec(v_a_2806_);
v___x_2815_ = lean_box(0);
v_isShared_2816_ = v_isSharedCheck_2821_;
goto v_resetjp_2814_;
}
v_resetjp_2814_:
{
lean_object* v___x_2818_; 
if (v_isShared_2816_ == 0)
{
lean_ctor_set(v___x_2815_, 1, v_a_2807_);
v___x_2818_ = v___x_2815_;
goto v_reusejp_2817_;
}
else
{
lean_object* v_reuseFailAlloc_2820_; 
v_reuseFailAlloc_2820_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2820_, 0, v_head_2809_);
lean_ctor_set(v_reuseFailAlloc_2820_, 1, v_a_2807_);
v___x_2818_ = v_reuseFailAlloc_2820_;
goto v_reusejp_2817_;
}
v_reusejp_2817_:
{
v_a_2806_ = v_tail_2813_;
v_a_2807_ = v___x_2818_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__5(lean_object* v_gs_2823_, lean_object* v_x_2824_, lean_object* v_x_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_){
_start:
{
if (lean_obj_tag(v_x_2824_) == 0)
{
lean_object* v___x_2831_; lean_object* v___x_2832_; 
lean_dec(v_gs_2823_);
v___x_2831_ = l_List_reverse___redArg(v_x_2825_);
v___x_2832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2832_, 0, v___x_2831_);
return v___x_2832_;
}
else
{
lean_object* v_head_2833_; lean_object* v_snd_2834_; lean_object* v_fst_2835_; lean_object* v_snd_2836_; lean_object* v_tail_2837_; lean_object* v___x_2839_; uint8_t v_isShared_2840_; uint8_t v_isSharedCheck_2961_; 
v_head_2833_ = lean_ctor_get(v_x_2824_, 0);
lean_inc(v_head_2833_);
v_snd_2834_ = lean_ctor_get(v_head_2833_, 1);
v_fst_2835_ = lean_ctor_get(v_snd_2834_, 0);
lean_inc(v_fst_2835_);
v_snd_2836_ = lean_ctor_get(v_snd_2834_, 1);
lean_inc(v_snd_2836_);
v_tail_2837_ = lean_ctor_get(v_x_2824_, 1);
v_isSharedCheck_2961_ = !lean_is_exclusive(v_x_2824_);
if (v_isSharedCheck_2961_ == 0)
{
lean_object* v_unused_2962_; 
v_unused_2962_ = lean_ctor_get(v_x_2824_, 0);
lean_dec(v_unused_2962_);
v___x_2839_ = v_x_2824_;
v_isShared_2840_ = v_isSharedCheck_2961_;
goto v_resetjp_2838_;
}
else
{
lean_inc(v_tail_2837_);
lean_dec(v_x_2824_);
v___x_2839_ = lean_box(0);
v_isShared_2840_ = v_isSharedCheck_2961_;
goto v_resetjp_2838_;
}
v_resetjp_2838_:
{
lean_object* v_fst_2841_; lean_object* v_fst_2842_; lean_object* v_snd_2843_; lean_object* v_variablesKept_2844_; lean_object* v_neqs_2845_; lean_object* v_fst_2847_; lean_object* v_snd_2848_; lean_object* v___y_2849_; lean_object* v___y_2850_; lean_object* v___y_2851_; lean_object* v___y_2852_; lean_object* v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; 
v_fst_2841_ = lean_ctor_get(v_head_2833_, 0);
lean_inc(v_fst_2841_);
lean_dec(v_head_2833_);
v_fst_2842_ = lean_ctor_get(v_fst_2835_, 0);
lean_inc(v_fst_2842_);
v_snd_2843_ = lean_ctor_get(v_fst_2835_, 1);
lean_inc(v_snd_2843_);
lean_dec(v_fst_2835_);
v_variablesKept_2844_ = lean_ctor_get(v_snd_2836_, 0);
lean_inc_n(v_variablesKept_2844_, 2);
v_neqs_2845_ = lean_ctor_get(v_snd_2836_, 1);
lean_inc(v_neqs_2845_);
lean_dec(v_snd_2836_);
v___x_2868_ = lean_box(0);
v___x_2869_ = l_List_filterTR_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__3(v_variablesKept_2844_, v___x_2868_);
v___x_2870_ = l_List_lengthTR___redArg(v___x_2869_);
lean_dec(v___x_2869_);
if (lean_obj_tag(v_neqs_2845_) == 0)
{
lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; 
v___x_2871_ = lean_unsigned_to_nat(1u);
v___x_2872_ = lean_nat_sub(v___x_2870_, v___x_2871_);
lean_dec(v___x_2870_);
v___x_2873_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesProd(v___x_2872_, v_snd_2843_, v_fst_2842_, v___y_2826_, v___y_2827_, v___y_2828_, v___y_2829_);
lean_dec(v___x_2872_);
if (lean_obj_tag(v___x_2873_) == 0)
{
lean_object* v_a_2874_; lean_object* v_fst_2875_; lean_object* v_snd_2876_; 
v_a_2874_ = lean_ctor_get(v___x_2873_, 0);
lean_inc(v_a_2874_);
lean_dec_ref_known(v___x_2873_, 1);
v_fst_2875_ = lean_ctor_get(v_a_2874_, 0);
lean_inc(v_fst_2875_);
v_snd_2876_ = lean_ctor_get(v_a_2874_, 1);
lean_inc(v_snd_2876_);
lean_dec(v_a_2874_);
v_fst_2847_ = v_fst_2875_;
v_snd_2848_ = v_snd_2876_;
v___y_2849_ = v___y_2826_;
v___y_2850_ = v___y_2827_;
v___y_2851_ = v___y_2828_;
v___y_2852_ = v___y_2829_;
goto v___jp_2846_;
}
else
{
lean_object* v_a_2877_; lean_object* v___x_2879_; uint8_t v_isShared_2880_; uint8_t v_isSharedCheck_2884_; 
lean_dec(v_variablesKept_2844_);
lean_dec(v_fst_2841_);
lean_del_object(v___x_2839_);
lean_dec(v_tail_2837_);
lean_dec(v_x_2825_);
lean_dec(v_gs_2823_);
v_a_2877_ = lean_ctor_get(v___x_2873_, 0);
v_isSharedCheck_2884_ = !lean_is_exclusive(v___x_2873_);
if (v_isSharedCheck_2884_ == 0)
{
v___x_2879_ = v___x_2873_;
v_isShared_2880_ = v_isSharedCheck_2884_;
goto v_resetjp_2878_;
}
else
{
lean_inc(v_a_2877_);
lean_dec(v___x_2873_);
v___x_2879_ = lean_box(0);
v_isShared_2880_ = v_isSharedCheck_2884_;
goto v_resetjp_2878_;
}
v_resetjp_2878_:
{
lean_object* v___x_2882_; 
if (v_isShared_2880_ == 0)
{
v___x_2882_ = v___x_2879_;
goto v_reusejp_2881_;
}
else
{
lean_object* v_reuseFailAlloc_2883_; 
v_reuseFailAlloc_2883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2883_, 0, v_a_2877_);
v___x_2882_ = v_reuseFailAlloc_2883_;
goto v_reusejp_2881_;
}
v_reusejp_2881_:
{
return v___x_2882_;
}
}
}
}
else
{
lean_object* v_val_2885_; lean_object* v___x_2886_; lean_object* v_zero_2887_; uint8_t v_isZero_2888_; 
v_val_2885_ = lean_ctor_get(v_neqs_2845_, 0);
lean_inc(v_val_2885_);
lean_dec_ref_known(v_neqs_2845_, 1);
v___x_2886_ = lean_box(0);
v_zero_2887_ = lean_unsigned_to_nat(0u);
v_isZero_2888_ = lean_nat_dec_eq(v_val_2885_, v_zero_2887_);
if (v_isZero_2888_ == 1)
{
lean_object* v___x_2889_; 
lean_dec(v_val_2885_);
v___x_2889_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesProd(v___x_2870_, v_snd_2843_, v_fst_2842_, v___y_2826_, v___y_2827_, v___y_2828_, v___y_2829_);
lean_dec(v___x_2870_);
if (lean_obj_tag(v___x_2889_) == 0)
{
lean_object* v_a_2890_; lean_object* v_fst_2891_; lean_object* v_snd_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; 
v_a_2890_ = lean_ctor_get(v___x_2889_, 0);
lean_inc(v_a_2890_);
lean_dec_ref_known(v___x_2889_, 1);
v_fst_2891_ = lean_ctor_get(v_a_2890_, 0);
lean_inc(v_fst_2891_);
v_snd_2892_ = lean_ctor_get(v_a_2890_, 1);
lean_inc(v_snd_2892_);
lean_dec(v_a_2890_);
v___x_2893_ = l_List_getLast_x21___redArg(v___x_2886_, v_snd_2892_);
v___x_2894_ = l_Lean_MVarId_tryClear(v_fst_2891_, v___x_2893_, v___y_2826_, v___y_2827_, v___y_2828_, v___y_2829_);
if (lean_obj_tag(v___x_2894_) == 0)
{
lean_object* v_a_2895_; 
v_a_2895_ = lean_ctor_get(v___x_2894_, 0);
lean_inc(v_a_2895_);
lean_dec_ref_known(v___x_2894_, 1);
v_fst_2847_ = v_a_2895_;
v_snd_2848_ = v_snd_2892_;
v___y_2849_ = v___y_2826_;
v___y_2850_ = v___y_2827_;
v___y_2851_ = v___y_2828_;
v___y_2852_ = v___y_2829_;
goto v___jp_2846_;
}
else
{
lean_object* v_a_2896_; lean_object* v___x_2898_; uint8_t v_isShared_2899_; uint8_t v_isSharedCheck_2903_; 
lean_dec(v_snd_2892_);
lean_dec(v_variablesKept_2844_);
lean_dec(v_fst_2841_);
lean_del_object(v___x_2839_);
lean_dec(v_tail_2837_);
lean_dec(v_x_2825_);
lean_dec(v_gs_2823_);
v_a_2896_ = lean_ctor_get(v___x_2894_, 0);
v_isSharedCheck_2903_ = !lean_is_exclusive(v___x_2894_);
if (v_isSharedCheck_2903_ == 0)
{
v___x_2898_ = v___x_2894_;
v_isShared_2899_ = v_isSharedCheck_2903_;
goto v_resetjp_2897_;
}
else
{
lean_inc(v_a_2896_);
lean_dec(v___x_2894_);
v___x_2898_ = lean_box(0);
v_isShared_2899_ = v_isSharedCheck_2903_;
goto v_resetjp_2897_;
}
v_resetjp_2897_:
{
lean_object* v___x_2901_; 
if (v_isShared_2899_ == 0)
{
v___x_2901_ = v___x_2898_;
goto v_reusejp_2900_;
}
else
{
lean_object* v_reuseFailAlloc_2902_; 
v_reuseFailAlloc_2902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2902_, 0, v_a_2896_);
v___x_2901_ = v_reuseFailAlloc_2902_;
goto v_reusejp_2900_;
}
v_reusejp_2900_:
{
return v___x_2901_;
}
}
}
}
else
{
lean_object* v_a_2904_; lean_object* v___x_2906_; uint8_t v_isShared_2907_; uint8_t v_isSharedCheck_2911_; 
lean_dec(v_variablesKept_2844_);
lean_dec(v_fst_2841_);
lean_del_object(v___x_2839_);
lean_dec(v_tail_2837_);
lean_dec(v_x_2825_);
lean_dec(v_gs_2823_);
v_a_2904_ = lean_ctor_get(v___x_2889_, 0);
v_isSharedCheck_2911_ = !lean_is_exclusive(v___x_2889_);
if (v_isSharedCheck_2911_ == 0)
{
v___x_2906_ = v___x_2889_;
v_isShared_2907_ = v_isSharedCheck_2911_;
goto v_resetjp_2905_;
}
else
{
lean_inc(v_a_2904_);
lean_dec(v___x_2889_);
v___x_2906_ = lean_box(0);
v_isShared_2907_ = v_isSharedCheck_2911_;
goto v_resetjp_2905_;
}
v_resetjp_2905_:
{
lean_object* v___x_2909_; 
if (v_isShared_2907_ == 0)
{
v___x_2909_ = v___x_2906_;
goto v_reusejp_2908_;
}
else
{
lean_object* v_reuseFailAlloc_2910_; 
v_reuseFailAlloc_2910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2910_, 0, v_a_2904_);
v___x_2909_ = v_reuseFailAlloc_2910_;
goto v_reusejp_2908_;
}
v_reusejp_2908_:
{
return v___x_2909_;
}
}
}
}
else
{
lean_object* v_one_2912_; lean_object* v_n_2913_; lean_object* v___x_2914_; 
v_one_2912_ = lean_unsigned_to_nat(1u);
v_n_2913_ = lean_nat_sub(v_val_2885_, v_one_2912_);
lean_dec(v_val_2885_);
v___x_2914_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesProd(v___x_2870_, v_snd_2843_, v_fst_2842_, v___y_2826_, v___y_2827_, v___y_2828_, v___y_2829_);
lean_dec(v___x_2870_);
if (lean_obj_tag(v___x_2914_) == 0)
{
lean_object* v_a_2915_; lean_object* v_fst_2916_; lean_object* v_snd_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; 
v_a_2915_ = lean_ctor_get(v___x_2914_, 0);
lean_inc(v_a_2915_);
lean_dec_ref_known(v___x_2914_, 1);
v_fst_2916_ = lean_ctor_get(v_a_2915_, 0);
lean_inc(v_fst_2916_);
v_snd_2917_ = lean_ctor_get(v_a_2915_, 1);
lean_inc(v_snd_2917_);
lean_dec(v_a_2915_);
v___x_2918_ = l_List_getLast_x21___redArg(v___x_2886_, v_snd_2917_);
v___x_2919_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesProd(v_n_2913_, v_fst_2916_, v___x_2918_, v___y_2826_, v___y_2827_, v___y_2828_, v___y_2829_);
lean_dec(v_n_2913_);
if (lean_obj_tag(v___x_2919_) == 0)
{
lean_object* v_a_2920_; lean_object* v_fst_2921_; lean_object* v_snd_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; 
v_a_2920_ = lean_ctor_get(v___x_2919_, 0);
lean_inc(v_a_2920_);
lean_dec_ref_known(v___x_2919_, 1);
v_fst_2921_ = lean_ctor_get(v_a_2920_, 0);
lean_inc(v_fst_2921_);
v_snd_2922_ = lean_ctor_get(v_a_2920_, 1);
lean_inc_n(v_snd_2922_, 2);
lean_dec(v_a_2920_);
v___x_2923_ = lean_array_mk(v_snd_2922_);
v___x_2924_ = l_Lean_MVarId_revert(v_fst_2921_, v___x_2923_, v_isZero_2888_, v_isZero_2888_, v___y_2826_, v___y_2827_, v___y_2828_, v___y_2829_);
if (lean_obj_tag(v___x_2924_) == 0)
{
lean_object* v_a_2925_; lean_object* v_snd_2926_; lean_object* v___x_2927_; 
v_a_2925_ = lean_ctor_get(v___x_2924_, 0);
lean_inc(v_a_2925_);
lean_dec_ref_known(v___x_2924_, 1);
v_snd_2926_ = lean_ctor_get(v_a_2925_, 1);
lean_inc(v_snd_2926_);
lean_dec(v_a_2925_);
v___x_2927_ = l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__4(v_snd_2926_, v_snd_2922_, v___y_2826_, v___y_2827_, v___y_2828_, v___y_2829_);
lean_dec(v_snd_2922_);
if (lean_obj_tag(v___x_2927_) == 0)
{
lean_object* v_a_2928_; 
v_a_2928_ = lean_ctor_get(v___x_2927_, 0);
lean_inc(v_a_2928_);
lean_dec_ref_known(v___x_2927_, 1);
v_fst_2847_ = v_a_2928_;
v_snd_2848_ = v_snd_2917_;
v___y_2849_ = v___y_2826_;
v___y_2850_ = v___y_2827_;
v___y_2851_ = v___y_2828_;
v___y_2852_ = v___y_2829_;
goto v___jp_2846_;
}
else
{
lean_object* v_a_2929_; lean_object* v___x_2931_; uint8_t v_isShared_2932_; uint8_t v_isSharedCheck_2936_; 
lean_dec(v_snd_2917_);
lean_dec(v_variablesKept_2844_);
lean_dec(v_fst_2841_);
lean_del_object(v___x_2839_);
lean_dec(v_tail_2837_);
lean_dec(v_x_2825_);
lean_dec(v_gs_2823_);
v_a_2929_ = lean_ctor_get(v___x_2927_, 0);
v_isSharedCheck_2936_ = !lean_is_exclusive(v___x_2927_);
if (v_isSharedCheck_2936_ == 0)
{
v___x_2931_ = v___x_2927_;
v_isShared_2932_ = v_isSharedCheck_2936_;
goto v_resetjp_2930_;
}
else
{
lean_inc(v_a_2929_);
lean_dec(v___x_2927_);
v___x_2931_ = lean_box(0);
v_isShared_2932_ = v_isSharedCheck_2936_;
goto v_resetjp_2930_;
}
v_resetjp_2930_:
{
lean_object* v___x_2934_; 
if (v_isShared_2932_ == 0)
{
v___x_2934_ = v___x_2931_;
goto v_reusejp_2933_;
}
else
{
lean_object* v_reuseFailAlloc_2935_; 
v_reuseFailAlloc_2935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2935_, 0, v_a_2929_);
v___x_2934_ = v_reuseFailAlloc_2935_;
goto v_reusejp_2933_;
}
v_reusejp_2933_:
{
return v___x_2934_;
}
}
}
}
else
{
lean_object* v_a_2937_; lean_object* v___x_2939_; uint8_t v_isShared_2940_; uint8_t v_isSharedCheck_2944_; 
lean_dec(v_snd_2922_);
lean_dec(v_snd_2917_);
lean_dec(v_variablesKept_2844_);
lean_dec(v_fst_2841_);
lean_del_object(v___x_2839_);
lean_dec(v_tail_2837_);
lean_dec(v_x_2825_);
lean_dec(v_gs_2823_);
v_a_2937_ = lean_ctor_get(v___x_2924_, 0);
v_isSharedCheck_2944_ = !lean_is_exclusive(v___x_2924_);
if (v_isSharedCheck_2944_ == 0)
{
v___x_2939_ = v___x_2924_;
v_isShared_2940_ = v_isSharedCheck_2944_;
goto v_resetjp_2938_;
}
else
{
lean_inc(v_a_2937_);
lean_dec(v___x_2924_);
v___x_2939_ = lean_box(0);
v_isShared_2940_ = v_isSharedCheck_2944_;
goto v_resetjp_2938_;
}
v_resetjp_2938_:
{
lean_object* v___x_2942_; 
if (v_isShared_2940_ == 0)
{
v___x_2942_ = v___x_2939_;
goto v_reusejp_2941_;
}
else
{
lean_object* v_reuseFailAlloc_2943_; 
v_reuseFailAlloc_2943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2943_, 0, v_a_2937_);
v___x_2942_ = v_reuseFailAlloc_2943_;
goto v_reusejp_2941_;
}
v_reusejp_2941_:
{
return v___x_2942_;
}
}
}
}
else
{
lean_object* v_a_2945_; lean_object* v___x_2947_; uint8_t v_isShared_2948_; uint8_t v_isSharedCheck_2952_; 
lean_dec(v_snd_2917_);
lean_dec(v_variablesKept_2844_);
lean_dec(v_fst_2841_);
lean_del_object(v___x_2839_);
lean_dec(v_tail_2837_);
lean_dec(v_x_2825_);
lean_dec(v_gs_2823_);
v_a_2945_ = lean_ctor_get(v___x_2919_, 0);
v_isSharedCheck_2952_ = !lean_is_exclusive(v___x_2919_);
if (v_isSharedCheck_2952_ == 0)
{
v___x_2947_ = v___x_2919_;
v_isShared_2948_ = v_isSharedCheck_2952_;
goto v_resetjp_2946_;
}
else
{
lean_inc(v_a_2945_);
lean_dec(v___x_2919_);
v___x_2947_ = lean_box(0);
v_isShared_2948_ = v_isSharedCheck_2952_;
goto v_resetjp_2946_;
}
v_resetjp_2946_:
{
lean_object* v___x_2950_; 
if (v_isShared_2948_ == 0)
{
v___x_2950_ = v___x_2947_;
goto v_reusejp_2949_;
}
else
{
lean_object* v_reuseFailAlloc_2951_; 
v_reuseFailAlloc_2951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2951_, 0, v_a_2945_);
v___x_2950_ = v_reuseFailAlloc_2951_;
goto v_reusejp_2949_;
}
v_reusejp_2949_:
{
return v___x_2950_;
}
}
}
}
else
{
lean_object* v_a_2953_; lean_object* v___x_2955_; uint8_t v_isShared_2956_; uint8_t v_isSharedCheck_2960_; 
lean_dec(v_n_2913_);
lean_dec(v_variablesKept_2844_);
lean_dec(v_fst_2841_);
lean_del_object(v___x_2839_);
lean_dec(v_tail_2837_);
lean_dec(v_x_2825_);
lean_dec(v_gs_2823_);
v_a_2953_ = lean_ctor_get(v___x_2914_, 0);
v_isSharedCheck_2960_ = !lean_is_exclusive(v___x_2914_);
if (v_isSharedCheck_2960_ == 0)
{
v___x_2955_ = v___x_2914_;
v_isShared_2956_ = v_isSharedCheck_2960_;
goto v_resetjp_2954_;
}
else
{
lean_inc(v_a_2953_);
lean_dec(v___x_2914_);
v___x_2955_ = lean_box(0);
v_isShared_2956_ = v_isSharedCheck_2960_;
goto v_resetjp_2954_;
}
v_resetjp_2954_:
{
lean_object* v___x_2958_; 
if (v_isShared_2956_ == 0)
{
v___x_2958_ = v___x_2955_;
goto v_reusejp_2957_;
}
else
{
lean_object* v_reuseFailAlloc_2959_; 
v_reuseFailAlloc_2959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2959_, 0, v_a_2953_);
v___x_2958_ = v_reuseFailAlloc_2959_;
goto v_reusejp_2957_;
}
v_reusejp_2957_:
{
return v___x_2958_;
}
}
}
}
}
v___jp_2846_:
{
lean_object* v___f_2853_; lean_object* v___x_2854_; 
lean_inc(v_fst_2847_);
lean_inc(v_gs_2823_);
v___f_2853_ = lean_alloc_closure((void*)(l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__5___lam__0___boxed), 10, 5);
lean_closure_set(v___f_2853_, 0, v_gs_2823_);
lean_closure_set(v___f_2853_, 1, v_variablesKept_2844_);
lean_closure_set(v___f_2853_, 2, v_snd_2848_);
lean_closure_set(v___f_2853_, 3, v_fst_2841_);
lean_closure_set(v___f_2853_, 4, v_fst_2847_);
v___x_2854_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor_spec__0___redArg(v_fst_2847_, v___f_2853_, v___y_2849_, v___y_2850_, v___y_2851_, v___y_2852_);
if (lean_obj_tag(v___x_2854_) == 0)
{
lean_object* v_a_2855_; lean_object* v___x_2857_; 
v_a_2855_ = lean_ctor_get(v___x_2854_, 0);
lean_inc(v_a_2855_);
lean_dec_ref_known(v___x_2854_, 1);
if (v_isShared_2840_ == 0)
{
lean_ctor_set(v___x_2839_, 1, v_x_2825_);
lean_ctor_set(v___x_2839_, 0, v_a_2855_);
v___x_2857_ = v___x_2839_;
goto v_reusejp_2856_;
}
else
{
lean_object* v_reuseFailAlloc_2859_; 
v_reuseFailAlloc_2859_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2859_, 0, v_a_2855_);
lean_ctor_set(v_reuseFailAlloc_2859_, 1, v_x_2825_);
v___x_2857_ = v_reuseFailAlloc_2859_;
goto v_reusejp_2856_;
}
v_reusejp_2856_:
{
v_x_2824_ = v_tail_2837_;
v_x_2825_ = v___x_2857_;
goto _start;
}
}
else
{
lean_object* v_a_2860_; lean_object* v___x_2862_; uint8_t v_isShared_2863_; uint8_t v_isSharedCheck_2867_; 
lean_del_object(v___x_2839_);
lean_dec(v_tail_2837_);
lean_dec(v_x_2825_);
lean_dec(v_gs_2823_);
v_a_2860_ = lean_ctor_get(v___x_2854_, 0);
v_isSharedCheck_2867_ = !lean_is_exclusive(v___x_2854_);
if (v_isSharedCheck_2867_ == 0)
{
v___x_2862_ = v___x_2854_;
v_isShared_2863_ = v_isSharedCheck_2867_;
goto v_resetjp_2861_;
}
else
{
lean_inc(v_a_2860_);
lean_dec(v___x_2854_);
v___x_2862_ = lean_box(0);
v_isShared_2863_ = v_isSharedCheck_2867_;
goto v_resetjp_2861_;
}
v_resetjp_2861_:
{
lean_object* v___x_2865_; 
if (v_isShared_2863_ == 0)
{
v___x_2865_ = v___x_2862_;
goto v_reusejp_2864_;
}
else
{
lean_object* v_reuseFailAlloc_2866_; 
v_reuseFailAlloc_2866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2866_, 0, v_a_2860_);
v___x_2865_ = v_reuseFailAlloc_2866_;
goto v_reusejp_2864_;
}
v_reusejp_2864_:
{
return v___x_2865_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__5___boxed(lean_object* v_gs_2963_, lean_object* v_x_2964_, lean_object* v_x_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_, lean_object* v___y_2968_, lean_object* v___y_2969_, lean_object* v___y_2970_){
_start:
{
lean_object* v_res_2971_; 
v_res_2971_ = l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__5(v_gs_2963_, v_x_2964_, v_x_2965_, v___y_2966_, v___y_2967_, v___y_2968_, v___y_2969_);
lean_dec(v___y_2969_);
lean_dec_ref(v___y_2968_);
lean_dec(v___y_2967_);
lean_dec_ref(v___y_2966_);
return v_res_2971_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive(lean_object* v_mvar_2972_, lean_object* v_cs_2973_, lean_object* v_gs_2974_, lean_object* v_s_2975_, lean_object* v_h_2976_, lean_object* v_a_2977_, lean_object* v_a_2978_, lean_object* v_a_2979_, lean_object* v_a_2980_){
_start:
{
lean_object* v___x_2982_; lean_object* v_zero_2983_; uint8_t v_isZero_2984_; 
v___x_2982_ = l_List_lengthTR___redArg(v_s_2975_);
v_zero_2983_ = lean_unsigned_to_nat(0u);
v_isZero_2984_ = lean_nat_dec_eq(v___x_2982_, v_zero_2983_);
if (v_isZero_2984_ == 1)
{
lean_object* v___x_2985_; uint8_t v___x_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; 
lean_dec(v___x_2982_);
lean_dec(v_s_2975_);
lean_dec(v_gs_2974_);
lean_dec(v_cs_2973_);
v___x_2985_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toCases___closed__0));
v___x_2986_ = 0;
v___x_2987_ = lean_box(0);
v___x_2988_ = l_Lean_MVarId_cases(v_mvar_2972_, v_h_2976_, v___x_2985_, v___x_2986_, v___x_2987_, v_a_2977_, v_a_2978_, v_a_2979_, v_a_2980_);
if (lean_obj_tag(v___x_2988_) == 0)
{
lean_object* v___x_2990_; uint8_t v_isShared_2991_; uint8_t v_isSharedCheck_2996_; 
v_isSharedCheck_2996_ = !lean_is_exclusive(v___x_2988_);
if (v_isSharedCheck_2996_ == 0)
{
lean_object* v_unused_2997_; 
v_unused_2997_ = lean_ctor_get(v___x_2988_, 0);
lean_dec(v_unused_2997_);
v___x_2990_ = v___x_2988_;
v_isShared_2991_ = v_isSharedCheck_2996_;
goto v_resetjp_2989_;
}
else
{
lean_dec(v___x_2988_);
v___x_2990_ = lean_box(0);
v_isShared_2991_ = v_isSharedCheck_2996_;
goto v_resetjp_2989_;
}
v_resetjp_2989_:
{
lean_object* v___x_2992_; lean_object* v___x_2994_; 
v___x_2992_ = lean_box(0);
if (v_isShared_2991_ == 0)
{
lean_ctor_set(v___x_2990_, 0, v___x_2992_);
v___x_2994_ = v___x_2990_;
goto v_reusejp_2993_;
}
else
{
lean_object* v_reuseFailAlloc_2995_; 
v_reuseFailAlloc_2995_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2995_, 0, v___x_2992_);
v___x_2994_ = v_reuseFailAlloc_2995_;
goto v_reusejp_2993_;
}
v_reusejp_2993_:
{
return v___x_2994_;
}
}
}
else
{
lean_object* v_a_2998_; lean_object* v___x_3000_; uint8_t v_isShared_3001_; uint8_t v_isSharedCheck_3005_; 
v_a_2998_ = lean_ctor_get(v___x_2988_, 0);
v_isSharedCheck_3005_ = !lean_is_exclusive(v___x_2988_);
if (v_isSharedCheck_3005_ == 0)
{
v___x_3000_ = v___x_2988_;
v_isShared_3001_ = v_isSharedCheck_3005_;
goto v_resetjp_2999_;
}
else
{
lean_inc(v_a_2998_);
lean_dec(v___x_2988_);
v___x_3000_ = lean_box(0);
v_isShared_3001_ = v_isSharedCheck_3005_;
goto v_resetjp_2999_;
}
v_resetjp_2999_:
{
lean_object* v___x_3003_; 
if (v_isShared_3001_ == 0)
{
v___x_3003_ = v___x_3000_;
goto v_reusejp_3002_;
}
else
{
lean_object* v_reuseFailAlloc_3004_; 
v_reuseFailAlloc_3004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3004_, 0, v_a_2998_);
v___x_3003_ = v_reuseFailAlloc_3004_;
goto v_reusejp_3002_;
}
v_reusejp_3002_:
{
return v___x_3003_;
}
}
}
}
else
{
lean_object* v_one_3006_; lean_object* v_n_3007_; lean_object* v___x_3008_; 
v_one_3006_ = lean_unsigned_to_nat(1u);
v_n_3007_ = lean_nat_sub(v___x_2982_, v_one_3006_);
lean_dec(v___x_2982_);
v___x_3008_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesSum(v_n_3007_, v_mvar_2972_, v_h_2976_, v_a_2977_, v_a_2978_, v_a_2979_, v_a_2980_);
lean_dec(v_n_3007_);
if (lean_obj_tag(v___x_3008_) == 0)
{
lean_object* v_a_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; 
v_a_3009_ = lean_ctor_get(v___x_3008_, 0);
lean_inc(v_a_3009_);
lean_dec_ref_known(v___x_3008_, 1);
v___x_3010_ = l_List_zipWith___at___00List_zip_spec__0(lean_box(0), lean_box(0), v_a_3009_, v_s_2975_);
v___x_3011_ = l_List_zipWith___at___00List_zip_spec__0(lean_box(0), lean_box(0), v_cs_2973_, v___x_3010_);
v___x_3012_ = lean_box(0);
v___x_3013_ = l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__5(v_gs_2974_, v___x_3011_, v___x_3012_, v_a_2977_, v_a_2978_, v_a_2979_, v_a_2980_);
if (lean_obj_tag(v___x_3013_) == 0)
{
lean_object* v___x_3015_; uint8_t v_isShared_3016_; uint8_t v_isSharedCheck_3021_; 
v_isSharedCheck_3021_ = !lean_is_exclusive(v___x_3013_);
if (v_isSharedCheck_3021_ == 0)
{
lean_object* v_unused_3022_; 
v_unused_3022_ = lean_ctor_get(v___x_3013_, 0);
lean_dec(v_unused_3022_);
v___x_3015_ = v___x_3013_;
v_isShared_3016_ = v_isSharedCheck_3021_;
goto v_resetjp_3014_;
}
else
{
lean_dec(v___x_3013_);
v___x_3015_ = lean_box(0);
v_isShared_3016_ = v_isSharedCheck_3021_;
goto v_resetjp_3014_;
}
v_resetjp_3014_:
{
lean_object* v___x_3017_; lean_object* v___x_3019_; 
v___x_3017_ = lean_box(0);
if (v_isShared_3016_ == 0)
{
lean_ctor_set(v___x_3015_, 0, v___x_3017_);
v___x_3019_ = v___x_3015_;
goto v_reusejp_3018_;
}
else
{
lean_object* v_reuseFailAlloc_3020_; 
v_reuseFailAlloc_3020_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3020_, 0, v___x_3017_);
v___x_3019_ = v_reuseFailAlloc_3020_;
goto v_reusejp_3018_;
}
v_reusejp_3018_:
{
return v___x_3019_;
}
}
}
else
{
lean_object* v_a_3023_; lean_object* v___x_3025_; uint8_t v_isShared_3026_; uint8_t v_isSharedCheck_3030_; 
v_a_3023_ = lean_ctor_get(v___x_3013_, 0);
v_isSharedCheck_3030_ = !lean_is_exclusive(v___x_3013_);
if (v_isSharedCheck_3030_ == 0)
{
v___x_3025_ = v___x_3013_;
v_isShared_3026_ = v_isSharedCheck_3030_;
goto v_resetjp_3024_;
}
else
{
lean_inc(v_a_3023_);
lean_dec(v___x_3013_);
v___x_3025_ = lean_box(0);
v_isShared_3026_ = v_isSharedCheck_3030_;
goto v_resetjp_3024_;
}
v_resetjp_3024_:
{
lean_object* v___x_3028_; 
if (v_isShared_3026_ == 0)
{
v___x_3028_ = v___x_3025_;
goto v_reusejp_3027_;
}
else
{
lean_object* v_reuseFailAlloc_3029_; 
v_reuseFailAlloc_3029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3029_, 0, v_a_3023_);
v___x_3028_ = v_reuseFailAlloc_3029_;
goto v_reusejp_3027_;
}
v_reusejp_3027_:
{
return v___x_3028_;
}
}
}
}
else
{
lean_object* v_a_3031_; lean_object* v___x_3033_; uint8_t v_isShared_3034_; uint8_t v_isSharedCheck_3038_; 
lean_dec(v_s_2975_);
lean_dec(v_gs_2974_);
lean_dec(v_cs_2973_);
v_a_3031_ = lean_ctor_get(v___x_3008_, 0);
v_isSharedCheck_3038_ = !lean_is_exclusive(v___x_3008_);
if (v_isSharedCheck_3038_ == 0)
{
v___x_3033_ = v___x_3008_;
v_isShared_3034_ = v_isSharedCheck_3038_;
goto v_resetjp_3032_;
}
else
{
lean_inc(v_a_3031_);
lean_dec(v___x_3008_);
v___x_3033_ = lean_box(0);
v_isShared_3034_ = v_isSharedCheck_3038_;
goto v_resetjp_3032_;
}
v_resetjp_3032_:
{
lean_object* v___x_3036_; 
if (v_isShared_3034_ == 0)
{
v___x_3036_ = v___x_3033_;
goto v_reusejp_3035_;
}
else
{
lean_object* v_reuseFailAlloc_3037_; 
v_reuseFailAlloc_3037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3037_, 0, v_a_3031_);
v___x_3036_ = v_reuseFailAlloc_3037_;
goto v_reusejp_3035_;
}
v_reusejp_3035_:
{
return v___x_3036_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive___boxed(lean_object* v_mvar_3039_, lean_object* v_cs_3040_, lean_object* v_gs_3041_, lean_object* v_s_3042_, lean_object* v_h_3043_, lean_object* v_a_3044_, lean_object* v_a_3045_, lean_object* v_a_3046_, lean_object* v_a_3047_, lean_object* v_a_3048_){
_start:
{
lean_object* v_res_3049_; 
v_res_3049_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive(v_mvar_3039_, v_cs_3040_, v_gs_3041_, v_s_3042_, v_h_3043_, v_a_3044_, v_a_3045_, v_a_3046_, v_a_3047_);
lean_dec(v_a_3047_);
lean_dec_ref(v_a_3046_);
lean_dec(v_a_3045_);
lean_dec_ref(v_a_3044_);
return v_res_3049_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__1___redArg(lean_object* v_type_3050_, lean_object* v_k_3051_, uint8_t v_cleanupAnnotations_3052_, uint8_t v_whnfType_3053_, lean_object* v___y_3054_, lean_object* v___y_3055_, lean_object* v___y_3056_, lean_object* v___y_3057_){
_start:
{
lean_object* v___f_3059_; lean_object* v___x_3060_; 
v___f_3059_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__4___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_3059_, 0, v_k_3051_);
v___x_3060_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_3050_, v___f_3059_, v_cleanupAnnotations_3052_, v_whnfType_3053_, v___y_3054_, v___y_3055_, v___y_3056_, v___y_3057_);
if (lean_obj_tag(v___x_3060_) == 0)
{
lean_object* v_a_3061_; lean_object* v___x_3063_; uint8_t v_isShared_3064_; uint8_t v_isSharedCheck_3068_; 
v_a_3061_ = lean_ctor_get(v___x_3060_, 0);
v_isSharedCheck_3068_ = !lean_is_exclusive(v___x_3060_);
if (v_isSharedCheck_3068_ == 0)
{
v___x_3063_ = v___x_3060_;
v_isShared_3064_ = v_isSharedCheck_3068_;
goto v_resetjp_3062_;
}
else
{
lean_inc(v_a_3061_);
lean_dec(v___x_3060_);
v___x_3063_ = lean_box(0);
v_isShared_3064_ = v_isSharedCheck_3068_;
goto v_resetjp_3062_;
}
v_resetjp_3062_:
{
lean_object* v___x_3066_; 
if (v_isShared_3064_ == 0)
{
v___x_3066_ = v___x_3063_;
goto v_reusejp_3065_;
}
else
{
lean_object* v_reuseFailAlloc_3067_; 
v_reuseFailAlloc_3067_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3067_, 0, v_a_3061_);
v___x_3066_ = v_reuseFailAlloc_3067_;
goto v_reusejp_3065_;
}
v_reusejp_3065_:
{
return v___x_3066_;
}
}
}
else
{
lean_object* v_a_3069_; lean_object* v___x_3071_; uint8_t v_isShared_3072_; uint8_t v_isSharedCheck_3076_; 
v_a_3069_ = lean_ctor_get(v___x_3060_, 0);
v_isSharedCheck_3076_ = !lean_is_exclusive(v___x_3060_);
if (v_isSharedCheck_3076_ == 0)
{
v___x_3071_ = v___x_3060_;
v_isShared_3072_ = v_isSharedCheck_3076_;
goto v_resetjp_3070_;
}
else
{
lean_inc(v_a_3069_);
lean_dec(v___x_3060_);
v___x_3071_ = lean_box(0);
v_isShared_3072_ = v_isSharedCheck_3076_;
goto v_resetjp_3070_;
}
v_resetjp_3070_:
{
lean_object* v___x_3074_; 
if (v_isShared_3072_ == 0)
{
v___x_3074_ = v___x_3071_;
goto v_reusejp_3073_;
}
else
{
lean_object* v_reuseFailAlloc_3075_; 
v_reuseFailAlloc_3075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3075_, 0, v_a_3069_);
v___x_3074_ = v_reuseFailAlloc_3075_;
goto v_reusejp_3073_;
}
v_reusejp_3073_:
{
return v___x_3074_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__1___redArg___boxed(lean_object* v_type_3077_, lean_object* v_k_3078_, lean_object* v_cleanupAnnotations_3079_, lean_object* v_whnfType_3080_, lean_object* v___y_3081_, lean_object* v___y_3082_, lean_object* v___y_3083_, lean_object* v___y_3084_, lean_object* v___y_3085_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3086_; uint8_t v_whnfType_boxed_3087_; lean_object* v_res_3088_; 
v_cleanupAnnotations_boxed_3086_ = lean_unbox(v_cleanupAnnotations_3079_);
v_whnfType_boxed_3087_ = lean_unbox(v_whnfType_3080_);
v_res_3088_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__1___redArg(v_type_3077_, v_k_3078_, v_cleanupAnnotations_boxed_3086_, v_whnfType_boxed_3087_, v___y_3081_, v___y_3082_, v___y_3083_, v___y_3084_);
lean_dec(v___y_3084_);
lean_dec_ref(v___y_3083_);
lean_dec(v___y_3082_);
lean_dec_ref(v___y_3081_);
return v_res_3088_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__1(lean_object* v_00_u03b1_3089_, lean_object* v_type_3090_, lean_object* v_k_3091_, uint8_t v_cleanupAnnotations_3092_, uint8_t v_whnfType_3093_, lean_object* v___y_3094_, lean_object* v___y_3095_, lean_object* v___y_3096_, lean_object* v___y_3097_){
_start:
{
lean_object* v___x_3099_; 
v___x_3099_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__1___redArg(v_type_3090_, v_k_3091_, v_cleanupAnnotations_3092_, v_whnfType_3093_, v___y_3094_, v___y_3095_, v___y_3096_, v___y_3097_);
return v___x_3099_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__1___boxed(lean_object* v_00_u03b1_3100_, lean_object* v_type_3101_, lean_object* v_k_3102_, lean_object* v_cleanupAnnotations_3103_, lean_object* v_whnfType_3104_, lean_object* v___y_3105_, lean_object* v___y_3106_, lean_object* v___y_3107_, lean_object* v___y_3108_, lean_object* v___y_3109_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3110_; uint8_t v_whnfType_boxed_3111_; lean_object* v_res_3112_; 
v_cleanupAnnotations_boxed_3110_ = lean_unbox(v_cleanupAnnotations_3103_);
v_whnfType_boxed_3111_ = lean_unbox(v_whnfType_3104_);
v_res_3112_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__1(v_00_u03b1_3100_, v_type_3101_, v_k_3102_, v_cleanupAnnotations_boxed_3110_, v_whnfType_boxed_3111_, v___y_3105_, v___y_3106_, v___y_3107_, v___y_3108_);
lean_dec(v___y_3108_);
lean_dec_ref(v___y_3107_);
lean_dec(v___y_3106_);
lean_dec_ref(v___y_3105_);
return v_res_3112_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__3___redArg(lean_object* v_e_3113_, lean_object* v___y_3114_){
_start:
{
uint8_t v___x_3116_; 
v___x_3116_ = l_Lean_Expr_hasMVar(v_e_3113_);
if (v___x_3116_ == 0)
{
lean_object* v___x_3117_; 
v___x_3117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3117_, 0, v_e_3113_);
return v___x_3117_;
}
else
{
lean_object* v___x_3118_; lean_object* v_mctx_3119_; lean_object* v___x_3120_; lean_object* v_fst_3121_; lean_object* v_snd_3122_; lean_object* v___x_3123_; lean_object* v_cache_3124_; lean_object* v_zetaDeltaFVarIds_3125_; lean_object* v_postponed_3126_; lean_object* v_diag_3127_; lean_object* v___x_3129_; uint8_t v_isShared_3130_; uint8_t v_isSharedCheck_3136_; 
v___x_3118_ = lean_st_ref_get(v___y_3114_);
v_mctx_3119_ = lean_ctor_get(v___x_3118_, 0);
lean_inc_ref(v_mctx_3119_);
lean_dec(v___x_3118_);
v___x_3120_ = l_Lean_instantiateMVarsCore(v_mctx_3119_, v_e_3113_);
v_fst_3121_ = lean_ctor_get(v___x_3120_, 0);
lean_inc(v_fst_3121_);
v_snd_3122_ = lean_ctor_get(v___x_3120_, 1);
lean_inc(v_snd_3122_);
lean_dec_ref(v___x_3120_);
v___x_3123_ = lean_st_ref_take(v___y_3114_);
v_cache_3124_ = lean_ctor_get(v___x_3123_, 1);
v_zetaDeltaFVarIds_3125_ = lean_ctor_get(v___x_3123_, 2);
v_postponed_3126_ = lean_ctor_get(v___x_3123_, 3);
v_diag_3127_ = lean_ctor_get(v___x_3123_, 4);
v_isSharedCheck_3136_ = !lean_is_exclusive(v___x_3123_);
if (v_isSharedCheck_3136_ == 0)
{
lean_object* v_unused_3137_; 
v_unused_3137_ = lean_ctor_get(v___x_3123_, 0);
lean_dec(v_unused_3137_);
v___x_3129_ = v___x_3123_;
v_isShared_3130_ = v_isSharedCheck_3136_;
goto v_resetjp_3128_;
}
else
{
lean_inc(v_diag_3127_);
lean_inc(v_postponed_3126_);
lean_inc(v_zetaDeltaFVarIds_3125_);
lean_inc(v_cache_3124_);
lean_dec(v___x_3123_);
v___x_3129_ = lean_box(0);
v_isShared_3130_ = v_isSharedCheck_3136_;
goto v_resetjp_3128_;
}
v_resetjp_3128_:
{
lean_object* v___x_3132_; 
if (v_isShared_3130_ == 0)
{
lean_ctor_set(v___x_3129_, 0, v_snd_3122_);
v___x_3132_ = v___x_3129_;
goto v_reusejp_3131_;
}
else
{
lean_object* v_reuseFailAlloc_3135_; 
v_reuseFailAlloc_3135_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3135_, 0, v_snd_3122_);
lean_ctor_set(v_reuseFailAlloc_3135_, 1, v_cache_3124_);
lean_ctor_set(v_reuseFailAlloc_3135_, 2, v_zetaDeltaFVarIds_3125_);
lean_ctor_set(v_reuseFailAlloc_3135_, 3, v_postponed_3126_);
lean_ctor_set(v_reuseFailAlloc_3135_, 4, v_diag_3127_);
v___x_3132_ = v_reuseFailAlloc_3135_;
goto v_reusejp_3131_;
}
v_reusejp_3131_:
{
lean_object* v___x_3133_; lean_object* v___x_3134_; 
v___x_3133_ = lean_st_ref_put(v___y_3114_, v___x_3132_);
v___x_3134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3134_, 0, v_fst_3121_);
return v___x_3134_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__3___redArg___boxed(lean_object* v_e_3138_, lean_object* v___y_3139_, lean_object* v___y_3140_){
_start:
{
lean_object* v_res_3141_; 
v_res_3141_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__3___redArg(v_e_3138_, v___y_3139_);
lean_dec(v___y_3139_);
return v_res_3141_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__3(lean_object* v_e_3142_, lean_object* v___y_3143_, lean_object* v___y_3144_, lean_object* v___y_3145_, lean_object* v___y_3146_){
_start:
{
lean_object* v___x_3148_; 
v___x_3148_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__3___redArg(v_e_3142_, v___y_3144_);
return v___x_3148_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__3___boxed(lean_object* v_e_3149_, lean_object* v___y_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_, lean_object* v___y_3153_, lean_object* v___y_3154_){
_start:
{
lean_object* v_res_3155_; 
v_res_3155_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__3(v_e_3149_, v___y_3150_, v___y_3151_, v___y_3152_, v___y_3153_);
lean_dec(v___y_3153_);
lean_dec_ref(v___y_3152_);
lean_dec(v___y_3151_);
lean_dec_ref(v___y_3150_);
return v_res_3155_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__4___redArg(lean_object* v_thm_3156_, lean_object* v___y_3157_){
_start:
{
lean_object* v___x_3159_; lean_object* v_env_3160_; lean_object* v_toConstantVal_3161_; lean_object* v_value_3162_; lean_object* v_all_3163_; uint8_t v___y_3165_; lean_object* v_type_3173_; uint8_t v___x_3174_; 
v___x_3159_ = lean_st_ref_get(v___y_3157_);
v_env_3160_ = lean_ctor_get(v___x_3159_, 0);
lean_inc_ref_n(v_env_3160_, 2);
lean_dec(v___x_3159_);
v_toConstantVal_3161_ = lean_ctor_get(v_thm_3156_, 0);
v_value_3162_ = lean_ctor_get(v_thm_3156_, 1);
v_all_3163_ = lean_ctor_get(v_thm_3156_, 2);
v_type_3173_ = lean_ctor_get(v_toConstantVal_3161_, 2);
v___x_3174_ = l_Lean_Environment_hasUnsafe(v_env_3160_, v_type_3173_);
if (v___x_3174_ == 0)
{
uint8_t v___x_3175_; 
v___x_3175_ = l_Lean_Environment_hasUnsafe(v_env_3160_, v_value_3162_);
v___y_3165_ = v___x_3175_;
goto v___jp_3164_;
}
else
{
lean_dec_ref(v_env_3160_);
v___y_3165_ = v___x_3174_;
goto v___jp_3164_;
}
v___jp_3164_:
{
if (v___y_3165_ == 0)
{
lean_object* v___x_3166_; lean_object* v___x_3167_; 
v___x_3166_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3166_, 0, v_thm_3156_);
v___x_3167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3167_, 0, v___x_3166_);
return v___x_3167_;
}
else
{
lean_object* v___x_3168_; uint8_t v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; 
lean_inc(v_all_3163_);
lean_inc_ref(v_value_3162_);
lean_inc_ref(v_toConstantVal_3161_);
lean_dec_ref(v_thm_3156_);
v___x_3168_ = lean_box(0);
v___x_3169_ = 0;
v___x_3170_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3170_, 0, v_toConstantVal_3161_);
lean_ctor_set(v___x_3170_, 1, v_value_3162_);
lean_ctor_set(v___x_3170_, 2, v___x_3168_);
lean_ctor_set(v___x_3170_, 3, v_all_3163_);
lean_ctor_set_uint8(v___x_3170_, sizeof(void*)*4, v___x_3169_);
v___x_3171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3171_, 0, v___x_3170_);
v___x_3172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3172_, 0, v___x_3171_);
return v___x_3172_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__4___redArg___boxed(lean_object* v_thm_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_){
_start:
{
lean_object* v_res_3179_; 
v_res_3179_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__4___redArg(v_thm_3176_, v___y_3177_);
lean_dec(v___y_3177_);
return v_res_3179_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__4(lean_object* v_thm_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_){
_start:
{
lean_object* v___x_3186_; 
v___x_3186_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__4___redArg(v_thm_3180_, v___y_3184_);
return v___x_3186_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__4___boxed(lean_object* v_thm_3187_, lean_object* v___y_3188_, lean_object* v___y_3189_, lean_object* v___y_3190_, lean_object* v___y_3191_, lean_object* v___y_3192_){
_start:
{
lean_object* v_res_3193_; 
v_res_3193_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__4(v_thm_3187_, v___y_3188_, v___y_3189_, v___y_3190_, v___y_3191_);
lean_dec(v___y_3191_);
lean_dec_ref(v___y_3190_);
lean_dec(v___y_3189_);
lean_dec_ref(v___y_3188_);
return v_res_3193_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__5___redArg(lean_object* v_name_3194_, lean_object* v_levelParams_3195_, lean_object* v_type_3196_, lean_object* v_value_3197_, lean_object* v_hints_3198_, lean_object* v___y_3199_){
_start:
{
lean_object* v___x_3201_; uint8_t v___y_3203_; uint8_t v___y_3210_; lean_object* v_env_3213_; uint8_t v___x_3214_; 
v___x_3201_ = lean_st_ref_get(v___y_3199_);
v_env_3213_ = lean_ctor_get(v___x_3201_, 0);
lean_inc_ref_n(v_env_3213_, 2);
lean_dec(v___x_3201_);
v___x_3214_ = l_Lean_Environment_hasUnsafe(v_env_3213_, v_type_3196_);
if (v___x_3214_ == 0)
{
uint8_t v___x_3215_; 
v___x_3215_ = l_Lean_Environment_hasUnsafe(v_env_3213_, v_value_3197_);
v___y_3210_ = v___x_3215_;
goto v___jp_3209_;
}
else
{
lean_dec_ref(v_env_3213_);
v___y_3210_ = v___x_3214_;
goto v___jp_3209_;
}
v___jp_3202_:
{
lean_object* v___x_3204_; lean_object* v___x_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; lean_object* v___x_3208_; 
lean_inc(v_name_3194_);
v___x_3204_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3204_, 0, v_name_3194_);
lean_ctor_set(v___x_3204_, 1, v_levelParams_3195_);
lean_ctor_set(v___x_3204_, 2, v_type_3196_);
v___x_3205_ = lean_box(0);
v___x_3206_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3206_, 0, v_name_3194_);
lean_ctor_set(v___x_3206_, 1, v___x_3205_);
v___x_3207_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3207_, 0, v___x_3204_);
lean_ctor_set(v___x_3207_, 1, v_value_3197_);
lean_ctor_set(v___x_3207_, 2, v_hints_3198_);
lean_ctor_set(v___x_3207_, 3, v___x_3206_);
lean_ctor_set_uint8(v___x_3207_, sizeof(void*)*4, v___y_3203_);
v___x_3208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3208_, 0, v___x_3207_);
return v___x_3208_;
}
v___jp_3209_:
{
if (v___y_3210_ == 0)
{
uint8_t v___x_3211_; 
v___x_3211_ = 1;
v___y_3203_ = v___x_3211_;
goto v___jp_3202_;
}
else
{
uint8_t v___x_3212_; 
v___x_3212_ = 0;
v___y_3203_ = v___x_3212_;
goto v___jp_3202_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__5___redArg___boxed(lean_object* v_name_3216_, lean_object* v_levelParams_3217_, lean_object* v_type_3218_, lean_object* v_value_3219_, lean_object* v_hints_3220_, lean_object* v___y_3221_, lean_object* v___y_3222_){
_start:
{
lean_object* v_res_3223_; 
v_res_3223_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__5___redArg(v_name_3216_, v_levelParams_3217_, v_type_3218_, v_value_3219_, v_hints_3220_, v___y_3221_);
lean_dec(v___y_3221_);
return v_res_3223_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__5(lean_object* v_name_3224_, lean_object* v_levelParams_3225_, lean_object* v_type_3226_, lean_object* v_value_3227_, lean_object* v_hints_3228_, lean_object* v___y_3229_, lean_object* v___y_3230_, lean_object* v___y_3231_, lean_object* v___y_3232_){
_start:
{
lean_object* v___x_3234_; 
v___x_3234_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__5___redArg(v_name_3224_, v_levelParams_3225_, v_type_3226_, v_value_3227_, v_hints_3228_, v___y_3232_);
return v___x_3234_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__5___boxed(lean_object* v_name_3235_, lean_object* v_levelParams_3236_, lean_object* v_type_3237_, lean_object* v_value_3238_, lean_object* v_hints_3239_, lean_object* v___y_3240_, lean_object* v___y_3241_, lean_object* v___y_3242_, lean_object* v___y_3243_, lean_object* v___y_3244_){
_start:
{
lean_object* v_res_3245_; 
v_res_3245_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__5(v_name_3235_, v_levelParams_3236_, v_type_3237_, v_value_3238_, v_hints_3239_, v___y_3240_, v___y_3241_, v___y_3242_, v___y_3243_);
lean_dec(v___y_3243_);
lean_dec_ref(v___y_3242_);
lean_dec(v___y_3241_);
lean_dec_ref(v___y_3240_);
return v_res_3245_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__0(lean_object* v_univs_3246_, lean_object* v___x_3247_, lean_object* v___x_3248_, lean_object* v_x_3249_, lean_object* v_x_3250_, lean_object* v___y_3251_, lean_object* v___y_3252_, lean_object* v___y_3253_, lean_object* v___y_3254_){
_start:
{
if (lean_obj_tag(v_x_3249_) == 0)
{
lean_object* v___x_3256_; lean_object* v___x_3257_; 
lean_dec(v___x_3248_);
lean_dec(v___x_3247_);
lean_dec(v_univs_3246_);
v___x_3256_ = l_List_reverse___redArg(v_x_3250_);
v___x_3257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3257_, 0, v___x_3256_);
return v___x_3257_;
}
else
{
lean_object* v_head_3258_; lean_object* v_tail_3259_; lean_object* v___x_3261_; uint8_t v_isShared_3262_; uint8_t v_isSharedCheck_3277_; 
v_head_3258_ = lean_ctor_get(v_x_3249_, 0);
v_tail_3259_ = lean_ctor_get(v_x_3249_, 1);
v_isSharedCheck_3277_ = !lean_is_exclusive(v_x_3249_);
if (v_isSharedCheck_3277_ == 0)
{
v___x_3261_ = v_x_3249_;
v_isShared_3262_ = v_isSharedCheck_3277_;
goto v_resetjp_3260_;
}
else
{
lean_inc(v_tail_3259_);
lean_inc(v_head_3258_);
lean_dec(v_x_3249_);
v___x_3261_ = lean_box(0);
v_isShared_3262_ = v_isSharedCheck_3277_;
goto v_resetjp_3260_;
}
v_resetjp_3260_:
{
lean_object* v___x_3263_; 
lean_inc(v___x_3248_);
lean_inc(v___x_3247_);
lean_inc(v_univs_3246_);
v___x_3263_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp(v_univs_3246_, v___x_3247_, v___x_3248_, v_head_3258_, v___y_3251_, v___y_3252_, v___y_3253_, v___y_3254_);
if (lean_obj_tag(v___x_3263_) == 0)
{
lean_object* v_a_3264_; lean_object* v___x_3266_; 
v_a_3264_ = lean_ctor_get(v___x_3263_, 0);
lean_inc(v_a_3264_);
lean_dec_ref_known(v___x_3263_, 1);
if (v_isShared_3262_ == 0)
{
lean_ctor_set(v___x_3261_, 1, v_x_3250_);
lean_ctor_set(v___x_3261_, 0, v_a_3264_);
v___x_3266_ = v___x_3261_;
goto v_reusejp_3265_;
}
else
{
lean_object* v_reuseFailAlloc_3268_; 
v_reuseFailAlloc_3268_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3268_, 0, v_a_3264_);
lean_ctor_set(v_reuseFailAlloc_3268_, 1, v_x_3250_);
v___x_3266_ = v_reuseFailAlloc_3268_;
goto v_reusejp_3265_;
}
v_reusejp_3265_:
{
v_x_3249_ = v_tail_3259_;
v_x_3250_ = v___x_3266_;
goto _start;
}
}
else
{
lean_object* v_a_3269_; lean_object* v___x_3271_; uint8_t v_isShared_3272_; uint8_t v_isSharedCheck_3276_; 
lean_del_object(v___x_3261_);
lean_dec(v_tail_3259_);
lean_dec(v_x_3250_);
lean_dec(v___x_3248_);
lean_dec(v___x_3247_);
lean_dec(v_univs_3246_);
v_a_3269_ = lean_ctor_get(v___x_3263_, 0);
v_isSharedCheck_3276_ = !lean_is_exclusive(v___x_3263_);
if (v_isSharedCheck_3276_ == 0)
{
v___x_3271_ = v___x_3263_;
v_isShared_3272_ = v_isSharedCheck_3276_;
goto v_resetjp_3270_;
}
else
{
lean_inc(v_a_3269_);
lean_dec(v___x_3263_);
v___x_3271_ = lean_box(0);
v_isShared_3272_ = v_isSharedCheck_3276_;
goto v_resetjp_3270_;
}
v_resetjp_3270_:
{
lean_object* v___x_3274_; 
if (v_isShared_3272_ == 0)
{
v___x_3274_ = v___x_3271_;
goto v_reusejp_3273_;
}
else
{
lean_object* v_reuseFailAlloc_3275_; 
v_reuseFailAlloc_3275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3275_, 0, v_a_3269_);
v___x_3274_ = v_reuseFailAlloc_3275_;
goto v_reusejp_3273_;
}
v_reusejp_3273_:
{
return v___x_3274_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__0___boxed(lean_object* v_univs_3278_, lean_object* v___x_3279_, lean_object* v___x_3280_, lean_object* v_x_3281_, lean_object* v_x_3282_, lean_object* v___y_3283_, lean_object* v___y_3284_, lean_object* v___y_3285_, lean_object* v___y_3286_, lean_object* v___y_3287_){
_start:
{
lean_object* v_res_3288_; 
v_res_3288_ = l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__0(v_univs_3278_, v___x_3279_, v___x_3280_, v_x_3281_, v_x_3282_, v___y_3283_, v___y_3284_, v___y_3285_, v___y_3286_);
lean_dec(v___y_3286_);
lean_dec_ref(v___y_3285_);
lean_dec(v___y_3284_);
lean_dec_ref(v___y_3283_);
return v_res_3288_;
}
}
static lean_object* _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___lam__0___closed__3(void){
_start:
{
lean_object* v___x_3293_; lean_object* v___x_3294_; 
v___x_3293_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___lam__0___closed__2));
v___x_3294_ = l_Lean_stringToMessageData(v___x_3293_);
return v___x_3294_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___lam__0(lean_object* v_name_3295_, lean_object* v_univs_3296_, lean_object* v_numParams_3297_, lean_object* v_ctors_3298_, lean_object* v___x_3299_, lean_object* v_fvars_3300_, lean_object* v_ty_3301_, lean_object* v___y_3302_, lean_object* v___y_3303_, lean_object* v___y_3304_, lean_object* v___y_3305_){
_start:
{
uint8_t v___x_3370_; 
v___x_3370_ = l_Lean_Expr_isProp(v_ty_3301_);
if (v___x_3370_ == 0)
{
lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v_a_3373_; lean_object* v___x_3375_; uint8_t v_isShared_3376_; uint8_t v_isSharedCheck_3380_; 
lean_dec_ref(v_fvars_3300_);
lean_dec(v___x_3299_);
lean_dec(v_ctors_3298_);
lean_dec(v_numParams_3297_);
lean_dec(v_univs_3296_);
lean_dec(v_name_3295_);
v___x_3371_ = lean_obj_once(&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___lam__0___closed__3, &l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___lam__0___closed__3_once, _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___lam__0___closed__3);
v___x_3372_ = l_Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0___redArg(v___x_3371_, v___y_3302_, v___y_3303_, v___y_3304_, v___y_3305_);
v_a_3373_ = lean_ctor_get(v___x_3372_, 0);
v_isSharedCheck_3380_ = !lean_is_exclusive(v___x_3372_);
if (v_isSharedCheck_3380_ == 0)
{
v___x_3375_ = v___x_3372_;
v_isShared_3376_ = v_isSharedCheck_3380_;
goto v_resetjp_3374_;
}
else
{
lean_inc(v_a_3373_);
lean_dec(v___x_3372_);
v___x_3375_ = lean_box(0);
v_isShared_3376_ = v_isSharedCheck_3380_;
goto v_resetjp_3374_;
}
v_resetjp_3374_:
{
lean_object* v___x_3378_; 
if (v_isShared_3376_ == 0)
{
v___x_3378_ = v___x_3375_;
goto v_reusejp_3377_;
}
else
{
lean_object* v_reuseFailAlloc_3379_; 
v_reuseFailAlloc_3379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3379_, 0, v_a_3373_);
v___x_3378_ = v_reuseFailAlloc_3379_;
goto v_reusejp_3377_;
}
v_reusejp_3377_:
{
return v___x_3378_;
}
}
}
else
{
goto v___jp_3307_;
}
v___jp_3307_:
{
lean_object* v___x_3308_; lean_object* v_lhs_3309_; lean_object* v_fvars_x27_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; 
lean_inc(v_univs_3296_);
v___x_3308_ = l_Lean_mkConst(v_name_3295_, v_univs_3296_);
v_lhs_3309_ = l_Lean_mkAppN(v___x_3308_, v_fvars_3300_);
lean_inc_ref(v_fvars_3300_);
v_fvars_x27_3310_ = lean_array_to_list(v_fvars_3300_);
v___x_3311_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__1___closed__1));
lean_inc(v_numParams_3297_);
lean_inc(v_fvars_x27_3310_);
v___x_3312_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), v_fvars_x27_3310_, v_fvars_x27_3310_, v_numParams_3297_, v___x_3311_);
v___x_3313_ = l_List_drop___redArg(v_numParams_3297_, v_fvars_x27_3310_);
lean_dec(v_fvars_x27_3310_);
v___x_3314_ = lean_box(0);
v___x_3315_ = l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__0(v_univs_3296_, v___x_3312_, v___x_3313_, v_ctors_3298_, v___x_3314_, v___y_3302_, v___y_3303_, v___y_3304_, v___y_3305_);
if (lean_obj_tag(v___x_3315_) == 0)
{
lean_object* v_a_3316_; lean_object* v___x_3317_; lean_object* v_fst_3318_; lean_object* v_snd_3319_; lean_object* v___x_3321_; uint8_t v_isShared_3322_; uint8_t v_isSharedCheck_3361_; 
v_a_3316_ = lean_ctor_get(v___x_3315_, 0);
lean_inc(v_a_3316_);
lean_dec_ref_known(v___x_3315_, 1);
v___x_3317_ = l_List_unzipTR___redArg(v_a_3316_);
v_fst_3318_ = lean_ctor_get(v___x_3317_, 0);
v_snd_3319_ = lean_ctor_get(v___x_3317_, 1);
v_isSharedCheck_3361_ = !lean_is_exclusive(v___x_3317_);
if (v_isSharedCheck_3361_ == 0)
{
v___x_3321_ = v___x_3317_;
v_isShared_3322_ = v_isSharedCheck_3361_;
goto v_resetjp_3320_;
}
else
{
lean_inc(v_snd_3319_);
lean_inc(v_fst_3318_);
lean_dec(v___x_3317_);
v___x_3321_ = lean_box(0);
v_isShared_3322_ = v_isSharedCheck_3361_;
goto v_resetjp_3320_;
}
v_resetjp_3320_:
{
lean_object* v___x_3323_; uint8_t v___x_3324_; uint8_t v___x_3325_; uint8_t v___x_3326_; lean_object* v___x_3327_; 
v___x_3323_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkOrList(v_snd_3319_);
v___x_3324_ = 0;
v___x_3325_ = 1;
v___x_3326_ = 1;
lean_inc_ref(v___x_3323_);
v___x_3327_ = l_Lean_Meta_mkLambdaFVars(v_fvars_3300_, v___x_3323_, v___x_3324_, v___x_3325_, v___x_3324_, v___x_3325_, v___x_3326_, v___y_3302_, v___y_3303_, v___y_3304_, v___y_3305_);
if (lean_obj_tag(v___x_3327_) == 0)
{
lean_object* v_a_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; 
v_a_3328_ = lean_ctor_get(v___x_3327_, 0);
lean_inc(v_a_3328_);
lean_dec_ref_known(v___x_3327_, 1);
v___x_3329_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___lam__0___closed__1));
v___x_3330_ = l_Lean_mkConst(v___x_3329_, v___x_3299_);
v___x_3331_ = l_Lean_mkAppB(v___x_3330_, v_lhs_3309_, v___x_3323_);
v___x_3332_ = l_Lean_Meta_mkForallFVars(v_fvars_3300_, v___x_3331_, v___x_3324_, v___x_3325_, v___x_3325_, v___x_3326_, v___y_3302_, v___y_3303_, v___y_3304_, v___y_3305_);
lean_dec_ref(v_fvars_3300_);
if (lean_obj_tag(v___x_3332_) == 0)
{
lean_object* v_a_3333_; lean_object* v___x_3335_; uint8_t v_isShared_3336_; uint8_t v_isSharedCheck_3344_; 
v_a_3333_ = lean_ctor_get(v___x_3332_, 0);
v_isSharedCheck_3344_ = !lean_is_exclusive(v___x_3332_);
if (v_isSharedCheck_3344_ == 0)
{
v___x_3335_ = v___x_3332_;
v_isShared_3336_ = v_isSharedCheck_3344_;
goto v_resetjp_3334_;
}
else
{
lean_inc(v_a_3333_);
lean_dec(v___x_3332_);
v___x_3335_ = lean_box(0);
v_isShared_3336_ = v_isSharedCheck_3344_;
goto v_resetjp_3334_;
}
v_resetjp_3334_:
{
lean_object* v___x_3338_; 
if (v_isShared_3322_ == 0)
{
lean_ctor_set(v___x_3321_, 1, v_a_3328_);
v___x_3338_ = v___x_3321_;
goto v_reusejp_3337_;
}
else
{
lean_object* v_reuseFailAlloc_3343_; 
v_reuseFailAlloc_3343_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3343_, 0, v_fst_3318_);
lean_ctor_set(v_reuseFailAlloc_3343_, 1, v_a_3328_);
v___x_3338_ = v_reuseFailAlloc_3343_;
goto v_reusejp_3337_;
}
v_reusejp_3337_:
{
lean_object* v___x_3339_; lean_object* v___x_3341_; 
v___x_3339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3339_, 0, v_a_3333_);
lean_ctor_set(v___x_3339_, 1, v___x_3338_);
if (v_isShared_3336_ == 0)
{
lean_ctor_set(v___x_3335_, 0, v___x_3339_);
v___x_3341_ = v___x_3335_;
goto v_reusejp_3340_;
}
else
{
lean_object* v_reuseFailAlloc_3342_; 
v_reuseFailAlloc_3342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3342_, 0, v___x_3339_);
v___x_3341_ = v_reuseFailAlloc_3342_;
goto v_reusejp_3340_;
}
v_reusejp_3340_:
{
return v___x_3341_;
}
}
}
}
else
{
lean_object* v_a_3345_; lean_object* v___x_3347_; uint8_t v_isShared_3348_; uint8_t v_isSharedCheck_3352_; 
lean_dec(v_a_3328_);
lean_del_object(v___x_3321_);
lean_dec(v_fst_3318_);
v_a_3345_ = lean_ctor_get(v___x_3332_, 0);
v_isSharedCheck_3352_ = !lean_is_exclusive(v___x_3332_);
if (v_isSharedCheck_3352_ == 0)
{
v___x_3347_ = v___x_3332_;
v_isShared_3348_ = v_isSharedCheck_3352_;
goto v_resetjp_3346_;
}
else
{
lean_inc(v_a_3345_);
lean_dec(v___x_3332_);
v___x_3347_ = lean_box(0);
v_isShared_3348_ = v_isSharedCheck_3352_;
goto v_resetjp_3346_;
}
v_resetjp_3346_:
{
lean_object* v___x_3350_; 
if (v_isShared_3348_ == 0)
{
v___x_3350_ = v___x_3347_;
goto v_reusejp_3349_;
}
else
{
lean_object* v_reuseFailAlloc_3351_; 
v_reuseFailAlloc_3351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3351_, 0, v_a_3345_);
v___x_3350_ = v_reuseFailAlloc_3351_;
goto v_reusejp_3349_;
}
v_reusejp_3349_:
{
return v___x_3350_;
}
}
}
}
else
{
lean_object* v_a_3353_; lean_object* v___x_3355_; uint8_t v_isShared_3356_; uint8_t v_isSharedCheck_3360_; 
lean_dec_ref(v___x_3323_);
lean_del_object(v___x_3321_);
lean_dec(v_fst_3318_);
lean_dec_ref(v_lhs_3309_);
lean_dec_ref(v_fvars_3300_);
lean_dec(v___x_3299_);
v_a_3353_ = lean_ctor_get(v___x_3327_, 0);
v_isSharedCheck_3360_ = !lean_is_exclusive(v___x_3327_);
if (v_isSharedCheck_3360_ == 0)
{
v___x_3355_ = v___x_3327_;
v_isShared_3356_ = v_isSharedCheck_3360_;
goto v_resetjp_3354_;
}
else
{
lean_inc(v_a_3353_);
lean_dec(v___x_3327_);
v___x_3355_ = lean_box(0);
v_isShared_3356_ = v_isSharedCheck_3360_;
goto v_resetjp_3354_;
}
v_resetjp_3354_:
{
lean_object* v___x_3358_; 
if (v_isShared_3356_ == 0)
{
v___x_3358_ = v___x_3355_;
goto v_reusejp_3357_;
}
else
{
lean_object* v_reuseFailAlloc_3359_; 
v_reuseFailAlloc_3359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3359_, 0, v_a_3353_);
v___x_3358_ = v_reuseFailAlloc_3359_;
goto v_reusejp_3357_;
}
v_reusejp_3357_:
{
return v___x_3358_;
}
}
}
}
}
else
{
lean_object* v_a_3362_; lean_object* v___x_3364_; uint8_t v_isShared_3365_; uint8_t v_isSharedCheck_3369_; 
lean_dec_ref(v_lhs_3309_);
lean_dec_ref(v_fvars_3300_);
lean_dec(v___x_3299_);
v_a_3362_ = lean_ctor_get(v___x_3315_, 0);
v_isSharedCheck_3369_ = !lean_is_exclusive(v___x_3315_);
if (v_isSharedCheck_3369_ == 0)
{
v___x_3364_ = v___x_3315_;
v_isShared_3365_ = v_isSharedCheck_3369_;
goto v_resetjp_3363_;
}
else
{
lean_inc(v_a_3362_);
lean_dec(v___x_3315_);
v___x_3364_ = lean_box(0);
v_isShared_3365_ = v_isSharedCheck_3369_;
goto v_resetjp_3363_;
}
v_resetjp_3363_:
{
lean_object* v___x_3367_; 
if (v_isShared_3365_ == 0)
{
v___x_3367_ = v___x_3364_;
goto v_reusejp_3366_;
}
else
{
lean_object* v_reuseFailAlloc_3368_; 
v_reuseFailAlloc_3368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3368_, 0, v_a_3362_);
v___x_3367_ = v_reuseFailAlloc_3368_;
goto v_reusejp_3366_;
}
v_reusejp_3366_:
{
return v___x_3367_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___lam__0___boxed(lean_object* v_name_3381_, lean_object* v_univs_3382_, lean_object* v_numParams_3383_, lean_object* v_ctors_3384_, lean_object* v___x_3385_, lean_object* v_fvars_3386_, lean_object* v_ty_3387_, lean_object* v___y_3388_, lean_object* v___y_3389_, lean_object* v___y_3390_, lean_object* v___y_3391_, lean_object* v___y_3392_){
_start:
{
lean_object* v_res_3393_; 
v_res_3393_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___lam__0(v_name_3381_, v_univs_3382_, v_numParams_3383_, v_ctors_3384_, v___x_3385_, v_fvars_3386_, v_ty_3387_, v___y_3388_, v___y_3389_, v___y_3390_, v___y_3391_);
lean_dec(v___y_3391_);
lean_dec_ref(v___y_3390_);
lean_dec(v___y_3389_);
lean_dec_ref(v___y_3388_);
lean_dec_ref(v_ty_3387_);
return v_res_3393_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__2(lean_object* v_a_3394_, lean_object* v_a_3395_){
_start:
{
if (lean_obj_tag(v_a_3394_) == 0)
{
lean_object* v___x_3396_; 
v___x_3396_ = l_List_reverse___redArg(v_a_3395_);
return v___x_3396_;
}
else
{
lean_object* v_head_3397_; lean_object* v_tail_3398_; lean_object* v___x_3400_; uint8_t v_isShared_3401_; uint8_t v_isSharedCheck_3407_; 
v_head_3397_ = lean_ctor_get(v_a_3394_, 0);
v_tail_3398_ = lean_ctor_get(v_a_3394_, 1);
v_isSharedCheck_3407_ = !lean_is_exclusive(v_a_3394_);
if (v_isSharedCheck_3407_ == 0)
{
v___x_3400_ = v_a_3394_;
v_isShared_3401_ = v_isSharedCheck_3407_;
goto v_resetjp_3399_;
}
else
{
lean_inc(v_tail_3398_);
lean_inc(v_head_3397_);
lean_dec(v_a_3394_);
v___x_3400_ = lean_box(0);
v_isShared_3401_ = v_isSharedCheck_3407_;
goto v_resetjp_3399_;
}
v_resetjp_3399_:
{
lean_object* v___x_3402_; lean_object* v___x_3404_; 
v___x_3402_ = l_Lean_Expr_fvar___override(v_head_3397_);
if (v_isShared_3401_ == 0)
{
lean_ctor_set(v___x_3400_, 1, v_a_3395_);
lean_ctor_set(v___x_3400_, 0, v___x_3402_);
v___x_3404_ = v___x_3400_;
goto v_reusejp_3403_;
}
else
{
lean_object* v_reuseFailAlloc_3406_; 
v_reuseFailAlloc_3406_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3406_, 0, v___x_3402_);
lean_ctor_set(v_reuseFailAlloc_3406_, 1, v_a_3395_);
v___x_3404_ = v_reuseFailAlloc_3406_;
goto v_reusejp_3403_;
}
v_reusejp_3403_:
{
v_a_3394_ = v_tail_3398_;
v_a_3395_ = v___x_3404_;
goto _start;
}
}
}
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__6___closed__0(void){
_start:
{
lean_object* v___x_3408_; double v___x_3409_; 
v___x_3408_ = lean_unsigned_to_nat(0u);
v___x_3409_ = lean_float_of_nat(v___x_3408_);
return v___x_3409_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__6(lean_object* v_cls_3413_, lean_object* v_msg_3414_, lean_object* v___y_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_, lean_object* v___y_3418_){
_start:
{
lean_object* v_ref_3420_; lean_object* v___x_3421_; lean_object* v_a_3422_; lean_object* v___x_3424_; uint8_t v_isShared_3425_; uint8_t v_isSharedCheck_3467_; 
v_ref_3420_ = lean_ctor_get(v___y_3417_, 2);
v___x_3421_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0_spec__0(v_msg_3414_, v___y_3415_, v___y_3416_, v___y_3417_, v___y_3418_);
v_a_3422_ = lean_ctor_get(v___x_3421_, 0);
v_isSharedCheck_3467_ = !lean_is_exclusive(v___x_3421_);
if (v_isSharedCheck_3467_ == 0)
{
v___x_3424_ = v___x_3421_;
v_isShared_3425_ = v_isSharedCheck_3467_;
goto v_resetjp_3423_;
}
else
{
lean_inc(v_a_3422_);
lean_dec(v___x_3421_);
v___x_3424_ = lean_box(0);
v_isShared_3425_ = v_isSharedCheck_3467_;
goto v_resetjp_3423_;
}
v_resetjp_3423_:
{
lean_object* v___x_3426_; lean_object* v_traceState_3427_; lean_object* v_env_3428_; lean_object* v_nextMacroScope_3429_; lean_object* v_ngen_3430_; lean_object* v_auxDeclNGen_3431_; lean_object* v_cache_3432_; lean_object* v_recordedDeps_3433_; lean_object* v_messages_3434_; lean_object* v_infoState_3435_; lean_object* v_snapshotTasks_3436_; lean_object* v___x_3438_; uint8_t v_isShared_3439_; uint8_t v_isSharedCheck_3466_; 
v___x_3426_ = lean_st_ref_take(v___y_3418_);
v_traceState_3427_ = lean_ctor_get(v___x_3426_, 4);
v_env_3428_ = lean_ctor_get(v___x_3426_, 0);
v_nextMacroScope_3429_ = lean_ctor_get(v___x_3426_, 1);
v_ngen_3430_ = lean_ctor_get(v___x_3426_, 2);
v_auxDeclNGen_3431_ = lean_ctor_get(v___x_3426_, 3);
v_cache_3432_ = lean_ctor_get(v___x_3426_, 5);
v_recordedDeps_3433_ = lean_ctor_get(v___x_3426_, 6);
v_messages_3434_ = lean_ctor_get(v___x_3426_, 7);
v_infoState_3435_ = lean_ctor_get(v___x_3426_, 8);
v_snapshotTasks_3436_ = lean_ctor_get(v___x_3426_, 9);
v_isSharedCheck_3466_ = !lean_is_exclusive(v___x_3426_);
if (v_isSharedCheck_3466_ == 0)
{
v___x_3438_ = v___x_3426_;
v_isShared_3439_ = v_isSharedCheck_3466_;
goto v_resetjp_3437_;
}
else
{
lean_inc(v_snapshotTasks_3436_);
lean_inc(v_infoState_3435_);
lean_inc(v_messages_3434_);
lean_inc(v_recordedDeps_3433_);
lean_inc(v_cache_3432_);
lean_inc(v_traceState_3427_);
lean_inc(v_auxDeclNGen_3431_);
lean_inc(v_ngen_3430_);
lean_inc(v_nextMacroScope_3429_);
lean_inc(v_env_3428_);
lean_dec(v___x_3426_);
v___x_3438_ = lean_box(0);
v_isShared_3439_ = v_isSharedCheck_3466_;
goto v_resetjp_3437_;
}
v_resetjp_3437_:
{
uint64_t v_tid_3440_; lean_object* v_traces_3441_; lean_object* v___x_3443_; uint8_t v_isShared_3444_; uint8_t v_isSharedCheck_3465_; 
v_tid_3440_ = lean_ctor_get_uint64(v_traceState_3427_, sizeof(void*)*1);
v_traces_3441_ = lean_ctor_get(v_traceState_3427_, 0);
v_isSharedCheck_3465_ = !lean_is_exclusive(v_traceState_3427_);
if (v_isSharedCheck_3465_ == 0)
{
v___x_3443_ = v_traceState_3427_;
v_isShared_3444_ = v_isSharedCheck_3465_;
goto v_resetjp_3442_;
}
else
{
lean_inc(v_traces_3441_);
lean_dec(v_traceState_3427_);
v___x_3443_ = lean_box(0);
v_isShared_3444_ = v_isSharedCheck_3465_;
goto v_resetjp_3442_;
}
v_resetjp_3442_:
{
lean_object* v___x_3445_; lean_object* v___x_3446_; double v___x_3447_; uint8_t v___x_3448_; lean_object* v___x_3449_; lean_object* v___x_3450_; lean_object* v___x_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; lean_object* v___x_3454_; lean_object* v___x_3456_; 
v___x_3445_ = lean_box(0);
v___x_3446_ = lean_box(0);
v___x_3447_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__6___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__6___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__6___closed__0);
v___x_3448_ = 0;
v___x_3449_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__6___closed__1));
v___x_3450_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3450_, 0, v_cls_3413_);
lean_ctor_set(v___x_3450_, 1, v___x_3446_);
lean_ctor_set(v___x_3450_, 2, v___x_3449_);
lean_ctor_set_float(v___x_3450_, sizeof(void*)*3, v___x_3447_);
lean_ctor_set_float(v___x_3450_, sizeof(void*)*3 + 8, v___x_3447_);
lean_ctor_set_uint8(v___x_3450_, sizeof(void*)*3 + 16, v___x_3448_);
v___x_3451_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__6___closed__2));
v___x_3452_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3452_, 0, v___x_3450_);
lean_ctor_set(v___x_3452_, 1, v_a_3422_);
lean_ctor_set(v___x_3452_, 2, v___x_3451_);
lean_inc(v_ref_3420_);
v___x_3453_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3453_, 0, v_ref_3420_);
lean_ctor_set(v___x_3453_, 1, v___x_3452_);
v___x_3454_ = l_Lean_PersistentArray_push___redArg(v_traces_3441_, v___x_3453_);
if (v_isShared_3444_ == 0)
{
lean_ctor_set(v___x_3443_, 0, v___x_3454_);
v___x_3456_ = v___x_3443_;
goto v_reusejp_3455_;
}
else
{
lean_object* v_reuseFailAlloc_3464_; 
v_reuseFailAlloc_3464_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3464_, 0, v___x_3454_);
lean_ctor_set_uint64(v_reuseFailAlloc_3464_, sizeof(void*)*1, v_tid_3440_);
v___x_3456_ = v_reuseFailAlloc_3464_;
goto v_reusejp_3455_;
}
v_reusejp_3455_:
{
lean_object* v___x_3458_; 
if (v_isShared_3439_ == 0)
{
lean_ctor_set(v___x_3438_, 4, v___x_3456_);
v___x_3458_ = v___x_3438_;
goto v_reusejp_3457_;
}
else
{
lean_object* v_reuseFailAlloc_3463_; 
v_reuseFailAlloc_3463_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3463_, 0, v_env_3428_);
lean_ctor_set(v_reuseFailAlloc_3463_, 1, v_nextMacroScope_3429_);
lean_ctor_set(v_reuseFailAlloc_3463_, 2, v_ngen_3430_);
lean_ctor_set(v_reuseFailAlloc_3463_, 3, v_auxDeclNGen_3431_);
lean_ctor_set(v_reuseFailAlloc_3463_, 4, v___x_3456_);
lean_ctor_set(v_reuseFailAlloc_3463_, 5, v_cache_3432_);
lean_ctor_set(v_reuseFailAlloc_3463_, 6, v_recordedDeps_3433_);
lean_ctor_set(v_reuseFailAlloc_3463_, 7, v_messages_3434_);
lean_ctor_set(v_reuseFailAlloc_3463_, 8, v_infoState_3435_);
lean_ctor_set(v_reuseFailAlloc_3463_, 9, v_snapshotTasks_3436_);
v___x_3458_ = v_reuseFailAlloc_3463_;
goto v_reusejp_3457_;
}
v_reusejp_3457_:
{
lean_object* v___x_3459_; lean_object* v___x_3461_; 
v___x_3459_ = lean_st_ref_put(v___y_3418_, v___x_3458_);
if (v_isShared_3425_ == 0)
{
lean_ctor_set(v___x_3424_, 0, v___x_3445_);
v___x_3461_ = v___x_3424_;
goto v_reusejp_3460_;
}
else
{
lean_object* v_reuseFailAlloc_3462_; 
v_reuseFailAlloc_3462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3462_, 0, v___x_3445_);
v___x_3461_ = v_reuseFailAlloc_3462_;
goto v_reusejp_3460_;
}
v_reusejp_3460_:
{
return v___x_3461_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__6___boxed(lean_object* v_cls_3468_, lean_object* v_msg_3469_, lean_object* v___y_3470_, lean_object* v___y_3471_, lean_object* v___y_3472_, lean_object* v___y_3473_, lean_object* v___y_3474_){
_start:
{
lean_object* v_res_3475_; 
v_res_3475_ = l_Lean_addTrace___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__6(v_cls_3468_, v_msg_3469_, v___y_3470_, v___y_3471_, v___y_3472_, v___y_3473_);
lean_dec(v___y_3473_);
lean_dec_ref(v___y_3472_);
lean_dec(v___y_3471_);
lean_dec_ref(v___y_3470_);
return v_res_3475_;
}
}
static lean_object* _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__1(void){
_start:
{
lean_object* v___x_3477_; lean_object* v___x_3478_; 
v___x_3477_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__0));
v___x_3478_ = l_Lean_stringToMessageData(v___x_3477_);
return v___x_3478_;
}
}
static lean_object* _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__4(void){
_start:
{
lean_object* v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; 
v___x_3483_ = lean_box(0);
v___x_3484_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__3));
v___x_3485_ = l_Lean_mkConst(v___x_3484_, v___x_3483_);
return v___x_3485_;
}
}
static lean_object* _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__13(void){
_start:
{
lean_object* v___x_3501_; lean_object* v___x_3502_; lean_object* v___x_3503_; 
v___x_3501_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__10));
v___x_3502_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__12));
v___x_3503_ = l_Lean_Name_append(v___x_3502_, v___x_3501_);
return v___x_3503_;
}
}
static lean_object* _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__15(void){
_start:
{
lean_object* v___x_3505_; lean_object* v___x_3506_; 
v___x_3505_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__14));
v___x_3506_ = l_Lean_stringToMessageData(v___x_3505_);
return v___x_3506_;
}
}
static lean_object* _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__17(void){
_start:
{
lean_object* v___x_3508_; lean_object* v___x_3509_; 
v___x_3508_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__16));
v___x_3509_ = l_Lean_stringToMessageData(v___x_3508_);
return v___x_3509_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl(lean_object* v_inductVal_3510_, lean_object* v_rel_3511_, lean_object* v_a_3512_, lean_object* v_a_3513_, lean_object* v_a_3514_, lean_object* v_a_3515_){
_start:
{
lean_object* v___y_3518_; lean_object* v___y_3519_; lean_object* v___y_3520_; lean_object* v___y_3521_; lean_object* v_toConstantVal_3524_; lean_object* v_numParams_3525_; lean_object* v_ctors_3526_; lean_object* v_name_3527_; lean_object* v_levelParams_3528_; lean_object* v_type_3529_; lean_object* v___x_3531_; uint8_t v_isShared_3532_; uint8_t v_isSharedCheck_3693_; 
v_toConstantVal_3524_ = lean_ctor_get(v_inductVal_3510_, 0);
lean_inc_ref(v_toConstantVal_3524_);
v_numParams_3525_ = lean_ctor_get(v_inductVal_3510_, 1);
lean_inc(v_numParams_3525_);
v_ctors_3526_ = lean_ctor_get(v_inductVal_3510_, 4);
lean_inc(v_ctors_3526_);
lean_dec_ref(v_inductVal_3510_);
v_name_3527_ = lean_ctor_get(v_toConstantVal_3524_, 0);
v_levelParams_3528_ = lean_ctor_get(v_toConstantVal_3524_, 1);
v_type_3529_ = lean_ctor_get(v_toConstantVal_3524_, 2);
v_isSharedCheck_3693_ = !lean_is_exclusive(v_toConstantVal_3524_);
if (v_isSharedCheck_3693_ == 0)
{
v___x_3531_ = v_toConstantVal_3524_;
v_isShared_3532_ = v_isSharedCheck_3693_;
goto v_resetjp_3530_;
}
else
{
lean_inc(v_type_3529_);
lean_inc(v_levelParams_3528_);
lean_inc(v_name_3527_);
lean_dec(v_toConstantVal_3524_);
v___x_3531_ = lean_box(0);
v_isShared_3532_ = v_isSharedCheck_3693_;
goto v_resetjp_3530_;
}
v___jp_3517_:
{
lean_object* v___x_3522_; lean_object* v___x_3523_; 
v___x_3522_ = lean_obj_once(&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__1, &l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__1_once, _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__1);
v___x_3523_ = l_Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0___redArg(v___x_3522_, v___y_3518_, v___y_3519_, v___y_3520_, v___y_3521_);
return v___x_3523_;
}
v_resetjp_3530_:
{
lean_object* v___x_3533_; lean_object* v_univs_3534_; lean_object* v___f_3535_; uint8_t v___x_3536_; lean_object* v___x_3537_; 
v___x_3533_ = lean_box(0);
lean_inc(v_levelParams_3528_);
v_univs_3534_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__2_spec__3(v_levelParams_3528_, v___x_3533_);
lean_inc(v_ctors_3526_);
lean_inc(v_numParams_3525_);
lean_inc(v_name_3527_);
v___f_3535_ = lean_alloc_closure((void*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___lam__0___boxed), 12, 5);
lean_closure_set(v___f_3535_, 0, v_name_3527_);
lean_closure_set(v___f_3535_, 1, v_univs_3534_);
lean_closure_set(v___f_3535_, 2, v_numParams_3525_);
lean_closure_set(v___f_3535_, 3, v_ctors_3526_);
lean_closure_set(v___f_3535_, 4, v___x_3533_);
v___x_3536_ = 0;
v___x_3537_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__1___redArg(v_type_3529_, v___f_3535_, v___x_3536_, v___x_3536_, v_a_3512_, v_a_3513_, v_a_3514_, v_a_3515_);
if (lean_obj_tag(v___x_3537_) == 0)
{
lean_object* v_a_3538_; lean_object* v_snd_3539_; lean_object* v_fst_3540_; lean_object* v___x_3542_; uint8_t v_isShared_3543_; uint8_t v_isSharedCheck_3684_; 
v_a_3538_ = lean_ctor_get(v___x_3537_, 0);
lean_inc(v_a_3538_);
lean_dec_ref_known(v___x_3537_, 1);
v_snd_3539_ = lean_ctor_get(v_a_3538_, 1);
v_fst_3540_ = lean_ctor_get(v_a_3538_, 0);
v_isSharedCheck_3684_ = !lean_is_exclusive(v_a_3538_);
if (v_isSharedCheck_3684_ == 0)
{
v___x_3542_ = v_a_3538_;
v_isShared_3543_ = v_isSharedCheck_3684_;
goto v_resetjp_3541_;
}
else
{
lean_inc(v_snd_3539_);
lean_inc(v_fst_3540_);
lean_dec(v_a_3538_);
v___x_3542_ = lean_box(0);
v_isShared_3543_ = v_isSharedCheck_3684_;
goto v_resetjp_3541_;
}
v_resetjp_3541_:
{
lean_object* v_fst_3544_; lean_object* v_snd_3545_; lean_object* v___x_3547_; uint8_t v_isShared_3548_; uint8_t v_isSharedCheck_3683_; 
v_fst_3544_ = lean_ctor_get(v_snd_3539_, 0);
v_snd_3545_ = lean_ctor_get(v_snd_3539_, 1);
v_isSharedCheck_3683_ = !lean_is_exclusive(v_snd_3539_);
if (v_isSharedCheck_3683_ == 0)
{
v___x_3547_ = v_snd_3539_;
v_isShared_3548_ = v_isSharedCheck_3683_;
goto v_resetjp_3546_;
}
else
{
lean_inc(v_snd_3545_);
lean_inc(v_fst_3544_);
lean_dec(v_snd_3539_);
v___x_3547_ = lean_box(0);
v_isShared_3548_ = v_isSharedCheck_3683_;
goto v_resetjp_3546_;
}
v_resetjp_3546_:
{
lean_object* v___y_3550_; lean_object* v___y_3551_; lean_object* v___y_3552_; lean_object* v___y_3553_; lean_object* v_toCold_3655_; lean_object* v_options_3656_; uint8_t v_hasTrace_3657_; 
v_toCold_3655_ = lean_ctor_get(v_a_3514_, 0);
v_options_3656_ = lean_ctor_get(v_toCold_3655_, 2);
v_hasTrace_3657_ = lean_ctor_get_uint8(v_options_3656_, sizeof(void*)*1);
if (v_hasTrace_3657_ == 0)
{
lean_del_object(v___x_3547_);
lean_del_object(v___x_3542_);
v___y_3550_ = v_a_3512_;
v___y_3551_ = v_a_3513_;
v___y_3552_ = v_a_3514_;
v___y_3553_ = v_a_3515_;
goto v___jp_3549_;
}
else
{
lean_object* v_inheritedTraceOptions_3658_; lean_object* v___x_3659_; lean_object* v___y_3661_; lean_object* v___y_3662_; lean_object* v___y_3663_; lean_object* v_options_3664_; lean_object* v_inheritedTraceOptions_3665_; lean_object* v___y_3666_; lean_object* v___x_3675_; uint8_t v___x_3676_; 
v_inheritedTraceOptions_3658_ = lean_ctor_get(v_toCold_3655_, 11);
v___x_3659_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__10));
v___x_3675_ = lean_obj_once(&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__13, &l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__13_once, _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__13);
v___x_3676_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3658_, v_options_3656_, v___x_3675_);
if (v___x_3676_ == 0)
{
lean_del_object(v___x_3542_);
v___y_3661_ = v_a_3512_;
v___y_3662_ = v_a_3513_;
v___y_3663_ = v_a_3514_;
v_options_3664_ = v_options_3656_;
v_inheritedTraceOptions_3665_ = v_inheritedTraceOptions_3658_;
v___y_3666_ = v_a_3515_;
goto v___jp_3660_;
}
else
{
lean_object* v___x_3677_; lean_object* v___x_3678_; lean_object* v___x_3680_; 
v___x_3677_ = lean_obj_once(&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__17, &l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__17_once, _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__17);
lean_inc(v_snd_3545_);
v___x_3678_ = l_Lean_MessageData_ofExpr(v_snd_3545_);
if (v_isShared_3543_ == 0)
{
lean_ctor_set_tag(v___x_3542_, 7);
lean_ctor_set(v___x_3542_, 1, v___x_3678_);
lean_ctor_set(v___x_3542_, 0, v___x_3677_);
v___x_3680_ = v___x_3542_;
goto v_reusejp_3679_;
}
else
{
lean_object* v_reuseFailAlloc_3682_; 
v_reuseFailAlloc_3682_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3682_, 0, v___x_3677_);
lean_ctor_set(v_reuseFailAlloc_3682_, 1, v___x_3678_);
v___x_3680_ = v_reuseFailAlloc_3682_;
goto v_reusejp_3679_;
}
v_reusejp_3679_:
{
lean_object* v___x_3681_; 
v___x_3681_ = l_Lean_addTrace___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__6(v___x_3659_, v___x_3680_, v_a_3512_, v_a_3513_, v_a_3514_, v_a_3515_);
if (lean_obj_tag(v___x_3681_) == 0)
{
lean_dec_ref_known(v___x_3681_, 1);
v___y_3661_ = v_a_3512_;
v___y_3662_ = v_a_3513_;
v___y_3663_ = v_a_3514_;
v_options_3664_ = v_options_3656_;
v_inheritedTraceOptions_3665_ = v_inheritedTraceOptions_3658_;
v___y_3666_ = v_a_3515_;
goto v___jp_3660_;
}
else
{
lean_del_object(v___x_3547_);
lean_dec(v_snd_3545_);
lean_dec(v_fst_3544_);
lean_dec(v_fst_3540_);
lean_del_object(v___x_3531_);
lean_dec(v_levelParams_3528_);
lean_dec(v_name_3527_);
lean_dec(v_ctors_3526_);
lean_dec(v_numParams_3525_);
lean_dec(v_rel_3511_);
return v___x_3681_;
}
}
}
v___jp_3660_:
{
lean_object* v___x_3667_; uint8_t v___x_3668_; 
v___x_3667_ = lean_obj_once(&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__13, &l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__13_once, _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__13);
v___x_3668_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3665_, v_options_3664_, v___x_3667_);
if (v___x_3668_ == 0)
{
lean_del_object(v___x_3547_);
v___y_3550_ = v___y_3661_;
v___y_3551_ = v___y_3662_;
v___y_3552_ = v___y_3663_;
v___y_3553_ = v___y_3666_;
goto v___jp_3549_;
}
else
{
lean_object* v___x_3669_; lean_object* v___x_3670_; lean_object* v___x_3672_; 
v___x_3669_ = lean_obj_once(&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__15, &l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__15_once, _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__15);
lean_inc(v_fst_3540_);
v___x_3670_ = l_Lean_MessageData_ofExpr(v_fst_3540_);
if (v_isShared_3548_ == 0)
{
lean_ctor_set_tag(v___x_3547_, 7);
lean_ctor_set(v___x_3547_, 1, v___x_3670_);
lean_ctor_set(v___x_3547_, 0, v___x_3669_);
v___x_3672_ = v___x_3547_;
goto v_reusejp_3671_;
}
else
{
lean_object* v_reuseFailAlloc_3674_; 
v_reuseFailAlloc_3674_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3674_, 0, v___x_3669_);
lean_ctor_set(v_reuseFailAlloc_3674_, 1, v___x_3670_);
v___x_3672_ = v_reuseFailAlloc_3674_;
goto v_reusejp_3671_;
}
v_reusejp_3671_:
{
lean_object* v___x_3673_; 
v___x_3673_ = l_Lean_addTrace___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__6(v___x_3659_, v___x_3672_, v___y_3661_, v___y_3662_, v___y_3663_, v___y_3666_);
if (lean_obj_tag(v___x_3673_) == 0)
{
lean_dec_ref_known(v___x_3673_, 1);
v___y_3550_ = v___y_3661_;
v___y_3551_ = v___y_3662_;
v___y_3552_ = v___y_3663_;
v___y_3553_ = v___y_3666_;
goto v___jp_3549_;
}
else
{
lean_dec(v_snd_3545_);
lean_dec(v_fst_3544_);
lean_dec(v_fst_3540_);
lean_del_object(v___x_3531_);
lean_dec(v_levelParams_3528_);
lean_dec(v_name_3527_);
lean_dec(v_ctors_3526_);
lean_dec(v_numParams_3525_);
lean_dec(v_rel_3511_);
return v___x_3673_;
}
}
}
}
}
v___jp_3549_:
{
lean_object* v___x_3554_; uint8_t v___x_3555_; lean_object* v___x_3556_; lean_object* v___x_3557_; 
lean_inc(v_fst_3540_);
v___x_3554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3554_, 0, v_fst_3540_);
v___x_3555_ = 0;
v___x_3556_ = lean_box(0);
v___x_3557_ = l_Lean_Meta_mkFreshExprMVar(v___x_3554_, v___x_3555_, v___x_3556_, v___y_3550_, v___y_3551_, v___y_3552_, v___y_3553_);
if (lean_obj_tag(v___x_3557_) == 0)
{
lean_object* v_a_3558_; lean_object* v___x_3559_; lean_object* v___x_3560_; 
v_a_3558_ = lean_ctor_get(v___x_3557_, 0);
lean_inc(v_a_3558_);
lean_dec_ref_known(v___x_3557_, 1);
v___x_3559_ = l_Lean_Expr_mvarId_x21(v_a_3558_);
v___x_3560_ = l_Lean_MVarId_intros(v___x_3559_, v___y_3550_, v___y_3551_, v___y_3552_, v___y_3553_);
if (lean_obj_tag(v___x_3560_) == 0)
{
lean_object* v_a_3561_; lean_object* v_fst_3562_; lean_object* v_snd_3563_; lean_object* v___x_3564_; lean_object* v___x_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; 
v_a_3561_ = lean_ctor_get(v___x_3560_, 0);
lean_inc(v_a_3561_);
lean_dec_ref_known(v___x_3560_, 1);
v_fst_3562_ = lean_ctor_get(v_a_3561_, 0);
lean_inc(v_fst_3562_);
v_snd_3563_ = lean_ctor_get(v_a_3561_, 1);
lean_inc(v_snd_3563_);
lean_dec(v_a_3561_);
v___x_3564_ = lean_obj_once(&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__4, &l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__4_once, _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__4);
v___x_3565_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__5));
v___x_3566_ = lean_box(0);
v___x_3567_ = l_Lean_MVarId_apply(v_snd_3563_, v___x_3564_, v___x_3565_, v___x_3566_, v___y_3550_, v___y_3551_, v___y_3552_, v___y_3553_);
if (lean_obj_tag(v___x_3567_) == 0)
{
lean_object* v_a_3568_; 
v_a_3568_ = lean_ctor_get(v___x_3567_, 0);
lean_inc(v_a_3568_);
lean_dec_ref_known(v___x_3567_, 1);
if (lean_obj_tag(v_a_3568_) == 1)
{
lean_object* v_tail_3569_; 
v_tail_3569_ = lean_ctor_get(v_a_3568_, 1);
lean_inc(v_tail_3569_);
if (lean_obj_tag(v_tail_3569_) == 1)
{
lean_object* v_tail_3570_; 
v_tail_3570_ = lean_ctor_get(v_tail_3569_, 1);
if (lean_obj_tag(v_tail_3570_) == 0)
{
lean_object* v_head_3571_; lean_object* v_head_3572_; lean_object* v___x_3574_; uint8_t v_isShared_3575_; uint8_t v_isSharedCheck_3629_; 
v_head_3571_ = lean_ctor_get(v_a_3568_, 0);
lean_inc(v_head_3571_);
lean_dec_ref_known(v_a_3568_, 2);
v_head_3572_ = lean_ctor_get(v_tail_3569_, 0);
v_isSharedCheck_3629_ = !lean_is_exclusive(v_tail_3569_);
if (v_isSharedCheck_3629_ == 0)
{
lean_object* v_unused_3630_; 
v_unused_3630_ = lean_ctor_get(v_tail_3569_, 1);
lean_dec(v_unused_3630_);
v___x_3574_ = v_tail_3569_;
v_isShared_3575_ = v_isSharedCheck_3629_;
goto v_resetjp_3573_;
}
else
{
lean_inc(v_head_3572_);
lean_dec(v_tail_3569_);
v___x_3574_ = lean_box(0);
v_isShared_3575_ = v_isSharedCheck_3629_;
goto v_resetjp_3573_;
}
v_resetjp_3573_:
{
lean_object* v___x_3576_; 
lean_inc(v_fst_3544_);
v___x_3576_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toCases(v_head_3571_, v_fst_3544_, v___y_3550_, v___y_3551_, v___y_3552_, v___y_3553_);
if (lean_obj_tag(v___x_3576_) == 0)
{
lean_object* v___x_3577_; 
lean_dec_ref_known(v___x_3576_, 1);
v___x_3577_ = l_Lean_Meta_intro1Core(v_head_3572_, v___x_3536_, v___y_3550_, v___y_3551_, v___y_3552_, v___y_3553_);
if (lean_obj_tag(v___x_3577_) == 0)
{
lean_object* v_a_3578_; lean_object* v_fst_3579_; lean_object* v_snd_3580_; lean_object* v___x_3581_; lean_object* v___x_3582_; lean_object* v___x_3583_; lean_object* v___x_3584_; lean_object* v___x_3585_; 
v_a_3578_ = lean_ctor_get(v___x_3577_, 0);
lean_inc(v_a_3578_);
lean_dec_ref_known(v___x_3577_, 1);
v_fst_3579_ = lean_ctor_get(v_a_3578_, 0);
lean_inc(v_fst_3579_);
v_snd_3580_ = lean_ctor_get(v_a_3578_, 1);
lean_inc(v_snd_3580_);
lean_dec(v_a_3578_);
v___x_3581_ = lean_array_to_list(v_fst_3562_);
v___x_3582_ = ((lean_object*)(l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__5___lam__0___closed__0));
lean_inc(v___x_3581_);
v___x_3583_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), v___x_3581_, v___x_3581_, v_numParams_3525_, v___x_3582_);
lean_dec(v___x_3581_);
v___x_3584_ = l_List_mapTR_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__2(v___x_3583_, v___x_3533_);
v___x_3585_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive(v_snd_3580_, v_ctors_3526_, v___x_3584_, v_fst_3544_, v_fst_3579_, v___y_3550_, v___y_3551_, v___y_3552_, v___y_3553_);
if (lean_obj_tag(v___x_3585_) == 0)
{
lean_object* v___x_3586_; lean_object* v_a_3587_; lean_object* v___x_3589_; 
lean_dec_ref_known(v___x_3585_, 1);
v___x_3586_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__3___redArg(v_a_3558_, v___y_3551_);
v_a_3587_ = lean_ctor_get(v___x_3586_, 0);
lean_inc(v_a_3587_);
lean_dec_ref(v___x_3586_);
lean_inc(v_levelParams_3528_);
lean_inc(v_rel_3511_);
if (v_isShared_3532_ == 0)
{
lean_ctor_set(v___x_3531_, 2, v_fst_3540_);
lean_ctor_set(v___x_3531_, 0, v_rel_3511_);
v___x_3589_ = v___x_3531_;
goto v_reusejp_3588_;
}
else
{
lean_object* v_reuseFailAlloc_3620_; 
v_reuseFailAlloc_3620_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3620_, 0, v_rel_3511_);
lean_ctor_set(v_reuseFailAlloc_3620_, 1, v_levelParams_3528_);
lean_ctor_set(v_reuseFailAlloc_3620_, 2, v_fst_3540_);
v___x_3589_ = v_reuseFailAlloc_3620_;
goto v_reusejp_3588_;
}
v_reusejp_3588_:
{
lean_object* v___x_3591_; 
if (v_isShared_3575_ == 0)
{
lean_ctor_set(v___x_3574_, 1, v___x_3533_);
lean_ctor_set(v___x_3574_, 0, v_rel_3511_);
v___x_3591_ = v___x_3574_;
goto v_reusejp_3590_;
}
else
{
lean_object* v_reuseFailAlloc_3619_; 
v_reuseFailAlloc_3619_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3619_, 0, v_rel_3511_);
lean_ctor_set(v_reuseFailAlloc_3619_, 1, v___x_3533_);
v___x_3591_ = v_reuseFailAlloc_3619_;
goto v_reusejp_3590_;
}
v_reusejp_3590_:
{
lean_object* v___x_3592_; lean_object* v___x_3593_; lean_object* v_a_3594_; lean_object* v___x_3595_; 
v___x_3592_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3592_, 0, v___x_3589_);
lean_ctor_set(v___x_3592_, 1, v_a_3587_);
lean_ctor_set(v___x_3592_, 2, v___x_3591_);
v___x_3593_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__4___redArg(v___x_3592_, v___y_3553_);
v_a_3594_ = lean_ctor_get(v___x_3593_, 0);
lean_inc(v_a_3594_);
lean_dec_ref(v___x_3593_);
v___x_3595_ = l_Lean_addDecl(v_a_3594_, v___x_3536_, v___y_3552_, v___y_3553_);
if (lean_obj_tag(v___x_3595_) == 0)
{
lean_object* v___x_3596_; 
lean_dec_ref_known(v___x_3595_, 1);
lean_inc(v___y_3553_);
lean_inc_ref(v___y_3552_);
lean_inc(v___y_3551_);
lean_inc_ref(v___y_3550_);
lean_inc(v_snd_3545_);
v___x_3596_ = lean_infer_type(v_snd_3545_, v___y_3550_, v___y_3551_, v___y_3552_, v___y_3553_);
if (lean_obj_tag(v___x_3596_) == 0)
{
lean_object* v_a_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; lean_object* v___x_3600_; lean_object* v___x_3601_; lean_object* v_a_3602_; lean_object* v___x_3604_; uint8_t v_isShared_3605_; uint8_t v_isSharedCheck_3610_; 
v_a_3597_ = lean_ctor_get(v___x_3596_, 0);
lean_inc(v_a_3597_);
lean_dec_ref_known(v___x_3596_, 1);
v___x_3598_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__7));
v___x_3599_ = l_Lean_Name_append(v_name_3527_, v___x_3598_);
v___x_3600_ = lean_box(0);
v___x_3601_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__5___redArg(v___x_3599_, v_levelParams_3528_, v_a_3597_, v_snd_3545_, v___x_3600_, v___y_3553_);
v_a_3602_ = lean_ctor_get(v___x_3601_, 0);
v_isSharedCheck_3610_ = !lean_is_exclusive(v___x_3601_);
if (v_isSharedCheck_3610_ == 0)
{
v___x_3604_ = v___x_3601_;
v_isShared_3605_ = v_isSharedCheck_3610_;
goto v_resetjp_3603_;
}
else
{
lean_inc(v_a_3602_);
lean_dec(v___x_3601_);
v___x_3604_ = lean_box(0);
v_isShared_3605_ = v_isSharedCheck_3610_;
goto v_resetjp_3603_;
}
v_resetjp_3603_:
{
lean_object* v___x_3607_; 
if (v_isShared_3605_ == 0)
{
lean_ctor_set_tag(v___x_3604_, 1);
v___x_3607_ = v___x_3604_;
goto v_reusejp_3606_;
}
else
{
lean_object* v_reuseFailAlloc_3609_; 
v_reuseFailAlloc_3609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3609_, 0, v_a_3602_);
v___x_3607_ = v_reuseFailAlloc_3609_;
goto v_reusejp_3606_;
}
v_reusejp_3606_:
{
lean_object* v___x_3608_; 
v___x_3608_ = l_Lean_addDecl(v___x_3607_, v___x_3536_, v___y_3552_, v___y_3553_);
return v___x_3608_;
}
}
}
else
{
lean_object* v_a_3611_; lean_object* v___x_3613_; uint8_t v_isShared_3614_; uint8_t v_isSharedCheck_3618_; 
lean_dec(v_snd_3545_);
lean_dec(v_levelParams_3528_);
lean_dec(v_name_3527_);
v_a_3611_ = lean_ctor_get(v___x_3596_, 0);
v_isSharedCheck_3618_ = !lean_is_exclusive(v___x_3596_);
if (v_isSharedCheck_3618_ == 0)
{
v___x_3613_ = v___x_3596_;
v_isShared_3614_ = v_isSharedCheck_3618_;
goto v_resetjp_3612_;
}
else
{
lean_inc(v_a_3611_);
lean_dec(v___x_3596_);
v___x_3613_ = lean_box(0);
v_isShared_3614_ = v_isSharedCheck_3618_;
goto v_resetjp_3612_;
}
v_resetjp_3612_:
{
lean_object* v___x_3616_; 
if (v_isShared_3614_ == 0)
{
v___x_3616_ = v___x_3613_;
goto v_reusejp_3615_;
}
else
{
lean_object* v_reuseFailAlloc_3617_; 
v_reuseFailAlloc_3617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3617_, 0, v_a_3611_);
v___x_3616_ = v_reuseFailAlloc_3617_;
goto v_reusejp_3615_;
}
v_reusejp_3615_:
{
return v___x_3616_;
}
}
}
}
else
{
lean_dec(v_snd_3545_);
lean_dec(v_levelParams_3528_);
lean_dec(v_name_3527_);
return v___x_3595_;
}
}
}
}
else
{
lean_del_object(v___x_3574_);
lean_dec(v_a_3558_);
lean_dec(v_snd_3545_);
lean_dec(v_fst_3540_);
lean_del_object(v___x_3531_);
lean_dec(v_levelParams_3528_);
lean_dec(v_name_3527_);
lean_dec(v_rel_3511_);
return v___x_3585_;
}
}
else
{
lean_object* v_a_3621_; lean_object* v___x_3623_; uint8_t v_isShared_3624_; uint8_t v_isSharedCheck_3628_; 
lean_del_object(v___x_3574_);
lean_dec(v_fst_3562_);
lean_dec(v_a_3558_);
lean_dec(v_snd_3545_);
lean_dec(v_fst_3544_);
lean_dec(v_fst_3540_);
lean_del_object(v___x_3531_);
lean_dec(v_levelParams_3528_);
lean_dec(v_name_3527_);
lean_dec(v_ctors_3526_);
lean_dec(v_numParams_3525_);
lean_dec(v_rel_3511_);
v_a_3621_ = lean_ctor_get(v___x_3577_, 0);
v_isSharedCheck_3628_ = !lean_is_exclusive(v___x_3577_);
if (v_isSharedCheck_3628_ == 0)
{
v___x_3623_ = v___x_3577_;
v_isShared_3624_ = v_isSharedCheck_3628_;
goto v_resetjp_3622_;
}
else
{
lean_inc(v_a_3621_);
lean_dec(v___x_3577_);
v___x_3623_ = lean_box(0);
v_isShared_3624_ = v_isSharedCheck_3628_;
goto v_resetjp_3622_;
}
v_resetjp_3622_:
{
lean_object* v___x_3626_; 
if (v_isShared_3624_ == 0)
{
v___x_3626_ = v___x_3623_;
goto v_reusejp_3625_;
}
else
{
lean_object* v_reuseFailAlloc_3627_; 
v_reuseFailAlloc_3627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3627_, 0, v_a_3621_);
v___x_3626_ = v_reuseFailAlloc_3627_;
goto v_reusejp_3625_;
}
v_reusejp_3625_:
{
return v___x_3626_;
}
}
}
}
else
{
lean_del_object(v___x_3574_);
lean_dec(v_head_3572_);
lean_dec(v_fst_3562_);
lean_dec(v_a_3558_);
lean_dec(v_snd_3545_);
lean_dec(v_fst_3544_);
lean_dec(v_fst_3540_);
lean_del_object(v___x_3531_);
lean_dec(v_levelParams_3528_);
lean_dec(v_name_3527_);
lean_dec(v_ctors_3526_);
lean_dec(v_numParams_3525_);
lean_dec(v_rel_3511_);
return v___x_3576_;
}
}
}
else
{
lean_dec_ref_known(v_tail_3569_, 2);
lean_dec_ref_known(v_a_3568_, 2);
lean_dec(v_fst_3562_);
lean_dec(v_a_3558_);
lean_dec(v_snd_3545_);
lean_dec(v_fst_3544_);
lean_dec(v_fst_3540_);
lean_del_object(v___x_3531_);
lean_dec(v_levelParams_3528_);
lean_dec(v_name_3527_);
lean_dec(v_ctors_3526_);
lean_dec(v_numParams_3525_);
lean_dec(v_rel_3511_);
v___y_3518_ = v___y_3550_;
v___y_3519_ = v___y_3551_;
v___y_3520_ = v___y_3552_;
v___y_3521_ = v___y_3553_;
goto v___jp_3517_;
}
}
else
{
lean_dec(v_tail_3569_);
lean_dec_ref_known(v_a_3568_, 2);
lean_dec(v_fst_3562_);
lean_dec(v_a_3558_);
lean_dec(v_snd_3545_);
lean_dec(v_fst_3544_);
lean_dec(v_fst_3540_);
lean_del_object(v___x_3531_);
lean_dec(v_levelParams_3528_);
lean_dec(v_name_3527_);
lean_dec(v_ctors_3526_);
lean_dec(v_numParams_3525_);
lean_dec(v_rel_3511_);
v___y_3518_ = v___y_3550_;
v___y_3519_ = v___y_3551_;
v___y_3520_ = v___y_3552_;
v___y_3521_ = v___y_3553_;
goto v___jp_3517_;
}
}
else
{
lean_dec(v_a_3568_);
lean_dec(v_fst_3562_);
lean_dec(v_a_3558_);
lean_dec(v_snd_3545_);
lean_dec(v_fst_3544_);
lean_dec(v_fst_3540_);
lean_del_object(v___x_3531_);
lean_dec(v_levelParams_3528_);
lean_dec(v_name_3527_);
lean_dec(v_ctors_3526_);
lean_dec(v_numParams_3525_);
lean_dec(v_rel_3511_);
v___y_3518_ = v___y_3550_;
v___y_3519_ = v___y_3551_;
v___y_3520_ = v___y_3552_;
v___y_3521_ = v___y_3553_;
goto v___jp_3517_;
}
}
else
{
lean_object* v_a_3631_; lean_object* v___x_3633_; uint8_t v_isShared_3634_; uint8_t v_isSharedCheck_3638_; 
lean_dec(v_fst_3562_);
lean_dec(v_a_3558_);
lean_dec(v_snd_3545_);
lean_dec(v_fst_3544_);
lean_dec(v_fst_3540_);
lean_del_object(v___x_3531_);
lean_dec(v_levelParams_3528_);
lean_dec(v_name_3527_);
lean_dec(v_ctors_3526_);
lean_dec(v_numParams_3525_);
lean_dec(v_rel_3511_);
v_a_3631_ = lean_ctor_get(v___x_3567_, 0);
v_isSharedCheck_3638_ = !lean_is_exclusive(v___x_3567_);
if (v_isSharedCheck_3638_ == 0)
{
v___x_3633_ = v___x_3567_;
v_isShared_3634_ = v_isSharedCheck_3638_;
goto v_resetjp_3632_;
}
else
{
lean_inc(v_a_3631_);
lean_dec(v___x_3567_);
v___x_3633_ = lean_box(0);
v_isShared_3634_ = v_isSharedCheck_3638_;
goto v_resetjp_3632_;
}
v_resetjp_3632_:
{
lean_object* v___x_3636_; 
if (v_isShared_3634_ == 0)
{
v___x_3636_ = v___x_3633_;
goto v_reusejp_3635_;
}
else
{
lean_object* v_reuseFailAlloc_3637_; 
v_reuseFailAlloc_3637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3637_, 0, v_a_3631_);
v___x_3636_ = v_reuseFailAlloc_3637_;
goto v_reusejp_3635_;
}
v_reusejp_3635_:
{
return v___x_3636_;
}
}
}
}
else
{
lean_object* v_a_3639_; lean_object* v___x_3641_; uint8_t v_isShared_3642_; uint8_t v_isSharedCheck_3646_; 
lean_dec(v_a_3558_);
lean_dec(v_snd_3545_);
lean_dec(v_fst_3544_);
lean_dec(v_fst_3540_);
lean_del_object(v___x_3531_);
lean_dec(v_levelParams_3528_);
lean_dec(v_name_3527_);
lean_dec(v_ctors_3526_);
lean_dec(v_numParams_3525_);
lean_dec(v_rel_3511_);
v_a_3639_ = lean_ctor_get(v___x_3560_, 0);
v_isSharedCheck_3646_ = !lean_is_exclusive(v___x_3560_);
if (v_isSharedCheck_3646_ == 0)
{
v___x_3641_ = v___x_3560_;
v_isShared_3642_ = v_isSharedCheck_3646_;
goto v_resetjp_3640_;
}
else
{
lean_inc(v_a_3639_);
lean_dec(v___x_3560_);
v___x_3641_ = lean_box(0);
v_isShared_3642_ = v_isSharedCheck_3646_;
goto v_resetjp_3640_;
}
v_resetjp_3640_:
{
lean_object* v___x_3644_; 
if (v_isShared_3642_ == 0)
{
v___x_3644_ = v___x_3641_;
goto v_reusejp_3643_;
}
else
{
lean_object* v_reuseFailAlloc_3645_; 
v_reuseFailAlloc_3645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3645_, 0, v_a_3639_);
v___x_3644_ = v_reuseFailAlloc_3645_;
goto v_reusejp_3643_;
}
v_reusejp_3643_:
{
return v___x_3644_;
}
}
}
}
else
{
lean_object* v_a_3647_; lean_object* v___x_3649_; uint8_t v_isShared_3650_; uint8_t v_isSharedCheck_3654_; 
lean_dec(v_snd_3545_);
lean_dec(v_fst_3544_);
lean_dec(v_fst_3540_);
lean_del_object(v___x_3531_);
lean_dec(v_levelParams_3528_);
lean_dec(v_name_3527_);
lean_dec(v_ctors_3526_);
lean_dec(v_numParams_3525_);
lean_dec(v_rel_3511_);
v_a_3647_ = lean_ctor_get(v___x_3557_, 0);
v_isSharedCheck_3654_ = !lean_is_exclusive(v___x_3557_);
if (v_isSharedCheck_3654_ == 0)
{
v___x_3649_ = v___x_3557_;
v_isShared_3650_ = v_isSharedCheck_3654_;
goto v_resetjp_3648_;
}
else
{
lean_inc(v_a_3647_);
lean_dec(v___x_3557_);
v___x_3649_ = lean_box(0);
v_isShared_3650_ = v_isSharedCheck_3654_;
goto v_resetjp_3648_;
}
v_resetjp_3648_:
{
lean_object* v___x_3652_; 
if (v_isShared_3650_ == 0)
{
v___x_3652_ = v___x_3649_;
goto v_reusejp_3651_;
}
else
{
lean_object* v_reuseFailAlloc_3653_; 
v_reuseFailAlloc_3653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3653_, 0, v_a_3647_);
v___x_3652_ = v_reuseFailAlloc_3653_;
goto v_reusejp_3651_;
}
v_reusejp_3651_:
{
return v___x_3652_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3685_; lean_object* v___x_3687_; uint8_t v_isShared_3688_; uint8_t v_isSharedCheck_3692_; 
lean_del_object(v___x_3531_);
lean_dec(v_levelParams_3528_);
lean_dec(v_name_3527_);
lean_dec(v_ctors_3526_);
lean_dec(v_numParams_3525_);
lean_dec(v_rel_3511_);
v_a_3685_ = lean_ctor_get(v___x_3537_, 0);
v_isSharedCheck_3692_ = !lean_is_exclusive(v___x_3537_);
if (v_isSharedCheck_3692_ == 0)
{
v___x_3687_ = v___x_3537_;
v_isShared_3688_ = v_isSharedCheck_3692_;
goto v_resetjp_3686_;
}
else
{
lean_inc(v_a_3685_);
lean_dec(v___x_3537_);
v___x_3687_ = lean_box(0);
v_isShared_3688_ = v_isSharedCheck_3692_;
goto v_resetjp_3686_;
}
v_resetjp_3686_:
{
lean_object* v___x_3690_; 
if (v_isShared_3688_ == 0)
{
v___x_3690_ = v___x_3687_;
goto v_reusejp_3689_;
}
else
{
lean_object* v_reuseFailAlloc_3691_; 
v_reuseFailAlloc_3691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3691_, 0, v_a_3685_);
v___x_3690_ = v_reuseFailAlloc_3691_;
goto v_reusejp_3689_;
}
v_reusejp_3689_:
{
return v___x_3690_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___boxed(lean_object* v_inductVal_3694_, lean_object* v_rel_3695_, lean_object* v_a_3696_, lean_object* v_a_3697_, lean_object* v_a_3698_, lean_object* v_a_3699_, lean_object* v_a_3700_){
_start:
{
lean_object* v_res_3701_; 
v_res_3701_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl(v_inductVal_3694_, v_rel_3695_, v_a_3696_, v_a_3697_, v_a_3698_, v_a_3699_);
lean_dec(v_a_3699_);
lean_dec_ref(v_a_3698_);
lean_dec(v_a_3697_);
lean_dec_ref(v_a_3696_);
return v_res_3701_;
}
}
static lean_object* _init_l_Lean_Meta_mkSumOfProducts___closed__3(void){
_start:
{
lean_object* v___x_3706_; lean_object* v___x_3707_; 
v___x_3706_ = ((lean_object*)(l_Lean_Meta_mkSumOfProducts___closed__2));
v___x_3707_ = l_Lean_stringToMessageData(v___x_3706_);
return v___x_3707_;
}
}
static lean_object* _init_l_Lean_Meta_mkSumOfProducts___closed__5(void){
_start:
{
lean_object* v___x_3709_; lean_object* v___x_3710_; 
v___x_3709_ = ((lean_object*)(l_Lean_Meta_mkSumOfProducts___closed__4));
v___x_3710_ = l_Lean_stringToMessageData(v___x_3709_);
return v___x_3710_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSumOfProducts(lean_object* v_declName_3711_, lean_object* v_a_3712_, lean_object* v_a_3713_, lean_object* v_a_3714_, lean_object* v_a_3715_){
_start:
{
lean_object* v___y_3718_; lean_object* v___y_3719_; lean_object* v___y_3720_; lean_object* v___y_3721_; lean_object* v_toCold_3738_; lean_object* v_options_3739_; uint8_t v_hasTrace_3740_; 
v_toCold_3738_ = lean_ctor_get(v_a_3714_, 0);
v_options_3739_ = lean_ctor_get(v_toCold_3738_, 2);
v_hasTrace_3740_ = lean_ctor_get_uint8(v_options_3739_, sizeof(void*)*1);
if (v_hasTrace_3740_ == 0)
{
v___y_3718_ = v_a_3712_;
v___y_3719_ = v_a_3713_;
v___y_3720_ = v_a_3714_;
v___y_3721_ = v_a_3715_;
goto v___jp_3717_;
}
else
{
lean_object* v_inheritedTraceOptions_3741_; lean_object* v_cls_3742_; lean_object* v___x_3743_; uint8_t v___x_3744_; 
v_inheritedTraceOptions_3741_ = lean_ctor_get(v_toCold_3738_, 11);
v_cls_3742_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__10));
v___x_3743_ = lean_obj_once(&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__13, &l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__13_once, _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__13);
v___x_3744_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3741_, v_options_3739_, v___x_3743_);
if (v___x_3744_ == 0)
{
v___y_3718_ = v_a_3712_;
v___y_3719_ = v_a_3713_;
v___y_3720_ = v_a_3714_;
v___y_3721_ = v_a_3715_;
goto v___jp_3717_;
}
else
{
lean_object* v___x_3745_; lean_object* v___x_3746_; lean_object* v___x_3747_; lean_object* v___x_3748_; 
v___x_3745_ = lean_obj_once(&l_Lean_Meta_mkSumOfProducts___closed__5, &l_Lean_Meta_mkSumOfProducts___closed__5_once, _init_l_Lean_Meta_mkSumOfProducts___closed__5);
lean_inc(v_declName_3711_);
v___x_3746_ = l_Lean_MessageData_ofName(v_declName_3711_);
v___x_3747_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3747_, 0, v___x_3745_);
lean_ctor_set(v___x_3747_, 1, v___x_3746_);
v___x_3748_ = l_Lean_addTrace___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__6(v_cls_3742_, v___x_3747_, v_a_3712_, v_a_3713_, v_a_3714_, v_a_3715_);
if (lean_obj_tag(v___x_3748_) == 0)
{
lean_dec_ref_known(v___x_3748_, 1);
v___y_3718_ = v_a_3712_;
v___y_3719_ = v_a_3713_;
v___y_3720_ = v_a_3714_;
v___y_3721_ = v_a_3715_;
goto v___jp_3717_;
}
else
{
lean_dec(v_declName_3711_);
return v___x_3748_;
}
}
}
v___jp_3717_:
{
lean_object* v___x_3722_; 
lean_inc(v_declName_3711_);
v___x_3722_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0(v_declName_3711_, v___y_3718_, v___y_3719_, v___y_3720_, v___y_3721_);
if (lean_obj_tag(v___x_3722_) == 0)
{
lean_object* v_a_3723_; 
v_a_3723_ = lean_ctor_get(v___x_3722_, 0);
lean_inc(v_a_3723_);
lean_dec_ref_known(v___x_3722_, 1);
if (lean_obj_tag(v_a_3723_) == 5)
{
lean_object* v_val_3724_; lean_object* v___x_3725_; lean_object* v___x_3726_; lean_object* v___x_3727_; 
v_val_3724_ = lean_ctor_get(v_a_3723_, 0);
lean_inc_ref(v_val_3724_);
lean_dec_ref_known(v_a_3723_, 1);
v___x_3725_ = ((lean_object*)(l_Lean_Meta_mkSumOfProducts___closed__1));
v___x_3726_ = l_Lean_Name_append(v_declName_3711_, v___x_3725_);
v___x_3727_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl(v_val_3724_, v___x_3726_, v___y_3718_, v___y_3719_, v___y_3720_, v___y_3721_);
return v___x_3727_;
}
else
{
lean_object* v___x_3728_; lean_object* v___x_3729_; 
lean_dec(v_a_3723_);
lean_dec(v_declName_3711_);
v___x_3728_ = lean_obj_once(&l_Lean_Meta_mkSumOfProducts___closed__3, &l_Lean_Meta_mkSumOfProducts___closed__3_once, _init_l_Lean_Meta_mkSumOfProducts___closed__3);
v___x_3729_ = l_Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0___redArg(v___x_3728_, v___y_3718_, v___y_3719_, v___y_3720_, v___y_3721_);
return v___x_3729_;
}
}
else
{
lean_object* v_a_3730_; lean_object* v___x_3732_; uint8_t v_isShared_3733_; uint8_t v_isSharedCheck_3737_; 
lean_dec(v_declName_3711_);
v_a_3730_ = lean_ctor_get(v___x_3722_, 0);
v_isSharedCheck_3737_ = !lean_is_exclusive(v___x_3722_);
if (v_isSharedCheck_3737_ == 0)
{
v___x_3732_ = v___x_3722_;
v_isShared_3733_ = v_isSharedCheck_3737_;
goto v_resetjp_3731_;
}
else
{
lean_inc(v_a_3730_);
lean_dec(v___x_3722_);
v___x_3732_ = lean_box(0);
v_isShared_3733_ = v_isSharedCheck_3737_;
goto v_resetjp_3731_;
}
v_resetjp_3731_:
{
lean_object* v___x_3735_; 
if (v_isShared_3733_ == 0)
{
v___x_3735_ = v___x_3732_;
goto v_reusejp_3734_;
}
else
{
lean_object* v_reuseFailAlloc_3736_; 
v_reuseFailAlloc_3736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3736_, 0, v_a_3730_);
v___x_3735_ = v_reuseFailAlloc_3736_;
goto v_reusejp_3734_;
}
v_reusejp_3734_:
{
return v___x_3735_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSumOfProducts___boxed(lean_object* v_declName_3749_, lean_object* v_a_3750_, lean_object* v_a_3751_, lean_object* v_a_3752_, lean_object* v_a_3753_, lean_object* v_a_3754_){
_start:
{
lean_object* v_res_3755_; 
v_res_3755_ = l_Lean_Meta_mkSumOfProducts(v_declName_3749_, v_a_3750_, v_a_3751_, v_a_3752_, v_a_3753_);
lean_dec(v_a_3753_);
lean_dec_ref(v_a_3752_);
lean_dec(v_a_3751_);
lean_dec_ref(v_a_3750_);
return v_res_3755_;
}
}
static lean_object* _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3795_; lean_object* v___x_3796_; lean_object* v___x_3797_; 
v___x_3795_ = lean_unsigned_to_nat(3649998058u);
v___x_3796_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2_));
v___x_3797_ = l_Lean_Name_num___override(v___x_3796_, v___x_3795_);
return v___x_3797_;
}
}
static lean_object* _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3799_; lean_object* v___x_3800_; lean_object* v___x_3801_; 
v___x_3799_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2_));
v___x_3800_ = lean_obj_once(&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2_, &l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2_);
v___x_3801_ = l_Lean_Name_str___override(v___x_3800_, v___x_3799_);
return v___x_3801_;
}
}
static lean_object* _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3803_; lean_object* v___x_3804_; lean_object* v___x_3805_; 
v___x_3803_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2_));
v___x_3804_ = lean_obj_once(&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2_, &l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2_);
v___x_3805_ = l_Lean_Name_str___override(v___x_3804_, v___x_3803_);
return v___x_3805_;
}
}
static lean_object* _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3806_; lean_object* v___x_3807_; lean_object* v___x_3808_; 
v___x_3806_ = lean_unsigned_to_nat(2u);
v___x_3807_ = lean_obj_once(&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2_, &l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2_);
v___x_3808_ = l_Lean_Name_num___override(v___x_3807_, v___x_3806_);
return v___x_3808_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3810_; uint8_t v___x_3811_; lean_object* v___x_3812_; lean_object* v___x_3813_; 
v___x_3810_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__10));
v___x_3811_ = 0;
v___x_3812_ = lean_obj_once(&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2_, &l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2_);
v___x_3813_ = l_Lean_registerTraceClass(v___x_3810_, v___x_3811_, v___x_3812_);
return v___x_3813_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2____boxed(lean_object* v_a_3814_){
_start:
{
lean_object* v_res_3815_; 
v_res_3815_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2_();
return v_res_3815_;
}
}
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Apply(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Cases(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_MkIffOfInductiveProp(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Apply(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Cases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_MkIffOfInductiveProp(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Basic(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Apply(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Cases(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_MkIffOfInductiveProp(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Apply(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Cases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_MkIffOfInductiveProp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_MkIffOfInductiveProp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_MkIffOfInductiveProp(builtin);
}
#ifdef __cplusplus
}
#endif
