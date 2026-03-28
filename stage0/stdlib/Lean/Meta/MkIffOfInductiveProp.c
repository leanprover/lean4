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
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sortLevel_x21(lean_object*);
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_cases(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
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
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
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
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_tryClear(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_revert(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_intro1Core(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_List_zipIdxTR___redArg(lean_object*, lean_object*);
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
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3___redArg___closed__2;
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
static const lean_string_object l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "left"};
static const lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__0 = (const lean_object*)&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__0_value),LEAN_SCALAR_PTR_LITERAL(14, 26, 230, 200, 188, 33, 106, 9)}};
static const lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__1 = (const lean_object*)&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__2 = (const lean_object*)&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__2_value;
static const lean_string_object l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "expected only one new goal"};
static const lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__3 = (const lean_object*)&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__3_value;
static lean_once_cell_t l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__4;
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
static const lean_string_object l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "constructor"};
static const lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__1___closed__1_value_aux_0),((lean_object*)&l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__1___closed__1_value_aux_1),((lean_object*)&l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(144, 188, 57, 91, 27, 124, 155, 13)}};
static const lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__1___closed__1 = (const lean_object*)&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3___redArg___closed__0(void){
_start:
{
size_t v___x_41_; size_t v___x_42_; size_t v___x_43_; 
v___x_41_ = ((size_t)5ULL);
v___x_42_ = ((size_t)1ULL);
v___x_43_ = lean_usize_shift_left(v___x_42_, v___x_41_);
return v___x_43_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3___redArg___closed__1(void){
_start:
{
size_t v___x_44_; size_t v___x_45_; size_t v___x_46_; 
v___x_44_ = ((size_t)1ULL);
v___x_45_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3___redArg___closed__0);
v___x_46_ = lean_usize_sub(v___x_45_, v___x_44_);
return v___x_46_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3___redArg___closed__2(void){
_start:
{
lean_object* v___x_47_; 
v___x_47_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3___redArg(lean_object* v_x_48_, size_t v_x_49_, size_t v_x_50_, lean_object* v_x_51_, lean_object* v_x_52_){
_start:
{
if (lean_obj_tag(v_x_48_) == 0)
{
lean_object* v_es_53_; size_t v___x_54_; size_t v___x_55_; size_t v___x_56_; size_t v___x_57_; lean_object* v_j_58_; lean_object* v___x_59_; uint8_t v___x_60_; 
v_es_53_ = lean_ctor_get(v_x_48_, 0);
v___x_54_ = ((size_t)5ULL);
v___x_55_ = ((size_t)1ULL);
v___x_56_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3___redArg___closed__1);
v___x_57_ = lean_usize_land(v_x_49_, v___x_56_);
v_j_58_ = lean_usize_to_nat(v___x_57_);
v___x_59_ = lean_array_get_size(v_es_53_);
v___x_60_ = lean_nat_dec_lt(v_j_58_, v___x_59_);
if (v___x_60_ == 0)
{
lean_dec(v_j_58_);
lean_dec(v_x_52_);
lean_dec(v_x_51_);
return v_x_48_;
}
else
{
lean_object* v___x_62_; uint8_t v_isShared_63_; uint8_t v_isSharedCheck_97_; 
lean_inc_ref(v_es_53_);
v_isSharedCheck_97_ = !lean_is_exclusive(v_x_48_);
if (v_isSharedCheck_97_ == 0)
{
lean_object* v_unused_98_; 
v_unused_98_ = lean_ctor_get(v_x_48_, 0);
lean_dec(v_unused_98_);
v___x_62_ = v_x_48_;
v_isShared_63_ = v_isSharedCheck_97_;
goto v_resetjp_61_;
}
else
{
lean_dec(v_x_48_);
v___x_62_ = lean_box(0);
v_isShared_63_ = v_isSharedCheck_97_;
goto v_resetjp_61_;
}
v_resetjp_61_:
{
lean_object* v_v_64_; lean_object* v___x_65_; lean_object* v_xs_x27_66_; lean_object* v___y_68_; 
v_v_64_ = lean_array_fget(v_es_53_, v_j_58_);
v___x_65_ = lean_box(0);
v_xs_x27_66_ = lean_array_fset(v_es_53_, v_j_58_, v___x_65_);
switch(lean_obj_tag(v_v_64_))
{
case 0:
{
lean_object* v_key_73_; lean_object* v_val_74_; lean_object* v___x_76_; uint8_t v_isShared_77_; uint8_t v_isSharedCheck_84_; 
v_key_73_ = lean_ctor_get(v_v_64_, 0);
v_val_74_ = lean_ctor_get(v_v_64_, 1);
v_isSharedCheck_84_ = !lean_is_exclusive(v_v_64_);
if (v_isSharedCheck_84_ == 0)
{
v___x_76_ = v_v_64_;
v_isShared_77_ = v_isSharedCheck_84_;
goto v_resetjp_75_;
}
else
{
lean_inc(v_val_74_);
lean_inc(v_key_73_);
lean_dec(v_v_64_);
v___x_76_ = lean_box(0);
v_isShared_77_ = v_isSharedCheck_84_;
goto v_resetjp_75_;
}
v_resetjp_75_:
{
uint8_t v___x_78_; 
v___x_78_ = l_Lean_instBEqMVarId_beq(v_x_51_, v_key_73_);
if (v___x_78_ == 0)
{
lean_object* v___x_79_; lean_object* v___x_80_; 
lean_del_object(v___x_76_);
v___x_79_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_73_, v_val_74_, v_x_51_, v_x_52_);
v___x_80_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_80_, 0, v___x_79_);
v___y_68_ = v___x_80_;
goto v___jp_67_;
}
else
{
lean_object* v___x_82_; 
lean_dec(v_val_74_);
lean_dec(v_key_73_);
if (v_isShared_77_ == 0)
{
lean_ctor_set(v___x_76_, 1, v_x_52_);
lean_ctor_set(v___x_76_, 0, v_x_51_);
v___x_82_ = v___x_76_;
goto v_reusejp_81_;
}
else
{
lean_object* v_reuseFailAlloc_83_; 
v_reuseFailAlloc_83_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_83_, 0, v_x_51_);
lean_ctor_set(v_reuseFailAlloc_83_, 1, v_x_52_);
v___x_82_ = v_reuseFailAlloc_83_;
goto v_reusejp_81_;
}
v_reusejp_81_:
{
v___y_68_ = v___x_82_;
goto v___jp_67_;
}
}
}
}
case 1:
{
lean_object* v_node_85_; lean_object* v___x_87_; uint8_t v_isShared_88_; uint8_t v_isSharedCheck_95_; 
v_node_85_ = lean_ctor_get(v_v_64_, 0);
v_isSharedCheck_95_ = !lean_is_exclusive(v_v_64_);
if (v_isSharedCheck_95_ == 0)
{
v___x_87_ = v_v_64_;
v_isShared_88_ = v_isSharedCheck_95_;
goto v_resetjp_86_;
}
else
{
lean_inc(v_node_85_);
lean_dec(v_v_64_);
v___x_87_ = lean_box(0);
v_isShared_88_ = v_isSharedCheck_95_;
goto v_resetjp_86_;
}
v_resetjp_86_:
{
size_t v___x_89_; size_t v___x_90_; lean_object* v___x_91_; lean_object* v___x_93_; 
v___x_89_ = lean_usize_shift_right(v_x_49_, v___x_54_);
v___x_90_ = lean_usize_add(v_x_50_, v___x_55_);
v___x_91_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3___redArg(v_node_85_, v___x_89_, v___x_90_, v_x_51_, v_x_52_);
if (v_isShared_88_ == 0)
{
lean_ctor_set(v___x_87_, 0, v___x_91_);
v___x_93_ = v___x_87_;
goto v_reusejp_92_;
}
else
{
lean_object* v_reuseFailAlloc_94_; 
v_reuseFailAlloc_94_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_94_, 0, v___x_91_);
v___x_93_ = v_reuseFailAlloc_94_;
goto v_reusejp_92_;
}
v_reusejp_92_:
{
v___y_68_ = v___x_93_;
goto v___jp_67_;
}
}
}
default: 
{
lean_object* v___x_96_; 
v___x_96_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_96_, 0, v_x_51_);
lean_ctor_set(v___x_96_, 1, v_x_52_);
v___y_68_ = v___x_96_;
goto v___jp_67_;
}
}
v___jp_67_:
{
lean_object* v___x_69_; lean_object* v___x_71_; 
v___x_69_ = lean_array_fset(v_xs_x27_66_, v_j_58_, v___y_68_);
lean_dec(v_j_58_);
if (v_isShared_63_ == 0)
{
lean_ctor_set(v___x_62_, 0, v___x_69_);
v___x_71_ = v___x_62_;
goto v_reusejp_70_;
}
else
{
lean_object* v_reuseFailAlloc_72_; 
v_reuseFailAlloc_72_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_72_, 0, v___x_69_);
v___x_71_ = v_reuseFailAlloc_72_;
goto v_reusejp_70_;
}
v_reusejp_70_:
{
return v___x_71_;
}
}
}
}
}
else
{
lean_object* v_ks_99_; lean_object* v_vs_100_; lean_object* v___x_102_; uint8_t v_isShared_103_; uint8_t v_isSharedCheck_120_; 
v_ks_99_ = lean_ctor_get(v_x_48_, 0);
v_vs_100_ = lean_ctor_get(v_x_48_, 1);
v_isSharedCheck_120_ = !lean_is_exclusive(v_x_48_);
if (v_isSharedCheck_120_ == 0)
{
v___x_102_ = v_x_48_;
v_isShared_103_ = v_isSharedCheck_120_;
goto v_resetjp_101_;
}
else
{
lean_inc(v_vs_100_);
lean_inc(v_ks_99_);
lean_dec(v_x_48_);
v___x_102_ = lean_box(0);
v_isShared_103_ = v_isSharedCheck_120_;
goto v_resetjp_101_;
}
v_resetjp_101_:
{
lean_object* v___x_105_; 
if (v_isShared_103_ == 0)
{
v___x_105_ = v___x_102_;
goto v_reusejp_104_;
}
else
{
lean_object* v_reuseFailAlloc_119_; 
v_reuseFailAlloc_119_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_119_, 0, v_ks_99_);
lean_ctor_set(v_reuseFailAlloc_119_, 1, v_vs_100_);
v___x_105_ = v_reuseFailAlloc_119_;
goto v_reusejp_104_;
}
v_reusejp_104_:
{
lean_object* v_newNode_106_; uint8_t v___y_108_; size_t v___x_114_; uint8_t v___x_115_; 
v_newNode_106_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3_spec__5___redArg(v___x_105_, v_x_51_, v_x_52_);
v___x_114_ = ((size_t)7ULL);
v___x_115_ = lean_usize_dec_le(v___x_114_, v_x_50_);
if (v___x_115_ == 0)
{
lean_object* v___x_116_; lean_object* v___x_117_; uint8_t v___x_118_; 
v___x_116_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_106_);
v___x_117_ = lean_unsigned_to_nat(4u);
v___x_118_ = lean_nat_dec_lt(v___x_116_, v___x_117_);
lean_dec(v___x_116_);
v___y_108_ = v___x_118_;
goto v___jp_107_;
}
else
{
v___y_108_ = v___x_115_;
goto v___jp_107_;
}
v___jp_107_:
{
if (v___y_108_ == 0)
{
lean_object* v_ks_109_; lean_object* v_vs_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; 
v_ks_109_ = lean_ctor_get(v_newNode_106_, 0);
lean_inc_ref(v_ks_109_);
v_vs_110_ = lean_ctor_get(v_newNode_106_, 1);
lean_inc_ref(v_vs_110_);
lean_dec_ref(v_newNode_106_);
v___x_111_ = lean_unsigned_to_nat(0u);
v___x_112_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3___redArg___closed__2);
v___x_113_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3_spec__6___redArg(v_x_50_, v_ks_109_, v_vs_110_, v___x_111_, v___x_112_);
lean_dec_ref(v_vs_110_);
lean_dec_ref(v_ks_109_);
return v___x_113_;
}
else
{
return v_newNode_106_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3_spec__6___redArg(size_t v_depth_121_, lean_object* v_keys_122_, lean_object* v_vals_123_, lean_object* v_i_124_, lean_object* v_entries_125_){
_start:
{
lean_object* v___x_126_; uint8_t v___x_127_; 
v___x_126_ = lean_array_get_size(v_keys_122_);
v___x_127_ = lean_nat_dec_lt(v_i_124_, v___x_126_);
if (v___x_127_ == 0)
{
lean_dec(v_i_124_);
return v_entries_125_;
}
else
{
lean_object* v_k_128_; lean_object* v_v_129_; uint64_t v___x_130_; size_t v_h_131_; size_t v___x_132_; lean_object* v___x_133_; size_t v___x_134_; size_t v___x_135_; size_t v___x_136_; size_t v_h_137_; lean_object* v___x_138_; lean_object* v___x_139_; 
v_k_128_ = lean_array_fget_borrowed(v_keys_122_, v_i_124_);
v_v_129_ = lean_array_fget_borrowed(v_vals_123_, v_i_124_);
v___x_130_ = l_Lean_instHashableMVarId_hash(v_k_128_);
v_h_131_ = lean_uint64_to_usize(v___x_130_);
v___x_132_ = ((size_t)5ULL);
v___x_133_ = lean_unsigned_to_nat(1u);
v___x_134_ = ((size_t)1ULL);
v___x_135_ = lean_usize_sub(v_depth_121_, v___x_134_);
v___x_136_ = lean_usize_mul(v___x_132_, v___x_135_);
v_h_137_ = lean_usize_shift_right(v_h_131_, v___x_136_);
v___x_138_ = lean_nat_add(v_i_124_, v___x_133_);
lean_dec(v_i_124_);
lean_inc(v_v_129_);
lean_inc(v_k_128_);
v___x_139_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3___redArg(v_entries_125_, v_h_137_, v_depth_121_, v_k_128_, v_v_129_);
v_i_124_ = v___x_138_;
v_entries_125_ = v___x_139_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3_spec__6___redArg___boxed(lean_object* v_depth_141_, lean_object* v_keys_142_, lean_object* v_vals_143_, lean_object* v_i_144_, lean_object* v_entries_145_){
_start:
{
size_t v_depth_boxed_146_; lean_object* v_res_147_; 
v_depth_boxed_146_ = lean_unbox_usize(v_depth_141_);
lean_dec(v_depth_141_);
v_res_147_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3_spec__6___redArg(v_depth_boxed_146_, v_keys_142_, v_vals_143_, v_i_144_, v_entries_145_);
lean_dec_ref(v_vals_143_);
lean_dec_ref(v_keys_142_);
return v_res_147_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_x_148_, lean_object* v_x_149_, lean_object* v_x_150_, lean_object* v_x_151_, lean_object* v_x_152_){
_start:
{
size_t v_x_4200__boxed_153_; size_t v_x_4201__boxed_154_; lean_object* v_res_155_; 
v_x_4200__boxed_153_ = lean_unbox_usize(v_x_149_);
lean_dec(v_x_149_);
v_x_4201__boxed_154_ = lean_unbox_usize(v_x_150_);
lean_dec(v_x_150_);
v_res_155_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3___redArg(v_x_148_, v_x_4200__boxed_153_, v_x_4201__boxed_154_, v_x_151_, v_x_152_);
return v_res_155_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2___redArg(lean_object* v_x_156_, lean_object* v_x_157_, lean_object* v_x_158_){
_start:
{
uint64_t v___x_159_; size_t v___x_160_; size_t v___x_161_; lean_object* v___x_162_; 
v___x_159_ = l_Lean_instHashableMVarId_hash(v_x_157_);
v___x_160_ = lean_uint64_to_usize(v___x_159_);
v___x_161_ = ((size_t)1ULL);
v___x_162_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3___redArg(v_x_156_, v___x_160_, v___x_161_, v_x_157_, v_x_158_);
return v___x_162_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1___redArg(lean_object* v_mvarId_163_, lean_object* v_val_164_, lean_object* v___y_165_){
_start:
{
lean_object* v___x_167_; lean_object* v_mctx_168_; lean_object* v_cache_169_; lean_object* v_zetaDeltaFVarIds_170_; lean_object* v_postponed_171_; lean_object* v_diag_172_; lean_object* v___x_174_; uint8_t v_isShared_175_; uint8_t v_isSharedCheck_199_; 
v___x_167_ = lean_st_ref_take(v___y_165_);
v_mctx_168_ = lean_ctor_get(v___x_167_, 0);
v_cache_169_ = lean_ctor_get(v___x_167_, 1);
v_zetaDeltaFVarIds_170_ = lean_ctor_get(v___x_167_, 2);
v_postponed_171_ = lean_ctor_get(v___x_167_, 3);
v_diag_172_ = lean_ctor_get(v___x_167_, 4);
v_isSharedCheck_199_ = !lean_is_exclusive(v___x_167_);
if (v_isSharedCheck_199_ == 0)
{
v___x_174_ = v___x_167_;
v_isShared_175_ = v_isSharedCheck_199_;
goto v_resetjp_173_;
}
else
{
lean_inc(v_diag_172_);
lean_inc(v_postponed_171_);
lean_inc(v_zetaDeltaFVarIds_170_);
lean_inc(v_cache_169_);
lean_inc(v_mctx_168_);
lean_dec(v___x_167_);
v___x_174_ = lean_box(0);
v_isShared_175_ = v_isSharedCheck_199_;
goto v_resetjp_173_;
}
v_resetjp_173_:
{
lean_object* v_depth_176_; lean_object* v_levelAssignDepth_177_; lean_object* v_mvarCounter_178_; lean_object* v_lDepth_179_; lean_object* v_decls_180_; lean_object* v_userNames_181_; lean_object* v_lAssignment_182_; lean_object* v_eAssignment_183_; lean_object* v_dAssignment_184_; lean_object* v___x_186_; uint8_t v_isShared_187_; uint8_t v_isSharedCheck_198_; 
v_depth_176_ = lean_ctor_get(v_mctx_168_, 0);
v_levelAssignDepth_177_ = lean_ctor_get(v_mctx_168_, 1);
v_mvarCounter_178_ = lean_ctor_get(v_mctx_168_, 2);
v_lDepth_179_ = lean_ctor_get(v_mctx_168_, 3);
v_decls_180_ = lean_ctor_get(v_mctx_168_, 4);
v_userNames_181_ = lean_ctor_get(v_mctx_168_, 5);
v_lAssignment_182_ = lean_ctor_get(v_mctx_168_, 6);
v_eAssignment_183_ = lean_ctor_get(v_mctx_168_, 7);
v_dAssignment_184_ = lean_ctor_get(v_mctx_168_, 8);
v_isSharedCheck_198_ = !lean_is_exclusive(v_mctx_168_);
if (v_isSharedCheck_198_ == 0)
{
v___x_186_ = v_mctx_168_;
v_isShared_187_ = v_isSharedCheck_198_;
goto v_resetjp_185_;
}
else
{
lean_inc(v_dAssignment_184_);
lean_inc(v_eAssignment_183_);
lean_inc(v_lAssignment_182_);
lean_inc(v_userNames_181_);
lean_inc(v_decls_180_);
lean_inc(v_lDepth_179_);
lean_inc(v_mvarCounter_178_);
lean_inc(v_levelAssignDepth_177_);
lean_inc(v_depth_176_);
lean_dec(v_mctx_168_);
v___x_186_ = lean_box(0);
v_isShared_187_ = v_isSharedCheck_198_;
goto v_resetjp_185_;
}
v_resetjp_185_:
{
lean_object* v___x_188_; lean_object* v___x_190_; 
v___x_188_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2___redArg(v_eAssignment_183_, v_mvarId_163_, v_val_164_);
if (v_isShared_187_ == 0)
{
lean_ctor_set(v___x_186_, 7, v___x_188_);
v___x_190_ = v___x_186_;
goto v_reusejp_189_;
}
else
{
lean_object* v_reuseFailAlloc_197_; 
v_reuseFailAlloc_197_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_197_, 0, v_depth_176_);
lean_ctor_set(v_reuseFailAlloc_197_, 1, v_levelAssignDepth_177_);
lean_ctor_set(v_reuseFailAlloc_197_, 2, v_mvarCounter_178_);
lean_ctor_set(v_reuseFailAlloc_197_, 3, v_lDepth_179_);
lean_ctor_set(v_reuseFailAlloc_197_, 4, v_decls_180_);
lean_ctor_set(v_reuseFailAlloc_197_, 5, v_userNames_181_);
lean_ctor_set(v_reuseFailAlloc_197_, 6, v_lAssignment_182_);
lean_ctor_set(v_reuseFailAlloc_197_, 7, v___x_188_);
lean_ctor_set(v_reuseFailAlloc_197_, 8, v_dAssignment_184_);
v___x_190_ = v_reuseFailAlloc_197_;
goto v_reusejp_189_;
}
v_reusejp_189_:
{
lean_object* v___x_192_; 
if (v_isShared_175_ == 0)
{
lean_ctor_set(v___x_174_, 0, v___x_190_);
v___x_192_ = v___x_174_;
goto v_reusejp_191_;
}
else
{
lean_object* v_reuseFailAlloc_196_; 
v_reuseFailAlloc_196_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_196_, 0, v___x_190_);
lean_ctor_set(v_reuseFailAlloc_196_, 1, v_cache_169_);
lean_ctor_set(v_reuseFailAlloc_196_, 2, v_zetaDeltaFVarIds_170_);
lean_ctor_set(v_reuseFailAlloc_196_, 3, v_postponed_171_);
lean_ctor_set(v_reuseFailAlloc_196_, 4, v_diag_172_);
v___x_192_ = v_reuseFailAlloc_196_;
goto v_reusejp_191_;
}
v_reusejp_191_:
{
lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; 
v___x_193_ = lean_st_ref_set(v___y_165_, v___x_192_);
v___x_194_ = lean_box(0);
v___x_195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_195_, 0, v___x_194_);
return v___x_195_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1___redArg___boxed(lean_object* v_mvarId_200_, lean_object* v_val_201_, lean_object* v___y_202_, lean_object* v___y_203_){
_start:
{
lean_object* v_res_204_; 
v_res_204_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1___redArg(v_mvarId_200_, v_val_201_, v___y_202_);
lean_dec(v___y_202_);
return v_res_204_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1(lean_object* v___y_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_){
_start:
{
lean_object* v_ref_244_; uint8_t v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; 
v_ref_244_ = lean_ctor_get(v___y_241_, 5);
v___x_245_ = 0;
v___x_246_ = l_Lean_SourceInfo_fromRef(v_ref_244_, v___x_245_);
v___x_247_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__3));
v___x_248_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__4));
lean_inc_n(v___x_246_, 9);
v___x_249_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_249_, 0, v___x_246_);
lean_ctor_set(v___x_249_, 1, v___x_247_);
v___x_250_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__7));
v___x_251_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__8));
v___x_252_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_252_, 0, v___x_246_);
lean_ctor_set(v___x_252_, 1, v___x_251_);
v___x_253_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__10));
v___x_254_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__12));
v___x_255_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__13));
v___x_256_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_256_, 0, v___x_246_);
lean_ctor_set(v___x_256_, 1, v___x_255_);
v___x_257_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__14));
v___x_258_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_258_, 0, v___x_246_);
lean_ctor_set(v___x_258_, 1, v___x_257_);
v___x_259_ = l_Lean_Syntax_node2(v___x_246_, v___x_254_, v___x_256_, v___x_258_);
v___x_260_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__15));
v___x_261_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_261_, 0, v___x_246_);
lean_ctor_set(v___x_261_, 1, v___x_260_);
lean_inc(v___x_259_);
v___x_262_ = l_Lean_Syntax_node3(v___x_246_, v___x_253_, v___x_259_, v___x_261_, v___x_259_);
v___x_263_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__16));
v___x_264_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_264_, 0, v___x_246_);
lean_ctor_set(v___x_264_, 1, v___x_263_);
v___x_265_ = l_Lean_Syntax_node3(v___x_246_, v___x_250_, v___x_252_, v___x_262_, v___x_264_);
v___x_266_ = l_Lean_Syntax_node2(v___x_246_, v___x_248_, v___x_249_, v___x_265_);
v___x_267_ = l_Lean_Elab_Tactic_evalTactic(v___x_266_, v___y_235_, v___y_236_, v___y_237_, v___y_238_, v___y_239_, v___y_240_, v___y_241_, v___y_242_);
return v___x_267_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___boxed(lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_){
_start:
{
lean_object* v_res_277_; 
v_res_277_ = l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1(v___y_268_, v___y_269_, v___y_270_, v___y_271_, v___y_272_, v___y_273_, v___y_274_, v___y_275_);
lean_dec(v___y_275_);
lean_dec_ref(v___y_274_);
lean_dec(v___y_273_);
lean_dec_ref(v___y_272_);
lean_dec(v___y_271_);
lean_dec_ref(v___y_270_);
lean_dec(v___y_269_);
lean_dec_ref(v___y_268_);
return v_res_277_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0_spec__0(lean_object* v_msgData_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_){
_start:
{
lean_object* v___x_284_; lean_object* v_env_285_; lean_object* v___x_286_; lean_object* v_mctx_287_; lean_object* v_lctx_288_; lean_object* v_options_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; 
v___x_284_ = lean_st_ref_get(v___y_282_);
v_env_285_ = lean_ctor_get(v___x_284_, 0);
lean_inc_ref(v_env_285_);
lean_dec(v___x_284_);
v___x_286_ = lean_st_ref_get(v___y_280_);
v_mctx_287_ = lean_ctor_get(v___x_286_, 0);
lean_inc_ref(v_mctx_287_);
lean_dec(v___x_286_);
v_lctx_288_ = lean_ctor_get(v___y_279_, 2);
v_options_289_ = lean_ctor_get(v___y_281_, 2);
lean_inc_ref(v_options_289_);
lean_inc_ref(v_lctx_288_);
v___x_290_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_290_, 0, v_env_285_);
lean_ctor_set(v___x_290_, 1, v_mctx_287_);
lean_ctor_set(v___x_290_, 2, v_lctx_288_);
lean_ctor_set(v___x_290_, 3, v_options_289_);
v___x_291_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_291_, 0, v___x_290_);
lean_ctor_set(v___x_291_, 1, v_msgData_278_);
v___x_292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_292_, 0, v___x_291_);
return v___x_292_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0_spec__0___boxed(lean_object* v_msgData_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_){
_start:
{
lean_object* v_res_299_; 
v_res_299_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0_spec__0(v_msgData_293_, v___y_294_, v___y_295_, v___y_296_, v___y_297_);
lean_dec(v___y_297_);
lean_dec_ref(v___y_296_);
lean_dec(v___y_295_);
lean_dec_ref(v___y_294_);
return v_res_299_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0___redArg(lean_object* v_msg_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_){
_start:
{
lean_object* v_ref_306_; lean_object* v___x_307_; lean_object* v_a_308_; lean_object* v___x_310_; uint8_t v_isShared_311_; uint8_t v_isSharedCheck_316_; 
v_ref_306_ = lean_ctor_get(v___y_303_, 5);
v___x_307_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0_spec__0(v_msg_300_, v___y_301_, v___y_302_, v___y_303_, v___y_304_);
v_a_308_ = lean_ctor_get(v___x_307_, 0);
v_isSharedCheck_316_ = !lean_is_exclusive(v___x_307_);
if (v_isSharedCheck_316_ == 0)
{
v___x_310_ = v___x_307_;
v_isShared_311_ = v_isSharedCheck_316_;
goto v_resetjp_309_;
}
else
{
lean_inc(v_a_308_);
lean_dec(v___x_307_);
v___x_310_ = lean_box(0);
v_isShared_311_ = v_isSharedCheck_316_;
goto v_resetjp_309_;
}
v_resetjp_309_:
{
lean_object* v___x_312_; lean_object* v___x_314_; 
lean_inc(v_ref_306_);
v___x_312_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_312_, 0, v_ref_306_);
lean_ctor_set(v___x_312_, 1, v_a_308_);
if (v_isShared_311_ == 0)
{
lean_ctor_set_tag(v___x_310_, 1);
lean_ctor_set(v___x_310_, 0, v___x_312_);
v___x_314_ = v___x_310_;
goto v_reusejp_313_;
}
else
{
lean_object* v_reuseFailAlloc_315_; 
v_reuseFailAlloc_315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_315_, 0, v___x_312_);
v___x_314_ = v_reuseFailAlloc_315_;
goto v_reusejp_313_;
}
v_reusejp_313_:
{
return v___x_314_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0___redArg___boxed(lean_object* v_msg_317_, lean_object* v___y_318_, lean_object* v___y_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_){
_start:
{
lean_object* v_res_323_; 
v_res_323_ = l_Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0___redArg(v_msg_317_, v___y_318_, v___y_319_, v___y_320_, v___y_321_);
lean_dec(v___y_321_);
lean_dec_ref(v___y_320_);
lean_dec(v___y_319_);
lean_dec_ref(v___y_318_);
return v_res_323_;
}
}
static lean_object* _init_l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___closed__1(void){
_start:
{
lean_object* v___x_325_; lean_object* v___x_326_; 
v___x_325_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___closed__0));
v___x_326_ = l_Lean_stringToMessageData(v___x_325_);
return v___x_326_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2(lean_object* v_x_342_, lean_object* v_x_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_){
_start:
{
if (lean_obj_tag(v_x_343_) == 0)
{
lean_object* v___x_349_; 
v___x_349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_349_, 0, v_x_342_);
return v___x_349_;
}
else
{
lean_object* v_head_350_; lean_object* v_tail_351_; lean_object* v___y_353_; lean_object* v___y_354_; lean_object* v___y_355_; lean_object* v___y_356_; lean_object* v___f_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; 
v_head_350_ = lean_ctor_get(v_x_343_, 0);
lean_inc(v_head_350_);
v_tail_351_ = lean_ctor_get(v_x_343_, 1);
lean_inc(v_tail_351_);
lean_dec_ref(v_x_343_);
v___f_359_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___closed__3));
v___x_360_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_run___boxed), 9, 2);
lean_closure_set(v___x_360_, 0, v_x_342_);
lean_closure_set(v___x_360_, 1, v___f_359_);
v___x_361_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___closed__5));
v___x_362_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___closed__6));
v___x_363_ = l_Lean_Elab_Term_TermElabM_run___redArg(v___x_360_, v___x_361_, v___x_362_, v___y_344_, v___y_345_, v___y_346_, v___y_347_);
if (lean_obj_tag(v___x_363_) == 0)
{
lean_object* v_a_364_; lean_object* v_fst_365_; 
v_a_364_ = lean_ctor_get(v___x_363_, 0);
lean_inc(v_a_364_);
lean_dec_ref(v___x_363_);
v_fst_365_ = lean_ctor_get(v_a_364_, 0);
lean_inc(v_fst_365_);
lean_dec(v_a_364_);
if (lean_obj_tag(v_fst_365_) == 1)
{
lean_object* v_tail_366_; 
v_tail_366_ = lean_ctor_get(v_fst_365_, 1);
lean_inc(v_tail_366_);
if (lean_obj_tag(v_tail_366_) == 1)
{
lean_object* v_tail_367_; 
v_tail_367_ = lean_ctor_get(v_tail_366_, 1);
if (lean_obj_tag(v_tail_367_) == 0)
{
lean_object* v_head_368_; lean_object* v_head_369_; lean_object* v___x_370_; 
v_head_368_ = lean_ctor_get(v_fst_365_, 0);
lean_inc(v_head_368_);
lean_dec_ref(v_fst_365_);
v_head_369_ = lean_ctor_get(v_tail_366_, 0);
lean_inc(v_head_369_);
lean_dec_ref(v_tail_366_);
v___x_370_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1___redArg(v_head_368_, v_head_350_, v___y_345_);
lean_dec_ref(v___x_370_);
v_x_342_ = v_head_369_;
v_x_343_ = v_tail_351_;
goto _start;
}
else
{
lean_dec_ref(v_tail_366_);
lean_dec_ref(v_fst_365_);
lean_dec(v_tail_351_);
lean_dec(v_head_350_);
v___y_353_ = v___y_344_;
v___y_354_ = v___y_345_;
v___y_355_ = v___y_346_;
v___y_356_ = v___y_347_;
goto v___jp_352_;
}
}
else
{
lean_dec(v_tail_366_);
lean_dec_ref(v_fst_365_);
lean_dec(v_tail_351_);
lean_dec(v_head_350_);
v___y_353_ = v___y_344_;
v___y_354_ = v___y_345_;
v___y_355_ = v___y_346_;
v___y_356_ = v___y_347_;
goto v___jp_352_;
}
}
else
{
lean_dec(v_fst_365_);
lean_dec(v_tail_351_);
lean_dec(v_head_350_);
v___y_353_ = v___y_344_;
v___y_354_ = v___y_345_;
v___y_355_ = v___y_346_;
v___y_356_ = v___y_347_;
goto v___jp_352_;
}
}
else
{
lean_object* v_a_372_; lean_object* v___x_374_; uint8_t v_isShared_375_; uint8_t v_isSharedCheck_379_; 
lean_dec(v_tail_351_);
lean_dec(v_head_350_);
v_a_372_ = lean_ctor_get(v___x_363_, 0);
v_isSharedCheck_379_ = !lean_is_exclusive(v___x_363_);
if (v_isSharedCheck_379_ == 0)
{
v___x_374_ = v___x_363_;
v_isShared_375_ = v_isSharedCheck_379_;
goto v_resetjp_373_;
}
else
{
lean_inc(v_a_372_);
lean_dec(v___x_363_);
v___x_374_ = lean_box(0);
v_isShared_375_ = v_isSharedCheck_379_;
goto v_resetjp_373_;
}
v_resetjp_373_:
{
lean_object* v___x_377_; 
if (v_isShared_375_ == 0)
{
v___x_377_ = v___x_374_;
goto v_reusejp_376_;
}
else
{
lean_object* v_reuseFailAlloc_378_; 
v_reuseFailAlloc_378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_378_, 0, v_a_372_);
v___x_377_ = v_reuseFailAlloc_378_;
goto v_reusejp_376_;
}
v_reusejp_376_:
{
return v___x_377_;
}
}
}
v___jp_352_:
{
lean_object* v___x_357_; lean_object* v___x_358_; 
v___x_357_ = lean_obj_once(&l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___closed__1, &l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___closed__1_once, _init_l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___closed__1);
v___x_358_ = l_Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0___redArg(v___x_357_, v___y_353_, v___y_354_, v___y_355_, v___y_356_);
return v___x_358_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___boxed(lean_object* v_x_380_, lean_object* v_x_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_){
_start:
{
lean_object* v_res_387_; 
v_res_387_ = l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2(v_x_380_, v_x_381_, v___y_382_, v___y_383_, v___y_384_, v___y_385_);
lean_dec(v___y_385_);
lean_dec_ref(v___y_384_);
lean_dec(v___y_383_);
lean_dec_ref(v___y_382_);
return v_res_387_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi(lean_object* v_mvar_388_, lean_object* v_es_389_, lean_object* v_a_390_, lean_object* v_a_391_, lean_object* v_a_392_, lean_object* v_a_393_){
_start:
{
lean_object* v___x_395_; 
v___x_395_ = l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2(v_mvar_388_, v_es_389_, v_a_390_, v_a_391_, v_a_392_, v_a_393_);
return v___x_395_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi___boxed(lean_object* v_mvar_396_, lean_object* v_es_397_, lean_object* v_a_398_, lean_object* v_a_399_, lean_object* v_a_400_, lean_object* v_a_401_, lean_object* v_a_402_){
_start:
{
lean_object* v_res_403_; 
v_res_403_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi(v_mvar_396_, v_es_397_, v_a_398_, v_a_399_, v_a_400_, v_a_401_);
lean_dec(v_a_401_);
lean_dec_ref(v_a_400_);
lean_dec(v_a_399_);
lean_dec_ref(v_a_398_);
return v_res_403_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0(lean_object* v_00_u03b1_404_, lean_object* v_msg_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_){
_start:
{
lean_object* v___x_411_; 
v___x_411_ = l_Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0___redArg(v_msg_405_, v___y_406_, v___y_407_, v___y_408_, v___y_409_);
return v___x_411_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0___boxed(lean_object* v_00_u03b1_412_, lean_object* v_msg_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_){
_start:
{
lean_object* v_res_419_; 
v_res_419_ = l_Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0(v_00_u03b1_412_, v_msg_413_, v___y_414_, v___y_415_, v___y_416_, v___y_417_);
lean_dec(v___y_417_);
lean_dec_ref(v___y_416_);
lean_dec(v___y_415_);
lean_dec_ref(v___y_414_);
return v_res_419_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1(lean_object* v_mvarId_420_, lean_object* v_val_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_){
_start:
{
lean_object* v___x_427_; 
v___x_427_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1___redArg(v_mvarId_420_, v_val_421_, v___y_423_);
return v___x_427_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1___boxed(lean_object* v_mvarId_428_, lean_object* v_val_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_){
_start:
{
lean_object* v_res_435_; 
v_res_435_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1(v_mvarId_428_, v_val_429_, v___y_430_, v___y_431_, v___y_432_, v___y_433_);
lean_dec(v___y_433_);
lean_dec_ref(v___y_432_);
lean_dec(v___y_431_);
lean_dec_ref(v___y_430_);
return v_res_435_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2(lean_object* v_00_u03b2_436_, lean_object* v_x_437_, lean_object* v_x_438_, lean_object* v_x_439_){
_start:
{
lean_object* v___x_440_; 
v___x_440_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2___redArg(v_x_437_, v_x_438_, v_x_439_);
return v___x_440_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_441_, lean_object* v_x_442_, size_t v_x_443_, size_t v_x_444_, lean_object* v_x_445_, lean_object* v_x_446_){
_start:
{
lean_object* v___x_447_; 
v___x_447_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3___redArg(v_x_442_, v_x_443_, v_x_444_, v_x_445_, v_x_446_);
return v___x_447_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03b2_448_, lean_object* v_x_449_, lean_object* v_x_450_, lean_object* v_x_451_, lean_object* v_x_452_, lean_object* v_x_453_){
_start:
{
size_t v_x_4866__boxed_454_; size_t v_x_4867__boxed_455_; lean_object* v_res_456_; 
v_x_4866__boxed_454_ = lean_unbox_usize(v_x_450_);
lean_dec(v_x_450_);
v_x_4867__boxed_455_ = lean_unbox_usize(v_x_451_);
lean_dec(v_x_451_);
v_res_456_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3(v_00_u03b2_448_, v_x_449_, v_x_4866__boxed_454_, v_x_4867__boxed_455_, v_x_452_, v_x_453_);
return v_res_456_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3_spec__5(lean_object* v_00_u03b2_457_, lean_object* v_n_458_, lean_object* v_k_459_, lean_object* v_v_460_){
_start:
{
lean_object* v___x_461_; 
v___x_461_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3_spec__5___redArg(v_n_458_, v_k_459_, v_v_460_);
return v___x_461_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3_spec__6(lean_object* v_00_u03b2_462_, size_t v_depth_463_, lean_object* v_keys_464_, lean_object* v_vals_465_, lean_object* v_heq_466_, lean_object* v_i_467_, lean_object* v_entries_468_){
_start:
{
lean_object* v___x_469_; 
v___x_469_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3_spec__6___redArg(v_depth_463_, v_keys_464_, v_vals_465_, v_i_467_, v_entries_468_);
return v___x_469_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3_spec__6___boxed(lean_object* v_00_u03b2_470_, lean_object* v_depth_471_, lean_object* v_keys_472_, lean_object* v_vals_473_, lean_object* v_heq_474_, lean_object* v_i_475_, lean_object* v_entries_476_){
_start:
{
size_t v_depth_boxed_477_; lean_object* v_res_478_; 
v_depth_boxed_477_ = lean_unbox_usize(v_depth_471_);
lean_dec(v_depth_471_);
v_res_478_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3_spec__6(v_00_u03b2_470_, v_depth_boxed_477_, v_keys_472_, v_vals_473_, v_heq_474_, v_i_475_, v_entries_476_);
lean_dec_ref(v_vals_473_);
lean_dec_ref(v_keys_472_);
return v_res_478_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3_spec__5_spec__6(lean_object* v_00_u03b2_479_, lean_object* v_x_480_, lean_object* v_x_481_, lean_object* v_x_482_, lean_object* v_x_483_){
_start:
{
lean_object* v___x_484_; 
v___x_484_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3_spec__5_spec__6___redArg(v_x_480_, v_x_481_, v_x_482_, v_x_483_);
return v___x_484_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor_spec__0___redArg(lean_object* v_mvarId_485_, lean_object* v_x_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_){
_start:
{
lean_object* v___x_492_; 
v___x_492_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_485_, v_x_486_, v___y_487_, v___y_488_, v___y_489_, v___y_490_);
if (lean_obj_tag(v___x_492_) == 0)
{
lean_object* v_a_493_; lean_object* v___x_495_; uint8_t v_isShared_496_; uint8_t v_isSharedCheck_500_; 
v_a_493_ = lean_ctor_get(v___x_492_, 0);
v_isSharedCheck_500_ = !lean_is_exclusive(v___x_492_);
if (v_isSharedCheck_500_ == 0)
{
v___x_495_ = v___x_492_;
v_isShared_496_ = v_isSharedCheck_500_;
goto v_resetjp_494_;
}
else
{
lean_inc(v_a_493_);
lean_dec(v___x_492_);
v___x_495_ = lean_box(0);
v_isShared_496_ = v_isSharedCheck_500_;
goto v_resetjp_494_;
}
v_resetjp_494_:
{
lean_object* v___x_498_; 
if (v_isShared_496_ == 0)
{
v___x_498_ = v___x_495_;
goto v_reusejp_497_;
}
else
{
lean_object* v_reuseFailAlloc_499_; 
v_reuseFailAlloc_499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_499_, 0, v_a_493_);
v___x_498_ = v_reuseFailAlloc_499_;
goto v_reusejp_497_;
}
v_reusejp_497_:
{
return v___x_498_;
}
}
}
else
{
lean_object* v_a_501_; lean_object* v___x_503_; uint8_t v_isShared_504_; uint8_t v_isSharedCheck_508_; 
v_a_501_ = lean_ctor_get(v___x_492_, 0);
v_isSharedCheck_508_ = !lean_is_exclusive(v___x_492_);
if (v_isSharedCheck_508_ == 0)
{
v___x_503_ = v___x_492_;
v_isShared_504_ = v_isSharedCheck_508_;
goto v_resetjp_502_;
}
else
{
lean_inc(v_a_501_);
lean_dec(v___x_492_);
v___x_503_ = lean_box(0);
v_isShared_504_ = v_isSharedCheck_508_;
goto v_resetjp_502_;
}
v_resetjp_502_:
{
lean_object* v___x_506_; 
if (v_isShared_504_ == 0)
{
v___x_506_ = v___x_503_;
goto v_reusejp_505_;
}
else
{
lean_object* v_reuseFailAlloc_507_; 
v_reuseFailAlloc_507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_507_, 0, v_a_501_);
v___x_506_ = v_reuseFailAlloc_507_;
goto v_reusejp_505_;
}
v_reusejp_505_:
{
return v___x_506_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor_spec__0___redArg___boxed(lean_object* v_mvarId_509_, lean_object* v_x_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_){
_start:
{
lean_object* v_res_516_; 
v_res_516_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor_spec__0___redArg(v_mvarId_509_, v_x_510_, v___y_511_, v___y_512_, v___y_513_, v___y_514_);
lean_dec(v___y_514_);
lean_dec_ref(v___y_513_);
lean_dec(v___y_512_);
lean_dec_ref(v___y_511_);
return v_res_516_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor_spec__0(lean_object* v_00_u03b1_517_, lean_object* v_mvarId_518_, lean_object* v_x_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_){
_start:
{
lean_object* v___x_525_; 
v___x_525_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor_spec__0___redArg(v_mvarId_518_, v_x_519_, v___y_520_, v___y_521_, v___y_522_, v___y_523_);
return v___x_525_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor_spec__0___boxed(lean_object* v_00_u03b1_526_, lean_object* v_mvarId_527_, lean_object* v_x_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_){
_start:
{
lean_object* v_res_534_; 
v_res_534_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor_spec__0(v_00_u03b1_526_, v_mvarId_527_, v_x_528_, v___y_529_, v___y_530_, v___y_531_, v___y_532_);
lean_dec(v___y_532_);
lean_dec_ref(v___y_531_);
lean_dec(v___y_530_);
lean_dec_ref(v___y_529_);
return v_res_534_;
}
}
static lean_object* _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0___closed__2(void){
_start:
{
lean_object* v___x_538_; lean_object* v___x_539_; 
v___x_538_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0___closed__1));
v___x_539_ = l_Lean_MessageData_ofFormat(v___x_538_);
return v___x_539_;
}
}
static lean_object* _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0___closed__3(void){
_start:
{
lean_object* v___x_540_; lean_object* v___x_541_; 
v___x_540_ = lean_obj_once(&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0___closed__2, &l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0___closed__2_once, _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0___closed__2);
v___x_541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_541_, 0, v___x_540_);
return v___x_541_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0(lean_object* v_goal_546_, lean_object* v_name_547_, lean_object* v_idx_548_, lean_object* v_expected_x3f_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_){
_start:
{
lean_object* v___y_556_; lean_object* v___y_557_; lean_object* v___y_558_; lean_object* v___y_559_; lean_object* v___x_562_; 
lean_inc(v_name_547_);
lean_inc(v_goal_546_);
v___x_562_ = l_Lean_MVarId_checkNotAssigned(v_goal_546_, v_name_547_, v___y_550_, v___y_551_, v___y_552_, v___y_553_);
if (lean_obj_tag(v___x_562_) == 0)
{
lean_object* v___x_563_; 
lean_dec_ref(v___x_562_);
lean_inc(v_goal_546_);
v___x_563_ = l_Lean_MVarId_getType_x27(v_goal_546_, v___y_550_, v___y_551_, v___y_552_, v___y_553_);
if (lean_obj_tag(v___x_563_) == 0)
{
lean_object* v_a_564_; lean_object* v___x_565_; 
v_a_564_ = lean_ctor_get(v___x_563_, 0);
lean_inc(v_a_564_);
lean_dec_ref(v___x_563_);
v___x_565_ = l_Lean_Expr_getAppFn(v_a_564_);
lean_dec(v_a_564_);
if (lean_obj_tag(v___x_565_) == 4)
{
lean_object* v_declName_566_; lean_object* v_us_567_; lean_object* v___x_568_; lean_object* v_env_569_; uint8_t v___x_570_; lean_object* v___x_571_; 
v_declName_566_ = lean_ctor_get(v___x_565_, 0);
lean_inc(v_declName_566_);
v_us_567_ = lean_ctor_get(v___x_565_, 1);
lean_inc(v_us_567_);
lean_dec_ref(v___x_565_);
v___x_568_ = lean_st_ref_get(v___y_553_);
v_env_569_ = lean_ctor_get(v___x_568_, 0);
lean_inc_ref(v_env_569_);
lean_dec(v___x_568_);
v___x_570_ = 0;
v___x_571_ = l_Lean_Environment_find_x3f(v_env_569_, v_declName_566_, v___x_570_);
if (lean_obj_tag(v___x_571_) == 0)
{
lean_dec(v_us_567_);
lean_dec(v_expected_x3f_549_);
lean_dec(v_idx_548_);
v___y_556_ = v___y_550_;
v___y_557_ = v___y_551_;
v___y_558_ = v___y_552_;
v___y_559_ = v___y_553_;
goto v___jp_555_;
}
else
{
lean_object* v_val_572_; lean_object* v___x_574_; uint8_t v_isShared_575_; uint8_t v_isSharedCheck_642_; 
v_val_572_ = lean_ctor_get(v___x_571_, 0);
v_isSharedCheck_642_ = !lean_is_exclusive(v___x_571_);
if (v_isSharedCheck_642_ == 0)
{
v___x_574_ = v___x_571_;
v_isShared_575_ = v_isSharedCheck_642_;
goto v_resetjp_573_;
}
else
{
lean_inc(v_val_572_);
lean_dec(v___x_571_);
v___x_574_ = lean_box(0);
v_isShared_575_ = v_isSharedCheck_642_;
goto v_resetjp_573_;
}
v_resetjp_573_:
{
if (lean_obj_tag(v_val_572_) == 5)
{
lean_object* v_val_576_; lean_object* v___x_578_; uint8_t v_isShared_579_; uint8_t v_isSharedCheck_641_; 
v_val_576_ = lean_ctor_get(v_val_572_, 0);
v_isSharedCheck_641_ = !lean_is_exclusive(v_val_572_);
if (v_isSharedCheck_641_ == 0)
{
v___x_578_ = v_val_572_;
v_isShared_579_ = v_isSharedCheck_641_;
goto v_resetjp_577_;
}
else
{
lean_inc(v_val_576_);
lean_dec(v_val_572_);
v___x_578_ = lean_box(0);
v_isShared_579_ = v_isSharedCheck_641_;
goto v_resetjp_577_;
}
v_resetjp_577_:
{
lean_object* v___y_581_; lean_object* v___y_582_; lean_object* v___y_583_; lean_object* v___y_584_; 
if (lean_obj_tag(v_expected_x3f_549_) == 1)
{
lean_object* v_val_611_; lean_object* v___x_613_; uint8_t v_isShared_614_; uint8_t v_isSharedCheck_640_; 
v_val_611_ = lean_ctor_get(v_expected_x3f_549_, 0);
v_isSharedCheck_640_ = !lean_is_exclusive(v_expected_x3f_549_);
if (v_isSharedCheck_640_ == 0)
{
v___x_613_ = v_expected_x3f_549_;
v_isShared_614_ = v_isSharedCheck_640_;
goto v_resetjp_612_;
}
else
{
lean_inc(v_val_611_);
lean_dec(v_expected_x3f_549_);
v___x_613_ = lean_box(0);
v_isShared_614_ = v_isSharedCheck_640_;
goto v_resetjp_612_;
}
v_resetjp_612_:
{
lean_object* v_ctors_615_; lean_object* v___x_616_; uint8_t v___x_617_; 
v_ctors_615_ = lean_ctor_get(v_val_576_, 4);
v___x_616_ = l_List_lengthTR___redArg(v_ctors_615_);
v___x_617_ = lean_nat_dec_eq(v___x_616_, v_val_611_);
lean_dec(v___x_616_);
if (v___x_617_ == 0)
{
uint8_t v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_629_; 
v___x_618_ = 1;
lean_inc(v_name_547_);
v___x_619_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_547_, v___x_618_);
v___x_620_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0___closed__7));
v___x_621_ = lean_string_append(v___x_619_, v___x_620_);
v___x_622_ = l_Nat_reprFast(v_val_611_);
v___x_623_ = lean_string_append(v___x_621_, v___x_622_);
lean_dec_ref(v___x_622_);
v___x_624_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0___closed__6));
v___x_625_ = lean_string_append(v___x_623_, v___x_624_);
v___x_626_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_626_, 0, v___x_625_);
v___x_627_ = l_Lean_MessageData_ofFormat(v___x_626_);
if (v_isShared_614_ == 0)
{
lean_ctor_set(v___x_613_, 0, v___x_627_);
v___x_629_ = v___x_613_;
goto v_reusejp_628_;
}
else
{
lean_object* v_reuseFailAlloc_639_; 
v_reuseFailAlloc_639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_639_, 0, v___x_627_);
v___x_629_ = v_reuseFailAlloc_639_;
goto v_reusejp_628_;
}
v_reusejp_628_:
{
lean_object* v___x_630_; 
lean_inc(v_goal_546_);
lean_inc(v_name_547_);
v___x_630_ = l_Lean_Meta_throwTacticEx___redArg(v_name_547_, v_goal_546_, v___x_629_, v___y_550_, v___y_551_, v___y_552_, v___y_553_);
if (lean_obj_tag(v___x_630_) == 0)
{
lean_dec_ref(v___x_630_);
v___y_581_ = v___y_550_;
v___y_582_ = v___y_551_;
v___y_583_ = v___y_552_;
v___y_584_ = v___y_553_;
goto v___jp_580_;
}
else
{
lean_object* v_a_631_; lean_object* v___x_633_; uint8_t v_isShared_634_; uint8_t v_isSharedCheck_638_; 
lean_del_object(v___x_578_);
lean_dec_ref(v_val_576_);
lean_del_object(v___x_574_);
lean_dec(v_us_567_);
lean_dec(v_idx_548_);
lean_dec(v_name_547_);
lean_dec(v_goal_546_);
v_a_631_ = lean_ctor_get(v___x_630_, 0);
v_isSharedCheck_638_ = !lean_is_exclusive(v___x_630_);
if (v_isSharedCheck_638_ == 0)
{
v___x_633_ = v___x_630_;
v_isShared_634_ = v_isSharedCheck_638_;
goto v_resetjp_632_;
}
else
{
lean_inc(v_a_631_);
lean_dec(v___x_630_);
v___x_633_ = lean_box(0);
v_isShared_634_ = v_isSharedCheck_638_;
goto v_resetjp_632_;
}
v_resetjp_632_:
{
lean_object* v___x_636_; 
if (v_isShared_634_ == 0)
{
v___x_636_ = v___x_633_;
goto v_reusejp_635_;
}
else
{
lean_object* v_reuseFailAlloc_637_; 
v_reuseFailAlloc_637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_637_, 0, v_a_631_);
v___x_636_ = v_reuseFailAlloc_637_;
goto v_reusejp_635_;
}
v_reusejp_635_:
{
return v___x_636_;
}
}
}
}
}
else
{
lean_del_object(v___x_613_);
lean_dec(v_val_611_);
v___y_581_ = v___y_550_;
v___y_582_ = v___y_551_;
v___y_583_ = v___y_552_;
v___y_584_ = v___y_553_;
goto v___jp_580_;
}
}
}
else
{
lean_dec(v_expected_x3f_549_);
v___y_581_ = v___y_550_;
v___y_582_ = v___y_551_;
v___y_583_ = v___y_552_;
v___y_584_ = v___y_553_;
goto v___jp_580_;
}
v___jp_580_:
{
lean_object* v_ctors_585_; lean_object* v___x_586_; uint8_t v___x_587_; 
v_ctors_585_ = lean_ctor_get(v_val_576_, 4);
lean_inc(v_ctors_585_);
lean_dec_ref(v_val_576_);
v___x_586_ = l_List_lengthTR___redArg(v_ctors_585_);
v___x_587_ = lean_nat_dec_lt(v_idx_548_, v___x_586_);
if (v___x_587_ == 0)
{
lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_598_; 
lean_dec(v_ctors_585_);
lean_dec(v_us_567_);
v___x_588_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0___closed__4));
v___x_589_ = l_Nat_reprFast(v_idx_548_);
v___x_590_ = lean_string_append(v___x_588_, v___x_589_);
lean_dec_ref(v___x_589_);
v___x_591_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0___closed__5));
v___x_592_ = lean_string_append(v___x_590_, v___x_591_);
v___x_593_ = l_Nat_reprFast(v___x_586_);
v___x_594_ = lean_string_append(v___x_592_, v___x_593_);
lean_dec_ref(v___x_593_);
v___x_595_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0___closed__6));
v___x_596_ = lean_string_append(v___x_594_, v___x_595_);
if (v_isShared_579_ == 0)
{
lean_ctor_set_tag(v___x_578_, 3);
lean_ctor_set(v___x_578_, 0, v___x_596_);
v___x_598_ = v___x_578_;
goto v_reusejp_597_;
}
else
{
lean_object* v_reuseFailAlloc_604_; 
v_reuseFailAlloc_604_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_604_, 0, v___x_596_);
v___x_598_ = v_reuseFailAlloc_604_;
goto v_reusejp_597_;
}
v_reusejp_597_:
{
lean_object* v___x_599_; lean_object* v___x_601_; 
v___x_599_ = l_Lean_MessageData_ofFormat(v___x_598_);
if (v_isShared_575_ == 0)
{
lean_ctor_set(v___x_574_, 0, v___x_599_);
v___x_601_ = v___x_574_;
goto v_reusejp_600_;
}
else
{
lean_object* v_reuseFailAlloc_603_; 
v_reuseFailAlloc_603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_603_, 0, v___x_599_);
v___x_601_ = v_reuseFailAlloc_603_;
goto v_reusejp_600_;
}
v_reusejp_600_:
{
lean_object* v___x_602_; 
v___x_602_ = l_Lean_Meta_throwTacticEx___redArg(v_name_547_, v_goal_546_, v___x_601_, v___y_581_, v___y_582_, v___y_583_, v___y_584_);
return v___x_602_;
}
}
}
else
{
lean_object* v___x_605_; lean_object* v___x_606_; uint8_t v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; 
lean_dec(v___x_586_);
lean_del_object(v___x_578_);
lean_del_object(v___x_574_);
lean_dec(v_name_547_);
v___x_605_ = l_List_get___redArg(v_ctors_585_, v_idx_548_);
lean_dec(v_ctors_585_);
v___x_606_ = l_Lean_mkConst(v___x_605_, v_us_567_);
v___x_607_ = 0;
v___x_608_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_608_, 0, v___x_607_);
lean_ctor_set_uint8(v___x_608_, 1, v___x_587_);
lean_ctor_set_uint8(v___x_608_, 2, v___x_570_);
lean_ctor_set_uint8(v___x_608_, 3, v___x_587_);
v___x_609_ = lean_box(0);
v___x_610_ = l_Lean_MVarId_apply(v_goal_546_, v___x_606_, v___x_608_, v___x_609_, v___y_581_, v___y_582_, v___y_583_, v___y_584_);
return v___x_610_;
}
}
}
}
else
{
lean_del_object(v___x_574_);
lean_dec(v_val_572_);
lean_dec(v_us_567_);
lean_dec(v_expected_x3f_549_);
lean_dec(v_idx_548_);
v___y_556_ = v___y_550_;
v___y_557_ = v___y_551_;
v___y_558_ = v___y_552_;
v___y_559_ = v___y_553_;
goto v___jp_555_;
}
}
}
}
else
{
lean_dec_ref(v___x_565_);
lean_dec(v_expected_x3f_549_);
lean_dec(v_idx_548_);
v___y_556_ = v___y_550_;
v___y_557_ = v___y_551_;
v___y_558_ = v___y_552_;
v___y_559_ = v___y_553_;
goto v___jp_555_;
}
}
else
{
lean_object* v_a_643_; lean_object* v___x_645_; uint8_t v_isShared_646_; uint8_t v_isSharedCheck_650_; 
lean_dec(v_expected_x3f_549_);
lean_dec(v_idx_548_);
lean_dec(v_name_547_);
lean_dec(v_goal_546_);
v_a_643_ = lean_ctor_get(v___x_563_, 0);
v_isSharedCheck_650_ = !lean_is_exclusive(v___x_563_);
if (v_isSharedCheck_650_ == 0)
{
v___x_645_ = v___x_563_;
v_isShared_646_ = v_isSharedCheck_650_;
goto v_resetjp_644_;
}
else
{
lean_inc(v_a_643_);
lean_dec(v___x_563_);
v___x_645_ = lean_box(0);
v_isShared_646_ = v_isSharedCheck_650_;
goto v_resetjp_644_;
}
v_resetjp_644_:
{
lean_object* v___x_648_; 
if (v_isShared_646_ == 0)
{
v___x_648_ = v___x_645_;
goto v_reusejp_647_;
}
else
{
lean_object* v_reuseFailAlloc_649_; 
v_reuseFailAlloc_649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_649_, 0, v_a_643_);
v___x_648_ = v_reuseFailAlloc_649_;
goto v_reusejp_647_;
}
v_reusejp_647_:
{
return v___x_648_;
}
}
}
}
else
{
lean_object* v_a_651_; lean_object* v___x_653_; uint8_t v_isShared_654_; uint8_t v_isSharedCheck_658_; 
lean_dec(v_expected_x3f_549_);
lean_dec(v_idx_548_);
lean_dec(v_name_547_);
lean_dec(v_goal_546_);
v_a_651_ = lean_ctor_get(v___x_562_, 0);
v_isSharedCheck_658_ = !lean_is_exclusive(v___x_562_);
if (v_isSharedCheck_658_ == 0)
{
v___x_653_ = v___x_562_;
v_isShared_654_ = v_isSharedCheck_658_;
goto v_resetjp_652_;
}
else
{
lean_inc(v_a_651_);
lean_dec(v___x_562_);
v___x_653_ = lean_box(0);
v_isShared_654_ = v_isSharedCheck_658_;
goto v_resetjp_652_;
}
v_resetjp_652_:
{
lean_object* v___x_656_; 
if (v_isShared_654_ == 0)
{
v___x_656_ = v___x_653_;
goto v_reusejp_655_;
}
else
{
lean_object* v_reuseFailAlloc_657_; 
v_reuseFailAlloc_657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_657_, 0, v_a_651_);
v___x_656_ = v_reuseFailAlloc_657_;
goto v_reusejp_655_;
}
v_reusejp_655_:
{
return v___x_656_;
}
}
}
v___jp_555_:
{
lean_object* v___x_560_; lean_object* v___x_561_; 
v___x_560_ = lean_obj_once(&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0___closed__3, &l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0___closed__3_once, _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0___closed__3);
v___x_561_ = l_Lean_Meta_throwTacticEx___redArg(v_name_547_, v_goal_546_, v___x_560_, v___y_556_, v___y_557_, v___y_558_, v___y_559_);
return v___x_561_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0___boxed(lean_object* v_goal_659_, lean_object* v_name_660_, lean_object* v_idx_661_, lean_object* v_expected_x3f_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_){
_start:
{
lean_object* v_res_668_; 
v_res_668_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0(v_goal_659_, v_name_660_, v_idx_661_, v_expected_x3f_662_, v___y_663_, v___y_664_, v___y_665_, v___y_666_);
lean_dec(v___y_666_);
lean_dec_ref(v___y_665_);
lean_dec(v___y_664_);
lean_dec_ref(v___y_663_);
return v_res_668_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor(lean_object* v_name_669_, lean_object* v_idx_670_, lean_object* v_expected_x3f_671_, lean_object* v_goal_672_, lean_object* v_a_673_, lean_object* v_a_674_, lean_object* v_a_675_, lean_object* v_a_676_){
_start:
{
lean_object* v___f_678_; lean_object* v___x_679_; 
lean_inc(v_goal_672_);
v___f_678_ = lean_alloc_closure((void*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0___boxed), 9, 4);
lean_closure_set(v___f_678_, 0, v_goal_672_);
lean_closure_set(v___f_678_, 1, v_name_669_);
lean_closure_set(v___f_678_, 2, v_idx_670_);
lean_closure_set(v___f_678_, 3, v_expected_x3f_671_);
v___x_679_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor_spec__0___redArg(v_goal_672_, v___f_678_, v_a_673_, v_a_674_, v_a_675_, v_a_676_);
return v___x_679_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___boxed(lean_object* v_name_680_, lean_object* v_idx_681_, lean_object* v_expected_x3f_682_, lean_object* v_goal_683_, lean_object* v_a_684_, lean_object* v_a_685_, lean_object* v_a_686_, lean_object* v_a_687_, lean_object* v_a_688_){
_start:
{
lean_object* v_res_689_; 
v_res_689_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor(v_name_680_, v_idx_681_, v_expected_x3f_682_, v_goal_683_, v_a_684_, v_a_685_, v_a_686_, v_a_687_);
lean_dec(v_a_687_);
lean_dec_ref(v_a_686_);
lean_dec(v_a_685_);
lean_dec_ref(v_a_684_);
return v_res_689_;
}
}
static lean_object* _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__4(void){
_start:
{
lean_object* v___x_696_; lean_object* v___x_697_; 
v___x_696_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__3));
v___x_697_ = l_Lean_stringToMessageData(v___x_696_);
return v___x_697_;
}
}
static lean_object* _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__8(void){
_start:
{
lean_object* v___x_702_; lean_object* v___x_703_; 
v___x_702_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__7));
v___x_703_ = l_Lean_stringToMessageData(v___x_702_);
return v___x_703_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select(lean_object* v_m_704_, lean_object* v_n_705_, lean_object* v_goal_706_, lean_object* v_a_707_, lean_object* v_a_708_, lean_object* v_a_709_, lean_object* v_a_710_){
_start:
{
lean_object* v_zero_712_; uint8_t v_isZero_713_; 
v_zero_712_ = lean_unsigned_to_nat(0u);
v_isZero_713_ = lean_nat_dec_eq(v_m_704_, v_zero_712_);
if (v_isZero_713_ == 1)
{
uint8_t v_isZero_714_; 
lean_dec(v_m_704_);
v_isZero_714_ = lean_nat_dec_eq(v_n_705_, v_zero_712_);
lean_dec(v_n_705_);
if (v_isZero_714_ == 1)
{
lean_object* v___x_715_; 
v___x_715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_715_, 0, v_goal_706_);
return v___x_715_;
}
else
{
lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; 
v___x_716_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__1));
v___x_717_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__2));
v___x_718_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor(v___x_716_, v_zero_712_, v___x_717_, v_goal_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_);
if (lean_obj_tag(v___x_718_) == 0)
{
lean_object* v_a_719_; lean_object* v___x_721_; uint8_t v_isShared_722_; uint8_t v_isSharedCheck_735_; 
v_a_719_ = lean_ctor_get(v___x_718_, 0);
v_isSharedCheck_735_ = !lean_is_exclusive(v___x_718_);
if (v_isSharedCheck_735_ == 0)
{
v___x_721_ = v___x_718_;
v_isShared_722_ = v_isSharedCheck_735_;
goto v_resetjp_720_;
}
else
{
lean_inc(v_a_719_);
lean_dec(v___x_718_);
v___x_721_ = lean_box(0);
v_isShared_722_ = v_isSharedCheck_735_;
goto v_resetjp_720_;
}
v_resetjp_720_:
{
lean_object* v___y_724_; lean_object* v___y_725_; lean_object* v___y_726_; lean_object* v___y_727_; 
if (lean_obj_tag(v_a_719_) == 1)
{
lean_object* v_tail_730_; 
v_tail_730_ = lean_ctor_get(v_a_719_, 1);
if (lean_obj_tag(v_tail_730_) == 0)
{
lean_object* v_head_731_; lean_object* v___x_733_; 
v_head_731_ = lean_ctor_get(v_a_719_, 0);
lean_inc(v_head_731_);
lean_dec_ref(v_a_719_);
if (v_isShared_722_ == 0)
{
lean_ctor_set(v___x_721_, 0, v_head_731_);
v___x_733_ = v___x_721_;
goto v_reusejp_732_;
}
else
{
lean_object* v_reuseFailAlloc_734_; 
v_reuseFailAlloc_734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_734_, 0, v_head_731_);
v___x_733_ = v_reuseFailAlloc_734_;
goto v_reusejp_732_;
}
v_reusejp_732_:
{
return v___x_733_;
}
}
else
{
lean_dec_ref(v_a_719_);
lean_del_object(v___x_721_);
v___y_724_ = v_a_707_;
v___y_725_ = v_a_708_;
v___y_726_ = v_a_709_;
v___y_727_ = v_a_710_;
goto v___jp_723_;
}
}
else
{
lean_del_object(v___x_721_);
lean_dec(v_a_719_);
v___y_724_ = v_a_707_;
v___y_725_ = v_a_708_;
v___y_726_ = v_a_709_;
v___y_727_ = v_a_710_;
goto v___jp_723_;
}
v___jp_723_:
{
lean_object* v___x_728_; lean_object* v___x_729_; 
v___x_728_ = lean_obj_once(&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__4, &l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__4_once, _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__4);
v___x_729_ = l_Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0___redArg(v___x_728_, v___y_724_, v___y_725_, v___y_726_, v___y_727_);
return v___x_729_;
}
}
}
else
{
lean_object* v_a_736_; lean_object* v___x_738_; uint8_t v_isShared_739_; uint8_t v_isSharedCheck_743_; 
v_a_736_ = lean_ctor_get(v___x_718_, 0);
v_isSharedCheck_743_ = !lean_is_exclusive(v___x_718_);
if (v_isSharedCheck_743_ == 0)
{
v___x_738_ = v___x_718_;
v_isShared_739_ = v_isSharedCheck_743_;
goto v_resetjp_737_;
}
else
{
lean_inc(v_a_736_);
lean_dec(v___x_718_);
v___x_738_ = lean_box(0);
v_isShared_739_ = v_isSharedCheck_743_;
goto v_resetjp_737_;
}
v_resetjp_737_:
{
lean_object* v___x_741_; 
if (v_isShared_739_ == 0)
{
v___x_741_ = v___x_738_;
goto v_reusejp_740_;
}
else
{
lean_object* v_reuseFailAlloc_742_; 
v_reuseFailAlloc_742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_742_, 0, v_a_736_);
v___x_741_ = v_reuseFailAlloc_742_;
goto v_reusejp_740_;
}
v_reusejp_740_:
{
return v___x_741_;
}
}
}
}
}
else
{
uint8_t v_isZero_744_; 
v_isZero_744_ = lean_nat_dec_eq(v_n_705_, v_zero_712_);
if (v_isZero_744_ == 0)
{
lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; 
v___x_745_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__6));
v___x_746_ = lean_unsigned_to_nat(1u);
v___x_747_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__2));
v___x_748_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor(v___x_745_, v___x_746_, v___x_747_, v_goal_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_);
if (lean_obj_tag(v___x_748_) == 0)
{
lean_object* v_a_749_; lean_object* v___y_751_; lean_object* v___y_752_; lean_object* v___y_753_; lean_object* v___y_754_; 
v_a_749_ = lean_ctor_get(v___x_748_, 0);
lean_inc(v_a_749_);
lean_dec_ref(v___x_748_);
if (lean_obj_tag(v_a_749_) == 1)
{
lean_object* v_tail_757_; 
v_tail_757_ = lean_ctor_get(v_a_749_, 1);
if (lean_obj_tag(v_tail_757_) == 0)
{
lean_object* v_head_758_; lean_object* v_n_759_; lean_object* v_n_760_; 
v_head_758_ = lean_ctor_get(v_a_749_, 0);
lean_inc(v_head_758_);
lean_dec_ref(v_a_749_);
v_n_759_ = lean_nat_sub(v_m_704_, v___x_746_);
lean_dec(v_m_704_);
v_n_760_ = lean_nat_sub(v_n_705_, v___x_746_);
lean_dec(v_n_705_);
v_m_704_ = v_n_759_;
v_n_705_ = v_n_760_;
v_goal_706_ = v_head_758_;
goto _start;
}
else
{
lean_dec_ref(v_a_749_);
lean_dec(v_n_705_);
lean_dec(v_m_704_);
v___y_751_ = v_a_707_;
v___y_752_ = v_a_708_;
v___y_753_ = v_a_709_;
v___y_754_ = v_a_710_;
goto v___jp_750_;
}
}
else
{
lean_dec(v_a_749_);
lean_dec(v_n_705_);
lean_dec(v_m_704_);
v___y_751_ = v_a_707_;
v___y_752_ = v_a_708_;
v___y_753_ = v_a_709_;
v___y_754_ = v_a_710_;
goto v___jp_750_;
}
v___jp_750_:
{
lean_object* v___x_755_; lean_object* v___x_756_; 
v___x_755_ = lean_obj_once(&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__4, &l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__4_once, _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__4);
v___x_756_ = l_Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0___redArg(v___x_755_, v___y_751_, v___y_752_, v___y_753_, v___y_754_);
return v___x_756_;
}
}
else
{
lean_object* v_a_762_; lean_object* v___x_764_; uint8_t v_isShared_765_; uint8_t v_isSharedCheck_769_; 
lean_dec(v_n_705_);
lean_dec(v_m_704_);
v_a_762_ = lean_ctor_get(v___x_748_, 0);
v_isSharedCheck_769_ = !lean_is_exclusive(v___x_748_);
if (v_isSharedCheck_769_ == 0)
{
v___x_764_ = v___x_748_;
v_isShared_765_ = v_isSharedCheck_769_;
goto v_resetjp_763_;
}
else
{
lean_inc(v_a_762_);
lean_dec(v___x_748_);
v___x_764_ = lean_box(0);
v_isShared_765_ = v_isSharedCheck_769_;
goto v_resetjp_763_;
}
v_resetjp_763_:
{
lean_object* v___x_767_; 
if (v_isShared_765_ == 0)
{
v___x_767_ = v___x_764_;
goto v_reusejp_766_;
}
else
{
lean_object* v_reuseFailAlloc_768_; 
v_reuseFailAlloc_768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_768_, 0, v_a_762_);
v___x_767_ = v_reuseFailAlloc_768_;
goto v_reusejp_766_;
}
v_reusejp_766_:
{
return v___x_767_;
}
}
}
}
else
{
lean_object* v___x_770_; lean_object* v___x_771_; 
lean_dec(v_goal_706_);
lean_dec(v_n_705_);
lean_dec(v_m_704_);
v___x_770_ = lean_obj_once(&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__8, &l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__8_once, _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__8);
v___x_771_ = l_Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0___redArg(v___x_770_, v_a_707_, v_a_708_, v_a_709_, v_a_710_);
return v___x_771_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___boxed(lean_object* v_m_772_, lean_object* v_n_773_, lean_object* v_goal_774_, lean_object* v_a_775_, lean_object* v_a_776_, lean_object* v_a_777_, lean_object* v_a_778_, lean_object* v_a_779_){
_start:
{
lean_object* v_res_780_; 
v_res_780_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select(v_m_772_, v_n_773_, v_goal_774_, v_a_775_, v_a_776_, v_a_777_, v_a_778_);
lean_dec(v_a_778_);
lean_dec_ref(v_a_777_);
lean_dec(v_a_776_);
lean_dec_ref(v_a_775_);
return v_res_780_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_compactRelation___lam__0(lean_object* v___y_781_){
_start:
{
lean_inc_ref(v___y_781_);
return v___y_781_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_compactRelation___lam__0___boxed(lean_object* v___y_782_){
_start:
{
lean_object* v_res_783_; 
v_res_783_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_compactRelation___lam__0(v___y_782_);
lean_dec_ref(v___y_782_);
return v_res_783_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_compactRelation___lam__1(lean_object* v_snd_784_, lean_object* v_head_785_, lean_object* v_fst_786_, lean_object* v___y_787_){
_start:
{
lean_object* v___x_788_; lean_object* v___x_789_; 
v___x_788_ = lean_apply_1(v_snd_784_, v___y_787_);
v___x_789_ = l_Lean_Expr_replaceFVar(v___x_788_, v_head_785_, v_fst_786_);
lean_dec_ref(v___x_788_);
return v___x_789_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_compactRelation___lam__1___boxed(lean_object* v_snd_790_, lean_object* v_head_791_, lean_object* v_fst_792_, lean_object* v___y_793_){
_start:
{
lean_object* v_res_794_; 
v_res_794_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_compactRelation___lam__1(v_snd_790_, v_head_791_, v_fst_792_, v___y_793_);
lean_dec_ref(v_fst_792_);
return v_res_794_;
}
}
LEAN_EXPORT lean_object* l_List_span_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_compactRelation_spec__0(lean_object* v_head_795_, lean_object* v_a_796_, lean_object* v_a_797_){
_start:
{
if (lean_obj_tag(v_a_796_) == 0)
{
lean_object* v___x_798_; lean_object* v___x_799_; 
v___x_798_ = l_List_reverse___redArg(v_a_797_);
v___x_799_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_799_, 0, v___x_798_);
lean_ctor_set(v___x_799_, 1, v_a_796_);
return v___x_799_;
}
else
{
lean_object* v_head_800_; lean_object* v_tail_801_; lean_object* v_snd_802_; uint8_t v___x_803_; 
v_head_800_ = lean_ctor_get(v_a_796_, 0);
lean_inc(v_head_800_);
v_tail_801_ = lean_ctor_get(v_a_796_, 1);
v_snd_802_ = lean_ctor_get(v_head_800_, 1);
v___x_803_ = lean_expr_eqv(v_snd_802_, v_head_795_);
if (v___x_803_ == 0)
{
lean_object* v___x_805_; uint8_t v_isShared_806_; uint8_t v_isSharedCheck_811_; 
lean_inc(v_tail_801_);
v_isSharedCheck_811_ = !lean_is_exclusive(v_a_796_);
if (v_isSharedCheck_811_ == 0)
{
lean_object* v_unused_812_; lean_object* v_unused_813_; 
v_unused_812_ = lean_ctor_get(v_a_796_, 1);
lean_dec(v_unused_812_);
v_unused_813_ = lean_ctor_get(v_a_796_, 0);
lean_dec(v_unused_813_);
v___x_805_ = v_a_796_;
v_isShared_806_ = v_isSharedCheck_811_;
goto v_resetjp_804_;
}
else
{
lean_dec(v_a_796_);
v___x_805_ = lean_box(0);
v_isShared_806_ = v_isSharedCheck_811_;
goto v_resetjp_804_;
}
v_resetjp_804_:
{
lean_object* v___x_808_; 
if (v_isShared_806_ == 0)
{
lean_ctor_set(v___x_805_, 1, v_a_797_);
v___x_808_ = v___x_805_;
goto v_reusejp_807_;
}
else
{
lean_object* v_reuseFailAlloc_810_; 
v_reuseFailAlloc_810_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_810_, 0, v_head_800_);
lean_ctor_set(v_reuseFailAlloc_810_, 1, v_a_797_);
v___x_808_ = v_reuseFailAlloc_810_;
goto v_reusejp_807_;
}
v_reusejp_807_:
{
v_a_796_ = v_tail_801_;
v_a_797_ = v___x_808_;
goto _start;
}
}
}
else
{
lean_object* v___x_815_; uint8_t v_isShared_816_; uint8_t v_isSharedCheck_821_; 
v_isSharedCheck_821_ = !lean_is_exclusive(v_head_800_);
if (v_isSharedCheck_821_ == 0)
{
lean_object* v_unused_822_; lean_object* v_unused_823_; 
v_unused_822_ = lean_ctor_get(v_head_800_, 1);
lean_dec(v_unused_822_);
v_unused_823_ = lean_ctor_get(v_head_800_, 0);
lean_dec(v_unused_823_);
v___x_815_ = v_head_800_;
v_isShared_816_ = v_isSharedCheck_821_;
goto v_resetjp_814_;
}
else
{
lean_dec(v_head_800_);
v___x_815_ = lean_box(0);
v_isShared_816_ = v_isSharedCheck_821_;
goto v_resetjp_814_;
}
v_resetjp_814_:
{
lean_object* v___x_817_; lean_object* v___x_819_; 
v___x_817_ = l_List_reverse___redArg(v_a_797_);
if (v_isShared_816_ == 0)
{
lean_ctor_set(v___x_815_, 1, v_a_796_);
lean_ctor_set(v___x_815_, 0, v___x_817_);
v___x_819_ = v___x_815_;
goto v_reusejp_818_;
}
else
{
lean_object* v_reuseFailAlloc_820_; 
v_reuseFailAlloc_820_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_820_, 0, v___x_817_);
lean_ctor_set(v_reuseFailAlloc_820_, 1, v_a_796_);
v___x_819_ = v_reuseFailAlloc_820_;
goto v_reusejp_818_;
}
v_reusejp_818_:
{
return v___x_819_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_span_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_compactRelation_spec__0___boxed(lean_object* v_head_824_, lean_object* v_a_825_, lean_object* v_a_826_){
_start:
{
lean_object* v_res_827_; 
v_res_827_ = l_List_span_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_compactRelation_spec__0(v_head_824_, v_a_825_, v_a_826_);
lean_dec_ref(v_head_824_);
return v_res_827_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_compactRelation_spec__2(lean_object* v_head_828_, lean_object* v_fst_829_, lean_object* v_a_830_, lean_object* v_a_831_){
_start:
{
if (lean_obj_tag(v_a_830_) == 0)
{
lean_object* v___x_832_; 
lean_dec_ref(v_head_828_);
v___x_832_ = l_List_reverse___redArg(v_a_831_);
return v___x_832_;
}
else
{
lean_object* v_head_833_; lean_object* v_tail_834_; lean_object* v___x_836_; uint8_t v_isShared_837_; uint8_t v_isSharedCheck_852_; 
v_head_833_ = lean_ctor_get(v_a_830_, 0);
v_tail_834_ = lean_ctor_get(v_a_830_, 1);
v_isSharedCheck_852_ = !lean_is_exclusive(v_a_830_);
if (v_isSharedCheck_852_ == 0)
{
v___x_836_ = v_a_830_;
v_isShared_837_ = v_isSharedCheck_852_;
goto v_resetjp_835_;
}
else
{
lean_inc(v_tail_834_);
lean_inc(v_head_833_);
lean_dec(v_a_830_);
v___x_836_ = lean_box(0);
v_isShared_837_ = v_isSharedCheck_852_;
goto v_resetjp_835_;
}
v_resetjp_835_:
{
lean_object* v_fst_838_; lean_object* v_snd_839_; lean_object* v___x_841_; uint8_t v_isShared_842_; uint8_t v_isSharedCheck_851_; 
v_fst_838_ = lean_ctor_get(v_head_833_, 0);
v_snd_839_ = lean_ctor_get(v_head_833_, 1);
v_isSharedCheck_851_ = !lean_is_exclusive(v_head_833_);
if (v_isSharedCheck_851_ == 0)
{
v___x_841_ = v_head_833_;
v_isShared_842_ = v_isSharedCheck_851_;
goto v_resetjp_840_;
}
else
{
lean_inc(v_snd_839_);
lean_inc(v_fst_838_);
lean_dec(v_head_833_);
v___x_841_ = lean_box(0);
v_isShared_842_ = v_isSharedCheck_851_;
goto v_resetjp_840_;
}
v_resetjp_840_:
{
lean_object* v___x_843_; lean_object* v___x_845_; 
lean_inc_ref(v_head_828_);
v___x_843_ = l_Lean_Expr_replaceFVar(v_snd_839_, v_head_828_, v_fst_829_);
lean_dec(v_snd_839_);
if (v_isShared_842_ == 0)
{
lean_ctor_set(v___x_841_, 1, v___x_843_);
v___x_845_ = v___x_841_;
goto v_reusejp_844_;
}
else
{
lean_object* v_reuseFailAlloc_850_; 
v_reuseFailAlloc_850_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_850_, 0, v_fst_838_);
lean_ctor_set(v_reuseFailAlloc_850_, 1, v___x_843_);
v___x_845_ = v_reuseFailAlloc_850_;
goto v_reusejp_844_;
}
v_reusejp_844_:
{
lean_object* v___x_847_; 
if (v_isShared_837_ == 0)
{
lean_ctor_set(v___x_836_, 1, v_a_831_);
lean_ctor_set(v___x_836_, 0, v___x_845_);
v___x_847_ = v___x_836_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_849_; 
v_reuseFailAlloc_849_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_849_, 0, v___x_845_);
lean_ctor_set(v_reuseFailAlloc_849_, 1, v_a_831_);
v___x_847_ = v_reuseFailAlloc_849_;
goto v_reusejp_846_;
}
v_reusejp_846_:
{
v_a_830_ = v_tail_834_;
v_a_831_ = v___x_847_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_compactRelation_spec__2___boxed(lean_object* v_head_853_, lean_object* v_fst_854_, lean_object* v_a_855_, lean_object* v_a_856_){
_start:
{
lean_object* v_res_857_; 
v_res_857_ = l_List_mapTR_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_compactRelation_spec__2(v_head_853_, v_fst_854_, v_a_855_, v_a_856_);
lean_dec_ref(v_fst_854_);
return v_res_857_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_compactRelation_spec__1(lean_object* v_head_858_, lean_object* v_fst_859_, lean_object* v_a_860_, lean_object* v_a_861_){
_start:
{
if (lean_obj_tag(v_a_860_) == 0)
{
lean_object* v___x_862_; 
lean_dec_ref(v_head_858_);
v___x_862_ = l_List_reverse___redArg(v_a_861_);
return v___x_862_;
}
else
{
lean_object* v_head_863_; lean_object* v_tail_864_; lean_object* v___x_866_; uint8_t v_isShared_867_; uint8_t v_isSharedCheck_873_; 
v_head_863_ = lean_ctor_get(v_a_860_, 0);
v_tail_864_ = lean_ctor_get(v_a_860_, 1);
v_isSharedCheck_873_ = !lean_is_exclusive(v_a_860_);
if (v_isSharedCheck_873_ == 0)
{
v___x_866_ = v_a_860_;
v_isShared_867_ = v_isSharedCheck_873_;
goto v_resetjp_865_;
}
else
{
lean_inc(v_tail_864_);
lean_inc(v_head_863_);
lean_dec(v_a_860_);
v___x_866_ = lean_box(0);
v_isShared_867_ = v_isSharedCheck_873_;
goto v_resetjp_865_;
}
v_resetjp_865_:
{
lean_object* v___x_868_; lean_object* v___x_870_; 
lean_inc_ref(v_head_858_);
v___x_868_ = l_Lean_Expr_replaceFVar(v_head_863_, v_head_858_, v_fst_859_);
lean_dec(v_head_863_);
if (v_isShared_867_ == 0)
{
lean_ctor_set(v___x_866_, 1, v_a_861_);
lean_ctor_set(v___x_866_, 0, v___x_868_);
v___x_870_ = v___x_866_;
goto v_reusejp_869_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v___x_868_);
lean_ctor_set(v_reuseFailAlloc_872_, 1, v_a_861_);
v___x_870_ = v_reuseFailAlloc_872_;
goto v_reusejp_869_;
}
v_reusejp_869_:
{
v_a_860_ = v_tail_864_;
v_a_861_ = v___x_870_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_compactRelation_spec__1___boxed(lean_object* v_head_874_, lean_object* v_fst_875_, lean_object* v_a_876_, lean_object* v_a_877_){
_start:
{
lean_object* v_res_878_; 
v_res_878_ = l_List_mapTR_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_compactRelation_spec__1(v_head_874_, v_fst_875_, v_a_876_, v_a_877_);
lean_dec_ref(v_fst_875_);
return v_res_878_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_compactRelation(lean_object* v_x_880_, lean_object* v_x_881_){
_start:
{
if (lean_obj_tag(v_x_880_) == 0)
{
lean_object* v___f_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; 
v___f_882_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_compactRelation___closed__0));
v___x_883_ = lean_box(0);
v___x_884_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_884_, 0, v_x_881_);
lean_ctor_set(v___x_884_, 1, v___f_882_);
v___x_885_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_885_, 0, v___x_883_);
lean_ctor_set(v___x_885_, 1, v___x_884_);
return v___x_885_;
}
else
{
lean_object* v_head_886_; lean_object* v_tail_887_; lean_object* v___x_889_; uint8_t v_isShared_890_; uint8_t v_isSharedCheck_944_; 
v_head_886_ = lean_ctor_get(v_x_880_, 0);
v_tail_887_ = lean_ctor_get(v_x_880_, 1);
v_isSharedCheck_944_ = !lean_is_exclusive(v_x_880_);
if (v_isSharedCheck_944_ == 0)
{
v___x_889_ = v_x_880_;
v_isShared_890_ = v_isSharedCheck_944_;
goto v_resetjp_888_;
}
else
{
lean_inc(v_tail_887_);
lean_inc(v_head_886_);
lean_dec(v_x_880_);
v___x_889_ = lean_box(0);
v_isShared_890_ = v_isSharedCheck_944_;
goto v_resetjp_888_;
}
v_resetjp_888_:
{
lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v_snd_893_; 
v___x_891_ = lean_box(0);
lean_inc(v_x_881_);
v___x_892_ = l_List_span_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_compactRelation_spec__0(v_head_886_, v_x_881_, v___x_891_);
v_snd_893_ = lean_ctor_get(v___x_892_, 1);
lean_inc(v_snd_893_);
if (lean_obj_tag(v_snd_893_) == 0)
{
lean_object* v___x_894_; lean_object* v_fst_895_; lean_object* v_snd_896_; lean_object* v___x_898_; uint8_t v_isShared_899_; uint8_t v_isSharedCheck_907_; 
lean_dec_ref(v___x_892_);
v___x_894_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_compactRelation(v_tail_887_, v_x_881_);
v_fst_895_ = lean_ctor_get(v___x_894_, 0);
v_snd_896_ = lean_ctor_get(v___x_894_, 1);
v_isSharedCheck_907_ = !lean_is_exclusive(v___x_894_);
if (v_isSharedCheck_907_ == 0)
{
v___x_898_ = v___x_894_;
v_isShared_899_ = v_isSharedCheck_907_;
goto v_resetjp_897_;
}
else
{
lean_inc(v_snd_896_);
lean_inc(v_fst_895_);
lean_dec(v___x_894_);
v___x_898_ = lean_box(0);
v_isShared_899_ = v_isSharedCheck_907_;
goto v_resetjp_897_;
}
v_resetjp_897_:
{
lean_object* v___x_900_; lean_object* v___x_902_; 
v___x_900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_900_, 0, v_head_886_);
if (v_isShared_890_ == 0)
{
lean_ctor_set(v___x_889_, 1, v_fst_895_);
lean_ctor_set(v___x_889_, 0, v___x_900_);
v___x_902_ = v___x_889_;
goto v_reusejp_901_;
}
else
{
lean_object* v_reuseFailAlloc_906_; 
v_reuseFailAlloc_906_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_906_, 0, v___x_900_);
lean_ctor_set(v_reuseFailAlloc_906_, 1, v_fst_895_);
v___x_902_ = v_reuseFailAlloc_906_;
goto v_reusejp_901_;
}
v_reusejp_901_:
{
lean_object* v___x_904_; 
if (v_isShared_899_ == 0)
{
lean_ctor_set(v___x_898_, 0, v___x_902_);
v___x_904_ = v___x_898_;
goto v_reusejp_903_;
}
else
{
lean_object* v_reuseFailAlloc_905_; 
v_reuseFailAlloc_905_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_905_, 0, v___x_902_);
lean_ctor_set(v_reuseFailAlloc_905_, 1, v_snd_896_);
v___x_904_ = v_reuseFailAlloc_905_;
goto v_reusejp_903_;
}
v_reusejp_903_:
{
return v___x_904_;
}
}
}
}
else
{
lean_object* v_head_908_; lean_object* v_fst_909_; lean_object* v_tail_910_; lean_object* v___x_912_; uint8_t v_isShared_913_; uint8_t v_isSharedCheck_942_; 
lean_del_object(v___x_889_);
lean_dec(v_x_881_);
v_head_908_ = lean_ctor_get(v_snd_893_, 0);
lean_inc(v_head_908_);
v_fst_909_ = lean_ctor_get(v___x_892_, 0);
lean_inc(v_fst_909_);
lean_dec_ref(v___x_892_);
v_tail_910_ = lean_ctor_get(v_snd_893_, 1);
v_isSharedCheck_942_ = !lean_is_exclusive(v_snd_893_);
if (v_isSharedCheck_942_ == 0)
{
lean_object* v_unused_943_; 
v_unused_943_ = lean_ctor_get(v_snd_893_, 0);
lean_dec(v_unused_943_);
v___x_912_ = v_snd_893_;
v_isShared_913_ = v_isSharedCheck_942_;
goto v_resetjp_911_;
}
else
{
lean_inc(v_tail_910_);
lean_dec(v_snd_893_);
v___x_912_ = lean_box(0);
v_isShared_913_ = v_isSharedCheck_942_;
goto v_resetjp_911_;
}
v_resetjp_911_:
{
lean_object* v_fst_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v_snd_919_; lean_object* v_fst_920_; lean_object* v___x_922_; uint8_t v_isShared_923_; uint8_t v_isSharedCheck_941_; 
v_fst_914_ = lean_ctor_get(v_head_908_, 0);
lean_inc(v_fst_914_);
lean_dec(v_head_908_);
lean_inc_n(v_head_886_, 2);
v___x_915_ = l_List_mapTR_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_compactRelation_spec__1(v_head_886_, v_fst_914_, v_tail_887_, v___x_891_);
v___x_916_ = l_List_appendTR___redArg(v_fst_909_, v_tail_910_);
v___x_917_ = l_List_mapTR_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_compactRelation_spec__2(v_head_886_, v_fst_914_, v___x_916_, v___x_891_);
v___x_918_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_compactRelation(v___x_915_, v___x_917_);
v_snd_919_ = lean_ctor_get(v___x_918_, 1);
v_fst_920_ = lean_ctor_get(v___x_918_, 0);
v_isSharedCheck_941_ = !lean_is_exclusive(v___x_918_);
if (v_isSharedCheck_941_ == 0)
{
v___x_922_ = v___x_918_;
v_isShared_923_ = v_isSharedCheck_941_;
goto v_resetjp_921_;
}
else
{
lean_inc(v_snd_919_);
lean_inc(v_fst_920_);
lean_dec(v___x_918_);
v___x_922_ = lean_box(0);
v_isShared_923_ = v_isSharedCheck_941_;
goto v_resetjp_921_;
}
v_resetjp_921_:
{
lean_object* v_fst_924_; lean_object* v_snd_925_; lean_object* v___x_927_; uint8_t v_isShared_928_; uint8_t v_isSharedCheck_940_; 
v_fst_924_ = lean_ctor_get(v_snd_919_, 0);
v_snd_925_ = lean_ctor_get(v_snd_919_, 1);
v_isSharedCheck_940_ = !lean_is_exclusive(v_snd_919_);
if (v_isSharedCheck_940_ == 0)
{
v___x_927_ = v_snd_919_;
v_isShared_928_ = v_isSharedCheck_940_;
goto v_resetjp_926_;
}
else
{
lean_inc(v_snd_925_);
lean_inc(v_fst_924_);
lean_dec(v_snd_919_);
v___x_927_ = lean_box(0);
v_isShared_928_ = v_isSharedCheck_940_;
goto v_resetjp_926_;
}
v_resetjp_926_:
{
lean_object* v___f_929_; lean_object* v___x_930_; lean_object* v___x_932_; 
v___f_929_ = lean_alloc_closure((void*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_compactRelation___lam__1___boxed), 4, 3);
lean_closure_set(v___f_929_, 0, v_snd_925_);
lean_closure_set(v___f_929_, 1, v_head_886_);
lean_closure_set(v___f_929_, 2, v_fst_914_);
v___x_930_ = lean_box(0);
if (v_isShared_913_ == 0)
{
lean_ctor_set(v___x_912_, 1, v_fst_920_);
lean_ctor_set(v___x_912_, 0, v___x_930_);
v___x_932_ = v___x_912_;
goto v_reusejp_931_;
}
else
{
lean_object* v_reuseFailAlloc_939_; 
v_reuseFailAlloc_939_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_939_, 0, v___x_930_);
lean_ctor_set(v_reuseFailAlloc_939_, 1, v_fst_920_);
v___x_932_ = v_reuseFailAlloc_939_;
goto v_reusejp_931_;
}
v_reusejp_931_:
{
lean_object* v___x_934_; 
if (v_isShared_928_ == 0)
{
lean_ctor_set(v___x_927_, 1, v___f_929_);
v___x_934_ = v___x_927_;
goto v_reusejp_933_;
}
else
{
lean_object* v_reuseFailAlloc_938_; 
v_reuseFailAlloc_938_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_938_, 0, v_fst_924_);
lean_ctor_set(v_reuseFailAlloc_938_, 1, v___f_929_);
v___x_934_ = v_reuseFailAlloc_938_;
goto v_reusejp_933_;
}
v_reusejp_933_:
{
lean_object* v___x_936_; 
if (v_isShared_923_ == 0)
{
lean_ctor_set(v___x_922_, 1, v___x_934_);
lean_ctor_set(v___x_922_, 0, v___x_932_);
v___x_936_ = v___x_922_;
goto v_reusejp_935_;
}
else
{
lean_object* v_reuseFailAlloc_937_; 
v_reuseFailAlloc_937_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_937_, 0, v___x_932_);
lean_ctor_set(v_reuseFailAlloc_937_, 1, v___x_934_);
v___x_936_ = v_reuseFailAlloc_937_;
goto v_reusejp_935_;
}
v_reusejp_935_:
{
return v___x_936_;
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
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_updateLambdaBinderInfoD_x21_spec__0(lean_object* v_msg_945_){
_start:
{
lean_object* v___x_946_; lean_object* v___x_947_; 
v___x_946_ = l_Lean_instInhabitedExpr;
v___x_947_ = lean_panic_fn_borrowed(v___x_946_, v_msg_945_);
return v___x_947_;
}
}
static lean_object* _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_updateLambdaBinderInfoD_x21___closed__3(void){
_start:
{
lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; 
v___x_951_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_updateLambdaBinderInfoD_x21___closed__2));
v___x_952_ = lean_unsigned_to_nat(19u);
v___x_953_ = lean_unsigned_to_nat(96u);
v___x_954_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_updateLambdaBinderInfoD_x21___closed__1));
v___x_955_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_updateLambdaBinderInfoD_x21___closed__0));
v___x_956_ = l_mkPanicMessageWithDecl(v___x_955_, v___x_954_, v___x_953_, v___x_952_, v___x_951_);
return v___x_956_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_updateLambdaBinderInfoD_x21(lean_object* v_e_957_){
_start:
{
if (lean_obj_tag(v_e_957_) == 6)
{
lean_object* v_binderName_958_; lean_object* v_binderType_959_; lean_object* v_body_960_; uint8_t v___x_961_; lean_object* v___x_962_; 
v_binderName_958_ = lean_ctor_get(v_e_957_, 0);
lean_inc(v_binderName_958_);
v_binderType_959_ = lean_ctor_get(v_e_957_, 1);
lean_inc_ref(v_binderType_959_);
v_body_960_ = lean_ctor_get(v_e_957_, 2);
lean_inc_ref(v_body_960_);
lean_dec_ref(v_e_957_);
v___x_961_ = 0;
v___x_962_ = l_Lean_Expr_lam___override(v_binderName_958_, v_binderType_959_, v_body_960_, v___x_961_);
return v___x_962_;
}
else
{
lean_object* v___x_963_; lean_object* v___x_964_; 
lean_dec_ref(v_e_957_);
v___x_963_ = lean_obj_once(&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_updateLambdaBinderInfoD_x21___closed__3, &l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_updateLambdaBinderInfoD_x21___closed__3_once, _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_updateLambdaBinderInfoD_x21___closed__3);
v___x_964_ = l_panic___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_updateLambdaBinderInfoD_x21_spec__0(v___x_963_);
return v___x_964_;
}
}
}
static lean_object* _init_l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkExistsList_spec__0___closed__4(void){
_start:
{
lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; 
v___x_971_ = lean_box(0);
v___x_972_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkExistsList_spec__0___closed__3));
v___x_973_ = l_Lean_mkConst(v___x_972_, v___x_971_);
return v___x_973_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkExistsList_spec__0(lean_object* v_x_974_, lean_object* v_x_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_){
_start:
{
if (lean_obj_tag(v_x_975_) == 0)
{
lean_object* v___x_981_; 
v___x_981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_981_, 0, v_x_974_);
return v___x_981_;
}
else
{
lean_object* v_head_982_; lean_object* v_tail_983_; lean_object* v___x_985_; uint8_t v_isShared_986_; uint8_t v_isSharedCheck_1022_; 
v_head_982_ = lean_ctor_get(v_x_975_, 0);
v_tail_983_ = lean_ctor_get(v_x_975_, 1);
v_isSharedCheck_1022_ = !lean_is_exclusive(v_x_975_);
if (v_isSharedCheck_1022_ == 0)
{
v___x_985_ = v_x_975_;
v_isShared_986_ = v_isSharedCheck_1022_;
goto v_resetjp_984_;
}
else
{
lean_inc(v_tail_983_);
lean_inc(v_head_982_);
lean_dec(v_x_975_);
v___x_985_ = lean_box(0);
v_isShared_986_ = v_isSharedCheck_1022_;
goto v_resetjp_984_;
}
v_resetjp_984_:
{
lean_object* v___y_988_; lean_object* v___x_991_; 
lean_inc(v___y_979_);
lean_inc_ref(v___y_978_);
lean_inc(v___y_977_);
lean_inc_ref(v___y_976_);
lean_inc(v_head_982_);
v___x_991_ = lean_infer_type(v_head_982_, v___y_976_, v___y_977_, v___y_978_, v___y_979_);
if (lean_obj_tag(v___x_991_) == 0)
{
lean_object* v_a_992_; lean_object* v___x_993_; 
v_a_992_ = lean_ctor_get(v___x_991_, 0);
lean_inc_n(v_a_992_, 2);
lean_dec_ref(v___x_991_);
lean_inc(v___y_979_);
lean_inc_ref(v___y_978_);
lean_inc(v___y_977_);
lean_inc_ref(v___y_976_);
v___x_993_ = lean_infer_type(v_a_992_, v___y_976_, v___y_977_, v___y_978_, v___y_979_);
if (lean_obj_tag(v___x_993_) == 0)
{
lean_object* v_a_994_; lean_object* v___x_995_; uint8_t v___y_1015_; uint8_t v___x_1019_; 
v_a_994_ = lean_ctor_get(v___x_993_, 0);
lean_inc(v_a_994_);
lean_dec_ref(v___x_993_);
v___x_995_ = l_Lean_Expr_sortLevel_x21(v_a_994_);
lean_dec(v_a_994_);
lean_inc(v_head_982_);
v___x_1019_ = l_Lean_Expr_occurs(v_head_982_, v_x_974_);
if (v___x_1019_ == 0)
{
lean_object* v___x_1020_; uint8_t v___x_1021_; 
v___x_1020_ = lean_box(0);
v___x_1021_ = lean_level_eq(v___x_995_, v___x_1020_);
if (v___x_1021_ == 0)
{
goto v___jp_996_;
}
else
{
v___y_1015_ = v___x_1019_;
goto v___jp_1014_;
}
}
else
{
v___y_1015_ = v___x_1019_;
goto v___jp_1014_;
}
v___jp_996_:
{
uint8_t v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; uint8_t v___x_1001_; uint8_t v___x_1002_; lean_object* v___x_1003_; 
v___x_997_ = 1;
v___x_998_ = lean_unsigned_to_nat(1u);
v___x_999_ = lean_mk_empty_array_with_capacity(v___x_998_);
v___x_1000_ = lean_array_push(v___x_999_, v_head_982_);
v___x_1001_ = 0;
v___x_1002_ = 1;
v___x_1003_ = l_Lean_Meta_mkLambdaFVars(v___x_1000_, v_x_974_, v___x_1001_, v___x_997_, v___x_1001_, v___x_997_, v___x_1002_, v___y_976_, v___y_977_, v___y_978_, v___y_979_);
lean_dec_ref(v___x_1000_);
if (lean_obj_tag(v___x_1003_) == 0)
{
lean_object* v_a_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1008_; 
v_a_1004_ = lean_ctor_get(v___x_1003_, 0);
lean_inc(v_a_1004_);
lean_dec_ref(v___x_1003_);
v___x_1005_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkExistsList_spec__0___closed__1));
v___x_1006_ = lean_box(0);
if (v_isShared_986_ == 0)
{
lean_ctor_set(v___x_985_, 1, v___x_1006_);
lean_ctor_set(v___x_985_, 0, v___x_995_);
v___x_1008_ = v___x_985_;
goto v_reusejp_1007_;
}
else
{
lean_object* v_reuseFailAlloc_1013_; 
v_reuseFailAlloc_1013_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1013_, 0, v___x_995_);
lean_ctor_set(v_reuseFailAlloc_1013_, 1, v___x_1006_);
v___x_1008_ = v_reuseFailAlloc_1013_;
goto v_reusejp_1007_;
}
v_reusejp_1007_:
{
lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; 
v___x_1009_ = l_Lean_Expr_const___override(v___x_1005_, v___x_1008_);
v___x_1010_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_updateLambdaBinderInfoD_x21(v_a_1004_);
v___x_1011_ = l_Lean_mkAppB(v___x_1009_, v_a_992_, v___x_1010_);
v_x_974_ = v___x_1011_;
v_x_975_ = v_tail_983_;
goto _start;
}
}
else
{
lean_dec(v___x_995_);
lean_dec(v_a_992_);
lean_del_object(v___x_985_);
v___y_988_ = v___x_1003_;
goto v___jp_987_;
}
}
v___jp_1014_:
{
if (v___y_1015_ == 0)
{
lean_object* v___x_1016_; lean_object* v___x_1017_; 
lean_dec(v___x_995_);
lean_del_object(v___x_985_);
lean_dec(v_head_982_);
v___x_1016_ = lean_obj_once(&l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkExistsList_spec__0___closed__4, &l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkExistsList_spec__0___closed__4_once, _init_l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkExistsList_spec__0___closed__4);
v___x_1017_ = l_Lean_mkAppB(v___x_1016_, v_a_992_, v_x_974_);
v_x_974_ = v___x_1017_;
v_x_975_ = v_tail_983_;
goto _start;
}
else
{
goto v___jp_996_;
}
}
}
else
{
lean_dec(v_a_992_);
lean_del_object(v___x_985_);
lean_dec(v_head_982_);
lean_dec_ref(v_x_974_);
v___y_988_ = v___x_993_;
goto v___jp_987_;
}
}
else
{
lean_del_object(v___x_985_);
lean_dec(v_head_982_);
lean_dec_ref(v_x_974_);
v___y_988_ = v___x_991_;
goto v___jp_987_;
}
v___jp_987_:
{
if (lean_obj_tag(v___y_988_) == 0)
{
lean_object* v_a_989_; 
v_a_989_ = lean_ctor_get(v___y_988_, 0);
lean_inc(v_a_989_);
lean_dec_ref(v___y_988_);
v_x_974_ = v_a_989_;
v_x_975_ = v_tail_983_;
goto _start;
}
else
{
lean_dec(v_tail_983_);
return v___y_988_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkExistsList_spec__0___boxed(lean_object* v_x_1023_, lean_object* v_x_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_){
_start:
{
lean_object* v_res_1030_; 
v_res_1030_ = l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkExistsList_spec__0(v_x_1023_, v_x_1024_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_);
lean_dec(v___y_1028_);
lean_dec_ref(v___y_1027_);
lean_dec(v___y_1026_);
lean_dec_ref(v___y_1025_);
return v_res_1030_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkExistsList(lean_object* v_args_1031_, lean_object* v_inner_1032_, lean_object* v_a_1033_, lean_object* v_a_1034_, lean_object* v_a_1035_, lean_object* v_a_1036_){
_start:
{
lean_object* v___x_1038_; lean_object* v___x_1039_; 
v___x_1038_ = l_List_reverse___redArg(v_args_1031_);
v___x_1039_ = l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkExistsList_spec__0(v_inner_1032_, v___x_1038_, v_a_1033_, v_a_1034_, v_a_1035_, v_a_1036_);
return v___x_1039_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkExistsList___boxed(lean_object* v_args_1040_, lean_object* v_inner_1041_, lean_object* v_a_1042_, lean_object* v_a_1043_, lean_object* v_a_1044_, lean_object* v_a_1045_, lean_object* v_a_1046_){
_start:
{
lean_object* v_res_1047_; 
v_res_1047_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkExistsList(v_args_1040_, v_inner_1041_, v_a_1042_, v_a_1043_, v_a_1044_, v_a_1045_);
lean_dec(v_a_1045_);
lean_dec_ref(v_a_1044_);
lean_dec(v_a_1043_);
lean_dec_ref(v_a_1042_);
return v_res_1047_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkOpList(lean_object* v_op_1048_, lean_object* v_empty_1049_, lean_object* v_x_1050_){
_start:
{
if (lean_obj_tag(v_x_1050_) == 0)
{
lean_dec_ref(v_op_1048_);
lean_inc_ref(v_empty_1049_);
return v_empty_1049_;
}
else
{
lean_object* v_tail_1051_; 
v_tail_1051_ = lean_ctor_get(v_x_1050_, 1);
if (lean_obj_tag(v_tail_1051_) == 0)
{
lean_object* v_head_1052_; 
lean_dec_ref(v_op_1048_);
v_head_1052_ = lean_ctor_get(v_x_1050_, 0);
lean_inc(v_head_1052_);
lean_dec_ref(v_x_1050_);
return v_head_1052_;
}
else
{
lean_object* v_head_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; 
lean_inc(v_tail_1051_);
v_head_1053_ = lean_ctor_get(v_x_1050_, 0);
lean_inc(v_head_1053_);
lean_dec_ref(v_x_1050_);
lean_inc_ref(v_op_1048_);
v___x_1054_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkOpList(v_op_1048_, v_empty_1049_, v_tail_1051_);
v___x_1055_ = l_Lean_mkAppB(v_op_1048_, v_head_1053_, v___x_1054_);
return v___x_1055_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkOpList___boxed(lean_object* v_op_1056_, lean_object* v_empty_1057_, lean_object* v_x_1058_){
_start:
{
lean_object* v_res_1059_; 
v_res_1059_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkOpList(v_op_1056_, v_empty_1057_, v_x_1058_);
lean_dec_ref(v_empty_1057_);
return v_res_1059_;
}
}
static lean_object* _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkAndList___closed__2(void){
_start:
{
lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; 
v___x_1063_ = lean_box(0);
v___x_1064_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkAndList___closed__1));
v___x_1065_ = l_Lean_mkConst(v___x_1064_, v___x_1063_);
return v___x_1065_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkAndList(lean_object* v_a_1066_){
_start:
{
lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; 
v___x_1067_ = lean_obj_once(&l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkExistsList_spec__0___closed__4, &l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkExistsList_spec__0___closed__4_once, _init_l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkExistsList_spec__0___closed__4);
v___x_1068_ = lean_obj_once(&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkAndList___closed__2, &l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkAndList___closed__2_once, _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkAndList___closed__2);
v___x_1069_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkOpList(v___x_1067_, v___x_1068_, v_a_1066_);
return v___x_1069_;
}
}
static lean_object* _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkOrList___closed__2(void){
_start:
{
lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; 
v___x_1073_ = lean_box(0);
v___x_1074_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkOrList___closed__1));
v___x_1075_ = l_Lean_mkConst(v___x_1074_, v___x_1073_);
return v___x_1075_;
}
}
static lean_object* _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkOrList___closed__5(void){
_start:
{
lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; 
v___x_1079_ = lean_box(0);
v___x_1080_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkOrList___closed__4));
v___x_1081_ = l_Lean_mkConst(v___x_1080_, v___x_1079_);
return v___x_1081_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkOrList(lean_object* v_a_1082_){
_start:
{
lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; 
v___x_1083_ = lean_obj_once(&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkOrList___closed__2, &l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkOrList___closed__2_once, _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkOrList___closed__2);
v___x_1084_ = lean_obj_once(&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkOrList___closed__5, &l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkOrList___closed__5_once, _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkOrList___closed__5);
v___x_1085_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkOpList(v___x_1083_, v___x_1084_, v_a_1082_);
return v___x_1085_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_List_init___redArg(lean_object* v_x_1086_){
_start:
{
if (lean_obj_tag(v_x_1086_) == 0)
{
return v_x_1086_;
}
else
{
lean_object* v_tail_1087_; 
v_tail_1087_ = lean_ctor_get(v_x_1086_, 1);
lean_inc(v_tail_1087_);
if (lean_obj_tag(v_tail_1087_) == 0)
{
lean_dec_ref(v_x_1086_);
return v_tail_1087_;
}
else
{
lean_object* v_head_1088_; lean_object* v___x_1090_; uint8_t v_isShared_1091_; uint8_t v_isSharedCheck_1096_; 
v_head_1088_ = lean_ctor_get(v_x_1086_, 0);
v_isSharedCheck_1096_ = !lean_is_exclusive(v_x_1086_);
if (v_isSharedCheck_1096_ == 0)
{
lean_object* v_unused_1097_; 
v_unused_1097_ = lean_ctor_get(v_x_1086_, 1);
lean_dec(v_unused_1097_);
v___x_1090_ = v_x_1086_;
v_isShared_1091_ = v_isSharedCheck_1096_;
goto v_resetjp_1089_;
}
else
{
lean_inc(v_head_1088_);
lean_dec(v_x_1086_);
v___x_1090_ = lean_box(0);
v_isShared_1091_ = v_isSharedCheck_1096_;
goto v_resetjp_1089_;
}
v_resetjp_1089_:
{
lean_object* v___x_1092_; lean_object* v___x_1094_; 
v___x_1092_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_List_init___redArg(v_tail_1087_);
if (v_isShared_1091_ == 0)
{
lean_ctor_set(v___x_1090_, 1, v___x_1092_);
v___x_1094_ = v___x_1090_;
goto v_reusejp_1093_;
}
else
{
lean_object* v_reuseFailAlloc_1095_; 
v_reuseFailAlloc_1095_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1095_, 0, v_head_1088_);
lean_ctor_set(v_reuseFailAlloc_1095_, 1, v___x_1092_);
v___x_1094_ = v_reuseFailAlloc_1095_;
goto v_reusejp_1093_;
}
v_reusejp_1093_:
{
return v___x_1094_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_List_init(lean_object* v_00_u03b1_1098_, lean_object* v_x_1099_){
_start:
{
lean_object* v___x_1100_; 
v___x_1100_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_List_init___redArg(v_x_1099_);
return v___x_1100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__4___redArg___lam__0(lean_object* v_k_1101_, lean_object* v_b_1102_, lean_object* v_c_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_){
_start:
{
lean_object* v___x_1109_; 
lean_inc(v___y_1107_);
lean_inc_ref(v___y_1106_);
lean_inc(v___y_1105_);
lean_inc_ref(v___y_1104_);
v___x_1109_ = lean_apply_7(v_k_1101_, v_b_1102_, v_c_1103_, v___y_1104_, v___y_1105_, v___y_1106_, v___y_1107_, lean_box(0));
return v___x_1109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__4___redArg___lam__0___boxed(lean_object* v_k_1110_, lean_object* v_b_1111_, lean_object* v_c_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_){
_start:
{
lean_object* v_res_1118_; 
v_res_1118_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__4___redArg___lam__0(v_k_1110_, v_b_1111_, v_c_1112_, v___y_1113_, v___y_1114_, v___y_1115_, v___y_1116_);
lean_dec(v___y_1116_);
lean_dec_ref(v___y_1115_);
lean_dec(v___y_1114_);
lean_dec_ref(v___y_1113_);
return v_res_1118_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__4___redArg(lean_object* v_type_1119_, lean_object* v_maxFVars_x3f_1120_, lean_object* v_k_1121_, uint8_t v_cleanupAnnotations_1122_, uint8_t v_whnfType_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_){
_start:
{
lean_object* v___f_1129_; lean_object* v___x_1130_; 
v___f_1129_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__4___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1129_, 0, v_k_1121_);
v___x_1130_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_1119_, v_maxFVars_x3f_1120_, v___f_1129_, v_cleanupAnnotations_1122_, v_whnfType_1123_, v___y_1124_, v___y_1125_, v___y_1126_, v___y_1127_);
if (lean_obj_tag(v___x_1130_) == 0)
{
lean_object* v_a_1131_; lean_object* v___x_1133_; uint8_t v_isShared_1134_; uint8_t v_isSharedCheck_1138_; 
v_a_1131_ = lean_ctor_get(v___x_1130_, 0);
v_isSharedCheck_1138_ = !lean_is_exclusive(v___x_1130_);
if (v_isSharedCheck_1138_ == 0)
{
v___x_1133_ = v___x_1130_;
v_isShared_1134_ = v_isSharedCheck_1138_;
goto v_resetjp_1132_;
}
else
{
lean_inc(v_a_1131_);
lean_dec(v___x_1130_);
v___x_1133_ = lean_box(0);
v_isShared_1134_ = v_isSharedCheck_1138_;
goto v_resetjp_1132_;
}
v_resetjp_1132_:
{
lean_object* v___x_1136_; 
if (v_isShared_1134_ == 0)
{
v___x_1136_ = v___x_1133_;
goto v_reusejp_1135_;
}
else
{
lean_object* v_reuseFailAlloc_1137_; 
v_reuseFailAlloc_1137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1137_, 0, v_a_1131_);
v___x_1136_ = v_reuseFailAlloc_1137_;
goto v_reusejp_1135_;
}
v_reusejp_1135_:
{
return v___x_1136_;
}
}
}
else
{
lean_object* v_a_1139_; lean_object* v___x_1141_; uint8_t v_isShared_1142_; uint8_t v_isSharedCheck_1146_; 
v_a_1139_ = lean_ctor_get(v___x_1130_, 0);
v_isSharedCheck_1146_ = !lean_is_exclusive(v___x_1130_);
if (v_isSharedCheck_1146_ == 0)
{
v___x_1141_ = v___x_1130_;
v_isShared_1142_ = v_isSharedCheck_1146_;
goto v_resetjp_1140_;
}
else
{
lean_inc(v_a_1139_);
lean_dec(v___x_1130_);
v___x_1141_ = lean_box(0);
v_isShared_1142_ = v_isSharedCheck_1146_;
goto v_resetjp_1140_;
}
v_resetjp_1140_:
{
lean_object* v___x_1144_; 
if (v_isShared_1142_ == 0)
{
v___x_1144_ = v___x_1141_;
goto v_reusejp_1143_;
}
else
{
lean_object* v_reuseFailAlloc_1145_; 
v_reuseFailAlloc_1145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1145_, 0, v_a_1139_);
v___x_1144_ = v_reuseFailAlloc_1145_;
goto v_reusejp_1143_;
}
v_reusejp_1143_:
{
return v___x_1144_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__4___redArg___boxed(lean_object* v_type_1147_, lean_object* v_maxFVars_x3f_1148_, lean_object* v_k_1149_, lean_object* v_cleanupAnnotations_1150_, lean_object* v_whnfType_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1157_; uint8_t v_whnfType_boxed_1158_; lean_object* v_res_1159_; 
v_cleanupAnnotations_boxed_1157_ = lean_unbox(v_cleanupAnnotations_1150_);
v_whnfType_boxed_1158_ = lean_unbox(v_whnfType_1151_);
v_res_1159_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__4___redArg(v_type_1147_, v_maxFVars_x3f_1148_, v_k_1149_, v_cleanupAnnotations_boxed_1157_, v_whnfType_boxed_1158_, v___y_1152_, v___y_1153_, v___y_1154_, v___y_1155_);
lean_dec(v___y_1155_);
lean_dec_ref(v___y_1154_);
lean_dec(v___y_1153_);
lean_dec_ref(v___y_1152_);
return v_res_1159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__4(lean_object* v_00_u03b1_1160_, lean_object* v_type_1161_, lean_object* v_maxFVars_x3f_1162_, lean_object* v_k_1163_, uint8_t v_cleanupAnnotations_1164_, uint8_t v_whnfType_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_){
_start:
{
lean_object* v___x_1171_; 
v___x_1171_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__4___redArg(v_type_1161_, v_maxFVars_x3f_1162_, v_k_1163_, v_cleanupAnnotations_1164_, v_whnfType_1165_, v___y_1166_, v___y_1167_, v___y_1168_, v___y_1169_);
return v___x_1171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__4___boxed(lean_object* v_00_u03b1_1172_, lean_object* v_type_1173_, lean_object* v_maxFVars_x3f_1174_, lean_object* v_k_1175_, lean_object* v_cleanupAnnotations_1176_, lean_object* v_whnfType_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1183_; uint8_t v_whnfType_boxed_1184_; lean_object* v_res_1185_; 
v_cleanupAnnotations_boxed_1183_ = lean_unbox(v_cleanupAnnotations_1176_);
v_whnfType_boxed_1184_ = lean_unbox(v_whnfType_1177_);
v_res_1185_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__4(v_00_u03b1_1172_, v_type_1173_, v_maxFVars_x3f_1174_, v_k_1175_, v_cleanupAnnotations_boxed_1183_, v_whnfType_boxed_1184_, v___y_1178_, v___y_1179_, v___y_1180_, v___y_1181_);
lean_dec(v___y_1181_);
lean_dec_ref(v___y_1180_);
lean_dec(v___y_1179_);
lean_dec_ref(v___y_1178_);
return v_res_1185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__5___redArg(lean_object* v_type_1186_, lean_object* v_k_1187_, uint8_t v_cleanupAnnotations_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_){
_start:
{
lean_object* v___f_1194_; uint8_t v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; 
v___f_1194_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__4___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1194_, 0, v_k_1187_);
v___x_1195_ = 0;
v___x_1196_ = lean_box(0);
v___x_1197_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_1195_, v___x_1196_, v_type_1186_, v___f_1194_, v_cleanupAnnotations_1188_, v___x_1195_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_);
if (lean_obj_tag(v___x_1197_) == 0)
{
lean_object* v_a_1198_; lean_object* v___x_1200_; uint8_t v_isShared_1201_; uint8_t v_isSharedCheck_1205_; 
v_a_1198_ = lean_ctor_get(v___x_1197_, 0);
v_isSharedCheck_1205_ = !lean_is_exclusive(v___x_1197_);
if (v_isSharedCheck_1205_ == 0)
{
v___x_1200_ = v___x_1197_;
v_isShared_1201_ = v_isSharedCheck_1205_;
goto v_resetjp_1199_;
}
else
{
lean_inc(v_a_1198_);
lean_dec(v___x_1197_);
v___x_1200_ = lean_box(0);
v_isShared_1201_ = v_isSharedCheck_1205_;
goto v_resetjp_1199_;
}
v_resetjp_1199_:
{
lean_object* v___x_1203_; 
if (v_isShared_1201_ == 0)
{
v___x_1203_ = v___x_1200_;
goto v_reusejp_1202_;
}
else
{
lean_object* v_reuseFailAlloc_1204_; 
v_reuseFailAlloc_1204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1204_, 0, v_a_1198_);
v___x_1203_ = v_reuseFailAlloc_1204_;
goto v_reusejp_1202_;
}
v_reusejp_1202_:
{
return v___x_1203_;
}
}
}
else
{
lean_object* v_a_1206_; lean_object* v___x_1208_; uint8_t v_isShared_1209_; uint8_t v_isSharedCheck_1213_; 
v_a_1206_ = lean_ctor_get(v___x_1197_, 0);
v_isSharedCheck_1213_ = !lean_is_exclusive(v___x_1197_);
if (v_isSharedCheck_1213_ == 0)
{
v___x_1208_ = v___x_1197_;
v_isShared_1209_ = v_isSharedCheck_1213_;
goto v_resetjp_1207_;
}
else
{
lean_inc(v_a_1206_);
lean_dec(v___x_1197_);
v___x_1208_ = lean_box(0);
v_isShared_1209_ = v_isSharedCheck_1213_;
goto v_resetjp_1207_;
}
v_resetjp_1207_:
{
lean_object* v___x_1211_; 
if (v_isShared_1209_ == 0)
{
v___x_1211_ = v___x_1208_;
goto v_reusejp_1210_;
}
else
{
lean_object* v_reuseFailAlloc_1212_; 
v_reuseFailAlloc_1212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1212_, 0, v_a_1206_);
v___x_1211_ = v_reuseFailAlloc_1212_;
goto v_reusejp_1210_;
}
v_reusejp_1210_:
{
return v___x_1211_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__5___redArg___boxed(lean_object* v_type_1214_, lean_object* v_k_1215_, lean_object* v_cleanupAnnotations_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1222_; lean_object* v_res_1223_; 
v_cleanupAnnotations_boxed_1222_ = lean_unbox(v_cleanupAnnotations_1216_);
v_res_1223_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__5___redArg(v_type_1214_, v_k_1215_, v_cleanupAnnotations_boxed_1222_, v___y_1217_, v___y_1218_, v___y_1219_, v___y_1220_);
lean_dec(v___y_1220_);
lean_dec_ref(v___y_1219_);
lean_dec(v___y_1218_);
lean_dec_ref(v___y_1217_);
return v_res_1223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__5(lean_object* v_00_u03b1_1224_, lean_object* v_type_1225_, lean_object* v_k_1226_, uint8_t v_cleanupAnnotations_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_){
_start:
{
lean_object* v___x_1233_; 
v___x_1233_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__5___redArg(v_type_1225_, v_k_1226_, v_cleanupAnnotations_1227_, v___y_1228_, v___y_1229_, v___y_1230_, v___y_1231_);
return v___x_1233_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__5___boxed(lean_object* v_00_u03b1_1234_, lean_object* v_type_1235_, lean_object* v_k_1236_, lean_object* v_cleanupAnnotations_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1243_; lean_object* v_res_1244_; 
v_cleanupAnnotations_boxed_1243_ = lean_unbox(v_cleanupAnnotations_1237_);
v_res_1244_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__5(v_00_u03b1_1234_, v_type_1235_, v_k_1236_, v_cleanupAnnotations_boxed_1243_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_);
lean_dec(v___y_1241_);
lean_dec_ref(v___y_1240_);
lean_dec(v___y_1239_);
lean_dec_ref(v___y_1238_);
return v_res_1244_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__0(lean_object* v_params_1245_, lean_object* v_fvars_1246_, lean_object* v_ty_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_){
_start:
{
lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; 
v___x_1253_ = lean_array_mk(v_params_1245_);
v___x_1254_ = l_Lean_Expr_replaceFVars(v_ty_1247_, v_fvars_1246_, v___x_1253_);
lean_dec_ref(v___x_1253_);
v___x_1255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1255_, 0, v___x_1254_);
return v___x_1255_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__0___boxed(lean_object* v_params_1256_, lean_object* v_fvars_1257_, lean_object* v_ty_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_){
_start:
{
lean_object* v_res_1264_; 
v_res_1264_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__0(v_params_1256_, v_fvars_1257_, v_ty_1258_, v___y_1259_, v___y_1260_, v___y_1261_, v___y_1262_);
lean_dec(v___y_1262_);
lean_dec_ref(v___y_1261_);
lean_dec(v___y_1260_);
lean_dec_ref(v___y_1259_);
lean_dec_ref(v_ty_1258_);
lean_dec_ref(v_fvars_1257_);
return v_res_1264_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__2(lean_object* v_x_1271_, lean_object* v_x_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_){
_start:
{
if (lean_obj_tag(v_x_1271_) == 0)
{
lean_object* v___x_1278_; lean_object* v___x_1279_; 
v___x_1278_ = l_List_reverse___redArg(v_x_1272_);
v___x_1279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1279_, 0, v___x_1278_);
return v___x_1279_;
}
else
{
lean_object* v_head_1280_; lean_object* v_tail_1281_; lean_object* v___x_1283_; uint8_t v_isShared_1284_; uint8_t v_isSharedCheck_1341_; 
v_head_1280_ = lean_ctor_get(v_x_1271_, 0);
v_tail_1281_ = lean_ctor_get(v_x_1271_, 1);
v_isSharedCheck_1341_ = !lean_is_exclusive(v_x_1271_);
if (v_isSharedCheck_1341_ == 0)
{
v___x_1283_ = v_x_1271_;
v_isShared_1284_ = v_isSharedCheck_1341_;
goto v_resetjp_1282_;
}
else
{
lean_inc(v_tail_1281_);
lean_inc(v_head_1280_);
lean_dec(v_x_1271_);
v___x_1283_ = lean_box(0);
v_isShared_1284_ = v_isSharedCheck_1341_;
goto v_resetjp_1282_;
}
v_resetjp_1282_:
{
lean_object* v_a_1286_; lean_object* v___y_1292_; lean_object* v_fst_1302_; lean_object* v_snd_1303_; lean_object* v___x_1305_; uint8_t v_isShared_1306_; uint8_t v_isSharedCheck_1340_; 
v_fst_1302_ = lean_ctor_get(v_head_1280_, 0);
v_snd_1303_ = lean_ctor_get(v_head_1280_, 1);
v_isSharedCheck_1340_ = !lean_is_exclusive(v_head_1280_);
if (v_isSharedCheck_1340_ == 0)
{
v___x_1305_ = v_head_1280_;
v_isShared_1306_ = v_isSharedCheck_1340_;
goto v_resetjp_1304_;
}
else
{
lean_inc(v_snd_1303_);
lean_inc(v_fst_1302_);
lean_dec(v_head_1280_);
v___x_1305_ = lean_box(0);
v_isShared_1306_ = v_isSharedCheck_1340_;
goto v_resetjp_1304_;
}
v___jp_1285_:
{
lean_object* v___x_1288_; 
if (v_isShared_1284_ == 0)
{
lean_ctor_set(v___x_1283_, 1, v_x_1272_);
lean_ctor_set(v___x_1283_, 0, v_a_1286_);
v___x_1288_ = v___x_1283_;
goto v_reusejp_1287_;
}
else
{
lean_object* v_reuseFailAlloc_1290_; 
v_reuseFailAlloc_1290_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1290_, 0, v_a_1286_);
lean_ctor_set(v_reuseFailAlloc_1290_, 1, v_x_1272_);
v___x_1288_ = v_reuseFailAlloc_1290_;
goto v_reusejp_1287_;
}
v_reusejp_1287_:
{
v_x_1271_ = v_tail_1281_;
v_x_1272_ = v___x_1288_;
goto _start;
}
}
v___jp_1291_:
{
if (lean_obj_tag(v___y_1292_) == 0)
{
lean_object* v_a_1293_; 
v_a_1293_ = lean_ctor_get(v___y_1292_, 0);
lean_inc(v_a_1293_);
lean_dec_ref(v___y_1292_);
v_a_1286_ = v_a_1293_;
goto v___jp_1285_;
}
else
{
lean_object* v_a_1294_; lean_object* v___x_1296_; uint8_t v_isShared_1297_; uint8_t v_isSharedCheck_1301_; 
lean_del_object(v___x_1283_);
lean_dec(v_tail_1281_);
lean_dec(v_x_1272_);
v_a_1294_ = lean_ctor_get(v___y_1292_, 0);
v_isSharedCheck_1301_ = !lean_is_exclusive(v___y_1292_);
if (v_isSharedCheck_1301_ == 0)
{
v___x_1296_ = v___y_1292_;
v_isShared_1297_ = v_isSharedCheck_1301_;
goto v_resetjp_1295_;
}
else
{
lean_inc(v_a_1294_);
lean_dec(v___y_1292_);
v___x_1296_ = lean_box(0);
v_isShared_1297_ = v_isSharedCheck_1301_;
goto v_resetjp_1295_;
}
v_resetjp_1295_:
{
lean_object* v___x_1299_; 
if (v_isShared_1297_ == 0)
{
v___x_1299_ = v___x_1296_;
goto v_reusejp_1298_;
}
else
{
lean_object* v_reuseFailAlloc_1300_; 
v_reuseFailAlloc_1300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1300_, 0, v_a_1294_);
v___x_1299_ = v_reuseFailAlloc_1300_;
goto v_reusejp_1298_;
}
v_reusejp_1298_:
{
return v___x_1299_;
}
}
}
}
v_resetjp_1304_:
{
lean_object* v___x_1307_; lean_object* v___x_1308_; 
v___x_1307_ = l_Lean_Expr_fvarId_x21(v_fst_1302_);
v___x_1308_ = l_Lean_FVarId_getType___redArg(v___x_1307_, v___y_1273_, v___y_1275_, v___y_1276_);
if (lean_obj_tag(v___x_1308_) == 0)
{
lean_object* v_a_1309_; lean_object* v___x_1310_; 
v_a_1309_ = lean_ctor_get(v___x_1308_, 0);
lean_inc(v_a_1309_);
lean_dec_ref(v___x_1308_);
lean_inc(v___y_1276_);
lean_inc_ref(v___y_1275_);
lean_inc(v___y_1274_);
lean_inc_ref(v___y_1273_);
lean_inc(v_snd_1303_);
v___x_1310_ = lean_infer_type(v_snd_1303_, v___y_1273_, v___y_1274_, v___y_1275_, v___y_1276_);
if (lean_obj_tag(v___x_1310_) == 0)
{
lean_object* v_a_1311_; lean_object* v___x_1312_; 
v_a_1311_ = lean_ctor_get(v___x_1310_, 0);
lean_inc(v_a_1311_);
lean_dec_ref(v___x_1310_);
lean_inc(v___y_1276_);
lean_inc_ref(v___y_1275_);
lean_inc(v___y_1274_);
lean_inc_ref(v___y_1273_);
lean_inc(v_a_1309_);
v___x_1312_ = lean_infer_type(v_a_1309_, v___y_1273_, v___y_1274_, v___y_1275_, v___y_1276_);
if (lean_obj_tag(v___x_1312_) == 0)
{
lean_object* v_a_1313_; lean_object* v___x_1314_; 
v_a_1313_ = lean_ctor_get(v___x_1312_, 0);
lean_inc(v_a_1313_);
lean_dec_ref(v___x_1312_);
lean_inc(v_a_1311_);
lean_inc(v_a_1309_);
v___x_1314_ = l_Lean_Meta_isExprDefEq(v_a_1309_, v_a_1311_, v___y_1273_, v___y_1274_, v___y_1275_, v___y_1276_);
if (lean_obj_tag(v___x_1314_) == 0)
{
lean_object* v_a_1315_; lean_object* v___x_1316_; uint8_t v___x_1317_; 
v_a_1315_ = lean_ctor_get(v___x_1314_, 0);
lean_inc(v_a_1315_);
lean_dec_ref(v___x_1314_);
v___x_1316_ = l_Lean_Expr_sortLevel_x21(v_a_1313_);
lean_dec(v_a_1313_);
v___x_1317_ = lean_unbox(v_a_1315_);
lean_dec(v_a_1315_);
if (v___x_1317_ == 0)
{
lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1321_; 
v___x_1318_ = ((lean_object*)(l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__2___closed__1));
v___x_1319_ = lean_box(0);
if (v_isShared_1306_ == 0)
{
lean_ctor_set_tag(v___x_1305_, 1);
lean_ctor_set(v___x_1305_, 1, v___x_1319_);
lean_ctor_set(v___x_1305_, 0, v___x_1316_);
v___x_1321_ = v___x_1305_;
goto v_reusejp_1320_;
}
else
{
lean_object* v_reuseFailAlloc_1324_; 
v_reuseFailAlloc_1324_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1324_, 0, v___x_1316_);
lean_ctor_set(v_reuseFailAlloc_1324_, 1, v___x_1319_);
v___x_1321_ = v_reuseFailAlloc_1324_;
goto v_reusejp_1320_;
}
v_reusejp_1320_:
{
lean_object* v___x_1322_; lean_object* v___x_1323_; 
v___x_1322_ = l_Lean_Expr_const___override(v___x_1318_, v___x_1321_);
v___x_1323_ = l_Lean_mkApp4(v___x_1322_, v_a_1309_, v_fst_1302_, v_a_1311_, v_snd_1303_);
v_a_1286_ = v___x_1323_;
goto v___jp_1285_;
}
}
else
{
lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1328_; 
lean_dec(v_a_1311_);
v___x_1325_ = ((lean_object*)(l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__2___closed__3));
v___x_1326_ = lean_box(0);
if (v_isShared_1306_ == 0)
{
lean_ctor_set_tag(v___x_1305_, 1);
lean_ctor_set(v___x_1305_, 1, v___x_1326_);
lean_ctor_set(v___x_1305_, 0, v___x_1316_);
v___x_1328_ = v___x_1305_;
goto v_reusejp_1327_;
}
else
{
lean_object* v_reuseFailAlloc_1331_; 
v_reuseFailAlloc_1331_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1331_, 0, v___x_1316_);
lean_ctor_set(v_reuseFailAlloc_1331_, 1, v___x_1326_);
v___x_1328_ = v_reuseFailAlloc_1331_;
goto v_reusejp_1327_;
}
v_reusejp_1327_:
{
lean_object* v___x_1329_; lean_object* v___x_1330_; 
v___x_1329_ = l_Lean_Expr_const___override(v___x_1325_, v___x_1328_);
v___x_1330_ = l_Lean_mkApp3(v___x_1329_, v_a_1309_, v_fst_1302_, v_snd_1303_);
v_a_1286_ = v___x_1330_;
goto v___jp_1285_;
}
}
}
else
{
lean_object* v_a_1332_; lean_object* v___x_1334_; uint8_t v_isShared_1335_; uint8_t v_isSharedCheck_1339_; 
lean_dec(v_a_1313_);
lean_dec(v_a_1311_);
lean_dec(v_a_1309_);
lean_del_object(v___x_1305_);
lean_dec(v_snd_1303_);
lean_dec(v_fst_1302_);
lean_del_object(v___x_1283_);
lean_dec(v_tail_1281_);
lean_dec(v_x_1272_);
v_a_1332_ = lean_ctor_get(v___x_1314_, 0);
v_isSharedCheck_1339_ = !lean_is_exclusive(v___x_1314_);
if (v_isSharedCheck_1339_ == 0)
{
v___x_1334_ = v___x_1314_;
v_isShared_1335_ = v_isSharedCheck_1339_;
goto v_resetjp_1333_;
}
else
{
lean_inc(v_a_1332_);
lean_dec(v___x_1314_);
v___x_1334_ = lean_box(0);
v_isShared_1335_ = v_isSharedCheck_1339_;
goto v_resetjp_1333_;
}
v_resetjp_1333_:
{
lean_object* v___x_1337_; 
if (v_isShared_1335_ == 0)
{
v___x_1337_ = v___x_1334_;
goto v_reusejp_1336_;
}
else
{
lean_object* v_reuseFailAlloc_1338_; 
v_reuseFailAlloc_1338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1338_, 0, v_a_1332_);
v___x_1337_ = v_reuseFailAlloc_1338_;
goto v_reusejp_1336_;
}
v_reusejp_1336_:
{
return v___x_1337_;
}
}
}
}
else
{
lean_dec(v_a_1311_);
lean_dec(v_a_1309_);
lean_del_object(v___x_1305_);
lean_dec(v_snd_1303_);
lean_dec(v_fst_1302_);
v___y_1292_ = v___x_1312_;
goto v___jp_1291_;
}
}
else
{
lean_dec(v_a_1309_);
lean_del_object(v___x_1305_);
lean_dec(v_snd_1303_);
lean_dec(v_fst_1302_);
v___y_1292_ = v___x_1310_;
goto v___jp_1291_;
}
}
else
{
lean_del_object(v___x_1305_);
lean_dec(v_snd_1303_);
lean_dec(v_fst_1302_);
v___y_1292_ = v___x_1308_;
goto v___jp_1291_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__2___boxed(lean_object* v_x_1342_, lean_object* v_x_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_){
_start:
{
lean_object* v_res_1349_; 
v_res_1349_ = l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__2(v_x_1342_, v_x_1343_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_);
lean_dec(v___y_1347_);
lean_dec_ref(v___y_1346_);
lean_dec(v___y_1345_);
lean_dec_ref(v___y_1344_);
return v_res_1349_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__3(lean_object* v_a_1350_, lean_object* v_a_1351_){
_start:
{
if (lean_obj_tag(v_a_1350_) == 0)
{
lean_object* v___x_1352_; 
v___x_1352_ = lean_array_to_list(v_a_1351_);
return v___x_1352_;
}
else
{
lean_object* v_head_1353_; 
v_head_1353_ = lean_ctor_get(v_a_1350_, 0);
if (lean_obj_tag(v_head_1353_) == 0)
{
lean_object* v_tail_1354_; 
v_tail_1354_ = lean_ctor_get(v_a_1350_, 1);
lean_inc(v_tail_1354_);
lean_dec_ref(v_a_1350_);
v_a_1350_ = v_tail_1354_;
goto _start;
}
else
{
lean_object* v_tail_1356_; lean_object* v_val_1357_; lean_object* v___x_1358_; 
lean_inc_ref(v_head_1353_);
v_tail_1356_ = lean_ctor_get(v_a_1350_, 1);
lean_inc(v_tail_1356_);
lean_dec_ref(v_a_1350_);
v_val_1357_ = lean_ctor_get(v_head_1353_, 0);
lean_inc(v_val_1357_);
lean_dec_ref(v_head_1353_);
v___x_1358_ = lean_array_push(v_a_1351_, v_val_1357_);
v_a_1350_ = v_tail_1356_;
v_a_1351_ = v___x_1358_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__1(lean_object* v_a_1360_, lean_object* v_a_1361_){
_start:
{
if (lean_obj_tag(v_a_1360_) == 0)
{
lean_object* v___x_1362_; 
v___x_1362_ = l_List_reverse___redArg(v_a_1361_);
return v___x_1362_;
}
else
{
lean_object* v_head_1363_; lean_object* v_tail_1364_; lean_object* v___x_1366_; uint8_t v_isShared_1367_; uint8_t v_isSharedCheck_1377_; 
v_head_1363_ = lean_ctor_get(v_a_1360_, 0);
v_tail_1364_ = lean_ctor_get(v_a_1360_, 1);
v_isSharedCheck_1377_ = !lean_is_exclusive(v_a_1360_);
if (v_isSharedCheck_1377_ == 0)
{
v___x_1366_ = v_a_1360_;
v_isShared_1367_ = v_isSharedCheck_1377_;
goto v_resetjp_1365_;
}
else
{
lean_inc(v_tail_1364_);
lean_inc(v_head_1363_);
lean_dec(v_a_1360_);
v___x_1366_ = lean_box(0);
v_isShared_1367_ = v_isSharedCheck_1377_;
goto v_resetjp_1365_;
}
v_resetjp_1365_:
{
uint8_t v___y_1369_; 
if (lean_obj_tag(v_head_1363_) == 0)
{
uint8_t v___x_1375_; 
v___x_1375_ = 0;
v___y_1369_ = v___x_1375_;
goto v___jp_1368_;
}
else
{
uint8_t v___x_1376_; 
lean_dec_ref(v_head_1363_);
v___x_1376_ = 1;
v___y_1369_ = v___x_1376_;
goto v___jp_1368_;
}
v___jp_1368_:
{
lean_object* v___x_1370_; lean_object* v___x_1372_; 
v___x_1370_ = lean_box(v___y_1369_);
if (v_isShared_1367_ == 0)
{
lean_ctor_set(v___x_1366_, 1, v_a_1361_);
lean_ctor_set(v___x_1366_, 0, v___x_1370_);
v___x_1372_ = v___x_1366_;
goto v_reusejp_1371_;
}
else
{
lean_object* v_reuseFailAlloc_1374_; 
v_reuseFailAlloc_1374_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1374_, 0, v___x_1370_);
lean_ctor_set(v_reuseFailAlloc_1374_, 1, v_a_1361_);
v___x_1372_ = v_reuseFailAlloc_1374_;
goto v_reusejp_1371_;
}
v_reusejp_1371_:
{
v_a_1360_ = v_tail_1364_;
v_a_1361_ = v___x_1372_;
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
lean_object* v___x_1378_; lean_object* v_dummy_1379_; 
v___x_1378_ = lean_box(0);
v_dummy_1379_ = l_Lean_Expr_sort___override(v___x_1378_);
return v_dummy_1379_;
}
}
static lean_object* _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__1___closed__3(void){
_start:
{
lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; 
v___x_1384_ = lean_box(0);
v___x_1385_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkAndList___closed__1));
v___x_1386_ = l_Lean_mkConst(v___x_1385_, v___x_1384_);
return v___x_1386_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__1(lean_object* v___x_1387_, lean_object* v_idxs_1388_, lean_object* v___x_1389_, lean_object* v_fvars_1390_, lean_object* v_ty_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_){
_start:
{
lean_object* v___x_1397_; lean_object* v_dummy_1398_; lean_object* v_nargs_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v_fst_1409_; lean_object* v_snd_1410_; lean_object* v___x_1412_; uint8_t v_isShared_1413_; uint8_t v_isSharedCheck_1511_; 
v___x_1397_ = lean_box(0);
v_dummy_1398_ = lean_obj_once(&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__1___closed__0, &l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__1___closed__0_once, _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__1___closed__0);
v_nargs_1399_ = l_Lean_Expr_getAppNumArgs(v_ty_1391_);
lean_inc(v_nargs_1399_);
v___x_1400_ = lean_mk_array(v_nargs_1399_, v_dummy_1398_);
v___x_1401_ = lean_unsigned_to_nat(1u);
v___x_1402_ = lean_nat_sub(v_nargs_1399_, v___x_1401_);
lean_dec(v_nargs_1399_);
v___x_1403_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_ty_1391_, v___x_1400_, v___x_1402_);
v___x_1404_ = lean_array_to_list(v___x_1403_);
v___x_1405_ = l_List_drop___redArg(v___x_1387_, v___x_1404_);
lean_dec(v___x_1404_);
v___x_1406_ = lean_array_to_list(v_fvars_1390_);
v___x_1407_ = l_List_zipWith___at___00List_zip_spec__0(lean_box(0), lean_box(0), v_idxs_1388_, v___x_1405_);
v___x_1408_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_compactRelation(v___x_1406_, v___x_1407_);
v_fst_1409_ = lean_ctor_get(v___x_1408_, 0);
v_snd_1410_ = lean_ctor_get(v___x_1408_, 1);
v_isSharedCheck_1511_ = !lean_is_exclusive(v___x_1408_);
if (v_isSharedCheck_1511_ == 0)
{
v___x_1412_ = v___x_1408_;
v_isShared_1413_ = v_isSharedCheck_1511_;
goto v_resetjp_1411_;
}
else
{
lean_inc(v_snd_1410_);
lean_inc(v_fst_1409_);
lean_dec(v___x_1408_);
v___x_1412_ = lean_box(0);
v_isShared_1413_ = v_isSharedCheck_1511_;
goto v_resetjp_1411_;
}
v_resetjp_1411_:
{
lean_object* v_fst_1415_; lean_object* v_snd_1416_; lean_object* v_fst_1424_; lean_object* v_snd_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; 
v_fst_1424_ = lean_ctor_get(v_snd_1410_, 0);
lean_inc(v_fst_1424_);
v_snd_1425_ = lean_ctor_get(v_snd_1410_, 1);
lean_inc(v_snd_1425_);
lean_dec(v_snd_1410_);
v___x_1426_ = lean_box(0);
v___x_1427_ = l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__2(v_fst_1424_, v___x_1426_, v___y_1392_, v___y_1393_, v___y_1394_, v___y_1395_);
if (lean_obj_tag(v___x_1427_) == 0)
{
lean_object* v_a_1428_; lean_object* v_bs_x27_1430_; lean_object* v___y_1431_; lean_object* v___y_1432_; lean_object* v___y_1433_; lean_object* v___y_1434_; lean_object* v___x_1449_; lean_object* v___x_1450_; 
v_a_1428_ = lean_ctor_get(v___x_1427_, 0);
lean_inc(v_a_1428_);
lean_dec_ref(v___x_1427_);
v___x_1449_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__1___closed__1));
lean_inc(v_fst_1409_);
v___x_1450_ = l_List_filterMapTR_go___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__3(v_fst_1409_, v___x_1449_);
if (lean_obj_tag(v___x_1450_) == 0)
{
if (lean_obj_tag(v_a_1428_) == 0)
{
lean_object* v___x_1451_; lean_object* v___x_1452_; 
lean_dec(v_snd_1425_);
v___x_1451_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__1___closed__2));
v___x_1452_ = lean_obj_once(&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__1___closed__3, &l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__1___closed__3_once, _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__1___closed__3);
v_fst_1415_ = v___x_1451_;
v_snd_1416_ = v___x_1452_;
goto v___jp_1414_;
}
else
{
v_bs_x27_1430_ = v___x_1450_;
v___y_1431_ = v___y_1392_;
v___y_1432_ = v___y_1393_;
v___y_1433_ = v___y_1394_;
v___y_1434_ = v___y_1395_;
goto v___jp_1429_;
}
}
else
{
if (lean_obj_tag(v_a_1428_) == 0)
{
lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; 
v___x_1453_ = l_List_getLast_x21___redArg(v___x_1389_, v___x_1450_);
v___x_1454_ = l_Lean_Expr_fvarId_x21(v___x_1453_);
lean_dec(v___x_1453_);
v___x_1455_ = l_Lean_FVarId_getType___redArg(v___x_1454_, v___y_1392_, v___y_1394_, v___y_1395_);
if (lean_obj_tag(v___x_1455_) == 0)
{
lean_object* v_a_1456_; lean_object* v___x_1457_; 
v_a_1456_ = lean_ctor_get(v___x_1455_, 0);
lean_inc_n(v_a_1456_, 2);
lean_dec_ref(v___x_1455_);
lean_inc(v___y_1395_);
lean_inc_ref(v___y_1394_);
lean_inc(v___y_1393_);
lean_inc_ref(v___y_1392_);
v___x_1457_ = lean_infer_type(v_a_1456_, v___y_1392_, v___y_1393_, v___y_1394_, v___y_1395_);
if (lean_obj_tag(v___x_1457_) == 0)
{
lean_object* v_a_1458_; lean_object* v___x_1459_; uint8_t v___x_1460_; 
v_a_1458_ = lean_ctor_get(v___x_1457_, 0);
lean_inc(v_a_1458_);
lean_dec_ref(v___x_1457_);
v___x_1459_ = l_Lean_Expr_sortLevel_x21(v_a_1458_);
lean_dec(v_a_1458_);
v___x_1460_ = lean_level_eq(v___x_1459_, v___x_1397_);
lean_dec(v___x_1459_);
if (v___x_1460_ == 0)
{
lean_object* v___x_1461_; lean_object* v___x_1462_; 
lean_dec(v_a_1456_);
v___x_1461_ = lean_obj_once(&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__1___closed__3, &l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__1___closed__3_once, _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__1___closed__3);
v___x_1462_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkExistsList(v___x_1450_, v___x_1461_, v___y_1392_, v___y_1393_, v___y_1394_, v___y_1395_);
if (lean_obj_tag(v___x_1462_) == 0)
{
lean_object* v_a_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; 
v_a_1463_ = lean_ctor_get(v___x_1462_, 0);
lean_inc(v_a_1463_);
lean_dec_ref(v___x_1462_);
v___x_1464_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__1___closed__2));
v___x_1465_ = lean_apply_1(v_snd_1425_, v_a_1463_);
v_fst_1415_ = v___x_1464_;
v_snd_1416_ = v___x_1465_;
goto v___jp_1414_;
}
else
{
lean_object* v_a_1466_; lean_object* v___x_1468_; uint8_t v_isShared_1469_; uint8_t v_isSharedCheck_1473_; 
lean_dec(v_snd_1425_);
lean_del_object(v___x_1412_);
lean_dec(v_fst_1409_);
v_a_1466_ = lean_ctor_get(v___x_1462_, 0);
v_isSharedCheck_1473_ = !lean_is_exclusive(v___x_1462_);
if (v_isSharedCheck_1473_ == 0)
{
v___x_1468_ = v___x_1462_;
v_isShared_1469_ = v_isSharedCheck_1473_;
goto v_resetjp_1467_;
}
else
{
lean_inc(v_a_1466_);
lean_dec(v___x_1462_);
v___x_1468_ = lean_box(0);
v_isShared_1469_ = v_isSharedCheck_1473_;
goto v_resetjp_1467_;
}
v_resetjp_1467_:
{
lean_object* v___x_1471_; 
if (v_isShared_1469_ == 0)
{
v___x_1471_ = v___x_1468_;
goto v_reusejp_1470_;
}
else
{
lean_object* v_reuseFailAlloc_1472_; 
v_reuseFailAlloc_1472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1472_, 0, v_a_1466_);
v___x_1471_ = v_reuseFailAlloc_1472_;
goto v_reusejp_1470_;
}
v_reusejp_1470_:
{
return v___x_1471_;
}
}
}
}
else
{
lean_object* v___x_1474_; lean_object* v___x_1475_; 
v___x_1474_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_List_init___redArg(v___x_1450_);
v___x_1475_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkExistsList(v___x_1474_, v_a_1456_, v___y_1392_, v___y_1393_, v___y_1394_, v___y_1395_);
if (lean_obj_tag(v___x_1475_) == 0)
{
lean_object* v_a_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; 
v_a_1476_ = lean_ctor_get(v___x_1475_, 0);
lean_inc(v_a_1476_);
lean_dec_ref(v___x_1475_);
v___x_1477_ = lean_box(0);
v___x_1478_ = lean_apply_1(v_snd_1425_, v_a_1476_);
v_fst_1415_ = v___x_1477_;
v_snd_1416_ = v___x_1478_;
goto v___jp_1414_;
}
else
{
lean_object* v_a_1479_; lean_object* v___x_1481_; uint8_t v_isShared_1482_; uint8_t v_isSharedCheck_1486_; 
lean_dec(v_snd_1425_);
lean_del_object(v___x_1412_);
lean_dec(v_fst_1409_);
v_a_1479_ = lean_ctor_get(v___x_1475_, 0);
v_isSharedCheck_1486_ = !lean_is_exclusive(v___x_1475_);
if (v_isSharedCheck_1486_ == 0)
{
v___x_1481_ = v___x_1475_;
v_isShared_1482_ = v_isSharedCheck_1486_;
goto v_resetjp_1480_;
}
else
{
lean_inc(v_a_1479_);
lean_dec(v___x_1475_);
v___x_1481_ = lean_box(0);
v_isShared_1482_ = v_isSharedCheck_1486_;
goto v_resetjp_1480_;
}
v_resetjp_1480_:
{
lean_object* v___x_1484_; 
if (v_isShared_1482_ == 0)
{
v___x_1484_ = v___x_1481_;
goto v_reusejp_1483_;
}
else
{
lean_object* v_reuseFailAlloc_1485_; 
v_reuseFailAlloc_1485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1485_, 0, v_a_1479_);
v___x_1484_ = v_reuseFailAlloc_1485_;
goto v_reusejp_1483_;
}
v_reusejp_1483_:
{
return v___x_1484_;
}
}
}
}
}
else
{
lean_object* v_a_1487_; lean_object* v___x_1489_; uint8_t v_isShared_1490_; uint8_t v_isSharedCheck_1494_; 
lean_dec(v_a_1456_);
lean_dec(v___x_1450_);
lean_dec(v_snd_1425_);
lean_del_object(v___x_1412_);
lean_dec(v_fst_1409_);
v_a_1487_ = lean_ctor_get(v___x_1457_, 0);
v_isSharedCheck_1494_ = !lean_is_exclusive(v___x_1457_);
if (v_isSharedCheck_1494_ == 0)
{
v___x_1489_ = v___x_1457_;
v_isShared_1490_ = v_isSharedCheck_1494_;
goto v_resetjp_1488_;
}
else
{
lean_inc(v_a_1487_);
lean_dec(v___x_1457_);
v___x_1489_ = lean_box(0);
v_isShared_1490_ = v_isSharedCheck_1494_;
goto v_resetjp_1488_;
}
v_resetjp_1488_:
{
lean_object* v___x_1492_; 
if (v_isShared_1490_ == 0)
{
v___x_1492_ = v___x_1489_;
goto v_reusejp_1491_;
}
else
{
lean_object* v_reuseFailAlloc_1493_; 
v_reuseFailAlloc_1493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1493_, 0, v_a_1487_);
v___x_1492_ = v_reuseFailAlloc_1493_;
goto v_reusejp_1491_;
}
v_reusejp_1491_:
{
return v___x_1492_;
}
}
}
}
else
{
lean_object* v_a_1495_; lean_object* v___x_1497_; uint8_t v_isShared_1498_; uint8_t v_isSharedCheck_1502_; 
lean_dec(v___x_1450_);
lean_dec(v_snd_1425_);
lean_del_object(v___x_1412_);
lean_dec(v_fst_1409_);
v_a_1495_ = lean_ctor_get(v___x_1455_, 0);
v_isSharedCheck_1502_ = !lean_is_exclusive(v___x_1455_);
if (v_isSharedCheck_1502_ == 0)
{
v___x_1497_ = v___x_1455_;
v_isShared_1498_ = v_isSharedCheck_1502_;
goto v_resetjp_1496_;
}
else
{
lean_inc(v_a_1495_);
lean_dec(v___x_1455_);
v___x_1497_ = lean_box(0);
v_isShared_1498_ = v_isSharedCheck_1502_;
goto v_resetjp_1496_;
}
v_resetjp_1496_:
{
lean_object* v___x_1500_; 
if (v_isShared_1498_ == 0)
{
v___x_1500_ = v___x_1497_;
goto v_reusejp_1499_;
}
else
{
lean_object* v_reuseFailAlloc_1501_; 
v_reuseFailAlloc_1501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1501_, 0, v_a_1495_);
v___x_1500_ = v_reuseFailAlloc_1501_;
goto v_reusejp_1499_;
}
v_reusejp_1499_:
{
return v___x_1500_;
}
}
}
}
else
{
v_bs_x27_1430_ = v___x_1450_;
v___y_1431_ = v___y_1392_;
v___y_1432_ = v___y_1393_;
v___y_1433_ = v___y_1394_;
v___y_1434_ = v___y_1395_;
goto v___jp_1429_;
}
}
v___jp_1429_:
{
lean_object* v___x_1435_; lean_object* v___x_1436_; 
lean_inc(v_a_1428_);
v___x_1435_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkAndList(v_a_1428_);
v___x_1436_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkExistsList(v_bs_x27_1430_, v___x_1435_, v___y_1431_, v___y_1432_, v___y_1433_, v___y_1434_);
if (lean_obj_tag(v___x_1436_) == 0)
{
lean_object* v_a_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; 
v_a_1437_ = lean_ctor_get(v___x_1436_, 0);
lean_inc(v_a_1437_);
lean_dec_ref(v___x_1436_);
v___x_1438_ = l_List_lengthTR___redArg(v_a_1428_);
lean_dec(v_a_1428_);
v___x_1439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1439_, 0, v___x_1438_);
v___x_1440_ = lean_apply_1(v_snd_1425_, v_a_1437_);
v_fst_1415_ = v___x_1439_;
v_snd_1416_ = v___x_1440_;
goto v___jp_1414_;
}
else
{
lean_object* v_a_1441_; lean_object* v___x_1443_; uint8_t v_isShared_1444_; uint8_t v_isSharedCheck_1448_; 
lean_dec(v_a_1428_);
lean_dec(v_snd_1425_);
lean_del_object(v___x_1412_);
lean_dec(v_fst_1409_);
v_a_1441_ = lean_ctor_get(v___x_1436_, 0);
v_isSharedCheck_1448_ = !lean_is_exclusive(v___x_1436_);
if (v_isSharedCheck_1448_ == 0)
{
v___x_1443_ = v___x_1436_;
v_isShared_1444_ = v_isSharedCheck_1448_;
goto v_resetjp_1442_;
}
else
{
lean_inc(v_a_1441_);
lean_dec(v___x_1436_);
v___x_1443_ = lean_box(0);
v_isShared_1444_ = v_isSharedCheck_1448_;
goto v_resetjp_1442_;
}
v_resetjp_1442_:
{
lean_object* v___x_1446_; 
if (v_isShared_1444_ == 0)
{
v___x_1446_ = v___x_1443_;
goto v_reusejp_1445_;
}
else
{
lean_object* v_reuseFailAlloc_1447_; 
v_reuseFailAlloc_1447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1447_, 0, v_a_1441_);
v___x_1446_ = v_reuseFailAlloc_1447_;
goto v_reusejp_1445_;
}
v_reusejp_1445_:
{
return v___x_1446_;
}
}
}
}
}
else
{
lean_object* v_a_1503_; lean_object* v___x_1505_; uint8_t v_isShared_1506_; uint8_t v_isSharedCheck_1510_; 
lean_dec(v_snd_1425_);
lean_del_object(v___x_1412_);
lean_dec(v_fst_1409_);
v_a_1503_ = lean_ctor_get(v___x_1427_, 0);
v_isSharedCheck_1510_ = !lean_is_exclusive(v___x_1427_);
if (v_isSharedCheck_1510_ == 0)
{
v___x_1505_ = v___x_1427_;
v_isShared_1506_ = v_isSharedCheck_1510_;
goto v_resetjp_1504_;
}
else
{
lean_inc(v_a_1503_);
lean_dec(v___x_1427_);
v___x_1505_ = lean_box(0);
v_isShared_1506_ = v_isSharedCheck_1510_;
goto v_resetjp_1504_;
}
v_resetjp_1504_:
{
lean_object* v___x_1508_; 
if (v_isShared_1506_ == 0)
{
v___x_1508_ = v___x_1505_;
goto v_reusejp_1507_;
}
else
{
lean_object* v_reuseFailAlloc_1509_; 
v_reuseFailAlloc_1509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1509_, 0, v_a_1503_);
v___x_1508_ = v_reuseFailAlloc_1509_;
goto v_reusejp_1507_;
}
v_reusejp_1507_:
{
return v___x_1508_;
}
}
}
v___jp_1414_:
{
lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1421_; 
v___x_1417_ = lean_box(0);
v___x_1418_ = l_List_mapTR_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__1(v_fst_1409_, v___x_1417_);
v___x_1419_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1419_, 0, v___x_1418_);
lean_ctor_set(v___x_1419_, 1, v_fst_1415_);
if (v_isShared_1413_ == 0)
{
lean_ctor_set(v___x_1412_, 1, v_snd_1416_);
lean_ctor_set(v___x_1412_, 0, v___x_1419_);
v___x_1421_ = v___x_1412_;
goto v_reusejp_1420_;
}
else
{
lean_object* v_reuseFailAlloc_1423_; 
v_reuseFailAlloc_1423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1423_, 0, v___x_1419_);
lean_ctor_set(v_reuseFailAlloc_1423_, 1, v_snd_1416_);
v___x_1421_ = v_reuseFailAlloc_1423_;
goto v_reusejp_1420_;
}
v_reusejp_1420_:
{
lean_object* v___x_1422_; 
v___x_1422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1422_, 0, v___x_1421_);
return v___x_1422_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__1___boxed(lean_object* v___x_1512_, lean_object* v_idxs_1513_, lean_object* v___x_1514_, lean_object* v_fvars_1515_, lean_object* v_ty_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_){
_start:
{
lean_object* v_res_1522_; 
v_res_1522_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__1(v___x_1512_, v_idxs_1513_, v___x_1514_, v_fvars_1515_, v_ty_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_);
lean_dec(v___y_1520_);
lean_dec_ref(v___y_1519_);
lean_dec(v___y_1518_);
lean_dec_ref(v___y_1517_);
lean_dec_ref(v___x_1514_);
return v_res_1522_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__9___redArg(lean_object* v_ref_1523_, lean_object* v_msg_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_){
_start:
{
lean_object* v_fileName_1530_; lean_object* v_fileMap_1531_; lean_object* v_options_1532_; lean_object* v_currRecDepth_1533_; lean_object* v_maxRecDepth_1534_; lean_object* v_ref_1535_; lean_object* v_currNamespace_1536_; lean_object* v_openDecls_1537_; lean_object* v_initHeartbeats_1538_; lean_object* v_maxHeartbeats_1539_; lean_object* v_quotContext_1540_; lean_object* v_currMacroScope_1541_; uint8_t v_diag_1542_; lean_object* v_cancelTk_x3f_1543_; uint8_t v_suppressElabErrors_1544_; lean_object* v_inheritedTraceOptions_1545_; lean_object* v_ref_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; 
v_fileName_1530_ = lean_ctor_get(v___y_1527_, 0);
v_fileMap_1531_ = lean_ctor_get(v___y_1527_, 1);
v_options_1532_ = lean_ctor_get(v___y_1527_, 2);
v_currRecDepth_1533_ = lean_ctor_get(v___y_1527_, 3);
v_maxRecDepth_1534_ = lean_ctor_get(v___y_1527_, 4);
v_ref_1535_ = lean_ctor_get(v___y_1527_, 5);
v_currNamespace_1536_ = lean_ctor_get(v___y_1527_, 6);
v_openDecls_1537_ = lean_ctor_get(v___y_1527_, 7);
v_initHeartbeats_1538_ = lean_ctor_get(v___y_1527_, 8);
v_maxHeartbeats_1539_ = lean_ctor_get(v___y_1527_, 9);
v_quotContext_1540_ = lean_ctor_get(v___y_1527_, 10);
v_currMacroScope_1541_ = lean_ctor_get(v___y_1527_, 11);
v_diag_1542_ = lean_ctor_get_uint8(v___y_1527_, sizeof(void*)*14);
v_cancelTk_x3f_1543_ = lean_ctor_get(v___y_1527_, 12);
v_suppressElabErrors_1544_ = lean_ctor_get_uint8(v___y_1527_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1545_ = lean_ctor_get(v___y_1527_, 13);
v_ref_1546_ = l_Lean_replaceRef(v_ref_1523_, v_ref_1535_);
lean_inc_ref(v_inheritedTraceOptions_1545_);
lean_inc(v_cancelTk_x3f_1543_);
lean_inc(v_currMacroScope_1541_);
lean_inc(v_quotContext_1540_);
lean_inc(v_maxHeartbeats_1539_);
lean_inc(v_initHeartbeats_1538_);
lean_inc(v_openDecls_1537_);
lean_inc(v_currNamespace_1536_);
lean_inc(v_maxRecDepth_1534_);
lean_inc(v_currRecDepth_1533_);
lean_inc_ref(v_options_1532_);
lean_inc_ref(v_fileMap_1531_);
lean_inc_ref(v_fileName_1530_);
v___x_1547_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1547_, 0, v_fileName_1530_);
lean_ctor_set(v___x_1547_, 1, v_fileMap_1531_);
lean_ctor_set(v___x_1547_, 2, v_options_1532_);
lean_ctor_set(v___x_1547_, 3, v_currRecDepth_1533_);
lean_ctor_set(v___x_1547_, 4, v_maxRecDepth_1534_);
lean_ctor_set(v___x_1547_, 5, v_ref_1546_);
lean_ctor_set(v___x_1547_, 6, v_currNamespace_1536_);
lean_ctor_set(v___x_1547_, 7, v_openDecls_1537_);
lean_ctor_set(v___x_1547_, 8, v_initHeartbeats_1538_);
lean_ctor_set(v___x_1547_, 9, v_maxHeartbeats_1539_);
lean_ctor_set(v___x_1547_, 10, v_quotContext_1540_);
lean_ctor_set(v___x_1547_, 11, v_currMacroScope_1541_);
lean_ctor_set(v___x_1547_, 12, v_cancelTk_x3f_1543_);
lean_ctor_set(v___x_1547_, 13, v_inheritedTraceOptions_1545_);
lean_ctor_set_uint8(v___x_1547_, sizeof(void*)*14, v_diag_1542_);
lean_ctor_set_uint8(v___x_1547_, sizeof(void*)*14 + 1, v_suppressElabErrors_1544_);
v___x_1548_ = l_Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0___redArg(v_msg_1524_, v___y_1525_, v___y_1526_, v___x_1547_, v___y_1528_);
lean_dec_ref(v___x_1547_);
return v___x_1548_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__9___redArg___boxed(lean_object* v_ref_1549_, lean_object* v_msg_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_){
_start:
{
lean_object* v_res_1556_; 
v_res_1556_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__9___redArg(v_ref_1549_, v_msg_1550_, v___y_1551_, v___y_1552_, v___y_1553_, v___y_1554_);
lean_dec(v___y_1554_);
lean_dec_ref(v___y_1553_);
lean_dec(v___y_1552_);
lean_dec_ref(v___y_1551_);
lean_dec(v_ref_1549_);
return v_res_1556_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__0(void){
_start:
{
lean_object* v___x_1557_; 
v___x_1557_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1557_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__1(void){
_start:
{
lean_object* v___x_1558_; lean_object* v___x_1559_; 
v___x_1558_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__0);
v___x_1559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1559_, 0, v___x_1558_);
return v___x_1559_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__2(void){
_start:
{
lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; 
v___x_1560_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__1);
v___x_1561_ = lean_unsigned_to_nat(0u);
v___x_1562_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_1562_, 0, v___x_1561_);
lean_ctor_set(v___x_1562_, 1, v___x_1561_);
lean_ctor_set(v___x_1562_, 2, v___x_1561_);
lean_ctor_set(v___x_1562_, 3, v___x_1560_);
lean_ctor_set(v___x_1562_, 4, v___x_1560_);
lean_ctor_set(v___x_1562_, 5, v___x_1560_);
lean_ctor_set(v___x_1562_, 6, v___x_1560_);
lean_ctor_set(v___x_1562_, 7, v___x_1560_);
lean_ctor_set(v___x_1562_, 8, v___x_1560_);
return v___x_1562_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__3(void){
_start:
{
lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; 
v___x_1563_ = lean_unsigned_to_nat(32u);
v___x_1564_ = lean_mk_empty_array_with_capacity(v___x_1563_);
v___x_1565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1565_, 0, v___x_1564_);
return v___x_1565_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__4(void){
_start:
{
size_t v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; 
v___x_1566_ = ((size_t)5ULL);
v___x_1567_ = lean_unsigned_to_nat(0u);
v___x_1568_ = lean_unsigned_to_nat(32u);
v___x_1569_ = lean_mk_empty_array_with_capacity(v___x_1568_);
v___x_1570_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__3);
v___x_1571_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1571_, 0, v___x_1570_);
lean_ctor_set(v___x_1571_, 1, v___x_1569_);
lean_ctor_set(v___x_1571_, 2, v___x_1567_);
lean_ctor_set(v___x_1571_, 3, v___x_1567_);
lean_ctor_set_usize(v___x_1571_, 4, v___x_1566_);
return v___x_1571_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__5(void){
_start:
{
lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; 
v___x_1572_ = lean_box(1);
v___x_1573_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__4);
v___x_1574_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__1);
v___x_1575_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1575_, 0, v___x_1574_);
lean_ctor_set(v___x_1575_, 1, v___x_1573_);
lean_ctor_set(v___x_1575_, 2, v___x_1572_);
return v___x_1575_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__7(void){
_start:
{
lean_object* v___x_1577_; lean_object* v___x_1578_; 
v___x_1577_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__6));
v___x_1578_ = l_Lean_stringToMessageData(v___x_1577_);
return v___x_1578_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__9(void){
_start:
{
lean_object* v___x_1580_; lean_object* v___x_1581_; 
v___x_1580_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__8));
v___x_1581_ = l_Lean_stringToMessageData(v___x_1580_);
return v___x_1581_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__11(void){
_start:
{
lean_object* v___x_1583_; lean_object* v___x_1584_; 
v___x_1583_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__10));
v___x_1584_ = l_Lean_stringToMessageData(v___x_1583_);
return v___x_1584_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__13(void){
_start:
{
lean_object* v___x_1586_; lean_object* v___x_1587_; 
v___x_1586_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__12));
v___x_1587_ = l_Lean_stringToMessageData(v___x_1586_);
return v___x_1587_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__15(void){
_start:
{
lean_object* v___x_1589_; lean_object* v___x_1590_; 
v___x_1589_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__14));
v___x_1590_ = l_Lean_stringToMessageData(v___x_1589_);
return v___x_1590_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__17(void){
_start:
{
lean_object* v___x_1592_; lean_object* v___x_1593_; 
v___x_1592_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__16));
v___x_1593_ = l_Lean_stringToMessageData(v___x_1592_);
return v___x_1593_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__19(void){
_start:
{
lean_object* v___x_1595_; lean_object* v___x_1596_; 
v___x_1595_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__18));
v___x_1596_ = l_Lean_stringToMessageData(v___x_1595_);
return v___x_1596_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg(lean_object* v_msg_1597_, lean_object* v_declHint_1598_, lean_object* v___y_1599_){
_start:
{
lean_object* v___x_1601_; lean_object* v_env_1602_; uint8_t v___x_1603_; 
v___x_1601_ = lean_st_ref_get(v___y_1599_);
v_env_1602_ = lean_ctor_get(v___x_1601_, 0);
lean_inc_ref(v_env_1602_);
lean_dec(v___x_1601_);
v___x_1603_ = l_Lean_Name_isAnonymous(v_declHint_1598_);
if (v___x_1603_ == 0)
{
uint8_t v_isExporting_1604_; 
v_isExporting_1604_ = lean_ctor_get_uint8(v_env_1602_, sizeof(void*)*8);
if (v_isExporting_1604_ == 0)
{
lean_object* v___x_1605_; 
lean_dec_ref(v_env_1602_);
lean_dec(v_declHint_1598_);
v___x_1605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1605_, 0, v_msg_1597_);
return v___x_1605_;
}
else
{
lean_object* v___x_1606_; uint8_t v___x_1607_; 
lean_inc_ref(v_env_1602_);
v___x_1606_ = l_Lean_Environment_setExporting(v_env_1602_, v___x_1603_);
lean_inc(v_declHint_1598_);
lean_inc_ref(v___x_1606_);
v___x_1607_ = l_Lean_Environment_contains(v___x_1606_, v_declHint_1598_, v_isExporting_1604_);
if (v___x_1607_ == 0)
{
lean_object* v___x_1608_; 
lean_dec_ref(v___x_1606_);
lean_dec_ref(v_env_1602_);
lean_dec(v_declHint_1598_);
v___x_1608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1608_, 0, v_msg_1597_);
return v___x_1608_;
}
else
{
lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v_c_1614_; lean_object* v___x_1615_; 
v___x_1609_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__2);
v___x_1610_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__5);
v___x_1611_ = l_Lean_Options_empty;
v___x_1612_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1612_, 0, v___x_1606_);
lean_ctor_set(v___x_1612_, 1, v___x_1609_);
lean_ctor_set(v___x_1612_, 2, v___x_1610_);
lean_ctor_set(v___x_1612_, 3, v___x_1611_);
lean_inc(v_declHint_1598_);
v___x_1613_ = l_Lean_MessageData_ofConstName(v_declHint_1598_, v___x_1603_);
v_c_1614_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1614_, 0, v___x_1612_);
lean_ctor_set(v_c_1614_, 1, v___x_1613_);
v___x_1615_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1602_, v_declHint_1598_);
if (lean_obj_tag(v___x_1615_) == 0)
{
lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; 
lean_dec_ref(v_env_1602_);
lean_dec(v_declHint_1598_);
v___x_1616_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__7);
v___x_1617_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1617_, 0, v___x_1616_);
lean_ctor_set(v___x_1617_, 1, v_c_1614_);
v___x_1618_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__9);
v___x_1619_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1619_, 0, v___x_1617_);
lean_ctor_set(v___x_1619_, 1, v___x_1618_);
v___x_1620_ = l_Lean_MessageData_note(v___x_1619_);
v___x_1621_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1621_, 0, v_msg_1597_);
lean_ctor_set(v___x_1621_, 1, v___x_1620_);
v___x_1622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1622_, 0, v___x_1621_);
return v___x_1622_;
}
else
{
lean_object* v_val_1623_; lean_object* v___x_1625_; uint8_t v_isShared_1626_; uint8_t v_isSharedCheck_1658_; 
v_val_1623_ = lean_ctor_get(v___x_1615_, 0);
v_isSharedCheck_1658_ = !lean_is_exclusive(v___x_1615_);
if (v_isSharedCheck_1658_ == 0)
{
v___x_1625_ = v___x_1615_;
v_isShared_1626_ = v_isSharedCheck_1658_;
goto v_resetjp_1624_;
}
else
{
lean_inc(v_val_1623_);
lean_dec(v___x_1615_);
v___x_1625_ = lean_box(0);
v_isShared_1626_ = v_isSharedCheck_1658_;
goto v_resetjp_1624_;
}
v_resetjp_1624_:
{
lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v_mod_1630_; uint8_t v___x_1631_; 
v___x_1627_ = lean_box(0);
v___x_1628_ = l_Lean_Environment_header(v_env_1602_);
lean_dec_ref(v_env_1602_);
v___x_1629_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1628_);
v_mod_1630_ = lean_array_get(v___x_1627_, v___x_1629_, v_val_1623_);
lean_dec(v_val_1623_);
lean_dec_ref(v___x_1629_);
v___x_1631_ = l_Lean_isPrivateName(v_declHint_1598_);
lean_dec(v_declHint_1598_);
if (v___x_1631_ == 0)
{
lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1643_; 
v___x_1632_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__11);
v___x_1633_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1633_, 0, v___x_1632_);
lean_ctor_set(v___x_1633_, 1, v_c_1614_);
v___x_1634_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__13);
v___x_1635_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1635_, 0, v___x_1633_);
lean_ctor_set(v___x_1635_, 1, v___x_1634_);
v___x_1636_ = l_Lean_MessageData_ofName(v_mod_1630_);
v___x_1637_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1637_, 0, v___x_1635_);
lean_ctor_set(v___x_1637_, 1, v___x_1636_);
v___x_1638_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__15);
v___x_1639_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1639_, 0, v___x_1637_);
lean_ctor_set(v___x_1639_, 1, v___x_1638_);
v___x_1640_ = l_Lean_MessageData_note(v___x_1639_);
v___x_1641_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1641_, 0, v_msg_1597_);
lean_ctor_set(v___x_1641_, 1, v___x_1640_);
if (v_isShared_1626_ == 0)
{
lean_ctor_set_tag(v___x_1625_, 0);
lean_ctor_set(v___x_1625_, 0, v___x_1641_);
v___x_1643_ = v___x_1625_;
goto v_reusejp_1642_;
}
else
{
lean_object* v_reuseFailAlloc_1644_; 
v_reuseFailAlloc_1644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1644_, 0, v___x_1641_);
v___x_1643_ = v_reuseFailAlloc_1644_;
goto v_reusejp_1642_;
}
v_reusejp_1642_:
{
return v___x_1643_;
}
}
else
{
lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1656_; 
v___x_1645_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__7);
v___x_1646_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1646_, 0, v___x_1645_);
lean_ctor_set(v___x_1646_, 1, v_c_1614_);
v___x_1647_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__17);
v___x_1648_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1648_, 0, v___x_1646_);
lean_ctor_set(v___x_1648_, 1, v___x_1647_);
v___x_1649_ = l_Lean_MessageData_ofName(v_mod_1630_);
v___x_1650_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1650_, 0, v___x_1648_);
lean_ctor_set(v___x_1650_, 1, v___x_1649_);
v___x_1651_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__19);
v___x_1652_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1652_, 0, v___x_1650_);
lean_ctor_set(v___x_1652_, 1, v___x_1651_);
v___x_1653_ = l_Lean_MessageData_note(v___x_1652_);
v___x_1654_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1654_, 0, v_msg_1597_);
lean_ctor_set(v___x_1654_, 1, v___x_1653_);
if (v_isShared_1626_ == 0)
{
lean_ctor_set_tag(v___x_1625_, 0);
lean_ctor_set(v___x_1625_, 0, v___x_1654_);
v___x_1656_ = v___x_1625_;
goto v_reusejp_1655_;
}
else
{
lean_object* v_reuseFailAlloc_1657_; 
v_reuseFailAlloc_1657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1657_, 0, v___x_1654_);
v___x_1656_ = v_reuseFailAlloc_1657_;
goto v_reusejp_1655_;
}
v_reusejp_1655_:
{
return v___x_1656_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1659_; 
lean_dec_ref(v_env_1602_);
lean_dec(v_declHint_1598_);
v___x_1659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1659_, 0, v_msg_1597_);
return v___x_1659_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___boxed(lean_object* v_msg_1660_, lean_object* v_declHint_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_){
_start:
{
lean_object* v_res_1664_; 
v_res_1664_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg(v_msg_1660_, v_declHint_1661_, v___y_1662_);
lean_dec(v___y_1662_);
return v_res_1664_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8(lean_object* v_msg_1665_, lean_object* v_declHint_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_){
_start:
{
lean_object* v___x_1672_; lean_object* v_a_1673_; lean_object* v___x_1675_; uint8_t v_isShared_1676_; uint8_t v_isSharedCheck_1682_; 
v___x_1672_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg(v_msg_1665_, v_declHint_1666_, v___y_1670_);
v_a_1673_ = lean_ctor_get(v___x_1672_, 0);
v_isSharedCheck_1682_ = !lean_is_exclusive(v___x_1672_);
if (v_isSharedCheck_1682_ == 0)
{
v___x_1675_ = v___x_1672_;
v_isShared_1676_ = v_isSharedCheck_1682_;
goto v_resetjp_1674_;
}
else
{
lean_inc(v_a_1673_);
lean_dec(v___x_1672_);
v___x_1675_ = lean_box(0);
v_isShared_1676_ = v_isSharedCheck_1682_;
goto v_resetjp_1674_;
}
v_resetjp_1674_:
{
lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1680_; 
v___x_1677_ = l_Lean_unknownIdentifierMessageTag;
v___x_1678_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1678_, 0, v___x_1677_);
lean_ctor_set(v___x_1678_, 1, v_a_1673_);
if (v_isShared_1676_ == 0)
{
lean_ctor_set(v___x_1675_, 0, v___x_1678_);
v___x_1680_ = v___x_1675_;
goto v_reusejp_1679_;
}
else
{
lean_object* v_reuseFailAlloc_1681_; 
v_reuseFailAlloc_1681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1681_, 0, v___x_1678_);
v___x_1680_ = v_reuseFailAlloc_1681_;
goto v_reusejp_1679_;
}
v_reusejp_1679_:
{
return v___x_1680_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8___boxed(lean_object* v_msg_1683_, lean_object* v_declHint_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_){
_start:
{
lean_object* v_res_1690_; 
v_res_1690_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8(v_msg_1683_, v_declHint_1684_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_);
lean_dec(v___y_1688_);
lean_dec_ref(v___y_1687_);
lean_dec(v___y_1686_);
lean_dec_ref(v___y_1685_);
return v_res_1690_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7___redArg(lean_object* v_ref_1691_, lean_object* v_msg_1692_, lean_object* v_declHint_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_){
_start:
{
lean_object* v___x_1699_; lean_object* v_a_1700_; lean_object* v___x_1701_; 
v___x_1699_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8(v_msg_1692_, v_declHint_1693_, v___y_1694_, v___y_1695_, v___y_1696_, v___y_1697_);
v_a_1700_ = lean_ctor_get(v___x_1699_, 0);
lean_inc(v_a_1700_);
lean_dec_ref(v___x_1699_);
v___x_1701_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__9___redArg(v_ref_1691_, v_a_1700_, v___y_1694_, v___y_1695_, v___y_1696_, v___y_1697_);
return v___x_1701_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7___redArg___boxed(lean_object* v_ref_1702_, lean_object* v_msg_1703_, lean_object* v_declHint_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_){
_start:
{
lean_object* v_res_1710_; 
v_res_1710_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7___redArg(v_ref_1702_, v_msg_1703_, v_declHint_1704_, v___y_1705_, v___y_1706_, v___y_1707_, v___y_1708_);
lean_dec(v___y_1708_);
lean_dec_ref(v___y_1707_);
lean_dec(v___y_1706_);
lean_dec_ref(v___y_1705_);
lean_dec(v_ref_1702_);
return v_res_1710_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_1712_; lean_object* v___x_1713_; 
v___x_1712_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3___redArg___closed__0));
v___x_1713_ = l_Lean_stringToMessageData(v___x_1712_);
return v___x_1713_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_1715_; lean_object* v___x_1716_; 
v___x_1715_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3___redArg___closed__2));
v___x_1716_ = l_Lean_stringToMessageData(v___x_1715_);
return v___x_1716_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3___redArg(lean_object* v_ref_1717_, lean_object* v_constName_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_){
_start:
{
lean_object* v___x_1724_; uint8_t v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; 
v___x_1724_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3___redArg___closed__1);
v___x_1725_ = 0;
lean_inc(v_constName_1718_);
v___x_1726_ = l_Lean_MessageData_ofConstName(v_constName_1718_, v___x_1725_);
v___x_1727_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1727_, 0, v___x_1724_);
lean_ctor_set(v___x_1727_, 1, v___x_1726_);
v___x_1728_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3___redArg___closed__3);
v___x_1729_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1729_, 0, v___x_1727_);
lean_ctor_set(v___x_1729_, 1, v___x_1728_);
v___x_1730_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7___redArg(v_ref_1717_, v___x_1729_, v_constName_1718_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_);
return v___x_1730_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_ref_1731_, lean_object* v_constName_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_){
_start:
{
lean_object* v_res_1738_; 
v_res_1738_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3___redArg(v_ref_1731_, v_constName_1732_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_);
lean_dec(v___y_1736_);
lean_dec_ref(v___y_1735_);
lean_dec(v___y_1734_);
lean_dec_ref(v___y_1733_);
lean_dec(v_ref_1731_);
return v_res_1738_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0___redArg(lean_object* v_constName_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_){
_start:
{
lean_object* v_ref_1745_; lean_object* v___x_1746_; 
v_ref_1745_ = lean_ctor_get(v___y_1742_, 5);
v___x_1746_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3___redArg(v_ref_1745_, v_constName_1739_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_);
return v___x_1746_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0___redArg___boxed(lean_object* v_constName_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_){
_start:
{
lean_object* v_res_1753_; 
v_res_1753_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0___redArg(v_constName_1747_, v___y_1748_, v___y_1749_, v___y_1750_, v___y_1751_);
lean_dec(v___y_1751_);
lean_dec_ref(v___y_1750_);
lean_dec(v___y_1749_);
lean_dec_ref(v___y_1748_);
return v_res_1753_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0(lean_object* v_constName_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_){
_start:
{
lean_object* v___x_1760_; lean_object* v_env_1761_; uint8_t v___x_1762_; lean_object* v___x_1763_; 
v___x_1760_ = lean_st_ref_get(v___y_1758_);
v_env_1761_ = lean_ctor_get(v___x_1760_, 0);
lean_inc_ref(v_env_1761_);
lean_dec(v___x_1760_);
v___x_1762_ = 0;
lean_inc(v_constName_1754_);
v___x_1763_ = l_Lean_Environment_find_x3f(v_env_1761_, v_constName_1754_, v___x_1762_);
if (lean_obj_tag(v___x_1763_) == 0)
{
lean_object* v___x_1764_; 
v___x_1764_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0___redArg(v_constName_1754_, v___y_1755_, v___y_1756_, v___y_1757_, v___y_1758_);
return v___x_1764_;
}
else
{
lean_object* v_val_1765_; lean_object* v___x_1767_; uint8_t v_isShared_1768_; uint8_t v_isSharedCheck_1772_; 
lean_dec(v_constName_1754_);
v_val_1765_ = lean_ctor_get(v___x_1763_, 0);
v_isSharedCheck_1772_ = !lean_is_exclusive(v___x_1763_);
if (v_isSharedCheck_1772_ == 0)
{
v___x_1767_ = v___x_1763_;
v_isShared_1768_ = v_isSharedCheck_1772_;
goto v_resetjp_1766_;
}
else
{
lean_inc(v_val_1765_);
lean_dec(v___x_1763_);
v___x_1767_ = lean_box(0);
v_isShared_1768_ = v_isSharedCheck_1772_;
goto v_resetjp_1766_;
}
v_resetjp_1766_:
{
lean_object* v___x_1770_; 
if (v_isShared_1768_ == 0)
{
lean_ctor_set_tag(v___x_1767_, 0);
v___x_1770_ = v___x_1767_;
goto v_reusejp_1769_;
}
else
{
lean_object* v_reuseFailAlloc_1771_; 
v_reuseFailAlloc_1771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1771_, 0, v_val_1765_);
v___x_1770_ = v_reuseFailAlloc_1771_;
goto v_reusejp_1769_;
}
v_reusejp_1769_:
{
return v___x_1770_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0___boxed(lean_object* v_constName_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_){
_start:
{
lean_object* v_res_1779_; 
v_res_1779_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0(v_constName_1773_, v___y_1774_, v___y_1775_, v___y_1776_, v___y_1777_);
lean_dec(v___y_1777_);
lean_dec_ref(v___y_1776_);
lean_dec(v___y_1775_);
lean_dec_ref(v___y_1774_);
return v_res_1779_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp(lean_object* v_univs_1780_, lean_object* v_params_1781_, lean_object* v_idxs_1782_, lean_object* v_c_1783_, lean_object* v_a_1784_, lean_object* v_a_1785_, lean_object* v_a_1786_, lean_object* v_a_1787_){
_start:
{
lean_object* v___x_1789_; 
v___x_1789_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0(v_c_1783_, v_a_1784_, v_a_1785_, v_a_1786_, v_a_1787_);
if (lean_obj_tag(v___x_1789_) == 0)
{
lean_object* v_a_1790_; lean_object* v___f_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; uint8_t v___x_1795_; lean_object* v___x_1796_; 
v_a_1790_ = lean_ctor_get(v___x_1789_, 0);
lean_inc(v_a_1790_);
lean_dec_ref(v___x_1789_);
lean_inc(v_params_1781_);
v___f_1791_ = lean_alloc_closure((void*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1791_, 0, v_params_1781_);
v___x_1792_ = l_Lean_ConstantInfo_instantiateTypeLevelParams(v_a_1790_, v_univs_1780_);
lean_dec(v_a_1790_);
v___x_1793_ = l_List_lengthTR___redArg(v_params_1781_);
lean_dec(v_params_1781_);
lean_inc(v___x_1793_);
v___x_1794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1794_, 0, v___x_1793_);
v___x_1795_ = 0;
v___x_1796_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__4___redArg(v___x_1792_, v___x_1794_, v___f_1791_, v___x_1795_, v___x_1795_, v_a_1784_, v_a_1785_, v_a_1786_, v_a_1787_);
if (lean_obj_tag(v___x_1796_) == 0)
{
lean_object* v_a_1797_; lean_object* v___x_1798_; lean_object* v___f_1799_; lean_object* v___x_1800_; 
v_a_1797_ = lean_ctor_get(v___x_1796_, 0);
lean_inc(v_a_1797_);
lean_dec_ref(v___x_1796_);
v___x_1798_ = l_Lean_instInhabitedExpr;
v___f_1799_ = lean_alloc_closure((void*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__1___boxed), 10, 3);
lean_closure_set(v___f_1799_, 0, v___x_1793_);
lean_closure_set(v___f_1799_, 1, v_idxs_1782_);
lean_closure_set(v___f_1799_, 2, v___x_1798_);
v___x_1800_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__5___redArg(v_a_1797_, v___f_1799_, v___x_1795_, v_a_1784_, v_a_1785_, v_a_1786_, v_a_1787_);
return v___x_1800_;
}
else
{
lean_object* v_a_1801_; lean_object* v___x_1803_; uint8_t v_isShared_1804_; uint8_t v_isSharedCheck_1808_; 
lean_dec(v___x_1793_);
lean_dec(v_idxs_1782_);
v_a_1801_ = lean_ctor_get(v___x_1796_, 0);
v_isSharedCheck_1808_ = !lean_is_exclusive(v___x_1796_);
if (v_isSharedCheck_1808_ == 0)
{
v___x_1803_ = v___x_1796_;
v_isShared_1804_ = v_isSharedCheck_1808_;
goto v_resetjp_1802_;
}
else
{
lean_inc(v_a_1801_);
lean_dec(v___x_1796_);
v___x_1803_ = lean_box(0);
v_isShared_1804_ = v_isSharedCheck_1808_;
goto v_resetjp_1802_;
}
v_resetjp_1802_:
{
lean_object* v___x_1806_; 
if (v_isShared_1804_ == 0)
{
v___x_1806_ = v___x_1803_;
goto v_reusejp_1805_;
}
else
{
lean_object* v_reuseFailAlloc_1807_; 
v_reuseFailAlloc_1807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1807_, 0, v_a_1801_);
v___x_1806_ = v_reuseFailAlloc_1807_;
goto v_reusejp_1805_;
}
v_reusejp_1805_:
{
return v___x_1806_;
}
}
}
}
else
{
lean_object* v_a_1809_; lean_object* v___x_1811_; uint8_t v_isShared_1812_; uint8_t v_isSharedCheck_1816_; 
lean_dec(v_idxs_1782_);
lean_dec(v_params_1781_);
lean_dec(v_univs_1780_);
v_a_1809_ = lean_ctor_get(v___x_1789_, 0);
v_isSharedCheck_1816_ = !lean_is_exclusive(v___x_1789_);
if (v_isSharedCheck_1816_ == 0)
{
v___x_1811_ = v___x_1789_;
v_isShared_1812_ = v_isSharedCheck_1816_;
goto v_resetjp_1810_;
}
else
{
lean_inc(v_a_1809_);
lean_dec(v___x_1789_);
v___x_1811_ = lean_box(0);
v_isShared_1812_ = v_isSharedCheck_1816_;
goto v_resetjp_1810_;
}
v_resetjp_1810_:
{
lean_object* v___x_1814_; 
if (v_isShared_1812_ == 0)
{
v___x_1814_ = v___x_1811_;
goto v_reusejp_1813_;
}
else
{
lean_object* v_reuseFailAlloc_1815_; 
v_reuseFailAlloc_1815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1815_, 0, v_a_1809_);
v___x_1814_ = v_reuseFailAlloc_1815_;
goto v_reusejp_1813_;
}
v_reusejp_1813_:
{
return v___x_1814_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___boxed(lean_object* v_univs_1817_, lean_object* v_params_1818_, lean_object* v_idxs_1819_, lean_object* v_c_1820_, lean_object* v_a_1821_, lean_object* v_a_1822_, lean_object* v_a_1823_, lean_object* v_a_1824_, lean_object* v_a_1825_){
_start:
{
lean_object* v_res_1826_; 
v_res_1826_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp(v_univs_1817_, v_params_1818_, v_idxs_1819_, v_c_1820_, v_a_1821_, v_a_1822_, v_a_1823_, v_a_1824_);
lean_dec(v_a_1824_);
lean_dec_ref(v_a_1823_);
lean_dec(v_a_1822_);
lean_dec_ref(v_a_1821_);
return v_res_1826_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0(lean_object* v_00_u03b1_1827_, lean_object* v_constName_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_){
_start:
{
lean_object* v___x_1834_; 
v___x_1834_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0___redArg(v_constName_1828_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_);
return v___x_1834_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1835_, lean_object* v_constName_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_){
_start:
{
lean_object* v_res_1842_; 
v_res_1842_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0(v_00_u03b1_1835_, v_constName_1836_, v___y_1837_, v___y_1838_, v___y_1839_, v___y_1840_);
lean_dec(v___y_1840_);
lean_dec_ref(v___y_1839_);
lean_dec(v___y_1838_);
lean_dec_ref(v___y_1837_);
return v_res_1842_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3(lean_object* v_00_u03b1_1843_, lean_object* v_ref_1844_, lean_object* v_constName_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_){
_start:
{
lean_object* v___x_1851_; 
v___x_1851_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3___redArg(v_ref_1844_, v_constName_1845_, v___y_1846_, v___y_1847_, v___y_1848_, v___y_1849_);
return v___x_1851_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b1_1852_, lean_object* v_ref_1853_, lean_object* v_constName_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_){
_start:
{
lean_object* v_res_1860_; 
v_res_1860_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3(v_00_u03b1_1852_, v_ref_1853_, v_constName_1854_, v___y_1855_, v___y_1856_, v___y_1857_, v___y_1858_);
lean_dec(v___y_1858_);
lean_dec_ref(v___y_1857_);
lean_dec(v___y_1856_);
lean_dec_ref(v___y_1855_);
lean_dec(v_ref_1853_);
return v_res_1860_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7(lean_object* v_00_u03b1_1861_, lean_object* v_ref_1862_, lean_object* v_msg_1863_, lean_object* v_declHint_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_){
_start:
{
lean_object* v___x_1870_; 
v___x_1870_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7___redArg(v_ref_1862_, v_msg_1863_, v_declHint_1864_, v___y_1865_, v___y_1866_, v___y_1867_, v___y_1868_);
return v___x_1870_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7___boxed(lean_object* v_00_u03b1_1871_, lean_object* v_ref_1872_, lean_object* v_msg_1873_, lean_object* v_declHint_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_){
_start:
{
lean_object* v_res_1880_; 
v_res_1880_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7(v_00_u03b1_1871_, v_ref_1872_, v_msg_1873_, v_declHint_1874_, v___y_1875_, v___y_1876_, v___y_1877_, v___y_1878_);
lean_dec(v___y_1878_);
lean_dec_ref(v___y_1877_);
lean_dec(v___y_1876_);
lean_dec_ref(v___y_1875_);
lean_dec(v_ref_1872_);
return v_res_1880_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9(lean_object* v_msg_1881_, lean_object* v_declHint_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_){
_start:
{
lean_object* v___x_1888_; 
v___x_1888_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg(v_msg_1881_, v_declHint_1882_, v___y_1886_);
return v___x_1888_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___boxed(lean_object* v_msg_1889_, lean_object* v_declHint_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_){
_start:
{
lean_object* v_res_1896_; 
v_res_1896_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9(v_msg_1889_, v_declHint_1890_, v___y_1891_, v___y_1892_, v___y_1893_, v___y_1894_);
lean_dec(v___y_1894_);
lean_dec_ref(v___y_1893_);
lean_dec(v___y_1892_);
lean_dec_ref(v___y_1891_);
return v_res_1896_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__9(lean_object* v_00_u03b1_1897_, lean_object* v_ref_1898_, lean_object* v_msg_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_){
_start:
{
lean_object* v___x_1905_; 
v___x_1905_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__9___redArg(v_ref_1898_, v_msg_1899_, v___y_1900_, v___y_1901_, v___y_1902_, v___y_1903_);
return v___x_1905_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__9___boxed(lean_object* v_00_u03b1_1906_, lean_object* v_ref_1907_, lean_object* v_msg_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_){
_start:
{
lean_object* v_res_1914_; 
v_res_1914_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__9(v_00_u03b1_1906_, v_ref_1907_, v_msg_1908_, v___y_1909_, v___y_1910_, v___y_1911_, v___y_1912_);
lean_dec(v___y_1912_);
lean_dec_ref(v___y_1911_);
lean_dec(v___y_1910_);
lean_dec_ref(v___y_1909_);
lean_dec(v_ref_1907_);
return v_res_1914_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__1(lean_object* v___y_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_){
_start:
{
lean_object* v_ref_1930_; uint8_t v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; 
v_ref_1930_ = lean_ctor_get(v___y_1927_, 5);
v___x_1931_ = 0;
v___x_1932_ = l_Lean_SourceInfo_fromRef(v_ref_1930_, v___x_1931_);
v___x_1933_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__1___closed__0));
v___x_1934_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__1___closed__1));
lean_inc(v___x_1932_);
v___x_1935_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1935_, 0, v___x_1932_);
lean_ctor_set(v___x_1935_, 1, v___x_1933_);
v___x_1936_ = l_Lean_Syntax_node1(v___x_1932_, v___x_1934_, v___x_1935_);
v___x_1937_ = l_Lean_Elab_Tactic_evalTactic(v___x_1936_, v___y_1921_, v___y_1922_, v___y_1923_, v___y_1924_, v___y_1925_, v___y_1926_, v___y_1927_, v___y_1928_);
return v___x_1937_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__1___boxed(lean_object* v___y_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_){
_start:
{
lean_object* v_res_1947_; 
v_res_1947_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__1(v___y_1938_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_, v___y_1943_, v___y_1944_, v___y_1945_);
lean_dec(v___y_1945_);
lean_dec_ref(v___y_1944_);
lean_dec(v___y_1943_);
lean_dec_ref(v___y_1942_);
lean_dec(v___y_1941_);
lean_dec_ref(v___y_1940_);
lean_dec(v___y_1939_);
lean_dec_ref(v___y_1938_);
return v_res_1947_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__0(uint8_t v_isZero_1948_, lean_object* v_x_1949_){
_start:
{
return v_isZero_1948_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__0___boxed(lean_object* v_isZero_1950_, lean_object* v_x_1951_){
_start:
{
uint8_t v_isZero_boxed_1952_; uint8_t v_res_1953_; lean_object* v_r_1954_; 
v_isZero_boxed_1952_ = lean_unbox(v_isZero_1950_);
v_res_1953_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__0(v_isZero_boxed_1952_, v_x_1951_);
lean_dec(v_x_1951_);
v_r_1954_ = lean_box(v_res_1953_);
return v_r_1954_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__2(uint8_t v_isZero_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_){
_start:
{
lean_object* v_ref_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; 
v_ref_1965_ = lean_ctor_get(v___y_1962_, 5);
v___x_1966_ = l_Lean_SourceInfo_fromRef(v_ref_1965_, v_isZero_1955_);
v___x_1967_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__3));
v___x_1968_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__4));
lean_inc_n(v___x_1966_, 9);
v___x_1969_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1969_, 0, v___x_1966_);
lean_ctor_set(v___x_1969_, 1, v___x_1967_);
v___x_1970_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__7));
v___x_1971_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__8));
v___x_1972_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1972_, 0, v___x_1966_);
lean_ctor_set(v___x_1972_, 1, v___x_1971_);
v___x_1973_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__10));
v___x_1974_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__12));
v___x_1975_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__13));
v___x_1976_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1976_, 0, v___x_1966_);
lean_ctor_set(v___x_1976_, 1, v___x_1975_);
v___x_1977_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__14));
v___x_1978_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1978_, 0, v___x_1966_);
lean_ctor_set(v___x_1978_, 1, v___x_1977_);
v___x_1979_ = l_Lean_Syntax_node2(v___x_1966_, v___x_1974_, v___x_1976_, v___x_1978_);
v___x_1980_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__15));
v___x_1981_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1981_, 0, v___x_1966_);
lean_ctor_set(v___x_1981_, 1, v___x_1980_);
lean_inc(v___x_1979_);
v___x_1982_ = l_Lean_Syntax_node3(v___x_1966_, v___x_1973_, v___x_1979_, v___x_1981_, v___x_1979_);
v___x_1983_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__16));
v___x_1984_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1984_, 0, v___x_1966_);
lean_ctor_set(v___x_1984_, 1, v___x_1983_);
v___x_1985_ = l_Lean_Syntax_node3(v___x_1966_, v___x_1970_, v___x_1972_, v___x_1982_, v___x_1984_);
v___x_1986_ = l_Lean_Syntax_node2(v___x_1966_, v___x_1968_, v___x_1969_, v___x_1985_);
v___x_1987_ = l_Lean_Elab_Tactic_evalTactic(v___x_1986_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_);
return v___x_1987_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__2___boxed(lean_object* v_isZero_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_){
_start:
{
uint8_t v_isZero_boxed_1998_; lean_object* v_res_1999_; 
v_isZero_boxed_1998_ = lean_unbox(v_isZero_1988_);
v_res_1999_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__2(v_isZero_boxed_1998_, v___y_1989_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_);
lean_dec(v___y_1996_);
lean_dec_ref(v___y_1995_);
lean_dec(v___y_1994_);
lean_dec_ref(v___y_1993_);
lean_dec(v___y_1992_);
lean_dec_ref(v___y_1991_);
lean_dec(v___y_1990_);
lean_dec_ref(v___y_1989_);
return v_res_1999_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__3(uint8_t v_isZero_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_){
_start:
{
lean_object* v_ref_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; 
v_ref_2010_ = lean_ctor_get(v___y_2007_, 5);
v___x_2011_ = l_Lean_SourceInfo_fromRef(v_ref_2010_, v_isZero_2000_);
v___x_2012_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__1___closed__0));
v___x_2013_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__1___closed__1));
lean_inc(v___x_2011_);
v___x_2014_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2014_, 0, v___x_2011_);
lean_ctor_set(v___x_2014_, 1, v___x_2012_);
v___x_2015_ = l_Lean_Syntax_node1(v___x_2011_, v___x_2013_, v___x_2014_);
v___x_2016_ = l_Lean_Elab_Tactic_evalTactic(v___x_2015_, v___y_2001_, v___y_2002_, v___y_2003_, v___y_2004_, v___y_2005_, v___y_2006_, v___y_2007_, v___y_2008_);
return v___x_2016_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__3___boxed(lean_object* v_isZero_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_){
_start:
{
uint8_t v_isZero_boxed_2027_; lean_object* v_res_2028_; 
v_isZero_boxed_2027_ = lean_unbox(v_isZero_2017_);
v_res_2028_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__3(v_isZero_boxed_2027_, v___y_2018_, v___y_2019_, v___y_2020_, v___y_2021_, v___y_2022_, v___y_2023_, v___y_2024_, v___y_2025_);
lean_dec(v___y_2025_);
lean_dec_ref(v___y_2024_);
lean_dec(v___y_2023_);
lean_dec_ref(v___y_2022_);
lean_dec(v___y_2021_);
lean_dec_ref(v___y_2020_);
lean_dec(v___y_2019_);
lean_dec_ref(v___y_2018_);
return v_res_2028_;
}
}
static lean_object* _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___closed__2(void){
_start:
{
lean_object* v___x_2031_; lean_object* v___x_2032_; 
v___x_2031_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___closed__1));
v___x_2032_ = l_Lean_stringToMessageData(v___x_2031_);
return v___x_2032_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor(lean_object* v_mvar_2033_, lean_object* v_n_2034_, lean_object* v_a_2035_, lean_object* v_a_2036_, lean_object* v_a_2037_, lean_object* v_a_2038_){
_start:
{
lean_object* v___y_2041_; lean_object* v___y_2042_; lean_object* v___y_2043_; lean_object* v___y_2044_; lean_object* v_zero_2047_; uint8_t v_isZero_2048_; 
v_zero_2047_ = lean_unsigned_to_nat(0u);
v_isZero_2048_ = lean_nat_dec_eq(v_n_2034_, v_zero_2047_);
if (v_isZero_2048_ == 1)
{
lean_object* v___f_2049_; lean_object* v___f_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; uint8_t v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; 
lean_dec(v_n_2034_);
v___f_2049_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___closed__2));
v___f_2050_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___closed__0));
v___x_2051_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_run___boxed), 9, 2);
lean_closure_set(v___x_2051_, 0, v_mvar_2033_);
lean_closure_set(v___x_2051_, 1, v___f_2050_);
v___x_2052_ = lean_box(0);
v___x_2053_ = lean_box(0);
v___x_2054_ = lean_box(1);
v___x_2055_ = 0;
v___x_2056_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___closed__4));
v___x_2057_ = lean_alloc_ctor(0, 8, 11);
lean_ctor_set(v___x_2057_, 0, v___x_2052_);
lean_ctor_set(v___x_2057_, 1, v___x_2053_);
lean_ctor_set(v___x_2057_, 2, v___x_2052_);
lean_ctor_set(v___x_2057_, 3, v___f_2049_);
lean_ctor_set(v___x_2057_, 4, v___x_2054_);
lean_ctor_set(v___x_2057_, 5, v___x_2054_);
lean_ctor_set(v___x_2057_, 6, v___x_2052_);
lean_ctor_set(v___x_2057_, 7, v___x_2056_);
lean_ctor_set_uint8(v___x_2057_, sizeof(void*)*8, v_isZero_2048_);
lean_ctor_set_uint8(v___x_2057_, sizeof(void*)*8 + 1, v_isZero_2048_);
lean_ctor_set_uint8(v___x_2057_, sizeof(void*)*8 + 2, v_isZero_2048_);
lean_ctor_set_uint8(v___x_2057_, sizeof(void*)*8 + 3, v_isZero_2048_);
lean_ctor_set_uint8(v___x_2057_, sizeof(void*)*8 + 4, v___x_2055_);
lean_ctor_set_uint8(v___x_2057_, sizeof(void*)*8 + 5, v___x_2055_);
lean_ctor_set_uint8(v___x_2057_, sizeof(void*)*8 + 6, v___x_2055_);
lean_ctor_set_uint8(v___x_2057_, sizeof(void*)*8 + 7, v___x_2055_);
lean_ctor_set_uint8(v___x_2057_, sizeof(void*)*8 + 8, v_isZero_2048_);
lean_ctor_set_uint8(v___x_2057_, sizeof(void*)*8 + 9, v___x_2055_);
lean_ctor_set_uint8(v___x_2057_, sizeof(void*)*8 + 10, v_isZero_2048_);
v___x_2058_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___closed__6));
v___x_2059_ = l_Lean_Elab_Term_TermElabM_run___redArg(v___x_2051_, v___x_2057_, v___x_2058_, v_a_2035_, v_a_2036_, v_a_2037_, v_a_2038_);
if (lean_obj_tag(v___x_2059_) == 0)
{
lean_object* v_a_2060_; lean_object* v___x_2062_; uint8_t v_isShared_2063_; uint8_t v_isSharedCheck_2071_; 
v_a_2060_ = lean_ctor_get(v___x_2059_, 0);
v_isSharedCheck_2071_ = !lean_is_exclusive(v___x_2059_);
if (v_isSharedCheck_2071_ == 0)
{
v___x_2062_ = v___x_2059_;
v_isShared_2063_ = v_isSharedCheck_2071_;
goto v_resetjp_2061_;
}
else
{
lean_inc(v_a_2060_);
lean_dec(v___x_2059_);
v___x_2062_ = lean_box(0);
v_isShared_2063_ = v_isSharedCheck_2071_;
goto v_resetjp_2061_;
}
v_resetjp_2061_:
{
lean_object* v_fst_2064_; 
v_fst_2064_ = lean_ctor_get(v_a_2060_, 0);
lean_inc(v_fst_2064_);
lean_dec(v_a_2060_);
if (lean_obj_tag(v_fst_2064_) == 0)
{
lean_object* v___x_2065_; lean_object* v___x_2067_; 
v___x_2065_ = lean_box(0);
if (v_isShared_2063_ == 0)
{
lean_ctor_set(v___x_2062_, 0, v___x_2065_);
v___x_2067_ = v___x_2062_;
goto v_reusejp_2066_;
}
else
{
lean_object* v_reuseFailAlloc_2068_; 
v_reuseFailAlloc_2068_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2068_, 0, v___x_2065_);
v___x_2067_ = v_reuseFailAlloc_2068_;
goto v_reusejp_2066_;
}
v_reusejp_2066_:
{
return v___x_2067_;
}
}
else
{
lean_object* v___x_2069_; lean_object* v___x_2070_; 
lean_dec(v_fst_2064_);
lean_del_object(v___x_2062_);
v___x_2069_ = lean_obj_once(&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___closed__2, &l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___closed__2_once, _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___closed__2);
v___x_2070_ = l_Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0___redArg(v___x_2069_, v_a_2035_, v_a_2036_, v_a_2037_, v_a_2038_);
return v___x_2070_;
}
}
}
else
{
lean_object* v_a_2072_; lean_object* v___x_2074_; uint8_t v_isShared_2075_; uint8_t v_isSharedCheck_2079_; 
v_a_2072_ = lean_ctor_get(v___x_2059_, 0);
v_isSharedCheck_2079_ = !lean_is_exclusive(v___x_2059_);
if (v_isSharedCheck_2079_ == 0)
{
v___x_2074_ = v___x_2059_;
v_isShared_2075_ = v_isSharedCheck_2079_;
goto v_resetjp_2073_;
}
else
{
lean_inc(v_a_2072_);
lean_dec(v___x_2059_);
v___x_2074_ = lean_box(0);
v_isShared_2075_ = v_isSharedCheck_2079_;
goto v_resetjp_2073_;
}
v_resetjp_2073_:
{
lean_object* v___x_2077_; 
if (v_isShared_2075_ == 0)
{
v___x_2077_ = v___x_2074_;
goto v_reusejp_2076_;
}
else
{
lean_object* v_reuseFailAlloc_2078_; 
v_reuseFailAlloc_2078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2078_, 0, v_a_2072_);
v___x_2077_ = v_reuseFailAlloc_2078_;
goto v_reusejp_2076_;
}
v_reusejp_2076_:
{
return v___x_2077_;
}
}
}
}
else
{
lean_object* v___x_2080_; lean_object* v___f_2081_; lean_object* v___x_2082_; lean_object* v___f_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; uint8_t v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; 
v___x_2080_ = lean_box(v_isZero_2048_);
v___f_2081_ = lean_alloc_closure((void*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2081_, 0, v___x_2080_);
v___x_2082_ = lean_box(v_isZero_2048_);
v___f_2083_ = lean_alloc_closure((void*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__2___boxed), 10, 1);
lean_closure_set(v___f_2083_, 0, v___x_2082_);
v___x_2084_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_run___boxed), 9, 2);
lean_closure_set(v___x_2084_, 0, v_mvar_2033_);
lean_closure_set(v___x_2084_, 1, v___f_2083_);
v___x_2085_ = lean_box(0);
v___x_2086_ = lean_box(0);
v___x_2087_ = 1;
v___x_2088_ = lean_box(1);
v___x_2089_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___closed__4));
v___x_2090_ = lean_alloc_ctor(0, 8, 11);
lean_ctor_set(v___x_2090_, 0, v___x_2085_);
lean_ctor_set(v___x_2090_, 1, v___x_2086_);
lean_ctor_set(v___x_2090_, 2, v___x_2085_);
lean_ctor_set(v___x_2090_, 3, v___f_2081_);
lean_ctor_set(v___x_2090_, 4, v___x_2088_);
lean_ctor_set(v___x_2090_, 5, v___x_2088_);
lean_ctor_set(v___x_2090_, 6, v___x_2085_);
lean_ctor_set(v___x_2090_, 7, v___x_2089_);
lean_ctor_set_uint8(v___x_2090_, sizeof(void*)*8, v___x_2087_);
lean_ctor_set_uint8(v___x_2090_, sizeof(void*)*8 + 1, v___x_2087_);
lean_ctor_set_uint8(v___x_2090_, sizeof(void*)*8 + 2, v___x_2087_);
lean_ctor_set_uint8(v___x_2090_, sizeof(void*)*8 + 3, v___x_2087_);
lean_ctor_set_uint8(v___x_2090_, sizeof(void*)*8 + 4, v_isZero_2048_);
lean_ctor_set_uint8(v___x_2090_, sizeof(void*)*8 + 5, v_isZero_2048_);
lean_ctor_set_uint8(v___x_2090_, sizeof(void*)*8 + 6, v_isZero_2048_);
lean_ctor_set_uint8(v___x_2090_, sizeof(void*)*8 + 7, v_isZero_2048_);
lean_ctor_set_uint8(v___x_2090_, sizeof(void*)*8 + 8, v___x_2087_);
lean_ctor_set_uint8(v___x_2090_, sizeof(void*)*8 + 9, v_isZero_2048_);
lean_ctor_set_uint8(v___x_2090_, sizeof(void*)*8 + 10, v___x_2087_);
v___x_2091_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___closed__6));
lean_inc_ref(v___x_2090_);
v___x_2092_ = l_Lean_Elab_Term_TermElabM_run___redArg(v___x_2084_, v___x_2090_, v___x_2091_, v_a_2035_, v_a_2036_, v_a_2037_, v_a_2038_);
if (lean_obj_tag(v___x_2092_) == 0)
{
lean_object* v_a_2093_; lean_object* v_fst_2094_; 
v_a_2093_ = lean_ctor_get(v___x_2092_, 0);
lean_inc(v_a_2093_);
lean_dec_ref(v___x_2092_);
v_fst_2094_ = lean_ctor_get(v_a_2093_, 0);
lean_inc(v_fst_2094_);
lean_dec(v_a_2093_);
if (lean_obj_tag(v_fst_2094_) == 1)
{
lean_object* v_tail_2095_; 
v_tail_2095_ = lean_ctor_get(v_fst_2094_, 1);
lean_inc(v_tail_2095_);
if (lean_obj_tag(v_tail_2095_) == 1)
{
lean_object* v_tail_2096_; 
v_tail_2096_ = lean_ctor_get(v_tail_2095_, 1);
if (lean_obj_tag(v_tail_2096_) == 0)
{
lean_object* v_head_2097_; lean_object* v_head_2098_; lean_object* v___x_2099_; lean_object* v___f_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; 
v_head_2097_ = lean_ctor_get(v_fst_2094_, 0);
lean_inc(v_head_2097_);
lean_dec_ref(v_fst_2094_);
v_head_2098_ = lean_ctor_get(v_tail_2095_, 0);
lean_inc(v_head_2098_);
lean_dec_ref(v_tail_2095_);
v___x_2099_ = lean_box(v_isZero_2048_);
v___f_2100_ = lean_alloc_closure((void*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__3___boxed), 10, 1);
lean_closure_set(v___f_2100_, 0, v___x_2099_);
v___x_2101_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_run___boxed), 9, 2);
lean_closure_set(v___x_2101_, 0, v_head_2097_);
lean_closure_set(v___x_2101_, 1, v___f_2100_);
v___x_2102_ = l_Lean_Elab_Term_TermElabM_run___redArg(v___x_2101_, v___x_2090_, v___x_2091_, v_a_2035_, v_a_2036_, v_a_2037_, v_a_2038_);
if (lean_obj_tag(v___x_2102_) == 0)
{
lean_object* v_a_2103_; lean_object* v_fst_2104_; 
v_a_2103_ = lean_ctor_get(v___x_2102_, 0);
lean_inc(v_a_2103_);
lean_dec_ref(v___x_2102_);
v_fst_2104_ = lean_ctor_get(v_a_2103_, 0);
lean_inc(v_fst_2104_);
lean_dec(v_a_2103_);
if (lean_obj_tag(v_fst_2104_) == 0)
{
lean_object* v_one_2105_; lean_object* v_n_2106_; 
v_one_2105_ = lean_unsigned_to_nat(1u);
v_n_2106_ = lean_nat_sub(v_n_2034_, v_one_2105_);
lean_dec(v_n_2034_);
v_mvar_2033_ = v_head_2098_;
v_n_2034_ = v_n_2106_;
goto _start;
}
else
{
lean_object* v___x_2108_; lean_object* v___x_2109_; 
lean_dec(v_fst_2104_);
lean_dec(v_head_2098_);
lean_dec(v_n_2034_);
v___x_2108_ = lean_obj_once(&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___closed__2, &l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___closed__2_once, _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___closed__2);
v___x_2109_ = l_Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0___redArg(v___x_2108_, v_a_2035_, v_a_2036_, v_a_2037_, v_a_2038_);
return v___x_2109_;
}
}
else
{
lean_object* v_a_2110_; lean_object* v___x_2112_; uint8_t v_isShared_2113_; uint8_t v_isSharedCheck_2117_; 
lean_dec(v_head_2098_);
lean_dec(v_n_2034_);
v_a_2110_ = lean_ctor_get(v___x_2102_, 0);
v_isSharedCheck_2117_ = !lean_is_exclusive(v___x_2102_);
if (v_isSharedCheck_2117_ == 0)
{
v___x_2112_ = v___x_2102_;
v_isShared_2113_ = v_isSharedCheck_2117_;
goto v_resetjp_2111_;
}
else
{
lean_inc(v_a_2110_);
lean_dec(v___x_2102_);
v___x_2112_ = lean_box(0);
v_isShared_2113_ = v_isSharedCheck_2117_;
goto v_resetjp_2111_;
}
v_resetjp_2111_:
{
lean_object* v___x_2115_; 
if (v_isShared_2113_ == 0)
{
v___x_2115_ = v___x_2112_;
goto v_reusejp_2114_;
}
else
{
lean_object* v_reuseFailAlloc_2116_; 
v_reuseFailAlloc_2116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2116_, 0, v_a_2110_);
v___x_2115_ = v_reuseFailAlloc_2116_;
goto v_reusejp_2114_;
}
v_reusejp_2114_:
{
return v___x_2115_;
}
}
}
}
else
{
lean_dec_ref(v_tail_2095_);
lean_dec_ref(v_fst_2094_);
lean_dec_ref(v___x_2090_);
lean_dec(v_n_2034_);
v___y_2041_ = v_a_2035_;
v___y_2042_ = v_a_2036_;
v___y_2043_ = v_a_2037_;
v___y_2044_ = v_a_2038_;
goto v___jp_2040_;
}
}
else
{
lean_dec(v_tail_2095_);
lean_dec_ref(v_fst_2094_);
lean_dec_ref(v___x_2090_);
lean_dec(v_n_2034_);
v___y_2041_ = v_a_2035_;
v___y_2042_ = v_a_2036_;
v___y_2043_ = v_a_2037_;
v___y_2044_ = v_a_2038_;
goto v___jp_2040_;
}
}
else
{
lean_dec(v_fst_2094_);
lean_dec_ref(v___x_2090_);
lean_dec(v_n_2034_);
v___y_2041_ = v_a_2035_;
v___y_2042_ = v_a_2036_;
v___y_2043_ = v_a_2037_;
v___y_2044_ = v_a_2038_;
goto v___jp_2040_;
}
}
else
{
lean_object* v_a_2118_; lean_object* v___x_2120_; uint8_t v_isShared_2121_; uint8_t v_isSharedCheck_2125_; 
lean_dec_ref(v___x_2090_);
lean_dec(v_n_2034_);
v_a_2118_ = lean_ctor_get(v___x_2092_, 0);
v_isSharedCheck_2125_ = !lean_is_exclusive(v___x_2092_);
if (v_isSharedCheck_2125_ == 0)
{
v___x_2120_ = v___x_2092_;
v_isShared_2121_ = v_isSharedCheck_2125_;
goto v_resetjp_2119_;
}
else
{
lean_inc(v_a_2118_);
lean_dec(v___x_2092_);
v___x_2120_ = lean_box(0);
v_isShared_2121_ = v_isSharedCheck_2125_;
goto v_resetjp_2119_;
}
v_resetjp_2119_:
{
lean_object* v___x_2123_; 
if (v_isShared_2121_ == 0)
{
v___x_2123_ = v___x_2120_;
goto v_reusejp_2122_;
}
else
{
lean_object* v_reuseFailAlloc_2124_; 
v_reuseFailAlloc_2124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2124_, 0, v_a_2118_);
v___x_2123_ = v_reuseFailAlloc_2124_;
goto v_reusejp_2122_;
}
v_reusejp_2122_:
{
return v___x_2123_;
}
}
}
}
v___jp_2040_:
{
lean_object* v___x_2045_; lean_object* v___x_2046_; 
v___x_2045_ = lean_obj_once(&l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___closed__1, &l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___closed__1_once, _init_l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___closed__1);
v___x_2046_ = l_Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0___redArg(v___x_2045_, v___y_2041_, v___y_2042_, v___y_2043_, v___y_2044_);
return v___x_2046_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___boxed(lean_object* v_mvar_2126_, lean_object* v_n_2127_, lean_object* v_a_2128_, lean_object* v_a_2129_, lean_object* v_a_2130_, lean_object* v_a_2131_, lean_object* v_a_2132_){
_start:
{
lean_object* v_res_2133_; 
v_res_2133_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor(v_mvar_2126_, v_n_2127_, v_a_2128_, v_a_2129_, v_a_2130_, v_a_2131_);
lean_dec(v_a_2131_);
lean_dec_ref(v_a_2130_);
lean_dec(v_a_2129_);
lean_dec_ref(v_a_2128_);
return v_res_2133_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toCases_spec__0(lean_object* v_a_2134_, lean_object* v_a_2135_){
_start:
{
if (lean_obj_tag(v_a_2134_) == 0)
{
lean_object* v___x_2136_; 
v___x_2136_ = lean_array_to_list(v_a_2135_);
return v___x_2136_;
}
else
{
lean_object* v_head_2137_; lean_object* v_fst_2138_; uint8_t v___x_2139_; 
v_head_2137_ = lean_ctor_get(v_a_2134_, 0);
v_fst_2138_ = lean_ctor_get(v_head_2137_, 0);
v___x_2139_ = lean_unbox(v_fst_2138_);
if (v___x_2139_ == 0)
{
lean_object* v_tail_2140_; 
v_tail_2140_ = lean_ctor_get(v_a_2134_, 1);
lean_inc(v_tail_2140_);
lean_dec_ref(v_a_2134_);
v_a_2134_ = v_tail_2140_;
goto _start;
}
else
{
lean_object* v_tail_2142_; lean_object* v_snd_2143_; lean_object* v___x_2144_; 
lean_inc(v_head_2137_);
v_tail_2142_ = lean_ctor_get(v_a_2134_, 1);
lean_inc(v_tail_2142_);
lean_dec_ref(v_a_2134_);
v_snd_2143_ = lean_ctor_get(v_head_2137_, 1);
lean_inc(v_snd_2143_);
lean_dec(v_head_2137_);
v___x_2144_ = lean_array_push(v_a_2135_, v_snd_2143_);
v_a_2134_ = v_tail_2142_;
v_a_2135_ = v___x_2144_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toCases_spec__1(lean_object* v_a_2146_, lean_object* v_x_2147_, lean_object* v_x_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_){
_start:
{
if (lean_obj_tag(v_x_2147_) == 0)
{
lean_object* v___x_2154_; lean_object* v___x_2155_; 
v___x_2154_ = l_List_reverse___redArg(v_x_2148_);
v___x_2155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2155_, 0, v___x_2154_);
return v___x_2155_;
}
else
{
lean_object* v_head_2156_; lean_object* v_tail_2157_; lean_object* v___x_2159_; uint8_t v_isShared_2160_; uint8_t v_isSharedCheck_2231_; 
v_head_2156_ = lean_ctor_get(v_x_2147_, 0);
v_tail_2157_ = lean_ctor_get(v_x_2147_, 1);
v_isSharedCheck_2231_ = !lean_is_exclusive(v_x_2147_);
if (v_isSharedCheck_2231_ == 0)
{
v___x_2159_ = v_x_2147_;
v_isShared_2160_ = v_isSharedCheck_2231_;
goto v_resetjp_2158_;
}
else
{
lean_inc(v_tail_2157_);
lean_inc(v_head_2156_);
lean_dec(v_x_2147_);
v___x_2159_ = lean_box(0);
v_isShared_2160_ = v_isSharedCheck_2231_;
goto v_resetjp_2158_;
}
v_resetjp_2158_:
{
lean_object* v___y_2162_; lean_object* v_fst_2176_; lean_object* v_fst_2177_; lean_object* v_snd_2178_; lean_object* v_toInductionSubgoal_2179_; lean_object* v_snd_2180_; lean_object* v_variablesKept_2181_; lean_object* v_neqs_2182_; lean_object* v_mvarId_2183_; lean_object* v_fields_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; 
v_fst_2176_ = lean_ctor_get(v_head_2156_, 0);
v_fst_2177_ = lean_ctor_get(v_fst_2176_, 0);
lean_inc(v_fst_2177_);
v_snd_2178_ = lean_ctor_get(v_fst_2176_, 1);
v_toInductionSubgoal_2179_ = lean_ctor_get(v_snd_2178_, 0);
lean_inc_ref(v_toInductionSubgoal_2179_);
v_snd_2180_ = lean_ctor_get(v_head_2156_, 1);
lean_inc(v_snd_2180_);
lean_dec(v_head_2156_);
v_variablesKept_2181_ = lean_ctor_get(v_fst_2177_, 0);
lean_inc(v_variablesKept_2181_);
v_neqs_2182_ = lean_ctor_get(v_fst_2177_, 1);
lean_inc(v_neqs_2182_);
lean_dec(v_fst_2177_);
v_mvarId_2183_ = lean_ctor_get(v_toInductionSubgoal_2179_, 0);
lean_inc(v_mvarId_2183_);
v_fields_2184_ = lean_ctor_get(v_toInductionSubgoal_2179_, 1);
lean_inc_ref(v_fields_2184_);
lean_dec_ref(v_toInductionSubgoal_2179_);
v___x_2185_ = lean_array_get_size(v_a_2146_);
v___x_2186_ = lean_unsigned_to_nat(1u);
v___x_2187_ = lean_nat_sub(v___x_2185_, v___x_2186_);
v___x_2188_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select(v_snd_2180_, v___x_2187_, v_mvarId_2183_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_);
if (lean_obj_tag(v___x_2188_) == 0)
{
lean_object* v_a_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; 
v_a_2189_ = lean_ctor_get(v___x_2188_, 0);
lean_inc(v_a_2189_);
lean_dec_ref(v___x_2188_);
lean_inc_ref(v_fields_2184_);
v___x_2190_ = lean_array_to_list(v_fields_2184_);
lean_inc(v_variablesKept_2181_);
v___x_2191_ = l_List_zipWith___at___00List_zip_spec__0(lean_box(0), lean_box(0), v_variablesKept_2181_, v___x_2190_);
v___x_2192_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__1___closed__1));
v___x_2193_ = l_List_filterMapTR_go___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toCases_spec__0(v___x_2191_, v___x_2192_);
if (lean_obj_tag(v_neqs_2182_) == 0)
{
lean_object* v___x_2194_; lean_object* v___x_2195_; 
v___x_2194_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_List_init___redArg(v___x_2193_);
v___x_2195_ = l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2(v_a_2189_, v___x_2194_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_);
if (lean_obj_tag(v___x_2195_) == 0)
{
lean_object* v_a_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; 
v_a_2196_ = lean_ctor_get(v___x_2195_, 0);
lean_inc(v_a_2196_);
lean_dec_ref(v___x_2195_);
v___x_2197_ = l_Lean_instInhabitedExpr;
v___x_2198_ = l_List_lengthTR___redArg(v_variablesKept_2181_);
lean_dec(v_variablesKept_2181_);
v___x_2199_ = lean_nat_sub(v___x_2198_, v___x_2186_);
lean_dec(v___x_2198_);
v___x_2200_ = lean_array_get(v___x_2197_, v_fields_2184_, v___x_2199_);
lean_dec(v___x_2199_);
lean_dec_ref(v_fields_2184_);
v___x_2201_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1___redArg(v_a_2196_, v___x_2200_, v___y_2150_);
v___y_2162_ = v___x_2201_;
goto v___jp_2161_;
}
else
{
lean_object* v_a_2202_; lean_object* v___x_2204_; uint8_t v_isShared_2205_; uint8_t v_isSharedCheck_2209_; 
lean_dec_ref(v_fields_2184_);
lean_dec(v_variablesKept_2181_);
lean_del_object(v___x_2159_);
lean_dec(v_tail_2157_);
lean_dec(v_x_2148_);
v_a_2202_ = lean_ctor_get(v___x_2195_, 0);
v_isSharedCheck_2209_ = !lean_is_exclusive(v___x_2195_);
if (v_isSharedCheck_2209_ == 0)
{
v___x_2204_ = v___x_2195_;
v_isShared_2205_ = v_isSharedCheck_2209_;
goto v_resetjp_2203_;
}
else
{
lean_inc(v_a_2202_);
lean_dec(v___x_2195_);
v___x_2204_ = lean_box(0);
v_isShared_2205_ = v_isSharedCheck_2209_;
goto v_resetjp_2203_;
}
v_resetjp_2203_:
{
lean_object* v___x_2207_; 
if (v_isShared_2205_ == 0)
{
v___x_2207_ = v___x_2204_;
goto v_reusejp_2206_;
}
else
{
lean_object* v_reuseFailAlloc_2208_; 
v_reuseFailAlloc_2208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2208_, 0, v_a_2202_);
v___x_2207_ = v_reuseFailAlloc_2208_;
goto v_reusejp_2206_;
}
v_reusejp_2206_:
{
return v___x_2207_;
}
}
}
}
else
{
lean_object* v_val_2210_; lean_object* v___x_2211_; 
lean_dec_ref(v_fields_2184_);
lean_dec(v_variablesKept_2181_);
v_val_2210_ = lean_ctor_get(v_neqs_2182_, 0);
lean_inc(v_val_2210_);
lean_dec_ref(v_neqs_2182_);
v___x_2211_ = l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2(v_a_2189_, v___x_2193_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_);
if (lean_obj_tag(v___x_2211_) == 0)
{
lean_object* v_a_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; 
v_a_2212_ = lean_ctor_get(v___x_2211_, 0);
lean_inc(v_a_2212_);
lean_dec_ref(v___x_2211_);
v___x_2213_ = lean_nat_sub(v_val_2210_, v___x_2186_);
lean_dec(v_val_2210_);
v___x_2214_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor(v_a_2212_, v___x_2213_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_);
v___y_2162_ = v___x_2214_;
goto v___jp_2161_;
}
else
{
lean_object* v_a_2215_; lean_object* v___x_2217_; uint8_t v_isShared_2218_; uint8_t v_isSharedCheck_2222_; 
lean_dec(v_val_2210_);
lean_del_object(v___x_2159_);
lean_dec(v_tail_2157_);
lean_dec(v_x_2148_);
v_a_2215_ = lean_ctor_get(v___x_2211_, 0);
v_isSharedCheck_2222_ = !lean_is_exclusive(v___x_2211_);
if (v_isSharedCheck_2222_ == 0)
{
v___x_2217_ = v___x_2211_;
v_isShared_2218_ = v_isSharedCheck_2222_;
goto v_resetjp_2216_;
}
else
{
lean_inc(v_a_2215_);
lean_dec(v___x_2211_);
v___x_2217_ = lean_box(0);
v_isShared_2218_ = v_isSharedCheck_2222_;
goto v_resetjp_2216_;
}
v_resetjp_2216_:
{
lean_object* v___x_2220_; 
if (v_isShared_2218_ == 0)
{
v___x_2220_ = v___x_2217_;
goto v_reusejp_2219_;
}
else
{
lean_object* v_reuseFailAlloc_2221_; 
v_reuseFailAlloc_2221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2221_, 0, v_a_2215_);
v___x_2220_ = v_reuseFailAlloc_2221_;
goto v_reusejp_2219_;
}
v_reusejp_2219_:
{
return v___x_2220_;
}
}
}
}
}
else
{
lean_object* v_a_2223_; lean_object* v___x_2225_; uint8_t v_isShared_2226_; uint8_t v_isSharedCheck_2230_; 
lean_dec_ref(v_fields_2184_);
lean_dec(v_neqs_2182_);
lean_dec(v_variablesKept_2181_);
lean_del_object(v___x_2159_);
lean_dec(v_tail_2157_);
lean_dec(v_x_2148_);
v_a_2223_ = lean_ctor_get(v___x_2188_, 0);
v_isSharedCheck_2230_ = !lean_is_exclusive(v___x_2188_);
if (v_isSharedCheck_2230_ == 0)
{
v___x_2225_ = v___x_2188_;
v_isShared_2226_ = v_isSharedCheck_2230_;
goto v_resetjp_2224_;
}
else
{
lean_inc(v_a_2223_);
lean_dec(v___x_2188_);
v___x_2225_ = lean_box(0);
v_isShared_2226_ = v_isSharedCheck_2230_;
goto v_resetjp_2224_;
}
v_resetjp_2224_:
{
lean_object* v___x_2228_; 
if (v_isShared_2226_ == 0)
{
v___x_2228_ = v___x_2225_;
goto v_reusejp_2227_;
}
else
{
lean_object* v_reuseFailAlloc_2229_; 
v_reuseFailAlloc_2229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2229_, 0, v_a_2223_);
v___x_2228_ = v_reuseFailAlloc_2229_;
goto v_reusejp_2227_;
}
v_reusejp_2227_:
{
return v___x_2228_;
}
}
}
v___jp_2161_:
{
if (lean_obj_tag(v___y_2162_) == 0)
{
lean_object* v_a_2163_; lean_object* v___x_2165_; 
v_a_2163_ = lean_ctor_get(v___y_2162_, 0);
lean_inc(v_a_2163_);
lean_dec_ref(v___y_2162_);
if (v_isShared_2160_ == 0)
{
lean_ctor_set(v___x_2159_, 1, v_x_2148_);
lean_ctor_set(v___x_2159_, 0, v_a_2163_);
v___x_2165_ = v___x_2159_;
goto v_reusejp_2164_;
}
else
{
lean_object* v_reuseFailAlloc_2167_; 
v_reuseFailAlloc_2167_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2167_, 0, v_a_2163_);
lean_ctor_set(v_reuseFailAlloc_2167_, 1, v_x_2148_);
v___x_2165_ = v_reuseFailAlloc_2167_;
goto v_reusejp_2164_;
}
v_reusejp_2164_:
{
v_x_2147_ = v_tail_2157_;
v_x_2148_ = v___x_2165_;
goto _start;
}
}
else
{
lean_object* v_a_2168_; lean_object* v___x_2170_; uint8_t v_isShared_2171_; uint8_t v_isSharedCheck_2175_; 
lean_del_object(v___x_2159_);
lean_dec(v_tail_2157_);
lean_dec(v_x_2148_);
v_a_2168_ = lean_ctor_get(v___y_2162_, 0);
v_isSharedCheck_2175_ = !lean_is_exclusive(v___y_2162_);
if (v_isSharedCheck_2175_ == 0)
{
v___x_2170_ = v___y_2162_;
v_isShared_2171_ = v_isSharedCheck_2175_;
goto v_resetjp_2169_;
}
else
{
lean_inc(v_a_2168_);
lean_dec(v___y_2162_);
v___x_2170_ = lean_box(0);
v_isShared_2171_ = v_isSharedCheck_2175_;
goto v_resetjp_2169_;
}
v_resetjp_2169_:
{
lean_object* v___x_2173_; 
if (v_isShared_2171_ == 0)
{
v___x_2173_ = v___x_2170_;
goto v_reusejp_2172_;
}
else
{
lean_object* v_reuseFailAlloc_2174_; 
v_reuseFailAlloc_2174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2174_, 0, v_a_2168_);
v___x_2173_ = v_reuseFailAlloc_2174_;
goto v_reusejp_2172_;
}
v_reusejp_2172_:
{
return v___x_2173_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toCases_spec__1___boxed(lean_object* v_a_2232_, lean_object* v_x_2233_, lean_object* v_x_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_){
_start:
{
lean_object* v_res_2240_; 
v_res_2240_ = l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toCases_spec__1(v_a_2232_, v_x_2233_, v_x_2234_, v___y_2235_, v___y_2236_, v___y_2237_, v___y_2238_);
lean_dec(v___y_2238_);
lean_dec_ref(v___y_2237_);
lean_dec(v___y_2236_);
lean_dec_ref(v___y_2235_);
lean_dec_ref(v_a_2232_);
return v_res_2240_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toCases(lean_object* v_mvar_2243_, lean_object* v_shape_2244_, lean_object* v_a_2245_, lean_object* v_a_2246_, lean_object* v_a_2247_, lean_object* v_a_2248_){
_start:
{
uint8_t v___x_2250_; lean_object* v___x_2251_; 
v___x_2250_ = 0;
v___x_2251_ = l_Lean_Meta_intro1Core(v_mvar_2243_, v___x_2250_, v_a_2245_, v_a_2246_, v_a_2247_, v_a_2248_);
if (lean_obj_tag(v___x_2251_) == 0)
{
lean_object* v_a_2252_; lean_object* v_fst_2253_; lean_object* v_snd_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; 
v_a_2252_ = lean_ctor_get(v___x_2251_, 0);
lean_inc(v_a_2252_);
lean_dec_ref(v___x_2251_);
v_fst_2253_ = lean_ctor_get(v_a_2252_, 0);
lean_inc(v_fst_2253_);
v_snd_2254_ = lean_ctor_get(v_a_2252_, 1);
lean_inc(v_snd_2254_);
lean_dec(v_a_2252_);
v___x_2255_ = lean_unsigned_to_nat(0u);
v___x_2256_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toCases___closed__0));
v___x_2257_ = lean_box(0);
v___x_2258_ = l_Lean_MVarId_cases(v_snd_2254_, v_fst_2253_, v___x_2256_, v___x_2250_, v___x_2257_, v_a_2245_, v_a_2246_, v_a_2247_, v_a_2248_);
if (lean_obj_tag(v___x_2258_) == 0)
{
lean_object* v_a_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; 
v_a_2259_ = lean_ctor_get(v___x_2258_, 0);
lean_inc_n(v_a_2259_, 2);
lean_dec_ref(v___x_2258_);
v___x_2260_ = lean_array_to_list(v_a_2259_);
v___x_2261_ = l_List_zipWith___at___00List_zip_spec__0(lean_box(0), lean_box(0), v_shape_2244_, v___x_2260_);
v___x_2262_ = l_List_zipIdxTR___redArg(v___x_2261_, v___x_2255_);
v___x_2263_ = lean_box(0);
v___x_2264_ = l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toCases_spec__1(v_a_2259_, v___x_2262_, v___x_2263_, v_a_2245_, v_a_2246_, v_a_2247_, v_a_2248_);
lean_dec(v_a_2259_);
if (lean_obj_tag(v___x_2264_) == 0)
{
lean_object* v___x_2266_; uint8_t v_isShared_2267_; uint8_t v_isSharedCheck_2272_; 
v_isSharedCheck_2272_ = !lean_is_exclusive(v___x_2264_);
if (v_isSharedCheck_2272_ == 0)
{
lean_object* v_unused_2273_; 
v_unused_2273_ = lean_ctor_get(v___x_2264_, 0);
lean_dec(v_unused_2273_);
v___x_2266_ = v___x_2264_;
v_isShared_2267_ = v_isSharedCheck_2272_;
goto v_resetjp_2265_;
}
else
{
lean_dec(v___x_2264_);
v___x_2266_ = lean_box(0);
v_isShared_2267_ = v_isSharedCheck_2272_;
goto v_resetjp_2265_;
}
v_resetjp_2265_:
{
lean_object* v___x_2268_; lean_object* v___x_2270_; 
v___x_2268_ = lean_box(0);
if (v_isShared_2267_ == 0)
{
lean_ctor_set(v___x_2266_, 0, v___x_2268_);
v___x_2270_ = v___x_2266_;
goto v_reusejp_2269_;
}
else
{
lean_object* v_reuseFailAlloc_2271_; 
v_reuseFailAlloc_2271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2271_, 0, v___x_2268_);
v___x_2270_ = v_reuseFailAlloc_2271_;
goto v_reusejp_2269_;
}
v_reusejp_2269_:
{
return v___x_2270_;
}
}
}
else
{
lean_object* v_a_2274_; lean_object* v___x_2276_; uint8_t v_isShared_2277_; uint8_t v_isSharedCheck_2281_; 
v_a_2274_ = lean_ctor_get(v___x_2264_, 0);
v_isSharedCheck_2281_ = !lean_is_exclusive(v___x_2264_);
if (v_isSharedCheck_2281_ == 0)
{
v___x_2276_ = v___x_2264_;
v_isShared_2277_ = v_isSharedCheck_2281_;
goto v_resetjp_2275_;
}
else
{
lean_inc(v_a_2274_);
lean_dec(v___x_2264_);
v___x_2276_ = lean_box(0);
v_isShared_2277_ = v_isSharedCheck_2281_;
goto v_resetjp_2275_;
}
v_resetjp_2275_:
{
lean_object* v___x_2279_; 
if (v_isShared_2277_ == 0)
{
v___x_2279_ = v___x_2276_;
goto v_reusejp_2278_;
}
else
{
lean_object* v_reuseFailAlloc_2280_; 
v_reuseFailAlloc_2280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2280_, 0, v_a_2274_);
v___x_2279_ = v_reuseFailAlloc_2280_;
goto v_reusejp_2278_;
}
v_reusejp_2278_:
{
return v___x_2279_;
}
}
}
}
else
{
lean_object* v_a_2282_; lean_object* v___x_2284_; uint8_t v_isShared_2285_; uint8_t v_isSharedCheck_2289_; 
lean_dec(v_shape_2244_);
v_a_2282_ = lean_ctor_get(v___x_2258_, 0);
v_isSharedCheck_2289_ = !lean_is_exclusive(v___x_2258_);
if (v_isSharedCheck_2289_ == 0)
{
v___x_2284_ = v___x_2258_;
v_isShared_2285_ = v_isSharedCheck_2289_;
goto v_resetjp_2283_;
}
else
{
lean_inc(v_a_2282_);
lean_dec(v___x_2258_);
v___x_2284_ = lean_box(0);
v_isShared_2285_ = v_isSharedCheck_2289_;
goto v_resetjp_2283_;
}
v_resetjp_2283_:
{
lean_object* v___x_2287_; 
if (v_isShared_2285_ == 0)
{
v___x_2287_ = v___x_2284_;
goto v_reusejp_2286_;
}
else
{
lean_object* v_reuseFailAlloc_2288_; 
v_reuseFailAlloc_2288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2288_, 0, v_a_2282_);
v___x_2287_ = v_reuseFailAlloc_2288_;
goto v_reusejp_2286_;
}
v_reusejp_2286_:
{
return v___x_2287_;
}
}
}
}
else
{
lean_object* v_a_2290_; lean_object* v___x_2292_; uint8_t v_isShared_2293_; uint8_t v_isSharedCheck_2297_; 
lean_dec(v_shape_2244_);
v_a_2290_ = lean_ctor_get(v___x_2251_, 0);
v_isSharedCheck_2297_ = !lean_is_exclusive(v___x_2251_);
if (v_isSharedCheck_2297_ == 0)
{
v___x_2292_ = v___x_2251_;
v_isShared_2293_ = v_isSharedCheck_2297_;
goto v_resetjp_2291_;
}
else
{
lean_inc(v_a_2290_);
lean_dec(v___x_2251_);
v___x_2292_ = lean_box(0);
v_isShared_2293_ = v_isSharedCheck_2297_;
goto v_resetjp_2291_;
}
v_resetjp_2291_:
{
lean_object* v___x_2295_; 
if (v_isShared_2293_ == 0)
{
v___x_2295_ = v___x_2292_;
goto v_reusejp_2294_;
}
else
{
lean_object* v_reuseFailAlloc_2296_; 
v_reuseFailAlloc_2296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2296_, 0, v_a_2290_);
v___x_2295_ = v_reuseFailAlloc_2296_;
goto v_reusejp_2294_;
}
v_reusejp_2294_:
{
return v___x_2295_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toCases___boxed(lean_object* v_mvar_2298_, lean_object* v_shape_2299_, lean_object* v_a_2300_, lean_object* v_a_2301_, lean_object* v_a_2302_, lean_object* v_a_2303_, lean_object* v_a_2304_){
_start:
{
lean_object* v_res_2305_; 
v_res_2305_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toCases(v_mvar_2298_, v_shape_2299_, v_a_2300_, v_a_2301_, v_a_2302_, v_a_2303_);
lean_dec(v_a_2303_);
lean_dec_ref(v_a_2302_);
lean_dec(v_a_2301_);
lean_dec_ref(v_a_2300_);
return v_res_2305_;
}
}
static lean_object* _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesSum___closed__1(void){
_start:
{
lean_object* v___x_2307_; lean_object* v___x_2308_; 
v___x_2307_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesSum___closed__0));
v___x_2308_ = l_Lean_stringToMessageData(v___x_2307_);
return v___x_2308_;
}
}
static lean_object* _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesSum___closed__3(void){
_start:
{
lean_object* v___x_2310_; lean_object* v___x_2311_; 
v___x_2310_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesSum___closed__2));
v___x_2311_ = l_Lean_stringToMessageData(v___x_2310_);
return v___x_2311_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesSum(lean_object* v_n_2312_, lean_object* v_mvar_2313_, lean_object* v_h_2314_, lean_object* v_a_2315_, lean_object* v_a_2316_, lean_object* v_a_2317_, lean_object* v_a_2318_){
_start:
{
lean_object* v___y_2321_; lean_object* v___y_2322_; lean_object* v___y_2323_; lean_object* v___y_2324_; lean_object* v___y_2328_; lean_object* v___y_2329_; lean_object* v___y_2330_; lean_object* v___y_2331_; lean_object* v_zero_2334_; uint8_t v_isZero_2335_; 
v_zero_2334_ = lean_unsigned_to_nat(0u);
v_isZero_2335_ = lean_nat_dec_eq(v_n_2312_, v_zero_2334_);
if (v_isZero_2335_ == 1)
{
lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; 
v___x_2336_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2336_, 0, v_h_2314_);
lean_ctor_set(v___x_2336_, 1, v_mvar_2313_);
v___x_2337_ = lean_box(0);
v___x_2338_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2338_, 0, v___x_2336_);
lean_ctor_set(v___x_2338_, 1, v___x_2337_);
v___x_2339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2339_, 0, v___x_2338_);
return v___x_2339_;
}
else
{
lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; 
v___x_2340_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toCases___closed__0));
v___x_2341_ = lean_box(0);
v___x_2342_ = l_Lean_MVarId_cases(v_mvar_2313_, v_h_2314_, v___x_2340_, v_isZero_2335_, v___x_2341_, v_a_2315_, v_a_2316_, v_a_2317_, v_a_2318_);
if (lean_obj_tag(v___x_2342_) == 0)
{
lean_object* v_a_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; uint8_t v___x_2346_; 
v_a_2343_ = lean_ctor_get(v___x_2342_, 0);
lean_inc(v_a_2343_);
lean_dec_ref(v___x_2342_);
v___x_2344_ = lean_array_get_size(v_a_2343_);
v___x_2345_ = lean_unsigned_to_nat(2u);
v___x_2346_ = lean_nat_dec_eq(v___x_2344_, v___x_2345_);
if (v___x_2346_ == 0)
{
lean_object* v___x_2347_; lean_object* v___x_2348_; 
lean_dec(v_a_2343_);
v___x_2347_ = lean_obj_once(&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesSum___closed__3, &l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesSum___closed__3_once, _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesSum___closed__3);
v___x_2348_ = l_Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0___redArg(v___x_2347_, v_a_2315_, v_a_2316_, v_a_2317_, v_a_2318_);
return v___x_2348_;
}
else
{
lean_object* v___x_2349_; lean_object* v_toInductionSubgoal_2350_; lean_object* v___x_2352_; uint8_t v_isShared_2353_; uint8_t v_isSharedCheck_2390_; 
v___x_2349_ = lean_array_fget(v_a_2343_, v_zero_2334_);
v_toInductionSubgoal_2350_ = lean_ctor_get(v___x_2349_, 0);
v_isSharedCheck_2390_ = !lean_is_exclusive(v___x_2349_);
if (v_isSharedCheck_2390_ == 0)
{
lean_object* v_unused_2391_; 
v_unused_2391_ = lean_ctor_get(v___x_2349_, 1);
lean_dec(v_unused_2391_);
v___x_2352_ = v___x_2349_;
v_isShared_2353_ = v_isSharedCheck_2390_;
goto v_resetjp_2351_;
}
else
{
lean_inc(v_toInductionSubgoal_2350_);
lean_dec(v___x_2349_);
v___x_2352_ = lean_box(0);
v_isShared_2353_ = v_isSharedCheck_2390_;
goto v_resetjp_2351_;
}
v_resetjp_2351_:
{
lean_object* v_mvarId_2354_; lean_object* v_fields_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; uint8_t v___x_2358_; 
v_mvarId_2354_ = lean_ctor_get(v_toInductionSubgoal_2350_, 0);
lean_inc(v_mvarId_2354_);
v_fields_2355_ = lean_ctor_get(v_toInductionSubgoal_2350_, 1);
lean_inc_ref(v_fields_2355_);
lean_dec_ref(v_toInductionSubgoal_2350_);
v___x_2356_ = lean_array_get_size(v_fields_2355_);
v___x_2357_ = lean_unsigned_to_nat(1u);
v___x_2358_ = lean_nat_dec_eq(v___x_2356_, v___x_2357_);
if (v___x_2358_ == 0)
{
lean_dec_ref(v_fields_2355_);
lean_dec(v_mvarId_2354_);
lean_del_object(v___x_2352_);
lean_dec(v_a_2343_);
v___y_2321_ = v_a_2315_;
v___y_2322_ = v_a_2316_;
v___y_2323_ = v_a_2317_;
v___y_2324_ = v_a_2318_;
goto v___jp_2320_;
}
else
{
lean_object* v___x_2359_; 
v___x_2359_ = lean_array_fget(v_fields_2355_, v_zero_2334_);
lean_dec_ref(v_fields_2355_);
if (lean_obj_tag(v___x_2359_) == 1)
{
lean_object* v_fvarId_2360_; lean_object* v___x_2361_; lean_object* v_toInductionSubgoal_2362_; lean_object* v___x_2364_; uint8_t v_isShared_2365_; uint8_t v_isSharedCheck_2388_; 
v_fvarId_2360_ = lean_ctor_get(v___x_2359_, 0);
lean_inc(v_fvarId_2360_);
lean_dec_ref(v___x_2359_);
v___x_2361_ = lean_array_fget(v_a_2343_, v___x_2357_);
lean_dec(v_a_2343_);
v_toInductionSubgoal_2362_ = lean_ctor_get(v___x_2361_, 0);
v_isSharedCheck_2388_ = !lean_is_exclusive(v___x_2361_);
if (v_isSharedCheck_2388_ == 0)
{
lean_object* v_unused_2389_; 
v_unused_2389_ = lean_ctor_get(v___x_2361_, 1);
lean_dec(v_unused_2389_);
v___x_2364_ = v___x_2361_;
v_isShared_2365_ = v_isSharedCheck_2388_;
goto v_resetjp_2363_;
}
else
{
lean_inc(v_toInductionSubgoal_2362_);
lean_dec(v___x_2361_);
v___x_2364_ = lean_box(0);
v_isShared_2365_ = v_isSharedCheck_2388_;
goto v_resetjp_2363_;
}
v_resetjp_2363_:
{
lean_object* v_mvarId_2366_; lean_object* v_fields_2367_; lean_object* v___x_2368_; uint8_t v___x_2369_; 
v_mvarId_2366_ = lean_ctor_get(v_toInductionSubgoal_2362_, 0);
lean_inc(v_mvarId_2366_);
v_fields_2367_ = lean_ctor_get(v_toInductionSubgoal_2362_, 1);
lean_inc_ref(v_fields_2367_);
lean_dec_ref(v_toInductionSubgoal_2362_);
v___x_2368_ = lean_array_get_size(v_fields_2367_);
v___x_2369_ = lean_nat_dec_eq(v___x_2368_, v___x_2357_);
if (v___x_2369_ == 0)
{
lean_dec_ref(v_fields_2367_);
lean_dec(v_mvarId_2366_);
lean_del_object(v___x_2364_);
lean_dec(v_fvarId_2360_);
lean_dec(v_mvarId_2354_);
lean_del_object(v___x_2352_);
v___y_2328_ = v_a_2315_;
v___y_2329_ = v_a_2316_;
v___y_2330_ = v_a_2317_;
v___y_2331_ = v_a_2318_;
goto v___jp_2327_;
}
else
{
lean_object* v___x_2370_; 
v___x_2370_ = lean_array_fget(v_fields_2367_, v_zero_2334_);
lean_dec_ref(v_fields_2367_);
if (lean_obj_tag(v___x_2370_) == 1)
{
lean_object* v_fvarId_2371_; lean_object* v_n_2372_; lean_object* v___x_2373_; 
v_fvarId_2371_ = lean_ctor_get(v___x_2370_, 0);
lean_inc(v_fvarId_2371_);
lean_dec_ref(v___x_2370_);
v_n_2372_ = lean_nat_sub(v_n_2312_, v___x_2357_);
v___x_2373_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesSum(v_n_2372_, v_mvarId_2366_, v_fvarId_2371_, v_a_2315_, v_a_2316_, v_a_2317_, v_a_2318_);
lean_dec(v_n_2372_);
if (lean_obj_tag(v___x_2373_) == 0)
{
lean_object* v_a_2374_; lean_object* v___x_2376_; uint8_t v_isShared_2377_; uint8_t v_isSharedCheck_2387_; 
v_a_2374_ = lean_ctor_get(v___x_2373_, 0);
v_isSharedCheck_2387_ = !lean_is_exclusive(v___x_2373_);
if (v_isSharedCheck_2387_ == 0)
{
v___x_2376_ = v___x_2373_;
v_isShared_2377_ = v_isSharedCheck_2387_;
goto v_resetjp_2375_;
}
else
{
lean_inc(v_a_2374_);
lean_dec(v___x_2373_);
v___x_2376_ = lean_box(0);
v_isShared_2377_ = v_isSharedCheck_2387_;
goto v_resetjp_2375_;
}
v_resetjp_2375_:
{
lean_object* v___x_2379_; 
if (v_isShared_2365_ == 0)
{
lean_ctor_set(v___x_2364_, 1, v_mvarId_2354_);
lean_ctor_set(v___x_2364_, 0, v_fvarId_2360_);
v___x_2379_ = v___x_2364_;
goto v_reusejp_2378_;
}
else
{
lean_object* v_reuseFailAlloc_2386_; 
v_reuseFailAlloc_2386_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2386_, 0, v_fvarId_2360_);
lean_ctor_set(v_reuseFailAlloc_2386_, 1, v_mvarId_2354_);
v___x_2379_ = v_reuseFailAlloc_2386_;
goto v_reusejp_2378_;
}
v_reusejp_2378_:
{
lean_object* v___x_2381_; 
if (v_isShared_2353_ == 0)
{
lean_ctor_set_tag(v___x_2352_, 1);
lean_ctor_set(v___x_2352_, 1, v_a_2374_);
lean_ctor_set(v___x_2352_, 0, v___x_2379_);
v___x_2381_ = v___x_2352_;
goto v_reusejp_2380_;
}
else
{
lean_object* v_reuseFailAlloc_2385_; 
v_reuseFailAlloc_2385_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2385_, 0, v___x_2379_);
lean_ctor_set(v_reuseFailAlloc_2385_, 1, v_a_2374_);
v___x_2381_ = v_reuseFailAlloc_2385_;
goto v_reusejp_2380_;
}
v_reusejp_2380_:
{
lean_object* v___x_2383_; 
if (v_isShared_2377_ == 0)
{
lean_ctor_set(v___x_2376_, 0, v___x_2381_);
v___x_2383_ = v___x_2376_;
goto v_reusejp_2382_;
}
else
{
lean_object* v_reuseFailAlloc_2384_; 
v_reuseFailAlloc_2384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2384_, 0, v___x_2381_);
v___x_2383_ = v_reuseFailAlloc_2384_;
goto v_reusejp_2382_;
}
v_reusejp_2382_:
{
return v___x_2383_;
}
}
}
}
}
else
{
lean_del_object(v___x_2364_);
lean_dec(v_fvarId_2360_);
lean_dec(v_mvarId_2354_);
lean_del_object(v___x_2352_);
return v___x_2373_;
}
}
else
{
lean_dec(v___x_2370_);
lean_dec(v_mvarId_2366_);
lean_del_object(v___x_2364_);
lean_dec(v_fvarId_2360_);
lean_dec(v_mvarId_2354_);
lean_del_object(v___x_2352_);
v___y_2328_ = v_a_2315_;
v___y_2329_ = v_a_2316_;
v___y_2330_ = v_a_2317_;
v___y_2331_ = v_a_2318_;
goto v___jp_2327_;
}
}
}
}
else
{
lean_dec(v___x_2359_);
lean_dec(v_mvarId_2354_);
lean_del_object(v___x_2352_);
lean_dec(v_a_2343_);
v___y_2321_ = v_a_2315_;
v___y_2322_ = v_a_2316_;
v___y_2323_ = v_a_2317_;
v___y_2324_ = v_a_2318_;
goto v___jp_2320_;
}
}
}
}
}
else
{
lean_object* v_a_2392_; lean_object* v___x_2394_; uint8_t v_isShared_2395_; uint8_t v_isSharedCheck_2399_; 
v_a_2392_ = lean_ctor_get(v___x_2342_, 0);
v_isSharedCheck_2399_ = !lean_is_exclusive(v___x_2342_);
if (v_isSharedCheck_2399_ == 0)
{
v___x_2394_ = v___x_2342_;
v_isShared_2395_ = v_isSharedCheck_2399_;
goto v_resetjp_2393_;
}
else
{
lean_inc(v_a_2392_);
lean_dec(v___x_2342_);
v___x_2394_ = lean_box(0);
v_isShared_2395_ = v_isSharedCheck_2399_;
goto v_resetjp_2393_;
}
v_resetjp_2393_:
{
lean_object* v___x_2397_; 
if (v_isShared_2395_ == 0)
{
v___x_2397_ = v___x_2394_;
goto v_reusejp_2396_;
}
else
{
lean_object* v_reuseFailAlloc_2398_; 
v_reuseFailAlloc_2398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2398_, 0, v_a_2392_);
v___x_2397_ = v_reuseFailAlloc_2398_;
goto v_reusejp_2396_;
}
v_reusejp_2396_:
{
return v___x_2397_;
}
}
}
}
v___jp_2320_:
{
lean_object* v___x_2325_; lean_object* v___x_2326_; 
v___x_2325_ = lean_obj_once(&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesSum___closed__1, &l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesSum___closed__1_once, _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesSum___closed__1);
v___x_2326_ = l_Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0___redArg(v___x_2325_, v___y_2321_, v___y_2322_, v___y_2323_, v___y_2324_);
return v___x_2326_;
}
v___jp_2327_:
{
lean_object* v___x_2332_; lean_object* v___x_2333_; 
v___x_2332_ = lean_obj_once(&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesSum___closed__1, &l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesSum___closed__1_once, _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesSum___closed__1);
v___x_2333_ = l_Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0___redArg(v___x_2332_, v___y_2328_, v___y_2329_, v___y_2330_, v___y_2331_);
return v___x_2333_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesSum___boxed(lean_object* v_n_2400_, lean_object* v_mvar_2401_, lean_object* v_h_2402_, lean_object* v_a_2403_, lean_object* v_a_2404_, lean_object* v_a_2405_, lean_object* v_a_2406_, lean_object* v_a_2407_){
_start:
{
lean_object* v_res_2408_; 
v_res_2408_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesSum(v_n_2400_, v_mvar_2401_, v_h_2402_, v_a_2403_, v_a_2404_, v_a_2405_, v_a_2406_);
lean_dec(v_a_2406_);
lean_dec_ref(v_a_2405_);
lean_dec(v_a_2404_);
lean_dec_ref(v_a_2403_);
lean_dec(v_n_2400_);
return v_res_2408_;
}
}
static lean_object* _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesProd___closed__1(void){
_start:
{
lean_object* v___x_2410_; lean_object* v___x_2411_; 
v___x_2410_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesProd___closed__0));
v___x_2411_ = l_Lean_stringToMessageData(v___x_2410_);
return v___x_2411_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesProd(lean_object* v_n_2412_, lean_object* v_mvar_2413_, lean_object* v_h_2414_, lean_object* v_a_2415_, lean_object* v_a_2416_, lean_object* v_a_2417_, lean_object* v_a_2418_){
_start:
{
lean_object* v___y_2421_; lean_object* v___y_2422_; lean_object* v___y_2423_; lean_object* v___y_2424_; lean_object* v_zero_2427_; uint8_t v_isZero_2428_; 
v_zero_2427_ = lean_unsigned_to_nat(0u);
v_isZero_2428_ = lean_nat_dec_eq(v_n_2412_, v_zero_2427_);
if (v_isZero_2428_ == 1)
{
lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; 
v___x_2429_ = lean_box(0);
v___x_2430_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2430_, 0, v_h_2414_);
lean_ctor_set(v___x_2430_, 1, v___x_2429_);
v___x_2431_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2431_, 0, v_mvar_2413_);
lean_ctor_set(v___x_2431_, 1, v___x_2430_);
v___x_2432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2432_, 0, v___x_2431_);
return v___x_2432_;
}
else
{
lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; 
v___x_2433_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toCases___closed__0));
v___x_2434_ = lean_box(0);
v___x_2435_ = l_Lean_MVarId_cases(v_mvar_2413_, v_h_2414_, v___x_2433_, v_isZero_2428_, v___x_2434_, v_a_2415_, v_a_2416_, v_a_2417_, v_a_2418_);
if (lean_obj_tag(v___x_2435_) == 0)
{
lean_object* v_a_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; uint8_t v___x_2439_; 
v_a_2436_ = lean_ctor_get(v___x_2435_, 0);
lean_inc(v_a_2436_);
lean_dec_ref(v___x_2435_);
v___x_2437_ = lean_array_get_size(v_a_2436_);
v___x_2438_ = lean_unsigned_to_nat(1u);
v___x_2439_ = lean_nat_dec_eq(v___x_2437_, v___x_2438_);
if (v___x_2439_ == 0)
{
lean_object* v___x_2440_; lean_object* v___x_2441_; 
lean_dec(v_a_2436_);
v___x_2440_ = lean_obj_once(&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesProd___closed__1, &l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesProd___closed__1_once, _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesProd___closed__1);
v___x_2441_ = l_Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0___redArg(v___x_2440_, v_a_2415_, v_a_2416_, v_a_2417_, v_a_2418_);
return v___x_2441_;
}
else
{
lean_object* v___x_2442_; lean_object* v_toInductionSubgoal_2443_; lean_object* v___x_2445_; uint8_t v_isShared_2446_; uint8_t v_isSharedCheck_2478_; 
v___x_2442_ = lean_array_fget(v_a_2436_, v_zero_2427_);
lean_dec(v_a_2436_);
v_toInductionSubgoal_2443_ = lean_ctor_get(v___x_2442_, 0);
v_isSharedCheck_2478_ = !lean_is_exclusive(v___x_2442_);
if (v_isSharedCheck_2478_ == 0)
{
lean_object* v_unused_2479_; 
v_unused_2479_ = lean_ctor_get(v___x_2442_, 1);
lean_dec(v_unused_2479_);
v___x_2445_ = v___x_2442_;
v_isShared_2446_ = v_isSharedCheck_2478_;
goto v_resetjp_2444_;
}
else
{
lean_inc(v_toInductionSubgoal_2443_);
lean_dec(v___x_2442_);
v___x_2445_ = lean_box(0);
v_isShared_2446_ = v_isSharedCheck_2478_;
goto v_resetjp_2444_;
}
v_resetjp_2444_:
{
lean_object* v_mvarId_2447_; lean_object* v_fields_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; uint8_t v___x_2451_; 
v_mvarId_2447_ = lean_ctor_get(v_toInductionSubgoal_2443_, 0);
lean_inc(v_mvarId_2447_);
v_fields_2448_ = lean_ctor_get(v_toInductionSubgoal_2443_, 1);
lean_inc_ref(v_fields_2448_);
lean_dec_ref(v_toInductionSubgoal_2443_);
v___x_2449_ = lean_array_get_size(v_fields_2448_);
v___x_2450_ = lean_unsigned_to_nat(2u);
v___x_2451_ = lean_nat_dec_eq(v___x_2449_, v___x_2450_);
if (v___x_2451_ == 0)
{
lean_dec_ref(v_fields_2448_);
lean_dec(v_mvarId_2447_);
lean_del_object(v___x_2445_);
v___y_2421_ = v_a_2415_;
v___y_2422_ = v_a_2416_;
v___y_2423_ = v_a_2417_;
v___y_2424_ = v_a_2418_;
goto v___jp_2420_;
}
else
{
lean_object* v___x_2452_; 
v___x_2452_ = lean_array_fget_borrowed(v_fields_2448_, v_zero_2427_);
if (lean_obj_tag(v___x_2452_) == 1)
{
lean_object* v_fvarId_2453_; lean_object* v___x_2454_; 
v_fvarId_2453_ = lean_ctor_get(v___x_2452_, 0);
lean_inc(v_fvarId_2453_);
v___x_2454_ = lean_array_fget(v_fields_2448_, v___x_2438_);
lean_dec_ref(v_fields_2448_);
if (lean_obj_tag(v___x_2454_) == 1)
{
lean_object* v_fvarId_2455_; lean_object* v_n_2456_; lean_object* v___x_2457_; 
v_fvarId_2455_ = lean_ctor_get(v___x_2454_, 0);
lean_inc(v_fvarId_2455_);
lean_dec_ref(v___x_2454_);
v_n_2456_ = lean_nat_sub(v_n_2412_, v___x_2438_);
v___x_2457_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesProd(v_n_2456_, v_mvarId_2447_, v_fvarId_2455_, v_a_2415_, v_a_2416_, v_a_2417_, v_a_2418_);
lean_dec(v_n_2456_);
if (lean_obj_tag(v___x_2457_) == 0)
{
lean_object* v_a_2458_; lean_object* v___x_2460_; uint8_t v_isShared_2461_; uint8_t v_isSharedCheck_2477_; 
v_a_2458_ = lean_ctor_get(v___x_2457_, 0);
v_isSharedCheck_2477_ = !lean_is_exclusive(v___x_2457_);
if (v_isSharedCheck_2477_ == 0)
{
v___x_2460_ = v___x_2457_;
v_isShared_2461_ = v_isSharedCheck_2477_;
goto v_resetjp_2459_;
}
else
{
lean_inc(v_a_2458_);
lean_dec(v___x_2457_);
v___x_2460_ = lean_box(0);
v_isShared_2461_ = v_isSharedCheck_2477_;
goto v_resetjp_2459_;
}
v_resetjp_2459_:
{
lean_object* v_fst_2462_; lean_object* v_snd_2463_; lean_object* v___x_2465_; uint8_t v_isShared_2466_; uint8_t v_isSharedCheck_2476_; 
v_fst_2462_ = lean_ctor_get(v_a_2458_, 0);
v_snd_2463_ = lean_ctor_get(v_a_2458_, 1);
v_isSharedCheck_2476_ = !lean_is_exclusive(v_a_2458_);
if (v_isSharedCheck_2476_ == 0)
{
v___x_2465_ = v_a_2458_;
v_isShared_2466_ = v_isSharedCheck_2476_;
goto v_resetjp_2464_;
}
else
{
lean_inc(v_snd_2463_);
lean_inc(v_fst_2462_);
lean_dec(v_a_2458_);
v___x_2465_ = lean_box(0);
v_isShared_2466_ = v_isSharedCheck_2476_;
goto v_resetjp_2464_;
}
v_resetjp_2464_:
{
lean_object* v___x_2468_; 
if (v_isShared_2446_ == 0)
{
lean_ctor_set_tag(v___x_2445_, 1);
lean_ctor_set(v___x_2445_, 1, v_snd_2463_);
lean_ctor_set(v___x_2445_, 0, v_fvarId_2453_);
v___x_2468_ = v___x_2445_;
goto v_reusejp_2467_;
}
else
{
lean_object* v_reuseFailAlloc_2475_; 
v_reuseFailAlloc_2475_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2475_, 0, v_fvarId_2453_);
lean_ctor_set(v_reuseFailAlloc_2475_, 1, v_snd_2463_);
v___x_2468_ = v_reuseFailAlloc_2475_;
goto v_reusejp_2467_;
}
v_reusejp_2467_:
{
lean_object* v___x_2470_; 
if (v_isShared_2466_ == 0)
{
lean_ctor_set(v___x_2465_, 1, v___x_2468_);
v___x_2470_ = v___x_2465_;
goto v_reusejp_2469_;
}
else
{
lean_object* v_reuseFailAlloc_2474_; 
v_reuseFailAlloc_2474_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2474_, 0, v_fst_2462_);
lean_ctor_set(v_reuseFailAlloc_2474_, 1, v___x_2468_);
v___x_2470_ = v_reuseFailAlloc_2474_;
goto v_reusejp_2469_;
}
v_reusejp_2469_:
{
lean_object* v___x_2472_; 
if (v_isShared_2461_ == 0)
{
lean_ctor_set(v___x_2460_, 0, v___x_2470_);
v___x_2472_ = v___x_2460_;
goto v_reusejp_2471_;
}
else
{
lean_object* v_reuseFailAlloc_2473_; 
v_reuseFailAlloc_2473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2473_, 0, v___x_2470_);
v___x_2472_ = v_reuseFailAlloc_2473_;
goto v_reusejp_2471_;
}
v_reusejp_2471_:
{
return v___x_2472_;
}
}
}
}
}
}
else
{
lean_dec(v_fvarId_2453_);
lean_del_object(v___x_2445_);
return v___x_2457_;
}
}
else
{
lean_dec(v___x_2454_);
lean_dec(v_fvarId_2453_);
lean_dec(v_mvarId_2447_);
lean_del_object(v___x_2445_);
v___y_2421_ = v_a_2415_;
v___y_2422_ = v_a_2416_;
v___y_2423_ = v_a_2417_;
v___y_2424_ = v_a_2418_;
goto v___jp_2420_;
}
}
else
{
lean_dec_ref(v_fields_2448_);
lean_dec(v_mvarId_2447_);
lean_del_object(v___x_2445_);
v___y_2421_ = v_a_2415_;
v___y_2422_ = v_a_2416_;
v___y_2423_ = v_a_2417_;
v___y_2424_ = v_a_2418_;
goto v___jp_2420_;
}
}
}
}
}
else
{
lean_object* v_a_2480_; lean_object* v___x_2482_; uint8_t v_isShared_2483_; uint8_t v_isSharedCheck_2487_; 
v_a_2480_ = lean_ctor_get(v___x_2435_, 0);
v_isSharedCheck_2487_ = !lean_is_exclusive(v___x_2435_);
if (v_isSharedCheck_2487_ == 0)
{
v___x_2482_ = v___x_2435_;
v_isShared_2483_ = v_isSharedCheck_2487_;
goto v_resetjp_2481_;
}
else
{
lean_inc(v_a_2480_);
lean_dec(v___x_2435_);
v___x_2482_ = lean_box(0);
v_isShared_2483_ = v_isSharedCheck_2487_;
goto v_resetjp_2481_;
}
v_resetjp_2481_:
{
lean_object* v___x_2485_; 
if (v_isShared_2483_ == 0)
{
v___x_2485_ = v___x_2482_;
goto v_reusejp_2484_;
}
else
{
lean_object* v_reuseFailAlloc_2486_; 
v_reuseFailAlloc_2486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2486_, 0, v_a_2480_);
v___x_2485_ = v_reuseFailAlloc_2486_;
goto v_reusejp_2484_;
}
v_reusejp_2484_:
{
return v___x_2485_;
}
}
}
}
v___jp_2420_:
{
lean_object* v___x_2425_; lean_object* v___x_2426_; 
v___x_2425_ = lean_obj_once(&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesSum___closed__1, &l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesSum___closed__1_once, _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesSum___closed__1);
v___x_2426_ = l_Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0___redArg(v___x_2425_, v___y_2421_, v___y_2422_, v___y_2423_, v___y_2424_);
return v___x_2426_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesProd___boxed(lean_object* v_n_2488_, lean_object* v_mvar_2489_, lean_object* v_h_2490_, lean_object* v_a_2491_, lean_object* v_a_2492_, lean_object* v_a_2493_, lean_object* v_a_2494_, lean_object* v_a_2495_){
_start:
{
lean_object* v_res_2496_; 
v_res_2496_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesProd(v_n_2488_, v_mvar_2489_, v_h_2490_, v_a_2491_, v_a_2492_, v_a_2493_, v_a_2494_);
lean_dec(v_a_2494_);
lean_dec_ref(v_a_2493_);
lean_dec(v_a_2492_);
lean_dec_ref(v_a_2491_);
lean_dec(v_n_2488_);
return v_res_2496_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_listBoolMerge___redArg(lean_object* v_x_2497_, lean_object* v_x_2498_){
_start:
{
if (lean_obj_tag(v_x_2497_) == 0)
{
lean_object* v___x_2499_; 
lean_dec(v_x_2498_);
v___x_2499_ = lean_box(0);
return v___x_2499_;
}
else
{
lean_object* v_head_2500_; uint8_t v___x_2501_; 
v_head_2500_ = lean_ctor_get(v_x_2497_, 0);
v___x_2501_ = lean_unbox(v_head_2500_);
if (v___x_2501_ == 0)
{
lean_object* v_tail_2502_; lean_object* v___x_2504_; uint8_t v_isShared_2505_; uint8_t v_isSharedCheck_2511_; 
v_tail_2502_ = lean_ctor_get(v_x_2497_, 1);
v_isSharedCheck_2511_ = !lean_is_exclusive(v_x_2497_);
if (v_isSharedCheck_2511_ == 0)
{
lean_object* v_unused_2512_; 
v_unused_2512_ = lean_ctor_get(v_x_2497_, 0);
lean_dec(v_unused_2512_);
v___x_2504_ = v_x_2497_;
v_isShared_2505_ = v_isSharedCheck_2511_;
goto v_resetjp_2503_;
}
else
{
lean_inc(v_tail_2502_);
lean_dec(v_x_2497_);
v___x_2504_ = lean_box(0);
v_isShared_2505_ = v_isSharedCheck_2511_;
goto v_resetjp_2503_;
}
v_resetjp_2503_:
{
lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2509_; 
v___x_2506_ = lean_box(0);
v___x_2507_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_listBoolMerge___redArg(v_tail_2502_, v_x_2498_);
if (v_isShared_2505_ == 0)
{
lean_ctor_set(v___x_2504_, 1, v___x_2507_);
lean_ctor_set(v___x_2504_, 0, v___x_2506_);
v___x_2509_ = v___x_2504_;
goto v_reusejp_2508_;
}
else
{
lean_object* v_reuseFailAlloc_2510_; 
v_reuseFailAlloc_2510_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2510_, 0, v___x_2506_);
lean_ctor_set(v_reuseFailAlloc_2510_, 1, v___x_2507_);
v___x_2509_ = v_reuseFailAlloc_2510_;
goto v_reusejp_2508_;
}
v_reusejp_2508_:
{
return v___x_2509_;
}
}
}
else
{
if (lean_obj_tag(v_x_2498_) == 0)
{
lean_object* v___x_2513_; 
lean_dec_ref(v_x_2497_);
v___x_2513_ = lean_box(0);
return v___x_2513_;
}
else
{
lean_object* v_tail_2514_; lean_object* v_head_2515_; lean_object* v_tail_2516_; lean_object* v___x_2518_; uint8_t v_isShared_2519_; uint8_t v_isSharedCheck_2525_; 
v_tail_2514_ = lean_ctor_get(v_x_2497_, 1);
lean_inc(v_tail_2514_);
lean_dec_ref(v_x_2497_);
v_head_2515_ = lean_ctor_get(v_x_2498_, 0);
v_tail_2516_ = lean_ctor_get(v_x_2498_, 1);
v_isSharedCheck_2525_ = !lean_is_exclusive(v_x_2498_);
if (v_isSharedCheck_2525_ == 0)
{
v___x_2518_ = v_x_2498_;
v_isShared_2519_ = v_isSharedCheck_2525_;
goto v_resetjp_2517_;
}
else
{
lean_inc(v_tail_2516_);
lean_inc(v_head_2515_);
lean_dec(v_x_2498_);
v___x_2518_ = lean_box(0);
v_isShared_2519_ = v_isSharedCheck_2525_;
goto v_resetjp_2517_;
}
v_resetjp_2517_:
{
lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2523_; 
v___x_2520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2520_, 0, v_head_2515_);
v___x_2521_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_listBoolMerge___redArg(v_tail_2514_, v_tail_2516_);
if (v_isShared_2519_ == 0)
{
lean_ctor_set(v___x_2518_, 1, v___x_2521_);
lean_ctor_set(v___x_2518_, 0, v___x_2520_);
v___x_2523_ = v___x_2518_;
goto v_reusejp_2522_;
}
else
{
lean_object* v_reuseFailAlloc_2524_; 
v_reuseFailAlloc_2524_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2524_, 0, v___x_2520_);
lean_ctor_set(v_reuseFailAlloc_2524_, 1, v___x_2521_);
v___x_2523_ = v_reuseFailAlloc_2524_;
goto v_reusejp_2522_;
}
v_reusejp_2522_:
{
return v___x_2523_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_listBoolMerge(lean_object* v_00_u03b1_2526_, lean_object* v_x_2527_, lean_object* v_x_2528_){
_start:
{
lean_object* v___x_2529_; 
v___x_2529_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_listBoolMerge___redArg(v_x_2527_, v_x_2528_);
return v___x_2529_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__2_spec__3(lean_object* v_a_2530_, lean_object* v_a_2531_){
_start:
{
if (lean_obj_tag(v_a_2530_) == 0)
{
lean_object* v___x_2532_; 
v___x_2532_ = l_List_reverse___redArg(v_a_2531_);
return v___x_2532_;
}
else
{
lean_object* v_head_2533_; lean_object* v_tail_2534_; lean_object* v___x_2536_; uint8_t v_isShared_2537_; uint8_t v_isSharedCheck_2543_; 
v_head_2533_ = lean_ctor_get(v_a_2530_, 0);
v_tail_2534_ = lean_ctor_get(v_a_2530_, 1);
v_isSharedCheck_2543_ = !lean_is_exclusive(v_a_2530_);
if (v_isSharedCheck_2543_ == 0)
{
v___x_2536_ = v_a_2530_;
v_isShared_2537_ = v_isSharedCheck_2543_;
goto v_resetjp_2535_;
}
else
{
lean_inc(v_tail_2534_);
lean_inc(v_head_2533_);
lean_dec(v_a_2530_);
v___x_2536_ = lean_box(0);
v_isShared_2537_ = v_isSharedCheck_2543_;
goto v_resetjp_2535_;
}
v_resetjp_2535_:
{
lean_object* v___x_2538_; lean_object* v___x_2540_; 
v___x_2538_ = l_Lean_mkLevelParam(v_head_2533_);
if (v_isShared_2537_ == 0)
{
lean_ctor_set(v___x_2536_, 1, v_a_2531_);
lean_ctor_set(v___x_2536_, 0, v___x_2538_);
v___x_2540_ = v___x_2536_;
goto v_reusejp_2539_;
}
else
{
lean_object* v_reuseFailAlloc_2542_; 
v_reuseFailAlloc_2542_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2542_, 0, v___x_2538_);
lean_ctor_set(v_reuseFailAlloc_2542_, 1, v_a_2531_);
v___x_2540_ = v_reuseFailAlloc_2542_;
goto v_reusejp_2539_;
}
v_reusejp_2539_:
{
v_a_2530_ = v_tail_2534_;
v_a_2531_ = v___x_2540_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__2_spec__2(lean_object* v_constName_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_){
_start:
{
lean_object* v___x_2550_; lean_object* v_env_2551_; uint8_t v___x_2552_; lean_object* v___x_2553_; 
v___x_2550_ = lean_st_ref_get(v___y_2548_);
v_env_2551_ = lean_ctor_get(v___x_2550_, 0);
lean_inc_ref(v_env_2551_);
lean_dec(v___x_2550_);
v___x_2552_ = 0;
lean_inc(v_constName_2544_);
v___x_2553_ = l_Lean_Environment_findConstVal_x3f(v_env_2551_, v_constName_2544_, v___x_2552_);
if (lean_obj_tag(v___x_2553_) == 0)
{
lean_object* v___x_2554_; 
v___x_2554_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0___redArg(v_constName_2544_, v___y_2545_, v___y_2546_, v___y_2547_, v___y_2548_);
return v___x_2554_;
}
else
{
lean_object* v_val_2555_; lean_object* v___x_2557_; uint8_t v_isShared_2558_; uint8_t v_isSharedCheck_2562_; 
lean_dec(v_constName_2544_);
v_val_2555_ = lean_ctor_get(v___x_2553_, 0);
v_isSharedCheck_2562_ = !lean_is_exclusive(v___x_2553_);
if (v_isSharedCheck_2562_ == 0)
{
v___x_2557_ = v___x_2553_;
v_isShared_2558_ = v_isSharedCheck_2562_;
goto v_resetjp_2556_;
}
else
{
lean_inc(v_val_2555_);
lean_dec(v___x_2553_);
v___x_2557_ = lean_box(0);
v_isShared_2558_ = v_isSharedCheck_2562_;
goto v_resetjp_2556_;
}
v_resetjp_2556_:
{
lean_object* v___x_2560_; 
if (v_isShared_2558_ == 0)
{
lean_ctor_set_tag(v___x_2557_, 0);
v___x_2560_ = v___x_2557_;
goto v_reusejp_2559_;
}
else
{
lean_object* v_reuseFailAlloc_2561_; 
v_reuseFailAlloc_2561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2561_, 0, v_val_2555_);
v___x_2560_ = v_reuseFailAlloc_2561_;
goto v_reusejp_2559_;
}
v_reusejp_2559_:
{
return v___x_2560_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__2_spec__2___boxed(lean_object* v_constName_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_){
_start:
{
lean_object* v_res_2569_; 
v_res_2569_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__2_spec__2(v_constName_2563_, v___y_2564_, v___y_2565_, v___y_2566_, v___y_2567_);
lean_dec(v___y_2567_);
lean_dec_ref(v___y_2566_);
lean_dec(v___y_2565_);
lean_dec_ref(v___y_2564_);
return v_res_2569_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__2(lean_object* v_constName_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_){
_start:
{
lean_object* v___x_2576_; 
lean_inc(v_constName_2570_);
v___x_2576_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__2_spec__2(v_constName_2570_, v___y_2571_, v___y_2572_, v___y_2573_, v___y_2574_);
if (lean_obj_tag(v___x_2576_) == 0)
{
lean_object* v_a_2577_; lean_object* v___x_2579_; uint8_t v_isShared_2580_; uint8_t v_isSharedCheck_2588_; 
v_a_2577_ = lean_ctor_get(v___x_2576_, 0);
v_isSharedCheck_2588_ = !lean_is_exclusive(v___x_2576_);
if (v_isSharedCheck_2588_ == 0)
{
v___x_2579_ = v___x_2576_;
v_isShared_2580_ = v_isSharedCheck_2588_;
goto v_resetjp_2578_;
}
else
{
lean_inc(v_a_2577_);
lean_dec(v___x_2576_);
v___x_2579_ = lean_box(0);
v_isShared_2580_ = v_isSharedCheck_2588_;
goto v_resetjp_2578_;
}
v_resetjp_2578_:
{
lean_object* v_levelParams_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2586_; 
v_levelParams_2581_ = lean_ctor_get(v_a_2577_, 1);
lean_inc(v_levelParams_2581_);
lean_dec(v_a_2577_);
v___x_2582_ = lean_box(0);
v___x_2583_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__2_spec__3(v_levelParams_2581_, v___x_2582_);
v___x_2584_ = l_Lean_mkConst(v_constName_2570_, v___x_2583_);
if (v_isShared_2580_ == 0)
{
lean_ctor_set(v___x_2579_, 0, v___x_2584_);
v___x_2586_ = v___x_2579_;
goto v_reusejp_2585_;
}
else
{
lean_object* v_reuseFailAlloc_2587_; 
v_reuseFailAlloc_2587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2587_, 0, v___x_2584_);
v___x_2586_ = v_reuseFailAlloc_2587_;
goto v_reusejp_2585_;
}
v_reusejp_2585_:
{
return v___x_2586_;
}
}
}
else
{
lean_object* v_a_2589_; lean_object* v___x_2591_; uint8_t v_isShared_2592_; uint8_t v_isSharedCheck_2596_; 
lean_dec(v_constName_2570_);
v_a_2589_ = lean_ctor_get(v___x_2576_, 0);
v_isSharedCheck_2596_ = !lean_is_exclusive(v___x_2576_);
if (v_isSharedCheck_2596_ == 0)
{
v___x_2591_ = v___x_2576_;
v_isShared_2592_ = v_isSharedCheck_2596_;
goto v_resetjp_2590_;
}
else
{
lean_inc(v_a_2589_);
lean_dec(v___x_2576_);
v___x_2591_ = lean_box(0);
v_isShared_2592_ = v_isSharedCheck_2596_;
goto v_resetjp_2590_;
}
v_resetjp_2590_:
{
lean_object* v___x_2594_; 
if (v_isShared_2592_ == 0)
{
v___x_2594_ = v___x_2591_;
goto v_reusejp_2593_;
}
else
{
lean_object* v_reuseFailAlloc_2595_; 
v_reuseFailAlloc_2595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2595_, 0, v_a_2589_);
v___x_2594_ = v_reuseFailAlloc_2595_;
goto v_reusejp_2593_;
}
v_reusejp_2593_:
{
return v___x_2594_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__2___boxed(lean_object* v_constName_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_){
_start:
{
lean_object* v_res_2603_; 
v_res_2603_ = l_Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__2(v_constName_2597_, v___y_2598_, v___y_2599_, v___y_2600_, v___y_2601_);
lean_dec(v___y_2601_);
lean_dec_ref(v___y_2600_);
lean_dec(v___y_2599_);
lean_dec_ref(v___y_2598_);
return v_res_2603_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__1(lean_object* v_x_2604_, lean_object* v_x_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_){
_start:
{
if (lean_obj_tag(v_x_2604_) == 0)
{
lean_object* v___x_2611_; lean_object* v___x_2612_; 
v___x_2611_ = l_List_reverse___redArg(v_x_2605_);
v___x_2612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2612_, 0, v___x_2611_);
return v___x_2612_;
}
else
{
lean_object* v_head_2613_; lean_object* v_tail_2614_; lean_object* v___x_2616_; uint8_t v_isShared_2617_; uint8_t v_isSharedCheck_2639_; 
v_head_2613_ = lean_ctor_get(v_x_2604_, 0);
v_tail_2614_ = lean_ctor_get(v_x_2604_, 1);
v_isSharedCheck_2639_ = !lean_is_exclusive(v_x_2604_);
if (v_isSharedCheck_2639_ == 0)
{
v___x_2616_ = v_x_2604_;
v_isShared_2617_ = v_isSharedCheck_2639_;
goto v_resetjp_2615_;
}
else
{
lean_inc(v_tail_2614_);
lean_inc(v_head_2613_);
lean_dec(v_x_2604_);
v___x_2616_ = lean_box(0);
v_isShared_2617_ = v_isSharedCheck_2639_;
goto v_resetjp_2615_;
}
v_resetjp_2615_:
{
lean_object* v_a_2619_; 
if (lean_obj_tag(v_head_2613_) == 0)
{
lean_object* v___x_2624_; uint8_t v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; 
v___x_2624_ = lean_box(0);
v___x_2625_ = 0;
v___x_2626_ = lean_box(0);
v___x_2627_ = l_Lean_Meta_mkFreshExprMVar(v___x_2624_, v___x_2625_, v___x_2626_, v___y_2606_, v___y_2607_, v___y_2608_, v___y_2609_);
if (lean_obj_tag(v___x_2627_) == 0)
{
lean_object* v_a_2628_; 
v_a_2628_ = lean_ctor_get(v___x_2627_, 0);
lean_inc(v_a_2628_);
lean_dec_ref(v___x_2627_);
v_a_2619_ = v_a_2628_;
goto v___jp_2618_;
}
else
{
lean_object* v_a_2629_; lean_object* v___x_2631_; uint8_t v_isShared_2632_; uint8_t v_isSharedCheck_2636_; 
lean_del_object(v___x_2616_);
lean_dec(v_tail_2614_);
lean_dec(v_x_2605_);
v_a_2629_ = lean_ctor_get(v___x_2627_, 0);
v_isSharedCheck_2636_ = !lean_is_exclusive(v___x_2627_);
if (v_isSharedCheck_2636_ == 0)
{
v___x_2631_ = v___x_2627_;
v_isShared_2632_ = v_isSharedCheck_2636_;
goto v_resetjp_2630_;
}
else
{
lean_inc(v_a_2629_);
lean_dec(v___x_2627_);
v___x_2631_ = lean_box(0);
v_isShared_2632_ = v_isSharedCheck_2636_;
goto v_resetjp_2630_;
}
v_resetjp_2630_:
{
lean_object* v___x_2634_; 
if (v_isShared_2632_ == 0)
{
v___x_2634_ = v___x_2631_;
goto v_reusejp_2633_;
}
else
{
lean_object* v_reuseFailAlloc_2635_; 
v_reuseFailAlloc_2635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2635_, 0, v_a_2629_);
v___x_2634_ = v_reuseFailAlloc_2635_;
goto v_reusejp_2633_;
}
v_reusejp_2633_:
{
return v___x_2634_;
}
}
}
}
else
{
lean_object* v_val_2637_; lean_object* v___x_2638_; 
v_val_2637_ = lean_ctor_get(v_head_2613_, 0);
lean_inc(v_val_2637_);
lean_dec_ref(v_head_2613_);
v___x_2638_ = l_Lean_mkFVar(v_val_2637_);
v_a_2619_ = v___x_2638_;
goto v___jp_2618_;
}
v___jp_2618_:
{
lean_object* v___x_2621_; 
if (v_isShared_2617_ == 0)
{
lean_ctor_set(v___x_2616_, 1, v_x_2605_);
lean_ctor_set(v___x_2616_, 0, v_a_2619_);
v___x_2621_ = v___x_2616_;
goto v_reusejp_2620_;
}
else
{
lean_object* v_reuseFailAlloc_2623_; 
v_reuseFailAlloc_2623_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2623_, 0, v_a_2619_);
lean_ctor_set(v_reuseFailAlloc_2623_, 1, v_x_2605_);
v___x_2621_ = v_reuseFailAlloc_2623_;
goto v_reusejp_2620_;
}
v_reusejp_2620_:
{
v_x_2604_ = v_tail_2614_;
v_x_2605_ = v___x_2621_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__1___boxed(lean_object* v_x_2640_, lean_object* v_x_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_){
_start:
{
lean_object* v_res_2647_; 
v_res_2647_ = l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__1(v_x_2640_, v_x_2641_, v___y_2642_, v___y_2643_, v___y_2644_, v___y_2645_);
lean_dec(v___y_2645_);
lean_dec_ref(v___y_2644_);
lean_dec(v___y_2643_);
lean_dec_ref(v___y_2642_);
return v_res_2647_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__0(lean_object* v_a_2648_, lean_object* v_a_2649_){
_start:
{
if (lean_obj_tag(v_a_2648_) == 0)
{
lean_object* v___x_2650_; 
v___x_2650_ = l_List_reverse___redArg(v_a_2649_);
return v___x_2650_;
}
else
{
lean_object* v_head_2651_; lean_object* v_tail_2652_; lean_object* v___x_2654_; uint8_t v_isShared_2655_; uint8_t v_isSharedCheck_2661_; 
v_head_2651_ = lean_ctor_get(v_a_2648_, 0);
v_tail_2652_ = lean_ctor_get(v_a_2648_, 1);
v_isSharedCheck_2661_ = !lean_is_exclusive(v_a_2648_);
if (v_isSharedCheck_2661_ == 0)
{
v___x_2654_ = v_a_2648_;
v_isShared_2655_ = v_isSharedCheck_2661_;
goto v_resetjp_2653_;
}
else
{
lean_inc(v_tail_2652_);
lean_inc(v_head_2651_);
lean_dec(v_a_2648_);
v___x_2654_ = lean_box(0);
v_isShared_2655_ = v_isSharedCheck_2661_;
goto v_resetjp_2653_;
}
v_resetjp_2653_:
{
lean_object* v___x_2656_; lean_object* v___x_2658_; 
v___x_2656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2656_, 0, v_head_2651_);
if (v_isShared_2655_ == 0)
{
lean_ctor_set(v___x_2654_, 1, v_a_2649_);
lean_ctor_set(v___x_2654_, 0, v___x_2656_);
v___x_2658_ = v___x_2654_;
goto v_reusejp_2657_;
}
else
{
lean_object* v_reuseFailAlloc_2660_; 
v_reuseFailAlloc_2660_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2660_, 0, v___x_2656_);
lean_ctor_set(v_reuseFailAlloc_2660_, 1, v_a_2649_);
v___x_2658_ = v_reuseFailAlloc_2660_;
goto v_reusejp_2657_;
}
v_reusejp_2657_:
{
v_a_2648_ = v_tail_2652_;
v_a_2649_ = v___x_2658_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__5___lam__0(lean_object* v_gs_2664_, lean_object* v_variablesKept_2665_, lean_object* v_snd_2666_, lean_object* v_fst_2667_, lean_object* v_fst_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_){
_start:
{
lean_object* v_lctx_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; 
v_lctx_2674_ = lean_ctor_get(v___y_2669_, 2);
v___x_2675_ = l_Lean_LocalContext_getFVarIds(v_lctx_2674_);
v___x_2676_ = lean_array_to_list(v___x_2675_);
v___x_2677_ = l_List_lengthTR___redArg(v_gs_2664_);
v___x_2678_ = ((lean_object*)(l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__5___lam__0___closed__0));
lean_inc(v___x_2676_);
v___x_2679_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), v___x_2676_, v___x_2676_, v___x_2677_, v___x_2678_);
lean_dec(v___x_2676_);
v___x_2680_ = lean_box(0);
v___x_2681_ = l_List_mapTR_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__0(v___x_2679_, v___x_2680_);
v___x_2682_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_listBoolMerge___redArg(v_variablesKept_2665_, v_snd_2666_);
v___x_2683_ = l_List_appendTR___redArg(v___x_2681_, v___x_2682_);
v___x_2684_ = l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__1(v___x_2683_, v___x_2680_, v___y_2669_, v___y_2670_, v___y_2671_, v___y_2672_);
if (lean_obj_tag(v___x_2684_) == 0)
{
lean_object* v_a_2685_; lean_object* v___x_2686_; 
v_a_2685_ = lean_ctor_get(v___x_2684_, 0);
lean_inc(v_a_2685_);
lean_dec_ref(v___x_2684_);
v___x_2686_ = l_Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__2(v_fst_2667_, v___y_2669_, v___y_2670_, v___y_2671_, v___y_2672_);
if (lean_obj_tag(v___x_2686_) == 0)
{
lean_object* v_a_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; 
v_a_2687_ = lean_ctor_get(v___x_2686_, 0);
lean_inc(v_a_2687_);
lean_dec_ref(v___x_2686_);
v___x_2688_ = lean_array_mk(v_a_2685_);
v___x_2689_ = l_Lean_mkAppN(v_a_2687_, v___x_2688_);
lean_dec_ref(v___x_2688_);
lean_inc(v___y_2672_);
lean_inc_ref(v___y_2671_);
lean_inc(v___y_2670_);
lean_inc_ref(v___y_2669_);
lean_inc_ref(v___x_2689_);
v___x_2690_ = lean_infer_type(v___x_2689_, v___y_2669_, v___y_2670_, v___y_2671_, v___y_2672_);
if (lean_obj_tag(v___x_2690_) == 0)
{
lean_object* v_a_2691_; lean_object* v___x_2692_; 
v_a_2691_ = lean_ctor_get(v___x_2690_, 0);
lean_inc(v_a_2691_);
lean_dec_ref(v___x_2690_);
lean_inc(v_fst_2668_);
v___x_2692_ = l_Lean_MVarId_getType(v_fst_2668_, v___y_2669_, v___y_2670_, v___y_2671_, v___y_2672_);
if (lean_obj_tag(v___x_2692_) == 0)
{
lean_object* v_a_2693_; lean_object* v___x_2694_; 
v_a_2693_ = lean_ctor_get(v___x_2692_, 0);
lean_inc(v_a_2693_);
lean_dec_ref(v___x_2692_);
v___x_2694_ = l_Lean_Meta_isExprDefEq(v_a_2691_, v_a_2693_, v___y_2669_, v___y_2670_, v___y_2671_, v___y_2672_);
lean_dec(v___y_2672_);
lean_dec_ref(v___y_2671_);
lean_dec_ref(v___y_2669_);
if (lean_obj_tag(v___x_2694_) == 0)
{
lean_object* v___x_2695_; 
lean_dec_ref(v___x_2694_);
v___x_2695_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1___redArg(v_fst_2668_, v___x_2689_, v___y_2670_);
lean_dec(v___y_2670_);
return v___x_2695_;
}
else
{
lean_object* v_a_2696_; lean_object* v___x_2698_; uint8_t v_isShared_2699_; uint8_t v_isSharedCheck_2703_; 
lean_dec_ref(v___x_2689_);
lean_dec(v___y_2670_);
lean_dec(v_fst_2668_);
v_a_2696_ = lean_ctor_get(v___x_2694_, 0);
v_isSharedCheck_2703_ = !lean_is_exclusive(v___x_2694_);
if (v_isSharedCheck_2703_ == 0)
{
v___x_2698_ = v___x_2694_;
v_isShared_2699_ = v_isSharedCheck_2703_;
goto v_resetjp_2697_;
}
else
{
lean_inc(v_a_2696_);
lean_dec(v___x_2694_);
v___x_2698_ = lean_box(0);
v_isShared_2699_ = v_isSharedCheck_2703_;
goto v_resetjp_2697_;
}
v_resetjp_2697_:
{
lean_object* v___x_2701_; 
if (v_isShared_2699_ == 0)
{
v___x_2701_ = v___x_2698_;
goto v_reusejp_2700_;
}
else
{
lean_object* v_reuseFailAlloc_2702_; 
v_reuseFailAlloc_2702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2702_, 0, v_a_2696_);
v___x_2701_ = v_reuseFailAlloc_2702_;
goto v_reusejp_2700_;
}
v_reusejp_2700_:
{
return v___x_2701_;
}
}
}
}
else
{
lean_object* v_a_2704_; lean_object* v___x_2706_; uint8_t v_isShared_2707_; uint8_t v_isSharedCheck_2711_; 
lean_dec(v_a_2691_);
lean_dec_ref(v___x_2689_);
lean_dec(v___y_2672_);
lean_dec_ref(v___y_2671_);
lean_dec(v___y_2670_);
lean_dec_ref(v___y_2669_);
lean_dec(v_fst_2668_);
v_a_2704_ = lean_ctor_get(v___x_2692_, 0);
v_isSharedCheck_2711_ = !lean_is_exclusive(v___x_2692_);
if (v_isSharedCheck_2711_ == 0)
{
v___x_2706_ = v___x_2692_;
v_isShared_2707_ = v_isSharedCheck_2711_;
goto v_resetjp_2705_;
}
else
{
lean_inc(v_a_2704_);
lean_dec(v___x_2692_);
v___x_2706_ = lean_box(0);
v_isShared_2707_ = v_isSharedCheck_2711_;
goto v_resetjp_2705_;
}
v_resetjp_2705_:
{
lean_object* v___x_2709_; 
if (v_isShared_2707_ == 0)
{
v___x_2709_ = v___x_2706_;
goto v_reusejp_2708_;
}
else
{
lean_object* v_reuseFailAlloc_2710_; 
v_reuseFailAlloc_2710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2710_, 0, v_a_2704_);
v___x_2709_ = v_reuseFailAlloc_2710_;
goto v_reusejp_2708_;
}
v_reusejp_2708_:
{
return v___x_2709_;
}
}
}
}
else
{
lean_object* v_a_2712_; lean_object* v___x_2714_; uint8_t v_isShared_2715_; uint8_t v_isSharedCheck_2719_; 
lean_dec_ref(v___x_2689_);
lean_dec(v___y_2672_);
lean_dec_ref(v___y_2671_);
lean_dec(v___y_2670_);
lean_dec_ref(v___y_2669_);
lean_dec(v_fst_2668_);
v_a_2712_ = lean_ctor_get(v___x_2690_, 0);
v_isSharedCheck_2719_ = !lean_is_exclusive(v___x_2690_);
if (v_isSharedCheck_2719_ == 0)
{
v___x_2714_ = v___x_2690_;
v_isShared_2715_ = v_isSharedCheck_2719_;
goto v_resetjp_2713_;
}
else
{
lean_inc(v_a_2712_);
lean_dec(v___x_2690_);
v___x_2714_ = lean_box(0);
v_isShared_2715_ = v_isSharedCheck_2719_;
goto v_resetjp_2713_;
}
v_resetjp_2713_:
{
lean_object* v___x_2717_; 
if (v_isShared_2715_ == 0)
{
v___x_2717_ = v___x_2714_;
goto v_reusejp_2716_;
}
else
{
lean_object* v_reuseFailAlloc_2718_; 
v_reuseFailAlloc_2718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2718_, 0, v_a_2712_);
v___x_2717_ = v_reuseFailAlloc_2718_;
goto v_reusejp_2716_;
}
v_reusejp_2716_:
{
return v___x_2717_;
}
}
}
}
else
{
lean_object* v_a_2720_; lean_object* v___x_2722_; uint8_t v_isShared_2723_; uint8_t v_isSharedCheck_2727_; 
lean_dec(v_a_2685_);
lean_dec(v___y_2672_);
lean_dec_ref(v___y_2671_);
lean_dec(v___y_2670_);
lean_dec_ref(v___y_2669_);
lean_dec(v_fst_2668_);
v_a_2720_ = lean_ctor_get(v___x_2686_, 0);
v_isSharedCheck_2727_ = !lean_is_exclusive(v___x_2686_);
if (v_isSharedCheck_2727_ == 0)
{
v___x_2722_ = v___x_2686_;
v_isShared_2723_ = v_isSharedCheck_2727_;
goto v_resetjp_2721_;
}
else
{
lean_inc(v_a_2720_);
lean_dec(v___x_2686_);
v___x_2722_ = lean_box(0);
v_isShared_2723_ = v_isSharedCheck_2727_;
goto v_resetjp_2721_;
}
v_resetjp_2721_:
{
lean_object* v___x_2725_; 
if (v_isShared_2723_ == 0)
{
v___x_2725_ = v___x_2722_;
goto v_reusejp_2724_;
}
else
{
lean_object* v_reuseFailAlloc_2726_; 
v_reuseFailAlloc_2726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2726_, 0, v_a_2720_);
v___x_2725_ = v_reuseFailAlloc_2726_;
goto v_reusejp_2724_;
}
v_reusejp_2724_:
{
return v___x_2725_;
}
}
}
}
else
{
lean_object* v_a_2728_; lean_object* v___x_2730_; uint8_t v_isShared_2731_; uint8_t v_isSharedCheck_2735_; 
lean_dec(v___y_2672_);
lean_dec_ref(v___y_2671_);
lean_dec(v___y_2670_);
lean_dec_ref(v___y_2669_);
lean_dec(v_fst_2668_);
lean_dec(v_fst_2667_);
v_a_2728_ = lean_ctor_get(v___x_2684_, 0);
v_isSharedCheck_2735_ = !lean_is_exclusive(v___x_2684_);
if (v_isSharedCheck_2735_ == 0)
{
v___x_2730_ = v___x_2684_;
v_isShared_2731_ = v_isSharedCheck_2735_;
goto v_resetjp_2729_;
}
else
{
lean_inc(v_a_2728_);
lean_dec(v___x_2684_);
v___x_2730_ = lean_box(0);
v_isShared_2731_ = v_isSharedCheck_2735_;
goto v_resetjp_2729_;
}
v_resetjp_2729_:
{
lean_object* v___x_2733_; 
if (v_isShared_2731_ == 0)
{
v___x_2733_ = v___x_2730_;
goto v_reusejp_2732_;
}
else
{
lean_object* v_reuseFailAlloc_2734_; 
v_reuseFailAlloc_2734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2734_, 0, v_a_2728_);
v___x_2733_ = v_reuseFailAlloc_2734_;
goto v_reusejp_2732_;
}
v_reusejp_2732_:
{
return v___x_2733_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__5___lam__0___boxed(lean_object* v_gs_2736_, lean_object* v_variablesKept_2737_, lean_object* v_snd_2738_, lean_object* v_fst_2739_, lean_object* v_fst_2740_, lean_object* v___y_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_){
_start:
{
lean_object* v_res_2746_; 
v_res_2746_ = l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__5___lam__0(v_gs_2736_, v_variablesKept_2737_, v_snd_2738_, v_fst_2739_, v_fst_2740_, v___y_2741_, v___y_2742_, v___y_2743_, v___y_2744_);
lean_dec(v_gs_2736_);
return v_res_2746_;
}
}
static lean_object* _init_l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__4___closed__1(void){
_start:
{
lean_object* v___x_2748_; lean_object* v___x_2749_; 
v___x_2748_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__4___closed__0));
v___x_2749_ = l_Lean_stringToMessageData(v___x_2748_);
return v___x_2749_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__4(lean_object* v_x_2750_, lean_object* v_x_2751_, lean_object* v___y_2752_, lean_object* v___y_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_){
_start:
{
if (lean_obj_tag(v_x_2751_) == 0)
{
lean_object* v___x_2757_; 
v___x_2757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2757_, 0, v_x_2750_);
return v___x_2757_;
}
else
{
lean_object* v_tail_2758_; uint8_t v___x_2759_; lean_object* v___x_2760_; 
v_tail_2758_ = lean_ctor_get(v_x_2751_, 1);
v___x_2759_ = 0;
v___x_2760_ = l_Lean_Meta_intro1Core(v_x_2750_, v___x_2759_, v___y_2752_, v___y_2753_, v___y_2754_, v___y_2755_);
if (lean_obj_tag(v___x_2760_) == 0)
{
lean_object* v_a_2761_; lean_object* v_fst_2762_; lean_object* v_snd_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; 
v_a_2761_ = lean_ctor_get(v___x_2760_, 0);
lean_inc(v_a_2761_);
lean_dec_ref(v___x_2760_);
v_fst_2762_ = lean_ctor_get(v_a_2761_, 0);
lean_inc(v_fst_2762_);
v_snd_2763_ = lean_ctor_get(v_a_2761_, 1);
lean_inc(v_snd_2763_);
lean_dec(v_a_2761_);
v___x_2764_ = lean_unsigned_to_nat(0u);
v___x_2765_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toCases___closed__0));
v___x_2766_ = lean_box(0);
v___x_2767_ = l_Lean_MVarId_cases(v_snd_2763_, v_fst_2762_, v___x_2765_, v___x_2759_, v___x_2766_, v___y_2752_, v___y_2753_, v___y_2754_, v___y_2755_);
if (lean_obj_tag(v___x_2767_) == 0)
{
lean_object* v_a_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; uint8_t v___x_2771_; 
v_a_2768_ = lean_ctor_get(v___x_2767_, 0);
lean_inc(v_a_2768_);
lean_dec_ref(v___x_2767_);
v___x_2769_ = lean_array_get_size(v_a_2768_);
v___x_2770_ = lean_unsigned_to_nat(1u);
v___x_2771_ = lean_nat_dec_eq(v___x_2769_, v___x_2770_);
if (v___x_2771_ == 0)
{
lean_object* v___x_2772_; lean_object* v___x_2773_; 
lean_dec(v_a_2768_);
v___x_2772_ = lean_obj_once(&l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__4___closed__1, &l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__4___closed__1_once, _init_l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__4___closed__1);
v___x_2773_ = l_Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0___redArg(v___x_2772_, v___y_2752_, v___y_2753_, v___y_2754_, v___y_2755_);
return v___x_2773_;
}
else
{
lean_object* v___x_2774_; lean_object* v_toInductionSubgoal_2775_; lean_object* v_mvarId_2776_; 
v___x_2774_ = lean_array_fget(v_a_2768_, v___x_2764_);
lean_dec(v_a_2768_);
v_toInductionSubgoal_2775_ = lean_ctor_get(v___x_2774_, 0);
lean_inc_ref(v_toInductionSubgoal_2775_);
lean_dec(v___x_2774_);
v_mvarId_2776_ = lean_ctor_get(v_toInductionSubgoal_2775_, 0);
lean_inc(v_mvarId_2776_);
lean_dec_ref(v_toInductionSubgoal_2775_);
v_x_2750_ = v_mvarId_2776_;
v_x_2751_ = v_tail_2758_;
goto _start;
}
}
else
{
lean_object* v_a_2778_; lean_object* v___x_2780_; uint8_t v_isShared_2781_; uint8_t v_isSharedCheck_2785_; 
v_a_2778_ = lean_ctor_get(v___x_2767_, 0);
v_isSharedCheck_2785_ = !lean_is_exclusive(v___x_2767_);
if (v_isSharedCheck_2785_ == 0)
{
v___x_2780_ = v___x_2767_;
v_isShared_2781_ = v_isSharedCheck_2785_;
goto v_resetjp_2779_;
}
else
{
lean_inc(v_a_2778_);
lean_dec(v___x_2767_);
v___x_2780_ = lean_box(0);
v_isShared_2781_ = v_isSharedCheck_2785_;
goto v_resetjp_2779_;
}
v_resetjp_2779_:
{
lean_object* v___x_2783_; 
if (v_isShared_2781_ == 0)
{
v___x_2783_ = v___x_2780_;
goto v_reusejp_2782_;
}
else
{
lean_object* v_reuseFailAlloc_2784_; 
v_reuseFailAlloc_2784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2784_, 0, v_a_2778_);
v___x_2783_ = v_reuseFailAlloc_2784_;
goto v_reusejp_2782_;
}
v_reusejp_2782_:
{
return v___x_2783_;
}
}
}
}
else
{
lean_object* v_a_2786_; lean_object* v___x_2788_; uint8_t v_isShared_2789_; uint8_t v_isSharedCheck_2793_; 
v_a_2786_ = lean_ctor_get(v___x_2760_, 0);
v_isSharedCheck_2793_ = !lean_is_exclusive(v___x_2760_);
if (v_isSharedCheck_2793_ == 0)
{
v___x_2788_ = v___x_2760_;
v_isShared_2789_ = v_isSharedCheck_2793_;
goto v_resetjp_2787_;
}
else
{
lean_inc(v_a_2786_);
lean_dec(v___x_2760_);
v___x_2788_ = lean_box(0);
v_isShared_2789_ = v_isSharedCheck_2793_;
goto v_resetjp_2787_;
}
v_resetjp_2787_:
{
lean_object* v___x_2791_; 
if (v_isShared_2789_ == 0)
{
v___x_2791_ = v___x_2788_;
goto v_reusejp_2790_;
}
else
{
lean_object* v_reuseFailAlloc_2792_; 
v_reuseFailAlloc_2792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2792_, 0, v_a_2786_);
v___x_2791_ = v_reuseFailAlloc_2792_;
goto v_reusejp_2790_;
}
v_reusejp_2790_:
{
return v___x_2791_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__4___boxed(lean_object* v_x_2794_, lean_object* v_x_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_){
_start:
{
lean_object* v_res_2801_; 
v_res_2801_ = l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__4(v_x_2794_, v_x_2795_, v___y_2796_, v___y_2797_, v___y_2798_, v___y_2799_);
lean_dec(v___y_2799_);
lean_dec_ref(v___y_2798_);
lean_dec(v___y_2797_);
lean_dec_ref(v___y_2796_);
lean_dec(v_x_2795_);
return v_res_2801_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__3(lean_object* v_a_2802_, lean_object* v_a_2803_){
_start:
{
if (lean_obj_tag(v_a_2802_) == 0)
{
lean_object* v___x_2804_; 
v___x_2804_ = l_List_reverse___redArg(v_a_2803_);
return v___x_2804_;
}
else
{
lean_object* v_head_2805_; uint8_t v___x_2806_; 
v_head_2805_ = lean_ctor_get(v_a_2802_, 0);
v___x_2806_ = lean_unbox(v_head_2805_);
if (v___x_2806_ == 0)
{
lean_object* v_tail_2807_; 
v_tail_2807_ = lean_ctor_get(v_a_2802_, 1);
lean_inc(v_tail_2807_);
lean_dec_ref(v_a_2802_);
v_a_2802_ = v_tail_2807_;
goto _start;
}
else
{
lean_object* v_tail_2809_; lean_object* v___x_2811_; uint8_t v_isShared_2812_; uint8_t v_isSharedCheck_2817_; 
lean_inc(v_head_2805_);
v_tail_2809_ = lean_ctor_get(v_a_2802_, 1);
v_isSharedCheck_2817_ = !lean_is_exclusive(v_a_2802_);
if (v_isSharedCheck_2817_ == 0)
{
lean_object* v_unused_2818_; 
v_unused_2818_ = lean_ctor_get(v_a_2802_, 0);
lean_dec(v_unused_2818_);
v___x_2811_ = v_a_2802_;
v_isShared_2812_ = v_isSharedCheck_2817_;
goto v_resetjp_2810_;
}
else
{
lean_inc(v_tail_2809_);
lean_dec(v_a_2802_);
v___x_2811_ = lean_box(0);
v_isShared_2812_ = v_isSharedCheck_2817_;
goto v_resetjp_2810_;
}
v_resetjp_2810_:
{
lean_object* v___x_2814_; 
if (v_isShared_2812_ == 0)
{
lean_ctor_set(v___x_2811_, 1, v_a_2803_);
v___x_2814_ = v___x_2811_;
goto v_reusejp_2813_;
}
else
{
lean_object* v_reuseFailAlloc_2816_; 
v_reuseFailAlloc_2816_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2816_, 0, v_head_2805_);
lean_ctor_set(v_reuseFailAlloc_2816_, 1, v_a_2803_);
v___x_2814_ = v_reuseFailAlloc_2816_;
goto v_reusejp_2813_;
}
v_reusejp_2813_:
{
v_a_2802_ = v_tail_2809_;
v_a_2803_ = v___x_2814_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__5(lean_object* v_gs_2819_, lean_object* v_x_2820_, lean_object* v_x_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_){
_start:
{
if (lean_obj_tag(v_x_2820_) == 0)
{
lean_object* v___x_2827_; lean_object* v___x_2828_; 
lean_dec(v_gs_2819_);
v___x_2827_ = l_List_reverse___redArg(v_x_2821_);
v___x_2828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2828_, 0, v___x_2827_);
return v___x_2828_;
}
else
{
lean_object* v_head_2829_; lean_object* v_snd_2830_; lean_object* v_fst_2831_; lean_object* v_snd_2832_; lean_object* v_tail_2833_; lean_object* v___x_2835_; uint8_t v_isShared_2836_; uint8_t v_isSharedCheck_2957_; 
v_head_2829_ = lean_ctor_get(v_x_2820_, 0);
lean_inc(v_head_2829_);
v_snd_2830_ = lean_ctor_get(v_head_2829_, 1);
v_fst_2831_ = lean_ctor_get(v_snd_2830_, 0);
lean_inc(v_fst_2831_);
v_snd_2832_ = lean_ctor_get(v_snd_2830_, 1);
lean_inc(v_snd_2832_);
v_tail_2833_ = lean_ctor_get(v_x_2820_, 1);
v_isSharedCheck_2957_ = !lean_is_exclusive(v_x_2820_);
if (v_isSharedCheck_2957_ == 0)
{
lean_object* v_unused_2958_; 
v_unused_2958_ = lean_ctor_get(v_x_2820_, 0);
lean_dec(v_unused_2958_);
v___x_2835_ = v_x_2820_;
v_isShared_2836_ = v_isSharedCheck_2957_;
goto v_resetjp_2834_;
}
else
{
lean_inc(v_tail_2833_);
lean_dec(v_x_2820_);
v___x_2835_ = lean_box(0);
v_isShared_2836_ = v_isSharedCheck_2957_;
goto v_resetjp_2834_;
}
v_resetjp_2834_:
{
lean_object* v_fst_2837_; lean_object* v_fst_2838_; lean_object* v_snd_2839_; lean_object* v_variablesKept_2840_; lean_object* v_neqs_2841_; lean_object* v_fst_2843_; lean_object* v_snd_2844_; lean_object* v___y_2845_; lean_object* v___y_2846_; lean_object* v___y_2847_; lean_object* v___y_2848_; lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; 
v_fst_2837_ = lean_ctor_get(v_head_2829_, 0);
lean_inc(v_fst_2837_);
lean_dec(v_head_2829_);
v_fst_2838_ = lean_ctor_get(v_fst_2831_, 0);
lean_inc(v_fst_2838_);
v_snd_2839_ = lean_ctor_get(v_fst_2831_, 1);
lean_inc(v_snd_2839_);
lean_dec(v_fst_2831_);
v_variablesKept_2840_ = lean_ctor_get(v_snd_2832_, 0);
lean_inc_n(v_variablesKept_2840_, 2);
v_neqs_2841_ = lean_ctor_get(v_snd_2832_, 1);
lean_inc(v_neqs_2841_);
lean_dec(v_snd_2832_);
v___x_2864_ = lean_box(0);
v___x_2865_ = l_List_filterTR_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__3(v_variablesKept_2840_, v___x_2864_);
v___x_2866_ = l_List_lengthTR___redArg(v___x_2865_);
lean_dec(v___x_2865_);
if (lean_obj_tag(v_neqs_2841_) == 0)
{
lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; 
v___x_2867_ = lean_unsigned_to_nat(1u);
v___x_2868_ = lean_nat_sub(v___x_2866_, v___x_2867_);
lean_dec(v___x_2866_);
v___x_2869_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesProd(v___x_2868_, v_snd_2839_, v_fst_2838_, v___y_2822_, v___y_2823_, v___y_2824_, v___y_2825_);
lean_dec(v___x_2868_);
if (lean_obj_tag(v___x_2869_) == 0)
{
lean_object* v_a_2870_; lean_object* v_fst_2871_; lean_object* v_snd_2872_; 
v_a_2870_ = lean_ctor_get(v___x_2869_, 0);
lean_inc(v_a_2870_);
lean_dec_ref(v___x_2869_);
v_fst_2871_ = lean_ctor_get(v_a_2870_, 0);
lean_inc(v_fst_2871_);
v_snd_2872_ = lean_ctor_get(v_a_2870_, 1);
lean_inc(v_snd_2872_);
lean_dec(v_a_2870_);
v_fst_2843_ = v_fst_2871_;
v_snd_2844_ = v_snd_2872_;
v___y_2845_ = v___y_2822_;
v___y_2846_ = v___y_2823_;
v___y_2847_ = v___y_2824_;
v___y_2848_ = v___y_2825_;
goto v___jp_2842_;
}
else
{
lean_object* v_a_2873_; lean_object* v___x_2875_; uint8_t v_isShared_2876_; uint8_t v_isSharedCheck_2880_; 
lean_dec(v_variablesKept_2840_);
lean_dec(v_fst_2837_);
lean_del_object(v___x_2835_);
lean_dec(v_tail_2833_);
lean_dec(v_x_2821_);
lean_dec(v_gs_2819_);
v_a_2873_ = lean_ctor_get(v___x_2869_, 0);
v_isSharedCheck_2880_ = !lean_is_exclusive(v___x_2869_);
if (v_isSharedCheck_2880_ == 0)
{
v___x_2875_ = v___x_2869_;
v_isShared_2876_ = v_isSharedCheck_2880_;
goto v_resetjp_2874_;
}
else
{
lean_inc(v_a_2873_);
lean_dec(v___x_2869_);
v___x_2875_ = lean_box(0);
v_isShared_2876_ = v_isSharedCheck_2880_;
goto v_resetjp_2874_;
}
v_resetjp_2874_:
{
lean_object* v___x_2878_; 
if (v_isShared_2876_ == 0)
{
v___x_2878_ = v___x_2875_;
goto v_reusejp_2877_;
}
else
{
lean_object* v_reuseFailAlloc_2879_; 
v_reuseFailAlloc_2879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2879_, 0, v_a_2873_);
v___x_2878_ = v_reuseFailAlloc_2879_;
goto v_reusejp_2877_;
}
v_reusejp_2877_:
{
return v___x_2878_;
}
}
}
}
else
{
lean_object* v_val_2881_; lean_object* v___x_2882_; lean_object* v_zero_2883_; uint8_t v_isZero_2884_; 
v_val_2881_ = lean_ctor_get(v_neqs_2841_, 0);
lean_inc(v_val_2881_);
lean_dec_ref(v_neqs_2841_);
v___x_2882_ = lean_box(0);
v_zero_2883_ = lean_unsigned_to_nat(0u);
v_isZero_2884_ = lean_nat_dec_eq(v_val_2881_, v_zero_2883_);
if (v_isZero_2884_ == 1)
{
lean_object* v___x_2885_; 
lean_dec(v_val_2881_);
v___x_2885_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesProd(v___x_2866_, v_snd_2839_, v_fst_2838_, v___y_2822_, v___y_2823_, v___y_2824_, v___y_2825_);
lean_dec(v___x_2866_);
if (lean_obj_tag(v___x_2885_) == 0)
{
lean_object* v_a_2886_; lean_object* v_fst_2887_; lean_object* v_snd_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; 
v_a_2886_ = lean_ctor_get(v___x_2885_, 0);
lean_inc(v_a_2886_);
lean_dec_ref(v___x_2885_);
v_fst_2887_ = lean_ctor_get(v_a_2886_, 0);
lean_inc(v_fst_2887_);
v_snd_2888_ = lean_ctor_get(v_a_2886_, 1);
lean_inc(v_snd_2888_);
lean_dec(v_a_2886_);
v___x_2889_ = l_List_getLast_x21___redArg(v___x_2882_, v_snd_2888_);
v___x_2890_ = l_Lean_MVarId_tryClear(v_fst_2887_, v___x_2889_, v___y_2822_, v___y_2823_, v___y_2824_, v___y_2825_);
if (lean_obj_tag(v___x_2890_) == 0)
{
lean_object* v_a_2891_; 
v_a_2891_ = lean_ctor_get(v___x_2890_, 0);
lean_inc(v_a_2891_);
lean_dec_ref(v___x_2890_);
v_fst_2843_ = v_a_2891_;
v_snd_2844_ = v_snd_2888_;
v___y_2845_ = v___y_2822_;
v___y_2846_ = v___y_2823_;
v___y_2847_ = v___y_2824_;
v___y_2848_ = v___y_2825_;
goto v___jp_2842_;
}
else
{
lean_object* v_a_2892_; lean_object* v___x_2894_; uint8_t v_isShared_2895_; uint8_t v_isSharedCheck_2899_; 
lean_dec(v_snd_2888_);
lean_dec(v_variablesKept_2840_);
lean_dec(v_fst_2837_);
lean_del_object(v___x_2835_);
lean_dec(v_tail_2833_);
lean_dec(v_x_2821_);
lean_dec(v_gs_2819_);
v_a_2892_ = lean_ctor_get(v___x_2890_, 0);
v_isSharedCheck_2899_ = !lean_is_exclusive(v___x_2890_);
if (v_isSharedCheck_2899_ == 0)
{
v___x_2894_ = v___x_2890_;
v_isShared_2895_ = v_isSharedCheck_2899_;
goto v_resetjp_2893_;
}
else
{
lean_inc(v_a_2892_);
lean_dec(v___x_2890_);
v___x_2894_ = lean_box(0);
v_isShared_2895_ = v_isSharedCheck_2899_;
goto v_resetjp_2893_;
}
v_resetjp_2893_:
{
lean_object* v___x_2897_; 
if (v_isShared_2895_ == 0)
{
v___x_2897_ = v___x_2894_;
goto v_reusejp_2896_;
}
else
{
lean_object* v_reuseFailAlloc_2898_; 
v_reuseFailAlloc_2898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2898_, 0, v_a_2892_);
v___x_2897_ = v_reuseFailAlloc_2898_;
goto v_reusejp_2896_;
}
v_reusejp_2896_:
{
return v___x_2897_;
}
}
}
}
else
{
lean_object* v_a_2900_; lean_object* v___x_2902_; uint8_t v_isShared_2903_; uint8_t v_isSharedCheck_2907_; 
lean_dec(v_variablesKept_2840_);
lean_dec(v_fst_2837_);
lean_del_object(v___x_2835_);
lean_dec(v_tail_2833_);
lean_dec(v_x_2821_);
lean_dec(v_gs_2819_);
v_a_2900_ = lean_ctor_get(v___x_2885_, 0);
v_isSharedCheck_2907_ = !lean_is_exclusive(v___x_2885_);
if (v_isSharedCheck_2907_ == 0)
{
v___x_2902_ = v___x_2885_;
v_isShared_2903_ = v_isSharedCheck_2907_;
goto v_resetjp_2901_;
}
else
{
lean_inc(v_a_2900_);
lean_dec(v___x_2885_);
v___x_2902_ = lean_box(0);
v_isShared_2903_ = v_isSharedCheck_2907_;
goto v_resetjp_2901_;
}
v_resetjp_2901_:
{
lean_object* v___x_2905_; 
if (v_isShared_2903_ == 0)
{
v___x_2905_ = v___x_2902_;
goto v_reusejp_2904_;
}
else
{
lean_object* v_reuseFailAlloc_2906_; 
v_reuseFailAlloc_2906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2906_, 0, v_a_2900_);
v___x_2905_ = v_reuseFailAlloc_2906_;
goto v_reusejp_2904_;
}
v_reusejp_2904_:
{
return v___x_2905_;
}
}
}
}
else
{
lean_object* v___x_2908_; 
v___x_2908_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesProd(v___x_2866_, v_snd_2839_, v_fst_2838_, v___y_2822_, v___y_2823_, v___y_2824_, v___y_2825_);
lean_dec(v___x_2866_);
if (lean_obj_tag(v___x_2908_) == 0)
{
lean_object* v_a_2909_; lean_object* v_fst_2910_; lean_object* v_snd_2911_; lean_object* v_one_2912_; lean_object* v_n_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; 
v_a_2909_ = lean_ctor_get(v___x_2908_, 0);
lean_inc(v_a_2909_);
lean_dec_ref(v___x_2908_);
v_fst_2910_ = lean_ctor_get(v_a_2909_, 0);
lean_inc(v_fst_2910_);
v_snd_2911_ = lean_ctor_get(v_a_2909_, 1);
lean_inc(v_snd_2911_);
lean_dec(v_a_2909_);
v_one_2912_ = lean_unsigned_to_nat(1u);
v_n_2913_ = lean_nat_sub(v_val_2881_, v_one_2912_);
lean_dec(v_val_2881_);
v___x_2914_ = l_List_getLast_x21___redArg(v___x_2882_, v_snd_2911_);
v___x_2915_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesProd(v_n_2913_, v_fst_2910_, v___x_2914_, v___y_2822_, v___y_2823_, v___y_2824_, v___y_2825_);
lean_dec(v_n_2913_);
if (lean_obj_tag(v___x_2915_) == 0)
{
lean_object* v_a_2916_; lean_object* v_fst_2917_; lean_object* v_snd_2918_; lean_object* v___x_2919_; lean_object* v___x_2920_; 
v_a_2916_ = lean_ctor_get(v___x_2915_, 0);
lean_inc(v_a_2916_);
lean_dec_ref(v___x_2915_);
v_fst_2917_ = lean_ctor_get(v_a_2916_, 0);
lean_inc(v_fst_2917_);
v_snd_2918_ = lean_ctor_get(v_a_2916_, 1);
lean_inc_n(v_snd_2918_, 2);
lean_dec(v_a_2916_);
v___x_2919_ = lean_array_mk(v_snd_2918_);
v___x_2920_ = l_Lean_MVarId_revert(v_fst_2917_, v___x_2919_, v_isZero_2884_, v_isZero_2884_, v___y_2822_, v___y_2823_, v___y_2824_, v___y_2825_);
if (lean_obj_tag(v___x_2920_) == 0)
{
lean_object* v_a_2921_; lean_object* v_snd_2922_; lean_object* v___x_2923_; 
v_a_2921_ = lean_ctor_get(v___x_2920_, 0);
lean_inc(v_a_2921_);
lean_dec_ref(v___x_2920_);
v_snd_2922_ = lean_ctor_get(v_a_2921_, 1);
lean_inc(v_snd_2922_);
lean_dec(v_a_2921_);
v___x_2923_ = l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__4(v_snd_2922_, v_snd_2918_, v___y_2822_, v___y_2823_, v___y_2824_, v___y_2825_);
lean_dec(v_snd_2918_);
if (lean_obj_tag(v___x_2923_) == 0)
{
lean_object* v_a_2924_; 
v_a_2924_ = lean_ctor_get(v___x_2923_, 0);
lean_inc(v_a_2924_);
lean_dec_ref(v___x_2923_);
v_fst_2843_ = v_a_2924_;
v_snd_2844_ = v_snd_2911_;
v___y_2845_ = v___y_2822_;
v___y_2846_ = v___y_2823_;
v___y_2847_ = v___y_2824_;
v___y_2848_ = v___y_2825_;
goto v___jp_2842_;
}
else
{
lean_object* v_a_2925_; lean_object* v___x_2927_; uint8_t v_isShared_2928_; uint8_t v_isSharedCheck_2932_; 
lean_dec(v_snd_2911_);
lean_dec(v_variablesKept_2840_);
lean_dec(v_fst_2837_);
lean_del_object(v___x_2835_);
lean_dec(v_tail_2833_);
lean_dec(v_x_2821_);
lean_dec(v_gs_2819_);
v_a_2925_ = lean_ctor_get(v___x_2923_, 0);
v_isSharedCheck_2932_ = !lean_is_exclusive(v___x_2923_);
if (v_isSharedCheck_2932_ == 0)
{
v___x_2927_ = v___x_2923_;
v_isShared_2928_ = v_isSharedCheck_2932_;
goto v_resetjp_2926_;
}
else
{
lean_inc(v_a_2925_);
lean_dec(v___x_2923_);
v___x_2927_ = lean_box(0);
v_isShared_2928_ = v_isSharedCheck_2932_;
goto v_resetjp_2926_;
}
v_resetjp_2926_:
{
lean_object* v___x_2930_; 
if (v_isShared_2928_ == 0)
{
v___x_2930_ = v___x_2927_;
goto v_reusejp_2929_;
}
else
{
lean_object* v_reuseFailAlloc_2931_; 
v_reuseFailAlloc_2931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2931_, 0, v_a_2925_);
v___x_2930_ = v_reuseFailAlloc_2931_;
goto v_reusejp_2929_;
}
v_reusejp_2929_:
{
return v___x_2930_;
}
}
}
}
else
{
lean_object* v_a_2933_; lean_object* v___x_2935_; uint8_t v_isShared_2936_; uint8_t v_isSharedCheck_2940_; 
lean_dec(v_snd_2918_);
lean_dec(v_snd_2911_);
lean_dec(v_variablesKept_2840_);
lean_dec(v_fst_2837_);
lean_del_object(v___x_2835_);
lean_dec(v_tail_2833_);
lean_dec(v_x_2821_);
lean_dec(v_gs_2819_);
v_a_2933_ = lean_ctor_get(v___x_2920_, 0);
v_isSharedCheck_2940_ = !lean_is_exclusive(v___x_2920_);
if (v_isSharedCheck_2940_ == 0)
{
v___x_2935_ = v___x_2920_;
v_isShared_2936_ = v_isSharedCheck_2940_;
goto v_resetjp_2934_;
}
else
{
lean_inc(v_a_2933_);
lean_dec(v___x_2920_);
v___x_2935_ = lean_box(0);
v_isShared_2936_ = v_isSharedCheck_2940_;
goto v_resetjp_2934_;
}
v_resetjp_2934_:
{
lean_object* v___x_2938_; 
if (v_isShared_2936_ == 0)
{
v___x_2938_ = v___x_2935_;
goto v_reusejp_2937_;
}
else
{
lean_object* v_reuseFailAlloc_2939_; 
v_reuseFailAlloc_2939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2939_, 0, v_a_2933_);
v___x_2938_ = v_reuseFailAlloc_2939_;
goto v_reusejp_2937_;
}
v_reusejp_2937_:
{
return v___x_2938_;
}
}
}
}
else
{
lean_object* v_a_2941_; lean_object* v___x_2943_; uint8_t v_isShared_2944_; uint8_t v_isSharedCheck_2948_; 
lean_dec(v_snd_2911_);
lean_dec(v_variablesKept_2840_);
lean_dec(v_fst_2837_);
lean_del_object(v___x_2835_);
lean_dec(v_tail_2833_);
lean_dec(v_x_2821_);
lean_dec(v_gs_2819_);
v_a_2941_ = lean_ctor_get(v___x_2915_, 0);
v_isSharedCheck_2948_ = !lean_is_exclusive(v___x_2915_);
if (v_isSharedCheck_2948_ == 0)
{
v___x_2943_ = v___x_2915_;
v_isShared_2944_ = v_isSharedCheck_2948_;
goto v_resetjp_2942_;
}
else
{
lean_inc(v_a_2941_);
lean_dec(v___x_2915_);
v___x_2943_ = lean_box(0);
v_isShared_2944_ = v_isSharedCheck_2948_;
goto v_resetjp_2942_;
}
v_resetjp_2942_:
{
lean_object* v___x_2946_; 
if (v_isShared_2944_ == 0)
{
v___x_2946_ = v___x_2943_;
goto v_reusejp_2945_;
}
else
{
lean_object* v_reuseFailAlloc_2947_; 
v_reuseFailAlloc_2947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2947_, 0, v_a_2941_);
v___x_2946_ = v_reuseFailAlloc_2947_;
goto v_reusejp_2945_;
}
v_reusejp_2945_:
{
return v___x_2946_;
}
}
}
}
else
{
lean_object* v_a_2949_; lean_object* v___x_2951_; uint8_t v_isShared_2952_; uint8_t v_isSharedCheck_2956_; 
lean_dec(v_val_2881_);
lean_dec(v_variablesKept_2840_);
lean_dec(v_fst_2837_);
lean_del_object(v___x_2835_);
lean_dec(v_tail_2833_);
lean_dec(v_x_2821_);
lean_dec(v_gs_2819_);
v_a_2949_ = lean_ctor_get(v___x_2908_, 0);
v_isSharedCheck_2956_ = !lean_is_exclusive(v___x_2908_);
if (v_isSharedCheck_2956_ == 0)
{
v___x_2951_ = v___x_2908_;
v_isShared_2952_ = v_isSharedCheck_2956_;
goto v_resetjp_2950_;
}
else
{
lean_inc(v_a_2949_);
lean_dec(v___x_2908_);
v___x_2951_ = lean_box(0);
v_isShared_2952_ = v_isSharedCheck_2956_;
goto v_resetjp_2950_;
}
v_resetjp_2950_:
{
lean_object* v___x_2954_; 
if (v_isShared_2952_ == 0)
{
v___x_2954_ = v___x_2951_;
goto v_reusejp_2953_;
}
else
{
lean_object* v_reuseFailAlloc_2955_; 
v_reuseFailAlloc_2955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2955_, 0, v_a_2949_);
v___x_2954_ = v_reuseFailAlloc_2955_;
goto v_reusejp_2953_;
}
v_reusejp_2953_:
{
return v___x_2954_;
}
}
}
}
}
v___jp_2842_:
{
lean_object* v___f_2849_; lean_object* v___x_2850_; 
lean_inc(v_fst_2843_);
lean_inc(v_gs_2819_);
v___f_2849_ = lean_alloc_closure((void*)(l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__5___lam__0___boxed), 10, 5);
lean_closure_set(v___f_2849_, 0, v_gs_2819_);
lean_closure_set(v___f_2849_, 1, v_variablesKept_2840_);
lean_closure_set(v___f_2849_, 2, v_snd_2844_);
lean_closure_set(v___f_2849_, 3, v_fst_2837_);
lean_closure_set(v___f_2849_, 4, v_fst_2843_);
v___x_2850_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor_spec__0___redArg(v_fst_2843_, v___f_2849_, v___y_2845_, v___y_2846_, v___y_2847_, v___y_2848_);
if (lean_obj_tag(v___x_2850_) == 0)
{
lean_object* v_a_2851_; lean_object* v___x_2853_; 
v_a_2851_ = lean_ctor_get(v___x_2850_, 0);
lean_inc(v_a_2851_);
lean_dec_ref(v___x_2850_);
if (v_isShared_2836_ == 0)
{
lean_ctor_set(v___x_2835_, 1, v_x_2821_);
lean_ctor_set(v___x_2835_, 0, v_a_2851_);
v___x_2853_ = v___x_2835_;
goto v_reusejp_2852_;
}
else
{
lean_object* v_reuseFailAlloc_2855_; 
v_reuseFailAlloc_2855_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2855_, 0, v_a_2851_);
lean_ctor_set(v_reuseFailAlloc_2855_, 1, v_x_2821_);
v___x_2853_ = v_reuseFailAlloc_2855_;
goto v_reusejp_2852_;
}
v_reusejp_2852_:
{
v_x_2820_ = v_tail_2833_;
v_x_2821_ = v___x_2853_;
goto _start;
}
}
else
{
lean_object* v_a_2856_; lean_object* v___x_2858_; uint8_t v_isShared_2859_; uint8_t v_isSharedCheck_2863_; 
lean_del_object(v___x_2835_);
lean_dec(v_tail_2833_);
lean_dec(v_x_2821_);
lean_dec(v_gs_2819_);
v_a_2856_ = lean_ctor_get(v___x_2850_, 0);
v_isSharedCheck_2863_ = !lean_is_exclusive(v___x_2850_);
if (v_isSharedCheck_2863_ == 0)
{
v___x_2858_ = v___x_2850_;
v_isShared_2859_ = v_isSharedCheck_2863_;
goto v_resetjp_2857_;
}
else
{
lean_inc(v_a_2856_);
lean_dec(v___x_2850_);
v___x_2858_ = lean_box(0);
v_isShared_2859_ = v_isSharedCheck_2863_;
goto v_resetjp_2857_;
}
v_resetjp_2857_:
{
lean_object* v___x_2861_; 
if (v_isShared_2859_ == 0)
{
v___x_2861_ = v___x_2858_;
goto v_reusejp_2860_;
}
else
{
lean_object* v_reuseFailAlloc_2862_; 
v_reuseFailAlloc_2862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2862_, 0, v_a_2856_);
v___x_2861_ = v_reuseFailAlloc_2862_;
goto v_reusejp_2860_;
}
v_reusejp_2860_:
{
return v___x_2861_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__5___boxed(lean_object* v_gs_2959_, lean_object* v_x_2960_, lean_object* v_x_2961_, lean_object* v___y_2962_, lean_object* v___y_2963_, lean_object* v___y_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_){
_start:
{
lean_object* v_res_2967_; 
v_res_2967_ = l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__5(v_gs_2959_, v_x_2960_, v_x_2961_, v___y_2962_, v___y_2963_, v___y_2964_, v___y_2965_);
lean_dec(v___y_2965_);
lean_dec_ref(v___y_2964_);
lean_dec(v___y_2963_);
lean_dec_ref(v___y_2962_);
return v_res_2967_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive(lean_object* v_mvar_2968_, lean_object* v_cs_2969_, lean_object* v_gs_2970_, lean_object* v_s_2971_, lean_object* v_h_2972_, lean_object* v_a_2973_, lean_object* v_a_2974_, lean_object* v_a_2975_, lean_object* v_a_2976_){
_start:
{
lean_object* v___x_2978_; lean_object* v_zero_2979_; uint8_t v_isZero_2980_; 
v___x_2978_ = l_List_lengthTR___redArg(v_s_2971_);
v_zero_2979_ = lean_unsigned_to_nat(0u);
v_isZero_2980_ = lean_nat_dec_eq(v___x_2978_, v_zero_2979_);
if (v_isZero_2980_ == 1)
{
lean_object* v___x_2981_; uint8_t v___x_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; 
lean_dec(v___x_2978_);
lean_dec(v_s_2971_);
lean_dec(v_gs_2970_);
lean_dec(v_cs_2969_);
v___x_2981_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toCases___closed__0));
v___x_2982_ = 0;
v___x_2983_ = lean_box(0);
v___x_2984_ = l_Lean_MVarId_cases(v_mvar_2968_, v_h_2972_, v___x_2981_, v___x_2982_, v___x_2983_, v_a_2973_, v_a_2974_, v_a_2975_, v_a_2976_);
if (lean_obj_tag(v___x_2984_) == 0)
{
lean_object* v___x_2986_; uint8_t v_isShared_2987_; uint8_t v_isSharedCheck_2992_; 
v_isSharedCheck_2992_ = !lean_is_exclusive(v___x_2984_);
if (v_isSharedCheck_2992_ == 0)
{
lean_object* v_unused_2993_; 
v_unused_2993_ = lean_ctor_get(v___x_2984_, 0);
lean_dec(v_unused_2993_);
v___x_2986_ = v___x_2984_;
v_isShared_2987_ = v_isSharedCheck_2992_;
goto v_resetjp_2985_;
}
else
{
lean_dec(v___x_2984_);
v___x_2986_ = lean_box(0);
v_isShared_2987_ = v_isSharedCheck_2992_;
goto v_resetjp_2985_;
}
v_resetjp_2985_:
{
lean_object* v___x_2988_; lean_object* v___x_2990_; 
v___x_2988_ = lean_box(0);
if (v_isShared_2987_ == 0)
{
lean_ctor_set(v___x_2986_, 0, v___x_2988_);
v___x_2990_ = v___x_2986_;
goto v_reusejp_2989_;
}
else
{
lean_object* v_reuseFailAlloc_2991_; 
v_reuseFailAlloc_2991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2991_, 0, v___x_2988_);
v___x_2990_ = v_reuseFailAlloc_2991_;
goto v_reusejp_2989_;
}
v_reusejp_2989_:
{
return v___x_2990_;
}
}
}
else
{
lean_object* v_a_2994_; lean_object* v___x_2996_; uint8_t v_isShared_2997_; uint8_t v_isSharedCheck_3001_; 
v_a_2994_ = lean_ctor_get(v___x_2984_, 0);
v_isSharedCheck_3001_ = !lean_is_exclusive(v___x_2984_);
if (v_isSharedCheck_3001_ == 0)
{
v___x_2996_ = v___x_2984_;
v_isShared_2997_ = v_isSharedCheck_3001_;
goto v_resetjp_2995_;
}
else
{
lean_inc(v_a_2994_);
lean_dec(v___x_2984_);
v___x_2996_ = lean_box(0);
v_isShared_2997_ = v_isSharedCheck_3001_;
goto v_resetjp_2995_;
}
v_resetjp_2995_:
{
lean_object* v___x_2999_; 
if (v_isShared_2997_ == 0)
{
v___x_2999_ = v___x_2996_;
goto v_reusejp_2998_;
}
else
{
lean_object* v_reuseFailAlloc_3000_; 
v_reuseFailAlloc_3000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3000_, 0, v_a_2994_);
v___x_2999_ = v_reuseFailAlloc_3000_;
goto v_reusejp_2998_;
}
v_reusejp_2998_:
{
return v___x_2999_;
}
}
}
}
else
{
lean_object* v_one_3002_; lean_object* v_n_3003_; lean_object* v___x_3004_; 
v_one_3002_ = lean_unsigned_to_nat(1u);
v_n_3003_ = lean_nat_sub(v___x_2978_, v_one_3002_);
lean_dec(v___x_2978_);
v___x_3004_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesSum(v_n_3003_, v_mvar_2968_, v_h_2972_, v_a_2973_, v_a_2974_, v_a_2975_, v_a_2976_);
lean_dec(v_n_3003_);
if (lean_obj_tag(v___x_3004_) == 0)
{
lean_object* v_a_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; 
v_a_3005_ = lean_ctor_get(v___x_3004_, 0);
lean_inc(v_a_3005_);
lean_dec_ref(v___x_3004_);
v___x_3006_ = l_List_zipWith___at___00List_zip_spec__0(lean_box(0), lean_box(0), v_a_3005_, v_s_2971_);
v___x_3007_ = l_List_zipWith___at___00List_zip_spec__0(lean_box(0), lean_box(0), v_cs_2969_, v___x_3006_);
v___x_3008_ = lean_box(0);
v___x_3009_ = l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__5(v_gs_2970_, v___x_3007_, v___x_3008_, v_a_2973_, v_a_2974_, v_a_2975_, v_a_2976_);
if (lean_obj_tag(v___x_3009_) == 0)
{
lean_object* v___x_3011_; uint8_t v_isShared_3012_; uint8_t v_isSharedCheck_3017_; 
v_isSharedCheck_3017_ = !lean_is_exclusive(v___x_3009_);
if (v_isSharedCheck_3017_ == 0)
{
lean_object* v_unused_3018_; 
v_unused_3018_ = lean_ctor_get(v___x_3009_, 0);
lean_dec(v_unused_3018_);
v___x_3011_ = v___x_3009_;
v_isShared_3012_ = v_isSharedCheck_3017_;
goto v_resetjp_3010_;
}
else
{
lean_dec(v___x_3009_);
v___x_3011_ = lean_box(0);
v_isShared_3012_ = v_isSharedCheck_3017_;
goto v_resetjp_3010_;
}
v_resetjp_3010_:
{
lean_object* v___x_3013_; lean_object* v___x_3015_; 
v___x_3013_ = lean_box(0);
if (v_isShared_3012_ == 0)
{
lean_ctor_set(v___x_3011_, 0, v___x_3013_);
v___x_3015_ = v___x_3011_;
goto v_reusejp_3014_;
}
else
{
lean_object* v_reuseFailAlloc_3016_; 
v_reuseFailAlloc_3016_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3016_, 0, v___x_3013_);
v___x_3015_ = v_reuseFailAlloc_3016_;
goto v_reusejp_3014_;
}
v_reusejp_3014_:
{
return v___x_3015_;
}
}
}
else
{
lean_object* v_a_3019_; lean_object* v___x_3021_; uint8_t v_isShared_3022_; uint8_t v_isSharedCheck_3026_; 
v_a_3019_ = lean_ctor_get(v___x_3009_, 0);
v_isSharedCheck_3026_ = !lean_is_exclusive(v___x_3009_);
if (v_isSharedCheck_3026_ == 0)
{
v___x_3021_ = v___x_3009_;
v_isShared_3022_ = v_isSharedCheck_3026_;
goto v_resetjp_3020_;
}
else
{
lean_inc(v_a_3019_);
lean_dec(v___x_3009_);
v___x_3021_ = lean_box(0);
v_isShared_3022_ = v_isSharedCheck_3026_;
goto v_resetjp_3020_;
}
v_resetjp_3020_:
{
lean_object* v___x_3024_; 
if (v_isShared_3022_ == 0)
{
v___x_3024_ = v___x_3021_;
goto v_reusejp_3023_;
}
else
{
lean_object* v_reuseFailAlloc_3025_; 
v_reuseFailAlloc_3025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3025_, 0, v_a_3019_);
v___x_3024_ = v_reuseFailAlloc_3025_;
goto v_reusejp_3023_;
}
v_reusejp_3023_:
{
return v___x_3024_;
}
}
}
}
else
{
lean_object* v_a_3027_; lean_object* v___x_3029_; uint8_t v_isShared_3030_; uint8_t v_isSharedCheck_3034_; 
lean_dec(v_s_2971_);
lean_dec(v_gs_2970_);
lean_dec(v_cs_2969_);
v_a_3027_ = lean_ctor_get(v___x_3004_, 0);
v_isSharedCheck_3034_ = !lean_is_exclusive(v___x_3004_);
if (v_isSharedCheck_3034_ == 0)
{
v___x_3029_ = v___x_3004_;
v_isShared_3030_ = v_isSharedCheck_3034_;
goto v_resetjp_3028_;
}
else
{
lean_inc(v_a_3027_);
lean_dec(v___x_3004_);
v___x_3029_ = lean_box(0);
v_isShared_3030_ = v_isSharedCheck_3034_;
goto v_resetjp_3028_;
}
v_resetjp_3028_:
{
lean_object* v___x_3032_; 
if (v_isShared_3030_ == 0)
{
v___x_3032_ = v___x_3029_;
goto v_reusejp_3031_;
}
else
{
lean_object* v_reuseFailAlloc_3033_; 
v_reuseFailAlloc_3033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3033_, 0, v_a_3027_);
v___x_3032_ = v_reuseFailAlloc_3033_;
goto v_reusejp_3031_;
}
v_reusejp_3031_:
{
return v___x_3032_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive___boxed(lean_object* v_mvar_3035_, lean_object* v_cs_3036_, lean_object* v_gs_3037_, lean_object* v_s_3038_, lean_object* v_h_3039_, lean_object* v_a_3040_, lean_object* v_a_3041_, lean_object* v_a_3042_, lean_object* v_a_3043_, lean_object* v_a_3044_){
_start:
{
lean_object* v_res_3045_; 
v_res_3045_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive(v_mvar_3035_, v_cs_3036_, v_gs_3037_, v_s_3038_, v_h_3039_, v_a_3040_, v_a_3041_, v_a_3042_, v_a_3043_);
lean_dec(v_a_3043_);
lean_dec_ref(v_a_3042_);
lean_dec(v_a_3041_);
lean_dec_ref(v_a_3040_);
return v_res_3045_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__1___redArg(lean_object* v_type_3046_, lean_object* v_k_3047_, uint8_t v_cleanupAnnotations_3048_, uint8_t v_whnfType_3049_, lean_object* v___y_3050_, lean_object* v___y_3051_, lean_object* v___y_3052_, lean_object* v___y_3053_){
_start:
{
lean_object* v___f_3055_; lean_object* v___x_3056_; 
v___f_3055_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__4___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_3055_, 0, v_k_3047_);
v___x_3056_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_3046_, v___f_3055_, v_cleanupAnnotations_3048_, v_whnfType_3049_, v___y_3050_, v___y_3051_, v___y_3052_, v___y_3053_);
if (lean_obj_tag(v___x_3056_) == 0)
{
lean_object* v_a_3057_; lean_object* v___x_3059_; uint8_t v_isShared_3060_; uint8_t v_isSharedCheck_3064_; 
v_a_3057_ = lean_ctor_get(v___x_3056_, 0);
v_isSharedCheck_3064_ = !lean_is_exclusive(v___x_3056_);
if (v_isSharedCheck_3064_ == 0)
{
v___x_3059_ = v___x_3056_;
v_isShared_3060_ = v_isSharedCheck_3064_;
goto v_resetjp_3058_;
}
else
{
lean_inc(v_a_3057_);
lean_dec(v___x_3056_);
v___x_3059_ = lean_box(0);
v_isShared_3060_ = v_isSharedCheck_3064_;
goto v_resetjp_3058_;
}
v_resetjp_3058_:
{
lean_object* v___x_3062_; 
if (v_isShared_3060_ == 0)
{
v___x_3062_ = v___x_3059_;
goto v_reusejp_3061_;
}
else
{
lean_object* v_reuseFailAlloc_3063_; 
v_reuseFailAlloc_3063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3063_, 0, v_a_3057_);
v___x_3062_ = v_reuseFailAlloc_3063_;
goto v_reusejp_3061_;
}
v_reusejp_3061_:
{
return v___x_3062_;
}
}
}
else
{
lean_object* v_a_3065_; lean_object* v___x_3067_; uint8_t v_isShared_3068_; uint8_t v_isSharedCheck_3072_; 
v_a_3065_ = lean_ctor_get(v___x_3056_, 0);
v_isSharedCheck_3072_ = !lean_is_exclusive(v___x_3056_);
if (v_isSharedCheck_3072_ == 0)
{
v___x_3067_ = v___x_3056_;
v_isShared_3068_ = v_isSharedCheck_3072_;
goto v_resetjp_3066_;
}
else
{
lean_inc(v_a_3065_);
lean_dec(v___x_3056_);
v___x_3067_ = lean_box(0);
v_isShared_3068_ = v_isSharedCheck_3072_;
goto v_resetjp_3066_;
}
v_resetjp_3066_:
{
lean_object* v___x_3070_; 
if (v_isShared_3068_ == 0)
{
v___x_3070_ = v___x_3067_;
goto v_reusejp_3069_;
}
else
{
lean_object* v_reuseFailAlloc_3071_; 
v_reuseFailAlloc_3071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3071_, 0, v_a_3065_);
v___x_3070_ = v_reuseFailAlloc_3071_;
goto v_reusejp_3069_;
}
v_reusejp_3069_:
{
return v___x_3070_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__1___redArg___boxed(lean_object* v_type_3073_, lean_object* v_k_3074_, lean_object* v_cleanupAnnotations_3075_, lean_object* v_whnfType_3076_, lean_object* v___y_3077_, lean_object* v___y_3078_, lean_object* v___y_3079_, lean_object* v___y_3080_, lean_object* v___y_3081_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3082_; uint8_t v_whnfType_boxed_3083_; lean_object* v_res_3084_; 
v_cleanupAnnotations_boxed_3082_ = lean_unbox(v_cleanupAnnotations_3075_);
v_whnfType_boxed_3083_ = lean_unbox(v_whnfType_3076_);
v_res_3084_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__1___redArg(v_type_3073_, v_k_3074_, v_cleanupAnnotations_boxed_3082_, v_whnfType_boxed_3083_, v___y_3077_, v___y_3078_, v___y_3079_, v___y_3080_);
lean_dec(v___y_3080_);
lean_dec_ref(v___y_3079_);
lean_dec(v___y_3078_);
lean_dec_ref(v___y_3077_);
return v_res_3084_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__1(lean_object* v_00_u03b1_3085_, lean_object* v_type_3086_, lean_object* v_k_3087_, uint8_t v_cleanupAnnotations_3088_, uint8_t v_whnfType_3089_, lean_object* v___y_3090_, lean_object* v___y_3091_, lean_object* v___y_3092_, lean_object* v___y_3093_){
_start:
{
lean_object* v___x_3095_; 
v___x_3095_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__1___redArg(v_type_3086_, v_k_3087_, v_cleanupAnnotations_3088_, v_whnfType_3089_, v___y_3090_, v___y_3091_, v___y_3092_, v___y_3093_);
return v___x_3095_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__1___boxed(lean_object* v_00_u03b1_3096_, lean_object* v_type_3097_, lean_object* v_k_3098_, lean_object* v_cleanupAnnotations_3099_, lean_object* v_whnfType_3100_, lean_object* v___y_3101_, lean_object* v___y_3102_, lean_object* v___y_3103_, lean_object* v___y_3104_, lean_object* v___y_3105_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3106_; uint8_t v_whnfType_boxed_3107_; lean_object* v_res_3108_; 
v_cleanupAnnotations_boxed_3106_ = lean_unbox(v_cleanupAnnotations_3099_);
v_whnfType_boxed_3107_ = lean_unbox(v_whnfType_3100_);
v_res_3108_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__1(v_00_u03b1_3096_, v_type_3097_, v_k_3098_, v_cleanupAnnotations_boxed_3106_, v_whnfType_boxed_3107_, v___y_3101_, v___y_3102_, v___y_3103_, v___y_3104_);
lean_dec(v___y_3104_);
lean_dec_ref(v___y_3103_);
lean_dec(v___y_3102_);
lean_dec_ref(v___y_3101_);
return v_res_3108_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__3___redArg(lean_object* v_e_3109_, lean_object* v___y_3110_){
_start:
{
uint8_t v___x_3112_; 
v___x_3112_ = l_Lean_Expr_hasMVar(v_e_3109_);
if (v___x_3112_ == 0)
{
lean_object* v___x_3113_; 
v___x_3113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3113_, 0, v_e_3109_);
return v___x_3113_;
}
else
{
lean_object* v___x_3114_; lean_object* v_mctx_3115_; lean_object* v___x_3116_; lean_object* v_fst_3117_; lean_object* v_snd_3118_; lean_object* v___x_3119_; lean_object* v_cache_3120_; lean_object* v_zetaDeltaFVarIds_3121_; lean_object* v_postponed_3122_; lean_object* v_diag_3123_; lean_object* v___x_3125_; uint8_t v_isShared_3126_; uint8_t v_isSharedCheck_3132_; 
v___x_3114_ = lean_st_ref_get(v___y_3110_);
v_mctx_3115_ = lean_ctor_get(v___x_3114_, 0);
lean_inc_ref(v_mctx_3115_);
lean_dec(v___x_3114_);
v___x_3116_ = l_Lean_instantiateMVarsCore(v_mctx_3115_, v_e_3109_);
v_fst_3117_ = lean_ctor_get(v___x_3116_, 0);
lean_inc(v_fst_3117_);
v_snd_3118_ = lean_ctor_get(v___x_3116_, 1);
lean_inc(v_snd_3118_);
lean_dec_ref(v___x_3116_);
v___x_3119_ = lean_st_ref_take(v___y_3110_);
v_cache_3120_ = lean_ctor_get(v___x_3119_, 1);
v_zetaDeltaFVarIds_3121_ = lean_ctor_get(v___x_3119_, 2);
v_postponed_3122_ = lean_ctor_get(v___x_3119_, 3);
v_diag_3123_ = lean_ctor_get(v___x_3119_, 4);
v_isSharedCheck_3132_ = !lean_is_exclusive(v___x_3119_);
if (v_isSharedCheck_3132_ == 0)
{
lean_object* v_unused_3133_; 
v_unused_3133_ = lean_ctor_get(v___x_3119_, 0);
lean_dec(v_unused_3133_);
v___x_3125_ = v___x_3119_;
v_isShared_3126_ = v_isSharedCheck_3132_;
goto v_resetjp_3124_;
}
else
{
lean_inc(v_diag_3123_);
lean_inc(v_postponed_3122_);
lean_inc(v_zetaDeltaFVarIds_3121_);
lean_inc(v_cache_3120_);
lean_dec(v___x_3119_);
v___x_3125_ = lean_box(0);
v_isShared_3126_ = v_isSharedCheck_3132_;
goto v_resetjp_3124_;
}
v_resetjp_3124_:
{
lean_object* v___x_3128_; 
if (v_isShared_3126_ == 0)
{
lean_ctor_set(v___x_3125_, 0, v_snd_3118_);
v___x_3128_ = v___x_3125_;
goto v_reusejp_3127_;
}
else
{
lean_object* v_reuseFailAlloc_3131_; 
v_reuseFailAlloc_3131_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3131_, 0, v_snd_3118_);
lean_ctor_set(v_reuseFailAlloc_3131_, 1, v_cache_3120_);
lean_ctor_set(v_reuseFailAlloc_3131_, 2, v_zetaDeltaFVarIds_3121_);
lean_ctor_set(v_reuseFailAlloc_3131_, 3, v_postponed_3122_);
lean_ctor_set(v_reuseFailAlloc_3131_, 4, v_diag_3123_);
v___x_3128_ = v_reuseFailAlloc_3131_;
goto v_reusejp_3127_;
}
v_reusejp_3127_:
{
lean_object* v___x_3129_; lean_object* v___x_3130_; 
v___x_3129_ = lean_st_ref_set(v___y_3110_, v___x_3128_);
v___x_3130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3130_, 0, v_fst_3117_);
return v___x_3130_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__3___redArg___boxed(lean_object* v_e_3134_, lean_object* v___y_3135_, lean_object* v___y_3136_){
_start:
{
lean_object* v_res_3137_; 
v_res_3137_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__3___redArg(v_e_3134_, v___y_3135_);
lean_dec(v___y_3135_);
return v_res_3137_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__3(lean_object* v_e_3138_, lean_object* v___y_3139_, lean_object* v___y_3140_, lean_object* v___y_3141_, lean_object* v___y_3142_){
_start:
{
lean_object* v___x_3144_; 
v___x_3144_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__3___redArg(v_e_3138_, v___y_3140_);
return v___x_3144_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__3___boxed(lean_object* v_e_3145_, lean_object* v___y_3146_, lean_object* v___y_3147_, lean_object* v___y_3148_, lean_object* v___y_3149_, lean_object* v___y_3150_){
_start:
{
lean_object* v_res_3151_; 
v_res_3151_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__3(v_e_3145_, v___y_3146_, v___y_3147_, v___y_3148_, v___y_3149_);
lean_dec(v___y_3149_);
lean_dec_ref(v___y_3148_);
lean_dec(v___y_3147_);
lean_dec_ref(v___y_3146_);
return v_res_3151_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__4___redArg(lean_object* v_thm_3152_, lean_object* v___y_3153_){
_start:
{
lean_object* v___x_3155_; lean_object* v_env_3156_; lean_object* v_toConstantVal_3157_; lean_object* v_value_3158_; lean_object* v_all_3159_; uint8_t v___y_3161_; lean_object* v_type_3169_; uint8_t v___x_3170_; 
v___x_3155_ = lean_st_ref_get(v___y_3153_);
v_env_3156_ = lean_ctor_get(v___x_3155_, 0);
lean_inc_ref_n(v_env_3156_, 2);
lean_dec(v___x_3155_);
v_toConstantVal_3157_ = lean_ctor_get(v_thm_3152_, 0);
v_value_3158_ = lean_ctor_get(v_thm_3152_, 1);
v_all_3159_ = lean_ctor_get(v_thm_3152_, 2);
v_type_3169_ = lean_ctor_get(v_toConstantVal_3157_, 2);
v___x_3170_ = l_Lean_Environment_hasUnsafe(v_env_3156_, v_type_3169_);
if (v___x_3170_ == 0)
{
uint8_t v___x_3171_; 
v___x_3171_ = l_Lean_Environment_hasUnsafe(v_env_3156_, v_value_3158_);
v___y_3161_ = v___x_3171_;
goto v___jp_3160_;
}
else
{
lean_dec_ref(v_env_3156_);
v___y_3161_ = v___x_3170_;
goto v___jp_3160_;
}
v___jp_3160_:
{
if (v___y_3161_ == 0)
{
lean_object* v___x_3162_; lean_object* v___x_3163_; 
v___x_3162_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3162_, 0, v_thm_3152_);
v___x_3163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3163_, 0, v___x_3162_);
return v___x_3163_;
}
else
{
lean_object* v___x_3164_; uint8_t v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; 
lean_inc(v_all_3159_);
lean_inc_ref(v_value_3158_);
lean_inc_ref(v_toConstantVal_3157_);
lean_dec_ref(v_thm_3152_);
v___x_3164_ = lean_box(0);
v___x_3165_ = 0;
v___x_3166_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3166_, 0, v_toConstantVal_3157_);
lean_ctor_set(v___x_3166_, 1, v_value_3158_);
lean_ctor_set(v___x_3166_, 2, v___x_3164_);
lean_ctor_set(v___x_3166_, 3, v_all_3159_);
lean_ctor_set_uint8(v___x_3166_, sizeof(void*)*4, v___x_3165_);
v___x_3167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3167_, 0, v___x_3166_);
v___x_3168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3168_, 0, v___x_3167_);
return v___x_3168_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__4___redArg___boxed(lean_object* v_thm_3172_, lean_object* v___y_3173_, lean_object* v___y_3174_){
_start:
{
lean_object* v_res_3175_; 
v_res_3175_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__4___redArg(v_thm_3172_, v___y_3173_);
lean_dec(v___y_3173_);
return v_res_3175_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__4(lean_object* v_thm_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_, lean_object* v___y_3180_){
_start:
{
lean_object* v___x_3182_; 
v___x_3182_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__4___redArg(v_thm_3176_, v___y_3180_);
return v___x_3182_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__4___boxed(lean_object* v_thm_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_, lean_object* v___y_3188_){
_start:
{
lean_object* v_res_3189_; 
v_res_3189_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__4(v_thm_3183_, v___y_3184_, v___y_3185_, v___y_3186_, v___y_3187_);
lean_dec(v___y_3187_);
lean_dec_ref(v___y_3186_);
lean_dec(v___y_3185_);
lean_dec_ref(v___y_3184_);
return v_res_3189_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__5___redArg(lean_object* v_name_3190_, lean_object* v_levelParams_3191_, lean_object* v_type_3192_, lean_object* v_value_3193_, lean_object* v_hints_3194_, lean_object* v___y_3195_){
_start:
{
lean_object* v___x_3197_; uint8_t v___y_3199_; uint8_t v___y_3206_; lean_object* v_env_3209_; uint8_t v___x_3210_; 
v___x_3197_ = lean_st_ref_get(v___y_3195_);
v_env_3209_ = lean_ctor_get(v___x_3197_, 0);
lean_inc_ref_n(v_env_3209_, 2);
lean_dec(v___x_3197_);
v___x_3210_ = l_Lean_Environment_hasUnsafe(v_env_3209_, v_type_3192_);
if (v___x_3210_ == 0)
{
uint8_t v___x_3211_; 
v___x_3211_ = l_Lean_Environment_hasUnsafe(v_env_3209_, v_value_3193_);
v___y_3206_ = v___x_3211_;
goto v___jp_3205_;
}
else
{
lean_dec_ref(v_env_3209_);
v___y_3206_ = v___x_3210_;
goto v___jp_3205_;
}
v___jp_3198_:
{
lean_object* v___x_3200_; lean_object* v___x_3201_; lean_object* v___x_3202_; lean_object* v___x_3203_; lean_object* v___x_3204_; 
lean_inc(v_name_3190_);
v___x_3200_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3200_, 0, v_name_3190_);
lean_ctor_set(v___x_3200_, 1, v_levelParams_3191_);
lean_ctor_set(v___x_3200_, 2, v_type_3192_);
v___x_3201_ = lean_box(0);
v___x_3202_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3202_, 0, v_name_3190_);
lean_ctor_set(v___x_3202_, 1, v___x_3201_);
v___x_3203_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3203_, 0, v___x_3200_);
lean_ctor_set(v___x_3203_, 1, v_value_3193_);
lean_ctor_set(v___x_3203_, 2, v_hints_3194_);
lean_ctor_set(v___x_3203_, 3, v___x_3202_);
lean_ctor_set_uint8(v___x_3203_, sizeof(void*)*4, v___y_3199_);
v___x_3204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3204_, 0, v___x_3203_);
return v___x_3204_;
}
v___jp_3205_:
{
if (v___y_3206_ == 0)
{
uint8_t v___x_3207_; 
v___x_3207_ = 1;
v___y_3199_ = v___x_3207_;
goto v___jp_3198_;
}
else
{
uint8_t v___x_3208_; 
v___x_3208_ = 0;
v___y_3199_ = v___x_3208_;
goto v___jp_3198_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__5___redArg___boxed(lean_object* v_name_3212_, lean_object* v_levelParams_3213_, lean_object* v_type_3214_, lean_object* v_value_3215_, lean_object* v_hints_3216_, lean_object* v___y_3217_, lean_object* v___y_3218_){
_start:
{
lean_object* v_res_3219_; 
v_res_3219_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__5___redArg(v_name_3212_, v_levelParams_3213_, v_type_3214_, v_value_3215_, v_hints_3216_, v___y_3217_);
lean_dec(v___y_3217_);
return v_res_3219_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__5(lean_object* v_name_3220_, lean_object* v_levelParams_3221_, lean_object* v_type_3222_, lean_object* v_value_3223_, lean_object* v_hints_3224_, lean_object* v___y_3225_, lean_object* v___y_3226_, lean_object* v___y_3227_, lean_object* v___y_3228_){
_start:
{
lean_object* v___x_3230_; 
v___x_3230_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__5___redArg(v_name_3220_, v_levelParams_3221_, v_type_3222_, v_value_3223_, v_hints_3224_, v___y_3228_);
return v___x_3230_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__5___boxed(lean_object* v_name_3231_, lean_object* v_levelParams_3232_, lean_object* v_type_3233_, lean_object* v_value_3234_, lean_object* v_hints_3235_, lean_object* v___y_3236_, lean_object* v___y_3237_, lean_object* v___y_3238_, lean_object* v___y_3239_, lean_object* v___y_3240_){
_start:
{
lean_object* v_res_3241_; 
v_res_3241_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__5(v_name_3231_, v_levelParams_3232_, v_type_3233_, v_value_3234_, v_hints_3235_, v___y_3236_, v___y_3237_, v___y_3238_, v___y_3239_);
lean_dec(v___y_3239_);
lean_dec_ref(v___y_3238_);
lean_dec(v___y_3237_);
lean_dec_ref(v___y_3236_);
return v_res_3241_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__0(lean_object* v_univs_3242_, lean_object* v___x_3243_, lean_object* v___x_3244_, lean_object* v_x_3245_, lean_object* v_x_3246_, lean_object* v___y_3247_, lean_object* v___y_3248_, lean_object* v___y_3249_, lean_object* v___y_3250_){
_start:
{
if (lean_obj_tag(v_x_3245_) == 0)
{
lean_object* v___x_3252_; lean_object* v___x_3253_; 
lean_dec(v___x_3244_);
lean_dec(v___x_3243_);
lean_dec(v_univs_3242_);
v___x_3252_ = l_List_reverse___redArg(v_x_3246_);
v___x_3253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3253_, 0, v___x_3252_);
return v___x_3253_;
}
else
{
lean_object* v_head_3254_; lean_object* v_tail_3255_; lean_object* v___x_3257_; uint8_t v_isShared_3258_; uint8_t v_isSharedCheck_3273_; 
v_head_3254_ = lean_ctor_get(v_x_3245_, 0);
v_tail_3255_ = lean_ctor_get(v_x_3245_, 1);
v_isSharedCheck_3273_ = !lean_is_exclusive(v_x_3245_);
if (v_isSharedCheck_3273_ == 0)
{
v___x_3257_ = v_x_3245_;
v_isShared_3258_ = v_isSharedCheck_3273_;
goto v_resetjp_3256_;
}
else
{
lean_inc(v_tail_3255_);
lean_inc(v_head_3254_);
lean_dec(v_x_3245_);
v___x_3257_ = lean_box(0);
v_isShared_3258_ = v_isSharedCheck_3273_;
goto v_resetjp_3256_;
}
v_resetjp_3256_:
{
lean_object* v___x_3259_; 
lean_inc(v___x_3244_);
lean_inc(v___x_3243_);
lean_inc(v_univs_3242_);
v___x_3259_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp(v_univs_3242_, v___x_3243_, v___x_3244_, v_head_3254_, v___y_3247_, v___y_3248_, v___y_3249_, v___y_3250_);
if (lean_obj_tag(v___x_3259_) == 0)
{
lean_object* v_a_3260_; lean_object* v___x_3262_; 
v_a_3260_ = lean_ctor_get(v___x_3259_, 0);
lean_inc(v_a_3260_);
lean_dec_ref(v___x_3259_);
if (v_isShared_3258_ == 0)
{
lean_ctor_set(v___x_3257_, 1, v_x_3246_);
lean_ctor_set(v___x_3257_, 0, v_a_3260_);
v___x_3262_ = v___x_3257_;
goto v_reusejp_3261_;
}
else
{
lean_object* v_reuseFailAlloc_3264_; 
v_reuseFailAlloc_3264_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3264_, 0, v_a_3260_);
lean_ctor_set(v_reuseFailAlloc_3264_, 1, v_x_3246_);
v___x_3262_ = v_reuseFailAlloc_3264_;
goto v_reusejp_3261_;
}
v_reusejp_3261_:
{
v_x_3245_ = v_tail_3255_;
v_x_3246_ = v___x_3262_;
goto _start;
}
}
else
{
lean_object* v_a_3265_; lean_object* v___x_3267_; uint8_t v_isShared_3268_; uint8_t v_isSharedCheck_3272_; 
lean_del_object(v___x_3257_);
lean_dec(v_tail_3255_);
lean_dec(v_x_3246_);
lean_dec(v___x_3244_);
lean_dec(v___x_3243_);
lean_dec(v_univs_3242_);
v_a_3265_ = lean_ctor_get(v___x_3259_, 0);
v_isSharedCheck_3272_ = !lean_is_exclusive(v___x_3259_);
if (v_isSharedCheck_3272_ == 0)
{
v___x_3267_ = v___x_3259_;
v_isShared_3268_ = v_isSharedCheck_3272_;
goto v_resetjp_3266_;
}
else
{
lean_inc(v_a_3265_);
lean_dec(v___x_3259_);
v___x_3267_ = lean_box(0);
v_isShared_3268_ = v_isSharedCheck_3272_;
goto v_resetjp_3266_;
}
v_resetjp_3266_:
{
lean_object* v___x_3270_; 
if (v_isShared_3268_ == 0)
{
v___x_3270_ = v___x_3267_;
goto v_reusejp_3269_;
}
else
{
lean_object* v_reuseFailAlloc_3271_; 
v_reuseFailAlloc_3271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3271_, 0, v_a_3265_);
v___x_3270_ = v_reuseFailAlloc_3271_;
goto v_reusejp_3269_;
}
v_reusejp_3269_:
{
return v___x_3270_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__0___boxed(lean_object* v_univs_3274_, lean_object* v___x_3275_, lean_object* v___x_3276_, lean_object* v_x_3277_, lean_object* v_x_3278_, lean_object* v___y_3279_, lean_object* v___y_3280_, lean_object* v___y_3281_, lean_object* v___y_3282_, lean_object* v___y_3283_){
_start:
{
lean_object* v_res_3284_; 
v_res_3284_ = l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__0(v_univs_3274_, v___x_3275_, v___x_3276_, v_x_3277_, v_x_3278_, v___y_3279_, v___y_3280_, v___y_3281_, v___y_3282_);
lean_dec(v___y_3282_);
lean_dec_ref(v___y_3281_);
lean_dec(v___y_3280_);
lean_dec_ref(v___y_3279_);
return v_res_3284_;
}
}
static lean_object* _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___lam__0___closed__3(void){
_start:
{
lean_object* v___x_3289_; lean_object* v___x_3290_; 
v___x_3289_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___lam__0___closed__2));
v___x_3290_ = l_Lean_stringToMessageData(v___x_3289_);
return v___x_3290_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___lam__0(lean_object* v_name_3291_, lean_object* v_univs_3292_, lean_object* v_numParams_3293_, lean_object* v_ctors_3294_, lean_object* v___x_3295_, lean_object* v_fvars_3296_, lean_object* v_ty_3297_, lean_object* v___y_3298_, lean_object* v___y_3299_, lean_object* v___y_3300_, lean_object* v___y_3301_){
_start:
{
uint8_t v___x_3366_; 
v___x_3366_ = l_Lean_Expr_isProp(v_ty_3297_);
if (v___x_3366_ == 0)
{
lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v_a_3369_; lean_object* v___x_3371_; uint8_t v_isShared_3372_; uint8_t v_isSharedCheck_3376_; 
lean_dec_ref(v_fvars_3296_);
lean_dec(v___x_3295_);
lean_dec(v_ctors_3294_);
lean_dec(v_numParams_3293_);
lean_dec(v_univs_3292_);
lean_dec(v_name_3291_);
v___x_3367_ = lean_obj_once(&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___lam__0___closed__3, &l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___lam__0___closed__3_once, _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___lam__0___closed__3);
v___x_3368_ = l_Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0___redArg(v___x_3367_, v___y_3298_, v___y_3299_, v___y_3300_, v___y_3301_);
v_a_3369_ = lean_ctor_get(v___x_3368_, 0);
v_isSharedCheck_3376_ = !lean_is_exclusive(v___x_3368_);
if (v_isSharedCheck_3376_ == 0)
{
v___x_3371_ = v___x_3368_;
v_isShared_3372_ = v_isSharedCheck_3376_;
goto v_resetjp_3370_;
}
else
{
lean_inc(v_a_3369_);
lean_dec(v___x_3368_);
v___x_3371_ = lean_box(0);
v_isShared_3372_ = v_isSharedCheck_3376_;
goto v_resetjp_3370_;
}
v_resetjp_3370_:
{
lean_object* v___x_3374_; 
if (v_isShared_3372_ == 0)
{
v___x_3374_ = v___x_3371_;
goto v_reusejp_3373_;
}
else
{
lean_object* v_reuseFailAlloc_3375_; 
v_reuseFailAlloc_3375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3375_, 0, v_a_3369_);
v___x_3374_ = v_reuseFailAlloc_3375_;
goto v_reusejp_3373_;
}
v_reusejp_3373_:
{
return v___x_3374_;
}
}
}
else
{
goto v___jp_3303_;
}
v___jp_3303_:
{
lean_object* v___x_3304_; lean_object* v_lhs_3305_; lean_object* v_fvars_x27_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; 
lean_inc(v_univs_3292_);
v___x_3304_ = l_Lean_mkConst(v_name_3291_, v_univs_3292_);
v_lhs_3305_ = l_Lean_mkAppN(v___x_3304_, v_fvars_3296_);
lean_inc_ref(v_fvars_3296_);
v_fvars_x27_3306_ = lean_array_to_list(v_fvars_3296_);
v___x_3307_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__1___closed__1));
lean_inc(v_numParams_3293_);
lean_inc(v_fvars_x27_3306_);
v___x_3308_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), v_fvars_x27_3306_, v_fvars_x27_3306_, v_numParams_3293_, v___x_3307_);
v___x_3309_ = l_List_drop___redArg(v_numParams_3293_, v_fvars_x27_3306_);
lean_dec(v_fvars_x27_3306_);
v___x_3310_ = lean_box(0);
v___x_3311_ = l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__0(v_univs_3292_, v___x_3308_, v___x_3309_, v_ctors_3294_, v___x_3310_, v___y_3298_, v___y_3299_, v___y_3300_, v___y_3301_);
if (lean_obj_tag(v___x_3311_) == 0)
{
lean_object* v_a_3312_; lean_object* v___x_3313_; lean_object* v_fst_3314_; lean_object* v_snd_3315_; lean_object* v___x_3317_; uint8_t v_isShared_3318_; uint8_t v_isSharedCheck_3357_; 
v_a_3312_ = lean_ctor_get(v___x_3311_, 0);
lean_inc(v_a_3312_);
lean_dec_ref(v___x_3311_);
v___x_3313_ = l_List_unzipTR___redArg(v_a_3312_);
v_fst_3314_ = lean_ctor_get(v___x_3313_, 0);
v_snd_3315_ = lean_ctor_get(v___x_3313_, 1);
v_isSharedCheck_3357_ = !lean_is_exclusive(v___x_3313_);
if (v_isSharedCheck_3357_ == 0)
{
v___x_3317_ = v___x_3313_;
v_isShared_3318_ = v_isSharedCheck_3357_;
goto v_resetjp_3316_;
}
else
{
lean_inc(v_snd_3315_);
lean_inc(v_fst_3314_);
lean_dec(v___x_3313_);
v___x_3317_ = lean_box(0);
v_isShared_3318_ = v_isSharedCheck_3357_;
goto v_resetjp_3316_;
}
v_resetjp_3316_:
{
lean_object* v___x_3319_; uint8_t v___x_3320_; uint8_t v___x_3321_; uint8_t v___x_3322_; lean_object* v___x_3323_; 
v___x_3319_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkOrList(v_snd_3315_);
v___x_3320_ = 0;
v___x_3321_ = 1;
v___x_3322_ = 1;
lean_inc_ref(v___x_3319_);
v___x_3323_ = l_Lean_Meta_mkLambdaFVars(v_fvars_3296_, v___x_3319_, v___x_3320_, v___x_3321_, v___x_3320_, v___x_3321_, v___x_3322_, v___y_3298_, v___y_3299_, v___y_3300_, v___y_3301_);
if (lean_obj_tag(v___x_3323_) == 0)
{
lean_object* v_a_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; 
v_a_3324_ = lean_ctor_get(v___x_3323_, 0);
lean_inc(v_a_3324_);
lean_dec_ref(v___x_3323_);
v___x_3325_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___lam__0___closed__1));
v___x_3326_ = l_Lean_mkConst(v___x_3325_, v___x_3295_);
v___x_3327_ = l_Lean_mkAppB(v___x_3326_, v_lhs_3305_, v___x_3319_);
v___x_3328_ = l_Lean_Meta_mkForallFVars(v_fvars_3296_, v___x_3327_, v___x_3320_, v___x_3321_, v___x_3321_, v___x_3322_, v___y_3298_, v___y_3299_, v___y_3300_, v___y_3301_);
lean_dec_ref(v_fvars_3296_);
if (lean_obj_tag(v___x_3328_) == 0)
{
lean_object* v_a_3329_; lean_object* v___x_3331_; uint8_t v_isShared_3332_; uint8_t v_isSharedCheck_3340_; 
v_a_3329_ = lean_ctor_get(v___x_3328_, 0);
v_isSharedCheck_3340_ = !lean_is_exclusive(v___x_3328_);
if (v_isSharedCheck_3340_ == 0)
{
v___x_3331_ = v___x_3328_;
v_isShared_3332_ = v_isSharedCheck_3340_;
goto v_resetjp_3330_;
}
else
{
lean_inc(v_a_3329_);
lean_dec(v___x_3328_);
v___x_3331_ = lean_box(0);
v_isShared_3332_ = v_isSharedCheck_3340_;
goto v_resetjp_3330_;
}
v_resetjp_3330_:
{
lean_object* v___x_3334_; 
if (v_isShared_3318_ == 0)
{
lean_ctor_set(v___x_3317_, 1, v_a_3324_);
v___x_3334_ = v___x_3317_;
goto v_reusejp_3333_;
}
else
{
lean_object* v_reuseFailAlloc_3339_; 
v_reuseFailAlloc_3339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3339_, 0, v_fst_3314_);
lean_ctor_set(v_reuseFailAlloc_3339_, 1, v_a_3324_);
v___x_3334_ = v_reuseFailAlloc_3339_;
goto v_reusejp_3333_;
}
v_reusejp_3333_:
{
lean_object* v___x_3335_; lean_object* v___x_3337_; 
v___x_3335_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3335_, 0, v_a_3329_);
lean_ctor_set(v___x_3335_, 1, v___x_3334_);
if (v_isShared_3332_ == 0)
{
lean_ctor_set(v___x_3331_, 0, v___x_3335_);
v___x_3337_ = v___x_3331_;
goto v_reusejp_3336_;
}
else
{
lean_object* v_reuseFailAlloc_3338_; 
v_reuseFailAlloc_3338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3338_, 0, v___x_3335_);
v___x_3337_ = v_reuseFailAlloc_3338_;
goto v_reusejp_3336_;
}
v_reusejp_3336_:
{
return v___x_3337_;
}
}
}
}
else
{
lean_object* v_a_3341_; lean_object* v___x_3343_; uint8_t v_isShared_3344_; uint8_t v_isSharedCheck_3348_; 
lean_dec(v_a_3324_);
lean_del_object(v___x_3317_);
lean_dec(v_fst_3314_);
v_a_3341_ = lean_ctor_get(v___x_3328_, 0);
v_isSharedCheck_3348_ = !lean_is_exclusive(v___x_3328_);
if (v_isSharedCheck_3348_ == 0)
{
v___x_3343_ = v___x_3328_;
v_isShared_3344_ = v_isSharedCheck_3348_;
goto v_resetjp_3342_;
}
else
{
lean_inc(v_a_3341_);
lean_dec(v___x_3328_);
v___x_3343_ = lean_box(0);
v_isShared_3344_ = v_isSharedCheck_3348_;
goto v_resetjp_3342_;
}
v_resetjp_3342_:
{
lean_object* v___x_3346_; 
if (v_isShared_3344_ == 0)
{
v___x_3346_ = v___x_3343_;
goto v_reusejp_3345_;
}
else
{
lean_object* v_reuseFailAlloc_3347_; 
v_reuseFailAlloc_3347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3347_, 0, v_a_3341_);
v___x_3346_ = v_reuseFailAlloc_3347_;
goto v_reusejp_3345_;
}
v_reusejp_3345_:
{
return v___x_3346_;
}
}
}
}
else
{
lean_object* v_a_3349_; lean_object* v___x_3351_; uint8_t v_isShared_3352_; uint8_t v_isSharedCheck_3356_; 
lean_dec_ref(v___x_3319_);
lean_del_object(v___x_3317_);
lean_dec(v_fst_3314_);
lean_dec_ref(v_lhs_3305_);
lean_dec_ref(v_fvars_3296_);
lean_dec(v___x_3295_);
v_a_3349_ = lean_ctor_get(v___x_3323_, 0);
v_isSharedCheck_3356_ = !lean_is_exclusive(v___x_3323_);
if (v_isSharedCheck_3356_ == 0)
{
v___x_3351_ = v___x_3323_;
v_isShared_3352_ = v_isSharedCheck_3356_;
goto v_resetjp_3350_;
}
else
{
lean_inc(v_a_3349_);
lean_dec(v___x_3323_);
v___x_3351_ = lean_box(0);
v_isShared_3352_ = v_isSharedCheck_3356_;
goto v_resetjp_3350_;
}
v_resetjp_3350_:
{
lean_object* v___x_3354_; 
if (v_isShared_3352_ == 0)
{
v___x_3354_ = v___x_3351_;
goto v_reusejp_3353_;
}
else
{
lean_object* v_reuseFailAlloc_3355_; 
v_reuseFailAlloc_3355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3355_, 0, v_a_3349_);
v___x_3354_ = v_reuseFailAlloc_3355_;
goto v_reusejp_3353_;
}
v_reusejp_3353_:
{
return v___x_3354_;
}
}
}
}
}
else
{
lean_object* v_a_3358_; lean_object* v___x_3360_; uint8_t v_isShared_3361_; uint8_t v_isSharedCheck_3365_; 
lean_dec_ref(v_lhs_3305_);
lean_dec_ref(v_fvars_3296_);
lean_dec(v___x_3295_);
v_a_3358_ = lean_ctor_get(v___x_3311_, 0);
v_isSharedCheck_3365_ = !lean_is_exclusive(v___x_3311_);
if (v_isSharedCheck_3365_ == 0)
{
v___x_3360_ = v___x_3311_;
v_isShared_3361_ = v_isSharedCheck_3365_;
goto v_resetjp_3359_;
}
else
{
lean_inc(v_a_3358_);
lean_dec(v___x_3311_);
v___x_3360_ = lean_box(0);
v_isShared_3361_ = v_isSharedCheck_3365_;
goto v_resetjp_3359_;
}
v_resetjp_3359_:
{
lean_object* v___x_3363_; 
if (v_isShared_3361_ == 0)
{
v___x_3363_ = v___x_3360_;
goto v_reusejp_3362_;
}
else
{
lean_object* v_reuseFailAlloc_3364_; 
v_reuseFailAlloc_3364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3364_, 0, v_a_3358_);
v___x_3363_ = v_reuseFailAlloc_3364_;
goto v_reusejp_3362_;
}
v_reusejp_3362_:
{
return v___x_3363_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___lam__0___boxed(lean_object* v_name_3377_, lean_object* v_univs_3378_, lean_object* v_numParams_3379_, lean_object* v_ctors_3380_, lean_object* v___x_3381_, lean_object* v_fvars_3382_, lean_object* v_ty_3383_, lean_object* v___y_3384_, lean_object* v___y_3385_, lean_object* v___y_3386_, lean_object* v___y_3387_, lean_object* v___y_3388_){
_start:
{
lean_object* v_res_3389_; 
v_res_3389_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___lam__0(v_name_3377_, v_univs_3378_, v_numParams_3379_, v_ctors_3380_, v___x_3381_, v_fvars_3382_, v_ty_3383_, v___y_3384_, v___y_3385_, v___y_3386_, v___y_3387_);
lean_dec(v___y_3387_);
lean_dec_ref(v___y_3386_);
lean_dec(v___y_3385_);
lean_dec_ref(v___y_3384_);
lean_dec_ref(v_ty_3383_);
return v_res_3389_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__2(lean_object* v_a_3390_, lean_object* v_a_3391_){
_start:
{
if (lean_obj_tag(v_a_3390_) == 0)
{
lean_object* v___x_3392_; 
v___x_3392_ = l_List_reverse___redArg(v_a_3391_);
return v___x_3392_;
}
else
{
lean_object* v_head_3393_; lean_object* v_tail_3394_; lean_object* v___x_3396_; uint8_t v_isShared_3397_; uint8_t v_isSharedCheck_3403_; 
v_head_3393_ = lean_ctor_get(v_a_3390_, 0);
v_tail_3394_ = lean_ctor_get(v_a_3390_, 1);
v_isSharedCheck_3403_ = !lean_is_exclusive(v_a_3390_);
if (v_isSharedCheck_3403_ == 0)
{
v___x_3396_ = v_a_3390_;
v_isShared_3397_ = v_isSharedCheck_3403_;
goto v_resetjp_3395_;
}
else
{
lean_inc(v_tail_3394_);
lean_inc(v_head_3393_);
lean_dec(v_a_3390_);
v___x_3396_ = lean_box(0);
v_isShared_3397_ = v_isSharedCheck_3403_;
goto v_resetjp_3395_;
}
v_resetjp_3395_:
{
lean_object* v___x_3398_; lean_object* v___x_3400_; 
v___x_3398_ = l_Lean_Expr_fvar___override(v_head_3393_);
if (v_isShared_3397_ == 0)
{
lean_ctor_set(v___x_3396_, 1, v_a_3391_);
lean_ctor_set(v___x_3396_, 0, v___x_3398_);
v___x_3400_ = v___x_3396_;
goto v_reusejp_3399_;
}
else
{
lean_object* v_reuseFailAlloc_3402_; 
v_reuseFailAlloc_3402_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3402_, 0, v___x_3398_);
lean_ctor_set(v_reuseFailAlloc_3402_, 1, v_a_3391_);
v___x_3400_ = v_reuseFailAlloc_3402_;
goto v_reusejp_3399_;
}
v_reusejp_3399_:
{
v_a_3390_ = v_tail_3394_;
v_a_3391_ = v___x_3400_;
goto _start;
}
}
}
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__6___closed__0(void){
_start:
{
lean_object* v___x_3404_; double v___x_3405_; 
v___x_3404_ = lean_unsigned_to_nat(0u);
v___x_3405_ = lean_float_of_nat(v___x_3404_);
return v___x_3405_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__6(lean_object* v_cls_3409_, lean_object* v_msg_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_, lean_object* v___y_3413_, lean_object* v___y_3414_){
_start:
{
lean_object* v_ref_3416_; lean_object* v___x_3417_; lean_object* v_a_3418_; lean_object* v___x_3420_; uint8_t v_isShared_3421_; uint8_t v_isSharedCheck_3462_; 
v_ref_3416_ = lean_ctor_get(v___y_3413_, 5);
v___x_3417_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0_spec__0(v_msg_3410_, v___y_3411_, v___y_3412_, v___y_3413_, v___y_3414_);
v_a_3418_ = lean_ctor_get(v___x_3417_, 0);
v_isSharedCheck_3462_ = !lean_is_exclusive(v___x_3417_);
if (v_isSharedCheck_3462_ == 0)
{
v___x_3420_ = v___x_3417_;
v_isShared_3421_ = v_isSharedCheck_3462_;
goto v_resetjp_3419_;
}
else
{
lean_inc(v_a_3418_);
lean_dec(v___x_3417_);
v___x_3420_ = lean_box(0);
v_isShared_3421_ = v_isSharedCheck_3462_;
goto v_resetjp_3419_;
}
v_resetjp_3419_:
{
lean_object* v___x_3422_; lean_object* v_traceState_3423_; lean_object* v_env_3424_; lean_object* v_nextMacroScope_3425_; lean_object* v_ngen_3426_; lean_object* v_auxDeclNGen_3427_; lean_object* v_cache_3428_; lean_object* v_messages_3429_; lean_object* v_infoState_3430_; lean_object* v_snapshotTasks_3431_; lean_object* v___x_3433_; uint8_t v_isShared_3434_; uint8_t v_isSharedCheck_3461_; 
v___x_3422_ = lean_st_ref_take(v___y_3414_);
v_traceState_3423_ = lean_ctor_get(v___x_3422_, 4);
v_env_3424_ = lean_ctor_get(v___x_3422_, 0);
v_nextMacroScope_3425_ = lean_ctor_get(v___x_3422_, 1);
v_ngen_3426_ = lean_ctor_get(v___x_3422_, 2);
v_auxDeclNGen_3427_ = lean_ctor_get(v___x_3422_, 3);
v_cache_3428_ = lean_ctor_get(v___x_3422_, 5);
v_messages_3429_ = lean_ctor_get(v___x_3422_, 6);
v_infoState_3430_ = lean_ctor_get(v___x_3422_, 7);
v_snapshotTasks_3431_ = lean_ctor_get(v___x_3422_, 8);
v_isSharedCheck_3461_ = !lean_is_exclusive(v___x_3422_);
if (v_isSharedCheck_3461_ == 0)
{
v___x_3433_ = v___x_3422_;
v_isShared_3434_ = v_isSharedCheck_3461_;
goto v_resetjp_3432_;
}
else
{
lean_inc(v_snapshotTasks_3431_);
lean_inc(v_infoState_3430_);
lean_inc(v_messages_3429_);
lean_inc(v_cache_3428_);
lean_inc(v_traceState_3423_);
lean_inc(v_auxDeclNGen_3427_);
lean_inc(v_ngen_3426_);
lean_inc(v_nextMacroScope_3425_);
lean_inc(v_env_3424_);
lean_dec(v___x_3422_);
v___x_3433_ = lean_box(0);
v_isShared_3434_ = v_isSharedCheck_3461_;
goto v_resetjp_3432_;
}
v_resetjp_3432_:
{
uint64_t v_tid_3435_; lean_object* v_traces_3436_; lean_object* v___x_3438_; uint8_t v_isShared_3439_; uint8_t v_isSharedCheck_3460_; 
v_tid_3435_ = lean_ctor_get_uint64(v_traceState_3423_, sizeof(void*)*1);
v_traces_3436_ = lean_ctor_get(v_traceState_3423_, 0);
v_isSharedCheck_3460_ = !lean_is_exclusive(v_traceState_3423_);
if (v_isSharedCheck_3460_ == 0)
{
v___x_3438_ = v_traceState_3423_;
v_isShared_3439_ = v_isSharedCheck_3460_;
goto v_resetjp_3437_;
}
else
{
lean_inc(v_traces_3436_);
lean_dec(v_traceState_3423_);
v___x_3438_ = lean_box(0);
v_isShared_3439_ = v_isSharedCheck_3460_;
goto v_resetjp_3437_;
}
v_resetjp_3437_:
{
lean_object* v___x_3440_; double v___x_3441_; uint8_t v___x_3442_; lean_object* v___x_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; lean_object* v___x_3447_; lean_object* v___x_3448_; lean_object* v___x_3450_; 
v___x_3440_ = lean_box(0);
v___x_3441_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__6___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__6___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__6___closed__0);
v___x_3442_ = 0;
v___x_3443_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__6___closed__1));
v___x_3444_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3444_, 0, v_cls_3409_);
lean_ctor_set(v___x_3444_, 1, v___x_3440_);
lean_ctor_set(v___x_3444_, 2, v___x_3443_);
lean_ctor_set_float(v___x_3444_, sizeof(void*)*3, v___x_3441_);
lean_ctor_set_float(v___x_3444_, sizeof(void*)*3 + 8, v___x_3441_);
lean_ctor_set_uint8(v___x_3444_, sizeof(void*)*3 + 16, v___x_3442_);
v___x_3445_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__6___closed__2));
v___x_3446_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3446_, 0, v___x_3444_);
lean_ctor_set(v___x_3446_, 1, v_a_3418_);
lean_ctor_set(v___x_3446_, 2, v___x_3445_);
lean_inc(v_ref_3416_);
v___x_3447_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3447_, 0, v_ref_3416_);
lean_ctor_set(v___x_3447_, 1, v___x_3446_);
v___x_3448_ = l_Lean_PersistentArray_push___redArg(v_traces_3436_, v___x_3447_);
if (v_isShared_3439_ == 0)
{
lean_ctor_set(v___x_3438_, 0, v___x_3448_);
v___x_3450_ = v___x_3438_;
goto v_reusejp_3449_;
}
else
{
lean_object* v_reuseFailAlloc_3459_; 
v_reuseFailAlloc_3459_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3459_, 0, v___x_3448_);
lean_ctor_set_uint64(v_reuseFailAlloc_3459_, sizeof(void*)*1, v_tid_3435_);
v___x_3450_ = v_reuseFailAlloc_3459_;
goto v_reusejp_3449_;
}
v_reusejp_3449_:
{
lean_object* v___x_3452_; 
if (v_isShared_3434_ == 0)
{
lean_ctor_set(v___x_3433_, 4, v___x_3450_);
v___x_3452_ = v___x_3433_;
goto v_reusejp_3451_;
}
else
{
lean_object* v_reuseFailAlloc_3458_; 
v_reuseFailAlloc_3458_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3458_, 0, v_env_3424_);
lean_ctor_set(v_reuseFailAlloc_3458_, 1, v_nextMacroScope_3425_);
lean_ctor_set(v_reuseFailAlloc_3458_, 2, v_ngen_3426_);
lean_ctor_set(v_reuseFailAlloc_3458_, 3, v_auxDeclNGen_3427_);
lean_ctor_set(v_reuseFailAlloc_3458_, 4, v___x_3450_);
lean_ctor_set(v_reuseFailAlloc_3458_, 5, v_cache_3428_);
lean_ctor_set(v_reuseFailAlloc_3458_, 6, v_messages_3429_);
lean_ctor_set(v_reuseFailAlloc_3458_, 7, v_infoState_3430_);
lean_ctor_set(v_reuseFailAlloc_3458_, 8, v_snapshotTasks_3431_);
v___x_3452_ = v_reuseFailAlloc_3458_;
goto v_reusejp_3451_;
}
v_reusejp_3451_:
{
lean_object* v___x_3453_; lean_object* v___x_3454_; lean_object* v___x_3456_; 
v___x_3453_ = lean_st_ref_set(v___y_3414_, v___x_3452_);
v___x_3454_ = lean_box(0);
if (v_isShared_3421_ == 0)
{
lean_ctor_set(v___x_3420_, 0, v___x_3454_);
v___x_3456_ = v___x_3420_;
goto v_reusejp_3455_;
}
else
{
lean_object* v_reuseFailAlloc_3457_; 
v_reuseFailAlloc_3457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3457_, 0, v___x_3454_);
v___x_3456_ = v_reuseFailAlloc_3457_;
goto v_reusejp_3455_;
}
v_reusejp_3455_:
{
return v___x_3456_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__6___boxed(lean_object* v_cls_3463_, lean_object* v_msg_3464_, lean_object* v___y_3465_, lean_object* v___y_3466_, lean_object* v___y_3467_, lean_object* v___y_3468_, lean_object* v___y_3469_){
_start:
{
lean_object* v_res_3470_; 
v_res_3470_ = l_Lean_addTrace___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__6(v_cls_3463_, v_msg_3464_, v___y_3465_, v___y_3466_, v___y_3467_, v___y_3468_);
lean_dec(v___y_3468_);
lean_dec_ref(v___y_3467_);
lean_dec(v___y_3466_);
lean_dec_ref(v___y_3465_);
return v_res_3470_;
}
}
static lean_object* _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__1(void){
_start:
{
lean_object* v___x_3472_; lean_object* v___x_3473_; 
v___x_3472_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__0));
v___x_3473_ = l_Lean_stringToMessageData(v___x_3472_);
return v___x_3473_;
}
}
static lean_object* _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__4(void){
_start:
{
lean_object* v___x_3478_; lean_object* v___x_3479_; lean_object* v___x_3480_; 
v___x_3478_ = lean_box(0);
v___x_3479_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__3));
v___x_3480_ = l_Lean_mkConst(v___x_3479_, v___x_3478_);
return v___x_3480_;
}
}
static lean_object* _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__13(void){
_start:
{
lean_object* v___x_3496_; lean_object* v___x_3497_; lean_object* v___x_3498_; 
v___x_3496_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__10));
v___x_3497_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__12));
v___x_3498_ = l_Lean_Name_append(v___x_3497_, v___x_3496_);
return v___x_3498_;
}
}
static lean_object* _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__15(void){
_start:
{
lean_object* v___x_3500_; lean_object* v___x_3501_; 
v___x_3500_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__14));
v___x_3501_ = l_Lean_stringToMessageData(v___x_3500_);
return v___x_3501_;
}
}
static lean_object* _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__17(void){
_start:
{
lean_object* v___x_3503_; lean_object* v___x_3504_; 
v___x_3503_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__16));
v___x_3504_ = l_Lean_stringToMessageData(v___x_3503_);
return v___x_3504_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl(lean_object* v_inductVal_3505_, lean_object* v_rel_3506_, lean_object* v_a_3507_, lean_object* v_a_3508_, lean_object* v_a_3509_, lean_object* v_a_3510_){
_start:
{
lean_object* v___y_3513_; lean_object* v___y_3514_; lean_object* v___y_3515_; lean_object* v___y_3516_; lean_object* v_toConstantVal_3519_; lean_object* v_numParams_3520_; lean_object* v_ctors_3521_; lean_object* v_name_3522_; lean_object* v_levelParams_3523_; lean_object* v_type_3524_; lean_object* v___x_3526_; uint8_t v_isShared_3527_; uint8_t v_isSharedCheck_3687_; 
v_toConstantVal_3519_ = lean_ctor_get(v_inductVal_3505_, 0);
lean_inc_ref(v_toConstantVal_3519_);
v_numParams_3520_ = lean_ctor_get(v_inductVal_3505_, 1);
lean_inc(v_numParams_3520_);
v_ctors_3521_ = lean_ctor_get(v_inductVal_3505_, 4);
lean_inc(v_ctors_3521_);
lean_dec_ref(v_inductVal_3505_);
v_name_3522_ = lean_ctor_get(v_toConstantVal_3519_, 0);
v_levelParams_3523_ = lean_ctor_get(v_toConstantVal_3519_, 1);
v_type_3524_ = lean_ctor_get(v_toConstantVal_3519_, 2);
v_isSharedCheck_3687_ = !lean_is_exclusive(v_toConstantVal_3519_);
if (v_isSharedCheck_3687_ == 0)
{
v___x_3526_ = v_toConstantVal_3519_;
v_isShared_3527_ = v_isSharedCheck_3687_;
goto v_resetjp_3525_;
}
else
{
lean_inc(v_type_3524_);
lean_inc(v_levelParams_3523_);
lean_inc(v_name_3522_);
lean_dec(v_toConstantVal_3519_);
v___x_3526_ = lean_box(0);
v_isShared_3527_ = v_isSharedCheck_3687_;
goto v_resetjp_3525_;
}
v___jp_3512_:
{
lean_object* v___x_3517_; lean_object* v___x_3518_; 
v___x_3517_ = lean_obj_once(&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__1, &l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__1_once, _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__1);
v___x_3518_ = l_Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0___redArg(v___x_3517_, v___y_3513_, v___y_3514_, v___y_3515_, v___y_3516_);
return v___x_3518_;
}
v_resetjp_3525_:
{
lean_object* v___x_3528_; lean_object* v_univs_3529_; lean_object* v___f_3530_; uint8_t v___x_3531_; lean_object* v___x_3532_; 
v___x_3528_ = lean_box(0);
lean_inc(v_levelParams_3523_);
v_univs_3529_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__2_spec__3(v_levelParams_3523_, v___x_3528_);
lean_inc(v_ctors_3521_);
lean_inc(v_numParams_3520_);
lean_inc(v_name_3522_);
v___f_3530_ = lean_alloc_closure((void*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___lam__0___boxed), 12, 5);
lean_closure_set(v___f_3530_, 0, v_name_3522_);
lean_closure_set(v___f_3530_, 1, v_univs_3529_);
lean_closure_set(v___f_3530_, 2, v_numParams_3520_);
lean_closure_set(v___f_3530_, 3, v_ctors_3521_);
lean_closure_set(v___f_3530_, 4, v___x_3528_);
v___x_3531_ = 0;
v___x_3532_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__1___redArg(v_type_3524_, v___f_3530_, v___x_3531_, v___x_3531_, v_a_3507_, v_a_3508_, v_a_3509_, v_a_3510_);
if (lean_obj_tag(v___x_3532_) == 0)
{
lean_object* v_a_3533_; lean_object* v_snd_3534_; lean_object* v_fst_3535_; lean_object* v___x_3537_; uint8_t v_isShared_3538_; uint8_t v_isSharedCheck_3678_; 
v_a_3533_ = lean_ctor_get(v___x_3532_, 0);
lean_inc(v_a_3533_);
lean_dec_ref(v___x_3532_);
v_snd_3534_ = lean_ctor_get(v_a_3533_, 1);
v_fst_3535_ = lean_ctor_get(v_a_3533_, 0);
v_isSharedCheck_3678_ = !lean_is_exclusive(v_a_3533_);
if (v_isSharedCheck_3678_ == 0)
{
v___x_3537_ = v_a_3533_;
v_isShared_3538_ = v_isSharedCheck_3678_;
goto v_resetjp_3536_;
}
else
{
lean_inc(v_snd_3534_);
lean_inc(v_fst_3535_);
lean_dec(v_a_3533_);
v___x_3537_ = lean_box(0);
v_isShared_3538_ = v_isSharedCheck_3678_;
goto v_resetjp_3536_;
}
v_resetjp_3536_:
{
lean_object* v_fst_3539_; lean_object* v_snd_3540_; lean_object* v___x_3542_; uint8_t v_isShared_3543_; uint8_t v_isSharedCheck_3677_; 
v_fst_3539_ = lean_ctor_get(v_snd_3534_, 0);
v_snd_3540_ = lean_ctor_get(v_snd_3534_, 1);
v_isSharedCheck_3677_ = !lean_is_exclusive(v_snd_3534_);
if (v_isSharedCheck_3677_ == 0)
{
v___x_3542_ = v_snd_3534_;
v_isShared_3543_ = v_isSharedCheck_3677_;
goto v_resetjp_3541_;
}
else
{
lean_inc(v_snd_3540_);
lean_inc(v_fst_3539_);
lean_dec(v_snd_3534_);
v___x_3542_ = lean_box(0);
v_isShared_3543_ = v_isSharedCheck_3677_;
goto v_resetjp_3541_;
}
v_resetjp_3541_:
{
lean_object* v___y_3545_; lean_object* v___y_3546_; lean_object* v___y_3547_; lean_object* v___y_3548_; lean_object* v_options_3650_; uint8_t v_hasTrace_3651_; 
v_options_3650_ = lean_ctor_get(v_a_3509_, 2);
v_hasTrace_3651_ = lean_ctor_get_uint8(v_options_3650_, sizeof(void*)*1);
if (v_hasTrace_3651_ == 0)
{
lean_del_object(v___x_3542_);
lean_del_object(v___x_3537_);
v___y_3545_ = v_a_3507_;
v___y_3546_ = v_a_3508_;
v___y_3547_ = v_a_3509_;
v___y_3548_ = v_a_3510_;
goto v___jp_3544_;
}
else
{
lean_object* v_inheritedTraceOptions_3652_; lean_object* v___x_3653_; lean_object* v___y_3655_; lean_object* v___y_3656_; lean_object* v___y_3657_; lean_object* v_options_3658_; lean_object* v_inheritedTraceOptions_3659_; lean_object* v___y_3660_; lean_object* v___x_3669_; uint8_t v___x_3670_; 
v_inheritedTraceOptions_3652_ = lean_ctor_get(v_a_3509_, 13);
v___x_3653_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__10));
v___x_3669_ = lean_obj_once(&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__13, &l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__13_once, _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__13);
v___x_3670_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3652_, v_options_3650_, v___x_3669_);
if (v___x_3670_ == 0)
{
lean_del_object(v___x_3537_);
v___y_3655_ = v_a_3507_;
v___y_3656_ = v_a_3508_;
v___y_3657_ = v_a_3509_;
v_options_3658_ = v_options_3650_;
v_inheritedTraceOptions_3659_ = v_inheritedTraceOptions_3652_;
v___y_3660_ = v_a_3510_;
goto v___jp_3654_;
}
else
{
lean_object* v___x_3671_; lean_object* v___x_3672_; lean_object* v___x_3674_; 
v___x_3671_ = lean_obj_once(&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__17, &l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__17_once, _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__17);
lean_inc(v_snd_3540_);
v___x_3672_ = l_Lean_MessageData_ofExpr(v_snd_3540_);
if (v_isShared_3538_ == 0)
{
lean_ctor_set_tag(v___x_3537_, 7);
lean_ctor_set(v___x_3537_, 1, v___x_3672_);
lean_ctor_set(v___x_3537_, 0, v___x_3671_);
v___x_3674_ = v___x_3537_;
goto v_reusejp_3673_;
}
else
{
lean_object* v_reuseFailAlloc_3676_; 
v_reuseFailAlloc_3676_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3676_, 0, v___x_3671_);
lean_ctor_set(v_reuseFailAlloc_3676_, 1, v___x_3672_);
v___x_3674_ = v_reuseFailAlloc_3676_;
goto v_reusejp_3673_;
}
v_reusejp_3673_:
{
lean_object* v___x_3675_; 
v___x_3675_ = l_Lean_addTrace___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__6(v___x_3653_, v___x_3674_, v_a_3507_, v_a_3508_, v_a_3509_, v_a_3510_);
if (lean_obj_tag(v___x_3675_) == 0)
{
lean_dec_ref(v___x_3675_);
v___y_3655_ = v_a_3507_;
v___y_3656_ = v_a_3508_;
v___y_3657_ = v_a_3509_;
v_options_3658_ = v_options_3650_;
v_inheritedTraceOptions_3659_ = v_inheritedTraceOptions_3652_;
v___y_3660_ = v_a_3510_;
goto v___jp_3654_;
}
else
{
lean_del_object(v___x_3542_);
lean_dec(v_snd_3540_);
lean_dec(v_fst_3539_);
lean_dec(v_fst_3535_);
lean_del_object(v___x_3526_);
lean_dec(v_levelParams_3523_);
lean_dec(v_name_3522_);
lean_dec(v_ctors_3521_);
lean_dec(v_numParams_3520_);
lean_dec(v_rel_3506_);
return v___x_3675_;
}
}
}
v___jp_3654_:
{
lean_object* v___x_3661_; uint8_t v___x_3662_; 
v___x_3661_ = lean_obj_once(&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__13, &l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__13_once, _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__13);
v___x_3662_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3659_, v_options_3658_, v___x_3661_);
if (v___x_3662_ == 0)
{
lean_del_object(v___x_3542_);
v___y_3545_ = v___y_3655_;
v___y_3546_ = v___y_3656_;
v___y_3547_ = v___y_3657_;
v___y_3548_ = v___y_3660_;
goto v___jp_3544_;
}
else
{
lean_object* v___x_3663_; lean_object* v___x_3664_; lean_object* v___x_3666_; 
v___x_3663_ = lean_obj_once(&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__15, &l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__15_once, _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__15);
lean_inc(v_fst_3535_);
v___x_3664_ = l_Lean_MessageData_ofExpr(v_fst_3535_);
if (v_isShared_3543_ == 0)
{
lean_ctor_set_tag(v___x_3542_, 7);
lean_ctor_set(v___x_3542_, 1, v___x_3664_);
lean_ctor_set(v___x_3542_, 0, v___x_3663_);
v___x_3666_ = v___x_3542_;
goto v_reusejp_3665_;
}
else
{
lean_object* v_reuseFailAlloc_3668_; 
v_reuseFailAlloc_3668_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3668_, 0, v___x_3663_);
lean_ctor_set(v_reuseFailAlloc_3668_, 1, v___x_3664_);
v___x_3666_ = v_reuseFailAlloc_3668_;
goto v_reusejp_3665_;
}
v_reusejp_3665_:
{
lean_object* v___x_3667_; 
v___x_3667_ = l_Lean_addTrace___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__6(v___x_3653_, v___x_3666_, v___y_3655_, v___y_3656_, v___y_3657_, v___y_3660_);
if (lean_obj_tag(v___x_3667_) == 0)
{
lean_dec_ref(v___x_3667_);
v___y_3545_ = v___y_3655_;
v___y_3546_ = v___y_3656_;
v___y_3547_ = v___y_3657_;
v___y_3548_ = v___y_3660_;
goto v___jp_3544_;
}
else
{
lean_dec(v_snd_3540_);
lean_dec(v_fst_3539_);
lean_dec(v_fst_3535_);
lean_del_object(v___x_3526_);
lean_dec(v_levelParams_3523_);
lean_dec(v_name_3522_);
lean_dec(v_ctors_3521_);
lean_dec(v_numParams_3520_);
lean_dec(v_rel_3506_);
return v___x_3667_;
}
}
}
}
}
v___jp_3544_:
{
lean_object* v___x_3549_; uint8_t v___x_3550_; lean_object* v___x_3551_; lean_object* v___x_3552_; 
lean_inc(v_fst_3535_);
v___x_3549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3549_, 0, v_fst_3535_);
v___x_3550_ = 0;
v___x_3551_ = lean_box(0);
v___x_3552_ = l_Lean_Meta_mkFreshExprMVar(v___x_3549_, v___x_3550_, v___x_3551_, v___y_3545_, v___y_3546_, v___y_3547_, v___y_3548_);
if (lean_obj_tag(v___x_3552_) == 0)
{
lean_object* v_a_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; 
v_a_3553_ = lean_ctor_get(v___x_3552_, 0);
lean_inc(v_a_3553_);
lean_dec_ref(v___x_3552_);
v___x_3554_ = l_Lean_Expr_mvarId_x21(v_a_3553_);
v___x_3555_ = l_Lean_MVarId_intros(v___x_3554_, v___y_3545_, v___y_3546_, v___y_3547_, v___y_3548_);
if (lean_obj_tag(v___x_3555_) == 0)
{
lean_object* v_a_3556_; lean_object* v_fst_3557_; lean_object* v_snd_3558_; lean_object* v___x_3559_; lean_object* v___x_3560_; lean_object* v___x_3561_; lean_object* v___x_3562_; 
v_a_3556_ = lean_ctor_get(v___x_3555_, 0);
lean_inc(v_a_3556_);
lean_dec_ref(v___x_3555_);
v_fst_3557_ = lean_ctor_get(v_a_3556_, 0);
lean_inc(v_fst_3557_);
v_snd_3558_ = lean_ctor_get(v_a_3556_, 1);
lean_inc(v_snd_3558_);
lean_dec(v_a_3556_);
v___x_3559_ = lean_obj_once(&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__4, &l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__4_once, _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__4);
v___x_3560_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__5));
v___x_3561_ = lean_box(0);
v___x_3562_ = l_Lean_MVarId_apply(v_snd_3558_, v___x_3559_, v___x_3560_, v___x_3561_, v___y_3545_, v___y_3546_, v___y_3547_, v___y_3548_);
if (lean_obj_tag(v___x_3562_) == 0)
{
lean_object* v_a_3563_; 
v_a_3563_ = lean_ctor_get(v___x_3562_, 0);
lean_inc(v_a_3563_);
lean_dec_ref(v___x_3562_);
if (lean_obj_tag(v_a_3563_) == 1)
{
lean_object* v_tail_3564_; 
v_tail_3564_ = lean_ctor_get(v_a_3563_, 1);
lean_inc(v_tail_3564_);
if (lean_obj_tag(v_tail_3564_) == 1)
{
lean_object* v_tail_3565_; 
v_tail_3565_ = lean_ctor_get(v_tail_3564_, 1);
if (lean_obj_tag(v_tail_3565_) == 0)
{
lean_object* v_head_3566_; lean_object* v_head_3567_; lean_object* v___x_3569_; uint8_t v_isShared_3570_; uint8_t v_isSharedCheck_3624_; 
v_head_3566_ = lean_ctor_get(v_a_3563_, 0);
lean_inc(v_head_3566_);
lean_dec_ref(v_a_3563_);
v_head_3567_ = lean_ctor_get(v_tail_3564_, 0);
v_isSharedCheck_3624_ = !lean_is_exclusive(v_tail_3564_);
if (v_isSharedCheck_3624_ == 0)
{
lean_object* v_unused_3625_; 
v_unused_3625_ = lean_ctor_get(v_tail_3564_, 1);
lean_dec(v_unused_3625_);
v___x_3569_ = v_tail_3564_;
v_isShared_3570_ = v_isSharedCheck_3624_;
goto v_resetjp_3568_;
}
else
{
lean_inc(v_head_3567_);
lean_dec(v_tail_3564_);
v___x_3569_ = lean_box(0);
v_isShared_3570_ = v_isSharedCheck_3624_;
goto v_resetjp_3568_;
}
v_resetjp_3568_:
{
lean_object* v___x_3571_; 
lean_inc(v_fst_3539_);
v___x_3571_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toCases(v_head_3566_, v_fst_3539_, v___y_3545_, v___y_3546_, v___y_3547_, v___y_3548_);
if (lean_obj_tag(v___x_3571_) == 0)
{
lean_object* v___x_3572_; 
lean_dec_ref(v___x_3571_);
v___x_3572_ = l_Lean_Meta_intro1Core(v_head_3567_, v___x_3531_, v___y_3545_, v___y_3546_, v___y_3547_, v___y_3548_);
if (lean_obj_tag(v___x_3572_) == 0)
{
lean_object* v_a_3573_; lean_object* v_fst_3574_; lean_object* v_snd_3575_; lean_object* v___x_3576_; lean_object* v___x_3577_; lean_object* v___x_3578_; lean_object* v___x_3579_; lean_object* v___x_3580_; 
v_a_3573_ = lean_ctor_get(v___x_3572_, 0);
lean_inc(v_a_3573_);
lean_dec_ref(v___x_3572_);
v_fst_3574_ = lean_ctor_get(v_a_3573_, 0);
lean_inc(v_fst_3574_);
v_snd_3575_ = lean_ctor_get(v_a_3573_, 1);
lean_inc(v_snd_3575_);
lean_dec(v_a_3573_);
v___x_3576_ = lean_array_to_list(v_fst_3557_);
v___x_3577_ = ((lean_object*)(l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__5___lam__0___closed__0));
lean_inc(v___x_3576_);
v___x_3578_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), v___x_3576_, v___x_3576_, v_numParams_3520_, v___x_3577_);
lean_dec(v___x_3576_);
v___x_3579_ = l_List_mapTR_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__2(v___x_3578_, v___x_3528_);
v___x_3580_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive(v_snd_3575_, v_ctors_3521_, v___x_3579_, v_fst_3539_, v_fst_3574_, v___y_3545_, v___y_3546_, v___y_3547_, v___y_3548_);
if (lean_obj_tag(v___x_3580_) == 0)
{
lean_object* v___x_3581_; lean_object* v_a_3582_; lean_object* v___x_3584_; 
lean_dec_ref(v___x_3580_);
v___x_3581_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__3___redArg(v_a_3553_, v___y_3546_);
v_a_3582_ = lean_ctor_get(v___x_3581_, 0);
lean_inc(v_a_3582_);
lean_dec_ref(v___x_3581_);
lean_inc(v_levelParams_3523_);
lean_inc(v_rel_3506_);
if (v_isShared_3527_ == 0)
{
lean_ctor_set(v___x_3526_, 2, v_fst_3535_);
lean_ctor_set(v___x_3526_, 0, v_rel_3506_);
v___x_3584_ = v___x_3526_;
goto v_reusejp_3583_;
}
else
{
lean_object* v_reuseFailAlloc_3615_; 
v_reuseFailAlloc_3615_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3615_, 0, v_rel_3506_);
lean_ctor_set(v_reuseFailAlloc_3615_, 1, v_levelParams_3523_);
lean_ctor_set(v_reuseFailAlloc_3615_, 2, v_fst_3535_);
v___x_3584_ = v_reuseFailAlloc_3615_;
goto v_reusejp_3583_;
}
v_reusejp_3583_:
{
lean_object* v___x_3586_; 
if (v_isShared_3570_ == 0)
{
lean_ctor_set(v___x_3569_, 1, v___x_3528_);
lean_ctor_set(v___x_3569_, 0, v_rel_3506_);
v___x_3586_ = v___x_3569_;
goto v_reusejp_3585_;
}
else
{
lean_object* v_reuseFailAlloc_3614_; 
v_reuseFailAlloc_3614_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3614_, 0, v_rel_3506_);
lean_ctor_set(v_reuseFailAlloc_3614_, 1, v___x_3528_);
v___x_3586_ = v_reuseFailAlloc_3614_;
goto v_reusejp_3585_;
}
v_reusejp_3585_:
{
lean_object* v___x_3587_; lean_object* v___x_3588_; lean_object* v_a_3589_; lean_object* v___x_3590_; 
v___x_3587_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3587_, 0, v___x_3584_);
lean_ctor_set(v___x_3587_, 1, v_a_3582_);
lean_ctor_set(v___x_3587_, 2, v___x_3586_);
v___x_3588_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__4___redArg(v___x_3587_, v___y_3548_);
v_a_3589_ = lean_ctor_get(v___x_3588_, 0);
lean_inc(v_a_3589_);
lean_dec_ref(v___x_3588_);
v___x_3590_ = l_Lean_addDecl(v_a_3589_, v___x_3531_, v___y_3547_, v___y_3548_);
if (lean_obj_tag(v___x_3590_) == 0)
{
lean_object* v___x_3591_; 
lean_dec_ref(v___x_3590_);
lean_inc(v___y_3548_);
lean_inc_ref(v___y_3547_);
lean_inc(v___y_3546_);
lean_inc_ref(v___y_3545_);
lean_inc(v_snd_3540_);
v___x_3591_ = lean_infer_type(v_snd_3540_, v___y_3545_, v___y_3546_, v___y_3547_, v___y_3548_);
if (lean_obj_tag(v___x_3591_) == 0)
{
lean_object* v_a_3592_; lean_object* v___x_3593_; lean_object* v___x_3594_; lean_object* v___x_3595_; lean_object* v___x_3596_; lean_object* v_a_3597_; lean_object* v___x_3599_; uint8_t v_isShared_3600_; uint8_t v_isSharedCheck_3605_; 
v_a_3592_ = lean_ctor_get(v___x_3591_, 0);
lean_inc(v_a_3592_);
lean_dec_ref(v___x_3591_);
v___x_3593_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__7));
v___x_3594_ = l_Lean_Name_append(v_name_3522_, v___x_3593_);
v___x_3595_ = lean_box(0);
v___x_3596_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__5___redArg(v___x_3594_, v_levelParams_3523_, v_a_3592_, v_snd_3540_, v___x_3595_, v___y_3548_);
v_a_3597_ = lean_ctor_get(v___x_3596_, 0);
v_isSharedCheck_3605_ = !lean_is_exclusive(v___x_3596_);
if (v_isSharedCheck_3605_ == 0)
{
v___x_3599_ = v___x_3596_;
v_isShared_3600_ = v_isSharedCheck_3605_;
goto v_resetjp_3598_;
}
else
{
lean_inc(v_a_3597_);
lean_dec(v___x_3596_);
v___x_3599_ = lean_box(0);
v_isShared_3600_ = v_isSharedCheck_3605_;
goto v_resetjp_3598_;
}
v_resetjp_3598_:
{
lean_object* v___x_3602_; 
if (v_isShared_3600_ == 0)
{
lean_ctor_set_tag(v___x_3599_, 1);
v___x_3602_ = v___x_3599_;
goto v_reusejp_3601_;
}
else
{
lean_object* v_reuseFailAlloc_3604_; 
v_reuseFailAlloc_3604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3604_, 0, v_a_3597_);
v___x_3602_ = v_reuseFailAlloc_3604_;
goto v_reusejp_3601_;
}
v_reusejp_3601_:
{
lean_object* v___x_3603_; 
v___x_3603_ = l_Lean_addDecl(v___x_3602_, v___x_3531_, v___y_3547_, v___y_3548_);
return v___x_3603_;
}
}
}
else
{
lean_object* v_a_3606_; lean_object* v___x_3608_; uint8_t v_isShared_3609_; uint8_t v_isSharedCheck_3613_; 
lean_dec(v_snd_3540_);
lean_dec(v_levelParams_3523_);
lean_dec(v_name_3522_);
v_a_3606_ = lean_ctor_get(v___x_3591_, 0);
v_isSharedCheck_3613_ = !lean_is_exclusive(v___x_3591_);
if (v_isSharedCheck_3613_ == 0)
{
v___x_3608_ = v___x_3591_;
v_isShared_3609_ = v_isSharedCheck_3613_;
goto v_resetjp_3607_;
}
else
{
lean_inc(v_a_3606_);
lean_dec(v___x_3591_);
v___x_3608_ = lean_box(0);
v_isShared_3609_ = v_isSharedCheck_3613_;
goto v_resetjp_3607_;
}
v_resetjp_3607_:
{
lean_object* v___x_3611_; 
if (v_isShared_3609_ == 0)
{
v___x_3611_ = v___x_3608_;
goto v_reusejp_3610_;
}
else
{
lean_object* v_reuseFailAlloc_3612_; 
v_reuseFailAlloc_3612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3612_, 0, v_a_3606_);
v___x_3611_ = v_reuseFailAlloc_3612_;
goto v_reusejp_3610_;
}
v_reusejp_3610_:
{
return v___x_3611_;
}
}
}
}
else
{
lean_dec(v_snd_3540_);
lean_dec(v_levelParams_3523_);
lean_dec(v_name_3522_);
return v___x_3590_;
}
}
}
}
else
{
lean_del_object(v___x_3569_);
lean_dec(v_a_3553_);
lean_dec(v_snd_3540_);
lean_dec(v_fst_3535_);
lean_del_object(v___x_3526_);
lean_dec(v_levelParams_3523_);
lean_dec(v_name_3522_);
lean_dec(v_rel_3506_);
return v___x_3580_;
}
}
else
{
lean_object* v_a_3616_; lean_object* v___x_3618_; uint8_t v_isShared_3619_; uint8_t v_isSharedCheck_3623_; 
lean_del_object(v___x_3569_);
lean_dec(v_fst_3557_);
lean_dec(v_a_3553_);
lean_dec(v_snd_3540_);
lean_dec(v_fst_3539_);
lean_dec(v_fst_3535_);
lean_del_object(v___x_3526_);
lean_dec(v_levelParams_3523_);
lean_dec(v_name_3522_);
lean_dec(v_ctors_3521_);
lean_dec(v_numParams_3520_);
lean_dec(v_rel_3506_);
v_a_3616_ = lean_ctor_get(v___x_3572_, 0);
v_isSharedCheck_3623_ = !lean_is_exclusive(v___x_3572_);
if (v_isSharedCheck_3623_ == 0)
{
v___x_3618_ = v___x_3572_;
v_isShared_3619_ = v_isSharedCheck_3623_;
goto v_resetjp_3617_;
}
else
{
lean_inc(v_a_3616_);
lean_dec(v___x_3572_);
v___x_3618_ = lean_box(0);
v_isShared_3619_ = v_isSharedCheck_3623_;
goto v_resetjp_3617_;
}
v_resetjp_3617_:
{
lean_object* v___x_3621_; 
if (v_isShared_3619_ == 0)
{
v___x_3621_ = v___x_3618_;
goto v_reusejp_3620_;
}
else
{
lean_object* v_reuseFailAlloc_3622_; 
v_reuseFailAlloc_3622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3622_, 0, v_a_3616_);
v___x_3621_ = v_reuseFailAlloc_3622_;
goto v_reusejp_3620_;
}
v_reusejp_3620_:
{
return v___x_3621_;
}
}
}
}
else
{
lean_del_object(v___x_3569_);
lean_dec(v_head_3567_);
lean_dec(v_fst_3557_);
lean_dec(v_a_3553_);
lean_dec(v_snd_3540_);
lean_dec(v_fst_3539_);
lean_dec(v_fst_3535_);
lean_del_object(v___x_3526_);
lean_dec(v_levelParams_3523_);
lean_dec(v_name_3522_);
lean_dec(v_ctors_3521_);
lean_dec(v_numParams_3520_);
lean_dec(v_rel_3506_);
return v___x_3571_;
}
}
}
else
{
lean_dec_ref(v_tail_3564_);
lean_dec_ref(v_a_3563_);
lean_dec(v_fst_3557_);
lean_dec(v_a_3553_);
lean_dec(v_snd_3540_);
lean_dec(v_fst_3539_);
lean_dec(v_fst_3535_);
lean_del_object(v___x_3526_);
lean_dec(v_levelParams_3523_);
lean_dec(v_name_3522_);
lean_dec(v_ctors_3521_);
lean_dec(v_numParams_3520_);
lean_dec(v_rel_3506_);
v___y_3513_ = v___y_3545_;
v___y_3514_ = v___y_3546_;
v___y_3515_ = v___y_3547_;
v___y_3516_ = v___y_3548_;
goto v___jp_3512_;
}
}
else
{
lean_dec_ref(v_a_3563_);
lean_dec(v_tail_3564_);
lean_dec(v_fst_3557_);
lean_dec(v_a_3553_);
lean_dec(v_snd_3540_);
lean_dec(v_fst_3539_);
lean_dec(v_fst_3535_);
lean_del_object(v___x_3526_);
lean_dec(v_levelParams_3523_);
lean_dec(v_name_3522_);
lean_dec(v_ctors_3521_);
lean_dec(v_numParams_3520_);
lean_dec(v_rel_3506_);
v___y_3513_ = v___y_3545_;
v___y_3514_ = v___y_3546_;
v___y_3515_ = v___y_3547_;
v___y_3516_ = v___y_3548_;
goto v___jp_3512_;
}
}
else
{
lean_dec(v_a_3563_);
lean_dec(v_fst_3557_);
lean_dec(v_a_3553_);
lean_dec(v_snd_3540_);
lean_dec(v_fst_3539_);
lean_dec(v_fst_3535_);
lean_del_object(v___x_3526_);
lean_dec(v_levelParams_3523_);
lean_dec(v_name_3522_);
lean_dec(v_ctors_3521_);
lean_dec(v_numParams_3520_);
lean_dec(v_rel_3506_);
v___y_3513_ = v___y_3545_;
v___y_3514_ = v___y_3546_;
v___y_3515_ = v___y_3547_;
v___y_3516_ = v___y_3548_;
goto v___jp_3512_;
}
}
else
{
lean_object* v_a_3626_; lean_object* v___x_3628_; uint8_t v_isShared_3629_; uint8_t v_isSharedCheck_3633_; 
lean_dec(v_fst_3557_);
lean_dec(v_a_3553_);
lean_dec(v_snd_3540_);
lean_dec(v_fst_3539_);
lean_dec(v_fst_3535_);
lean_del_object(v___x_3526_);
lean_dec(v_levelParams_3523_);
lean_dec(v_name_3522_);
lean_dec(v_ctors_3521_);
lean_dec(v_numParams_3520_);
lean_dec(v_rel_3506_);
v_a_3626_ = lean_ctor_get(v___x_3562_, 0);
v_isSharedCheck_3633_ = !lean_is_exclusive(v___x_3562_);
if (v_isSharedCheck_3633_ == 0)
{
v___x_3628_ = v___x_3562_;
v_isShared_3629_ = v_isSharedCheck_3633_;
goto v_resetjp_3627_;
}
else
{
lean_inc(v_a_3626_);
lean_dec(v___x_3562_);
v___x_3628_ = lean_box(0);
v_isShared_3629_ = v_isSharedCheck_3633_;
goto v_resetjp_3627_;
}
v_resetjp_3627_:
{
lean_object* v___x_3631_; 
if (v_isShared_3629_ == 0)
{
v___x_3631_ = v___x_3628_;
goto v_reusejp_3630_;
}
else
{
lean_object* v_reuseFailAlloc_3632_; 
v_reuseFailAlloc_3632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3632_, 0, v_a_3626_);
v___x_3631_ = v_reuseFailAlloc_3632_;
goto v_reusejp_3630_;
}
v_reusejp_3630_:
{
return v___x_3631_;
}
}
}
}
else
{
lean_object* v_a_3634_; lean_object* v___x_3636_; uint8_t v_isShared_3637_; uint8_t v_isSharedCheck_3641_; 
lean_dec(v_a_3553_);
lean_dec(v_snd_3540_);
lean_dec(v_fst_3539_);
lean_dec(v_fst_3535_);
lean_del_object(v___x_3526_);
lean_dec(v_levelParams_3523_);
lean_dec(v_name_3522_);
lean_dec(v_ctors_3521_);
lean_dec(v_numParams_3520_);
lean_dec(v_rel_3506_);
v_a_3634_ = lean_ctor_get(v___x_3555_, 0);
v_isSharedCheck_3641_ = !lean_is_exclusive(v___x_3555_);
if (v_isSharedCheck_3641_ == 0)
{
v___x_3636_ = v___x_3555_;
v_isShared_3637_ = v_isSharedCheck_3641_;
goto v_resetjp_3635_;
}
else
{
lean_inc(v_a_3634_);
lean_dec(v___x_3555_);
v___x_3636_ = lean_box(0);
v_isShared_3637_ = v_isSharedCheck_3641_;
goto v_resetjp_3635_;
}
v_resetjp_3635_:
{
lean_object* v___x_3639_; 
if (v_isShared_3637_ == 0)
{
v___x_3639_ = v___x_3636_;
goto v_reusejp_3638_;
}
else
{
lean_object* v_reuseFailAlloc_3640_; 
v_reuseFailAlloc_3640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3640_, 0, v_a_3634_);
v___x_3639_ = v_reuseFailAlloc_3640_;
goto v_reusejp_3638_;
}
v_reusejp_3638_:
{
return v___x_3639_;
}
}
}
}
else
{
lean_object* v_a_3642_; lean_object* v___x_3644_; uint8_t v_isShared_3645_; uint8_t v_isSharedCheck_3649_; 
lean_dec(v_snd_3540_);
lean_dec(v_fst_3539_);
lean_dec(v_fst_3535_);
lean_del_object(v___x_3526_);
lean_dec(v_levelParams_3523_);
lean_dec(v_name_3522_);
lean_dec(v_ctors_3521_);
lean_dec(v_numParams_3520_);
lean_dec(v_rel_3506_);
v_a_3642_ = lean_ctor_get(v___x_3552_, 0);
v_isSharedCheck_3649_ = !lean_is_exclusive(v___x_3552_);
if (v_isSharedCheck_3649_ == 0)
{
v___x_3644_ = v___x_3552_;
v_isShared_3645_ = v_isSharedCheck_3649_;
goto v_resetjp_3643_;
}
else
{
lean_inc(v_a_3642_);
lean_dec(v___x_3552_);
v___x_3644_ = lean_box(0);
v_isShared_3645_ = v_isSharedCheck_3649_;
goto v_resetjp_3643_;
}
v_resetjp_3643_:
{
lean_object* v___x_3647_; 
if (v_isShared_3645_ == 0)
{
v___x_3647_ = v___x_3644_;
goto v_reusejp_3646_;
}
else
{
lean_object* v_reuseFailAlloc_3648_; 
v_reuseFailAlloc_3648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3648_, 0, v_a_3642_);
v___x_3647_ = v_reuseFailAlloc_3648_;
goto v_reusejp_3646_;
}
v_reusejp_3646_:
{
return v___x_3647_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3679_; lean_object* v___x_3681_; uint8_t v_isShared_3682_; uint8_t v_isSharedCheck_3686_; 
lean_del_object(v___x_3526_);
lean_dec(v_levelParams_3523_);
lean_dec(v_name_3522_);
lean_dec(v_ctors_3521_);
lean_dec(v_numParams_3520_);
lean_dec(v_rel_3506_);
v_a_3679_ = lean_ctor_get(v___x_3532_, 0);
v_isSharedCheck_3686_ = !lean_is_exclusive(v___x_3532_);
if (v_isSharedCheck_3686_ == 0)
{
v___x_3681_ = v___x_3532_;
v_isShared_3682_ = v_isSharedCheck_3686_;
goto v_resetjp_3680_;
}
else
{
lean_inc(v_a_3679_);
lean_dec(v___x_3532_);
v___x_3681_ = lean_box(0);
v_isShared_3682_ = v_isSharedCheck_3686_;
goto v_resetjp_3680_;
}
v_resetjp_3680_:
{
lean_object* v___x_3684_; 
if (v_isShared_3682_ == 0)
{
v___x_3684_ = v___x_3681_;
goto v_reusejp_3683_;
}
else
{
lean_object* v_reuseFailAlloc_3685_; 
v_reuseFailAlloc_3685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3685_, 0, v_a_3679_);
v___x_3684_ = v_reuseFailAlloc_3685_;
goto v_reusejp_3683_;
}
v_reusejp_3683_:
{
return v___x_3684_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___boxed(lean_object* v_inductVal_3688_, lean_object* v_rel_3689_, lean_object* v_a_3690_, lean_object* v_a_3691_, lean_object* v_a_3692_, lean_object* v_a_3693_, lean_object* v_a_3694_){
_start:
{
lean_object* v_res_3695_; 
v_res_3695_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl(v_inductVal_3688_, v_rel_3689_, v_a_3690_, v_a_3691_, v_a_3692_, v_a_3693_);
lean_dec(v_a_3693_);
lean_dec_ref(v_a_3692_);
lean_dec(v_a_3691_);
lean_dec_ref(v_a_3690_);
return v_res_3695_;
}
}
static lean_object* _init_l_Lean_Meta_mkSumOfProducts___closed__3(void){
_start:
{
lean_object* v___x_3700_; lean_object* v___x_3701_; 
v___x_3700_ = ((lean_object*)(l_Lean_Meta_mkSumOfProducts___closed__2));
v___x_3701_ = l_Lean_stringToMessageData(v___x_3700_);
return v___x_3701_;
}
}
static lean_object* _init_l_Lean_Meta_mkSumOfProducts___closed__5(void){
_start:
{
lean_object* v___x_3703_; lean_object* v___x_3704_; 
v___x_3703_ = ((lean_object*)(l_Lean_Meta_mkSumOfProducts___closed__4));
v___x_3704_ = l_Lean_stringToMessageData(v___x_3703_);
return v___x_3704_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSumOfProducts(lean_object* v_declName_3705_, lean_object* v_a_3706_, lean_object* v_a_3707_, lean_object* v_a_3708_, lean_object* v_a_3709_){
_start:
{
lean_object* v___y_3712_; lean_object* v___y_3713_; lean_object* v___y_3714_; lean_object* v___y_3715_; lean_object* v_options_3732_; uint8_t v_hasTrace_3733_; 
v_options_3732_ = lean_ctor_get(v_a_3708_, 2);
v_hasTrace_3733_ = lean_ctor_get_uint8(v_options_3732_, sizeof(void*)*1);
if (v_hasTrace_3733_ == 0)
{
v___y_3712_ = v_a_3706_;
v___y_3713_ = v_a_3707_;
v___y_3714_ = v_a_3708_;
v___y_3715_ = v_a_3709_;
goto v___jp_3711_;
}
else
{
lean_object* v_inheritedTraceOptions_3734_; lean_object* v_cls_3735_; lean_object* v___x_3736_; uint8_t v___x_3737_; 
v_inheritedTraceOptions_3734_ = lean_ctor_get(v_a_3708_, 13);
v_cls_3735_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__10));
v___x_3736_ = lean_obj_once(&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__13, &l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__13_once, _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__13);
v___x_3737_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3734_, v_options_3732_, v___x_3736_);
if (v___x_3737_ == 0)
{
v___y_3712_ = v_a_3706_;
v___y_3713_ = v_a_3707_;
v___y_3714_ = v_a_3708_;
v___y_3715_ = v_a_3709_;
goto v___jp_3711_;
}
else
{
lean_object* v___x_3738_; lean_object* v___x_3739_; lean_object* v___x_3740_; lean_object* v___x_3741_; 
v___x_3738_ = lean_obj_once(&l_Lean_Meta_mkSumOfProducts___closed__5, &l_Lean_Meta_mkSumOfProducts___closed__5_once, _init_l_Lean_Meta_mkSumOfProducts___closed__5);
lean_inc(v_declName_3705_);
v___x_3739_ = l_Lean_MessageData_ofName(v_declName_3705_);
v___x_3740_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3740_, 0, v___x_3738_);
lean_ctor_set(v___x_3740_, 1, v___x_3739_);
v___x_3741_ = l_Lean_addTrace___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__6(v_cls_3735_, v___x_3740_, v_a_3706_, v_a_3707_, v_a_3708_, v_a_3709_);
if (lean_obj_tag(v___x_3741_) == 0)
{
lean_dec_ref(v___x_3741_);
v___y_3712_ = v_a_3706_;
v___y_3713_ = v_a_3707_;
v___y_3714_ = v_a_3708_;
v___y_3715_ = v_a_3709_;
goto v___jp_3711_;
}
else
{
lean_dec(v_declName_3705_);
return v___x_3741_;
}
}
}
v___jp_3711_:
{
lean_object* v___x_3716_; 
lean_inc(v_declName_3705_);
v___x_3716_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0(v_declName_3705_, v___y_3712_, v___y_3713_, v___y_3714_, v___y_3715_);
if (lean_obj_tag(v___x_3716_) == 0)
{
lean_object* v_a_3717_; 
v_a_3717_ = lean_ctor_get(v___x_3716_, 0);
lean_inc(v_a_3717_);
lean_dec_ref(v___x_3716_);
if (lean_obj_tag(v_a_3717_) == 5)
{
lean_object* v_val_3718_; lean_object* v___x_3719_; lean_object* v___x_3720_; lean_object* v___x_3721_; 
v_val_3718_ = lean_ctor_get(v_a_3717_, 0);
lean_inc_ref(v_val_3718_);
lean_dec_ref(v_a_3717_);
v___x_3719_ = ((lean_object*)(l_Lean_Meta_mkSumOfProducts___closed__1));
v___x_3720_ = l_Lean_Name_append(v_declName_3705_, v___x_3719_);
v___x_3721_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl(v_val_3718_, v___x_3720_, v___y_3712_, v___y_3713_, v___y_3714_, v___y_3715_);
return v___x_3721_;
}
else
{
lean_object* v___x_3722_; lean_object* v___x_3723_; 
lean_dec(v_a_3717_);
lean_dec(v_declName_3705_);
v___x_3722_ = lean_obj_once(&l_Lean_Meta_mkSumOfProducts___closed__3, &l_Lean_Meta_mkSumOfProducts___closed__3_once, _init_l_Lean_Meta_mkSumOfProducts___closed__3);
v___x_3723_ = l_Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0___redArg(v___x_3722_, v___y_3712_, v___y_3713_, v___y_3714_, v___y_3715_);
return v___x_3723_;
}
}
else
{
lean_object* v_a_3724_; lean_object* v___x_3726_; uint8_t v_isShared_3727_; uint8_t v_isSharedCheck_3731_; 
lean_dec(v_declName_3705_);
v_a_3724_ = lean_ctor_get(v___x_3716_, 0);
v_isSharedCheck_3731_ = !lean_is_exclusive(v___x_3716_);
if (v_isSharedCheck_3731_ == 0)
{
v___x_3726_ = v___x_3716_;
v_isShared_3727_ = v_isSharedCheck_3731_;
goto v_resetjp_3725_;
}
else
{
lean_inc(v_a_3724_);
lean_dec(v___x_3716_);
v___x_3726_ = lean_box(0);
v_isShared_3727_ = v_isSharedCheck_3731_;
goto v_resetjp_3725_;
}
v_resetjp_3725_:
{
lean_object* v___x_3729_; 
if (v_isShared_3727_ == 0)
{
v___x_3729_ = v___x_3726_;
goto v_reusejp_3728_;
}
else
{
lean_object* v_reuseFailAlloc_3730_; 
v_reuseFailAlloc_3730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3730_, 0, v_a_3724_);
v___x_3729_ = v_reuseFailAlloc_3730_;
goto v_reusejp_3728_;
}
v_reusejp_3728_:
{
return v___x_3729_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSumOfProducts___boxed(lean_object* v_declName_3742_, lean_object* v_a_3743_, lean_object* v_a_3744_, lean_object* v_a_3745_, lean_object* v_a_3746_, lean_object* v_a_3747_){
_start:
{
lean_object* v_res_3748_; 
v_res_3748_ = l_Lean_Meta_mkSumOfProducts(v_declName_3742_, v_a_3743_, v_a_3744_, v_a_3745_, v_a_3746_);
lean_dec(v_a_3746_);
lean_dec_ref(v_a_3745_);
lean_dec(v_a_3744_);
lean_dec_ref(v_a_3743_);
return v_res_3748_;
}
}
static lean_object* _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3788_; lean_object* v___x_3789_; lean_object* v___x_3790_; 
v___x_3788_ = lean_unsigned_to_nat(3649998058u);
v___x_3789_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2_));
v___x_3790_ = l_Lean_Name_num___override(v___x_3789_, v___x_3788_);
return v___x_3790_;
}
}
static lean_object* _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3792_; lean_object* v___x_3793_; lean_object* v___x_3794_; 
v___x_3792_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2_));
v___x_3793_ = lean_obj_once(&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2_, &l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2_);
v___x_3794_ = l_Lean_Name_str___override(v___x_3793_, v___x_3792_);
return v___x_3794_;
}
}
static lean_object* _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3796_; lean_object* v___x_3797_; lean_object* v___x_3798_; 
v___x_3796_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2_));
v___x_3797_ = lean_obj_once(&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2_, &l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2_);
v___x_3798_ = l_Lean_Name_str___override(v___x_3797_, v___x_3796_);
return v___x_3798_;
}
}
static lean_object* _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3799_; lean_object* v___x_3800_; lean_object* v___x_3801_; 
v___x_3799_ = lean_unsigned_to_nat(2u);
v___x_3800_ = lean_obj_once(&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2_, &l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2_);
v___x_3801_ = l_Lean_Name_num___override(v___x_3800_, v___x_3799_);
return v___x_3801_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3803_; uint8_t v___x_3804_; lean_object* v___x_3805_; lean_object* v___x_3806_; 
v___x_3803_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__10));
v___x_3804_ = 0;
v___x_3805_ = lean_obj_once(&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2_, &l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2_);
v___x_3806_ = l_Lean_registerTraceClass(v___x_3803_, v___x_3804_, v___x_3805_);
return v___x_3806_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2____boxed(lean_object* v_a_3807_){
_start:
{
lean_object* v_res_3808_; 
v_res_3808_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2_();
return v_res_3808_;
}
}
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Apply(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Cases(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_MkIffOfInductiveProp(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
