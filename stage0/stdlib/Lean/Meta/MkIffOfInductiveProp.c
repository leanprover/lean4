// Lean compiler output
// Module: Lean.Meta.MkIffOfInductiveProp
// Imports: public import Lean.Meta.Basic import Lean.Elab.Tactic.Basic import Lean.Meta.Tactic.Apply import Lean.Meta.Tactic.Cases import Init.Data.List.Impl
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
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_MVarId_cases(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
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
lean_object* l_List_lengthTR___redArg(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_List_get___redArg(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
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
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
lean_object* l___private_Init_Data_List_Impl_0__List_zipWithTR_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_LocalContext_getFVarIds(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
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
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_getLast_x21___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_tryClear(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_revert(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_intro1Core(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_FVarId_getType___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sortLevel_x21(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_zipIdxTR___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_TermElabM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_List_drop___redArg(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_Expr_replaceFVar(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_Expr_occurs(lean_object*, lean_object*);
uint8_t lean_level_eq(lean_object*, lean_object*);
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
static const lean_ctor_object l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*8 + 16, .m_other = 8, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___closed__2_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___closed__4_value),LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 1, 0, 0, 0, 0),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___closed__5 = (const lean_object*)&l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___closed__5_value;
static const lean_ctor_object l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*8 + 0, .m_other = 8, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1))}};
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__1(lean_object*, lean_object*);
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
static lean_once_cell_t l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__2___closed__0;
static const lean_array_object l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__2___closed__1 = (const lean_object*)&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__2___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__2___closed__2 = (const lean_object*)&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__2___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__2___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_closure_object l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__1, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___closed__0 = (const lean_object*)&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___closed__0_value;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toCases___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toCases_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toCases_spec__1___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toCases_spec__1___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toCases_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toCases_spec__1___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toCases_spec__1___closed__0 = (const lean_object*)&l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toCases_spec__1___closed__0_value;
static const lean_array_object l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toCases_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toCases_spec__1___closed__1 = (const lean_object*)&l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toCases_spec__1___closed__1_value;
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toCases_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toCases_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toCases___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toCases___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toCases___closed__0 = (const lean_object*)&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toCases___closed__0_value;
static const lean_array_object l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toCases___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toCases___closed__1 = (const lean_object*)&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toCases___closed__1_value;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive___lam__1(lean_object*, lean_object*);
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
static const lean_closure_object l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive___closed__0 = (const lean_object*)&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive___closed__0_value;
static const lean_closure_object l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive___lam__1, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive___closed__1 = (const lean_object*)&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive___closed__1_value;
static const lean_array_object l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive___closed__2 = (const lean_object*)&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive___closed__2_value;
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
static const lean_array_object l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___lam__0___closed__0_value;
static const lean_string_object l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Iff"};
static const lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___lam__0___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(19, 54, 203, 28, 77, 25, 163, 137)}};
static const lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___lam__0___closed__2_value;
static const lean_string_object l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 48, .m_capacity = 48, .m_length = 47, .m_data = "mk_iff only applies to prop-valued declarations"};
static const lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___lam__0___closed__3 = (const lean_object*)&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___lam__0___closed__3_value;
static lean_once_cell_t l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___lam__0___closed__4;
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
static const lean_ctor_object l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(19, 54, 203, 28, 77, 25, 163, 137)}};
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
size_t v_x_4161__boxed_145_; size_t v_x_4162__boxed_146_; lean_object* v_res_147_; 
v_x_4161__boxed_145_ = lean_unbox_usize(v_x_141_);
lean_dec(v_x_141_);
v_x_4162__boxed_146_ = lean_unbox_usize(v_x_142_);
lean_dec(v_x_142_);
v_res_147_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3___redArg(v_x_140_, v_x_4161__boxed_145_, v_x_4162__boxed_146_, v_x_143_, v_x_144_);
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
lean_object* v___x_159_; lean_object* v_mctx_160_; lean_object* v_cache_161_; lean_object* v_zetaDeltaFVarIds_162_; lean_object* v_postponed_163_; lean_object* v_diag_164_; lean_object* v___x_166_; uint8_t v_isShared_167_; uint8_t v_isSharedCheck_193_; 
v___x_159_ = lean_st_ref_take(v___y_157_);
v_mctx_160_ = lean_ctor_get(v___x_159_, 0);
v_cache_161_ = lean_ctor_get(v___x_159_, 1);
v_zetaDeltaFVarIds_162_ = lean_ctor_get(v___x_159_, 2);
v_postponed_163_ = lean_ctor_get(v___x_159_, 3);
v_diag_164_ = lean_ctor_get(v___x_159_, 4);
v_isSharedCheck_193_ = !lean_is_exclusive(v___x_159_);
if (v_isSharedCheck_193_ == 0)
{
v___x_166_ = v___x_159_;
v_isShared_167_ = v_isSharedCheck_193_;
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
v_isShared_167_ = v_isSharedCheck_193_;
goto v_resetjp_165_;
}
v_resetjp_165_:
{
lean_object* v_depth_168_; lean_object* v_levelAssignDepth_169_; lean_object* v_lmvarCounter_170_; lean_object* v_mvarCounter_171_; lean_object* v_lDecls_172_; lean_object* v_decls_173_; lean_object* v_userNames_174_; lean_object* v_lAssignment_175_; lean_object* v_eAssignment_176_; lean_object* v_dAssignment_177_; lean_object* v_instanceTypedMVars_178_; lean_object* v___x_180_; uint8_t v_isShared_181_; uint8_t v_isSharedCheck_192_; 
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
v_isSharedCheck_192_ = !lean_is_exclusive(v_mctx_160_);
if (v_isSharedCheck_192_ == 0)
{
v___x_180_ = v_mctx_160_;
v_isShared_181_ = v_isSharedCheck_192_;
goto v_resetjp_179_;
}
else
{
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
v___x_180_ = lean_box(0);
v_isShared_181_ = v_isSharedCheck_192_;
goto v_resetjp_179_;
}
v_resetjp_179_:
{
lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_185_; 
v___x_182_ = lean_box(0);
v___x_183_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2___redArg(v_eAssignment_176_, v_mvarId_155_, v_val_156_);
if (v_isShared_181_ == 0)
{
lean_ctor_set(v___x_180_, 8, v___x_183_);
v___x_185_ = v___x_180_;
goto v_reusejp_184_;
}
else
{
lean_object* v_reuseFailAlloc_191_; 
v_reuseFailAlloc_191_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_191_, 0, v_depth_168_);
lean_ctor_set(v_reuseFailAlloc_191_, 1, v_levelAssignDepth_169_);
lean_ctor_set(v_reuseFailAlloc_191_, 2, v_lmvarCounter_170_);
lean_ctor_set(v_reuseFailAlloc_191_, 3, v_mvarCounter_171_);
lean_ctor_set(v_reuseFailAlloc_191_, 4, v_lDecls_172_);
lean_ctor_set(v_reuseFailAlloc_191_, 5, v_decls_173_);
lean_ctor_set(v_reuseFailAlloc_191_, 6, v_userNames_174_);
lean_ctor_set(v_reuseFailAlloc_191_, 7, v_lAssignment_175_);
lean_ctor_set(v_reuseFailAlloc_191_, 8, v___x_183_);
lean_ctor_set(v_reuseFailAlloc_191_, 9, v_dAssignment_177_);
lean_ctor_set(v_reuseFailAlloc_191_, 10, v_instanceTypedMVars_178_);
v___x_185_ = v_reuseFailAlloc_191_;
goto v_reusejp_184_;
}
v_reusejp_184_:
{
lean_object* v___x_187_; 
if (v_isShared_167_ == 0)
{
lean_ctor_set(v___x_166_, 0, v___x_185_);
v___x_187_ = v___x_166_;
goto v_reusejp_186_;
}
else
{
lean_object* v_reuseFailAlloc_190_; 
v_reuseFailAlloc_190_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_190_, 0, v___x_185_);
lean_ctor_set(v_reuseFailAlloc_190_, 1, v_cache_161_);
lean_ctor_set(v_reuseFailAlloc_190_, 2, v_zetaDeltaFVarIds_162_);
lean_ctor_set(v_reuseFailAlloc_190_, 3, v_postponed_163_);
lean_ctor_set(v_reuseFailAlloc_190_, 4, v_diag_164_);
v___x_187_ = v_reuseFailAlloc_190_;
goto v_reusejp_186_;
}
v_reusejp_186_:
{
lean_object* v___x_188_; lean_object* v___x_189_; 
v___x_188_ = lean_st_ref_put(v___y_157_, v___x_187_);
v___x_189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_189_, 0, v___x_182_);
return v___x_189_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1___redArg___boxed(lean_object* v_mvarId_194_, lean_object* v_val_195_, lean_object* v___y_196_, lean_object* v___y_197_){
_start:
{
lean_object* v_res_198_; 
v_res_198_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1___redArg(v_mvarId_194_, v_val_195_, v___y_196_);
lean_dec(v___y_196_);
return v_res_198_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1(lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v___y_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_, lean_object* v___y_236_){
_start:
{
lean_object* v_ref_238_; uint8_t v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; 
v_ref_238_ = lean_ctor_get(v___y_235_, 2);
v___x_239_ = 0;
v___x_240_ = l_Lean_SourceInfo_fromRef(v_ref_238_, v___x_239_);
v___x_241_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__3));
v___x_242_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__4));
lean_inc_n(v___x_240_, 9);
v___x_243_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_243_, 0, v___x_240_);
lean_ctor_set(v___x_243_, 1, v___x_241_);
v___x_244_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__7));
v___x_245_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__8));
v___x_246_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_246_, 0, v___x_240_);
lean_ctor_set(v___x_246_, 1, v___x_245_);
v___x_247_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__10));
v___x_248_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__12));
v___x_249_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__13));
v___x_250_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_250_, 0, v___x_240_);
lean_ctor_set(v___x_250_, 1, v___x_249_);
v___x_251_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__14));
v___x_252_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_252_, 0, v___x_240_);
lean_ctor_set(v___x_252_, 1, v___x_251_);
v___x_253_ = l_Lean_Syntax_node2(v___x_240_, v___x_248_, v___x_250_, v___x_252_);
v___x_254_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__15));
v___x_255_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_255_, 0, v___x_240_);
lean_ctor_set(v___x_255_, 1, v___x_254_);
lean_inc(v___x_253_);
v___x_256_ = l_Lean_Syntax_node3(v___x_240_, v___x_247_, v___x_253_, v___x_255_, v___x_253_);
v___x_257_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__16));
v___x_258_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_258_, 0, v___x_240_);
lean_ctor_set(v___x_258_, 1, v___x_257_);
v___x_259_ = l_Lean_Syntax_node3(v___x_240_, v___x_244_, v___x_246_, v___x_256_, v___x_258_);
v___x_260_ = l_Lean_Syntax_node2(v___x_240_, v___x_242_, v___x_243_, v___x_259_);
v___x_261_ = l_Lean_Elab_Tactic_evalTactic(v___x_260_, v___y_229_, v___y_230_, v___y_231_, v___y_232_, v___y_233_, v___y_234_, v___y_235_, v___y_236_);
return v___x_261_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___boxed(lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_){
_start:
{
lean_object* v_res_271_; 
v_res_271_ = l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1(v___y_262_, v___y_263_, v___y_264_, v___y_265_, v___y_266_, v___y_267_, v___y_268_, v___y_269_);
lean_dec(v___y_269_);
lean_dec_ref(v___y_268_);
lean_dec(v___y_267_);
lean_dec_ref(v___y_266_);
lean_dec(v___y_265_);
lean_dec_ref(v___y_264_);
lean_dec(v___y_263_);
lean_dec_ref(v___y_262_);
return v_res_271_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0_spec__0(lean_object* v_msgData_272_, lean_object* v___y_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_){
_start:
{
lean_object* v___x_278_; lean_object* v_env_279_; uint8_t v___x_280_; lean_object* v_env_281_; lean_object* v___x_282_; lean_object* v_toCold_283_; lean_object* v_mctx_284_; lean_object* v_lctx_285_; lean_object* v_options_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; 
v___x_278_ = lean_st_ref_get(v___y_276_);
v_env_279_ = lean_ctor_get(v___x_278_, 0);
lean_inc_ref(v_env_279_);
lean_dec(v___x_278_);
v___x_280_ = 0;
v_env_281_ = l_Lean_Environment_setRecordingDeps(v_env_279_, v___x_280_);
v___x_282_ = lean_st_ref_get(v___y_274_);
v_toCold_283_ = lean_ctor_get(v___y_275_, 0);
v_mctx_284_ = lean_ctor_get(v___x_282_, 0);
lean_inc_ref(v_mctx_284_);
lean_dec(v___x_282_);
v_lctx_285_ = lean_ctor_get(v___y_273_, 2);
v_options_286_ = lean_ctor_get(v_toCold_283_, 2);
lean_inc_ref(v_options_286_);
lean_inc_ref(v_lctx_285_);
v___x_287_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_287_, 0, v_env_281_);
lean_ctor_set(v___x_287_, 1, v_mctx_284_);
lean_ctor_set(v___x_287_, 2, v_lctx_285_);
lean_ctor_set(v___x_287_, 3, v_options_286_);
v___x_288_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_288_, 0, v___x_287_);
lean_ctor_set(v___x_288_, 1, v_msgData_272_);
v___x_289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_289_, 0, v___x_288_);
return v___x_289_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0_spec__0___boxed(lean_object* v_msgData_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_){
_start:
{
lean_object* v_res_296_; 
v_res_296_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0_spec__0(v_msgData_290_, v___y_291_, v___y_292_, v___y_293_, v___y_294_);
lean_dec(v___y_294_);
lean_dec_ref(v___y_293_);
lean_dec(v___y_292_);
lean_dec_ref(v___y_291_);
return v_res_296_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0___redArg(lean_object* v_msg_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_){
_start:
{
lean_object* v_ref_303_; lean_object* v___x_304_; lean_object* v_a_305_; lean_object* v___x_307_; uint8_t v_isShared_308_; uint8_t v_isSharedCheck_313_; 
v_ref_303_ = lean_ctor_get(v___y_300_, 2);
v___x_304_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0_spec__0(v_msg_297_, v___y_298_, v___y_299_, v___y_300_, v___y_301_);
v_a_305_ = lean_ctor_get(v___x_304_, 0);
v_isSharedCheck_313_ = !lean_is_exclusive(v___x_304_);
if (v_isSharedCheck_313_ == 0)
{
v___x_307_ = v___x_304_;
v_isShared_308_ = v_isSharedCheck_313_;
goto v_resetjp_306_;
}
else
{
lean_inc(v_a_305_);
lean_dec(v___x_304_);
v___x_307_ = lean_box(0);
v_isShared_308_ = v_isSharedCheck_313_;
goto v_resetjp_306_;
}
v_resetjp_306_:
{
lean_object* v___x_309_; lean_object* v___x_311_; 
lean_inc(v_ref_303_);
v___x_309_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_309_, 0, v_ref_303_);
lean_ctor_set(v___x_309_, 1, v_a_305_);
if (v_isShared_308_ == 0)
{
lean_ctor_set_tag(v___x_307_, 1);
lean_ctor_set(v___x_307_, 0, v___x_309_);
v___x_311_ = v___x_307_;
goto v_reusejp_310_;
}
else
{
lean_object* v_reuseFailAlloc_312_; 
v_reuseFailAlloc_312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_312_, 0, v___x_309_);
v___x_311_ = v_reuseFailAlloc_312_;
goto v_reusejp_310_;
}
v_reusejp_310_:
{
return v___x_311_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0___redArg___boxed(lean_object* v_msg_314_, lean_object* v___y_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_, lean_object* v___y_319_){
_start:
{
lean_object* v_res_320_; 
v_res_320_ = l_Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0___redArg(v_msg_314_, v___y_315_, v___y_316_, v___y_317_, v___y_318_);
lean_dec(v___y_318_);
lean_dec_ref(v___y_317_);
lean_dec(v___y_316_);
lean_dec_ref(v___y_315_);
return v_res_320_;
}
}
static lean_object* _init_l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___closed__1(void){
_start:
{
lean_object* v___x_322_; lean_object* v___x_323_; 
v___x_322_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___closed__0));
v___x_323_ = l_Lean_stringToMessageData(v___x_322_);
return v___x_323_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2(lean_object* v_x_339_, lean_object* v_x_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_){
_start:
{
if (lean_obj_tag(v_x_340_) == 0)
{
lean_object* v___x_346_; 
v___x_346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_346_, 0, v_x_339_);
return v___x_346_;
}
else
{
lean_object* v_head_347_; lean_object* v_tail_348_; lean_object* v___y_350_; lean_object* v___y_351_; lean_object* v___y_352_; lean_object* v___y_353_; lean_object* v___f_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; 
v_head_347_ = lean_ctor_get(v_x_340_, 0);
lean_inc(v_head_347_);
v_tail_348_ = lean_ctor_get(v_x_340_, 1);
lean_inc(v_tail_348_);
lean_dec_ref_known(v_x_340_, 2);
v___f_356_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___closed__3));
v___x_357_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_run___boxed), 9, 2);
lean_closure_set(v___x_357_, 0, v_x_339_);
lean_closure_set(v___x_357_, 1, v___f_356_);
v___x_358_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___closed__5));
v___x_359_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___closed__6));
v___x_360_ = l_Lean_Elab_Term_TermElabM_run___redArg(v___x_357_, v___x_358_, v___x_359_, v___y_341_, v___y_342_, v___y_343_, v___y_344_);
if (lean_obj_tag(v___x_360_) == 0)
{
lean_object* v_a_361_; lean_object* v_fst_362_; 
v_a_361_ = lean_ctor_get(v___x_360_, 0);
lean_inc(v_a_361_);
lean_dec_ref_known(v___x_360_, 1);
v_fst_362_ = lean_ctor_get(v_a_361_, 0);
lean_inc(v_fst_362_);
lean_dec(v_a_361_);
if (lean_obj_tag(v_fst_362_) == 1)
{
lean_object* v_tail_363_; 
v_tail_363_ = lean_ctor_get(v_fst_362_, 1);
lean_inc(v_tail_363_);
if (lean_obj_tag(v_tail_363_) == 1)
{
lean_object* v_tail_364_; 
v_tail_364_ = lean_ctor_get(v_tail_363_, 1);
if (lean_obj_tag(v_tail_364_) == 0)
{
lean_object* v_head_365_; lean_object* v_head_366_; lean_object* v___x_367_; 
v_head_365_ = lean_ctor_get(v_fst_362_, 0);
lean_inc(v_head_365_);
lean_dec_ref_known(v_fst_362_, 2);
v_head_366_ = lean_ctor_get(v_tail_363_, 0);
lean_inc(v_head_366_);
lean_dec_ref_known(v_tail_363_, 2);
v___x_367_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1___redArg(v_head_365_, v_head_347_, v___y_342_);
lean_dec_ref(v___x_367_);
v_x_339_ = v_head_366_;
v_x_340_ = v_tail_348_;
goto _start;
}
else
{
lean_dec_ref_known(v_tail_363_, 2);
lean_dec_ref_known(v_fst_362_, 2);
lean_dec(v_tail_348_);
lean_dec(v_head_347_);
v___y_350_ = v___y_341_;
v___y_351_ = v___y_342_;
v___y_352_ = v___y_343_;
v___y_353_ = v___y_344_;
goto v___jp_349_;
}
}
else
{
lean_dec_ref_known(v_fst_362_, 2);
lean_dec(v_tail_363_);
lean_dec(v_tail_348_);
lean_dec(v_head_347_);
v___y_350_ = v___y_341_;
v___y_351_ = v___y_342_;
v___y_352_ = v___y_343_;
v___y_353_ = v___y_344_;
goto v___jp_349_;
}
}
else
{
lean_dec(v_fst_362_);
lean_dec(v_tail_348_);
lean_dec(v_head_347_);
v___y_350_ = v___y_341_;
v___y_351_ = v___y_342_;
v___y_352_ = v___y_343_;
v___y_353_ = v___y_344_;
goto v___jp_349_;
}
}
else
{
lean_object* v_a_369_; lean_object* v___x_371_; uint8_t v_isShared_372_; uint8_t v_isSharedCheck_376_; 
lean_dec(v_tail_348_);
lean_dec(v_head_347_);
v_a_369_ = lean_ctor_get(v___x_360_, 0);
v_isSharedCheck_376_ = !lean_is_exclusive(v___x_360_);
if (v_isSharedCheck_376_ == 0)
{
v___x_371_ = v___x_360_;
v_isShared_372_ = v_isSharedCheck_376_;
goto v_resetjp_370_;
}
else
{
lean_inc(v_a_369_);
lean_dec(v___x_360_);
v___x_371_ = lean_box(0);
v_isShared_372_ = v_isSharedCheck_376_;
goto v_resetjp_370_;
}
v_resetjp_370_:
{
lean_object* v___x_374_; 
if (v_isShared_372_ == 0)
{
v___x_374_ = v___x_371_;
goto v_reusejp_373_;
}
else
{
lean_object* v_reuseFailAlloc_375_; 
v_reuseFailAlloc_375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_375_, 0, v_a_369_);
v___x_374_ = v_reuseFailAlloc_375_;
goto v_reusejp_373_;
}
v_reusejp_373_:
{
return v___x_374_;
}
}
}
v___jp_349_:
{
lean_object* v___x_354_; lean_object* v___x_355_; 
v___x_354_ = lean_obj_once(&l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___closed__1, &l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___closed__1_once, _init_l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___closed__1);
v___x_355_ = l_Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0___redArg(v___x_354_, v___y_350_, v___y_351_, v___y_352_, v___y_353_);
return v___x_355_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___boxed(lean_object* v_x_377_, lean_object* v_x_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_){
_start:
{
lean_object* v_res_384_; 
v_res_384_ = l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2(v_x_377_, v_x_378_, v___y_379_, v___y_380_, v___y_381_, v___y_382_);
lean_dec(v___y_382_);
lean_dec_ref(v___y_381_);
lean_dec(v___y_380_);
lean_dec_ref(v___y_379_);
return v_res_384_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi(lean_object* v_mvar_385_, lean_object* v_es_386_, lean_object* v_a_387_, lean_object* v_a_388_, lean_object* v_a_389_, lean_object* v_a_390_){
_start:
{
lean_object* v___x_392_; 
v___x_392_ = l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2(v_mvar_385_, v_es_386_, v_a_387_, v_a_388_, v_a_389_, v_a_390_);
return v___x_392_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi___boxed(lean_object* v_mvar_393_, lean_object* v_es_394_, lean_object* v_a_395_, lean_object* v_a_396_, lean_object* v_a_397_, lean_object* v_a_398_, lean_object* v_a_399_){
_start:
{
lean_object* v_res_400_; 
v_res_400_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi(v_mvar_393_, v_es_394_, v_a_395_, v_a_396_, v_a_397_, v_a_398_);
lean_dec(v_a_398_);
lean_dec_ref(v_a_397_);
lean_dec(v_a_396_);
lean_dec_ref(v_a_395_);
return v_res_400_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0(lean_object* v_00_u03b1_401_, lean_object* v_msg_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_){
_start:
{
lean_object* v___x_408_; 
v___x_408_ = l_Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0___redArg(v_msg_402_, v___y_403_, v___y_404_, v___y_405_, v___y_406_);
return v___x_408_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0___boxed(lean_object* v_00_u03b1_409_, lean_object* v_msg_410_, lean_object* v___y_411_, lean_object* v___y_412_, lean_object* v___y_413_, lean_object* v___y_414_, lean_object* v___y_415_){
_start:
{
lean_object* v_res_416_; 
v_res_416_ = l_Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0(v_00_u03b1_409_, v_msg_410_, v___y_411_, v___y_412_, v___y_413_, v___y_414_);
lean_dec(v___y_414_);
lean_dec_ref(v___y_413_);
lean_dec(v___y_412_);
lean_dec_ref(v___y_411_);
return v_res_416_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1(lean_object* v_mvarId_417_, lean_object* v_val_418_, lean_object* v___y_419_, lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_){
_start:
{
lean_object* v___x_424_; 
v___x_424_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1___redArg(v_mvarId_417_, v_val_418_, v___y_420_);
return v___x_424_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1___boxed(lean_object* v_mvarId_425_, lean_object* v_val_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_){
_start:
{
lean_object* v_res_432_; 
v_res_432_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1(v_mvarId_425_, v_val_426_, v___y_427_, v___y_428_, v___y_429_, v___y_430_);
lean_dec(v___y_430_);
lean_dec_ref(v___y_429_);
lean_dec(v___y_428_);
lean_dec_ref(v___y_427_);
return v_res_432_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2(lean_object* v_00_u03b2_433_, lean_object* v_x_434_, lean_object* v_x_435_, lean_object* v_x_436_){
_start:
{
lean_object* v___x_437_; 
v___x_437_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2___redArg(v_x_434_, v_x_435_, v_x_436_);
return v___x_437_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_438_, lean_object* v_x_439_, size_t v_x_440_, size_t v_x_441_, lean_object* v_x_442_, lean_object* v_x_443_){
_start:
{
lean_object* v___x_444_; 
v___x_444_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3___redArg(v_x_439_, v_x_440_, v_x_441_, v_x_442_, v_x_443_);
return v___x_444_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03b2_445_, lean_object* v_x_446_, lean_object* v_x_447_, lean_object* v_x_448_, lean_object* v_x_449_, lean_object* v_x_450_){
_start:
{
size_t v_x_4819__boxed_451_; size_t v_x_4820__boxed_452_; lean_object* v_res_453_; 
v_x_4819__boxed_451_ = lean_unbox_usize(v_x_447_);
lean_dec(v_x_447_);
v_x_4820__boxed_452_ = lean_unbox_usize(v_x_448_);
lean_dec(v_x_448_);
v_res_453_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3(v_00_u03b2_445_, v_x_446_, v_x_4819__boxed_451_, v_x_4820__boxed_452_, v_x_449_, v_x_450_);
return v_res_453_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3_spec__5(lean_object* v_00_u03b2_454_, lean_object* v_n_455_, lean_object* v_k_456_, lean_object* v_v_457_){
_start:
{
lean_object* v___x_458_; 
v___x_458_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3_spec__5___redArg(v_n_455_, v_k_456_, v_v_457_);
return v___x_458_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3_spec__6(lean_object* v_00_u03b2_459_, size_t v_depth_460_, lean_object* v_keys_461_, lean_object* v_vals_462_, lean_object* v_heq_463_, lean_object* v_i_464_, lean_object* v_entries_465_){
_start:
{
lean_object* v___x_466_; 
v___x_466_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3_spec__6___redArg(v_depth_460_, v_keys_461_, v_vals_462_, v_i_464_, v_entries_465_);
return v___x_466_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3_spec__6___boxed(lean_object* v_00_u03b2_467_, lean_object* v_depth_468_, lean_object* v_keys_469_, lean_object* v_vals_470_, lean_object* v_heq_471_, lean_object* v_i_472_, lean_object* v_entries_473_){
_start:
{
size_t v_depth_boxed_474_; lean_object* v_res_475_; 
v_depth_boxed_474_ = lean_unbox_usize(v_depth_468_);
lean_dec(v_depth_468_);
v_res_475_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3_spec__6(v_00_u03b2_467_, v_depth_boxed_474_, v_keys_469_, v_vals_470_, v_heq_471_, v_i_472_, v_entries_473_);
lean_dec_ref(v_vals_470_);
lean_dec_ref(v_keys_469_);
return v_res_475_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3_spec__5_spec__6(lean_object* v_00_u03b2_476_, lean_object* v_x_477_, lean_object* v_x_478_, lean_object* v_x_479_, lean_object* v_x_480_){
_start:
{
lean_object* v___x_481_; 
v___x_481_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3_spec__5_spec__6___redArg(v_x_477_, v_x_478_, v_x_479_, v_x_480_);
return v___x_481_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor_spec__0___redArg(lean_object* v_mvarId_482_, lean_object* v_x_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_){
_start:
{
lean_object* v___x_489_; 
v___x_489_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_482_, v_x_483_, v___y_484_, v___y_485_, v___y_486_, v___y_487_);
if (lean_obj_tag(v___x_489_) == 0)
{
lean_object* v_a_490_; lean_object* v___x_492_; uint8_t v_isShared_493_; uint8_t v_isSharedCheck_497_; 
v_a_490_ = lean_ctor_get(v___x_489_, 0);
v_isSharedCheck_497_ = !lean_is_exclusive(v___x_489_);
if (v_isSharedCheck_497_ == 0)
{
v___x_492_ = v___x_489_;
v_isShared_493_ = v_isSharedCheck_497_;
goto v_resetjp_491_;
}
else
{
lean_inc(v_a_490_);
lean_dec(v___x_489_);
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
v_reuseFailAlloc_496_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_498_; lean_object* v___x_500_; uint8_t v_isShared_501_; uint8_t v_isSharedCheck_505_; 
v_a_498_ = lean_ctor_get(v___x_489_, 0);
v_isSharedCheck_505_ = !lean_is_exclusive(v___x_489_);
if (v_isSharedCheck_505_ == 0)
{
v___x_500_ = v___x_489_;
v_isShared_501_ = v_isSharedCheck_505_;
goto v_resetjp_499_;
}
else
{
lean_inc(v_a_498_);
lean_dec(v___x_489_);
v___x_500_ = lean_box(0);
v_isShared_501_ = v_isSharedCheck_505_;
goto v_resetjp_499_;
}
v_resetjp_499_:
{
lean_object* v___x_503_; 
if (v_isShared_501_ == 0)
{
v___x_503_ = v___x_500_;
goto v_reusejp_502_;
}
else
{
lean_object* v_reuseFailAlloc_504_; 
v_reuseFailAlloc_504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_504_, 0, v_a_498_);
v___x_503_ = v_reuseFailAlloc_504_;
goto v_reusejp_502_;
}
v_reusejp_502_:
{
return v___x_503_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor_spec__0___redArg___boxed(lean_object* v_mvarId_506_, lean_object* v_x_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_){
_start:
{
lean_object* v_res_513_; 
v_res_513_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor_spec__0___redArg(v_mvarId_506_, v_x_507_, v___y_508_, v___y_509_, v___y_510_, v___y_511_);
lean_dec(v___y_511_);
lean_dec_ref(v___y_510_);
lean_dec(v___y_509_);
lean_dec_ref(v___y_508_);
return v_res_513_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor_spec__0(lean_object* v_00_u03b1_514_, lean_object* v_mvarId_515_, lean_object* v_x_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_){
_start:
{
lean_object* v___x_522_; 
v___x_522_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor_spec__0___redArg(v_mvarId_515_, v_x_516_, v___y_517_, v___y_518_, v___y_519_, v___y_520_);
return v___x_522_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor_spec__0___boxed(lean_object* v_00_u03b1_523_, lean_object* v_mvarId_524_, lean_object* v_x_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_){
_start:
{
lean_object* v_res_531_; 
v_res_531_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor_spec__0(v_00_u03b1_523_, v_mvarId_524_, v_x_525_, v___y_526_, v___y_527_, v___y_528_, v___y_529_);
lean_dec(v___y_529_);
lean_dec_ref(v___y_528_);
lean_dec(v___y_527_);
lean_dec_ref(v___y_526_);
return v_res_531_;
}
}
static lean_object* _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0___closed__2(void){
_start:
{
lean_object* v___x_535_; lean_object* v___x_536_; 
v___x_535_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0___closed__1));
v___x_536_ = l_Lean_MessageData_ofFormat(v___x_535_);
return v___x_536_;
}
}
static lean_object* _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0___closed__3(void){
_start:
{
lean_object* v___x_537_; lean_object* v___x_538_; 
v___x_537_ = lean_obj_once(&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0___closed__2, &l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0___closed__2_once, _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0___closed__2);
v___x_538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_538_, 0, v___x_537_);
return v___x_538_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0(lean_object* v_name_543_, lean_object* v_goal_544_, lean_object* v_idx_545_, lean_object* v_expected_x3f_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_){
_start:
{
lean_object* v___x_555_; 
lean_inc(v_name_543_);
lean_inc(v_goal_544_);
v___x_555_ = l_Lean_MVarId_checkNotAssigned(v_goal_544_, v_name_543_, v___y_547_, v___y_548_, v___y_549_, v___y_550_);
if (lean_obj_tag(v___x_555_) == 0)
{
lean_object* v___x_556_; 
lean_dec_ref_known(v___x_555_, 1);
lean_inc(v_goal_544_);
v___x_556_ = l_Lean_MVarId_getType_x27(v_goal_544_, v___y_547_, v___y_548_, v___y_549_, v___y_550_);
if (lean_obj_tag(v___x_556_) == 0)
{
lean_object* v_a_557_; lean_object* v___x_558_; 
v_a_557_ = lean_ctor_get(v___x_556_, 0);
lean_inc(v_a_557_);
lean_dec_ref_known(v___x_556_, 1);
v___x_558_ = l_Lean_Expr_getAppFn(v_a_557_);
lean_dec(v_a_557_);
if (lean_obj_tag(v___x_558_) == 4)
{
lean_object* v_declName_559_; lean_object* v_us_560_; lean_object* v___x_561_; lean_object* v_env_562_; uint8_t v___x_563_; lean_object* v___x_564_; 
v_declName_559_ = lean_ctor_get(v___x_558_, 0);
lean_inc(v_declName_559_);
v_us_560_ = lean_ctor_get(v___x_558_, 1);
lean_inc(v_us_560_);
lean_dec_ref_known(v___x_558_, 2);
v___x_561_ = lean_st_ref_get(v___y_550_);
v_env_562_ = lean_ctor_get(v___x_561_, 0);
lean_inc_ref(v_env_562_);
lean_dec(v___x_561_);
v___x_563_ = 0;
v___x_564_ = l_Lean_Environment_find_x3f(v_env_562_, v_declName_559_, v___x_563_);
if (lean_obj_tag(v___x_564_) == 0)
{
lean_dec(v_us_560_);
lean_dec(v_expected_x3f_546_);
lean_dec(v_idx_545_);
goto v___jp_552_;
}
else
{
lean_object* v_val_565_; lean_object* v___x_567_; uint8_t v_isShared_568_; uint8_t v_isSharedCheck_635_; 
v_val_565_ = lean_ctor_get(v___x_564_, 0);
v_isSharedCheck_635_ = !lean_is_exclusive(v___x_564_);
if (v_isSharedCheck_635_ == 0)
{
v___x_567_ = v___x_564_;
v_isShared_568_ = v_isSharedCheck_635_;
goto v_resetjp_566_;
}
else
{
lean_inc(v_val_565_);
lean_dec(v___x_564_);
v___x_567_ = lean_box(0);
v_isShared_568_ = v_isSharedCheck_635_;
goto v_resetjp_566_;
}
v_resetjp_566_:
{
if (lean_obj_tag(v_val_565_) == 5)
{
lean_object* v_val_569_; lean_object* v___x_571_; uint8_t v_isShared_572_; uint8_t v_isSharedCheck_634_; 
v_val_569_ = lean_ctor_get(v_val_565_, 0);
v_isSharedCheck_634_ = !lean_is_exclusive(v_val_565_);
if (v_isSharedCheck_634_ == 0)
{
v___x_571_ = v_val_565_;
v_isShared_572_ = v_isSharedCheck_634_;
goto v_resetjp_570_;
}
else
{
lean_inc(v_val_569_);
lean_dec(v_val_565_);
v___x_571_ = lean_box(0);
v_isShared_572_ = v_isSharedCheck_634_;
goto v_resetjp_570_;
}
v_resetjp_570_:
{
lean_object* v___y_574_; lean_object* v___y_575_; lean_object* v___y_576_; lean_object* v___y_577_; 
if (lean_obj_tag(v_expected_x3f_546_) == 1)
{
lean_object* v_val_604_; lean_object* v___x_606_; uint8_t v_isShared_607_; uint8_t v_isSharedCheck_633_; 
v_val_604_ = lean_ctor_get(v_expected_x3f_546_, 0);
v_isSharedCheck_633_ = !lean_is_exclusive(v_expected_x3f_546_);
if (v_isSharedCheck_633_ == 0)
{
v___x_606_ = v_expected_x3f_546_;
v_isShared_607_ = v_isSharedCheck_633_;
goto v_resetjp_605_;
}
else
{
lean_inc(v_val_604_);
lean_dec(v_expected_x3f_546_);
v___x_606_ = lean_box(0);
v_isShared_607_ = v_isSharedCheck_633_;
goto v_resetjp_605_;
}
v_resetjp_605_:
{
lean_object* v_ctors_608_; lean_object* v___x_609_; uint8_t v___x_610_; 
v_ctors_608_ = lean_ctor_get(v_val_569_, 4);
v___x_609_ = l_List_lengthTR___redArg(v_ctors_608_);
v___x_610_ = lean_nat_dec_eq(v___x_609_, v_val_604_);
lean_dec(v___x_609_);
if (v___x_610_ == 0)
{
uint8_t v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_622_; 
v___x_611_ = 1;
lean_inc(v_name_543_);
v___x_612_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_543_, v___x_611_);
v___x_613_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0___closed__7));
v___x_614_ = lean_string_append(v___x_612_, v___x_613_);
v___x_615_ = l_Nat_reprFast(v_val_604_);
v___x_616_ = lean_string_append(v___x_614_, v___x_615_);
lean_dec_ref(v___x_615_);
v___x_617_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0___closed__6));
v___x_618_ = lean_string_append(v___x_616_, v___x_617_);
v___x_619_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_619_, 0, v___x_618_);
v___x_620_ = l_Lean_MessageData_ofFormat(v___x_619_);
if (v_isShared_607_ == 0)
{
lean_ctor_set(v___x_606_, 0, v___x_620_);
v___x_622_ = v___x_606_;
goto v_reusejp_621_;
}
else
{
lean_object* v_reuseFailAlloc_632_; 
v_reuseFailAlloc_632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_632_, 0, v___x_620_);
v___x_622_ = v_reuseFailAlloc_632_;
goto v_reusejp_621_;
}
v_reusejp_621_:
{
lean_object* v___x_623_; 
lean_inc(v_goal_544_);
lean_inc(v_name_543_);
v___x_623_ = l_Lean_Meta_throwTacticEx___redArg(v_name_543_, v_goal_544_, v___x_622_, v___y_547_, v___y_548_, v___y_549_, v___y_550_);
if (lean_obj_tag(v___x_623_) == 0)
{
lean_dec_ref_known(v___x_623_, 1);
v___y_574_ = v___y_547_;
v___y_575_ = v___y_548_;
v___y_576_ = v___y_549_;
v___y_577_ = v___y_550_;
goto v___jp_573_;
}
else
{
lean_object* v_a_624_; lean_object* v___x_626_; uint8_t v_isShared_627_; uint8_t v_isSharedCheck_631_; 
lean_del_object(v___x_571_);
lean_dec_ref(v_val_569_);
lean_del_object(v___x_567_);
lean_dec(v_us_560_);
lean_dec(v_idx_545_);
lean_dec(v_goal_544_);
lean_dec(v_name_543_);
v_a_624_ = lean_ctor_get(v___x_623_, 0);
v_isSharedCheck_631_ = !lean_is_exclusive(v___x_623_);
if (v_isSharedCheck_631_ == 0)
{
v___x_626_ = v___x_623_;
v_isShared_627_ = v_isSharedCheck_631_;
goto v_resetjp_625_;
}
else
{
lean_inc(v_a_624_);
lean_dec(v___x_623_);
v___x_626_ = lean_box(0);
v_isShared_627_ = v_isSharedCheck_631_;
goto v_resetjp_625_;
}
v_resetjp_625_:
{
lean_object* v___x_629_; 
if (v_isShared_627_ == 0)
{
v___x_629_ = v___x_626_;
goto v_reusejp_628_;
}
else
{
lean_object* v_reuseFailAlloc_630_; 
v_reuseFailAlloc_630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_630_, 0, v_a_624_);
v___x_629_ = v_reuseFailAlloc_630_;
goto v_reusejp_628_;
}
v_reusejp_628_:
{
return v___x_629_;
}
}
}
}
}
else
{
lean_del_object(v___x_606_);
lean_dec(v_val_604_);
v___y_574_ = v___y_547_;
v___y_575_ = v___y_548_;
v___y_576_ = v___y_549_;
v___y_577_ = v___y_550_;
goto v___jp_573_;
}
}
}
else
{
lean_dec(v_expected_x3f_546_);
v___y_574_ = v___y_547_;
v___y_575_ = v___y_548_;
v___y_576_ = v___y_549_;
v___y_577_ = v___y_550_;
goto v___jp_573_;
}
v___jp_573_:
{
lean_object* v_ctors_578_; lean_object* v___x_579_; uint8_t v___x_580_; 
v_ctors_578_ = lean_ctor_get(v_val_569_, 4);
lean_inc(v_ctors_578_);
lean_dec_ref(v_val_569_);
v___x_579_ = l_List_lengthTR___redArg(v_ctors_578_);
v___x_580_ = lean_nat_dec_lt(v_idx_545_, v___x_579_);
if (v___x_580_ == 0)
{
lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_591_; 
lean_dec(v_ctors_578_);
lean_dec(v_us_560_);
v___x_581_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0___closed__4));
v___x_582_ = l_Nat_reprFast(v_idx_545_);
v___x_583_ = lean_string_append(v___x_581_, v___x_582_);
lean_dec_ref(v___x_582_);
v___x_584_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0___closed__5));
v___x_585_ = lean_string_append(v___x_583_, v___x_584_);
v___x_586_ = l_Nat_reprFast(v___x_579_);
v___x_587_ = lean_string_append(v___x_585_, v___x_586_);
lean_dec_ref(v___x_586_);
v___x_588_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0___closed__6));
v___x_589_ = lean_string_append(v___x_587_, v___x_588_);
if (v_isShared_572_ == 0)
{
lean_ctor_set_tag(v___x_571_, 3);
lean_ctor_set(v___x_571_, 0, v___x_589_);
v___x_591_ = v___x_571_;
goto v_reusejp_590_;
}
else
{
lean_object* v_reuseFailAlloc_597_; 
v_reuseFailAlloc_597_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_597_, 0, v___x_589_);
v___x_591_ = v_reuseFailAlloc_597_;
goto v_reusejp_590_;
}
v_reusejp_590_:
{
lean_object* v___x_592_; lean_object* v___x_594_; 
v___x_592_ = l_Lean_MessageData_ofFormat(v___x_591_);
if (v_isShared_568_ == 0)
{
lean_ctor_set(v___x_567_, 0, v___x_592_);
v___x_594_ = v___x_567_;
goto v_reusejp_593_;
}
else
{
lean_object* v_reuseFailAlloc_596_; 
v_reuseFailAlloc_596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_596_, 0, v___x_592_);
v___x_594_ = v_reuseFailAlloc_596_;
goto v_reusejp_593_;
}
v_reusejp_593_:
{
lean_object* v___x_595_; 
v___x_595_ = l_Lean_Meta_throwTacticEx___redArg(v_name_543_, v_goal_544_, v___x_594_, v___y_574_, v___y_575_, v___y_576_, v___y_577_);
return v___x_595_;
}
}
}
else
{
lean_object* v___x_598_; lean_object* v___x_599_; uint8_t v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; 
lean_dec(v___x_579_);
lean_del_object(v___x_571_);
lean_del_object(v___x_567_);
lean_dec(v_name_543_);
v___x_598_ = l_List_get___redArg(v_ctors_578_, v_idx_545_);
lean_dec(v_ctors_578_);
v___x_599_ = l_Lean_mkConst(v___x_598_, v_us_560_);
v___x_600_ = 0;
v___x_601_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_601_, 0, v___x_600_);
lean_ctor_set_uint8(v___x_601_, 1, v___x_580_);
lean_ctor_set_uint8(v___x_601_, 2, v___x_563_);
lean_ctor_set_uint8(v___x_601_, 3, v___x_580_);
v___x_602_ = lean_box(0);
v___x_603_ = l_Lean_MVarId_apply(v_goal_544_, v___x_599_, v___x_601_, v___x_602_, v___y_574_, v___y_575_, v___y_576_, v___y_577_);
return v___x_603_;
}
}
}
}
else
{
lean_del_object(v___x_567_);
lean_dec(v_val_565_);
lean_dec(v_us_560_);
lean_dec(v_expected_x3f_546_);
lean_dec(v_idx_545_);
goto v___jp_552_;
}
}
}
}
else
{
lean_dec_ref(v___x_558_);
lean_dec(v_expected_x3f_546_);
lean_dec(v_idx_545_);
goto v___jp_552_;
}
}
else
{
lean_object* v_a_636_; lean_object* v___x_638_; uint8_t v_isShared_639_; uint8_t v_isSharedCheck_643_; 
lean_dec(v_expected_x3f_546_);
lean_dec(v_idx_545_);
lean_dec(v_goal_544_);
lean_dec(v_name_543_);
v_a_636_ = lean_ctor_get(v___x_556_, 0);
v_isSharedCheck_643_ = !lean_is_exclusive(v___x_556_);
if (v_isSharedCheck_643_ == 0)
{
v___x_638_ = v___x_556_;
v_isShared_639_ = v_isSharedCheck_643_;
goto v_resetjp_637_;
}
else
{
lean_inc(v_a_636_);
lean_dec(v___x_556_);
v___x_638_ = lean_box(0);
v_isShared_639_ = v_isSharedCheck_643_;
goto v_resetjp_637_;
}
v_resetjp_637_:
{
lean_object* v___x_641_; 
if (v_isShared_639_ == 0)
{
v___x_641_ = v___x_638_;
goto v_reusejp_640_;
}
else
{
lean_object* v_reuseFailAlloc_642_; 
v_reuseFailAlloc_642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_642_, 0, v_a_636_);
v___x_641_ = v_reuseFailAlloc_642_;
goto v_reusejp_640_;
}
v_reusejp_640_:
{
return v___x_641_;
}
}
}
}
else
{
lean_object* v_a_644_; lean_object* v___x_646_; uint8_t v_isShared_647_; uint8_t v_isSharedCheck_651_; 
lean_dec(v_expected_x3f_546_);
lean_dec(v_idx_545_);
lean_dec(v_goal_544_);
lean_dec(v_name_543_);
v_a_644_ = lean_ctor_get(v___x_555_, 0);
v_isSharedCheck_651_ = !lean_is_exclusive(v___x_555_);
if (v_isSharedCheck_651_ == 0)
{
v___x_646_ = v___x_555_;
v_isShared_647_ = v_isSharedCheck_651_;
goto v_resetjp_645_;
}
else
{
lean_inc(v_a_644_);
lean_dec(v___x_555_);
v___x_646_ = lean_box(0);
v_isShared_647_ = v_isSharedCheck_651_;
goto v_resetjp_645_;
}
v_resetjp_645_:
{
lean_object* v___x_649_; 
if (v_isShared_647_ == 0)
{
v___x_649_ = v___x_646_;
goto v_reusejp_648_;
}
else
{
lean_object* v_reuseFailAlloc_650_; 
v_reuseFailAlloc_650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_650_, 0, v_a_644_);
v___x_649_ = v_reuseFailAlloc_650_;
goto v_reusejp_648_;
}
v_reusejp_648_:
{
return v___x_649_;
}
}
}
v___jp_552_:
{
lean_object* v___x_553_; lean_object* v___x_554_; 
v___x_553_ = lean_obj_once(&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0___closed__3, &l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0___closed__3_once, _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0___closed__3);
v___x_554_ = l_Lean_Meta_throwTacticEx___redArg(v_name_543_, v_goal_544_, v___x_553_, v___y_547_, v___y_548_, v___y_549_, v___y_550_);
return v___x_554_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0___boxed(lean_object* v_name_652_, lean_object* v_goal_653_, lean_object* v_idx_654_, lean_object* v_expected_x3f_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_){
_start:
{
lean_object* v_res_661_; 
v_res_661_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0(v_name_652_, v_goal_653_, v_idx_654_, v_expected_x3f_655_, v___y_656_, v___y_657_, v___y_658_, v___y_659_);
lean_dec(v___y_659_);
lean_dec_ref(v___y_658_);
lean_dec(v___y_657_);
lean_dec_ref(v___y_656_);
return v_res_661_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor(lean_object* v_name_662_, lean_object* v_idx_663_, lean_object* v_expected_x3f_664_, lean_object* v_goal_665_, lean_object* v_a_666_, lean_object* v_a_667_, lean_object* v_a_668_, lean_object* v_a_669_){
_start:
{
lean_object* v___f_671_; lean_object* v___x_672_; 
lean_inc(v_goal_665_);
v___f_671_ = lean_alloc_closure((void*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0___boxed), 9, 4);
lean_closure_set(v___f_671_, 0, v_name_662_);
lean_closure_set(v___f_671_, 1, v_goal_665_);
lean_closure_set(v___f_671_, 2, v_idx_663_);
lean_closure_set(v___f_671_, 3, v_expected_x3f_664_);
v___x_672_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor_spec__0___redArg(v_goal_665_, v___f_671_, v_a_666_, v_a_667_, v_a_668_, v_a_669_);
return v___x_672_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___boxed(lean_object* v_name_673_, lean_object* v_idx_674_, lean_object* v_expected_x3f_675_, lean_object* v_goal_676_, lean_object* v_a_677_, lean_object* v_a_678_, lean_object* v_a_679_, lean_object* v_a_680_, lean_object* v_a_681_){
_start:
{
lean_object* v_res_682_; 
v_res_682_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor(v_name_673_, v_idx_674_, v_expected_x3f_675_, v_goal_676_, v_a_677_, v_a_678_, v_a_679_, v_a_680_);
lean_dec(v_a_680_);
lean_dec_ref(v_a_679_);
lean_dec(v_a_678_);
lean_dec_ref(v_a_677_);
return v_res_682_;
}
}
static lean_object* _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__1(void){
_start:
{
lean_object* v___x_684_; lean_object* v___x_685_; 
v___x_684_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__0));
v___x_685_ = l_Lean_stringToMessageData(v___x_684_);
return v___x_685_;
}
}
static lean_object* _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__8(void){
_start:
{
lean_object* v___x_695_; lean_object* v___x_696_; 
v___x_695_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__7));
v___x_696_ = l_Lean_stringToMessageData(v___x_695_);
return v___x_696_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select(lean_object* v_m_697_, lean_object* v_n_698_, lean_object* v_goal_699_, lean_object* v_a_700_, lean_object* v_a_701_, lean_object* v_a_702_, lean_object* v_a_703_){
_start:
{
lean_object* v___y_706_; lean_object* v___y_707_; lean_object* v___y_708_; lean_object* v___y_709_; lean_object* v___y_713_; lean_object* v___y_714_; lean_object* v___y_715_; lean_object* v___y_716_; lean_object* v_zero_719_; uint8_t v_isZero_720_; 
v_zero_719_ = lean_unsigned_to_nat(0u);
v_isZero_720_ = lean_nat_dec_eq(v_m_697_, v_zero_719_);
if (v_isZero_720_ == 1)
{
uint8_t v_isZero_721_; 
lean_dec(v_m_697_);
v_isZero_721_ = lean_nat_dec_eq(v_n_698_, v_zero_719_);
lean_dec(v_n_698_);
if (v_isZero_721_ == 1)
{
lean_object* v___x_722_; 
v___x_722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_722_, 0, v_goal_699_);
return v___x_722_;
}
else
{
lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; 
v___x_723_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__3));
v___x_724_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__4));
v___x_725_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor(v___x_723_, v_zero_719_, v___x_724_, v_goal_699_, v_a_700_, v_a_701_, v_a_702_, v_a_703_);
if (lean_obj_tag(v___x_725_) == 0)
{
lean_object* v_a_726_; lean_object* v___x_728_; uint8_t v_isShared_729_; uint8_t v_isSharedCheck_735_; 
v_a_726_ = lean_ctor_get(v___x_725_, 0);
v_isSharedCheck_735_ = !lean_is_exclusive(v___x_725_);
if (v_isSharedCheck_735_ == 0)
{
v___x_728_ = v___x_725_;
v_isShared_729_ = v_isSharedCheck_735_;
goto v_resetjp_727_;
}
else
{
lean_inc(v_a_726_);
lean_dec(v___x_725_);
v___x_728_ = lean_box(0);
v_isShared_729_ = v_isSharedCheck_735_;
goto v_resetjp_727_;
}
v_resetjp_727_:
{
if (lean_obj_tag(v_a_726_) == 1)
{
lean_object* v_tail_730_; 
v_tail_730_ = lean_ctor_get(v_a_726_, 1);
if (lean_obj_tag(v_tail_730_) == 0)
{
lean_object* v_head_731_; lean_object* v___x_733_; 
v_head_731_ = lean_ctor_get(v_a_726_, 0);
lean_inc(v_head_731_);
lean_dec_ref_known(v_a_726_, 2);
if (v_isShared_729_ == 0)
{
lean_ctor_set(v___x_728_, 0, v_head_731_);
v___x_733_ = v___x_728_;
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
lean_dec_ref_known(v_a_726_, 2);
lean_del_object(v___x_728_);
v___y_706_ = v_a_700_;
v___y_707_ = v_a_701_;
v___y_708_ = v_a_702_;
v___y_709_ = v_a_703_;
goto v___jp_705_;
}
}
else
{
lean_del_object(v___x_728_);
lean_dec(v_a_726_);
v___y_706_ = v_a_700_;
v___y_707_ = v_a_701_;
v___y_708_ = v_a_702_;
v___y_709_ = v_a_703_;
goto v___jp_705_;
}
}
}
else
{
lean_object* v_a_736_; lean_object* v___x_738_; uint8_t v_isShared_739_; uint8_t v_isSharedCheck_743_; 
v_a_736_ = lean_ctor_get(v___x_725_, 0);
v_isSharedCheck_743_ = !lean_is_exclusive(v___x_725_);
if (v_isSharedCheck_743_ == 0)
{
v___x_738_ = v___x_725_;
v_isShared_739_ = v_isSharedCheck_743_;
goto v_resetjp_737_;
}
else
{
lean_inc(v_a_736_);
lean_dec(v___x_725_);
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
v_isZero_744_ = lean_nat_dec_eq(v_n_698_, v_zero_719_);
if (v_isZero_744_ == 0)
{
lean_object* v_one_745_; lean_object* v_n_746_; lean_object* v_n_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; 
v_one_745_ = lean_unsigned_to_nat(1u);
v_n_746_ = lean_nat_sub(v_m_697_, v_one_745_);
lean_dec(v_m_697_);
v_n_747_ = lean_nat_sub(v_n_698_, v_one_745_);
lean_dec(v_n_698_);
v___x_748_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__6));
v___x_749_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__4));
v___x_750_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor(v___x_748_, v_one_745_, v___x_749_, v_goal_699_, v_a_700_, v_a_701_, v_a_702_, v_a_703_);
if (lean_obj_tag(v___x_750_) == 0)
{
lean_object* v_a_751_; 
v_a_751_ = lean_ctor_get(v___x_750_, 0);
lean_inc(v_a_751_);
lean_dec_ref_known(v___x_750_, 1);
if (lean_obj_tag(v_a_751_) == 1)
{
lean_object* v_tail_752_; 
v_tail_752_ = lean_ctor_get(v_a_751_, 1);
if (lean_obj_tag(v_tail_752_) == 0)
{
lean_object* v_head_753_; 
v_head_753_ = lean_ctor_get(v_a_751_, 0);
lean_inc(v_head_753_);
lean_dec_ref_known(v_a_751_, 2);
v_m_697_ = v_n_746_;
v_n_698_ = v_n_747_;
v_goal_699_ = v_head_753_;
goto _start;
}
else
{
lean_dec_ref_known(v_a_751_, 2);
lean_dec(v_n_747_);
lean_dec(v_n_746_);
v___y_713_ = v_a_700_;
v___y_714_ = v_a_701_;
v___y_715_ = v_a_702_;
v___y_716_ = v_a_703_;
goto v___jp_712_;
}
}
else
{
lean_dec(v_a_751_);
lean_dec(v_n_747_);
lean_dec(v_n_746_);
v___y_713_ = v_a_700_;
v___y_714_ = v_a_701_;
v___y_715_ = v_a_702_;
v___y_716_ = v_a_703_;
goto v___jp_712_;
}
}
else
{
lean_object* v_a_755_; lean_object* v___x_757_; uint8_t v_isShared_758_; uint8_t v_isSharedCheck_762_; 
lean_dec(v_n_747_);
lean_dec(v_n_746_);
v_a_755_ = lean_ctor_get(v___x_750_, 0);
v_isSharedCheck_762_ = !lean_is_exclusive(v___x_750_);
if (v_isSharedCheck_762_ == 0)
{
v___x_757_ = v___x_750_;
v_isShared_758_ = v_isSharedCheck_762_;
goto v_resetjp_756_;
}
else
{
lean_inc(v_a_755_);
lean_dec(v___x_750_);
v___x_757_ = lean_box(0);
v_isShared_758_ = v_isSharedCheck_762_;
goto v_resetjp_756_;
}
v_resetjp_756_:
{
lean_object* v___x_760_; 
if (v_isShared_758_ == 0)
{
v___x_760_ = v___x_757_;
goto v_reusejp_759_;
}
else
{
lean_object* v_reuseFailAlloc_761_; 
v_reuseFailAlloc_761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_761_, 0, v_a_755_);
v___x_760_ = v_reuseFailAlloc_761_;
goto v_reusejp_759_;
}
v_reusejp_759_:
{
return v___x_760_;
}
}
}
}
else
{
lean_object* v___x_763_; lean_object* v___x_764_; 
lean_dec(v_goal_699_);
lean_dec(v_n_698_);
lean_dec(v_m_697_);
v___x_763_ = lean_obj_once(&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__8, &l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__8_once, _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__8);
v___x_764_ = l_Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0___redArg(v___x_763_, v_a_700_, v_a_701_, v_a_702_, v_a_703_);
return v___x_764_;
}
}
v___jp_705_:
{
lean_object* v___x_710_; lean_object* v___x_711_; 
v___x_710_ = lean_obj_once(&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__1, &l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__1_once, _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__1);
v___x_711_ = l_Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0___redArg(v___x_710_, v___y_706_, v___y_707_, v___y_708_, v___y_709_);
return v___x_711_;
}
v___jp_712_:
{
lean_object* v___x_717_; lean_object* v___x_718_; 
v___x_717_ = lean_obj_once(&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__1, &l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__1_once, _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__1);
v___x_718_ = l_Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0___redArg(v___x_717_, v___y_713_, v___y_714_, v___y_715_, v___y_716_);
return v___x_718_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___boxed(lean_object* v_m_765_, lean_object* v_n_766_, lean_object* v_goal_767_, lean_object* v_a_768_, lean_object* v_a_769_, lean_object* v_a_770_, lean_object* v_a_771_, lean_object* v_a_772_){
_start:
{
lean_object* v_res_773_; 
v_res_773_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select(v_m_765_, v_n_766_, v_goal_767_, v_a_768_, v_a_769_, v_a_770_, v_a_771_);
lean_dec(v_a_771_);
lean_dec_ref(v_a_770_);
lean_dec(v_a_769_);
lean_dec_ref(v_a_768_);
return v_res_773_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_compactRelation___lam__0(lean_object* v___y_774_){
_start:
{
lean_inc_ref(v___y_774_);
return v___y_774_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_compactRelation___lam__0___boxed(lean_object* v___y_775_){
_start:
{
lean_object* v_res_776_; 
v_res_776_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_compactRelation___lam__0(v___y_775_);
lean_dec_ref(v___y_775_);
return v_res_776_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_compactRelation___lam__1(lean_object* v_snd_777_, lean_object* v_head_778_, lean_object* v_fst_779_, lean_object* v___y_780_){
_start:
{
lean_object* v___x_781_; lean_object* v___x_782_; 
v___x_781_ = lean_apply_1(v_snd_777_, v___y_780_);
v___x_782_ = l_Lean_Expr_replaceFVar(v___x_781_, v_head_778_, v_fst_779_);
lean_dec_ref(v___x_781_);
return v___x_782_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_compactRelation___lam__1___boxed(lean_object* v_snd_783_, lean_object* v_head_784_, lean_object* v_fst_785_, lean_object* v___y_786_){
_start:
{
lean_object* v_res_787_; 
v_res_787_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_compactRelation___lam__1(v_snd_783_, v_head_784_, v_fst_785_, v___y_786_);
lean_dec_ref(v_fst_785_);
return v_res_787_;
}
}
LEAN_EXPORT lean_object* l_List_span_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_compactRelation_spec__0(lean_object* v_head_788_, lean_object* v_a_789_, lean_object* v_a_790_){
_start:
{
if (lean_obj_tag(v_a_789_) == 0)
{
lean_object* v___x_791_; lean_object* v___x_792_; 
v___x_791_ = l_List_reverse___redArg(v_a_790_);
v___x_792_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_792_, 0, v___x_791_);
lean_ctor_set(v___x_792_, 1, v_a_789_);
return v___x_792_;
}
else
{
lean_object* v_head_793_; lean_object* v_tail_794_; lean_object* v_snd_795_; uint8_t v___x_796_; 
v_head_793_ = lean_ctor_get(v_a_789_, 0);
lean_inc(v_head_793_);
v_tail_794_ = lean_ctor_get(v_a_789_, 1);
v_snd_795_ = lean_ctor_get(v_head_793_, 1);
v___x_796_ = lean_expr_eqv(v_snd_795_, v_head_788_);
if (v___x_796_ == 0)
{
lean_object* v___x_798_; uint8_t v_isShared_799_; uint8_t v_isSharedCheck_804_; 
lean_inc(v_tail_794_);
v_isSharedCheck_804_ = !lean_is_exclusive(v_a_789_);
if (v_isSharedCheck_804_ == 0)
{
lean_object* v_unused_805_; lean_object* v_unused_806_; 
v_unused_805_ = lean_ctor_get(v_a_789_, 1);
lean_dec(v_unused_805_);
v_unused_806_ = lean_ctor_get(v_a_789_, 0);
lean_dec(v_unused_806_);
v___x_798_ = v_a_789_;
v_isShared_799_ = v_isSharedCheck_804_;
goto v_resetjp_797_;
}
else
{
lean_dec(v_a_789_);
v___x_798_ = lean_box(0);
v_isShared_799_ = v_isSharedCheck_804_;
goto v_resetjp_797_;
}
v_resetjp_797_:
{
lean_object* v___x_801_; 
if (v_isShared_799_ == 0)
{
lean_ctor_set(v___x_798_, 1, v_a_790_);
v___x_801_ = v___x_798_;
goto v_reusejp_800_;
}
else
{
lean_object* v_reuseFailAlloc_803_; 
v_reuseFailAlloc_803_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_803_, 0, v_head_793_);
lean_ctor_set(v_reuseFailAlloc_803_, 1, v_a_790_);
v___x_801_ = v_reuseFailAlloc_803_;
goto v_reusejp_800_;
}
v_reusejp_800_:
{
v_a_789_ = v_tail_794_;
v_a_790_ = v___x_801_;
goto _start;
}
}
}
else
{
lean_object* v___x_808_; uint8_t v_isShared_809_; uint8_t v_isSharedCheck_814_; 
v_isSharedCheck_814_ = !lean_is_exclusive(v_head_793_);
if (v_isSharedCheck_814_ == 0)
{
lean_object* v_unused_815_; lean_object* v_unused_816_; 
v_unused_815_ = lean_ctor_get(v_head_793_, 1);
lean_dec(v_unused_815_);
v_unused_816_ = lean_ctor_get(v_head_793_, 0);
lean_dec(v_unused_816_);
v___x_808_ = v_head_793_;
v_isShared_809_ = v_isSharedCheck_814_;
goto v_resetjp_807_;
}
else
{
lean_dec(v_head_793_);
v___x_808_ = lean_box(0);
v_isShared_809_ = v_isSharedCheck_814_;
goto v_resetjp_807_;
}
v_resetjp_807_:
{
lean_object* v___x_810_; lean_object* v___x_812_; 
v___x_810_ = l_List_reverse___redArg(v_a_790_);
if (v_isShared_809_ == 0)
{
lean_ctor_set(v___x_808_, 1, v_a_789_);
lean_ctor_set(v___x_808_, 0, v___x_810_);
v___x_812_ = v___x_808_;
goto v_reusejp_811_;
}
else
{
lean_object* v_reuseFailAlloc_813_; 
v_reuseFailAlloc_813_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_813_, 0, v___x_810_);
lean_ctor_set(v_reuseFailAlloc_813_, 1, v_a_789_);
v___x_812_ = v_reuseFailAlloc_813_;
goto v_reusejp_811_;
}
v_reusejp_811_:
{
return v___x_812_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_span_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_compactRelation_spec__0___boxed(lean_object* v_head_817_, lean_object* v_a_818_, lean_object* v_a_819_){
_start:
{
lean_object* v_res_820_; 
v_res_820_ = l_List_span_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_compactRelation_spec__0(v_head_817_, v_a_818_, v_a_819_);
lean_dec_ref(v_head_817_);
return v_res_820_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_compactRelation_spec__2(lean_object* v_head_821_, lean_object* v_fst_822_, lean_object* v_a_823_, lean_object* v_a_824_){
_start:
{
if (lean_obj_tag(v_a_823_) == 0)
{
lean_object* v___x_825_; 
lean_dec_ref(v_head_821_);
v___x_825_ = l_List_reverse___redArg(v_a_824_);
return v___x_825_;
}
else
{
lean_object* v_head_826_; lean_object* v_tail_827_; lean_object* v___x_829_; uint8_t v_isShared_830_; uint8_t v_isSharedCheck_845_; 
v_head_826_ = lean_ctor_get(v_a_823_, 0);
v_tail_827_ = lean_ctor_get(v_a_823_, 1);
v_isSharedCheck_845_ = !lean_is_exclusive(v_a_823_);
if (v_isSharedCheck_845_ == 0)
{
v___x_829_ = v_a_823_;
v_isShared_830_ = v_isSharedCheck_845_;
goto v_resetjp_828_;
}
else
{
lean_inc(v_tail_827_);
lean_inc(v_head_826_);
lean_dec(v_a_823_);
v___x_829_ = lean_box(0);
v_isShared_830_ = v_isSharedCheck_845_;
goto v_resetjp_828_;
}
v_resetjp_828_:
{
lean_object* v_fst_831_; lean_object* v_snd_832_; lean_object* v___x_834_; uint8_t v_isShared_835_; uint8_t v_isSharedCheck_844_; 
v_fst_831_ = lean_ctor_get(v_head_826_, 0);
v_snd_832_ = lean_ctor_get(v_head_826_, 1);
v_isSharedCheck_844_ = !lean_is_exclusive(v_head_826_);
if (v_isSharedCheck_844_ == 0)
{
v___x_834_ = v_head_826_;
v_isShared_835_ = v_isSharedCheck_844_;
goto v_resetjp_833_;
}
else
{
lean_inc(v_snd_832_);
lean_inc(v_fst_831_);
lean_dec(v_head_826_);
v___x_834_ = lean_box(0);
v_isShared_835_ = v_isSharedCheck_844_;
goto v_resetjp_833_;
}
v_resetjp_833_:
{
lean_object* v___x_836_; lean_object* v___x_838_; 
lean_inc_ref(v_head_821_);
v___x_836_ = l_Lean_Expr_replaceFVar(v_snd_832_, v_head_821_, v_fst_822_);
lean_dec(v_snd_832_);
if (v_isShared_835_ == 0)
{
lean_ctor_set(v___x_834_, 1, v___x_836_);
v___x_838_ = v___x_834_;
goto v_reusejp_837_;
}
else
{
lean_object* v_reuseFailAlloc_843_; 
v_reuseFailAlloc_843_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_843_, 0, v_fst_831_);
lean_ctor_set(v_reuseFailAlloc_843_, 1, v___x_836_);
v___x_838_ = v_reuseFailAlloc_843_;
goto v_reusejp_837_;
}
v_reusejp_837_:
{
lean_object* v___x_840_; 
if (v_isShared_830_ == 0)
{
lean_ctor_set(v___x_829_, 1, v_a_824_);
lean_ctor_set(v___x_829_, 0, v___x_838_);
v___x_840_ = v___x_829_;
goto v_reusejp_839_;
}
else
{
lean_object* v_reuseFailAlloc_842_; 
v_reuseFailAlloc_842_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_842_, 0, v___x_838_);
lean_ctor_set(v_reuseFailAlloc_842_, 1, v_a_824_);
v___x_840_ = v_reuseFailAlloc_842_;
goto v_reusejp_839_;
}
v_reusejp_839_:
{
v_a_823_ = v_tail_827_;
v_a_824_ = v___x_840_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_compactRelation_spec__2___boxed(lean_object* v_head_846_, lean_object* v_fst_847_, lean_object* v_a_848_, lean_object* v_a_849_){
_start:
{
lean_object* v_res_850_; 
v_res_850_ = l_List_mapTR_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_compactRelation_spec__2(v_head_846_, v_fst_847_, v_a_848_, v_a_849_);
lean_dec_ref(v_fst_847_);
return v_res_850_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_compactRelation_spec__1(lean_object* v_head_851_, lean_object* v_fst_852_, lean_object* v_a_853_, lean_object* v_a_854_){
_start:
{
if (lean_obj_tag(v_a_853_) == 0)
{
lean_object* v___x_855_; 
lean_dec_ref(v_head_851_);
v___x_855_ = l_List_reverse___redArg(v_a_854_);
return v___x_855_;
}
else
{
lean_object* v_head_856_; lean_object* v_tail_857_; lean_object* v___x_859_; uint8_t v_isShared_860_; uint8_t v_isSharedCheck_866_; 
v_head_856_ = lean_ctor_get(v_a_853_, 0);
v_tail_857_ = lean_ctor_get(v_a_853_, 1);
v_isSharedCheck_866_ = !lean_is_exclusive(v_a_853_);
if (v_isSharedCheck_866_ == 0)
{
v___x_859_ = v_a_853_;
v_isShared_860_ = v_isSharedCheck_866_;
goto v_resetjp_858_;
}
else
{
lean_inc(v_tail_857_);
lean_inc(v_head_856_);
lean_dec(v_a_853_);
v___x_859_ = lean_box(0);
v_isShared_860_ = v_isSharedCheck_866_;
goto v_resetjp_858_;
}
v_resetjp_858_:
{
lean_object* v___x_861_; lean_object* v___x_863_; 
lean_inc_ref(v_head_851_);
v___x_861_ = l_Lean_Expr_replaceFVar(v_head_856_, v_head_851_, v_fst_852_);
lean_dec(v_head_856_);
if (v_isShared_860_ == 0)
{
lean_ctor_set(v___x_859_, 1, v_a_854_);
lean_ctor_set(v___x_859_, 0, v___x_861_);
v___x_863_ = v___x_859_;
goto v_reusejp_862_;
}
else
{
lean_object* v_reuseFailAlloc_865_; 
v_reuseFailAlloc_865_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_865_, 0, v___x_861_);
lean_ctor_set(v_reuseFailAlloc_865_, 1, v_a_854_);
v___x_863_ = v_reuseFailAlloc_865_;
goto v_reusejp_862_;
}
v_reusejp_862_:
{
v_a_853_ = v_tail_857_;
v_a_854_ = v___x_863_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_compactRelation_spec__1___boxed(lean_object* v_head_867_, lean_object* v_fst_868_, lean_object* v_a_869_, lean_object* v_a_870_){
_start:
{
lean_object* v_res_871_; 
v_res_871_ = l_List_mapTR_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_compactRelation_spec__1(v_head_867_, v_fst_868_, v_a_869_, v_a_870_);
lean_dec_ref(v_fst_868_);
return v_res_871_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_compactRelation(lean_object* v_x_873_, lean_object* v_x_874_){
_start:
{
if (lean_obj_tag(v_x_873_) == 0)
{
lean_object* v___f_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; 
v___f_875_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_compactRelation___closed__0));
v___x_876_ = lean_box(0);
v___x_877_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_877_, 0, v_x_874_);
lean_ctor_set(v___x_877_, 1, v___f_875_);
v___x_878_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_878_, 0, v___x_876_);
lean_ctor_set(v___x_878_, 1, v___x_877_);
return v___x_878_;
}
else
{
lean_object* v_head_879_; lean_object* v_tail_880_; lean_object* v___x_882_; uint8_t v_isShared_883_; uint8_t v_isSharedCheck_937_; 
v_head_879_ = lean_ctor_get(v_x_873_, 0);
v_tail_880_ = lean_ctor_get(v_x_873_, 1);
v_isSharedCheck_937_ = !lean_is_exclusive(v_x_873_);
if (v_isSharedCheck_937_ == 0)
{
v___x_882_ = v_x_873_;
v_isShared_883_ = v_isSharedCheck_937_;
goto v_resetjp_881_;
}
else
{
lean_inc(v_tail_880_);
lean_inc(v_head_879_);
lean_dec(v_x_873_);
v___x_882_ = lean_box(0);
v_isShared_883_ = v_isSharedCheck_937_;
goto v_resetjp_881_;
}
v_resetjp_881_:
{
lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v_snd_886_; 
v___x_884_ = lean_box(0);
lean_inc(v_x_874_);
v___x_885_ = l_List_span_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_compactRelation_spec__0(v_head_879_, v_x_874_, v___x_884_);
v_snd_886_ = lean_ctor_get(v___x_885_, 1);
lean_inc(v_snd_886_);
if (lean_obj_tag(v_snd_886_) == 0)
{
lean_object* v___x_887_; lean_object* v_fst_888_; lean_object* v_snd_889_; lean_object* v___x_891_; uint8_t v_isShared_892_; uint8_t v_isSharedCheck_900_; 
lean_dec_ref(v___x_885_);
v___x_887_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_compactRelation(v_tail_880_, v_x_874_);
v_fst_888_ = lean_ctor_get(v___x_887_, 0);
v_snd_889_ = lean_ctor_get(v___x_887_, 1);
v_isSharedCheck_900_ = !lean_is_exclusive(v___x_887_);
if (v_isSharedCheck_900_ == 0)
{
v___x_891_ = v___x_887_;
v_isShared_892_ = v_isSharedCheck_900_;
goto v_resetjp_890_;
}
else
{
lean_inc(v_snd_889_);
lean_inc(v_fst_888_);
lean_dec(v___x_887_);
v___x_891_ = lean_box(0);
v_isShared_892_ = v_isSharedCheck_900_;
goto v_resetjp_890_;
}
v_resetjp_890_:
{
lean_object* v___x_893_; lean_object* v___x_895_; 
v___x_893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_893_, 0, v_head_879_);
if (v_isShared_883_ == 0)
{
lean_ctor_set(v___x_882_, 1, v_fst_888_);
lean_ctor_set(v___x_882_, 0, v___x_893_);
v___x_895_ = v___x_882_;
goto v_reusejp_894_;
}
else
{
lean_object* v_reuseFailAlloc_899_; 
v_reuseFailAlloc_899_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_899_, 0, v___x_893_);
lean_ctor_set(v_reuseFailAlloc_899_, 1, v_fst_888_);
v___x_895_ = v_reuseFailAlloc_899_;
goto v_reusejp_894_;
}
v_reusejp_894_:
{
lean_object* v___x_897_; 
if (v_isShared_892_ == 0)
{
lean_ctor_set(v___x_891_, 0, v___x_895_);
v___x_897_ = v___x_891_;
goto v_reusejp_896_;
}
else
{
lean_object* v_reuseFailAlloc_898_; 
v_reuseFailAlloc_898_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_898_, 0, v___x_895_);
lean_ctor_set(v_reuseFailAlloc_898_, 1, v_snd_889_);
v___x_897_ = v_reuseFailAlloc_898_;
goto v_reusejp_896_;
}
v_reusejp_896_:
{
return v___x_897_;
}
}
}
}
else
{
lean_object* v_head_901_; lean_object* v_fst_902_; lean_object* v_tail_903_; lean_object* v___x_905_; uint8_t v_isShared_906_; uint8_t v_isSharedCheck_935_; 
lean_del_object(v___x_882_);
lean_dec(v_x_874_);
v_head_901_ = lean_ctor_get(v_snd_886_, 0);
lean_inc(v_head_901_);
v_fst_902_ = lean_ctor_get(v___x_885_, 0);
lean_inc(v_fst_902_);
lean_dec_ref(v___x_885_);
v_tail_903_ = lean_ctor_get(v_snd_886_, 1);
v_isSharedCheck_935_ = !lean_is_exclusive(v_snd_886_);
if (v_isSharedCheck_935_ == 0)
{
lean_object* v_unused_936_; 
v_unused_936_ = lean_ctor_get(v_snd_886_, 0);
lean_dec(v_unused_936_);
v___x_905_ = v_snd_886_;
v_isShared_906_ = v_isSharedCheck_935_;
goto v_resetjp_904_;
}
else
{
lean_inc(v_tail_903_);
lean_dec(v_snd_886_);
v___x_905_ = lean_box(0);
v_isShared_906_ = v_isSharedCheck_935_;
goto v_resetjp_904_;
}
v_resetjp_904_:
{
lean_object* v_fst_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v_snd_912_; lean_object* v_fst_913_; lean_object* v___x_915_; uint8_t v_isShared_916_; uint8_t v_isSharedCheck_934_; 
v_fst_907_ = lean_ctor_get(v_head_901_, 0);
lean_inc(v_fst_907_);
lean_dec(v_head_901_);
lean_inc_n(v_head_879_, 2);
v___x_908_ = l_List_mapTR_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_compactRelation_spec__1(v_head_879_, v_fst_907_, v_tail_880_, v___x_884_);
v___x_909_ = l_List_appendTR___redArg(v_fst_902_, v_tail_903_);
v___x_910_ = l_List_mapTR_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_compactRelation_spec__2(v_head_879_, v_fst_907_, v___x_909_, v___x_884_);
v___x_911_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_compactRelation(v___x_908_, v___x_910_);
v_snd_912_ = lean_ctor_get(v___x_911_, 1);
v_fst_913_ = lean_ctor_get(v___x_911_, 0);
v_isSharedCheck_934_ = !lean_is_exclusive(v___x_911_);
if (v_isSharedCheck_934_ == 0)
{
v___x_915_ = v___x_911_;
v_isShared_916_ = v_isSharedCheck_934_;
goto v_resetjp_914_;
}
else
{
lean_inc(v_snd_912_);
lean_inc(v_fst_913_);
lean_dec(v___x_911_);
v___x_915_ = lean_box(0);
v_isShared_916_ = v_isSharedCheck_934_;
goto v_resetjp_914_;
}
v_resetjp_914_:
{
lean_object* v_fst_917_; lean_object* v_snd_918_; lean_object* v___x_920_; uint8_t v_isShared_921_; uint8_t v_isSharedCheck_933_; 
v_fst_917_ = lean_ctor_get(v_snd_912_, 0);
v_snd_918_ = lean_ctor_get(v_snd_912_, 1);
v_isSharedCheck_933_ = !lean_is_exclusive(v_snd_912_);
if (v_isSharedCheck_933_ == 0)
{
v___x_920_ = v_snd_912_;
v_isShared_921_ = v_isSharedCheck_933_;
goto v_resetjp_919_;
}
else
{
lean_inc(v_snd_918_);
lean_inc(v_fst_917_);
lean_dec(v_snd_912_);
v___x_920_ = lean_box(0);
v_isShared_921_ = v_isSharedCheck_933_;
goto v_resetjp_919_;
}
v_resetjp_919_:
{
lean_object* v___f_922_; lean_object* v___x_923_; lean_object* v___x_925_; 
v___f_922_ = lean_alloc_closure((void*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_compactRelation___lam__1___boxed), 4, 3);
lean_closure_set(v___f_922_, 0, v_snd_918_);
lean_closure_set(v___f_922_, 1, v_head_879_);
lean_closure_set(v___f_922_, 2, v_fst_907_);
v___x_923_ = lean_box(0);
if (v_isShared_906_ == 0)
{
lean_ctor_set(v___x_905_, 1, v_fst_913_);
lean_ctor_set(v___x_905_, 0, v___x_923_);
v___x_925_ = v___x_905_;
goto v_reusejp_924_;
}
else
{
lean_object* v_reuseFailAlloc_932_; 
v_reuseFailAlloc_932_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_932_, 0, v___x_923_);
lean_ctor_set(v_reuseFailAlloc_932_, 1, v_fst_913_);
v___x_925_ = v_reuseFailAlloc_932_;
goto v_reusejp_924_;
}
v_reusejp_924_:
{
lean_object* v___x_927_; 
if (v_isShared_921_ == 0)
{
lean_ctor_set(v___x_920_, 1, v___f_922_);
v___x_927_ = v___x_920_;
goto v_reusejp_926_;
}
else
{
lean_object* v_reuseFailAlloc_931_; 
v_reuseFailAlloc_931_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_931_, 0, v_fst_917_);
lean_ctor_set(v_reuseFailAlloc_931_, 1, v___f_922_);
v___x_927_ = v_reuseFailAlloc_931_;
goto v_reusejp_926_;
}
v_reusejp_926_:
{
lean_object* v___x_929_; 
if (v_isShared_916_ == 0)
{
lean_ctor_set(v___x_915_, 1, v___x_927_);
lean_ctor_set(v___x_915_, 0, v___x_925_);
v___x_929_ = v___x_915_;
goto v_reusejp_928_;
}
else
{
lean_object* v_reuseFailAlloc_930_; 
v_reuseFailAlloc_930_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_930_, 0, v___x_925_);
lean_ctor_set(v_reuseFailAlloc_930_, 1, v___x_927_);
v___x_929_ = v_reuseFailAlloc_930_;
goto v_reusejp_928_;
}
v_reusejp_928_:
{
return v___x_929_;
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
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_updateLambdaBinderInfoD_x21_spec__0(lean_object* v_msg_938_){
_start:
{
lean_object* v___x_939_; lean_object* v___x_940_; 
v___x_939_ = l_Lean_instInhabitedExpr;
v___x_940_ = lean_panic_fn_borrowed(v___x_939_, v_msg_938_);
return v___x_940_;
}
}
static lean_object* _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_updateLambdaBinderInfoD_x21___closed__3(void){
_start:
{
lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; 
v___x_944_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_updateLambdaBinderInfoD_x21___closed__2));
v___x_945_ = lean_unsigned_to_nat(19u);
v___x_946_ = lean_unsigned_to_nat(97u);
v___x_947_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_updateLambdaBinderInfoD_x21___closed__1));
v___x_948_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_updateLambdaBinderInfoD_x21___closed__0));
v___x_949_ = l_mkPanicMessageWithDecl(v___x_948_, v___x_947_, v___x_946_, v___x_945_, v___x_944_);
return v___x_949_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_updateLambdaBinderInfoD_x21(lean_object* v_e_950_){
_start:
{
if (lean_obj_tag(v_e_950_) == 6)
{
lean_object* v_binderName_951_; lean_object* v_binderType_952_; lean_object* v_body_953_; uint8_t v___x_954_; lean_object* v___x_955_; 
v_binderName_951_ = lean_ctor_get(v_e_950_, 0);
lean_inc(v_binderName_951_);
v_binderType_952_ = lean_ctor_get(v_e_950_, 1);
lean_inc_ref(v_binderType_952_);
v_body_953_ = lean_ctor_get(v_e_950_, 2);
lean_inc_ref(v_body_953_);
lean_dec_ref_known(v_e_950_, 3);
v___x_954_ = 0;
v___x_955_ = l_Lean_Expr_lam___override(v_binderName_951_, v_binderType_952_, v_body_953_, v___x_954_);
return v___x_955_;
}
else
{
lean_object* v___x_956_; lean_object* v___x_957_; 
lean_dec_ref(v_e_950_);
v___x_956_ = lean_obj_once(&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_updateLambdaBinderInfoD_x21___closed__3, &l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_updateLambdaBinderInfoD_x21___closed__3_once, _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_updateLambdaBinderInfoD_x21___closed__3);
v___x_957_ = l_panic___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_updateLambdaBinderInfoD_x21_spec__0(v___x_956_);
return v___x_957_;
}
}
}
static lean_object* _init_l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkExistsList_spec__0___closed__4(void){
_start:
{
lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; 
v___x_964_ = lean_box(0);
v___x_965_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkExistsList_spec__0___closed__3));
v___x_966_ = l_Lean_mkConst(v___x_965_, v___x_964_);
return v___x_966_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkExistsList_spec__0(lean_object* v_x_967_, lean_object* v_x_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_){
_start:
{
if (lean_obj_tag(v_x_968_) == 0)
{
lean_object* v___x_974_; 
v___x_974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_974_, 0, v_x_967_);
return v___x_974_;
}
else
{
lean_object* v_head_975_; lean_object* v_tail_976_; lean_object* v___x_978_; uint8_t v_isShared_979_; uint8_t v_isSharedCheck_1009_; 
v_head_975_ = lean_ctor_get(v_x_968_, 0);
v_tail_976_ = lean_ctor_get(v_x_968_, 1);
v_isSharedCheck_1009_ = !lean_is_exclusive(v_x_968_);
if (v_isSharedCheck_1009_ == 0)
{
v___x_978_ = v_x_968_;
v_isShared_979_ = v_isSharedCheck_1009_;
goto v_resetjp_977_;
}
else
{
lean_inc(v_tail_976_);
lean_inc(v_head_975_);
lean_dec(v_x_968_);
v___x_978_ = lean_box(0);
v_isShared_979_ = v_isSharedCheck_1009_;
goto v_resetjp_977_;
}
v_resetjp_977_:
{
lean_object* v___x_980_; 
lean_inc(v___y_972_);
lean_inc_ref(v___y_971_);
lean_inc(v___y_970_);
lean_inc_ref(v___y_969_);
lean_inc(v_head_975_);
v___x_980_ = lean_infer_type(v_head_975_, v___y_969_, v___y_970_, v___y_971_, v___y_972_);
if (lean_obj_tag(v___x_980_) == 0)
{
lean_object* v_a_981_; lean_object* v___x_982_; 
v_a_981_ = lean_ctor_get(v___x_980_, 0);
lean_inc_n(v_a_981_, 2);
lean_dec_ref_known(v___x_980_, 1);
lean_inc(v___y_972_);
lean_inc_ref(v___y_971_);
lean_inc(v___y_970_);
lean_inc_ref(v___y_969_);
v___x_982_ = lean_infer_type(v_a_981_, v___y_969_, v___y_970_, v___y_971_, v___y_972_);
if (lean_obj_tag(v___x_982_) == 0)
{
lean_object* v_a_983_; lean_object* v___x_984_; uint8_t v___x_1003_; 
v_a_983_ = lean_ctor_get(v___x_982_, 0);
lean_inc(v_a_983_);
lean_dec_ref_known(v___x_982_, 1);
v___x_984_ = l_Lean_Expr_sortLevel_x21(v_a_983_);
lean_dec(v_a_983_);
lean_inc(v_head_975_);
v___x_1003_ = l_Lean_Expr_occurs(v_head_975_, v_x_967_);
if (v___x_1003_ == 0)
{
lean_object* v___x_1004_; uint8_t v___x_1005_; 
v___x_1004_ = lean_box(0);
v___x_1005_ = lean_level_eq(v___x_984_, v___x_1004_);
if (v___x_1005_ == 0)
{
goto v___jp_985_;
}
else
{
lean_object* v___x_1006_; lean_object* v___x_1007_; 
lean_dec(v___x_984_);
lean_del_object(v___x_978_);
lean_dec(v_head_975_);
v___x_1006_ = lean_obj_once(&l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkExistsList_spec__0___closed__4, &l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkExistsList_spec__0___closed__4_once, _init_l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkExistsList_spec__0___closed__4);
v___x_1007_ = l_Lean_mkAppB(v___x_1006_, v_a_981_, v_x_967_);
v_x_967_ = v___x_1007_;
v_x_968_ = v_tail_976_;
goto _start;
}
}
else
{
goto v___jp_985_;
}
v___jp_985_:
{
uint8_t v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; uint8_t v___x_990_; uint8_t v___x_991_; lean_object* v___x_992_; 
v___x_986_ = 1;
v___x_987_ = lean_unsigned_to_nat(1u);
v___x_988_ = lean_mk_empty_array_with_capacity(v___x_987_);
v___x_989_ = lean_array_push(v___x_988_, v_head_975_);
v___x_990_ = 0;
v___x_991_ = 1;
v___x_992_ = l_Lean_Meta_mkLambdaFVars(v___x_989_, v_x_967_, v___x_990_, v___x_986_, v___x_990_, v___x_986_, v___x_991_, v___y_969_, v___y_970_, v___y_971_, v___y_972_);
lean_dec_ref(v___x_989_);
if (lean_obj_tag(v___x_992_) == 0)
{
lean_object* v_a_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_997_; 
v_a_993_ = lean_ctor_get(v___x_992_, 0);
lean_inc(v_a_993_);
lean_dec_ref_known(v___x_992_, 1);
v___x_994_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkExistsList_spec__0___closed__1));
v___x_995_ = lean_box(0);
if (v_isShared_979_ == 0)
{
lean_ctor_set(v___x_978_, 1, v___x_995_);
lean_ctor_set(v___x_978_, 0, v___x_984_);
v___x_997_ = v___x_978_;
goto v_reusejp_996_;
}
else
{
lean_object* v_reuseFailAlloc_1002_; 
v_reuseFailAlloc_1002_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1002_, 0, v___x_984_);
lean_ctor_set(v_reuseFailAlloc_1002_, 1, v___x_995_);
v___x_997_ = v_reuseFailAlloc_1002_;
goto v_reusejp_996_;
}
v_reusejp_996_:
{
lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; 
v___x_998_ = l_Lean_Expr_const___override(v___x_994_, v___x_997_);
v___x_999_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_updateLambdaBinderInfoD_x21(v_a_993_);
v___x_1000_ = l_Lean_mkAppB(v___x_998_, v_a_981_, v___x_999_);
v_x_967_ = v___x_1000_;
v_x_968_ = v_tail_976_;
goto _start;
}
}
else
{
lean_dec(v___x_984_);
lean_dec(v_a_981_);
lean_del_object(v___x_978_);
lean_dec(v_tail_976_);
return v___x_992_;
}
}
}
else
{
lean_dec(v_a_981_);
lean_del_object(v___x_978_);
lean_dec(v_tail_976_);
lean_dec(v_head_975_);
lean_dec_ref(v_x_967_);
return v___x_982_;
}
}
else
{
lean_del_object(v___x_978_);
lean_dec(v_tail_976_);
lean_dec(v_head_975_);
lean_dec_ref(v_x_967_);
return v___x_980_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkExistsList_spec__0___boxed(lean_object* v_x_1010_, lean_object* v_x_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_){
_start:
{
lean_object* v_res_1017_; 
v_res_1017_ = l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkExistsList_spec__0(v_x_1010_, v_x_1011_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_);
lean_dec(v___y_1015_);
lean_dec_ref(v___y_1014_);
lean_dec(v___y_1013_);
lean_dec_ref(v___y_1012_);
return v_res_1017_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkExistsList(lean_object* v_args_1018_, lean_object* v_inner_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_, lean_object* v_a_1022_, lean_object* v_a_1023_){
_start:
{
lean_object* v___x_1025_; lean_object* v___x_1026_; 
v___x_1025_ = l_List_reverse___redArg(v_args_1018_);
v___x_1026_ = l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkExistsList_spec__0(v_inner_1019_, v___x_1025_, v_a_1020_, v_a_1021_, v_a_1022_, v_a_1023_);
return v___x_1026_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkExistsList___boxed(lean_object* v_args_1027_, lean_object* v_inner_1028_, lean_object* v_a_1029_, lean_object* v_a_1030_, lean_object* v_a_1031_, lean_object* v_a_1032_, lean_object* v_a_1033_){
_start:
{
lean_object* v_res_1034_; 
v_res_1034_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkExistsList(v_args_1027_, v_inner_1028_, v_a_1029_, v_a_1030_, v_a_1031_, v_a_1032_);
lean_dec(v_a_1032_);
lean_dec_ref(v_a_1031_);
lean_dec(v_a_1030_);
lean_dec_ref(v_a_1029_);
return v_res_1034_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkOpList(lean_object* v_op_1035_, lean_object* v_empty_1036_, lean_object* v_x_1037_){
_start:
{
if (lean_obj_tag(v_x_1037_) == 0)
{
lean_dec_ref(v_op_1035_);
lean_inc_ref(v_empty_1036_);
return v_empty_1036_;
}
else
{
lean_object* v_tail_1038_; 
v_tail_1038_ = lean_ctor_get(v_x_1037_, 1);
if (lean_obj_tag(v_tail_1038_) == 0)
{
lean_object* v_head_1039_; 
lean_dec_ref(v_op_1035_);
v_head_1039_ = lean_ctor_get(v_x_1037_, 0);
lean_inc(v_head_1039_);
lean_dec_ref_known(v_x_1037_, 2);
return v_head_1039_;
}
else
{
lean_object* v_head_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; 
lean_inc(v_tail_1038_);
v_head_1040_ = lean_ctor_get(v_x_1037_, 0);
lean_inc(v_head_1040_);
lean_dec_ref_known(v_x_1037_, 2);
lean_inc_ref(v_op_1035_);
v___x_1041_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkOpList(v_op_1035_, v_empty_1036_, v_tail_1038_);
v___x_1042_ = l_Lean_mkAppB(v_op_1035_, v_head_1040_, v___x_1041_);
return v___x_1042_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkOpList___boxed(lean_object* v_op_1043_, lean_object* v_empty_1044_, lean_object* v_x_1045_){
_start:
{
lean_object* v_res_1046_; 
v_res_1046_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkOpList(v_op_1043_, v_empty_1044_, v_x_1045_);
lean_dec_ref(v_empty_1044_);
return v_res_1046_;
}
}
static lean_object* _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkAndList___closed__2(void){
_start:
{
lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; 
v___x_1050_ = lean_box(0);
v___x_1051_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkAndList___closed__1));
v___x_1052_ = l_Lean_mkConst(v___x_1051_, v___x_1050_);
return v___x_1052_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkAndList(lean_object* v_a_1053_){
_start:
{
lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; 
v___x_1054_ = lean_obj_once(&l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkExistsList_spec__0___closed__4, &l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkExistsList_spec__0___closed__4_once, _init_l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkExistsList_spec__0___closed__4);
v___x_1055_ = lean_obj_once(&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkAndList___closed__2, &l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkAndList___closed__2_once, _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkAndList___closed__2);
v___x_1056_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkOpList(v___x_1054_, v___x_1055_, v_a_1053_);
return v___x_1056_;
}
}
static lean_object* _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkOrList___closed__2(void){
_start:
{
lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; 
v___x_1060_ = lean_box(0);
v___x_1061_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkOrList___closed__1));
v___x_1062_ = l_Lean_mkConst(v___x_1061_, v___x_1060_);
return v___x_1062_;
}
}
static lean_object* _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkOrList___closed__5(void){
_start:
{
lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; 
v___x_1066_ = lean_box(0);
v___x_1067_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkOrList___closed__4));
v___x_1068_ = l_Lean_mkConst(v___x_1067_, v___x_1066_);
return v___x_1068_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkOrList(lean_object* v_a_1069_){
_start:
{
lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; 
v___x_1070_ = lean_obj_once(&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkOrList___closed__2, &l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkOrList___closed__2_once, _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkOrList___closed__2);
v___x_1071_ = lean_obj_once(&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkOrList___closed__5, &l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkOrList___closed__5_once, _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkOrList___closed__5);
v___x_1072_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkOpList(v___x_1070_, v___x_1071_, v_a_1069_);
return v___x_1072_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_List_init___redArg(lean_object* v_x_1073_){
_start:
{
if (lean_obj_tag(v_x_1073_) == 0)
{
return v_x_1073_;
}
else
{
lean_object* v_tail_1074_; 
v_tail_1074_ = lean_ctor_get(v_x_1073_, 1);
lean_inc(v_tail_1074_);
if (lean_obj_tag(v_tail_1074_) == 0)
{
lean_dec_ref_known(v_x_1073_, 2);
return v_tail_1074_;
}
else
{
lean_object* v_head_1075_; lean_object* v___x_1077_; uint8_t v_isShared_1078_; uint8_t v_isSharedCheck_1083_; 
v_head_1075_ = lean_ctor_get(v_x_1073_, 0);
v_isSharedCheck_1083_ = !lean_is_exclusive(v_x_1073_);
if (v_isSharedCheck_1083_ == 0)
{
lean_object* v_unused_1084_; 
v_unused_1084_ = lean_ctor_get(v_x_1073_, 1);
lean_dec(v_unused_1084_);
v___x_1077_ = v_x_1073_;
v_isShared_1078_ = v_isSharedCheck_1083_;
goto v_resetjp_1076_;
}
else
{
lean_inc(v_head_1075_);
lean_dec(v_x_1073_);
v___x_1077_ = lean_box(0);
v_isShared_1078_ = v_isSharedCheck_1083_;
goto v_resetjp_1076_;
}
v_resetjp_1076_:
{
lean_object* v___x_1079_; lean_object* v___x_1081_; 
v___x_1079_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_List_init___redArg(v_tail_1074_);
if (v_isShared_1078_ == 0)
{
lean_ctor_set(v___x_1077_, 1, v___x_1079_);
v___x_1081_ = v___x_1077_;
goto v_reusejp_1080_;
}
else
{
lean_object* v_reuseFailAlloc_1082_; 
v_reuseFailAlloc_1082_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1082_, 0, v_head_1075_);
lean_ctor_set(v_reuseFailAlloc_1082_, 1, v___x_1079_);
v___x_1081_ = v_reuseFailAlloc_1082_;
goto v_reusejp_1080_;
}
v_reusejp_1080_:
{
return v___x_1081_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_List_init(lean_object* v_00_u03b1_1085_, lean_object* v_x_1086_){
_start:
{
lean_object* v___x_1087_; 
v___x_1087_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_List_init___redArg(v_x_1086_);
return v___x_1087_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__4___redArg___lam__0(lean_object* v_k_1088_, lean_object* v_b_1089_, lean_object* v_c_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_){
_start:
{
lean_object* v___x_1096_; 
lean_inc(v___y_1094_);
lean_inc_ref(v___y_1093_);
lean_inc(v___y_1092_);
lean_inc_ref(v___y_1091_);
v___x_1096_ = lean_apply_7(v_k_1088_, v_b_1089_, v_c_1090_, v___y_1091_, v___y_1092_, v___y_1093_, v___y_1094_, lean_box(0));
return v___x_1096_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__4___redArg___lam__0___boxed(lean_object* v_k_1097_, lean_object* v_b_1098_, lean_object* v_c_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_){
_start:
{
lean_object* v_res_1105_; 
v_res_1105_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__4___redArg___lam__0(v_k_1097_, v_b_1098_, v_c_1099_, v___y_1100_, v___y_1101_, v___y_1102_, v___y_1103_);
lean_dec(v___y_1103_);
lean_dec_ref(v___y_1102_);
lean_dec(v___y_1101_);
lean_dec_ref(v___y_1100_);
return v_res_1105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__4___redArg(lean_object* v_type_1106_, lean_object* v_maxFVars_x3f_1107_, lean_object* v_k_1108_, uint8_t v_cleanupAnnotations_1109_, uint8_t v_whnfType_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_){
_start:
{
lean_object* v___f_1116_; lean_object* v___x_1117_; 
v___f_1116_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__4___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1116_, 0, v_k_1108_);
v___x_1117_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_1106_, v_maxFVars_x3f_1107_, v___f_1116_, v_cleanupAnnotations_1109_, v_whnfType_1110_, v___y_1111_, v___y_1112_, v___y_1113_, v___y_1114_);
if (lean_obj_tag(v___x_1117_) == 0)
{
lean_object* v_a_1118_; lean_object* v___x_1120_; uint8_t v_isShared_1121_; uint8_t v_isSharedCheck_1125_; 
v_a_1118_ = lean_ctor_get(v___x_1117_, 0);
v_isSharedCheck_1125_ = !lean_is_exclusive(v___x_1117_);
if (v_isSharedCheck_1125_ == 0)
{
v___x_1120_ = v___x_1117_;
v_isShared_1121_ = v_isSharedCheck_1125_;
goto v_resetjp_1119_;
}
else
{
lean_inc(v_a_1118_);
lean_dec(v___x_1117_);
v___x_1120_ = lean_box(0);
v_isShared_1121_ = v_isSharedCheck_1125_;
goto v_resetjp_1119_;
}
v_resetjp_1119_:
{
lean_object* v___x_1123_; 
if (v_isShared_1121_ == 0)
{
v___x_1123_ = v___x_1120_;
goto v_reusejp_1122_;
}
else
{
lean_object* v_reuseFailAlloc_1124_; 
v_reuseFailAlloc_1124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1124_, 0, v_a_1118_);
v___x_1123_ = v_reuseFailAlloc_1124_;
goto v_reusejp_1122_;
}
v_reusejp_1122_:
{
return v___x_1123_;
}
}
}
else
{
lean_object* v_a_1126_; lean_object* v___x_1128_; uint8_t v_isShared_1129_; uint8_t v_isSharedCheck_1133_; 
v_a_1126_ = lean_ctor_get(v___x_1117_, 0);
v_isSharedCheck_1133_ = !lean_is_exclusive(v___x_1117_);
if (v_isSharedCheck_1133_ == 0)
{
v___x_1128_ = v___x_1117_;
v_isShared_1129_ = v_isSharedCheck_1133_;
goto v_resetjp_1127_;
}
else
{
lean_inc(v_a_1126_);
lean_dec(v___x_1117_);
v___x_1128_ = lean_box(0);
v_isShared_1129_ = v_isSharedCheck_1133_;
goto v_resetjp_1127_;
}
v_resetjp_1127_:
{
lean_object* v___x_1131_; 
if (v_isShared_1129_ == 0)
{
v___x_1131_ = v___x_1128_;
goto v_reusejp_1130_;
}
else
{
lean_object* v_reuseFailAlloc_1132_; 
v_reuseFailAlloc_1132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1132_, 0, v_a_1126_);
v___x_1131_ = v_reuseFailAlloc_1132_;
goto v_reusejp_1130_;
}
v_reusejp_1130_:
{
return v___x_1131_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__4___redArg___boxed(lean_object* v_type_1134_, lean_object* v_maxFVars_x3f_1135_, lean_object* v_k_1136_, lean_object* v_cleanupAnnotations_1137_, lean_object* v_whnfType_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1144_; uint8_t v_whnfType_boxed_1145_; lean_object* v_res_1146_; 
v_cleanupAnnotations_boxed_1144_ = lean_unbox(v_cleanupAnnotations_1137_);
v_whnfType_boxed_1145_ = lean_unbox(v_whnfType_1138_);
v_res_1146_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__4___redArg(v_type_1134_, v_maxFVars_x3f_1135_, v_k_1136_, v_cleanupAnnotations_boxed_1144_, v_whnfType_boxed_1145_, v___y_1139_, v___y_1140_, v___y_1141_, v___y_1142_);
lean_dec(v___y_1142_);
lean_dec_ref(v___y_1141_);
lean_dec(v___y_1140_);
lean_dec_ref(v___y_1139_);
return v_res_1146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__4(lean_object* v_00_u03b1_1147_, lean_object* v_type_1148_, lean_object* v_maxFVars_x3f_1149_, lean_object* v_k_1150_, uint8_t v_cleanupAnnotations_1151_, uint8_t v_whnfType_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_){
_start:
{
lean_object* v___x_1158_; 
v___x_1158_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__4___redArg(v_type_1148_, v_maxFVars_x3f_1149_, v_k_1150_, v_cleanupAnnotations_1151_, v_whnfType_1152_, v___y_1153_, v___y_1154_, v___y_1155_, v___y_1156_);
return v___x_1158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__4___boxed(lean_object* v_00_u03b1_1159_, lean_object* v_type_1160_, lean_object* v_maxFVars_x3f_1161_, lean_object* v_k_1162_, lean_object* v_cleanupAnnotations_1163_, lean_object* v_whnfType_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1170_; uint8_t v_whnfType_boxed_1171_; lean_object* v_res_1172_; 
v_cleanupAnnotations_boxed_1170_ = lean_unbox(v_cleanupAnnotations_1163_);
v_whnfType_boxed_1171_ = lean_unbox(v_whnfType_1164_);
v_res_1172_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__4(v_00_u03b1_1159_, v_type_1160_, v_maxFVars_x3f_1161_, v_k_1162_, v_cleanupAnnotations_boxed_1170_, v_whnfType_boxed_1171_, v___y_1165_, v___y_1166_, v___y_1167_, v___y_1168_);
lean_dec(v___y_1168_);
lean_dec_ref(v___y_1167_);
lean_dec(v___y_1166_);
lean_dec_ref(v___y_1165_);
return v_res_1172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__5___redArg(lean_object* v_type_1173_, lean_object* v_k_1174_, uint8_t v_cleanupAnnotations_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_){
_start:
{
lean_object* v___f_1181_; uint8_t v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; 
v___f_1181_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__4___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1181_, 0, v_k_1174_);
v___x_1182_ = 0;
v___x_1183_ = lean_box(0);
v___x_1184_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_1182_, v___x_1183_, v_type_1173_, v___f_1181_, v_cleanupAnnotations_1175_, v___x_1182_, v___y_1176_, v___y_1177_, v___y_1178_, v___y_1179_);
if (lean_obj_tag(v___x_1184_) == 0)
{
lean_object* v_a_1185_; lean_object* v___x_1187_; uint8_t v_isShared_1188_; uint8_t v_isSharedCheck_1192_; 
v_a_1185_ = lean_ctor_get(v___x_1184_, 0);
v_isSharedCheck_1192_ = !lean_is_exclusive(v___x_1184_);
if (v_isSharedCheck_1192_ == 0)
{
v___x_1187_ = v___x_1184_;
v_isShared_1188_ = v_isSharedCheck_1192_;
goto v_resetjp_1186_;
}
else
{
lean_inc(v_a_1185_);
lean_dec(v___x_1184_);
v___x_1187_ = lean_box(0);
v_isShared_1188_ = v_isSharedCheck_1192_;
goto v_resetjp_1186_;
}
v_resetjp_1186_:
{
lean_object* v___x_1190_; 
if (v_isShared_1188_ == 0)
{
v___x_1190_ = v___x_1187_;
goto v_reusejp_1189_;
}
else
{
lean_object* v_reuseFailAlloc_1191_; 
v_reuseFailAlloc_1191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1191_, 0, v_a_1185_);
v___x_1190_ = v_reuseFailAlloc_1191_;
goto v_reusejp_1189_;
}
v_reusejp_1189_:
{
return v___x_1190_;
}
}
}
else
{
lean_object* v_a_1193_; lean_object* v___x_1195_; uint8_t v_isShared_1196_; uint8_t v_isSharedCheck_1200_; 
v_a_1193_ = lean_ctor_get(v___x_1184_, 0);
v_isSharedCheck_1200_ = !lean_is_exclusive(v___x_1184_);
if (v_isSharedCheck_1200_ == 0)
{
v___x_1195_ = v___x_1184_;
v_isShared_1196_ = v_isSharedCheck_1200_;
goto v_resetjp_1194_;
}
else
{
lean_inc(v_a_1193_);
lean_dec(v___x_1184_);
v___x_1195_ = lean_box(0);
v_isShared_1196_ = v_isSharedCheck_1200_;
goto v_resetjp_1194_;
}
v_resetjp_1194_:
{
lean_object* v___x_1198_; 
if (v_isShared_1196_ == 0)
{
v___x_1198_ = v___x_1195_;
goto v_reusejp_1197_;
}
else
{
lean_object* v_reuseFailAlloc_1199_; 
v_reuseFailAlloc_1199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1199_, 0, v_a_1193_);
v___x_1198_ = v_reuseFailAlloc_1199_;
goto v_reusejp_1197_;
}
v_reusejp_1197_:
{
return v___x_1198_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__5___redArg___boxed(lean_object* v_type_1201_, lean_object* v_k_1202_, lean_object* v_cleanupAnnotations_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1209_; lean_object* v_res_1210_; 
v_cleanupAnnotations_boxed_1209_ = lean_unbox(v_cleanupAnnotations_1203_);
v_res_1210_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__5___redArg(v_type_1201_, v_k_1202_, v_cleanupAnnotations_boxed_1209_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_);
lean_dec(v___y_1207_);
lean_dec_ref(v___y_1206_);
lean_dec(v___y_1205_);
lean_dec_ref(v___y_1204_);
return v_res_1210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__5(lean_object* v_00_u03b1_1211_, lean_object* v_type_1212_, lean_object* v_k_1213_, uint8_t v_cleanupAnnotations_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_){
_start:
{
lean_object* v___x_1220_; 
v___x_1220_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__5___redArg(v_type_1212_, v_k_1213_, v_cleanupAnnotations_1214_, v___y_1215_, v___y_1216_, v___y_1217_, v___y_1218_);
return v___x_1220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__5___boxed(lean_object* v_00_u03b1_1221_, lean_object* v_type_1222_, lean_object* v_k_1223_, lean_object* v_cleanupAnnotations_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1230_; lean_object* v_res_1231_; 
v_cleanupAnnotations_boxed_1230_ = lean_unbox(v_cleanupAnnotations_1224_);
v_res_1231_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__5(v_00_u03b1_1221_, v_type_1222_, v_k_1223_, v_cleanupAnnotations_boxed_1230_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_);
lean_dec(v___y_1228_);
lean_dec_ref(v___y_1227_);
lean_dec(v___y_1226_);
lean_dec_ref(v___y_1225_);
return v_res_1231_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__0(lean_object* v_params_1232_, lean_object* v_fvars_1233_, lean_object* v_ty_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_){
_start:
{
lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; 
v___x_1240_ = lean_array_mk(v_params_1232_);
v___x_1241_ = l_Lean_Expr_replaceFVars(v_ty_1234_, v_fvars_1233_, v___x_1240_);
lean_dec_ref(v___x_1240_);
v___x_1242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1242_, 0, v___x_1241_);
return v___x_1242_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__0___boxed(lean_object* v_params_1243_, lean_object* v_fvars_1244_, lean_object* v_ty_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_){
_start:
{
lean_object* v_res_1251_; 
v_res_1251_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__0(v_params_1243_, v_fvars_1244_, v_ty_1245_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_);
lean_dec(v___y_1249_);
lean_dec_ref(v___y_1248_);
lean_dec(v___y_1247_);
lean_dec_ref(v___y_1246_);
lean_dec_ref(v_ty_1245_);
lean_dec_ref(v_fvars_1244_);
return v_res_1251_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__1(lean_object* v_fst_1252_, lean_object* v_snd_1253_){
_start:
{
lean_object* v___x_1254_; 
v___x_1254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1254_, 0, v_fst_1252_);
lean_ctor_set(v___x_1254_, 1, v_snd_1253_);
return v___x_1254_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__2(lean_object* v_x_1261_, lean_object* v_x_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_){
_start:
{
if (lean_obj_tag(v_x_1261_) == 0)
{
lean_object* v___x_1268_; lean_object* v___x_1269_; 
v___x_1268_ = l_List_reverse___redArg(v_x_1262_);
v___x_1269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1269_, 0, v___x_1268_);
return v___x_1269_;
}
else
{
lean_object* v_head_1270_; lean_object* v_tail_1271_; lean_object* v___x_1273_; uint8_t v_isShared_1274_; uint8_t v_isSharedCheck_1344_; 
v_head_1270_ = lean_ctor_get(v_x_1261_, 0);
v_tail_1271_ = lean_ctor_get(v_x_1261_, 1);
v_isSharedCheck_1344_ = !lean_is_exclusive(v_x_1261_);
if (v_isSharedCheck_1344_ == 0)
{
v___x_1273_ = v_x_1261_;
v_isShared_1274_ = v_isSharedCheck_1344_;
goto v_resetjp_1272_;
}
else
{
lean_inc(v_tail_1271_);
lean_inc(v_head_1270_);
lean_dec(v_x_1261_);
v___x_1273_ = lean_box(0);
v_isShared_1274_ = v_isSharedCheck_1344_;
goto v_resetjp_1272_;
}
v_resetjp_1272_:
{
lean_object* v_a_1276_; lean_object* v_fst_1281_; lean_object* v_snd_1282_; lean_object* v___x_1284_; uint8_t v_isShared_1285_; uint8_t v_isSharedCheck_1343_; 
v_fst_1281_ = lean_ctor_get(v_head_1270_, 0);
v_snd_1282_ = lean_ctor_get(v_head_1270_, 1);
v_isSharedCheck_1343_ = !lean_is_exclusive(v_head_1270_);
if (v_isSharedCheck_1343_ == 0)
{
v___x_1284_ = v_head_1270_;
v_isShared_1285_ = v_isSharedCheck_1343_;
goto v_resetjp_1283_;
}
else
{
lean_inc(v_snd_1282_);
lean_inc(v_fst_1281_);
lean_dec(v_head_1270_);
v___x_1284_ = lean_box(0);
v_isShared_1285_ = v_isSharedCheck_1343_;
goto v_resetjp_1283_;
}
v___jp_1275_:
{
lean_object* v___x_1278_; 
if (v_isShared_1274_ == 0)
{
lean_ctor_set(v___x_1273_, 1, v_x_1262_);
lean_ctor_set(v___x_1273_, 0, v_a_1276_);
v___x_1278_ = v___x_1273_;
goto v_reusejp_1277_;
}
else
{
lean_object* v_reuseFailAlloc_1280_; 
v_reuseFailAlloc_1280_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1280_, 0, v_a_1276_);
lean_ctor_set(v_reuseFailAlloc_1280_, 1, v_x_1262_);
v___x_1278_ = v_reuseFailAlloc_1280_;
goto v_reusejp_1277_;
}
v_reusejp_1277_:
{
v_x_1261_ = v_tail_1271_;
v_x_1262_ = v___x_1278_;
goto _start;
}
}
v_resetjp_1283_:
{
lean_object* v___x_1286_; lean_object* v___x_1287_; 
v___x_1286_ = l_Lean_Expr_fvarId_x21(v_fst_1281_);
v___x_1287_ = l_Lean_FVarId_getType___redArg(v___x_1286_, v___y_1263_, v___y_1265_, v___y_1266_);
if (lean_obj_tag(v___x_1287_) == 0)
{
lean_object* v_a_1288_; lean_object* v___x_1289_; 
v_a_1288_ = lean_ctor_get(v___x_1287_, 0);
lean_inc(v_a_1288_);
lean_dec_ref_known(v___x_1287_, 1);
lean_inc(v___y_1266_);
lean_inc_ref(v___y_1265_);
lean_inc(v___y_1264_);
lean_inc_ref(v___y_1263_);
lean_inc(v_snd_1282_);
v___x_1289_ = lean_infer_type(v_snd_1282_, v___y_1263_, v___y_1264_, v___y_1265_, v___y_1266_);
if (lean_obj_tag(v___x_1289_) == 0)
{
lean_object* v_a_1290_; lean_object* v___x_1291_; 
v_a_1290_ = lean_ctor_get(v___x_1289_, 0);
lean_inc(v_a_1290_);
lean_dec_ref_known(v___x_1289_, 1);
lean_inc(v___y_1266_);
lean_inc_ref(v___y_1265_);
lean_inc(v___y_1264_);
lean_inc_ref(v___y_1263_);
lean_inc(v_a_1288_);
v___x_1291_ = lean_infer_type(v_a_1288_, v___y_1263_, v___y_1264_, v___y_1265_, v___y_1266_);
if (lean_obj_tag(v___x_1291_) == 0)
{
lean_object* v_a_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; 
v_a_1292_ = lean_ctor_get(v___x_1291_, 0);
lean_inc(v_a_1292_);
lean_dec_ref_known(v___x_1291_, 1);
v___x_1293_ = l_Lean_Expr_sortLevel_x21(v_a_1292_);
lean_dec(v_a_1292_);
lean_inc(v_a_1290_);
lean_inc(v_a_1288_);
v___x_1294_ = l_Lean_Meta_isExprDefEq(v_a_1288_, v_a_1290_, v___y_1263_, v___y_1264_, v___y_1265_, v___y_1266_);
if (lean_obj_tag(v___x_1294_) == 0)
{
lean_object* v_a_1295_; uint8_t v___x_1296_; 
v_a_1295_ = lean_ctor_get(v___x_1294_, 0);
lean_inc(v_a_1295_);
lean_dec_ref_known(v___x_1294_, 1);
v___x_1296_ = lean_unbox(v_a_1295_);
lean_dec(v_a_1295_);
if (v___x_1296_ == 0)
{
lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1300_; 
v___x_1297_ = ((lean_object*)(l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__2___closed__1));
v___x_1298_ = lean_box(0);
if (v_isShared_1285_ == 0)
{
lean_ctor_set_tag(v___x_1284_, 1);
lean_ctor_set(v___x_1284_, 1, v___x_1298_);
lean_ctor_set(v___x_1284_, 0, v___x_1293_);
v___x_1300_ = v___x_1284_;
goto v_reusejp_1299_;
}
else
{
lean_object* v_reuseFailAlloc_1303_; 
v_reuseFailAlloc_1303_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1303_, 0, v___x_1293_);
lean_ctor_set(v_reuseFailAlloc_1303_, 1, v___x_1298_);
v___x_1300_ = v_reuseFailAlloc_1303_;
goto v_reusejp_1299_;
}
v_reusejp_1299_:
{
lean_object* v___x_1301_; lean_object* v___x_1302_; 
v___x_1301_ = l_Lean_Expr_const___override(v___x_1297_, v___x_1300_);
v___x_1302_ = l_Lean_mkApp4(v___x_1301_, v_a_1288_, v_fst_1281_, v_a_1290_, v_snd_1282_);
v_a_1276_ = v___x_1302_;
goto v___jp_1275_;
}
}
else
{
lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1307_; 
lean_dec(v_a_1290_);
v___x_1304_ = ((lean_object*)(l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__2___closed__3));
v___x_1305_ = lean_box(0);
if (v_isShared_1285_ == 0)
{
lean_ctor_set_tag(v___x_1284_, 1);
lean_ctor_set(v___x_1284_, 1, v___x_1305_);
lean_ctor_set(v___x_1284_, 0, v___x_1293_);
v___x_1307_ = v___x_1284_;
goto v_reusejp_1306_;
}
else
{
lean_object* v_reuseFailAlloc_1310_; 
v_reuseFailAlloc_1310_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1310_, 0, v___x_1293_);
lean_ctor_set(v_reuseFailAlloc_1310_, 1, v___x_1305_);
v___x_1307_ = v_reuseFailAlloc_1310_;
goto v_reusejp_1306_;
}
v_reusejp_1306_:
{
lean_object* v___x_1308_; lean_object* v___x_1309_; 
v___x_1308_ = l_Lean_Expr_const___override(v___x_1304_, v___x_1307_);
v___x_1309_ = l_Lean_mkApp3(v___x_1308_, v_a_1288_, v_fst_1281_, v_snd_1282_);
v_a_1276_ = v___x_1309_;
goto v___jp_1275_;
}
}
}
else
{
lean_object* v_a_1311_; lean_object* v___x_1313_; uint8_t v_isShared_1314_; uint8_t v_isSharedCheck_1318_; 
lean_dec(v___x_1293_);
lean_dec(v_a_1290_);
lean_dec(v_a_1288_);
lean_del_object(v___x_1284_);
lean_dec(v_snd_1282_);
lean_dec(v_fst_1281_);
lean_del_object(v___x_1273_);
lean_dec(v_tail_1271_);
lean_dec(v_x_1262_);
v_a_1311_ = lean_ctor_get(v___x_1294_, 0);
v_isSharedCheck_1318_ = !lean_is_exclusive(v___x_1294_);
if (v_isSharedCheck_1318_ == 0)
{
v___x_1313_ = v___x_1294_;
v_isShared_1314_ = v_isSharedCheck_1318_;
goto v_resetjp_1312_;
}
else
{
lean_inc(v_a_1311_);
lean_dec(v___x_1294_);
v___x_1313_ = lean_box(0);
v_isShared_1314_ = v_isSharedCheck_1318_;
goto v_resetjp_1312_;
}
v_resetjp_1312_:
{
lean_object* v___x_1316_; 
if (v_isShared_1314_ == 0)
{
v___x_1316_ = v___x_1313_;
goto v_reusejp_1315_;
}
else
{
lean_object* v_reuseFailAlloc_1317_; 
v_reuseFailAlloc_1317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1317_, 0, v_a_1311_);
v___x_1316_ = v_reuseFailAlloc_1317_;
goto v_reusejp_1315_;
}
v_reusejp_1315_:
{
return v___x_1316_;
}
}
}
}
else
{
lean_object* v_a_1319_; lean_object* v___x_1321_; uint8_t v_isShared_1322_; uint8_t v_isSharedCheck_1326_; 
lean_dec(v_a_1290_);
lean_dec(v_a_1288_);
lean_del_object(v___x_1284_);
lean_dec(v_snd_1282_);
lean_dec(v_fst_1281_);
lean_del_object(v___x_1273_);
lean_dec(v_tail_1271_);
lean_dec(v_x_1262_);
v_a_1319_ = lean_ctor_get(v___x_1291_, 0);
v_isSharedCheck_1326_ = !lean_is_exclusive(v___x_1291_);
if (v_isSharedCheck_1326_ == 0)
{
v___x_1321_ = v___x_1291_;
v_isShared_1322_ = v_isSharedCheck_1326_;
goto v_resetjp_1320_;
}
else
{
lean_inc(v_a_1319_);
lean_dec(v___x_1291_);
v___x_1321_ = lean_box(0);
v_isShared_1322_ = v_isSharedCheck_1326_;
goto v_resetjp_1320_;
}
v_resetjp_1320_:
{
lean_object* v___x_1324_; 
if (v_isShared_1322_ == 0)
{
v___x_1324_ = v___x_1321_;
goto v_reusejp_1323_;
}
else
{
lean_object* v_reuseFailAlloc_1325_; 
v_reuseFailAlloc_1325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1325_, 0, v_a_1319_);
v___x_1324_ = v_reuseFailAlloc_1325_;
goto v_reusejp_1323_;
}
v_reusejp_1323_:
{
return v___x_1324_;
}
}
}
}
else
{
lean_object* v_a_1327_; lean_object* v___x_1329_; uint8_t v_isShared_1330_; uint8_t v_isSharedCheck_1334_; 
lean_dec(v_a_1288_);
lean_del_object(v___x_1284_);
lean_dec(v_snd_1282_);
lean_dec(v_fst_1281_);
lean_del_object(v___x_1273_);
lean_dec(v_tail_1271_);
lean_dec(v_x_1262_);
v_a_1327_ = lean_ctor_get(v___x_1289_, 0);
v_isSharedCheck_1334_ = !lean_is_exclusive(v___x_1289_);
if (v_isSharedCheck_1334_ == 0)
{
v___x_1329_ = v___x_1289_;
v_isShared_1330_ = v_isSharedCheck_1334_;
goto v_resetjp_1328_;
}
else
{
lean_inc(v_a_1327_);
lean_dec(v___x_1289_);
v___x_1329_ = lean_box(0);
v_isShared_1330_ = v_isSharedCheck_1334_;
goto v_resetjp_1328_;
}
v_resetjp_1328_:
{
lean_object* v___x_1332_; 
if (v_isShared_1330_ == 0)
{
v___x_1332_ = v___x_1329_;
goto v_reusejp_1331_;
}
else
{
lean_object* v_reuseFailAlloc_1333_; 
v_reuseFailAlloc_1333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1333_, 0, v_a_1327_);
v___x_1332_ = v_reuseFailAlloc_1333_;
goto v_reusejp_1331_;
}
v_reusejp_1331_:
{
return v___x_1332_;
}
}
}
}
else
{
lean_object* v_a_1335_; lean_object* v___x_1337_; uint8_t v_isShared_1338_; uint8_t v_isSharedCheck_1342_; 
lean_del_object(v___x_1284_);
lean_dec(v_snd_1282_);
lean_dec(v_fst_1281_);
lean_del_object(v___x_1273_);
lean_dec(v_tail_1271_);
lean_dec(v_x_1262_);
v_a_1335_ = lean_ctor_get(v___x_1287_, 0);
v_isSharedCheck_1342_ = !lean_is_exclusive(v___x_1287_);
if (v_isSharedCheck_1342_ == 0)
{
v___x_1337_ = v___x_1287_;
v_isShared_1338_ = v_isSharedCheck_1342_;
goto v_resetjp_1336_;
}
else
{
lean_inc(v_a_1335_);
lean_dec(v___x_1287_);
v___x_1337_ = lean_box(0);
v_isShared_1338_ = v_isSharedCheck_1342_;
goto v_resetjp_1336_;
}
v_resetjp_1336_:
{
lean_object* v___x_1340_; 
if (v_isShared_1338_ == 0)
{
v___x_1340_ = v___x_1337_;
goto v_reusejp_1339_;
}
else
{
lean_object* v_reuseFailAlloc_1341_; 
v_reuseFailAlloc_1341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1341_, 0, v_a_1335_);
v___x_1340_ = v_reuseFailAlloc_1341_;
goto v_reusejp_1339_;
}
v_reusejp_1339_:
{
return v___x_1340_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__2___boxed(lean_object* v_x_1345_, lean_object* v_x_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_){
_start:
{
lean_object* v_res_1352_; 
v_res_1352_ = l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__2(v_x_1345_, v_x_1346_, v___y_1347_, v___y_1348_, v___y_1349_, v___y_1350_);
lean_dec(v___y_1350_);
lean_dec_ref(v___y_1349_);
lean_dec(v___y_1348_);
lean_dec_ref(v___y_1347_);
return v_res_1352_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__3(lean_object* v_a_1353_, lean_object* v_a_1354_){
_start:
{
if (lean_obj_tag(v_a_1353_) == 0)
{
lean_object* v___x_1355_; 
v___x_1355_ = lean_array_to_list(v_a_1354_);
return v___x_1355_;
}
else
{
lean_object* v_head_1356_; 
v_head_1356_ = lean_ctor_get(v_a_1353_, 0);
if (lean_obj_tag(v_head_1356_) == 0)
{
lean_object* v_tail_1357_; 
v_tail_1357_ = lean_ctor_get(v_a_1353_, 1);
lean_inc(v_tail_1357_);
lean_dec_ref_known(v_a_1353_, 2);
v_a_1353_ = v_tail_1357_;
goto _start;
}
else
{
lean_object* v_tail_1359_; lean_object* v_val_1360_; lean_object* v___x_1361_; 
lean_inc_ref(v_head_1356_);
v_tail_1359_ = lean_ctor_get(v_a_1353_, 1);
lean_inc(v_tail_1359_);
lean_dec_ref_known(v_a_1353_, 2);
v_val_1360_ = lean_ctor_get(v_head_1356_, 0);
lean_inc(v_val_1360_);
lean_dec_ref_known(v_head_1356_, 1);
v___x_1361_ = lean_array_push(v_a_1354_, v_val_1360_);
v_a_1353_ = v_tail_1359_;
v_a_1354_ = v___x_1361_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__1(lean_object* v_a_1363_, lean_object* v_a_1364_){
_start:
{
if (lean_obj_tag(v_a_1363_) == 0)
{
lean_object* v___x_1365_; 
v___x_1365_ = l_List_reverse___redArg(v_a_1364_);
return v___x_1365_;
}
else
{
lean_object* v_head_1366_; lean_object* v_tail_1367_; lean_object* v___x_1369_; uint8_t v_isShared_1370_; uint8_t v_isSharedCheck_1380_; 
v_head_1366_ = lean_ctor_get(v_a_1363_, 0);
v_tail_1367_ = lean_ctor_get(v_a_1363_, 1);
v_isSharedCheck_1380_ = !lean_is_exclusive(v_a_1363_);
if (v_isSharedCheck_1380_ == 0)
{
v___x_1369_ = v_a_1363_;
v_isShared_1370_ = v_isSharedCheck_1380_;
goto v_resetjp_1368_;
}
else
{
lean_inc(v_tail_1367_);
lean_inc(v_head_1366_);
lean_dec(v_a_1363_);
v___x_1369_ = lean_box(0);
v_isShared_1370_ = v_isSharedCheck_1380_;
goto v_resetjp_1368_;
}
v_resetjp_1368_:
{
uint8_t v___y_1372_; 
if (lean_obj_tag(v_head_1366_) == 0)
{
uint8_t v___x_1378_; 
v___x_1378_ = 0;
v___y_1372_ = v___x_1378_;
goto v___jp_1371_;
}
else
{
uint8_t v___x_1379_; 
lean_dec_ref_known(v_head_1366_, 1);
v___x_1379_ = 1;
v___y_1372_ = v___x_1379_;
goto v___jp_1371_;
}
v___jp_1371_:
{
lean_object* v___x_1373_; lean_object* v___x_1375_; 
v___x_1373_ = lean_box(v___y_1372_);
if (v_isShared_1370_ == 0)
{
lean_ctor_set(v___x_1369_, 1, v_a_1364_);
lean_ctor_set(v___x_1369_, 0, v___x_1373_);
v___x_1375_ = v___x_1369_;
goto v_reusejp_1374_;
}
else
{
lean_object* v_reuseFailAlloc_1377_; 
v_reuseFailAlloc_1377_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1377_, 0, v___x_1373_);
lean_ctor_set(v_reuseFailAlloc_1377_, 1, v_a_1364_);
v___x_1375_ = v_reuseFailAlloc_1377_;
goto v_reusejp_1374_;
}
v_reusejp_1374_:
{
v_a_1363_ = v_tail_1367_;
v_a_1364_ = v___x_1375_;
goto _start;
}
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__2___closed__0(void){
_start:
{
lean_object* v___x_1381_; lean_object* v_dummy_1382_; 
v___x_1381_ = lean_box(0);
v_dummy_1382_ = l_Lean_Expr_sort___override(v___x_1381_);
return v_dummy_1382_;
}
}
static lean_object* _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__2___closed__3(void){
_start:
{
lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; 
v___x_1387_ = lean_box(0);
v___x_1388_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkAndList___closed__1));
v___x_1389_ = l_Lean_mkConst(v___x_1388_, v___x_1387_);
return v___x_1389_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__2(lean_object* v___x_1390_, lean_object* v___f_1391_, lean_object* v_idxs_1392_, lean_object* v___x_1393_, lean_object* v_fvars_1394_, lean_object* v_ty_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_){
_start:
{
lean_object* v___x_1401_; lean_object* v_dummy_1402_; lean_object* v_nargs_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v_fst_1414_; lean_object* v_snd_1415_; lean_object* v___x_1417_; uint8_t v_isShared_1418_; uint8_t v_isSharedCheck_1515_; 
v___x_1401_ = lean_box(0);
v_dummy_1402_ = lean_obj_once(&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__2___closed__0, &l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__2___closed__0_once, _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__2___closed__0);
v_nargs_1403_ = l_Lean_Expr_getAppNumArgs(v_ty_1395_);
lean_inc(v_nargs_1403_);
v___x_1404_ = lean_mk_array(v_nargs_1403_, v_dummy_1402_);
v___x_1405_ = lean_unsigned_to_nat(1u);
v___x_1406_ = lean_nat_sub(v_nargs_1403_, v___x_1405_);
lean_dec(v_nargs_1403_);
v___x_1407_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_ty_1395_, v___x_1404_, v___x_1406_);
v___x_1408_ = lean_array_to_list(v___x_1407_);
v___x_1409_ = l_List_drop___redArg(v___x_1390_, v___x_1408_);
lean_dec(v___x_1408_);
v___x_1410_ = lean_array_to_list(v_fvars_1394_);
v___x_1411_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__2___closed__1));
v___x_1412_ = l___private_Init_Data_List_Impl_0__List_zipWithTR_go(lean_box(0), lean_box(0), lean_box(0), v___f_1391_, v_idxs_1392_, v___x_1409_, v___x_1411_);
v___x_1413_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_compactRelation(v___x_1410_, v___x_1412_);
v_fst_1414_ = lean_ctor_get(v___x_1413_, 0);
v_snd_1415_ = lean_ctor_get(v___x_1413_, 1);
v_isSharedCheck_1515_ = !lean_is_exclusive(v___x_1413_);
if (v_isSharedCheck_1515_ == 0)
{
v___x_1417_ = v___x_1413_;
v_isShared_1418_ = v_isSharedCheck_1515_;
goto v_resetjp_1416_;
}
else
{
lean_inc(v_snd_1415_);
lean_inc(v_fst_1414_);
lean_dec(v___x_1413_);
v___x_1417_ = lean_box(0);
v_isShared_1418_ = v_isSharedCheck_1515_;
goto v_resetjp_1416_;
}
v_resetjp_1416_:
{
lean_object* v_fst_1420_; lean_object* v_snd_1421_; lean_object* v_fst_1429_; lean_object* v_snd_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; 
v_fst_1429_ = lean_ctor_get(v_snd_1415_, 0);
lean_inc(v_fst_1429_);
v_snd_1430_ = lean_ctor_get(v_snd_1415_, 1);
lean_inc(v_snd_1430_);
lean_dec(v_snd_1415_);
v___x_1431_ = lean_box(0);
v___x_1432_ = l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__2(v_fst_1429_, v___x_1431_, v___y_1396_, v___y_1397_, v___y_1398_, v___y_1399_);
if (lean_obj_tag(v___x_1432_) == 0)
{
lean_object* v_a_1433_; lean_object* v_bs_x27_1435_; lean_object* v___y_1436_; lean_object* v___y_1437_; lean_object* v___y_1438_; lean_object* v___y_1439_; lean_object* v___x_1454_; 
v_a_1433_ = lean_ctor_get(v___x_1432_, 0);
lean_inc(v_a_1433_);
lean_dec_ref_known(v___x_1432_, 1);
lean_inc(v_fst_1414_);
v___x_1454_ = l_List_filterMapTR_go___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__3(v_fst_1414_, v___x_1411_);
if (lean_obj_tag(v___x_1454_) == 0)
{
if (lean_obj_tag(v_a_1433_) == 0)
{
lean_object* v___x_1455_; lean_object* v___x_1456_; 
lean_dec(v_snd_1430_);
v___x_1455_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__2___closed__2));
v___x_1456_ = lean_obj_once(&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__2___closed__3, &l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__2___closed__3_once, _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__2___closed__3);
v_fst_1420_ = v___x_1455_;
v_snd_1421_ = v___x_1456_;
goto v___jp_1419_;
}
else
{
v_bs_x27_1435_ = v___x_1454_;
v___y_1436_ = v___y_1396_;
v___y_1437_ = v___y_1397_;
v___y_1438_ = v___y_1398_;
v___y_1439_ = v___y_1399_;
goto v___jp_1434_;
}
}
else
{
if (lean_obj_tag(v_a_1433_) == 0)
{
lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; 
v___x_1457_ = l_List_getLast_x21___redArg(v___x_1393_, v___x_1454_);
v___x_1458_ = l_Lean_Expr_fvarId_x21(v___x_1457_);
lean_dec(v___x_1457_);
v___x_1459_ = l_Lean_FVarId_getType___redArg(v___x_1458_, v___y_1396_, v___y_1398_, v___y_1399_);
if (lean_obj_tag(v___x_1459_) == 0)
{
lean_object* v_a_1460_; lean_object* v___x_1461_; 
v_a_1460_ = lean_ctor_get(v___x_1459_, 0);
lean_inc_n(v_a_1460_, 2);
lean_dec_ref_known(v___x_1459_, 1);
lean_inc(v___y_1399_);
lean_inc_ref(v___y_1398_);
lean_inc(v___y_1397_);
lean_inc_ref(v___y_1396_);
v___x_1461_ = lean_infer_type(v_a_1460_, v___y_1396_, v___y_1397_, v___y_1398_, v___y_1399_);
if (lean_obj_tag(v___x_1461_) == 0)
{
lean_object* v_a_1462_; lean_object* v___x_1463_; uint8_t v___x_1464_; 
v_a_1462_ = lean_ctor_get(v___x_1461_, 0);
lean_inc(v_a_1462_);
lean_dec_ref_known(v___x_1461_, 1);
v___x_1463_ = l_Lean_Expr_sortLevel_x21(v_a_1462_);
lean_dec(v_a_1462_);
v___x_1464_ = lean_level_eq(v___x_1463_, v___x_1401_);
lean_dec(v___x_1463_);
if (v___x_1464_ == 0)
{
lean_object* v___x_1465_; lean_object* v___x_1466_; 
lean_dec(v_a_1460_);
v___x_1465_ = lean_obj_once(&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__2___closed__3, &l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__2___closed__3_once, _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__2___closed__3);
v___x_1466_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkExistsList(v___x_1454_, v___x_1465_, v___y_1396_, v___y_1397_, v___y_1398_, v___y_1399_);
if (lean_obj_tag(v___x_1466_) == 0)
{
lean_object* v_a_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; 
v_a_1467_ = lean_ctor_get(v___x_1466_, 0);
lean_inc(v_a_1467_);
lean_dec_ref_known(v___x_1466_, 1);
v___x_1468_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__2___closed__2));
v___x_1469_ = lean_apply_1(v_snd_1430_, v_a_1467_);
v_fst_1420_ = v___x_1468_;
v_snd_1421_ = v___x_1469_;
goto v___jp_1419_;
}
else
{
lean_object* v_a_1470_; lean_object* v___x_1472_; uint8_t v_isShared_1473_; uint8_t v_isSharedCheck_1477_; 
lean_dec(v_snd_1430_);
lean_del_object(v___x_1417_);
lean_dec(v_fst_1414_);
v_a_1470_ = lean_ctor_get(v___x_1466_, 0);
v_isSharedCheck_1477_ = !lean_is_exclusive(v___x_1466_);
if (v_isSharedCheck_1477_ == 0)
{
v___x_1472_ = v___x_1466_;
v_isShared_1473_ = v_isSharedCheck_1477_;
goto v_resetjp_1471_;
}
else
{
lean_inc(v_a_1470_);
lean_dec(v___x_1466_);
v___x_1472_ = lean_box(0);
v_isShared_1473_ = v_isSharedCheck_1477_;
goto v_resetjp_1471_;
}
v_resetjp_1471_:
{
lean_object* v___x_1475_; 
if (v_isShared_1473_ == 0)
{
v___x_1475_ = v___x_1472_;
goto v_reusejp_1474_;
}
else
{
lean_object* v_reuseFailAlloc_1476_; 
v_reuseFailAlloc_1476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1476_, 0, v_a_1470_);
v___x_1475_ = v_reuseFailAlloc_1476_;
goto v_reusejp_1474_;
}
v_reusejp_1474_:
{
return v___x_1475_;
}
}
}
}
else
{
lean_object* v___x_1478_; lean_object* v___x_1479_; 
v___x_1478_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_List_init___redArg(v___x_1454_);
v___x_1479_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkExistsList(v___x_1478_, v_a_1460_, v___y_1396_, v___y_1397_, v___y_1398_, v___y_1399_);
if (lean_obj_tag(v___x_1479_) == 0)
{
lean_object* v_a_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; 
v_a_1480_ = lean_ctor_get(v___x_1479_, 0);
lean_inc(v_a_1480_);
lean_dec_ref_known(v___x_1479_, 1);
v___x_1481_ = lean_box(0);
v___x_1482_ = lean_apply_1(v_snd_1430_, v_a_1480_);
v_fst_1420_ = v___x_1481_;
v_snd_1421_ = v___x_1482_;
goto v___jp_1419_;
}
else
{
lean_object* v_a_1483_; lean_object* v___x_1485_; uint8_t v_isShared_1486_; uint8_t v_isSharedCheck_1490_; 
lean_dec(v_snd_1430_);
lean_del_object(v___x_1417_);
lean_dec(v_fst_1414_);
v_a_1483_ = lean_ctor_get(v___x_1479_, 0);
v_isSharedCheck_1490_ = !lean_is_exclusive(v___x_1479_);
if (v_isSharedCheck_1490_ == 0)
{
v___x_1485_ = v___x_1479_;
v_isShared_1486_ = v_isSharedCheck_1490_;
goto v_resetjp_1484_;
}
else
{
lean_inc(v_a_1483_);
lean_dec(v___x_1479_);
v___x_1485_ = lean_box(0);
v_isShared_1486_ = v_isSharedCheck_1490_;
goto v_resetjp_1484_;
}
v_resetjp_1484_:
{
lean_object* v___x_1488_; 
if (v_isShared_1486_ == 0)
{
v___x_1488_ = v___x_1485_;
goto v_reusejp_1487_;
}
else
{
lean_object* v_reuseFailAlloc_1489_; 
v_reuseFailAlloc_1489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1489_, 0, v_a_1483_);
v___x_1488_ = v_reuseFailAlloc_1489_;
goto v_reusejp_1487_;
}
v_reusejp_1487_:
{
return v___x_1488_;
}
}
}
}
}
else
{
lean_object* v_a_1491_; lean_object* v___x_1493_; uint8_t v_isShared_1494_; uint8_t v_isSharedCheck_1498_; 
lean_dec(v_a_1460_);
lean_dec(v___x_1454_);
lean_dec(v_snd_1430_);
lean_del_object(v___x_1417_);
lean_dec(v_fst_1414_);
v_a_1491_ = lean_ctor_get(v___x_1461_, 0);
v_isSharedCheck_1498_ = !lean_is_exclusive(v___x_1461_);
if (v_isSharedCheck_1498_ == 0)
{
v___x_1493_ = v___x_1461_;
v_isShared_1494_ = v_isSharedCheck_1498_;
goto v_resetjp_1492_;
}
else
{
lean_inc(v_a_1491_);
lean_dec(v___x_1461_);
v___x_1493_ = lean_box(0);
v_isShared_1494_ = v_isSharedCheck_1498_;
goto v_resetjp_1492_;
}
v_resetjp_1492_:
{
lean_object* v___x_1496_; 
if (v_isShared_1494_ == 0)
{
v___x_1496_ = v___x_1493_;
goto v_reusejp_1495_;
}
else
{
lean_object* v_reuseFailAlloc_1497_; 
v_reuseFailAlloc_1497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1497_, 0, v_a_1491_);
v___x_1496_ = v_reuseFailAlloc_1497_;
goto v_reusejp_1495_;
}
v_reusejp_1495_:
{
return v___x_1496_;
}
}
}
}
else
{
lean_object* v_a_1499_; lean_object* v___x_1501_; uint8_t v_isShared_1502_; uint8_t v_isSharedCheck_1506_; 
lean_dec(v___x_1454_);
lean_dec(v_snd_1430_);
lean_del_object(v___x_1417_);
lean_dec(v_fst_1414_);
v_a_1499_ = lean_ctor_get(v___x_1459_, 0);
v_isSharedCheck_1506_ = !lean_is_exclusive(v___x_1459_);
if (v_isSharedCheck_1506_ == 0)
{
v___x_1501_ = v___x_1459_;
v_isShared_1502_ = v_isSharedCheck_1506_;
goto v_resetjp_1500_;
}
else
{
lean_inc(v_a_1499_);
lean_dec(v___x_1459_);
v___x_1501_ = lean_box(0);
v_isShared_1502_ = v_isSharedCheck_1506_;
goto v_resetjp_1500_;
}
v_resetjp_1500_:
{
lean_object* v___x_1504_; 
if (v_isShared_1502_ == 0)
{
v___x_1504_ = v___x_1501_;
goto v_reusejp_1503_;
}
else
{
lean_object* v_reuseFailAlloc_1505_; 
v_reuseFailAlloc_1505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1505_, 0, v_a_1499_);
v___x_1504_ = v_reuseFailAlloc_1505_;
goto v_reusejp_1503_;
}
v_reusejp_1503_:
{
return v___x_1504_;
}
}
}
}
else
{
v_bs_x27_1435_ = v___x_1454_;
v___y_1436_ = v___y_1396_;
v___y_1437_ = v___y_1397_;
v___y_1438_ = v___y_1398_;
v___y_1439_ = v___y_1399_;
goto v___jp_1434_;
}
}
v___jp_1434_:
{
lean_object* v___x_1440_; lean_object* v___x_1441_; 
lean_inc(v_a_1433_);
v___x_1440_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkAndList(v_a_1433_);
v___x_1441_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkExistsList(v_bs_x27_1435_, v___x_1440_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_);
if (lean_obj_tag(v___x_1441_) == 0)
{
lean_object* v_a_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; 
v_a_1442_ = lean_ctor_get(v___x_1441_, 0);
lean_inc(v_a_1442_);
lean_dec_ref_known(v___x_1441_, 1);
v___x_1443_ = l_List_lengthTR___redArg(v_a_1433_);
lean_dec(v_a_1433_);
v___x_1444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1444_, 0, v___x_1443_);
v___x_1445_ = lean_apply_1(v_snd_1430_, v_a_1442_);
v_fst_1420_ = v___x_1444_;
v_snd_1421_ = v___x_1445_;
goto v___jp_1419_;
}
else
{
lean_object* v_a_1446_; lean_object* v___x_1448_; uint8_t v_isShared_1449_; uint8_t v_isSharedCheck_1453_; 
lean_dec(v_a_1433_);
lean_dec(v_snd_1430_);
lean_del_object(v___x_1417_);
lean_dec(v_fst_1414_);
v_a_1446_ = lean_ctor_get(v___x_1441_, 0);
v_isSharedCheck_1453_ = !lean_is_exclusive(v___x_1441_);
if (v_isSharedCheck_1453_ == 0)
{
v___x_1448_ = v___x_1441_;
v_isShared_1449_ = v_isSharedCheck_1453_;
goto v_resetjp_1447_;
}
else
{
lean_inc(v_a_1446_);
lean_dec(v___x_1441_);
v___x_1448_ = lean_box(0);
v_isShared_1449_ = v_isSharedCheck_1453_;
goto v_resetjp_1447_;
}
v_resetjp_1447_:
{
lean_object* v___x_1451_; 
if (v_isShared_1449_ == 0)
{
v___x_1451_ = v___x_1448_;
goto v_reusejp_1450_;
}
else
{
lean_object* v_reuseFailAlloc_1452_; 
v_reuseFailAlloc_1452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1452_, 0, v_a_1446_);
v___x_1451_ = v_reuseFailAlloc_1452_;
goto v_reusejp_1450_;
}
v_reusejp_1450_:
{
return v___x_1451_;
}
}
}
}
}
else
{
lean_object* v_a_1507_; lean_object* v___x_1509_; uint8_t v_isShared_1510_; uint8_t v_isSharedCheck_1514_; 
lean_dec(v_snd_1430_);
lean_del_object(v___x_1417_);
lean_dec(v_fst_1414_);
v_a_1507_ = lean_ctor_get(v___x_1432_, 0);
v_isSharedCheck_1514_ = !lean_is_exclusive(v___x_1432_);
if (v_isSharedCheck_1514_ == 0)
{
v___x_1509_ = v___x_1432_;
v_isShared_1510_ = v_isSharedCheck_1514_;
goto v_resetjp_1508_;
}
else
{
lean_inc(v_a_1507_);
lean_dec(v___x_1432_);
v___x_1509_ = lean_box(0);
v_isShared_1510_ = v_isSharedCheck_1514_;
goto v_resetjp_1508_;
}
v_resetjp_1508_:
{
lean_object* v___x_1512_; 
if (v_isShared_1510_ == 0)
{
v___x_1512_ = v___x_1509_;
goto v_reusejp_1511_;
}
else
{
lean_object* v_reuseFailAlloc_1513_; 
v_reuseFailAlloc_1513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1513_, 0, v_a_1507_);
v___x_1512_ = v_reuseFailAlloc_1513_;
goto v_reusejp_1511_;
}
v_reusejp_1511_:
{
return v___x_1512_;
}
}
}
v___jp_1419_:
{
lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1426_; 
v___x_1422_ = lean_box(0);
v___x_1423_ = l_List_mapTR_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__1(v_fst_1414_, v___x_1422_);
v___x_1424_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1424_, 0, v___x_1423_);
lean_ctor_set(v___x_1424_, 1, v_fst_1420_);
if (v_isShared_1418_ == 0)
{
lean_ctor_set(v___x_1417_, 1, v_snd_1421_);
lean_ctor_set(v___x_1417_, 0, v___x_1424_);
v___x_1426_ = v___x_1417_;
goto v_reusejp_1425_;
}
else
{
lean_object* v_reuseFailAlloc_1428_; 
v_reuseFailAlloc_1428_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1428_, 0, v___x_1424_);
lean_ctor_set(v_reuseFailAlloc_1428_, 1, v_snd_1421_);
v___x_1426_ = v_reuseFailAlloc_1428_;
goto v_reusejp_1425_;
}
v_reusejp_1425_:
{
lean_object* v___x_1427_; 
v___x_1427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1427_, 0, v___x_1426_);
return v___x_1427_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__2___boxed(lean_object* v___x_1516_, lean_object* v___f_1517_, lean_object* v_idxs_1518_, lean_object* v___x_1519_, lean_object* v_fvars_1520_, lean_object* v_ty_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_){
_start:
{
lean_object* v_res_1527_; 
v_res_1527_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__2(v___x_1516_, v___f_1517_, v_idxs_1518_, v___x_1519_, v_fvars_1520_, v_ty_1521_, v___y_1522_, v___y_1523_, v___y_1524_, v___y_1525_);
lean_dec(v___y_1525_);
lean_dec_ref(v___y_1524_);
lean_dec(v___y_1523_);
lean_dec_ref(v___y_1522_);
lean_dec_ref(v___x_1519_);
return v_res_1527_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__9___redArg(lean_object* v_ref_1528_, lean_object* v_msg_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_){
_start:
{
lean_object* v_toCold_1535_; lean_object* v_currRecDepth_1536_; lean_object* v_ref_1537_; uint16_t v_optionFlags_1538_; uint8_t v_suppressElabErrors_1539_; uint8_t v_checkDeprecated_1540_; uint8_t v_isRecordingDeps_1541_; lean_object* v_ref_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; 
v_toCold_1535_ = lean_ctor_get(v___y_1532_, 0);
v_currRecDepth_1536_ = lean_ctor_get(v___y_1532_, 1);
v_ref_1537_ = lean_ctor_get(v___y_1532_, 2);
v_optionFlags_1538_ = lean_ctor_get_uint16(v___y_1532_, sizeof(void*)*3);
v_suppressElabErrors_1539_ = lean_ctor_get_uint8(v___y_1532_, sizeof(void*)*3 + 2);
v_checkDeprecated_1540_ = lean_ctor_get_uint8(v___y_1532_, sizeof(void*)*3 + 3);
v_isRecordingDeps_1541_ = lean_ctor_get_uint8(v___y_1532_, sizeof(void*)*3 + 4);
v_ref_1542_ = l_Lean_replaceRef(v_ref_1528_, v_ref_1537_);
lean_inc(v_currRecDepth_1536_);
lean_inc_ref(v_toCold_1535_);
v___x_1543_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_1543_, 0, v_toCold_1535_);
lean_ctor_set(v___x_1543_, 1, v_currRecDepth_1536_);
lean_ctor_set(v___x_1543_, 2, v_ref_1542_);
lean_ctor_set_uint16(v___x_1543_, sizeof(void*)*3, v_optionFlags_1538_);
lean_ctor_set_uint8(v___x_1543_, sizeof(void*)*3 + 2, v_suppressElabErrors_1539_);
lean_ctor_set_uint8(v___x_1543_, sizeof(void*)*3 + 3, v_checkDeprecated_1540_);
lean_ctor_set_uint8(v___x_1543_, sizeof(void*)*3 + 4, v_isRecordingDeps_1541_);
v___x_1544_ = l_Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0___redArg(v_msg_1529_, v___y_1530_, v___y_1531_, v___x_1543_, v___y_1533_);
lean_dec_ref_known(v___x_1543_, 3);
return v___x_1544_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__9___redArg___boxed(lean_object* v_ref_1545_, lean_object* v_msg_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_){
_start:
{
lean_object* v_res_1552_; 
v_res_1552_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__9___redArg(v_ref_1545_, v_msg_1546_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_);
lean_dec(v___y_1550_);
lean_dec_ref(v___y_1549_);
lean_dec(v___y_1548_);
lean_dec_ref(v___y_1547_);
lean_dec(v_ref_1545_);
return v_res_1552_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__0(void){
_start:
{
lean_object* v___x_1553_; 
v___x_1553_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1553_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__1(void){
_start:
{
lean_object* v___x_1554_; lean_object* v___x_1555_; 
v___x_1554_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__0);
v___x_1555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1555_, 0, v___x_1554_);
return v___x_1555_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__2(void){
_start:
{
lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; 
v___x_1556_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__1);
v___x_1557_ = lean_unsigned_to_nat(0u);
v___x_1558_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_1558_, 0, v___x_1557_);
lean_ctor_set(v___x_1558_, 1, v___x_1557_);
lean_ctor_set(v___x_1558_, 2, v___x_1557_);
lean_ctor_set(v___x_1558_, 3, v___x_1557_);
lean_ctor_set(v___x_1558_, 4, v___x_1556_);
lean_ctor_set(v___x_1558_, 5, v___x_1556_);
lean_ctor_set(v___x_1558_, 6, v___x_1556_);
lean_ctor_set(v___x_1558_, 7, v___x_1556_);
lean_ctor_set(v___x_1558_, 8, v___x_1556_);
lean_ctor_set(v___x_1558_, 9, v___x_1556_);
lean_ctor_set(v___x_1558_, 10, v___x_1556_);
return v___x_1558_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__3(void){
_start:
{
lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; 
v___x_1559_ = lean_unsigned_to_nat(32u);
v___x_1560_ = lean_mk_empty_array_with_capacity(v___x_1559_);
v___x_1561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1561_, 0, v___x_1560_);
return v___x_1561_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__4(void){
_start:
{
size_t v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; 
v___x_1562_ = ((size_t)5ULL);
v___x_1563_ = lean_unsigned_to_nat(0u);
v___x_1564_ = lean_unsigned_to_nat(32u);
v___x_1565_ = lean_mk_empty_array_with_capacity(v___x_1564_);
v___x_1566_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__3);
v___x_1567_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1567_, 0, v___x_1566_);
lean_ctor_set(v___x_1567_, 1, v___x_1565_);
lean_ctor_set(v___x_1567_, 2, v___x_1563_);
lean_ctor_set(v___x_1567_, 3, v___x_1563_);
lean_ctor_set_usize(v___x_1567_, 4, v___x_1562_);
return v___x_1567_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__5(void){
_start:
{
lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; 
v___x_1568_ = lean_box(1);
v___x_1569_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__4);
v___x_1570_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__1);
v___x_1571_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1571_, 0, v___x_1570_);
lean_ctor_set(v___x_1571_, 1, v___x_1569_);
lean_ctor_set(v___x_1571_, 2, v___x_1568_);
return v___x_1571_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__7(void){
_start:
{
lean_object* v___x_1573_; lean_object* v___x_1574_; 
v___x_1573_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__6));
v___x_1574_ = l_Lean_stringToMessageData(v___x_1573_);
return v___x_1574_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__9(void){
_start:
{
lean_object* v___x_1576_; lean_object* v___x_1577_; 
v___x_1576_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__8));
v___x_1577_ = l_Lean_stringToMessageData(v___x_1576_);
return v___x_1577_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__11(void){
_start:
{
lean_object* v___x_1579_; lean_object* v___x_1580_; 
v___x_1579_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__10));
v___x_1580_ = l_Lean_stringToMessageData(v___x_1579_);
return v___x_1580_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__13(void){
_start:
{
lean_object* v___x_1582_; lean_object* v___x_1583_; 
v___x_1582_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__12));
v___x_1583_ = l_Lean_stringToMessageData(v___x_1582_);
return v___x_1583_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__15(void){
_start:
{
lean_object* v___x_1585_; lean_object* v___x_1586_; 
v___x_1585_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__14));
v___x_1586_ = l_Lean_stringToMessageData(v___x_1585_);
return v___x_1586_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__17(void){
_start:
{
lean_object* v___x_1588_; lean_object* v___x_1589_; 
v___x_1588_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__16));
v___x_1589_ = l_Lean_stringToMessageData(v___x_1588_);
return v___x_1589_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__19(void){
_start:
{
lean_object* v___x_1591_; lean_object* v___x_1592_; 
v___x_1591_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__18));
v___x_1592_ = l_Lean_stringToMessageData(v___x_1591_);
return v___x_1592_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg(lean_object* v_msg_1593_, lean_object* v_declHint_1594_, lean_object* v___y_1595_){
_start:
{
lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v_env_1599_; uint8_t v___x_1600_; 
v___x_1597_ = lean_box(0);
v___x_1598_ = lean_st_ref_get(v___y_1595_);
v_env_1599_ = lean_ctor_get(v___x_1598_, 0);
lean_inc_ref(v_env_1599_);
lean_dec(v___x_1598_);
v___x_1600_ = l_Lean_Name_isAnonymous(v_declHint_1594_);
if (v___x_1600_ == 0)
{
uint8_t v_isExporting_1601_; 
v_isExporting_1601_ = lean_ctor_get_uint8(v_env_1599_, sizeof(void*)*13);
if (v_isExporting_1601_ == 0)
{
lean_object* v___x_1602_; 
lean_dec_ref(v_env_1599_);
lean_dec(v_declHint_1594_);
v___x_1602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1602_, 0, v_msg_1593_);
return v___x_1602_;
}
else
{
lean_object* v___x_1603_; uint8_t v___x_1604_; 
lean_inc_ref(v_env_1599_);
v___x_1603_ = l_Lean_Environment_setExporting(v_env_1599_, v___x_1600_);
lean_inc(v_declHint_1594_);
lean_inc_ref(v___x_1603_);
v___x_1604_ = l_Lean_Environment_contains(v___x_1603_, v_declHint_1594_, v_isExporting_1601_);
if (v___x_1604_ == 0)
{
lean_object* v___x_1605_; 
lean_dec_ref(v___x_1603_);
lean_dec_ref(v_env_1599_);
lean_dec(v_declHint_1594_);
v___x_1605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1605_, 0, v_msg_1593_);
return v___x_1605_;
}
else
{
lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v_c_1611_; lean_object* v___x_1612_; 
v___x_1606_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__2);
v___x_1607_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__5);
v___x_1608_ = l_Lean_Options_empty;
lean_inc_ref(v___x_1603_);
v___x_1609_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1609_, 0, v___x_1603_);
lean_ctor_set(v___x_1609_, 1, v___x_1606_);
lean_ctor_set(v___x_1609_, 2, v___x_1607_);
lean_ctor_set(v___x_1609_, 3, v___x_1608_);
lean_inc(v_declHint_1594_);
v___x_1610_ = l_Lean_MessageData_ofConstName(v_declHint_1594_, v___x_1600_);
v_c_1611_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1611_, 0, v___x_1609_);
lean_ctor_set(v_c_1611_, 1, v___x_1610_);
v___x_1612_ = l_Lean_Environment_getModuleIdxFor_x3f(v___x_1603_, v_declHint_1594_);
lean_dec_ref(v___x_1603_);
if (lean_obj_tag(v___x_1612_) == 0)
{
lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; 
lean_dec_ref(v_env_1599_);
lean_dec(v_declHint_1594_);
v___x_1613_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__7);
v___x_1614_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1614_, 0, v___x_1613_);
lean_ctor_set(v___x_1614_, 1, v_c_1611_);
v___x_1615_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__9);
v___x_1616_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1616_, 0, v___x_1614_);
lean_ctor_set(v___x_1616_, 1, v___x_1615_);
v___x_1617_ = l_Lean_MessageData_note(v___x_1616_);
v___x_1618_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1618_, 0, v_msg_1593_);
lean_ctor_set(v___x_1618_, 1, v___x_1617_);
v___x_1619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1619_, 0, v___x_1618_);
return v___x_1619_;
}
else
{
lean_object* v_val_1620_; lean_object* v___x_1622_; uint8_t v_isShared_1623_; uint8_t v_isSharedCheck_1654_; 
v_val_1620_ = lean_ctor_get(v___x_1612_, 0);
v_isSharedCheck_1654_ = !lean_is_exclusive(v___x_1612_);
if (v_isSharedCheck_1654_ == 0)
{
v___x_1622_ = v___x_1612_;
v_isShared_1623_ = v_isSharedCheck_1654_;
goto v_resetjp_1621_;
}
else
{
lean_inc(v_val_1620_);
lean_dec(v___x_1612_);
v___x_1622_ = lean_box(0);
v_isShared_1623_ = v_isSharedCheck_1654_;
goto v_resetjp_1621_;
}
v_resetjp_1621_:
{
lean_object* v___x_1624_; lean_object* v_moduleNames_1625_; lean_object* v_mod_1626_; uint8_t v___x_1627_; 
v___x_1624_ = l_Lean_Environment_header(v_env_1599_);
lean_dec_ref(v_env_1599_);
v_moduleNames_1625_ = lean_ctor_get(v___x_1624_, 4);
lean_inc_ref(v_moduleNames_1625_);
lean_dec_ref(v___x_1624_);
v_mod_1626_ = lean_array_get(v___x_1597_, v_moduleNames_1625_, v_val_1620_);
lean_dec(v_val_1620_);
lean_dec_ref(v_moduleNames_1625_);
v___x_1627_ = l_Lean_isPrivateName(v_declHint_1594_);
lean_dec(v_declHint_1594_);
if (v___x_1627_ == 0)
{
lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1639_; 
v___x_1628_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__11);
v___x_1629_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1629_, 0, v___x_1628_);
lean_ctor_set(v___x_1629_, 1, v_c_1611_);
v___x_1630_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__13);
v___x_1631_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1631_, 0, v___x_1629_);
lean_ctor_set(v___x_1631_, 1, v___x_1630_);
v___x_1632_ = l_Lean_MessageData_ofName(v_mod_1626_);
v___x_1633_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1633_, 0, v___x_1631_);
lean_ctor_set(v___x_1633_, 1, v___x_1632_);
v___x_1634_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__15);
v___x_1635_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1635_, 0, v___x_1633_);
lean_ctor_set(v___x_1635_, 1, v___x_1634_);
v___x_1636_ = l_Lean_MessageData_note(v___x_1635_);
v___x_1637_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1637_, 0, v_msg_1593_);
lean_ctor_set(v___x_1637_, 1, v___x_1636_);
if (v_isShared_1623_ == 0)
{
lean_ctor_set_tag(v___x_1622_, 0);
lean_ctor_set(v___x_1622_, 0, v___x_1637_);
v___x_1639_ = v___x_1622_;
goto v_reusejp_1638_;
}
else
{
lean_object* v_reuseFailAlloc_1640_; 
v_reuseFailAlloc_1640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1640_, 0, v___x_1637_);
v___x_1639_ = v_reuseFailAlloc_1640_;
goto v_reusejp_1638_;
}
v_reusejp_1638_:
{
return v___x_1639_;
}
}
else
{
lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1652_; 
v___x_1641_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__7);
v___x_1642_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1642_, 0, v___x_1641_);
lean_ctor_set(v___x_1642_, 1, v_c_1611_);
v___x_1643_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__17);
v___x_1644_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1644_, 0, v___x_1642_);
lean_ctor_set(v___x_1644_, 1, v___x_1643_);
v___x_1645_ = l_Lean_MessageData_ofName(v_mod_1626_);
v___x_1646_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1646_, 0, v___x_1644_);
lean_ctor_set(v___x_1646_, 1, v___x_1645_);
v___x_1647_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__19);
v___x_1648_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1648_, 0, v___x_1646_);
lean_ctor_set(v___x_1648_, 1, v___x_1647_);
v___x_1649_ = l_Lean_MessageData_note(v___x_1648_);
v___x_1650_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1650_, 0, v_msg_1593_);
lean_ctor_set(v___x_1650_, 1, v___x_1649_);
if (v_isShared_1623_ == 0)
{
lean_ctor_set_tag(v___x_1622_, 0);
lean_ctor_set(v___x_1622_, 0, v___x_1650_);
v___x_1652_ = v___x_1622_;
goto v_reusejp_1651_;
}
else
{
lean_object* v_reuseFailAlloc_1653_; 
v_reuseFailAlloc_1653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1653_, 0, v___x_1650_);
v___x_1652_ = v_reuseFailAlloc_1653_;
goto v_reusejp_1651_;
}
v_reusejp_1651_:
{
return v___x_1652_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1655_; 
lean_dec_ref(v_env_1599_);
lean_dec(v_declHint_1594_);
v___x_1655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1655_, 0, v_msg_1593_);
return v___x_1655_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___boxed(lean_object* v_msg_1656_, lean_object* v_declHint_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_){
_start:
{
lean_object* v_res_1660_; 
v_res_1660_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg(v_msg_1656_, v_declHint_1657_, v___y_1658_);
lean_dec(v___y_1658_);
return v_res_1660_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8(lean_object* v_msg_1661_, lean_object* v_declHint_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_){
_start:
{
lean_object* v___x_1668_; lean_object* v_a_1669_; lean_object* v___x_1671_; uint8_t v_isShared_1672_; uint8_t v_isSharedCheck_1678_; 
v___x_1668_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg(v_msg_1661_, v_declHint_1662_, v___y_1666_);
v_a_1669_ = lean_ctor_get(v___x_1668_, 0);
v_isSharedCheck_1678_ = !lean_is_exclusive(v___x_1668_);
if (v_isSharedCheck_1678_ == 0)
{
v___x_1671_ = v___x_1668_;
v_isShared_1672_ = v_isSharedCheck_1678_;
goto v_resetjp_1670_;
}
else
{
lean_inc(v_a_1669_);
lean_dec(v___x_1668_);
v___x_1671_ = lean_box(0);
v_isShared_1672_ = v_isSharedCheck_1678_;
goto v_resetjp_1670_;
}
v_resetjp_1670_:
{
lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1676_; 
v___x_1673_ = l_Lean_unknownIdentifierMessageTag;
v___x_1674_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1674_, 0, v___x_1673_);
lean_ctor_set(v___x_1674_, 1, v_a_1669_);
if (v_isShared_1672_ == 0)
{
lean_ctor_set(v___x_1671_, 0, v___x_1674_);
v___x_1676_ = v___x_1671_;
goto v_reusejp_1675_;
}
else
{
lean_object* v_reuseFailAlloc_1677_; 
v_reuseFailAlloc_1677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1677_, 0, v___x_1674_);
v___x_1676_ = v_reuseFailAlloc_1677_;
goto v_reusejp_1675_;
}
v_reusejp_1675_:
{
return v___x_1676_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8___boxed(lean_object* v_msg_1679_, lean_object* v_declHint_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_){
_start:
{
lean_object* v_res_1686_; 
v_res_1686_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8(v_msg_1679_, v_declHint_1680_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_);
lean_dec(v___y_1684_);
lean_dec_ref(v___y_1683_);
lean_dec(v___y_1682_);
lean_dec_ref(v___y_1681_);
return v_res_1686_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7___redArg(lean_object* v_ref_1687_, lean_object* v_msg_1688_, lean_object* v_declHint_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_){
_start:
{
lean_object* v___x_1695_; lean_object* v_a_1696_; lean_object* v___x_1697_; 
v___x_1695_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8(v_msg_1688_, v_declHint_1689_, v___y_1690_, v___y_1691_, v___y_1692_, v___y_1693_);
v_a_1696_ = lean_ctor_get(v___x_1695_, 0);
lean_inc(v_a_1696_);
lean_dec_ref(v___x_1695_);
v___x_1697_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__9___redArg(v_ref_1687_, v_a_1696_, v___y_1690_, v___y_1691_, v___y_1692_, v___y_1693_);
return v___x_1697_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7___redArg___boxed(lean_object* v_ref_1698_, lean_object* v_msg_1699_, lean_object* v_declHint_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_){
_start:
{
lean_object* v_res_1706_; 
v_res_1706_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7___redArg(v_ref_1698_, v_msg_1699_, v_declHint_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_);
lean_dec(v___y_1704_);
lean_dec_ref(v___y_1703_);
lean_dec(v___y_1702_);
lean_dec_ref(v___y_1701_);
lean_dec(v_ref_1698_);
return v_res_1706_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_1708_; lean_object* v___x_1709_; 
v___x_1708_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3___redArg___closed__0));
v___x_1709_ = l_Lean_stringToMessageData(v___x_1708_);
return v___x_1709_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_1711_; lean_object* v___x_1712_; 
v___x_1711_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3___redArg___closed__2));
v___x_1712_ = l_Lean_stringToMessageData(v___x_1711_);
return v___x_1712_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3___redArg(lean_object* v_ref_1713_, lean_object* v_constName_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_){
_start:
{
lean_object* v___x_1720_; uint8_t v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; 
v___x_1720_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3___redArg___closed__1);
v___x_1721_ = 0;
lean_inc(v_constName_1714_);
v___x_1722_ = l_Lean_MessageData_ofConstName(v_constName_1714_, v___x_1721_);
v___x_1723_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1723_, 0, v___x_1720_);
lean_ctor_set(v___x_1723_, 1, v___x_1722_);
v___x_1724_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3___redArg___closed__3);
v___x_1725_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1725_, 0, v___x_1723_);
lean_ctor_set(v___x_1725_, 1, v___x_1724_);
v___x_1726_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7___redArg(v_ref_1713_, v___x_1725_, v_constName_1714_, v___y_1715_, v___y_1716_, v___y_1717_, v___y_1718_);
return v___x_1726_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_ref_1727_, lean_object* v_constName_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_){
_start:
{
lean_object* v_res_1734_; 
v_res_1734_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3___redArg(v_ref_1727_, v_constName_1728_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_);
lean_dec(v___y_1732_);
lean_dec_ref(v___y_1731_);
lean_dec(v___y_1730_);
lean_dec_ref(v___y_1729_);
lean_dec(v_ref_1727_);
return v_res_1734_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0___redArg(lean_object* v_constName_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_){
_start:
{
lean_object* v_ref_1741_; lean_object* v___x_1742_; 
v_ref_1741_ = lean_ctor_get(v___y_1738_, 2);
v___x_1742_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3___redArg(v_ref_1741_, v_constName_1735_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_);
return v___x_1742_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0___redArg___boxed(lean_object* v_constName_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_){
_start:
{
lean_object* v_res_1749_; 
v_res_1749_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0___redArg(v_constName_1743_, v___y_1744_, v___y_1745_, v___y_1746_, v___y_1747_);
lean_dec(v___y_1747_);
lean_dec_ref(v___y_1746_);
lean_dec(v___y_1745_);
lean_dec_ref(v___y_1744_);
return v_res_1749_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0(lean_object* v_constName_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_){
_start:
{
lean_object* v___x_1756_; lean_object* v_env_1757_; uint8_t v___x_1758_; lean_object* v___x_1759_; 
v___x_1756_ = lean_st_ref_get(v___y_1754_);
v_env_1757_ = lean_ctor_get(v___x_1756_, 0);
lean_inc_ref(v_env_1757_);
lean_dec(v___x_1756_);
v___x_1758_ = 0;
lean_inc(v_constName_1750_);
v___x_1759_ = l_Lean_Environment_find_x3f(v_env_1757_, v_constName_1750_, v___x_1758_);
if (lean_obj_tag(v___x_1759_) == 0)
{
lean_object* v___x_1760_; 
v___x_1760_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0___redArg(v_constName_1750_, v___y_1751_, v___y_1752_, v___y_1753_, v___y_1754_);
return v___x_1760_;
}
else
{
lean_object* v_val_1761_; lean_object* v___x_1763_; uint8_t v_isShared_1764_; uint8_t v_isSharedCheck_1768_; 
lean_dec(v_constName_1750_);
v_val_1761_ = lean_ctor_get(v___x_1759_, 0);
v_isSharedCheck_1768_ = !lean_is_exclusive(v___x_1759_);
if (v_isSharedCheck_1768_ == 0)
{
v___x_1763_ = v___x_1759_;
v_isShared_1764_ = v_isSharedCheck_1768_;
goto v_resetjp_1762_;
}
else
{
lean_inc(v_val_1761_);
lean_dec(v___x_1759_);
v___x_1763_ = lean_box(0);
v_isShared_1764_ = v_isSharedCheck_1768_;
goto v_resetjp_1762_;
}
v_resetjp_1762_:
{
lean_object* v___x_1766_; 
if (v_isShared_1764_ == 0)
{
lean_ctor_set_tag(v___x_1763_, 0);
v___x_1766_ = v___x_1763_;
goto v_reusejp_1765_;
}
else
{
lean_object* v_reuseFailAlloc_1767_; 
v_reuseFailAlloc_1767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1767_, 0, v_val_1761_);
v___x_1766_ = v_reuseFailAlloc_1767_;
goto v_reusejp_1765_;
}
v_reusejp_1765_:
{
return v___x_1766_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0___boxed(lean_object* v_constName_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_){
_start:
{
lean_object* v_res_1775_; 
v_res_1775_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0(v_constName_1769_, v___y_1770_, v___y_1771_, v___y_1772_, v___y_1773_);
lean_dec(v___y_1773_);
lean_dec_ref(v___y_1772_);
lean_dec(v___y_1771_);
lean_dec_ref(v___y_1770_);
return v_res_1775_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp(lean_object* v_univs_1777_, lean_object* v_params_1778_, lean_object* v_idxs_1779_, lean_object* v_c_1780_, lean_object* v_a_1781_, lean_object* v_a_1782_, lean_object* v_a_1783_, lean_object* v_a_1784_){
_start:
{
lean_object* v___f_1786_; lean_object* v___f_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; 
lean_inc(v_params_1778_);
v___f_1786_ = lean_alloc_closure((void*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1786_, 0, v_params_1778_);
v___f_1787_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___closed__0));
v___x_1788_ = l_Lean_instInhabitedExpr;
v___x_1789_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0(v_c_1780_, v_a_1781_, v_a_1782_, v_a_1783_, v_a_1784_);
if (lean_obj_tag(v___x_1789_) == 0)
{
lean_object* v_a_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___f_1793_; lean_object* v___x_1794_; uint8_t v___x_1795_; lean_object* v___x_1796_; 
v_a_1790_ = lean_ctor_get(v___x_1789_, 0);
lean_inc(v_a_1790_);
lean_dec_ref_known(v___x_1789_, 1);
v___x_1791_ = l_Lean_ConstantInfo_instantiateTypeLevelParams(v_a_1790_, v_univs_1777_);
lean_dec(v_a_1790_);
v___x_1792_ = l_List_lengthTR___redArg(v_params_1778_);
lean_dec(v_params_1778_);
lean_inc(v___x_1792_);
v___f_1793_ = lean_alloc_closure((void*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__2___boxed), 11, 4);
lean_closure_set(v___f_1793_, 0, v___x_1792_);
lean_closure_set(v___f_1793_, 1, v___f_1787_);
lean_closure_set(v___f_1793_, 2, v_idxs_1779_);
lean_closure_set(v___f_1793_, 3, v___x_1788_);
v___x_1794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1794_, 0, v___x_1792_);
v___x_1795_ = 0;
v___x_1796_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__4___redArg(v___x_1791_, v___x_1794_, v___f_1786_, v___x_1795_, v___x_1795_, v_a_1781_, v_a_1782_, v_a_1783_, v_a_1784_);
if (lean_obj_tag(v___x_1796_) == 0)
{
lean_object* v_a_1797_; lean_object* v___x_1798_; 
v_a_1797_ = lean_ctor_get(v___x_1796_, 0);
lean_inc(v_a_1797_);
lean_dec_ref_known(v___x_1796_, 1);
v___x_1798_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__5___redArg(v_a_1797_, v___f_1793_, v___x_1795_, v_a_1781_, v_a_1782_, v_a_1783_, v_a_1784_);
return v___x_1798_;
}
else
{
lean_object* v_a_1799_; lean_object* v___x_1801_; uint8_t v_isShared_1802_; uint8_t v_isSharedCheck_1806_; 
lean_dec_ref(v___f_1793_);
v_a_1799_ = lean_ctor_get(v___x_1796_, 0);
v_isSharedCheck_1806_ = !lean_is_exclusive(v___x_1796_);
if (v_isSharedCheck_1806_ == 0)
{
v___x_1801_ = v___x_1796_;
v_isShared_1802_ = v_isSharedCheck_1806_;
goto v_resetjp_1800_;
}
else
{
lean_inc(v_a_1799_);
lean_dec(v___x_1796_);
v___x_1801_ = lean_box(0);
v_isShared_1802_ = v_isSharedCheck_1806_;
goto v_resetjp_1800_;
}
v_resetjp_1800_:
{
lean_object* v___x_1804_; 
if (v_isShared_1802_ == 0)
{
v___x_1804_ = v___x_1801_;
goto v_reusejp_1803_;
}
else
{
lean_object* v_reuseFailAlloc_1805_; 
v_reuseFailAlloc_1805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1805_, 0, v_a_1799_);
v___x_1804_ = v_reuseFailAlloc_1805_;
goto v_reusejp_1803_;
}
v_reusejp_1803_:
{
return v___x_1804_;
}
}
}
}
else
{
lean_object* v_a_1807_; lean_object* v___x_1809_; uint8_t v_isShared_1810_; uint8_t v_isSharedCheck_1814_; 
lean_dec_ref(v___f_1786_);
lean_dec(v_idxs_1779_);
lean_dec(v_params_1778_);
v_a_1807_ = lean_ctor_get(v___x_1789_, 0);
v_isSharedCheck_1814_ = !lean_is_exclusive(v___x_1789_);
if (v_isSharedCheck_1814_ == 0)
{
v___x_1809_ = v___x_1789_;
v_isShared_1810_ = v_isSharedCheck_1814_;
goto v_resetjp_1808_;
}
else
{
lean_inc(v_a_1807_);
lean_dec(v___x_1789_);
v___x_1809_ = lean_box(0);
v_isShared_1810_ = v_isSharedCheck_1814_;
goto v_resetjp_1808_;
}
v_resetjp_1808_:
{
lean_object* v___x_1812_; 
if (v_isShared_1810_ == 0)
{
v___x_1812_ = v___x_1809_;
goto v_reusejp_1811_;
}
else
{
lean_object* v_reuseFailAlloc_1813_; 
v_reuseFailAlloc_1813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1813_, 0, v_a_1807_);
v___x_1812_ = v_reuseFailAlloc_1813_;
goto v_reusejp_1811_;
}
v_reusejp_1811_:
{
return v___x_1812_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___boxed(lean_object* v_univs_1815_, lean_object* v_params_1816_, lean_object* v_idxs_1817_, lean_object* v_c_1818_, lean_object* v_a_1819_, lean_object* v_a_1820_, lean_object* v_a_1821_, lean_object* v_a_1822_, lean_object* v_a_1823_){
_start:
{
lean_object* v_res_1824_; 
v_res_1824_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp(v_univs_1815_, v_params_1816_, v_idxs_1817_, v_c_1818_, v_a_1819_, v_a_1820_, v_a_1821_, v_a_1822_);
lean_dec(v_a_1822_);
lean_dec_ref(v_a_1821_);
lean_dec(v_a_1820_);
lean_dec_ref(v_a_1819_);
lean_dec(v_univs_1815_);
return v_res_1824_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0(lean_object* v_00_u03b1_1825_, lean_object* v_constName_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_){
_start:
{
lean_object* v___x_1832_; 
v___x_1832_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0___redArg(v_constName_1826_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_);
return v___x_1832_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1833_, lean_object* v_constName_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_){
_start:
{
lean_object* v_res_1840_; 
v_res_1840_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0(v_00_u03b1_1833_, v_constName_1834_, v___y_1835_, v___y_1836_, v___y_1837_, v___y_1838_);
lean_dec(v___y_1838_);
lean_dec_ref(v___y_1837_);
lean_dec(v___y_1836_);
lean_dec_ref(v___y_1835_);
return v_res_1840_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3(lean_object* v_00_u03b1_1841_, lean_object* v_ref_1842_, lean_object* v_constName_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_){
_start:
{
lean_object* v___x_1849_; 
v___x_1849_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3___redArg(v_ref_1842_, v_constName_1843_, v___y_1844_, v___y_1845_, v___y_1846_, v___y_1847_);
return v___x_1849_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b1_1850_, lean_object* v_ref_1851_, lean_object* v_constName_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_){
_start:
{
lean_object* v_res_1858_; 
v_res_1858_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3(v_00_u03b1_1850_, v_ref_1851_, v_constName_1852_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_);
lean_dec(v___y_1856_);
lean_dec_ref(v___y_1855_);
lean_dec(v___y_1854_);
lean_dec_ref(v___y_1853_);
lean_dec(v_ref_1851_);
return v_res_1858_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7(lean_object* v_00_u03b1_1859_, lean_object* v_ref_1860_, lean_object* v_msg_1861_, lean_object* v_declHint_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_){
_start:
{
lean_object* v___x_1868_; 
v___x_1868_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7___redArg(v_ref_1860_, v_msg_1861_, v_declHint_1862_, v___y_1863_, v___y_1864_, v___y_1865_, v___y_1866_);
return v___x_1868_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7___boxed(lean_object* v_00_u03b1_1869_, lean_object* v_ref_1870_, lean_object* v_msg_1871_, lean_object* v_declHint_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_){
_start:
{
lean_object* v_res_1878_; 
v_res_1878_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7(v_00_u03b1_1869_, v_ref_1870_, v_msg_1871_, v_declHint_1872_, v___y_1873_, v___y_1874_, v___y_1875_, v___y_1876_);
lean_dec(v___y_1876_);
lean_dec_ref(v___y_1875_);
lean_dec(v___y_1874_);
lean_dec_ref(v___y_1873_);
lean_dec(v_ref_1870_);
return v_res_1878_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9(lean_object* v_msg_1879_, lean_object* v_declHint_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_){
_start:
{
lean_object* v___x_1886_; 
v___x_1886_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg(v_msg_1879_, v_declHint_1880_, v___y_1884_);
return v___x_1886_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___boxed(lean_object* v_msg_1887_, lean_object* v_declHint_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_){
_start:
{
lean_object* v_res_1894_; 
v_res_1894_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9(v_msg_1887_, v_declHint_1888_, v___y_1889_, v___y_1890_, v___y_1891_, v___y_1892_);
lean_dec(v___y_1892_);
lean_dec_ref(v___y_1891_);
lean_dec(v___y_1890_);
lean_dec_ref(v___y_1889_);
return v_res_1894_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__9(lean_object* v_00_u03b1_1895_, lean_object* v_ref_1896_, lean_object* v_msg_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_){
_start:
{
lean_object* v___x_1903_; 
v___x_1903_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__9___redArg(v_ref_1896_, v_msg_1897_, v___y_1898_, v___y_1899_, v___y_1900_, v___y_1901_);
return v___x_1903_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__9___boxed(lean_object* v_00_u03b1_1904_, lean_object* v_ref_1905_, lean_object* v_msg_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_){
_start:
{
lean_object* v_res_1912_; 
v_res_1912_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__9(v_00_u03b1_1904_, v_ref_1905_, v_msg_1906_, v___y_1907_, v___y_1908_, v___y_1909_, v___y_1910_);
lean_dec(v___y_1910_);
lean_dec_ref(v___y_1909_);
lean_dec(v___y_1908_);
lean_dec_ref(v___y_1907_);
lean_dec(v_ref_1905_);
return v_res_1912_;
}
}
static lean_object* _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__1___closed__5(void){
_start:
{
lean_object* v___x_1926_; 
v___x_1926_ = l_Array_mkArray0___redArg();
return v___x_1926_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__1(lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_){
_start:
{
lean_object* v_ref_1936_; uint8_t v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; 
v_ref_1936_ = lean_ctor_get(v___y_1933_, 2);
v___x_1937_ = 0;
v___x_1938_ = l_Lean_SourceInfo_fromRef(v_ref_1936_, v___x_1937_);
v___x_1939_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__1___closed__1));
v___x_1940_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__1___closed__2));
lean_inc_n(v___x_1938_, 3);
v___x_1941_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1941_, 0, v___x_1938_);
lean_ctor_set(v___x_1941_, 1, v___x_1940_);
v___x_1942_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__1___closed__4));
v___x_1943_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__10));
v___x_1944_ = lean_obj_once(&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__1___closed__5, &l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__1___closed__5_once, _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__1___closed__5);
v___x_1945_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1945_, 0, v___x_1938_);
lean_ctor_set(v___x_1945_, 1, v___x_1943_);
lean_ctor_set(v___x_1945_, 2, v___x_1944_);
v___x_1946_ = l_Lean_Syntax_node1(v___x_1938_, v___x_1942_, v___x_1945_);
v___x_1947_ = l_Lean_Syntax_node2(v___x_1938_, v___x_1939_, v___x_1941_, v___x_1946_);
v___x_1948_ = l_Lean_Elab_Tactic_evalTactic(v___x_1947_, v___y_1927_, v___y_1928_, v___y_1929_, v___y_1930_, v___y_1931_, v___y_1932_, v___y_1933_, v___y_1934_);
return v___x_1948_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__1___boxed(lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_){
_start:
{
lean_object* v_res_1958_; 
v_res_1958_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__1(v___y_1949_, v___y_1950_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_, v___y_1956_);
lean_dec(v___y_1956_);
lean_dec_ref(v___y_1955_);
lean_dec(v___y_1954_);
lean_dec_ref(v___y_1953_);
lean_dec(v___y_1952_);
lean_dec_ref(v___y_1951_);
lean_dec(v___y_1950_);
lean_dec_ref(v___y_1949_);
return v_res_1958_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__0(uint8_t v_isZero_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_){
_start:
{
lean_object* v_ref_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; 
v_ref_1969_ = lean_ctor_get(v___y_1966_, 2);
v___x_1970_ = l_Lean_SourceInfo_fromRef(v_ref_1969_, v_isZero_1959_);
v___x_1971_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__1___closed__1));
v___x_1972_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__1___closed__2));
lean_inc_n(v___x_1970_, 3);
v___x_1973_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1973_, 0, v___x_1970_);
lean_ctor_set(v___x_1973_, 1, v___x_1972_);
v___x_1974_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__1___closed__4));
v___x_1975_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__10));
v___x_1976_ = lean_obj_once(&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__1___closed__5, &l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__1___closed__5_once, _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__1___closed__5);
v___x_1977_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1977_, 0, v___x_1970_);
lean_ctor_set(v___x_1977_, 1, v___x_1975_);
lean_ctor_set(v___x_1977_, 2, v___x_1976_);
v___x_1978_ = l_Lean_Syntax_node1(v___x_1970_, v___x_1974_, v___x_1977_);
v___x_1979_ = l_Lean_Syntax_node2(v___x_1970_, v___x_1971_, v___x_1973_, v___x_1978_);
v___x_1980_ = l_Lean_Elab_Tactic_evalTactic(v___x_1979_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_, v___y_1964_, v___y_1965_, v___y_1966_, v___y_1967_);
return v___x_1980_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__0___boxed(lean_object* v_isZero_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_){
_start:
{
uint8_t v_isZero_boxed_1991_; lean_object* v_res_1992_; 
v_isZero_boxed_1991_ = lean_unbox(v_isZero_1981_);
v_res_1992_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__0(v_isZero_boxed_1991_, v___y_1982_, v___y_1983_, v___y_1984_, v___y_1985_, v___y_1986_, v___y_1987_, v___y_1988_, v___y_1989_);
lean_dec(v___y_1989_);
lean_dec_ref(v___y_1988_);
lean_dec(v___y_1987_);
lean_dec_ref(v___y_1986_);
lean_dec(v___y_1985_);
lean_dec_ref(v___y_1984_);
lean_dec(v___y_1983_);
lean_dec_ref(v___y_1982_);
return v_res_1992_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__2(uint8_t v_isZero_1993_, lean_object* v_x_1994_){
_start:
{
return v_isZero_1993_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__2___boxed(lean_object* v_isZero_1995_, lean_object* v_x_1996_){
_start:
{
uint8_t v_isZero_boxed_1997_; uint8_t v_res_1998_; lean_object* v_r_1999_; 
v_isZero_boxed_1997_ = lean_unbox(v_isZero_1995_);
v_res_1998_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__2(v_isZero_boxed_1997_, v_x_1996_);
lean_dec(v_x_1996_);
v_r_1999_ = lean_box(v_res_1998_);
return v_r_1999_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__3(uint8_t v_isZero_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_){
_start:
{
lean_object* v_ref_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; 
v_ref_2010_ = lean_ctor_get(v___y_2007_, 2);
v___x_2011_ = l_Lean_SourceInfo_fromRef(v_ref_2010_, v_isZero_2000_);
v___x_2012_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__3));
v___x_2013_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__4));
lean_inc_n(v___x_2011_, 9);
v___x_2014_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2014_, 0, v___x_2011_);
lean_ctor_set(v___x_2014_, 1, v___x_2012_);
v___x_2015_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__7));
v___x_2016_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__8));
v___x_2017_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2017_, 0, v___x_2011_);
lean_ctor_set(v___x_2017_, 1, v___x_2016_);
v___x_2018_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__10));
v___x_2019_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__12));
v___x_2020_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__13));
v___x_2021_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2021_, 0, v___x_2011_);
lean_ctor_set(v___x_2021_, 1, v___x_2020_);
v___x_2022_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__14));
v___x_2023_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2023_, 0, v___x_2011_);
lean_ctor_set(v___x_2023_, 1, v___x_2022_);
v___x_2024_ = l_Lean_Syntax_node2(v___x_2011_, v___x_2019_, v___x_2021_, v___x_2023_);
v___x_2025_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__15));
v___x_2026_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2026_, 0, v___x_2011_);
lean_ctor_set(v___x_2026_, 1, v___x_2025_);
lean_inc(v___x_2024_);
v___x_2027_ = l_Lean_Syntax_node3(v___x_2011_, v___x_2018_, v___x_2024_, v___x_2026_, v___x_2024_);
v___x_2028_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__16));
v___x_2029_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2029_, 0, v___x_2011_);
lean_ctor_set(v___x_2029_, 1, v___x_2028_);
v___x_2030_ = l_Lean_Syntax_node3(v___x_2011_, v___x_2015_, v___x_2017_, v___x_2027_, v___x_2029_);
v___x_2031_ = l_Lean_Syntax_node2(v___x_2011_, v___x_2013_, v___x_2014_, v___x_2030_);
v___x_2032_ = l_Lean_Elab_Tactic_evalTactic(v___x_2031_, v___y_2001_, v___y_2002_, v___y_2003_, v___y_2004_, v___y_2005_, v___y_2006_, v___y_2007_, v___y_2008_);
return v___x_2032_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__3___boxed(lean_object* v_isZero_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_){
_start:
{
uint8_t v_isZero_boxed_2043_; lean_object* v_res_2044_; 
v_isZero_boxed_2043_ = lean_unbox(v_isZero_2033_);
v_res_2044_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__3(v_isZero_boxed_2043_, v___y_2034_, v___y_2035_, v___y_2036_, v___y_2037_, v___y_2038_, v___y_2039_, v___y_2040_, v___y_2041_);
lean_dec(v___y_2041_);
lean_dec_ref(v___y_2040_);
lean_dec(v___y_2039_);
lean_dec_ref(v___y_2038_);
lean_dec(v___y_2037_);
lean_dec_ref(v___y_2036_);
lean_dec(v___y_2035_);
lean_dec_ref(v___y_2034_);
return v_res_2044_;
}
}
static lean_object* _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___closed__2(void){
_start:
{
lean_object* v___x_2047_; lean_object* v___x_2048_; 
v___x_2047_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___closed__1));
v___x_2048_ = l_Lean_stringToMessageData(v___x_2047_);
return v___x_2048_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor(lean_object* v_mvar_2049_, lean_object* v_n_2050_, lean_object* v_a_2051_, lean_object* v_a_2052_, lean_object* v_a_2053_, lean_object* v_a_2054_){
_start:
{
lean_object* v___y_2057_; lean_object* v___y_2058_; lean_object* v___y_2059_; lean_object* v___y_2060_; lean_object* v_zero_2063_; uint8_t v_isZero_2064_; 
v_zero_2063_ = lean_unsigned_to_nat(0u);
v_isZero_2064_ = lean_nat_dec_eq(v_n_2050_, v_zero_2063_);
if (v_isZero_2064_ == 1)
{
lean_object* v___f_2065_; lean_object* v___f_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; uint8_t v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; 
lean_dec(v_n_2050_);
v___f_2065_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___closed__2));
v___f_2066_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___closed__0));
v___x_2067_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_run___boxed), 9, 2);
lean_closure_set(v___x_2067_, 0, v_mvar_2049_);
lean_closure_set(v___x_2067_, 1, v___f_2066_);
v___x_2068_ = lean_box(0);
v___x_2069_ = lean_box(0);
v___x_2070_ = lean_box(1);
v___x_2071_ = 0;
v___x_2072_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___closed__4));
v___x_2073_ = lean_alloc_ctor(0, 8, 10);
lean_ctor_set(v___x_2073_, 0, v___x_2068_);
lean_ctor_set(v___x_2073_, 1, v___x_2069_);
lean_ctor_set(v___x_2073_, 2, v___x_2068_);
lean_ctor_set(v___x_2073_, 3, v___f_2065_);
lean_ctor_set(v___x_2073_, 4, v___x_2070_);
lean_ctor_set(v___x_2073_, 5, v___x_2070_);
lean_ctor_set(v___x_2073_, 6, v___x_2068_);
lean_ctor_set(v___x_2073_, 7, v___x_2072_);
lean_ctor_set_uint8(v___x_2073_, sizeof(void*)*8, v_isZero_2064_);
lean_ctor_set_uint8(v___x_2073_, sizeof(void*)*8 + 1, v_isZero_2064_);
lean_ctor_set_uint8(v___x_2073_, sizeof(void*)*8 + 2, v_isZero_2064_);
lean_ctor_set_uint8(v___x_2073_, sizeof(void*)*8 + 3, v_isZero_2064_);
lean_ctor_set_uint8(v___x_2073_, sizeof(void*)*8 + 4, v___x_2071_);
lean_ctor_set_uint8(v___x_2073_, sizeof(void*)*8 + 5, v___x_2071_);
lean_ctor_set_uint8(v___x_2073_, sizeof(void*)*8 + 6, v___x_2071_);
lean_ctor_set_uint8(v___x_2073_, sizeof(void*)*8 + 7, v___x_2071_);
lean_ctor_set_uint8(v___x_2073_, sizeof(void*)*8 + 8, v_isZero_2064_);
lean_ctor_set_uint8(v___x_2073_, sizeof(void*)*8 + 9, v___x_2071_);
v___x_2074_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___closed__6));
v___x_2075_ = l_Lean_Elab_Term_TermElabM_run___redArg(v___x_2067_, v___x_2073_, v___x_2074_, v_a_2051_, v_a_2052_, v_a_2053_, v_a_2054_);
if (lean_obj_tag(v___x_2075_) == 0)
{
lean_object* v_a_2076_; lean_object* v___x_2078_; uint8_t v_isShared_2079_; uint8_t v_isSharedCheck_2087_; 
v_a_2076_ = lean_ctor_get(v___x_2075_, 0);
v_isSharedCheck_2087_ = !lean_is_exclusive(v___x_2075_);
if (v_isSharedCheck_2087_ == 0)
{
v___x_2078_ = v___x_2075_;
v_isShared_2079_ = v_isSharedCheck_2087_;
goto v_resetjp_2077_;
}
else
{
lean_inc(v_a_2076_);
lean_dec(v___x_2075_);
v___x_2078_ = lean_box(0);
v_isShared_2079_ = v_isSharedCheck_2087_;
goto v_resetjp_2077_;
}
v_resetjp_2077_:
{
lean_object* v_fst_2080_; 
v_fst_2080_ = lean_ctor_get(v_a_2076_, 0);
lean_inc(v_fst_2080_);
lean_dec(v_a_2076_);
if (lean_obj_tag(v_fst_2080_) == 0)
{
lean_object* v___x_2081_; lean_object* v___x_2083_; 
v___x_2081_ = lean_box(0);
if (v_isShared_2079_ == 0)
{
lean_ctor_set(v___x_2078_, 0, v___x_2081_);
v___x_2083_ = v___x_2078_;
goto v_reusejp_2082_;
}
else
{
lean_object* v_reuseFailAlloc_2084_; 
v_reuseFailAlloc_2084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2084_, 0, v___x_2081_);
v___x_2083_ = v_reuseFailAlloc_2084_;
goto v_reusejp_2082_;
}
v_reusejp_2082_:
{
return v___x_2083_;
}
}
else
{
lean_object* v___x_2085_; lean_object* v___x_2086_; 
lean_dec(v_fst_2080_);
lean_del_object(v___x_2078_);
v___x_2085_ = lean_obj_once(&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___closed__2, &l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___closed__2_once, _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___closed__2);
v___x_2086_ = l_Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0___redArg(v___x_2085_, v_a_2051_, v_a_2052_, v_a_2053_, v_a_2054_);
return v___x_2086_;
}
}
}
else
{
lean_object* v_a_2088_; lean_object* v___x_2090_; uint8_t v_isShared_2091_; uint8_t v_isSharedCheck_2095_; 
v_a_2088_ = lean_ctor_get(v___x_2075_, 0);
v_isSharedCheck_2095_ = !lean_is_exclusive(v___x_2075_);
if (v_isSharedCheck_2095_ == 0)
{
v___x_2090_ = v___x_2075_;
v_isShared_2091_ = v_isSharedCheck_2095_;
goto v_resetjp_2089_;
}
else
{
lean_inc(v_a_2088_);
lean_dec(v___x_2075_);
v___x_2090_ = lean_box(0);
v_isShared_2091_ = v_isSharedCheck_2095_;
goto v_resetjp_2089_;
}
v_resetjp_2089_:
{
lean_object* v___x_2093_; 
if (v_isShared_2091_ == 0)
{
v___x_2093_ = v___x_2090_;
goto v_reusejp_2092_;
}
else
{
lean_object* v_reuseFailAlloc_2094_; 
v_reuseFailAlloc_2094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2094_, 0, v_a_2088_);
v___x_2093_ = v_reuseFailAlloc_2094_;
goto v_reusejp_2092_;
}
v_reusejp_2092_:
{
return v___x_2093_;
}
}
}
}
else
{
lean_object* v___x_2096_; lean_object* v___f_2097_; lean_object* v___x_2098_; lean_object* v___f_2099_; lean_object* v___x_2100_; lean_object* v___f_2101_; lean_object* v_one_2102_; lean_object* v_n_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; uint8_t v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; 
v___x_2096_ = lean_box(v_isZero_2064_);
v___f_2097_ = lean_alloc_closure((void*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__0___boxed), 10, 1);
lean_closure_set(v___f_2097_, 0, v___x_2096_);
v___x_2098_ = lean_box(v_isZero_2064_);
v___f_2099_ = lean_alloc_closure((void*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__2___boxed), 2, 1);
lean_closure_set(v___f_2099_, 0, v___x_2098_);
v___x_2100_ = lean_box(v_isZero_2064_);
v___f_2101_ = lean_alloc_closure((void*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__3___boxed), 10, 1);
lean_closure_set(v___f_2101_, 0, v___x_2100_);
v_one_2102_ = lean_unsigned_to_nat(1u);
v_n_2103_ = lean_nat_sub(v_n_2050_, v_one_2102_);
lean_dec(v_n_2050_);
v___x_2104_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_run___boxed), 9, 2);
lean_closure_set(v___x_2104_, 0, v_mvar_2049_);
lean_closure_set(v___x_2104_, 1, v___f_2101_);
v___x_2105_ = lean_box(0);
v___x_2106_ = lean_box(0);
v___x_2107_ = 1;
v___x_2108_ = lean_box(1);
v___x_2109_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___closed__4));
v___x_2110_ = lean_alloc_ctor(0, 8, 10);
lean_ctor_set(v___x_2110_, 0, v___x_2105_);
lean_ctor_set(v___x_2110_, 1, v___x_2106_);
lean_ctor_set(v___x_2110_, 2, v___x_2105_);
lean_ctor_set(v___x_2110_, 3, v___f_2099_);
lean_ctor_set(v___x_2110_, 4, v___x_2108_);
lean_ctor_set(v___x_2110_, 5, v___x_2108_);
lean_ctor_set(v___x_2110_, 6, v___x_2105_);
lean_ctor_set(v___x_2110_, 7, v___x_2109_);
lean_ctor_set_uint8(v___x_2110_, sizeof(void*)*8, v___x_2107_);
lean_ctor_set_uint8(v___x_2110_, sizeof(void*)*8 + 1, v___x_2107_);
lean_ctor_set_uint8(v___x_2110_, sizeof(void*)*8 + 2, v___x_2107_);
lean_ctor_set_uint8(v___x_2110_, sizeof(void*)*8 + 3, v___x_2107_);
lean_ctor_set_uint8(v___x_2110_, sizeof(void*)*8 + 4, v_isZero_2064_);
lean_ctor_set_uint8(v___x_2110_, sizeof(void*)*8 + 5, v_isZero_2064_);
lean_ctor_set_uint8(v___x_2110_, sizeof(void*)*8 + 6, v_isZero_2064_);
lean_ctor_set_uint8(v___x_2110_, sizeof(void*)*8 + 7, v_isZero_2064_);
lean_ctor_set_uint8(v___x_2110_, sizeof(void*)*8 + 8, v___x_2107_);
lean_ctor_set_uint8(v___x_2110_, sizeof(void*)*8 + 9, v_isZero_2064_);
v___x_2111_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___closed__6));
lean_inc_ref(v___x_2110_);
v___x_2112_ = l_Lean_Elab_Term_TermElabM_run___redArg(v___x_2104_, v___x_2110_, v___x_2111_, v_a_2051_, v_a_2052_, v_a_2053_, v_a_2054_);
if (lean_obj_tag(v___x_2112_) == 0)
{
lean_object* v_a_2113_; lean_object* v_fst_2114_; 
v_a_2113_ = lean_ctor_get(v___x_2112_, 0);
lean_inc(v_a_2113_);
lean_dec_ref_known(v___x_2112_, 1);
v_fst_2114_ = lean_ctor_get(v_a_2113_, 0);
lean_inc(v_fst_2114_);
lean_dec(v_a_2113_);
if (lean_obj_tag(v_fst_2114_) == 1)
{
lean_object* v_tail_2115_; 
v_tail_2115_ = lean_ctor_get(v_fst_2114_, 1);
lean_inc(v_tail_2115_);
if (lean_obj_tag(v_tail_2115_) == 1)
{
lean_object* v_tail_2116_; 
v_tail_2116_ = lean_ctor_get(v_tail_2115_, 1);
if (lean_obj_tag(v_tail_2116_) == 0)
{
lean_object* v_head_2117_; lean_object* v_head_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; 
v_head_2117_ = lean_ctor_get(v_fst_2114_, 0);
lean_inc(v_head_2117_);
lean_dec_ref_known(v_fst_2114_, 2);
v_head_2118_ = lean_ctor_get(v_tail_2115_, 0);
lean_inc(v_head_2118_);
lean_dec_ref_known(v_tail_2115_, 2);
v___x_2119_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_run___boxed), 9, 2);
lean_closure_set(v___x_2119_, 0, v_head_2117_);
lean_closure_set(v___x_2119_, 1, v___f_2097_);
v___x_2120_ = l_Lean_Elab_Term_TermElabM_run___redArg(v___x_2119_, v___x_2110_, v___x_2111_, v_a_2051_, v_a_2052_, v_a_2053_, v_a_2054_);
if (lean_obj_tag(v___x_2120_) == 0)
{
lean_object* v_a_2121_; lean_object* v_fst_2122_; 
v_a_2121_ = lean_ctor_get(v___x_2120_, 0);
lean_inc(v_a_2121_);
lean_dec_ref_known(v___x_2120_, 1);
v_fst_2122_ = lean_ctor_get(v_a_2121_, 0);
lean_inc(v_fst_2122_);
lean_dec(v_a_2121_);
if (lean_obj_tag(v_fst_2122_) == 0)
{
v_mvar_2049_ = v_head_2118_;
v_n_2050_ = v_n_2103_;
goto _start;
}
else
{
lean_object* v___x_2124_; lean_object* v___x_2125_; 
lean_dec(v_fst_2122_);
lean_dec(v_head_2118_);
lean_dec(v_n_2103_);
v___x_2124_ = lean_obj_once(&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___closed__2, &l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___closed__2_once, _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___closed__2);
v___x_2125_ = l_Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0___redArg(v___x_2124_, v_a_2051_, v_a_2052_, v_a_2053_, v_a_2054_);
return v___x_2125_;
}
}
else
{
lean_object* v_a_2126_; lean_object* v___x_2128_; uint8_t v_isShared_2129_; uint8_t v_isSharedCheck_2133_; 
lean_dec(v_head_2118_);
lean_dec(v_n_2103_);
v_a_2126_ = lean_ctor_get(v___x_2120_, 0);
v_isSharedCheck_2133_ = !lean_is_exclusive(v___x_2120_);
if (v_isSharedCheck_2133_ == 0)
{
v___x_2128_ = v___x_2120_;
v_isShared_2129_ = v_isSharedCheck_2133_;
goto v_resetjp_2127_;
}
else
{
lean_inc(v_a_2126_);
lean_dec(v___x_2120_);
v___x_2128_ = lean_box(0);
v_isShared_2129_ = v_isSharedCheck_2133_;
goto v_resetjp_2127_;
}
v_resetjp_2127_:
{
lean_object* v___x_2131_; 
if (v_isShared_2129_ == 0)
{
v___x_2131_ = v___x_2128_;
goto v_reusejp_2130_;
}
else
{
lean_object* v_reuseFailAlloc_2132_; 
v_reuseFailAlloc_2132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2132_, 0, v_a_2126_);
v___x_2131_ = v_reuseFailAlloc_2132_;
goto v_reusejp_2130_;
}
v_reusejp_2130_:
{
return v___x_2131_;
}
}
}
}
else
{
lean_dec_ref_known(v_tail_2115_, 2);
lean_dec_ref_known(v_fst_2114_, 2);
lean_dec_ref_known(v___x_2110_, 8);
lean_dec(v_n_2103_);
lean_dec_ref(v___f_2097_);
v___y_2057_ = v_a_2051_;
v___y_2058_ = v_a_2052_;
v___y_2059_ = v_a_2053_;
v___y_2060_ = v_a_2054_;
goto v___jp_2056_;
}
}
else
{
lean_dec(v_tail_2115_);
lean_dec_ref_known(v_fst_2114_, 2);
lean_dec_ref_known(v___x_2110_, 8);
lean_dec(v_n_2103_);
lean_dec_ref(v___f_2097_);
v___y_2057_ = v_a_2051_;
v___y_2058_ = v_a_2052_;
v___y_2059_ = v_a_2053_;
v___y_2060_ = v_a_2054_;
goto v___jp_2056_;
}
}
else
{
lean_dec(v_fst_2114_);
lean_dec_ref_known(v___x_2110_, 8);
lean_dec(v_n_2103_);
lean_dec_ref(v___f_2097_);
v___y_2057_ = v_a_2051_;
v___y_2058_ = v_a_2052_;
v___y_2059_ = v_a_2053_;
v___y_2060_ = v_a_2054_;
goto v___jp_2056_;
}
}
else
{
lean_object* v_a_2134_; lean_object* v___x_2136_; uint8_t v_isShared_2137_; uint8_t v_isSharedCheck_2141_; 
lean_dec_ref_known(v___x_2110_, 8);
lean_dec(v_n_2103_);
lean_dec_ref(v___f_2097_);
v_a_2134_ = lean_ctor_get(v___x_2112_, 0);
v_isSharedCheck_2141_ = !lean_is_exclusive(v___x_2112_);
if (v_isSharedCheck_2141_ == 0)
{
v___x_2136_ = v___x_2112_;
v_isShared_2137_ = v_isSharedCheck_2141_;
goto v_resetjp_2135_;
}
else
{
lean_inc(v_a_2134_);
lean_dec(v___x_2112_);
v___x_2136_ = lean_box(0);
v_isShared_2137_ = v_isSharedCheck_2141_;
goto v_resetjp_2135_;
}
v_resetjp_2135_:
{
lean_object* v___x_2139_; 
if (v_isShared_2137_ == 0)
{
v___x_2139_ = v___x_2136_;
goto v_reusejp_2138_;
}
else
{
lean_object* v_reuseFailAlloc_2140_; 
v_reuseFailAlloc_2140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2140_, 0, v_a_2134_);
v___x_2139_ = v_reuseFailAlloc_2140_;
goto v_reusejp_2138_;
}
v_reusejp_2138_:
{
return v___x_2139_;
}
}
}
}
v___jp_2056_:
{
lean_object* v___x_2061_; lean_object* v___x_2062_; 
v___x_2061_ = lean_obj_once(&l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___closed__1, &l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___closed__1_once, _init_l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___closed__1);
v___x_2062_ = l_Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0___redArg(v___x_2061_, v___y_2057_, v___y_2058_, v___y_2059_, v___y_2060_);
return v___x_2062_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___boxed(lean_object* v_mvar_2142_, lean_object* v_n_2143_, lean_object* v_a_2144_, lean_object* v_a_2145_, lean_object* v_a_2146_, lean_object* v_a_2147_, lean_object* v_a_2148_){
_start:
{
lean_object* v_res_2149_; 
v_res_2149_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor(v_mvar_2142_, v_n_2143_, v_a_2144_, v_a_2145_, v_a_2146_, v_a_2147_);
lean_dec(v_a_2147_);
lean_dec_ref(v_a_2146_);
lean_dec(v_a_2145_);
lean_dec_ref(v_a_2144_);
return v_res_2149_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toCases___lam__0(lean_object* v_fst_2150_, lean_object* v_snd_2151_){
_start:
{
lean_object* v___x_2152_; 
v___x_2152_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2152_, 0, v_fst_2150_);
lean_ctor_set(v___x_2152_, 1, v_snd_2151_);
return v___x_2152_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toCases_spec__0(lean_object* v_a_2153_, lean_object* v_a_2154_){
_start:
{
if (lean_obj_tag(v_a_2153_) == 0)
{
lean_object* v___x_2155_; 
v___x_2155_ = lean_array_to_list(v_a_2154_);
return v___x_2155_;
}
else
{
lean_object* v_head_2156_; lean_object* v_fst_2157_; uint8_t v___x_2158_; 
v_head_2156_ = lean_ctor_get(v_a_2153_, 0);
v_fst_2157_ = lean_ctor_get(v_head_2156_, 0);
v___x_2158_ = lean_unbox(v_fst_2157_);
if (v___x_2158_ == 0)
{
lean_object* v_tail_2159_; 
v_tail_2159_ = lean_ctor_get(v_a_2153_, 1);
lean_inc(v_tail_2159_);
lean_dec_ref_known(v_a_2153_, 2);
v_a_2153_ = v_tail_2159_;
goto _start;
}
else
{
lean_object* v_tail_2161_; lean_object* v_snd_2162_; lean_object* v___x_2163_; 
lean_inc(v_head_2156_);
v_tail_2161_ = lean_ctor_get(v_a_2153_, 1);
lean_inc(v_tail_2161_);
lean_dec_ref_known(v_a_2153_, 2);
v_snd_2162_ = lean_ctor_get(v_head_2156_, 1);
lean_inc(v_snd_2162_);
lean_dec(v_head_2156_);
v___x_2163_ = lean_array_push(v_a_2154_, v_snd_2162_);
v_a_2153_ = v_tail_2161_;
v_a_2154_ = v___x_2163_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toCases_spec__1___lam__0(uint8_t v_fst_2165_, lean_object* v_snd_2166_){
_start:
{
lean_object* v___x_2167_; lean_object* v___x_2168_; 
v___x_2167_ = lean_box(v_fst_2165_);
v___x_2168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2168_, 0, v___x_2167_);
lean_ctor_set(v___x_2168_, 1, v_snd_2166_);
return v___x_2168_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toCases_spec__1___lam__0___boxed(lean_object* v_fst_2169_, lean_object* v_snd_2170_){
_start:
{
uint8_t v_fst_boxed_2171_; lean_object* v_res_2172_; 
v_fst_boxed_2171_ = lean_unbox(v_fst_2169_);
v_res_2172_ = l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toCases_spec__1___lam__0(v_fst_boxed_2171_, v_snd_2170_);
return v_res_2172_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toCases_spec__1(lean_object* v_a_2176_, lean_object* v_x_2177_, lean_object* v_x_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_){
_start:
{
if (lean_obj_tag(v_x_2177_) == 0)
{
lean_object* v___x_2184_; lean_object* v___x_2185_; 
v___x_2184_ = l_List_reverse___redArg(v_x_2178_);
v___x_2185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2185_, 0, v___x_2184_);
return v___x_2185_;
}
else
{
lean_object* v_head_2186_; lean_object* v_tail_2187_; lean_object* v___x_2189_; uint8_t v_isShared_2190_; uint8_t v_isSharedCheck_2263_; 
v_head_2186_ = lean_ctor_get(v_x_2177_, 0);
v_tail_2187_ = lean_ctor_get(v_x_2177_, 1);
v_isSharedCheck_2263_ = !lean_is_exclusive(v_x_2177_);
if (v_isSharedCheck_2263_ == 0)
{
v___x_2189_ = v_x_2177_;
v_isShared_2190_ = v_isSharedCheck_2263_;
goto v_resetjp_2188_;
}
else
{
lean_inc(v_tail_2187_);
lean_inc(v_head_2186_);
lean_dec(v_x_2177_);
v___x_2189_ = lean_box(0);
v_isShared_2190_ = v_isSharedCheck_2263_;
goto v_resetjp_2188_;
}
v_resetjp_2188_:
{
lean_object* v___y_2192_; lean_object* v_fst_2206_; lean_object* v_fst_2207_; lean_object* v_snd_2208_; lean_object* v_toInductionSubgoal_2209_; lean_object* v_snd_2210_; lean_object* v_variablesKept_2211_; lean_object* v_neqs_2212_; lean_object* v_mvarId_2213_; lean_object* v_fields_2214_; lean_object* v___f_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; 
v_fst_2206_ = lean_ctor_get(v_head_2186_, 0);
v_fst_2207_ = lean_ctor_get(v_fst_2206_, 0);
lean_inc(v_fst_2207_);
v_snd_2208_ = lean_ctor_get(v_fst_2206_, 1);
v_toInductionSubgoal_2209_ = lean_ctor_get(v_snd_2208_, 0);
lean_inc_ref(v_toInductionSubgoal_2209_);
v_snd_2210_ = lean_ctor_get(v_head_2186_, 1);
lean_inc(v_snd_2210_);
lean_dec(v_head_2186_);
v_variablesKept_2211_ = lean_ctor_get(v_fst_2207_, 0);
lean_inc_n(v_variablesKept_2211_, 2);
v_neqs_2212_ = lean_ctor_get(v_fst_2207_, 1);
lean_inc(v_neqs_2212_);
lean_dec(v_fst_2207_);
v_mvarId_2213_ = lean_ctor_get(v_toInductionSubgoal_2209_, 0);
lean_inc(v_mvarId_2213_);
v_fields_2214_ = lean_ctor_get(v_toInductionSubgoal_2209_, 1);
lean_inc_ref_n(v_fields_2214_, 2);
lean_dec_ref(v_toInductionSubgoal_2209_);
v___f_2215_ = ((lean_object*)(l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toCases_spec__1___closed__0));
v___x_2216_ = l_Lean_instInhabitedExpr;
v___x_2217_ = lean_array_to_list(v_fields_2214_);
v___x_2218_ = ((lean_object*)(l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toCases_spec__1___closed__1));
v___x_2219_ = l___private_Init_Data_List_Impl_0__List_zipWithTR_go(lean_box(0), lean_box(0), lean_box(0), v___f_2215_, v_variablesKept_2211_, v___x_2217_, v___x_2218_);
v___x_2220_ = l_List_filterMapTR_go___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toCases_spec__0(v___x_2219_, v___x_2218_);
v___x_2221_ = lean_array_get_size(v_a_2176_);
v___x_2222_ = lean_unsigned_to_nat(1u);
v___x_2223_ = lean_nat_sub(v___x_2221_, v___x_2222_);
v___x_2224_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select(v_snd_2210_, v___x_2223_, v_mvarId_2213_, v___y_2179_, v___y_2180_, v___y_2181_, v___y_2182_);
if (lean_obj_tag(v___x_2224_) == 0)
{
if (lean_obj_tag(v_neqs_2212_) == 0)
{
lean_object* v_a_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; 
v_a_2225_ = lean_ctor_get(v___x_2224_, 0);
lean_inc(v_a_2225_);
lean_dec_ref_known(v___x_2224_, 1);
v___x_2226_ = l_List_lengthTR___redArg(v_variablesKept_2211_);
lean_dec(v_variablesKept_2211_);
v___x_2227_ = lean_nat_sub(v___x_2226_, v___x_2222_);
lean_dec(v___x_2226_);
v___x_2228_ = lean_array_get(v___x_2216_, v_fields_2214_, v___x_2227_);
lean_dec(v___x_2227_);
lean_dec_ref(v_fields_2214_);
v___x_2229_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_List_init___redArg(v___x_2220_);
v___x_2230_ = l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2(v_a_2225_, v___x_2229_, v___y_2179_, v___y_2180_, v___y_2181_, v___y_2182_);
if (lean_obj_tag(v___x_2230_) == 0)
{
lean_object* v_a_2231_; lean_object* v___x_2232_; 
v_a_2231_ = lean_ctor_get(v___x_2230_, 0);
lean_inc(v_a_2231_);
lean_dec_ref_known(v___x_2230_, 1);
v___x_2232_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1___redArg(v_a_2231_, v___x_2228_, v___y_2180_);
v___y_2192_ = v___x_2232_;
goto v___jp_2191_;
}
else
{
lean_object* v_a_2233_; lean_object* v___x_2235_; uint8_t v_isShared_2236_; uint8_t v_isSharedCheck_2240_; 
lean_dec(v___x_2228_);
lean_del_object(v___x_2189_);
lean_dec(v_tail_2187_);
lean_dec(v_x_2178_);
v_a_2233_ = lean_ctor_get(v___x_2230_, 0);
v_isSharedCheck_2240_ = !lean_is_exclusive(v___x_2230_);
if (v_isSharedCheck_2240_ == 0)
{
v___x_2235_ = v___x_2230_;
v_isShared_2236_ = v_isSharedCheck_2240_;
goto v_resetjp_2234_;
}
else
{
lean_inc(v_a_2233_);
lean_dec(v___x_2230_);
v___x_2235_ = lean_box(0);
v_isShared_2236_ = v_isSharedCheck_2240_;
goto v_resetjp_2234_;
}
v_resetjp_2234_:
{
lean_object* v___x_2238_; 
if (v_isShared_2236_ == 0)
{
v___x_2238_ = v___x_2235_;
goto v_reusejp_2237_;
}
else
{
lean_object* v_reuseFailAlloc_2239_; 
v_reuseFailAlloc_2239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2239_, 0, v_a_2233_);
v___x_2238_ = v_reuseFailAlloc_2239_;
goto v_reusejp_2237_;
}
v_reusejp_2237_:
{
return v___x_2238_;
}
}
}
}
else
{
lean_object* v_a_2241_; lean_object* v_val_2242_; lean_object* v___x_2243_; 
lean_dec_ref(v_fields_2214_);
lean_dec(v_variablesKept_2211_);
v_a_2241_ = lean_ctor_get(v___x_2224_, 0);
lean_inc(v_a_2241_);
lean_dec_ref_known(v___x_2224_, 1);
v_val_2242_ = lean_ctor_get(v_neqs_2212_, 0);
lean_inc(v_val_2242_);
lean_dec_ref_known(v_neqs_2212_, 1);
v___x_2243_ = l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2(v_a_2241_, v___x_2220_, v___y_2179_, v___y_2180_, v___y_2181_, v___y_2182_);
if (lean_obj_tag(v___x_2243_) == 0)
{
lean_object* v_a_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; 
v_a_2244_ = lean_ctor_get(v___x_2243_, 0);
lean_inc(v_a_2244_);
lean_dec_ref_known(v___x_2243_, 1);
v___x_2245_ = lean_nat_sub(v_val_2242_, v___x_2222_);
lean_dec(v_val_2242_);
v___x_2246_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor(v_a_2244_, v___x_2245_, v___y_2179_, v___y_2180_, v___y_2181_, v___y_2182_);
v___y_2192_ = v___x_2246_;
goto v___jp_2191_;
}
else
{
lean_object* v_a_2247_; lean_object* v___x_2249_; uint8_t v_isShared_2250_; uint8_t v_isSharedCheck_2254_; 
lean_dec(v_val_2242_);
lean_del_object(v___x_2189_);
lean_dec(v_tail_2187_);
lean_dec(v_x_2178_);
v_a_2247_ = lean_ctor_get(v___x_2243_, 0);
v_isSharedCheck_2254_ = !lean_is_exclusive(v___x_2243_);
if (v_isSharedCheck_2254_ == 0)
{
v___x_2249_ = v___x_2243_;
v_isShared_2250_ = v_isSharedCheck_2254_;
goto v_resetjp_2248_;
}
else
{
lean_inc(v_a_2247_);
lean_dec(v___x_2243_);
v___x_2249_ = lean_box(0);
v_isShared_2250_ = v_isSharedCheck_2254_;
goto v_resetjp_2248_;
}
v_resetjp_2248_:
{
lean_object* v___x_2252_; 
if (v_isShared_2250_ == 0)
{
v___x_2252_ = v___x_2249_;
goto v_reusejp_2251_;
}
else
{
lean_object* v_reuseFailAlloc_2253_; 
v_reuseFailAlloc_2253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2253_, 0, v_a_2247_);
v___x_2252_ = v_reuseFailAlloc_2253_;
goto v_reusejp_2251_;
}
v_reusejp_2251_:
{
return v___x_2252_;
}
}
}
}
}
else
{
lean_object* v_a_2255_; lean_object* v___x_2257_; uint8_t v_isShared_2258_; uint8_t v_isSharedCheck_2262_; 
lean_dec(v___x_2220_);
lean_dec_ref(v_fields_2214_);
lean_dec(v_neqs_2212_);
lean_dec(v_variablesKept_2211_);
lean_del_object(v___x_2189_);
lean_dec(v_tail_2187_);
lean_dec(v_x_2178_);
v_a_2255_ = lean_ctor_get(v___x_2224_, 0);
v_isSharedCheck_2262_ = !lean_is_exclusive(v___x_2224_);
if (v_isSharedCheck_2262_ == 0)
{
v___x_2257_ = v___x_2224_;
v_isShared_2258_ = v_isSharedCheck_2262_;
goto v_resetjp_2256_;
}
else
{
lean_inc(v_a_2255_);
lean_dec(v___x_2224_);
v___x_2257_ = lean_box(0);
v_isShared_2258_ = v_isSharedCheck_2262_;
goto v_resetjp_2256_;
}
v_resetjp_2256_:
{
lean_object* v___x_2260_; 
if (v_isShared_2258_ == 0)
{
v___x_2260_ = v___x_2257_;
goto v_reusejp_2259_;
}
else
{
lean_object* v_reuseFailAlloc_2261_; 
v_reuseFailAlloc_2261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2261_, 0, v_a_2255_);
v___x_2260_ = v_reuseFailAlloc_2261_;
goto v_reusejp_2259_;
}
v_reusejp_2259_:
{
return v___x_2260_;
}
}
}
v___jp_2191_:
{
if (lean_obj_tag(v___y_2192_) == 0)
{
lean_object* v_a_2193_; lean_object* v___x_2195_; 
v_a_2193_ = lean_ctor_get(v___y_2192_, 0);
lean_inc(v_a_2193_);
lean_dec_ref_known(v___y_2192_, 1);
if (v_isShared_2190_ == 0)
{
lean_ctor_set(v___x_2189_, 1, v_x_2178_);
lean_ctor_set(v___x_2189_, 0, v_a_2193_);
v___x_2195_ = v___x_2189_;
goto v_reusejp_2194_;
}
else
{
lean_object* v_reuseFailAlloc_2197_; 
v_reuseFailAlloc_2197_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2197_, 0, v_a_2193_);
lean_ctor_set(v_reuseFailAlloc_2197_, 1, v_x_2178_);
v___x_2195_ = v_reuseFailAlloc_2197_;
goto v_reusejp_2194_;
}
v_reusejp_2194_:
{
v_x_2177_ = v_tail_2187_;
v_x_2178_ = v___x_2195_;
goto _start;
}
}
else
{
lean_object* v_a_2198_; lean_object* v___x_2200_; uint8_t v_isShared_2201_; uint8_t v_isSharedCheck_2205_; 
lean_del_object(v___x_2189_);
lean_dec(v_tail_2187_);
lean_dec(v_x_2178_);
v_a_2198_ = lean_ctor_get(v___y_2192_, 0);
v_isSharedCheck_2205_ = !lean_is_exclusive(v___y_2192_);
if (v_isSharedCheck_2205_ == 0)
{
v___x_2200_ = v___y_2192_;
v_isShared_2201_ = v_isSharedCheck_2205_;
goto v_resetjp_2199_;
}
else
{
lean_inc(v_a_2198_);
lean_dec(v___y_2192_);
v___x_2200_ = lean_box(0);
v_isShared_2201_ = v_isSharedCheck_2205_;
goto v_resetjp_2199_;
}
v_resetjp_2199_:
{
lean_object* v___x_2203_; 
if (v_isShared_2201_ == 0)
{
v___x_2203_ = v___x_2200_;
goto v_reusejp_2202_;
}
else
{
lean_object* v_reuseFailAlloc_2204_; 
v_reuseFailAlloc_2204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2204_, 0, v_a_2198_);
v___x_2203_ = v_reuseFailAlloc_2204_;
goto v_reusejp_2202_;
}
v_reusejp_2202_:
{
return v___x_2203_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toCases_spec__1___boxed(lean_object* v_a_2264_, lean_object* v_x_2265_, lean_object* v_x_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_){
_start:
{
lean_object* v_res_2272_; 
v_res_2272_ = l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toCases_spec__1(v_a_2264_, v_x_2265_, v_x_2266_, v___y_2267_, v___y_2268_, v___y_2269_, v___y_2270_);
lean_dec(v___y_2270_);
lean_dec_ref(v___y_2269_);
lean_dec(v___y_2268_);
lean_dec_ref(v___y_2267_);
lean_dec_ref(v_a_2264_);
return v_res_2272_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toCases(lean_object* v_mvar_2276_, lean_object* v_shape_2277_, lean_object* v_a_2278_, lean_object* v_a_2279_, lean_object* v_a_2280_, lean_object* v_a_2281_){
_start:
{
lean_object* v___f_2283_; uint8_t v___x_2284_; lean_object* v___x_2285_; 
v___f_2283_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toCases___closed__0));
v___x_2284_ = 0;
v___x_2285_ = l_Lean_Meta_intro1Core(v_mvar_2276_, v___x_2284_, v_a_2278_, v_a_2279_, v_a_2280_, v_a_2281_);
if (lean_obj_tag(v___x_2285_) == 0)
{
lean_object* v_a_2286_; lean_object* v_fst_2287_; lean_object* v_snd_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; 
v_a_2286_ = lean_ctor_get(v___x_2285_, 0);
lean_inc(v_a_2286_);
lean_dec_ref_known(v___x_2285_, 1);
v_fst_2287_ = lean_ctor_get(v_a_2286_, 0);
lean_inc(v_fst_2287_);
v_snd_2288_ = lean_ctor_get(v_a_2286_, 1);
lean_inc(v_snd_2288_);
lean_dec(v_a_2286_);
v___x_2289_ = lean_unsigned_to_nat(0u);
v___x_2290_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toCases___closed__1));
v___x_2291_ = lean_box(0);
v___x_2292_ = l_Lean_MVarId_cases(v_snd_2288_, v_fst_2287_, v___x_2290_, v___x_2284_, v___x_2291_, v_a_2278_, v_a_2279_, v_a_2280_, v_a_2281_);
if (lean_obj_tag(v___x_2292_) == 0)
{
lean_object* v_a_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; 
v_a_2293_ = lean_ctor_get(v___x_2292_, 0);
lean_inc_n(v_a_2293_, 2);
lean_dec_ref_known(v___x_2292_, 1);
v___x_2294_ = lean_array_to_list(v_a_2293_);
v___x_2295_ = l___private_Init_Data_List_Impl_0__List_zipWithTR_go(lean_box(0), lean_box(0), lean_box(0), v___f_2283_, v_shape_2277_, v___x_2294_, v___x_2290_);
v___x_2296_ = l_List_zipIdxTR___redArg(v___x_2295_, v___x_2289_);
v___x_2297_ = lean_box(0);
v___x_2298_ = l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toCases_spec__1(v_a_2293_, v___x_2296_, v___x_2297_, v_a_2278_, v_a_2279_, v_a_2280_, v_a_2281_);
lean_dec(v_a_2293_);
if (lean_obj_tag(v___x_2298_) == 0)
{
lean_object* v___x_2300_; uint8_t v_isShared_2301_; uint8_t v_isSharedCheck_2306_; 
v_isSharedCheck_2306_ = !lean_is_exclusive(v___x_2298_);
if (v_isSharedCheck_2306_ == 0)
{
lean_object* v_unused_2307_; 
v_unused_2307_ = lean_ctor_get(v___x_2298_, 0);
lean_dec(v_unused_2307_);
v___x_2300_ = v___x_2298_;
v_isShared_2301_ = v_isSharedCheck_2306_;
goto v_resetjp_2299_;
}
else
{
lean_dec(v___x_2298_);
v___x_2300_ = lean_box(0);
v_isShared_2301_ = v_isSharedCheck_2306_;
goto v_resetjp_2299_;
}
v_resetjp_2299_:
{
lean_object* v___x_2302_; lean_object* v___x_2304_; 
v___x_2302_ = lean_box(0);
if (v_isShared_2301_ == 0)
{
lean_ctor_set(v___x_2300_, 0, v___x_2302_);
v___x_2304_ = v___x_2300_;
goto v_reusejp_2303_;
}
else
{
lean_object* v_reuseFailAlloc_2305_; 
v_reuseFailAlloc_2305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2305_, 0, v___x_2302_);
v___x_2304_ = v_reuseFailAlloc_2305_;
goto v_reusejp_2303_;
}
v_reusejp_2303_:
{
return v___x_2304_;
}
}
}
else
{
lean_object* v_a_2308_; lean_object* v___x_2310_; uint8_t v_isShared_2311_; uint8_t v_isSharedCheck_2315_; 
v_a_2308_ = lean_ctor_get(v___x_2298_, 0);
v_isSharedCheck_2315_ = !lean_is_exclusive(v___x_2298_);
if (v_isSharedCheck_2315_ == 0)
{
v___x_2310_ = v___x_2298_;
v_isShared_2311_ = v_isSharedCheck_2315_;
goto v_resetjp_2309_;
}
else
{
lean_inc(v_a_2308_);
lean_dec(v___x_2298_);
v___x_2310_ = lean_box(0);
v_isShared_2311_ = v_isSharedCheck_2315_;
goto v_resetjp_2309_;
}
v_resetjp_2309_:
{
lean_object* v___x_2313_; 
if (v_isShared_2311_ == 0)
{
v___x_2313_ = v___x_2310_;
goto v_reusejp_2312_;
}
else
{
lean_object* v_reuseFailAlloc_2314_; 
v_reuseFailAlloc_2314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2314_, 0, v_a_2308_);
v___x_2313_ = v_reuseFailAlloc_2314_;
goto v_reusejp_2312_;
}
v_reusejp_2312_:
{
return v___x_2313_;
}
}
}
}
else
{
lean_object* v_a_2316_; lean_object* v___x_2318_; uint8_t v_isShared_2319_; uint8_t v_isSharedCheck_2323_; 
lean_dec(v_shape_2277_);
v_a_2316_ = lean_ctor_get(v___x_2292_, 0);
v_isSharedCheck_2323_ = !lean_is_exclusive(v___x_2292_);
if (v_isSharedCheck_2323_ == 0)
{
v___x_2318_ = v___x_2292_;
v_isShared_2319_ = v_isSharedCheck_2323_;
goto v_resetjp_2317_;
}
else
{
lean_inc(v_a_2316_);
lean_dec(v___x_2292_);
v___x_2318_ = lean_box(0);
v_isShared_2319_ = v_isSharedCheck_2323_;
goto v_resetjp_2317_;
}
v_resetjp_2317_:
{
lean_object* v___x_2321_; 
if (v_isShared_2319_ == 0)
{
v___x_2321_ = v___x_2318_;
goto v_reusejp_2320_;
}
else
{
lean_object* v_reuseFailAlloc_2322_; 
v_reuseFailAlloc_2322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2322_, 0, v_a_2316_);
v___x_2321_ = v_reuseFailAlloc_2322_;
goto v_reusejp_2320_;
}
v_reusejp_2320_:
{
return v___x_2321_;
}
}
}
}
else
{
lean_object* v_a_2324_; lean_object* v___x_2326_; uint8_t v_isShared_2327_; uint8_t v_isSharedCheck_2331_; 
lean_dec(v_shape_2277_);
v_a_2324_ = lean_ctor_get(v___x_2285_, 0);
v_isSharedCheck_2331_ = !lean_is_exclusive(v___x_2285_);
if (v_isSharedCheck_2331_ == 0)
{
v___x_2326_ = v___x_2285_;
v_isShared_2327_ = v_isSharedCheck_2331_;
goto v_resetjp_2325_;
}
else
{
lean_inc(v_a_2324_);
lean_dec(v___x_2285_);
v___x_2326_ = lean_box(0);
v_isShared_2327_ = v_isSharedCheck_2331_;
goto v_resetjp_2325_;
}
v_resetjp_2325_:
{
lean_object* v___x_2329_; 
if (v_isShared_2327_ == 0)
{
v___x_2329_ = v___x_2326_;
goto v_reusejp_2328_;
}
else
{
lean_object* v_reuseFailAlloc_2330_; 
v_reuseFailAlloc_2330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2330_, 0, v_a_2324_);
v___x_2329_ = v_reuseFailAlloc_2330_;
goto v_reusejp_2328_;
}
v_reusejp_2328_:
{
return v___x_2329_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toCases___boxed(lean_object* v_mvar_2332_, lean_object* v_shape_2333_, lean_object* v_a_2334_, lean_object* v_a_2335_, lean_object* v_a_2336_, lean_object* v_a_2337_, lean_object* v_a_2338_){
_start:
{
lean_object* v_res_2339_; 
v_res_2339_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toCases(v_mvar_2332_, v_shape_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_);
lean_dec(v_a_2337_);
lean_dec_ref(v_a_2336_);
lean_dec(v_a_2335_);
lean_dec_ref(v_a_2334_);
return v_res_2339_;
}
}
static lean_object* _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesSum___closed__1(void){
_start:
{
lean_object* v___x_2341_; lean_object* v___x_2342_; 
v___x_2341_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesSum___closed__0));
v___x_2342_ = l_Lean_stringToMessageData(v___x_2341_);
return v___x_2342_;
}
}
static lean_object* _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesSum___closed__3(void){
_start:
{
lean_object* v___x_2344_; lean_object* v___x_2345_; 
v___x_2344_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesSum___closed__2));
v___x_2345_ = l_Lean_stringToMessageData(v___x_2344_);
return v___x_2345_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesSum(lean_object* v_n_2346_, lean_object* v_mvar_2347_, lean_object* v_h_2348_, lean_object* v_a_2349_, lean_object* v_a_2350_, lean_object* v_a_2351_, lean_object* v_a_2352_){
_start:
{
lean_object* v___y_2355_; lean_object* v___y_2356_; lean_object* v___y_2357_; lean_object* v___y_2358_; lean_object* v___y_2362_; lean_object* v___y_2363_; lean_object* v___y_2364_; lean_object* v___y_2365_; lean_object* v_zero_2368_; uint8_t v_isZero_2369_; 
v_zero_2368_ = lean_unsigned_to_nat(0u);
v_isZero_2369_ = lean_nat_dec_eq(v_n_2346_, v_zero_2368_);
if (v_isZero_2369_ == 1)
{
lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; 
v___x_2370_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2370_, 0, v_h_2348_);
lean_ctor_set(v___x_2370_, 1, v_mvar_2347_);
v___x_2371_ = lean_box(0);
v___x_2372_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2372_, 0, v___x_2370_);
lean_ctor_set(v___x_2372_, 1, v___x_2371_);
v___x_2373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2373_, 0, v___x_2372_);
return v___x_2373_;
}
else
{
lean_object* v_one_2374_; lean_object* v_n_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; 
v_one_2374_ = lean_unsigned_to_nat(1u);
v_n_2375_ = lean_nat_sub(v_n_2346_, v_one_2374_);
v___x_2376_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toCases___closed__1));
v___x_2377_ = lean_box(0);
v___x_2378_ = l_Lean_MVarId_cases(v_mvar_2347_, v_h_2348_, v___x_2376_, v_isZero_2369_, v___x_2377_, v_a_2349_, v_a_2350_, v_a_2351_, v_a_2352_);
if (lean_obj_tag(v___x_2378_) == 0)
{
lean_object* v_a_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; uint8_t v___x_2382_; 
v_a_2379_ = lean_ctor_get(v___x_2378_, 0);
lean_inc(v_a_2379_);
lean_dec_ref_known(v___x_2378_, 1);
v___x_2380_ = lean_array_get_size(v_a_2379_);
v___x_2381_ = lean_unsigned_to_nat(2u);
v___x_2382_ = lean_nat_dec_eq(v___x_2380_, v___x_2381_);
if (v___x_2382_ == 0)
{
lean_object* v___x_2383_; lean_object* v___x_2384_; 
lean_dec(v_a_2379_);
lean_dec(v_n_2375_);
v___x_2383_ = lean_obj_once(&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesSum___closed__3, &l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesSum___closed__3_once, _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesSum___closed__3);
v___x_2384_ = l_Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0___redArg(v___x_2383_, v_a_2349_, v_a_2350_, v_a_2351_, v_a_2352_);
return v___x_2384_;
}
else
{
lean_object* v___x_2385_; lean_object* v_toInductionSubgoal_2386_; lean_object* v___x_2388_; uint8_t v_isShared_2389_; uint8_t v_isSharedCheck_2424_; 
v___x_2385_ = lean_array_fget(v_a_2379_, v_zero_2368_);
v_toInductionSubgoal_2386_ = lean_ctor_get(v___x_2385_, 0);
v_isSharedCheck_2424_ = !lean_is_exclusive(v___x_2385_);
if (v_isSharedCheck_2424_ == 0)
{
lean_object* v_unused_2425_; 
v_unused_2425_ = lean_ctor_get(v___x_2385_, 1);
lean_dec(v_unused_2425_);
v___x_2388_ = v___x_2385_;
v_isShared_2389_ = v_isSharedCheck_2424_;
goto v_resetjp_2387_;
}
else
{
lean_inc(v_toInductionSubgoal_2386_);
lean_dec(v___x_2385_);
v___x_2388_ = lean_box(0);
v_isShared_2389_ = v_isSharedCheck_2424_;
goto v_resetjp_2387_;
}
v_resetjp_2387_:
{
lean_object* v_mvarId_2390_; lean_object* v_fields_2391_; lean_object* v___x_2392_; uint8_t v___x_2393_; 
v_mvarId_2390_ = lean_ctor_get(v_toInductionSubgoal_2386_, 0);
lean_inc(v_mvarId_2390_);
v_fields_2391_ = lean_ctor_get(v_toInductionSubgoal_2386_, 1);
lean_inc_ref(v_fields_2391_);
lean_dec_ref(v_toInductionSubgoal_2386_);
v___x_2392_ = lean_array_get_size(v_fields_2391_);
v___x_2393_ = lean_nat_dec_eq(v___x_2392_, v_one_2374_);
if (v___x_2393_ == 0)
{
lean_dec_ref(v_fields_2391_);
lean_dec(v_mvarId_2390_);
lean_del_object(v___x_2388_);
lean_dec(v_a_2379_);
lean_dec(v_n_2375_);
v___y_2362_ = v_a_2349_;
v___y_2363_ = v_a_2350_;
v___y_2364_ = v_a_2351_;
v___y_2365_ = v_a_2352_;
goto v___jp_2361_;
}
else
{
lean_object* v___x_2394_; 
v___x_2394_ = lean_array_fget(v_fields_2391_, v_zero_2368_);
lean_dec_ref(v_fields_2391_);
if (lean_obj_tag(v___x_2394_) == 1)
{
lean_object* v_fvarId_2395_; lean_object* v___x_2396_; lean_object* v_toInductionSubgoal_2397_; lean_object* v___x_2399_; uint8_t v_isShared_2400_; uint8_t v_isSharedCheck_2422_; 
v_fvarId_2395_ = lean_ctor_get(v___x_2394_, 0);
lean_inc(v_fvarId_2395_);
lean_dec_ref_known(v___x_2394_, 1);
v___x_2396_ = lean_array_fget(v_a_2379_, v_one_2374_);
lean_dec(v_a_2379_);
v_toInductionSubgoal_2397_ = lean_ctor_get(v___x_2396_, 0);
v_isSharedCheck_2422_ = !lean_is_exclusive(v___x_2396_);
if (v_isSharedCheck_2422_ == 0)
{
lean_object* v_unused_2423_; 
v_unused_2423_ = lean_ctor_get(v___x_2396_, 1);
lean_dec(v_unused_2423_);
v___x_2399_ = v___x_2396_;
v_isShared_2400_ = v_isSharedCheck_2422_;
goto v_resetjp_2398_;
}
else
{
lean_inc(v_toInductionSubgoal_2397_);
lean_dec(v___x_2396_);
v___x_2399_ = lean_box(0);
v_isShared_2400_ = v_isSharedCheck_2422_;
goto v_resetjp_2398_;
}
v_resetjp_2398_:
{
lean_object* v_mvarId_2401_; lean_object* v_fields_2402_; lean_object* v___x_2403_; uint8_t v___x_2404_; 
v_mvarId_2401_ = lean_ctor_get(v_toInductionSubgoal_2397_, 0);
lean_inc(v_mvarId_2401_);
v_fields_2402_ = lean_ctor_get(v_toInductionSubgoal_2397_, 1);
lean_inc_ref(v_fields_2402_);
lean_dec_ref(v_toInductionSubgoal_2397_);
v___x_2403_ = lean_array_get_size(v_fields_2402_);
v___x_2404_ = lean_nat_dec_eq(v___x_2403_, v_one_2374_);
if (v___x_2404_ == 0)
{
lean_dec_ref(v_fields_2402_);
lean_dec(v_mvarId_2401_);
lean_del_object(v___x_2399_);
lean_dec(v_fvarId_2395_);
lean_dec(v_mvarId_2390_);
lean_del_object(v___x_2388_);
lean_dec(v_n_2375_);
v___y_2355_ = v_a_2349_;
v___y_2356_ = v_a_2350_;
v___y_2357_ = v_a_2351_;
v___y_2358_ = v_a_2352_;
goto v___jp_2354_;
}
else
{
lean_object* v___x_2405_; 
v___x_2405_ = lean_array_fget(v_fields_2402_, v_zero_2368_);
lean_dec_ref(v_fields_2402_);
if (lean_obj_tag(v___x_2405_) == 1)
{
lean_object* v_fvarId_2406_; lean_object* v___x_2407_; 
v_fvarId_2406_ = lean_ctor_get(v___x_2405_, 0);
lean_inc(v_fvarId_2406_);
lean_dec_ref_known(v___x_2405_, 1);
v___x_2407_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesSum(v_n_2375_, v_mvarId_2401_, v_fvarId_2406_, v_a_2349_, v_a_2350_, v_a_2351_, v_a_2352_);
lean_dec(v_n_2375_);
if (lean_obj_tag(v___x_2407_) == 0)
{
lean_object* v_a_2408_; lean_object* v___x_2410_; uint8_t v_isShared_2411_; uint8_t v_isSharedCheck_2421_; 
v_a_2408_ = lean_ctor_get(v___x_2407_, 0);
v_isSharedCheck_2421_ = !lean_is_exclusive(v___x_2407_);
if (v_isSharedCheck_2421_ == 0)
{
v___x_2410_ = v___x_2407_;
v_isShared_2411_ = v_isSharedCheck_2421_;
goto v_resetjp_2409_;
}
else
{
lean_inc(v_a_2408_);
lean_dec(v___x_2407_);
v___x_2410_ = lean_box(0);
v_isShared_2411_ = v_isSharedCheck_2421_;
goto v_resetjp_2409_;
}
v_resetjp_2409_:
{
lean_object* v___x_2413_; 
if (v_isShared_2400_ == 0)
{
lean_ctor_set(v___x_2399_, 1, v_mvarId_2390_);
lean_ctor_set(v___x_2399_, 0, v_fvarId_2395_);
v___x_2413_ = v___x_2399_;
goto v_reusejp_2412_;
}
else
{
lean_object* v_reuseFailAlloc_2420_; 
v_reuseFailAlloc_2420_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2420_, 0, v_fvarId_2395_);
lean_ctor_set(v_reuseFailAlloc_2420_, 1, v_mvarId_2390_);
v___x_2413_ = v_reuseFailAlloc_2420_;
goto v_reusejp_2412_;
}
v_reusejp_2412_:
{
lean_object* v___x_2415_; 
if (v_isShared_2389_ == 0)
{
lean_ctor_set_tag(v___x_2388_, 1);
lean_ctor_set(v___x_2388_, 1, v_a_2408_);
lean_ctor_set(v___x_2388_, 0, v___x_2413_);
v___x_2415_ = v___x_2388_;
goto v_reusejp_2414_;
}
else
{
lean_object* v_reuseFailAlloc_2419_; 
v_reuseFailAlloc_2419_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2419_, 0, v___x_2413_);
lean_ctor_set(v_reuseFailAlloc_2419_, 1, v_a_2408_);
v___x_2415_ = v_reuseFailAlloc_2419_;
goto v_reusejp_2414_;
}
v_reusejp_2414_:
{
lean_object* v___x_2417_; 
if (v_isShared_2411_ == 0)
{
lean_ctor_set(v___x_2410_, 0, v___x_2415_);
v___x_2417_ = v___x_2410_;
goto v_reusejp_2416_;
}
else
{
lean_object* v_reuseFailAlloc_2418_; 
v_reuseFailAlloc_2418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2418_, 0, v___x_2415_);
v___x_2417_ = v_reuseFailAlloc_2418_;
goto v_reusejp_2416_;
}
v_reusejp_2416_:
{
return v___x_2417_;
}
}
}
}
}
else
{
lean_del_object(v___x_2399_);
lean_dec(v_fvarId_2395_);
lean_dec(v_mvarId_2390_);
lean_del_object(v___x_2388_);
return v___x_2407_;
}
}
else
{
lean_dec(v___x_2405_);
lean_dec(v_mvarId_2401_);
lean_del_object(v___x_2399_);
lean_dec(v_fvarId_2395_);
lean_dec(v_mvarId_2390_);
lean_del_object(v___x_2388_);
lean_dec(v_n_2375_);
v___y_2355_ = v_a_2349_;
v___y_2356_ = v_a_2350_;
v___y_2357_ = v_a_2351_;
v___y_2358_ = v_a_2352_;
goto v___jp_2354_;
}
}
}
}
else
{
lean_dec(v___x_2394_);
lean_dec(v_mvarId_2390_);
lean_del_object(v___x_2388_);
lean_dec(v_a_2379_);
lean_dec(v_n_2375_);
v___y_2362_ = v_a_2349_;
v___y_2363_ = v_a_2350_;
v___y_2364_ = v_a_2351_;
v___y_2365_ = v_a_2352_;
goto v___jp_2361_;
}
}
}
}
}
else
{
lean_object* v_a_2426_; lean_object* v___x_2428_; uint8_t v_isShared_2429_; uint8_t v_isSharedCheck_2433_; 
lean_dec(v_n_2375_);
v_a_2426_ = lean_ctor_get(v___x_2378_, 0);
v_isSharedCheck_2433_ = !lean_is_exclusive(v___x_2378_);
if (v_isSharedCheck_2433_ == 0)
{
v___x_2428_ = v___x_2378_;
v_isShared_2429_ = v_isSharedCheck_2433_;
goto v_resetjp_2427_;
}
else
{
lean_inc(v_a_2426_);
lean_dec(v___x_2378_);
v___x_2428_ = lean_box(0);
v_isShared_2429_ = v_isSharedCheck_2433_;
goto v_resetjp_2427_;
}
v_resetjp_2427_:
{
lean_object* v___x_2431_; 
if (v_isShared_2429_ == 0)
{
v___x_2431_ = v___x_2428_;
goto v_reusejp_2430_;
}
else
{
lean_object* v_reuseFailAlloc_2432_; 
v_reuseFailAlloc_2432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2432_, 0, v_a_2426_);
v___x_2431_ = v_reuseFailAlloc_2432_;
goto v_reusejp_2430_;
}
v_reusejp_2430_:
{
return v___x_2431_;
}
}
}
}
v___jp_2354_:
{
lean_object* v___x_2359_; lean_object* v___x_2360_; 
v___x_2359_ = lean_obj_once(&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesSum___closed__1, &l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesSum___closed__1_once, _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesSum___closed__1);
v___x_2360_ = l_Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0___redArg(v___x_2359_, v___y_2355_, v___y_2356_, v___y_2357_, v___y_2358_);
return v___x_2360_;
}
v___jp_2361_:
{
lean_object* v___x_2366_; lean_object* v___x_2367_; 
v___x_2366_ = lean_obj_once(&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesSum___closed__1, &l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesSum___closed__1_once, _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesSum___closed__1);
v___x_2367_ = l_Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0___redArg(v___x_2366_, v___y_2362_, v___y_2363_, v___y_2364_, v___y_2365_);
return v___x_2367_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesSum___boxed(lean_object* v_n_2434_, lean_object* v_mvar_2435_, lean_object* v_h_2436_, lean_object* v_a_2437_, lean_object* v_a_2438_, lean_object* v_a_2439_, lean_object* v_a_2440_, lean_object* v_a_2441_){
_start:
{
lean_object* v_res_2442_; 
v_res_2442_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesSum(v_n_2434_, v_mvar_2435_, v_h_2436_, v_a_2437_, v_a_2438_, v_a_2439_, v_a_2440_);
lean_dec(v_a_2440_);
lean_dec_ref(v_a_2439_);
lean_dec(v_a_2438_);
lean_dec_ref(v_a_2437_);
lean_dec(v_n_2434_);
return v_res_2442_;
}
}
static lean_object* _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesProd___closed__1(void){
_start:
{
lean_object* v___x_2444_; lean_object* v___x_2445_; 
v___x_2444_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesProd___closed__0));
v___x_2445_ = l_Lean_stringToMessageData(v___x_2444_);
return v___x_2445_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesProd(lean_object* v_n_2446_, lean_object* v_mvar_2447_, lean_object* v_h_2448_, lean_object* v_a_2449_, lean_object* v_a_2450_, lean_object* v_a_2451_, lean_object* v_a_2452_){
_start:
{
lean_object* v___y_2455_; lean_object* v___y_2456_; lean_object* v___y_2457_; lean_object* v___y_2458_; lean_object* v_zero_2461_; uint8_t v_isZero_2462_; 
v_zero_2461_ = lean_unsigned_to_nat(0u);
v_isZero_2462_ = lean_nat_dec_eq(v_n_2446_, v_zero_2461_);
if (v_isZero_2462_ == 1)
{
lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; 
v___x_2463_ = lean_box(0);
v___x_2464_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2464_, 0, v_h_2448_);
lean_ctor_set(v___x_2464_, 1, v___x_2463_);
v___x_2465_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2465_, 0, v_mvar_2447_);
lean_ctor_set(v___x_2465_, 1, v___x_2464_);
v___x_2466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2466_, 0, v___x_2465_);
return v___x_2466_;
}
else
{
lean_object* v_one_2467_; lean_object* v_n_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; 
v_one_2467_ = lean_unsigned_to_nat(1u);
v_n_2468_ = lean_nat_sub(v_n_2446_, v_one_2467_);
v___x_2469_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toCases___closed__1));
v___x_2470_ = lean_box(0);
v___x_2471_ = l_Lean_MVarId_cases(v_mvar_2447_, v_h_2448_, v___x_2469_, v_isZero_2462_, v___x_2470_, v_a_2449_, v_a_2450_, v_a_2451_, v_a_2452_);
if (lean_obj_tag(v___x_2471_) == 0)
{
lean_object* v_a_2472_; lean_object* v___x_2473_; uint8_t v___x_2474_; 
v_a_2472_ = lean_ctor_get(v___x_2471_, 0);
lean_inc(v_a_2472_);
lean_dec_ref_known(v___x_2471_, 1);
v___x_2473_ = lean_array_get_size(v_a_2472_);
v___x_2474_ = lean_nat_dec_eq(v___x_2473_, v_one_2467_);
if (v___x_2474_ == 0)
{
lean_object* v___x_2475_; lean_object* v___x_2476_; 
lean_dec(v_a_2472_);
lean_dec(v_n_2468_);
v___x_2475_ = lean_obj_once(&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesProd___closed__1, &l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesProd___closed__1_once, _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesProd___closed__1);
v___x_2476_ = l_Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0___redArg(v___x_2475_, v_a_2449_, v_a_2450_, v_a_2451_, v_a_2452_);
return v___x_2476_;
}
else
{
lean_object* v___x_2477_; lean_object* v_toInductionSubgoal_2478_; lean_object* v___x_2480_; uint8_t v_isShared_2481_; uint8_t v_isSharedCheck_2512_; 
v___x_2477_ = lean_array_fget(v_a_2472_, v_zero_2461_);
lean_dec(v_a_2472_);
v_toInductionSubgoal_2478_ = lean_ctor_get(v___x_2477_, 0);
v_isSharedCheck_2512_ = !lean_is_exclusive(v___x_2477_);
if (v_isSharedCheck_2512_ == 0)
{
lean_object* v_unused_2513_; 
v_unused_2513_ = lean_ctor_get(v___x_2477_, 1);
lean_dec(v_unused_2513_);
v___x_2480_ = v___x_2477_;
v_isShared_2481_ = v_isSharedCheck_2512_;
goto v_resetjp_2479_;
}
else
{
lean_inc(v_toInductionSubgoal_2478_);
lean_dec(v___x_2477_);
v___x_2480_ = lean_box(0);
v_isShared_2481_ = v_isSharedCheck_2512_;
goto v_resetjp_2479_;
}
v_resetjp_2479_:
{
lean_object* v_mvarId_2482_; lean_object* v_fields_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; uint8_t v___x_2486_; 
v_mvarId_2482_ = lean_ctor_get(v_toInductionSubgoal_2478_, 0);
lean_inc(v_mvarId_2482_);
v_fields_2483_ = lean_ctor_get(v_toInductionSubgoal_2478_, 1);
lean_inc_ref(v_fields_2483_);
lean_dec_ref(v_toInductionSubgoal_2478_);
v___x_2484_ = lean_array_get_size(v_fields_2483_);
v___x_2485_ = lean_unsigned_to_nat(2u);
v___x_2486_ = lean_nat_dec_eq(v___x_2484_, v___x_2485_);
if (v___x_2486_ == 0)
{
lean_dec_ref(v_fields_2483_);
lean_dec(v_mvarId_2482_);
lean_del_object(v___x_2480_);
lean_dec(v_n_2468_);
v___y_2455_ = v_a_2449_;
v___y_2456_ = v_a_2450_;
v___y_2457_ = v_a_2451_;
v___y_2458_ = v_a_2452_;
goto v___jp_2454_;
}
else
{
lean_object* v___x_2487_; 
v___x_2487_ = lean_array_fget_borrowed(v_fields_2483_, v_zero_2461_);
if (lean_obj_tag(v___x_2487_) == 1)
{
lean_object* v_fvarId_2488_; lean_object* v___x_2489_; 
v_fvarId_2488_ = lean_ctor_get(v___x_2487_, 0);
lean_inc(v_fvarId_2488_);
v___x_2489_ = lean_array_fget(v_fields_2483_, v_one_2467_);
lean_dec_ref(v_fields_2483_);
if (lean_obj_tag(v___x_2489_) == 1)
{
lean_object* v_fvarId_2490_; lean_object* v___x_2491_; 
v_fvarId_2490_ = lean_ctor_get(v___x_2489_, 0);
lean_inc(v_fvarId_2490_);
lean_dec_ref_known(v___x_2489_, 1);
v___x_2491_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesProd(v_n_2468_, v_mvarId_2482_, v_fvarId_2490_, v_a_2449_, v_a_2450_, v_a_2451_, v_a_2452_);
lean_dec(v_n_2468_);
if (lean_obj_tag(v___x_2491_) == 0)
{
lean_object* v_a_2492_; lean_object* v___x_2494_; uint8_t v_isShared_2495_; uint8_t v_isSharedCheck_2511_; 
v_a_2492_ = lean_ctor_get(v___x_2491_, 0);
v_isSharedCheck_2511_ = !lean_is_exclusive(v___x_2491_);
if (v_isSharedCheck_2511_ == 0)
{
v___x_2494_ = v___x_2491_;
v_isShared_2495_ = v_isSharedCheck_2511_;
goto v_resetjp_2493_;
}
else
{
lean_inc(v_a_2492_);
lean_dec(v___x_2491_);
v___x_2494_ = lean_box(0);
v_isShared_2495_ = v_isSharedCheck_2511_;
goto v_resetjp_2493_;
}
v_resetjp_2493_:
{
lean_object* v_fst_2496_; lean_object* v_snd_2497_; lean_object* v___x_2499_; uint8_t v_isShared_2500_; uint8_t v_isSharedCheck_2510_; 
v_fst_2496_ = lean_ctor_get(v_a_2492_, 0);
v_snd_2497_ = lean_ctor_get(v_a_2492_, 1);
v_isSharedCheck_2510_ = !lean_is_exclusive(v_a_2492_);
if (v_isSharedCheck_2510_ == 0)
{
v___x_2499_ = v_a_2492_;
v_isShared_2500_ = v_isSharedCheck_2510_;
goto v_resetjp_2498_;
}
else
{
lean_inc(v_snd_2497_);
lean_inc(v_fst_2496_);
lean_dec(v_a_2492_);
v___x_2499_ = lean_box(0);
v_isShared_2500_ = v_isSharedCheck_2510_;
goto v_resetjp_2498_;
}
v_resetjp_2498_:
{
lean_object* v___x_2502_; 
if (v_isShared_2481_ == 0)
{
lean_ctor_set_tag(v___x_2480_, 1);
lean_ctor_set(v___x_2480_, 1, v_snd_2497_);
lean_ctor_set(v___x_2480_, 0, v_fvarId_2488_);
v___x_2502_ = v___x_2480_;
goto v_reusejp_2501_;
}
else
{
lean_object* v_reuseFailAlloc_2509_; 
v_reuseFailAlloc_2509_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2509_, 0, v_fvarId_2488_);
lean_ctor_set(v_reuseFailAlloc_2509_, 1, v_snd_2497_);
v___x_2502_ = v_reuseFailAlloc_2509_;
goto v_reusejp_2501_;
}
v_reusejp_2501_:
{
lean_object* v___x_2504_; 
if (v_isShared_2500_ == 0)
{
lean_ctor_set(v___x_2499_, 1, v___x_2502_);
v___x_2504_ = v___x_2499_;
goto v_reusejp_2503_;
}
else
{
lean_object* v_reuseFailAlloc_2508_; 
v_reuseFailAlloc_2508_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2508_, 0, v_fst_2496_);
lean_ctor_set(v_reuseFailAlloc_2508_, 1, v___x_2502_);
v___x_2504_ = v_reuseFailAlloc_2508_;
goto v_reusejp_2503_;
}
v_reusejp_2503_:
{
lean_object* v___x_2506_; 
if (v_isShared_2495_ == 0)
{
lean_ctor_set(v___x_2494_, 0, v___x_2504_);
v___x_2506_ = v___x_2494_;
goto v_reusejp_2505_;
}
else
{
lean_object* v_reuseFailAlloc_2507_; 
v_reuseFailAlloc_2507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2507_, 0, v___x_2504_);
v___x_2506_ = v_reuseFailAlloc_2507_;
goto v_reusejp_2505_;
}
v_reusejp_2505_:
{
return v___x_2506_;
}
}
}
}
}
}
else
{
lean_dec(v_fvarId_2488_);
lean_del_object(v___x_2480_);
return v___x_2491_;
}
}
else
{
lean_dec(v___x_2489_);
lean_dec(v_fvarId_2488_);
lean_dec(v_mvarId_2482_);
lean_del_object(v___x_2480_);
lean_dec(v_n_2468_);
v___y_2455_ = v_a_2449_;
v___y_2456_ = v_a_2450_;
v___y_2457_ = v_a_2451_;
v___y_2458_ = v_a_2452_;
goto v___jp_2454_;
}
}
else
{
lean_dec_ref(v_fields_2483_);
lean_dec(v_mvarId_2482_);
lean_del_object(v___x_2480_);
lean_dec(v_n_2468_);
v___y_2455_ = v_a_2449_;
v___y_2456_ = v_a_2450_;
v___y_2457_ = v_a_2451_;
v___y_2458_ = v_a_2452_;
goto v___jp_2454_;
}
}
}
}
}
else
{
lean_object* v_a_2514_; lean_object* v___x_2516_; uint8_t v_isShared_2517_; uint8_t v_isSharedCheck_2521_; 
lean_dec(v_n_2468_);
v_a_2514_ = lean_ctor_get(v___x_2471_, 0);
v_isSharedCheck_2521_ = !lean_is_exclusive(v___x_2471_);
if (v_isSharedCheck_2521_ == 0)
{
v___x_2516_ = v___x_2471_;
v_isShared_2517_ = v_isSharedCheck_2521_;
goto v_resetjp_2515_;
}
else
{
lean_inc(v_a_2514_);
lean_dec(v___x_2471_);
v___x_2516_ = lean_box(0);
v_isShared_2517_ = v_isSharedCheck_2521_;
goto v_resetjp_2515_;
}
v_resetjp_2515_:
{
lean_object* v___x_2519_; 
if (v_isShared_2517_ == 0)
{
v___x_2519_ = v___x_2516_;
goto v_reusejp_2518_;
}
else
{
lean_object* v_reuseFailAlloc_2520_; 
v_reuseFailAlloc_2520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2520_, 0, v_a_2514_);
v___x_2519_ = v_reuseFailAlloc_2520_;
goto v_reusejp_2518_;
}
v_reusejp_2518_:
{
return v___x_2519_;
}
}
}
}
v___jp_2454_:
{
lean_object* v___x_2459_; lean_object* v___x_2460_; 
v___x_2459_ = lean_obj_once(&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesSum___closed__1, &l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesSum___closed__1_once, _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesSum___closed__1);
v___x_2460_ = l_Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0___redArg(v___x_2459_, v___y_2455_, v___y_2456_, v___y_2457_, v___y_2458_);
return v___x_2460_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesProd___boxed(lean_object* v_n_2522_, lean_object* v_mvar_2523_, lean_object* v_h_2524_, lean_object* v_a_2525_, lean_object* v_a_2526_, lean_object* v_a_2527_, lean_object* v_a_2528_, lean_object* v_a_2529_){
_start:
{
lean_object* v_res_2530_; 
v_res_2530_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesProd(v_n_2522_, v_mvar_2523_, v_h_2524_, v_a_2525_, v_a_2526_, v_a_2527_, v_a_2528_);
lean_dec(v_a_2528_);
lean_dec_ref(v_a_2527_);
lean_dec(v_a_2526_);
lean_dec_ref(v_a_2525_);
lean_dec(v_n_2522_);
return v_res_2530_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_listBoolMerge___redArg(lean_object* v_x_2531_, lean_object* v_x_2532_){
_start:
{
if (lean_obj_tag(v_x_2531_) == 0)
{
lean_object* v___x_2533_; 
lean_dec(v_x_2532_);
v___x_2533_ = lean_box(0);
return v___x_2533_;
}
else
{
lean_object* v_head_2534_; uint8_t v___x_2535_; 
v_head_2534_ = lean_ctor_get(v_x_2531_, 0);
v___x_2535_ = lean_unbox(v_head_2534_);
if (v___x_2535_ == 0)
{
lean_object* v_tail_2536_; lean_object* v___x_2538_; uint8_t v_isShared_2539_; uint8_t v_isSharedCheck_2545_; 
v_tail_2536_ = lean_ctor_get(v_x_2531_, 1);
v_isSharedCheck_2545_ = !lean_is_exclusive(v_x_2531_);
if (v_isSharedCheck_2545_ == 0)
{
lean_object* v_unused_2546_; 
v_unused_2546_ = lean_ctor_get(v_x_2531_, 0);
lean_dec(v_unused_2546_);
v___x_2538_ = v_x_2531_;
v_isShared_2539_ = v_isSharedCheck_2545_;
goto v_resetjp_2537_;
}
else
{
lean_inc(v_tail_2536_);
lean_dec(v_x_2531_);
v___x_2538_ = lean_box(0);
v_isShared_2539_ = v_isSharedCheck_2545_;
goto v_resetjp_2537_;
}
v_resetjp_2537_:
{
lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v___x_2543_; 
v___x_2540_ = lean_box(0);
v___x_2541_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_listBoolMerge___redArg(v_tail_2536_, v_x_2532_);
if (v_isShared_2539_ == 0)
{
lean_ctor_set(v___x_2538_, 1, v___x_2541_);
lean_ctor_set(v___x_2538_, 0, v___x_2540_);
v___x_2543_ = v___x_2538_;
goto v_reusejp_2542_;
}
else
{
lean_object* v_reuseFailAlloc_2544_; 
v_reuseFailAlloc_2544_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2544_, 0, v___x_2540_);
lean_ctor_set(v_reuseFailAlloc_2544_, 1, v___x_2541_);
v___x_2543_ = v_reuseFailAlloc_2544_;
goto v_reusejp_2542_;
}
v_reusejp_2542_:
{
return v___x_2543_;
}
}
}
else
{
if (lean_obj_tag(v_x_2532_) == 0)
{
lean_object* v___x_2547_; 
lean_dec_ref_known(v_x_2531_, 2);
v___x_2547_ = lean_box(0);
return v___x_2547_;
}
else
{
lean_object* v_tail_2548_; lean_object* v_head_2549_; lean_object* v_tail_2550_; lean_object* v___x_2552_; uint8_t v_isShared_2553_; uint8_t v_isSharedCheck_2559_; 
v_tail_2548_ = lean_ctor_get(v_x_2531_, 1);
lean_inc(v_tail_2548_);
lean_dec_ref_known(v_x_2531_, 2);
v_head_2549_ = lean_ctor_get(v_x_2532_, 0);
v_tail_2550_ = lean_ctor_get(v_x_2532_, 1);
v_isSharedCheck_2559_ = !lean_is_exclusive(v_x_2532_);
if (v_isSharedCheck_2559_ == 0)
{
v___x_2552_ = v_x_2532_;
v_isShared_2553_ = v_isSharedCheck_2559_;
goto v_resetjp_2551_;
}
else
{
lean_inc(v_tail_2550_);
lean_inc(v_head_2549_);
lean_dec(v_x_2532_);
v___x_2552_ = lean_box(0);
v_isShared_2553_ = v_isSharedCheck_2559_;
goto v_resetjp_2551_;
}
v_resetjp_2551_:
{
lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2557_; 
v___x_2554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2554_, 0, v_head_2549_);
v___x_2555_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_listBoolMerge___redArg(v_tail_2548_, v_tail_2550_);
if (v_isShared_2553_ == 0)
{
lean_ctor_set(v___x_2552_, 1, v___x_2555_);
lean_ctor_set(v___x_2552_, 0, v___x_2554_);
v___x_2557_ = v___x_2552_;
goto v_reusejp_2556_;
}
else
{
lean_object* v_reuseFailAlloc_2558_; 
v_reuseFailAlloc_2558_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2558_, 0, v___x_2554_);
lean_ctor_set(v_reuseFailAlloc_2558_, 1, v___x_2555_);
v___x_2557_ = v_reuseFailAlloc_2558_;
goto v_reusejp_2556_;
}
v_reusejp_2556_:
{
return v___x_2557_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_listBoolMerge(lean_object* v_00_u03b1_2560_, lean_object* v_x_2561_, lean_object* v_x_2562_){
_start:
{
lean_object* v___x_2563_; 
v___x_2563_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_listBoolMerge___redArg(v_x_2561_, v_x_2562_);
return v___x_2563_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive___lam__0(lean_object* v_fst_2564_, lean_object* v_snd_2565_){
_start:
{
lean_object* v___x_2566_; 
v___x_2566_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2566_, 0, v_fst_2564_);
lean_ctor_set(v___x_2566_, 1, v_snd_2565_);
return v___x_2566_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive___lam__1(lean_object* v_fst_2567_, lean_object* v_snd_2568_){
_start:
{
lean_object* v___x_2569_; 
v___x_2569_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2569_, 0, v_fst_2567_);
lean_ctor_set(v___x_2569_, 1, v_snd_2568_);
return v___x_2569_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__2_spec__3(lean_object* v_a_2570_, lean_object* v_a_2571_){
_start:
{
if (lean_obj_tag(v_a_2570_) == 0)
{
lean_object* v___x_2572_; 
v___x_2572_ = l_List_reverse___redArg(v_a_2571_);
return v___x_2572_;
}
else
{
lean_object* v_head_2573_; lean_object* v_tail_2574_; lean_object* v___x_2576_; uint8_t v_isShared_2577_; uint8_t v_isSharedCheck_2583_; 
v_head_2573_ = lean_ctor_get(v_a_2570_, 0);
v_tail_2574_ = lean_ctor_get(v_a_2570_, 1);
v_isSharedCheck_2583_ = !lean_is_exclusive(v_a_2570_);
if (v_isSharedCheck_2583_ == 0)
{
v___x_2576_ = v_a_2570_;
v_isShared_2577_ = v_isSharedCheck_2583_;
goto v_resetjp_2575_;
}
else
{
lean_inc(v_tail_2574_);
lean_inc(v_head_2573_);
lean_dec(v_a_2570_);
v___x_2576_ = lean_box(0);
v_isShared_2577_ = v_isSharedCheck_2583_;
goto v_resetjp_2575_;
}
v_resetjp_2575_:
{
lean_object* v___x_2578_; lean_object* v___x_2580_; 
v___x_2578_ = l_Lean_mkLevelParam(v_head_2573_);
if (v_isShared_2577_ == 0)
{
lean_ctor_set(v___x_2576_, 1, v_a_2571_);
lean_ctor_set(v___x_2576_, 0, v___x_2578_);
v___x_2580_ = v___x_2576_;
goto v_reusejp_2579_;
}
else
{
lean_object* v_reuseFailAlloc_2582_; 
v_reuseFailAlloc_2582_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2582_, 0, v___x_2578_);
lean_ctor_set(v_reuseFailAlloc_2582_, 1, v_a_2571_);
v___x_2580_ = v_reuseFailAlloc_2582_;
goto v_reusejp_2579_;
}
v_reusejp_2579_:
{
v_a_2570_ = v_tail_2574_;
v_a_2571_ = v___x_2580_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__2_spec__2(lean_object* v_constName_2584_, lean_object* v___y_2585_, lean_object* v___y_2586_, lean_object* v___y_2587_, lean_object* v___y_2588_){
_start:
{
lean_object* v___x_2590_; lean_object* v_env_2591_; uint8_t v___x_2592_; lean_object* v___x_2593_; 
v___x_2590_ = lean_st_ref_get(v___y_2588_);
v_env_2591_ = lean_ctor_get(v___x_2590_, 0);
lean_inc_ref(v_env_2591_);
lean_dec(v___x_2590_);
v___x_2592_ = 0;
lean_inc(v_constName_2584_);
v___x_2593_ = l_Lean_Environment_findConstVal_x3f(v_env_2591_, v_constName_2584_, v___x_2592_);
if (lean_obj_tag(v___x_2593_) == 0)
{
lean_object* v___x_2594_; 
v___x_2594_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0___redArg(v_constName_2584_, v___y_2585_, v___y_2586_, v___y_2587_, v___y_2588_);
return v___x_2594_;
}
else
{
lean_object* v_val_2595_; lean_object* v___x_2597_; uint8_t v_isShared_2598_; uint8_t v_isSharedCheck_2602_; 
lean_dec(v_constName_2584_);
v_val_2595_ = lean_ctor_get(v___x_2593_, 0);
v_isSharedCheck_2602_ = !lean_is_exclusive(v___x_2593_);
if (v_isSharedCheck_2602_ == 0)
{
v___x_2597_ = v___x_2593_;
v_isShared_2598_ = v_isSharedCheck_2602_;
goto v_resetjp_2596_;
}
else
{
lean_inc(v_val_2595_);
lean_dec(v___x_2593_);
v___x_2597_ = lean_box(0);
v_isShared_2598_ = v_isSharedCheck_2602_;
goto v_resetjp_2596_;
}
v_resetjp_2596_:
{
lean_object* v___x_2600_; 
if (v_isShared_2598_ == 0)
{
lean_ctor_set_tag(v___x_2597_, 0);
v___x_2600_ = v___x_2597_;
goto v_reusejp_2599_;
}
else
{
lean_object* v_reuseFailAlloc_2601_; 
v_reuseFailAlloc_2601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2601_, 0, v_val_2595_);
v___x_2600_ = v_reuseFailAlloc_2601_;
goto v_reusejp_2599_;
}
v_reusejp_2599_:
{
return v___x_2600_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__2_spec__2___boxed(lean_object* v_constName_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_){
_start:
{
lean_object* v_res_2609_; 
v_res_2609_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__2_spec__2(v_constName_2603_, v___y_2604_, v___y_2605_, v___y_2606_, v___y_2607_);
lean_dec(v___y_2607_);
lean_dec_ref(v___y_2606_);
lean_dec(v___y_2605_);
lean_dec_ref(v___y_2604_);
return v_res_2609_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__2(lean_object* v_constName_2610_, lean_object* v___y_2611_, lean_object* v___y_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_){
_start:
{
lean_object* v___x_2616_; 
lean_inc(v_constName_2610_);
v___x_2616_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__2_spec__2(v_constName_2610_, v___y_2611_, v___y_2612_, v___y_2613_, v___y_2614_);
if (lean_obj_tag(v___x_2616_) == 0)
{
lean_object* v_a_2617_; lean_object* v___x_2619_; uint8_t v_isShared_2620_; uint8_t v_isSharedCheck_2628_; 
v_a_2617_ = lean_ctor_get(v___x_2616_, 0);
v_isSharedCheck_2628_ = !lean_is_exclusive(v___x_2616_);
if (v_isSharedCheck_2628_ == 0)
{
v___x_2619_ = v___x_2616_;
v_isShared_2620_ = v_isSharedCheck_2628_;
goto v_resetjp_2618_;
}
else
{
lean_inc(v_a_2617_);
lean_dec(v___x_2616_);
v___x_2619_ = lean_box(0);
v_isShared_2620_ = v_isSharedCheck_2628_;
goto v_resetjp_2618_;
}
v_resetjp_2618_:
{
lean_object* v_levelParams_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2626_; 
v_levelParams_2621_ = lean_ctor_get(v_a_2617_, 1);
lean_inc(v_levelParams_2621_);
lean_dec(v_a_2617_);
v___x_2622_ = lean_box(0);
v___x_2623_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__2_spec__3(v_levelParams_2621_, v___x_2622_);
v___x_2624_ = l_Lean_mkConst(v_constName_2610_, v___x_2623_);
if (v_isShared_2620_ == 0)
{
lean_ctor_set(v___x_2619_, 0, v___x_2624_);
v___x_2626_ = v___x_2619_;
goto v_reusejp_2625_;
}
else
{
lean_object* v_reuseFailAlloc_2627_; 
v_reuseFailAlloc_2627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2627_, 0, v___x_2624_);
v___x_2626_ = v_reuseFailAlloc_2627_;
goto v_reusejp_2625_;
}
v_reusejp_2625_:
{
return v___x_2626_;
}
}
}
else
{
lean_object* v_a_2629_; lean_object* v___x_2631_; uint8_t v_isShared_2632_; uint8_t v_isSharedCheck_2636_; 
lean_dec(v_constName_2610_);
v_a_2629_ = lean_ctor_get(v___x_2616_, 0);
v_isSharedCheck_2636_ = !lean_is_exclusive(v___x_2616_);
if (v_isSharedCheck_2636_ == 0)
{
v___x_2631_ = v___x_2616_;
v_isShared_2632_ = v_isSharedCheck_2636_;
goto v_resetjp_2630_;
}
else
{
lean_inc(v_a_2629_);
lean_dec(v___x_2616_);
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
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__2___boxed(lean_object* v_constName_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_){
_start:
{
lean_object* v_res_2643_; 
v_res_2643_ = l_Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__2(v_constName_2637_, v___y_2638_, v___y_2639_, v___y_2640_, v___y_2641_);
lean_dec(v___y_2641_);
lean_dec_ref(v___y_2640_);
lean_dec(v___y_2639_);
lean_dec_ref(v___y_2638_);
return v_res_2643_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__1(lean_object* v_x_2644_, lean_object* v_x_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_){
_start:
{
if (lean_obj_tag(v_x_2644_) == 0)
{
lean_object* v___x_2651_; lean_object* v___x_2652_; 
v___x_2651_ = l_List_reverse___redArg(v_x_2645_);
v___x_2652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2652_, 0, v___x_2651_);
return v___x_2652_;
}
else
{
lean_object* v_head_2653_; lean_object* v_tail_2654_; lean_object* v___x_2656_; uint8_t v_isShared_2657_; uint8_t v_isSharedCheck_2679_; 
v_head_2653_ = lean_ctor_get(v_x_2644_, 0);
v_tail_2654_ = lean_ctor_get(v_x_2644_, 1);
v_isSharedCheck_2679_ = !lean_is_exclusive(v_x_2644_);
if (v_isSharedCheck_2679_ == 0)
{
v___x_2656_ = v_x_2644_;
v_isShared_2657_ = v_isSharedCheck_2679_;
goto v_resetjp_2655_;
}
else
{
lean_inc(v_tail_2654_);
lean_inc(v_head_2653_);
lean_dec(v_x_2644_);
v___x_2656_ = lean_box(0);
v_isShared_2657_ = v_isSharedCheck_2679_;
goto v_resetjp_2655_;
}
v_resetjp_2655_:
{
lean_object* v_a_2659_; 
if (lean_obj_tag(v_head_2653_) == 0)
{
lean_object* v___x_2664_; uint8_t v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; 
v___x_2664_ = lean_box(0);
v___x_2665_ = 0;
v___x_2666_ = lean_box(0);
v___x_2667_ = l_Lean_Meta_mkFreshExprMVar(v___x_2664_, v___x_2665_, v___x_2666_, v___y_2646_, v___y_2647_, v___y_2648_, v___y_2649_);
if (lean_obj_tag(v___x_2667_) == 0)
{
lean_object* v_a_2668_; 
v_a_2668_ = lean_ctor_get(v___x_2667_, 0);
lean_inc(v_a_2668_);
lean_dec_ref_known(v___x_2667_, 1);
v_a_2659_ = v_a_2668_;
goto v___jp_2658_;
}
else
{
lean_object* v_a_2669_; lean_object* v___x_2671_; uint8_t v_isShared_2672_; uint8_t v_isSharedCheck_2676_; 
lean_del_object(v___x_2656_);
lean_dec(v_tail_2654_);
lean_dec(v_x_2645_);
v_a_2669_ = lean_ctor_get(v___x_2667_, 0);
v_isSharedCheck_2676_ = !lean_is_exclusive(v___x_2667_);
if (v_isSharedCheck_2676_ == 0)
{
v___x_2671_ = v___x_2667_;
v_isShared_2672_ = v_isSharedCheck_2676_;
goto v_resetjp_2670_;
}
else
{
lean_inc(v_a_2669_);
lean_dec(v___x_2667_);
v___x_2671_ = lean_box(0);
v_isShared_2672_ = v_isSharedCheck_2676_;
goto v_resetjp_2670_;
}
v_resetjp_2670_:
{
lean_object* v___x_2674_; 
if (v_isShared_2672_ == 0)
{
v___x_2674_ = v___x_2671_;
goto v_reusejp_2673_;
}
else
{
lean_object* v_reuseFailAlloc_2675_; 
v_reuseFailAlloc_2675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2675_, 0, v_a_2669_);
v___x_2674_ = v_reuseFailAlloc_2675_;
goto v_reusejp_2673_;
}
v_reusejp_2673_:
{
return v___x_2674_;
}
}
}
}
else
{
lean_object* v_val_2677_; lean_object* v___x_2678_; 
v_val_2677_ = lean_ctor_get(v_head_2653_, 0);
lean_inc(v_val_2677_);
lean_dec_ref_known(v_head_2653_, 1);
v___x_2678_ = l_Lean_mkFVar(v_val_2677_);
v_a_2659_ = v___x_2678_;
goto v___jp_2658_;
}
v___jp_2658_:
{
lean_object* v___x_2661_; 
if (v_isShared_2657_ == 0)
{
lean_ctor_set(v___x_2656_, 1, v_x_2645_);
lean_ctor_set(v___x_2656_, 0, v_a_2659_);
v___x_2661_ = v___x_2656_;
goto v_reusejp_2660_;
}
else
{
lean_object* v_reuseFailAlloc_2663_; 
v_reuseFailAlloc_2663_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2663_, 0, v_a_2659_);
lean_ctor_set(v_reuseFailAlloc_2663_, 1, v_x_2645_);
v___x_2661_ = v_reuseFailAlloc_2663_;
goto v_reusejp_2660_;
}
v_reusejp_2660_:
{
v_x_2644_ = v_tail_2654_;
v_x_2645_ = v___x_2661_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__1___boxed(lean_object* v_x_2680_, lean_object* v_x_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_, lean_object* v___y_2685_, lean_object* v___y_2686_){
_start:
{
lean_object* v_res_2687_; 
v_res_2687_ = l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__1(v_x_2680_, v_x_2681_, v___y_2682_, v___y_2683_, v___y_2684_, v___y_2685_);
lean_dec(v___y_2685_);
lean_dec_ref(v___y_2684_);
lean_dec(v___y_2683_);
lean_dec_ref(v___y_2682_);
return v_res_2687_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__0(lean_object* v_a_2688_, lean_object* v_a_2689_){
_start:
{
if (lean_obj_tag(v_a_2688_) == 0)
{
lean_object* v___x_2690_; 
v___x_2690_ = l_List_reverse___redArg(v_a_2689_);
return v___x_2690_;
}
else
{
lean_object* v_head_2691_; lean_object* v_tail_2692_; lean_object* v___x_2694_; uint8_t v_isShared_2695_; uint8_t v_isSharedCheck_2701_; 
v_head_2691_ = lean_ctor_get(v_a_2688_, 0);
v_tail_2692_ = lean_ctor_get(v_a_2688_, 1);
v_isSharedCheck_2701_ = !lean_is_exclusive(v_a_2688_);
if (v_isSharedCheck_2701_ == 0)
{
v___x_2694_ = v_a_2688_;
v_isShared_2695_ = v_isSharedCheck_2701_;
goto v_resetjp_2693_;
}
else
{
lean_inc(v_tail_2692_);
lean_inc(v_head_2691_);
lean_dec(v_a_2688_);
v___x_2694_ = lean_box(0);
v_isShared_2695_ = v_isSharedCheck_2701_;
goto v_resetjp_2693_;
}
v_resetjp_2693_:
{
lean_object* v___x_2696_; lean_object* v___x_2698_; 
v___x_2696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2696_, 0, v_head_2691_);
if (v_isShared_2695_ == 0)
{
lean_ctor_set(v___x_2694_, 1, v_a_2689_);
lean_ctor_set(v___x_2694_, 0, v___x_2696_);
v___x_2698_ = v___x_2694_;
goto v_reusejp_2697_;
}
else
{
lean_object* v_reuseFailAlloc_2700_; 
v_reuseFailAlloc_2700_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2700_, 0, v___x_2696_);
lean_ctor_set(v_reuseFailAlloc_2700_, 1, v_a_2689_);
v___x_2698_ = v_reuseFailAlloc_2700_;
goto v_reusejp_2697_;
}
v_reusejp_2697_:
{
v_a_2688_ = v_tail_2692_;
v_a_2689_ = v___x_2698_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__5___lam__0(lean_object* v_gs_2704_, lean_object* v_variablesKept_2705_, lean_object* v_snd_2706_, lean_object* v_fst_2707_, lean_object* v_fst_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_, lean_object* v___y_2712_){
_start:
{
lean_object* v_lctx_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; 
v_lctx_2714_ = lean_ctor_get(v___y_2709_, 2);
v___x_2715_ = l_Lean_LocalContext_getFVarIds(v_lctx_2714_);
v___x_2716_ = lean_array_to_list(v___x_2715_);
v___x_2717_ = l_List_lengthTR___redArg(v_gs_2704_);
v___x_2718_ = ((lean_object*)(l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__5___lam__0___closed__0));
lean_inc(v___x_2716_);
v___x_2719_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), v___x_2716_, v___x_2716_, v___x_2717_, v___x_2718_);
lean_dec(v___x_2716_);
v___x_2720_ = lean_box(0);
v___x_2721_ = l_List_mapTR_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__0(v___x_2719_, v___x_2720_);
v___x_2722_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_listBoolMerge___redArg(v_variablesKept_2705_, v_snd_2706_);
v___x_2723_ = l_List_appendTR___redArg(v___x_2721_, v___x_2722_);
v___x_2724_ = l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__1(v___x_2723_, v___x_2720_, v___y_2709_, v___y_2710_, v___y_2711_, v___y_2712_);
if (lean_obj_tag(v___x_2724_) == 0)
{
lean_object* v_a_2725_; lean_object* v___x_2726_; 
v_a_2725_ = lean_ctor_get(v___x_2724_, 0);
lean_inc(v_a_2725_);
lean_dec_ref_known(v___x_2724_, 1);
v___x_2726_ = l_Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__2(v_fst_2707_, v___y_2709_, v___y_2710_, v___y_2711_, v___y_2712_);
if (lean_obj_tag(v___x_2726_) == 0)
{
lean_object* v_a_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; 
v_a_2727_ = lean_ctor_get(v___x_2726_, 0);
lean_inc(v_a_2727_);
lean_dec_ref_known(v___x_2726_, 1);
v___x_2728_ = lean_array_mk(v_a_2725_);
v___x_2729_ = l_Lean_mkAppN(v_a_2727_, v___x_2728_);
lean_dec_ref(v___x_2728_);
lean_inc(v___y_2712_);
lean_inc_ref(v___y_2711_);
lean_inc(v___y_2710_);
lean_inc_ref(v___y_2709_);
lean_inc_ref(v___x_2729_);
v___x_2730_ = lean_infer_type(v___x_2729_, v___y_2709_, v___y_2710_, v___y_2711_, v___y_2712_);
if (lean_obj_tag(v___x_2730_) == 0)
{
lean_object* v_a_2731_; lean_object* v___x_2732_; 
v_a_2731_ = lean_ctor_get(v___x_2730_, 0);
lean_inc(v_a_2731_);
lean_dec_ref_known(v___x_2730_, 1);
lean_inc(v_fst_2708_);
v___x_2732_ = l_Lean_MVarId_getType(v_fst_2708_, v___y_2709_, v___y_2710_, v___y_2711_, v___y_2712_);
if (lean_obj_tag(v___x_2732_) == 0)
{
lean_object* v_a_2733_; lean_object* v___x_2734_; 
v_a_2733_ = lean_ctor_get(v___x_2732_, 0);
lean_inc(v_a_2733_);
lean_dec_ref_known(v___x_2732_, 1);
v___x_2734_ = l_Lean_Meta_isExprDefEq(v_a_2731_, v_a_2733_, v___y_2709_, v___y_2710_, v___y_2711_, v___y_2712_);
lean_dec(v___y_2712_);
lean_dec_ref(v___y_2711_);
lean_dec_ref(v___y_2709_);
if (lean_obj_tag(v___x_2734_) == 0)
{
lean_object* v___x_2735_; 
lean_dec_ref_known(v___x_2734_, 1);
v___x_2735_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1___redArg(v_fst_2708_, v___x_2729_, v___y_2710_);
lean_dec(v___y_2710_);
return v___x_2735_;
}
else
{
lean_object* v_a_2736_; lean_object* v___x_2738_; uint8_t v_isShared_2739_; uint8_t v_isSharedCheck_2743_; 
lean_dec_ref(v___x_2729_);
lean_dec(v___y_2710_);
lean_dec(v_fst_2708_);
v_a_2736_ = lean_ctor_get(v___x_2734_, 0);
v_isSharedCheck_2743_ = !lean_is_exclusive(v___x_2734_);
if (v_isSharedCheck_2743_ == 0)
{
v___x_2738_ = v___x_2734_;
v_isShared_2739_ = v_isSharedCheck_2743_;
goto v_resetjp_2737_;
}
else
{
lean_inc(v_a_2736_);
lean_dec(v___x_2734_);
v___x_2738_ = lean_box(0);
v_isShared_2739_ = v_isSharedCheck_2743_;
goto v_resetjp_2737_;
}
v_resetjp_2737_:
{
lean_object* v___x_2741_; 
if (v_isShared_2739_ == 0)
{
v___x_2741_ = v___x_2738_;
goto v_reusejp_2740_;
}
else
{
lean_object* v_reuseFailAlloc_2742_; 
v_reuseFailAlloc_2742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2742_, 0, v_a_2736_);
v___x_2741_ = v_reuseFailAlloc_2742_;
goto v_reusejp_2740_;
}
v_reusejp_2740_:
{
return v___x_2741_;
}
}
}
}
else
{
lean_object* v_a_2744_; lean_object* v___x_2746_; uint8_t v_isShared_2747_; uint8_t v_isSharedCheck_2751_; 
lean_dec(v_a_2731_);
lean_dec_ref(v___x_2729_);
lean_dec(v___y_2712_);
lean_dec_ref(v___y_2711_);
lean_dec(v___y_2710_);
lean_dec_ref(v___y_2709_);
lean_dec(v_fst_2708_);
v_a_2744_ = lean_ctor_get(v___x_2732_, 0);
v_isSharedCheck_2751_ = !lean_is_exclusive(v___x_2732_);
if (v_isSharedCheck_2751_ == 0)
{
v___x_2746_ = v___x_2732_;
v_isShared_2747_ = v_isSharedCheck_2751_;
goto v_resetjp_2745_;
}
else
{
lean_inc(v_a_2744_);
lean_dec(v___x_2732_);
v___x_2746_ = lean_box(0);
v_isShared_2747_ = v_isSharedCheck_2751_;
goto v_resetjp_2745_;
}
v_resetjp_2745_:
{
lean_object* v___x_2749_; 
if (v_isShared_2747_ == 0)
{
v___x_2749_ = v___x_2746_;
goto v_reusejp_2748_;
}
else
{
lean_object* v_reuseFailAlloc_2750_; 
v_reuseFailAlloc_2750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2750_, 0, v_a_2744_);
v___x_2749_ = v_reuseFailAlloc_2750_;
goto v_reusejp_2748_;
}
v_reusejp_2748_:
{
return v___x_2749_;
}
}
}
}
else
{
lean_object* v_a_2752_; lean_object* v___x_2754_; uint8_t v_isShared_2755_; uint8_t v_isSharedCheck_2759_; 
lean_dec_ref(v___x_2729_);
lean_dec(v___y_2712_);
lean_dec_ref(v___y_2711_);
lean_dec(v___y_2710_);
lean_dec_ref(v___y_2709_);
lean_dec(v_fst_2708_);
v_a_2752_ = lean_ctor_get(v___x_2730_, 0);
v_isSharedCheck_2759_ = !lean_is_exclusive(v___x_2730_);
if (v_isSharedCheck_2759_ == 0)
{
v___x_2754_ = v___x_2730_;
v_isShared_2755_ = v_isSharedCheck_2759_;
goto v_resetjp_2753_;
}
else
{
lean_inc(v_a_2752_);
lean_dec(v___x_2730_);
v___x_2754_ = lean_box(0);
v_isShared_2755_ = v_isSharedCheck_2759_;
goto v_resetjp_2753_;
}
v_resetjp_2753_:
{
lean_object* v___x_2757_; 
if (v_isShared_2755_ == 0)
{
v___x_2757_ = v___x_2754_;
goto v_reusejp_2756_;
}
else
{
lean_object* v_reuseFailAlloc_2758_; 
v_reuseFailAlloc_2758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2758_, 0, v_a_2752_);
v___x_2757_ = v_reuseFailAlloc_2758_;
goto v_reusejp_2756_;
}
v_reusejp_2756_:
{
return v___x_2757_;
}
}
}
}
else
{
lean_object* v_a_2760_; lean_object* v___x_2762_; uint8_t v_isShared_2763_; uint8_t v_isSharedCheck_2767_; 
lean_dec(v_a_2725_);
lean_dec(v___y_2712_);
lean_dec_ref(v___y_2711_);
lean_dec(v___y_2710_);
lean_dec_ref(v___y_2709_);
lean_dec(v_fst_2708_);
v_a_2760_ = lean_ctor_get(v___x_2726_, 0);
v_isSharedCheck_2767_ = !lean_is_exclusive(v___x_2726_);
if (v_isSharedCheck_2767_ == 0)
{
v___x_2762_ = v___x_2726_;
v_isShared_2763_ = v_isSharedCheck_2767_;
goto v_resetjp_2761_;
}
else
{
lean_inc(v_a_2760_);
lean_dec(v___x_2726_);
v___x_2762_ = lean_box(0);
v_isShared_2763_ = v_isSharedCheck_2767_;
goto v_resetjp_2761_;
}
v_resetjp_2761_:
{
lean_object* v___x_2765_; 
if (v_isShared_2763_ == 0)
{
v___x_2765_ = v___x_2762_;
goto v_reusejp_2764_;
}
else
{
lean_object* v_reuseFailAlloc_2766_; 
v_reuseFailAlloc_2766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2766_, 0, v_a_2760_);
v___x_2765_ = v_reuseFailAlloc_2766_;
goto v_reusejp_2764_;
}
v_reusejp_2764_:
{
return v___x_2765_;
}
}
}
}
else
{
lean_object* v_a_2768_; lean_object* v___x_2770_; uint8_t v_isShared_2771_; uint8_t v_isSharedCheck_2775_; 
lean_dec(v___y_2712_);
lean_dec_ref(v___y_2711_);
lean_dec(v___y_2710_);
lean_dec_ref(v___y_2709_);
lean_dec(v_fst_2708_);
lean_dec(v_fst_2707_);
v_a_2768_ = lean_ctor_get(v___x_2724_, 0);
v_isSharedCheck_2775_ = !lean_is_exclusive(v___x_2724_);
if (v_isSharedCheck_2775_ == 0)
{
v___x_2770_ = v___x_2724_;
v_isShared_2771_ = v_isSharedCheck_2775_;
goto v_resetjp_2769_;
}
else
{
lean_inc(v_a_2768_);
lean_dec(v___x_2724_);
v___x_2770_ = lean_box(0);
v_isShared_2771_ = v_isSharedCheck_2775_;
goto v_resetjp_2769_;
}
v_resetjp_2769_:
{
lean_object* v___x_2773_; 
if (v_isShared_2771_ == 0)
{
v___x_2773_ = v___x_2770_;
goto v_reusejp_2772_;
}
else
{
lean_object* v_reuseFailAlloc_2774_; 
v_reuseFailAlloc_2774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2774_, 0, v_a_2768_);
v___x_2773_ = v_reuseFailAlloc_2774_;
goto v_reusejp_2772_;
}
v_reusejp_2772_:
{
return v___x_2773_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__5___lam__0___boxed(lean_object* v_gs_2776_, lean_object* v_variablesKept_2777_, lean_object* v_snd_2778_, lean_object* v_fst_2779_, lean_object* v_fst_2780_, lean_object* v___y_2781_, lean_object* v___y_2782_, lean_object* v___y_2783_, lean_object* v___y_2784_, lean_object* v___y_2785_){
_start:
{
lean_object* v_res_2786_; 
v_res_2786_ = l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__5___lam__0(v_gs_2776_, v_variablesKept_2777_, v_snd_2778_, v_fst_2779_, v_fst_2780_, v___y_2781_, v___y_2782_, v___y_2783_, v___y_2784_);
lean_dec(v_gs_2776_);
return v_res_2786_;
}
}
static lean_object* _init_l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__4___closed__1(void){
_start:
{
lean_object* v___x_2788_; lean_object* v___x_2789_; 
v___x_2788_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__4___closed__0));
v___x_2789_ = l_Lean_stringToMessageData(v___x_2788_);
return v___x_2789_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__4(lean_object* v_x_2790_, lean_object* v_x_2791_, lean_object* v___y_2792_, lean_object* v___y_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_){
_start:
{
if (lean_obj_tag(v_x_2791_) == 0)
{
lean_object* v___x_2797_; 
v___x_2797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2797_, 0, v_x_2790_);
return v___x_2797_;
}
else
{
lean_object* v_tail_2798_; uint8_t v___x_2799_; lean_object* v___x_2800_; 
v_tail_2798_ = lean_ctor_get(v_x_2791_, 1);
v___x_2799_ = 0;
v___x_2800_ = l_Lean_Meta_intro1Core(v_x_2790_, v___x_2799_, v___y_2792_, v___y_2793_, v___y_2794_, v___y_2795_);
if (lean_obj_tag(v___x_2800_) == 0)
{
lean_object* v_a_2801_; lean_object* v_fst_2802_; lean_object* v_snd_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; 
v_a_2801_ = lean_ctor_get(v___x_2800_, 0);
lean_inc(v_a_2801_);
lean_dec_ref_known(v___x_2800_, 1);
v_fst_2802_ = lean_ctor_get(v_a_2801_, 0);
lean_inc(v_fst_2802_);
v_snd_2803_ = lean_ctor_get(v_a_2801_, 1);
lean_inc(v_snd_2803_);
lean_dec(v_a_2801_);
v___x_2804_ = lean_unsigned_to_nat(0u);
v___x_2805_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toCases___closed__1));
v___x_2806_ = lean_box(0);
v___x_2807_ = l_Lean_MVarId_cases(v_snd_2803_, v_fst_2802_, v___x_2805_, v___x_2799_, v___x_2806_, v___y_2792_, v___y_2793_, v___y_2794_, v___y_2795_);
if (lean_obj_tag(v___x_2807_) == 0)
{
lean_object* v_a_2808_; lean_object* v___x_2809_; lean_object* v___x_2810_; uint8_t v___x_2811_; 
v_a_2808_ = lean_ctor_get(v___x_2807_, 0);
lean_inc(v_a_2808_);
lean_dec_ref_known(v___x_2807_, 1);
v___x_2809_ = lean_array_get_size(v_a_2808_);
v___x_2810_ = lean_unsigned_to_nat(1u);
v___x_2811_ = lean_nat_dec_eq(v___x_2809_, v___x_2810_);
if (v___x_2811_ == 0)
{
lean_object* v___x_2812_; lean_object* v___x_2813_; 
lean_dec(v_a_2808_);
v___x_2812_ = lean_obj_once(&l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__4___closed__1, &l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__4___closed__1_once, _init_l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__4___closed__1);
v___x_2813_ = l_Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0___redArg(v___x_2812_, v___y_2792_, v___y_2793_, v___y_2794_, v___y_2795_);
return v___x_2813_;
}
else
{
lean_object* v___x_2814_; lean_object* v_toInductionSubgoal_2815_; lean_object* v_mvarId_2816_; 
v___x_2814_ = lean_array_fget(v_a_2808_, v___x_2804_);
lean_dec(v_a_2808_);
v_toInductionSubgoal_2815_ = lean_ctor_get(v___x_2814_, 0);
lean_inc_ref(v_toInductionSubgoal_2815_);
lean_dec(v___x_2814_);
v_mvarId_2816_ = lean_ctor_get(v_toInductionSubgoal_2815_, 0);
lean_inc(v_mvarId_2816_);
lean_dec_ref(v_toInductionSubgoal_2815_);
v_x_2790_ = v_mvarId_2816_;
v_x_2791_ = v_tail_2798_;
goto _start;
}
}
else
{
lean_object* v_a_2818_; lean_object* v___x_2820_; uint8_t v_isShared_2821_; uint8_t v_isSharedCheck_2825_; 
v_a_2818_ = lean_ctor_get(v___x_2807_, 0);
v_isSharedCheck_2825_ = !lean_is_exclusive(v___x_2807_);
if (v_isSharedCheck_2825_ == 0)
{
v___x_2820_ = v___x_2807_;
v_isShared_2821_ = v_isSharedCheck_2825_;
goto v_resetjp_2819_;
}
else
{
lean_inc(v_a_2818_);
lean_dec(v___x_2807_);
v___x_2820_ = lean_box(0);
v_isShared_2821_ = v_isSharedCheck_2825_;
goto v_resetjp_2819_;
}
v_resetjp_2819_:
{
lean_object* v___x_2823_; 
if (v_isShared_2821_ == 0)
{
v___x_2823_ = v___x_2820_;
goto v_reusejp_2822_;
}
else
{
lean_object* v_reuseFailAlloc_2824_; 
v_reuseFailAlloc_2824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2824_, 0, v_a_2818_);
v___x_2823_ = v_reuseFailAlloc_2824_;
goto v_reusejp_2822_;
}
v_reusejp_2822_:
{
return v___x_2823_;
}
}
}
}
else
{
lean_object* v_a_2826_; lean_object* v___x_2828_; uint8_t v_isShared_2829_; uint8_t v_isSharedCheck_2833_; 
v_a_2826_ = lean_ctor_get(v___x_2800_, 0);
v_isSharedCheck_2833_ = !lean_is_exclusive(v___x_2800_);
if (v_isSharedCheck_2833_ == 0)
{
v___x_2828_ = v___x_2800_;
v_isShared_2829_ = v_isSharedCheck_2833_;
goto v_resetjp_2827_;
}
else
{
lean_inc(v_a_2826_);
lean_dec(v___x_2800_);
v___x_2828_ = lean_box(0);
v_isShared_2829_ = v_isSharedCheck_2833_;
goto v_resetjp_2827_;
}
v_resetjp_2827_:
{
lean_object* v___x_2831_; 
if (v_isShared_2829_ == 0)
{
v___x_2831_ = v___x_2828_;
goto v_reusejp_2830_;
}
else
{
lean_object* v_reuseFailAlloc_2832_; 
v_reuseFailAlloc_2832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2832_, 0, v_a_2826_);
v___x_2831_ = v_reuseFailAlloc_2832_;
goto v_reusejp_2830_;
}
v_reusejp_2830_:
{
return v___x_2831_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__4___boxed(lean_object* v_x_2834_, lean_object* v_x_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_, lean_object* v___y_2839_, lean_object* v___y_2840_){
_start:
{
lean_object* v_res_2841_; 
v_res_2841_ = l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__4(v_x_2834_, v_x_2835_, v___y_2836_, v___y_2837_, v___y_2838_, v___y_2839_);
lean_dec(v___y_2839_);
lean_dec_ref(v___y_2838_);
lean_dec(v___y_2837_);
lean_dec_ref(v___y_2836_);
lean_dec(v_x_2835_);
return v_res_2841_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__3(lean_object* v_a_2842_, lean_object* v_a_2843_){
_start:
{
if (lean_obj_tag(v_a_2842_) == 0)
{
lean_object* v___x_2844_; 
v___x_2844_ = l_List_reverse___redArg(v_a_2843_);
return v___x_2844_;
}
else
{
lean_object* v_head_2845_; uint8_t v___x_2846_; 
v_head_2845_ = lean_ctor_get(v_a_2842_, 0);
v___x_2846_ = lean_unbox(v_head_2845_);
if (v___x_2846_ == 0)
{
lean_object* v_tail_2847_; 
v_tail_2847_ = lean_ctor_get(v_a_2842_, 1);
lean_inc(v_tail_2847_);
lean_dec_ref_known(v_a_2842_, 2);
v_a_2842_ = v_tail_2847_;
goto _start;
}
else
{
lean_object* v_tail_2849_; lean_object* v___x_2851_; uint8_t v_isShared_2852_; uint8_t v_isSharedCheck_2857_; 
lean_inc(v_head_2845_);
v_tail_2849_ = lean_ctor_get(v_a_2842_, 1);
v_isSharedCheck_2857_ = !lean_is_exclusive(v_a_2842_);
if (v_isSharedCheck_2857_ == 0)
{
lean_object* v_unused_2858_; 
v_unused_2858_ = lean_ctor_get(v_a_2842_, 0);
lean_dec(v_unused_2858_);
v___x_2851_ = v_a_2842_;
v_isShared_2852_ = v_isSharedCheck_2857_;
goto v_resetjp_2850_;
}
else
{
lean_inc(v_tail_2849_);
lean_dec(v_a_2842_);
v___x_2851_ = lean_box(0);
v_isShared_2852_ = v_isSharedCheck_2857_;
goto v_resetjp_2850_;
}
v_resetjp_2850_:
{
lean_object* v___x_2854_; 
if (v_isShared_2852_ == 0)
{
lean_ctor_set(v___x_2851_, 1, v_a_2843_);
v___x_2854_ = v___x_2851_;
goto v_reusejp_2853_;
}
else
{
lean_object* v_reuseFailAlloc_2856_; 
v_reuseFailAlloc_2856_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2856_, 0, v_head_2845_);
lean_ctor_set(v_reuseFailAlloc_2856_, 1, v_a_2843_);
v___x_2854_ = v_reuseFailAlloc_2856_;
goto v_reusejp_2853_;
}
v_reusejp_2853_:
{
v_a_2842_ = v_tail_2849_;
v_a_2843_ = v___x_2854_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__5(lean_object* v_gs_2859_, lean_object* v_x_2860_, lean_object* v_x_2861_, lean_object* v___y_2862_, lean_object* v___y_2863_, lean_object* v___y_2864_, lean_object* v___y_2865_){
_start:
{
if (lean_obj_tag(v_x_2860_) == 0)
{
lean_object* v___x_2867_; lean_object* v___x_2868_; 
lean_dec(v_gs_2859_);
v___x_2867_ = l_List_reverse___redArg(v_x_2861_);
v___x_2868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2868_, 0, v___x_2867_);
return v___x_2868_;
}
else
{
lean_object* v_head_2869_; lean_object* v_snd_2870_; lean_object* v_fst_2871_; lean_object* v_snd_2872_; lean_object* v_tail_2873_; lean_object* v___x_2875_; uint8_t v_isShared_2876_; uint8_t v_isSharedCheck_2997_; 
v_head_2869_ = lean_ctor_get(v_x_2860_, 0);
lean_inc(v_head_2869_);
v_snd_2870_ = lean_ctor_get(v_head_2869_, 1);
v_fst_2871_ = lean_ctor_get(v_snd_2870_, 0);
lean_inc(v_fst_2871_);
v_snd_2872_ = lean_ctor_get(v_snd_2870_, 1);
lean_inc(v_snd_2872_);
v_tail_2873_ = lean_ctor_get(v_x_2860_, 1);
v_isSharedCheck_2997_ = !lean_is_exclusive(v_x_2860_);
if (v_isSharedCheck_2997_ == 0)
{
lean_object* v_unused_2998_; 
v_unused_2998_ = lean_ctor_get(v_x_2860_, 0);
lean_dec(v_unused_2998_);
v___x_2875_ = v_x_2860_;
v_isShared_2876_ = v_isSharedCheck_2997_;
goto v_resetjp_2874_;
}
else
{
lean_inc(v_tail_2873_);
lean_dec(v_x_2860_);
v___x_2875_ = lean_box(0);
v_isShared_2876_ = v_isSharedCheck_2997_;
goto v_resetjp_2874_;
}
v_resetjp_2874_:
{
lean_object* v_fst_2877_; lean_object* v_fst_2878_; lean_object* v_snd_2879_; lean_object* v_variablesKept_2880_; lean_object* v_neqs_2881_; lean_object* v_fst_2883_; lean_object* v_snd_2884_; lean_object* v___y_2885_; lean_object* v___y_2886_; lean_object* v___y_2887_; lean_object* v___y_2888_; lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; 
v_fst_2877_ = lean_ctor_get(v_head_2869_, 0);
lean_inc(v_fst_2877_);
lean_dec(v_head_2869_);
v_fst_2878_ = lean_ctor_get(v_fst_2871_, 0);
lean_inc(v_fst_2878_);
v_snd_2879_ = lean_ctor_get(v_fst_2871_, 1);
lean_inc(v_snd_2879_);
lean_dec(v_fst_2871_);
v_variablesKept_2880_ = lean_ctor_get(v_snd_2872_, 0);
lean_inc_n(v_variablesKept_2880_, 2);
v_neqs_2881_ = lean_ctor_get(v_snd_2872_, 1);
lean_inc(v_neqs_2881_);
lean_dec(v_snd_2872_);
v___x_2904_ = lean_box(0);
v___x_2905_ = l_List_filterTR_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__3(v_variablesKept_2880_, v___x_2904_);
v___x_2906_ = l_List_lengthTR___redArg(v___x_2905_);
lean_dec(v___x_2905_);
if (lean_obj_tag(v_neqs_2881_) == 0)
{
lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; 
v___x_2907_ = lean_unsigned_to_nat(1u);
v___x_2908_ = lean_nat_sub(v___x_2906_, v___x_2907_);
lean_dec(v___x_2906_);
v___x_2909_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesProd(v___x_2908_, v_snd_2879_, v_fst_2878_, v___y_2862_, v___y_2863_, v___y_2864_, v___y_2865_);
lean_dec(v___x_2908_);
if (lean_obj_tag(v___x_2909_) == 0)
{
lean_object* v_a_2910_; lean_object* v_fst_2911_; lean_object* v_snd_2912_; 
v_a_2910_ = lean_ctor_get(v___x_2909_, 0);
lean_inc(v_a_2910_);
lean_dec_ref_known(v___x_2909_, 1);
v_fst_2911_ = lean_ctor_get(v_a_2910_, 0);
lean_inc(v_fst_2911_);
v_snd_2912_ = lean_ctor_get(v_a_2910_, 1);
lean_inc(v_snd_2912_);
lean_dec(v_a_2910_);
v_fst_2883_ = v_fst_2911_;
v_snd_2884_ = v_snd_2912_;
v___y_2885_ = v___y_2862_;
v___y_2886_ = v___y_2863_;
v___y_2887_ = v___y_2864_;
v___y_2888_ = v___y_2865_;
goto v___jp_2882_;
}
else
{
lean_object* v_a_2913_; lean_object* v___x_2915_; uint8_t v_isShared_2916_; uint8_t v_isSharedCheck_2920_; 
lean_dec(v_variablesKept_2880_);
lean_dec(v_fst_2877_);
lean_del_object(v___x_2875_);
lean_dec(v_tail_2873_);
lean_dec(v_x_2861_);
lean_dec(v_gs_2859_);
v_a_2913_ = lean_ctor_get(v___x_2909_, 0);
v_isSharedCheck_2920_ = !lean_is_exclusive(v___x_2909_);
if (v_isSharedCheck_2920_ == 0)
{
v___x_2915_ = v___x_2909_;
v_isShared_2916_ = v_isSharedCheck_2920_;
goto v_resetjp_2914_;
}
else
{
lean_inc(v_a_2913_);
lean_dec(v___x_2909_);
v___x_2915_ = lean_box(0);
v_isShared_2916_ = v_isSharedCheck_2920_;
goto v_resetjp_2914_;
}
v_resetjp_2914_:
{
lean_object* v___x_2918_; 
if (v_isShared_2916_ == 0)
{
v___x_2918_ = v___x_2915_;
goto v_reusejp_2917_;
}
else
{
lean_object* v_reuseFailAlloc_2919_; 
v_reuseFailAlloc_2919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2919_, 0, v_a_2913_);
v___x_2918_ = v_reuseFailAlloc_2919_;
goto v_reusejp_2917_;
}
v_reusejp_2917_:
{
return v___x_2918_;
}
}
}
}
else
{
lean_object* v_val_2921_; lean_object* v___x_2922_; lean_object* v_zero_2923_; uint8_t v_isZero_2924_; 
v_val_2921_ = lean_ctor_get(v_neqs_2881_, 0);
lean_inc(v_val_2921_);
lean_dec_ref_known(v_neqs_2881_, 1);
v___x_2922_ = lean_box(0);
v_zero_2923_ = lean_unsigned_to_nat(0u);
v_isZero_2924_ = lean_nat_dec_eq(v_val_2921_, v_zero_2923_);
if (v_isZero_2924_ == 1)
{
lean_object* v___x_2925_; 
lean_dec(v_val_2921_);
v___x_2925_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesProd(v___x_2906_, v_snd_2879_, v_fst_2878_, v___y_2862_, v___y_2863_, v___y_2864_, v___y_2865_);
lean_dec(v___x_2906_);
if (lean_obj_tag(v___x_2925_) == 0)
{
lean_object* v_a_2926_; lean_object* v_fst_2927_; lean_object* v_snd_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; 
v_a_2926_ = lean_ctor_get(v___x_2925_, 0);
lean_inc(v_a_2926_);
lean_dec_ref_known(v___x_2925_, 1);
v_fst_2927_ = lean_ctor_get(v_a_2926_, 0);
lean_inc(v_fst_2927_);
v_snd_2928_ = lean_ctor_get(v_a_2926_, 1);
lean_inc(v_snd_2928_);
lean_dec(v_a_2926_);
v___x_2929_ = l_List_getLast_x21___redArg(v___x_2922_, v_snd_2928_);
v___x_2930_ = l_Lean_MVarId_tryClear(v_fst_2927_, v___x_2929_, v___y_2862_, v___y_2863_, v___y_2864_, v___y_2865_);
if (lean_obj_tag(v___x_2930_) == 0)
{
lean_object* v_a_2931_; 
v_a_2931_ = lean_ctor_get(v___x_2930_, 0);
lean_inc(v_a_2931_);
lean_dec_ref_known(v___x_2930_, 1);
v_fst_2883_ = v_a_2931_;
v_snd_2884_ = v_snd_2928_;
v___y_2885_ = v___y_2862_;
v___y_2886_ = v___y_2863_;
v___y_2887_ = v___y_2864_;
v___y_2888_ = v___y_2865_;
goto v___jp_2882_;
}
else
{
lean_object* v_a_2932_; lean_object* v___x_2934_; uint8_t v_isShared_2935_; uint8_t v_isSharedCheck_2939_; 
lean_dec(v_snd_2928_);
lean_dec(v_variablesKept_2880_);
lean_dec(v_fst_2877_);
lean_del_object(v___x_2875_);
lean_dec(v_tail_2873_);
lean_dec(v_x_2861_);
lean_dec(v_gs_2859_);
v_a_2932_ = lean_ctor_get(v___x_2930_, 0);
v_isSharedCheck_2939_ = !lean_is_exclusive(v___x_2930_);
if (v_isSharedCheck_2939_ == 0)
{
v___x_2934_ = v___x_2930_;
v_isShared_2935_ = v_isSharedCheck_2939_;
goto v_resetjp_2933_;
}
else
{
lean_inc(v_a_2932_);
lean_dec(v___x_2930_);
v___x_2934_ = lean_box(0);
v_isShared_2935_ = v_isSharedCheck_2939_;
goto v_resetjp_2933_;
}
v_resetjp_2933_:
{
lean_object* v___x_2937_; 
if (v_isShared_2935_ == 0)
{
v___x_2937_ = v___x_2934_;
goto v_reusejp_2936_;
}
else
{
lean_object* v_reuseFailAlloc_2938_; 
v_reuseFailAlloc_2938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2938_, 0, v_a_2932_);
v___x_2937_ = v_reuseFailAlloc_2938_;
goto v_reusejp_2936_;
}
v_reusejp_2936_:
{
return v___x_2937_;
}
}
}
}
else
{
lean_object* v_a_2940_; lean_object* v___x_2942_; uint8_t v_isShared_2943_; uint8_t v_isSharedCheck_2947_; 
lean_dec(v_variablesKept_2880_);
lean_dec(v_fst_2877_);
lean_del_object(v___x_2875_);
lean_dec(v_tail_2873_);
lean_dec(v_x_2861_);
lean_dec(v_gs_2859_);
v_a_2940_ = lean_ctor_get(v___x_2925_, 0);
v_isSharedCheck_2947_ = !lean_is_exclusive(v___x_2925_);
if (v_isSharedCheck_2947_ == 0)
{
v___x_2942_ = v___x_2925_;
v_isShared_2943_ = v_isSharedCheck_2947_;
goto v_resetjp_2941_;
}
else
{
lean_inc(v_a_2940_);
lean_dec(v___x_2925_);
v___x_2942_ = lean_box(0);
v_isShared_2943_ = v_isSharedCheck_2947_;
goto v_resetjp_2941_;
}
v_resetjp_2941_:
{
lean_object* v___x_2945_; 
if (v_isShared_2943_ == 0)
{
v___x_2945_ = v___x_2942_;
goto v_reusejp_2944_;
}
else
{
lean_object* v_reuseFailAlloc_2946_; 
v_reuseFailAlloc_2946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2946_, 0, v_a_2940_);
v___x_2945_ = v_reuseFailAlloc_2946_;
goto v_reusejp_2944_;
}
v_reusejp_2944_:
{
return v___x_2945_;
}
}
}
}
else
{
lean_object* v_one_2948_; lean_object* v_n_2949_; lean_object* v___x_2950_; 
v_one_2948_ = lean_unsigned_to_nat(1u);
v_n_2949_ = lean_nat_sub(v_val_2921_, v_one_2948_);
lean_dec(v_val_2921_);
v___x_2950_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesProd(v___x_2906_, v_snd_2879_, v_fst_2878_, v___y_2862_, v___y_2863_, v___y_2864_, v___y_2865_);
lean_dec(v___x_2906_);
if (lean_obj_tag(v___x_2950_) == 0)
{
lean_object* v_a_2951_; lean_object* v_fst_2952_; lean_object* v_snd_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; 
v_a_2951_ = lean_ctor_get(v___x_2950_, 0);
lean_inc(v_a_2951_);
lean_dec_ref_known(v___x_2950_, 1);
v_fst_2952_ = lean_ctor_get(v_a_2951_, 0);
lean_inc(v_fst_2952_);
v_snd_2953_ = lean_ctor_get(v_a_2951_, 1);
lean_inc(v_snd_2953_);
lean_dec(v_a_2951_);
v___x_2954_ = l_List_getLast_x21___redArg(v___x_2922_, v_snd_2953_);
v___x_2955_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesProd(v_n_2949_, v_fst_2952_, v___x_2954_, v___y_2862_, v___y_2863_, v___y_2864_, v___y_2865_);
lean_dec(v_n_2949_);
if (lean_obj_tag(v___x_2955_) == 0)
{
lean_object* v_a_2956_; lean_object* v_fst_2957_; lean_object* v_snd_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; 
v_a_2956_ = lean_ctor_get(v___x_2955_, 0);
lean_inc(v_a_2956_);
lean_dec_ref_known(v___x_2955_, 1);
v_fst_2957_ = lean_ctor_get(v_a_2956_, 0);
lean_inc(v_fst_2957_);
v_snd_2958_ = lean_ctor_get(v_a_2956_, 1);
lean_inc_n(v_snd_2958_, 2);
lean_dec(v_a_2956_);
v___x_2959_ = lean_array_mk(v_snd_2958_);
v___x_2960_ = l_Lean_MVarId_revert(v_fst_2957_, v___x_2959_, v_isZero_2924_, v_isZero_2924_, v___y_2862_, v___y_2863_, v___y_2864_, v___y_2865_);
if (lean_obj_tag(v___x_2960_) == 0)
{
lean_object* v_a_2961_; lean_object* v_snd_2962_; lean_object* v___x_2963_; 
v_a_2961_ = lean_ctor_get(v___x_2960_, 0);
lean_inc(v_a_2961_);
lean_dec_ref_known(v___x_2960_, 1);
v_snd_2962_ = lean_ctor_get(v_a_2961_, 1);
lean_inc(v_snd_2962_);
lean_dec(v_a_2961_);
v___x_2963_ = l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__4(v_snd_2962_, v_snd_2958_, v___y_2862_, v___y_2863_, v___y_2864_, v___y_2865_);
lean_dec(v_snd_2958_);
if (lean_obj_tag(v___x_2963_) == 0)
{
lean_object* v_a_2964_; 
v_a_2964_ = lean_ctor_get(v___x_2963_, 0);
lean_inc(v_a_2964_);
lean_dec_ref_known(v___x_2963_, 1);
v_fst_2883_ = v_a_2964_;
v_snd_2884_ = v_snd_2953_;
v___y_2885_ = v___y_2862_;
v___y_2886_ = v___y_2863_;
v___y_2887_ = v___y_2864_;
v___y_2888_ = v___y_2865_;
goto v___jp_2882_;
}
else
{
lean_object* v_a_2965_; lean_object* v___x_2967_; uint8_t v_isShared_2968_; uint8_t v_isSharedCheck_2972_; 
lean_dec(v_snd_2953_);
lean_dec(v_variablesKept_2880_);
lean_dec(v_fst_2877_);
lean_del_object(v___x_2875_);
lean_dec(v_tail_2873_);
lean_dec(v_x_2861_);
lean_dec(v_gs_2859_);
v_a_2965_ = lean_ctor_get(v___x_2963_, 0);
v_isSharedCheck_2972_ = !lean_is_exclusive(v___x_2963_);
if (v_isSharedCheck_2972_ == 0)
{
v___x_2967_ = v___x_2963_;
v_isShared_2968_ = v_isSharedCheck_2972_;
goto v_resetjp_2966_;
}
else
{
lean_inc(v_a_2965_);
lean_dec(v___x_2963_);
v___x_2967_ = lean_box(0);
v_isShared_2968_ = v_isSharedCheck_2972_;
goto v_resetjp_2966_;
}
v_resetjp_2966_:
{
lean_object* v___x_2970_; 
if (v_isShared_2968_ == 0)
{
v___x_2970_ = v___x_2967_;
goto v_reusejp_2969_;
}
else
{
lean_object* v_reuseFailAlloc_2971_; 
v_reuseFailAlloc_2971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2971_, 0, v_a_2965_);
v___x_2970_ = v_reuseFailAlloc_2971_;
goto v_reusejp_2969_;
}
v_reusejp_2969_:
{
return v___x_2970_;
}
}
}
}
else
{
lean_object* v_a_2973_; lean_object* v___x_2975_; uint8_t v_isShared_2976_; uint8_t v_isSharedCheck_2980_; 
lean_dec(v_snd_2958_);
lean_dec(v_snd_2953_);
lean_dec(v_variablesKept_2880_);
lean_dec(v_fst_2877_);
lean_del_object(v___x_2875_);
lean_dec(v_tail_2873_);
lean_dec(v_x_2861_);
lean_dec(v_gs_2859_);
v_a_2973_ = lean_ctor_get(v___x_2960_, 0);
v_isSharedCheck_2980_ = !lean_is_exclusive(v___x_2960_);
if (v_isSharedCheck_2980_ == 0)
{
v___x_2975_ = v___x_2960_;
v_isShared_2976_ = v_isSharedCheck_2980_;
goto v_resetjp_2974_;
}
else
{
lean_inc(v_a_2973_);
lean_dec(v___x_2960_);
v___x_2975_ = lean_box(0);
v_isShared_2976_ = v_isSharedCheck_2980_;
goto v_resetjp_2974_;
}
v_resetjp_2974_:
{
lean_object* v___x_2978_; 
if (v_isShared_2976_ == 0)
{
v___x_2978_ = v___x_2975_;
goto v_reusejp_2977_;
}
else
{
lean_object* v_reuseFailAlloc_2979_; 
v_reuseFailAlloc_2979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2979_, 0, v_a_2973_);
v___x_2978_ = v_reuseFailAlloc_2979_;
goto v_reusejp_2977_;
}
v_reusejp_2977_:
{
return v___x_2978_;
}
}
}
}
else
{
lean_object* v_a_2981_; lean_object* v___x_2983_; uint8_t v_isShared_2984_; uint8_t v_isSharedCheck_2988_; 
lean_dec(v_snd_2953_);
lean_dec(v_variablesKept_2880_);
lean_dec(v_fst_2877_);
lean_del_object(v___x_2875_);
lean_dec(v_tail_2873_);
lean_dec(v_x_2861_);
lean_dec(v_gs_2859_);
v_a_2981_ = lean_ctor_get(v___x_2955_, 0);
v_isSharedCheck_2988_ = !lean_is_exclusive(v___x_2955_);
if (v_isSharedCheck_2988_ == 0)
{
v___x_2983_ = v___x_2955_;
v_isShared_2984_ = v_isSharedCheck_2988_;
goto v_resetjp_2982_;
}
else
{
lean_inc(v_a_2981_);
lean_dec(v___x_2955_);
v___x_2983_ = lean_box(0);
v_isShared_2984_ = v_isSharedCheck_2988_;
goto v_resetjp_2982_;
}
v_resetjp_2982_:
{
lean_object* v___x_2986_; 
if (v_isShared_2984_ == 0)
{
v___x_2986_ = v___x_2983_;
goto v_reusejp_2985_;
}
else
{
lean_object* v_reuseFailAlloc_2987_; 
v_reuseFailAlloc_2987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2987_, 0, v_a_2981_);
v___x_2986_ = v_reuseFailAlloc_2987_;
goto v_reusejp_2985_;
}
v_reusejp_2985_:
{
return v___x_2986_;
}
}
}
}
else
{
lean_object* v_a_2989_; lean_object* v___x_2991_; uint8_t v_isShared_2992_; uint8_t v_isSharedCheck_2996_; 
lean_dec(v_n_2949_);
lean_dec(v_variablesKept_2880_);
lean_dec(v_fst_2877_);
lean_del_object(v___x_2875_);
lean_dec(v_tail_2873_);
lean_dec(v_x_2861_);
lean_dec(v_gs_2859_);
v_a_2989_ = lean_ctor_get(v___x_2950_, 0);
v_isSharedCheck_2996_ = !lean_is_exclusive(v___x_2950_);
if (v_isSharedCheck_2996_ == 0)
{
v___x_2991_ = v___x_2950_;
v_isShared_2992_ = v_isSharedCheck_2996_;
goto v_resetjp_2990_;
}
else
{
lean_inc(v_a_2989_);
lean_dec(v___x_2950_);
v___x_2991_ = lean_box(0);
v_isShared_2992_ = v_isSharedCheck_2996_;
goto v_resetjp_2990_;
}
v_resetjp_2990_:
{
lean_object* v___x_2994_; 
if (v_isShared_2992_ == 0)
{
v___x_2994_ = v___x_2991_;
goto v_reusejp_2993_;
}
else
{
lean_object* v_reuseFailAlloc_2995_; 
v_reuseFailAlloc_2995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2995_, 0, v_a_2989_);
v___x_2994_ = v_reuseFailAlloc_2995_;
goto v_reusejp_2993_;
}
v_reusejp_2993_:
{
return v___x_2994_;
}
}
}
}
}
v___jp_2882_:
{
lean_object* v___f_2889_; lean_object* v___x_2890_; 
lean_inc(v_fst_2883_);
lean_inc(v_gs_2859_);
v___f_2889_ = lean_alloc_closure((void*)(l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__5___lam__0___boxed), 10, 5);
lean_closure_set(v___f_2889_, 0, v_gs_2859_);
lean_closure_set(v___f_2889_, 1, v_variablesKept_2880_);
lean_closure_set(v___f_2889_, 2, v_snd_2884_);
lean_closure_set(v___f_2889_, 3, v_fst_2877_);
lean_closure_set(v___f_2889_, 4, v_fst_2883_);
v___x_2890_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor_spec__0___redArg(v_fst_2883_, v___f_2889_, v___y_2885_, v___y_2886_, v___y_2887_, v___y_2888_);
if (lean_obj_tag(v___x_2890_) == 0)
{
lean_object* v_a_2891_; lean_object* v___x_2893_; 
v_a_2891_ = lean_ctor_get(v___x_2890_, 0);
lean_inc(v_a_2891_);
lean_dec_ref_known(v___x_2890_, 1);
if (v_isShared_2876_ == 0)
{
lean_ctor_set(v___x_2875_, 1, v_x_2861_);
lean_ctor_set(v___x_2875_, 0, v_a_2891_);
v___x_2893_ = v___x_2875_;
goto v_reusejp_2892_;
}
else
{
lean_object* v_reuseFailAlloc_2895_; 
v_reuseFailAlloc_2895_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2895_, 0, v_a_2891_);
lean_ctor_set(v_reuseFailAlloc_2895_, 1, v_x_2861_);
v___x_2893_ = v_reuseFailAlloc_2895_;
goto v_reusejp_2892_;
}
v_reusejp_2892_:
{
v_x_2860_ = v_tail_2873_;
v_x_2861_ = v___x_2893_;
goto _start;
}
}
else
{
lean_object* v_a_2896_; lean_object* v___x_2898_; uint8_t v_isShared_2899_; uint8_t v_isSharedCheck_2903_; 
lean_del_object(v___x_2875_);
lean_dec(v_tail_2873_);
lean_dec(v_x_2861_);
lean_dec(v_gs_2859_);
v_a_2896_ = lean_ctor_get(v___x_2890_, 0);
v_isSharedCheck_2903_ = !lean_is_exclusive(v___x_2890_);
if (v_isSharedCheck_2903_ == 0)
{
v___x_2898_ = v___x_2890_;
v_isShared_2899_ = v_isSharedCheck_2903_;
goto v_resetjp_2897_;
}
else
{
lean_inc(v_a_2896_);
lean_dec(v___x_2890_);
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
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__5___boxed(lean_object* v_gs_2999_, lean_object* v_x_3000_, lean_object* v_x_3001_, lean_object* v___y_3002_, lean_object* v___y_3003_, lean_object* v___y_3004_, lean_object* v___y_3005_, lean_object* v___y_3006_){
_start:
{
lean_object* v_res_3007_; 
v_res_3007_ = l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__5(v_gs_2999_, v_x_3000_, v_x_3001_, v___y_3002_, v___y_3003_, v___y_3004_, v___y_3005_);
lean_dec(v___y_3005_);
lean_dec_ref(v___y_3004_);
lean_dec(v___y_3003_);
lean_dec_ref(v___y_3002_);
return v_res_3007_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive(lean_object* v_mvar_3012_, lean_object* v_cs_3013_, lean_object* v_gs_3014_, lean_object* v_s_3015_, lean_object* v_h_3016_, lean_object* v_a_3017_, lean_object* v_a_3018_, lean_object* v_a_3019_, lean_object* v_a_3020_){
_start:
{
lean_object* v___x_3022_; lean_object* v_zero_3023_; uint8_t v_isZero_3024_; 
v___x_3022_ = l_List_lengthTR___redArg(v_s_3015_);
v_zero_3023_ = lean_unsigned_to_nat(0u);
v_isZero_3024_ = lean_nat_dec_eq(v___x_3022_, v_zero_3023_);
if (v_isZero_3024_ == 1)
{
lean_object* v___x_3025_; uint8_t v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; 
lean_dec(v___x_3022_);
lean_dec(v_s_3015_);
lean_dec(v_gs_3014_);
lean_dec(v_cs_3013_);
v___x_3025_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toCases___closed__1));
v___x_3026_ = 0;
v___x_3027_ = lean_box(0);
v___x_3028_ = l_Lean_MVarId_cases(v_mvar_3012_, v_h_3016_, v___x_3025_, v___x_3026_, v___x_3027_, v_a_3017_, v_a_3018_, v_a_3019_, v_a_3020_);
if (lean_obj_tag(v___x_3028_) == 0)
{
lean_object* v___x_3030_; uint8_t v_isShared_3031_; uint8_t v_isSharedCheck_3036_; 
v_isSharedCheck_3036_ = !lean_is_exclusive(v___x_3028_);
if (v_isSharedCheck_3036_ == 0)
{
lean_object* v_unused_3037_; 
v_unused_3037_ = lean_ctor_get(v___x_3028_, 0);
lean_dec(v_unused_3037_);
v___x_3030_ = v___x_3028_;
v_isShared_3031_ = v_isSharedCheck_3036_;
goto v_resetjp_3029_;
}
else
{
lean_dec(v___x_3028_);
v___x_3030_ = lean_box(0);
v_isShared_3031_ = v_isSharedCheck_3036_;
goto v_resetjp_3029_;
}
v_resetjp_3029_:
{
lean_object* v___x_3032_; lean_object* v___x_3034_; 
v___x_3032_ = lean_box(0);
if (v_isShared_3031_ == 0)
{
lean_ctor_set(v___x_3030_, 0, v___x_3032_);
v___x_3034_ = v___x_3030_;
goto v_reusejp_3033_;
}
else
{
lean_object* v_reuseFailAlloc_3035_; 
v_reuseFailAlloc_3035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3035_, 0, v___x_3032_);
v___x_3034_ = v_reuseFailAlloc_3035_;
goto v_reusejp_3033_;
}
v_reusejp_3033_:
{
return v___x_3034_;
}
}
}
else
{
lean_object* v_a_3038_; lean_object* v___x_3040_; uint8_t v_isShared_3041_; uint8_t v_isSharedCheck_3045_; 
v_a_3038_ = lean_ctor_get(v___x_3028_, 0);
v_isSharedCheck_3045_ = !lean_is_exclusive(v___x_3028_);
if (v_isSharedCheck_3045_ == 0)
{
v___x_3040_ = v___x_3028_;
v_isShared_3041_ = v_isSharedCheck_3045_;
goto v_resetjp_3039_;
}
else
{
lean_inc(v_a_3038_);
lean_dec(v___x_3028_);
v___x_3040_ = lean_box(0);
v_isShared_3041_ = v_isSharedCheck_3045_;
goto v_resetjp_3039_;
}
v_resetjp_3039_:
{
lean_object* v___x_3043_; 
if (v_isShared_3041_ == 0)
{
v___x_3043_ = v___x_3040_;
goto v_reusejp_3042_;
}
else
{
lean_object* v_reuseFailAlloc_3044_; 
v_reuseFailAlloc_3044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3044_, 0, v_a_3038_);
v___x_3043_ = v_reuseFailAlloc_3044_;
goto v_reusejp_3042_;
}
v_reusejp_3042_:
{
return v___x_3043_;
}
}
}
}
else
{
lean_object* v___f_3046_; lean_object* v___f_3047_; lean_object* v_one_3048_; lean_object* v_n_3049_; lean_object* v___x_3050_; 
v___f_3046_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive___closed__0));
v___f_3047_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive___closed__1));
v_one_3048_ = lean_unsigned_to_nat(1u);
v_n_3049_ = lean_nat_sub(v___x_3022_, v_one_3048_);
lean_dec(v___x_3022_);
v___x_3050_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesSum(v_n_3049_, v_mvar_3012_, v_h_3016_, v_a_3017_, v_a_3018_, v_a_3019_, v_a_3020_);
lean_dec(v_n_3049_);
if (lean_obj_tag(v___x_3050_) == 0)
{
lean_object* v_a_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; 
v_a_3051_ = lean_ctor_get(v___x_3050_, 0);
lean_inc(v_a_3051_);
lean_dec_ref_known(v___x_3050_, 1);
v___x_3052_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive___closed__2));
v___x_3053_ = l___private_Init_Data_List_Impl_0__List_zipWithTR_go(lean_box(0), lean_box(0), lean_box(0), v___f_3047_, v_a_3051_, v_s_3015_, v___x_3052_);
v___x_3054_ = l___private_Init_Data_List_Impl_0__List_zipWithTR_go(lean_box(0), lean_box(0), lean_box(0), v___f_3046_, v_cs_3013_, v___x_3053_, v___x_3052_);
v___x_3055_ = lean_box(0);
v___x_3056_ = l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__5(v_gs_3014_, v___x_3054_, v___x_3055_, v_a_3017_, v_a_3018_, v_a_3019_, v_a_3020_);
if (lean_obj_tag(v___x_3056_) == 0)
{
lean_object* v___x_3058_; uint8_t v_isShared_3059_; uint8_t v_isSharedCheck_3064_; 
v_isSharedCheck_3064_ = !lean_is_exclusive(v___x_3056_);
if (v_isSharedCheck_3064_ == 0)
{
lean_object* v_unused_3065_; 
v_unused_3065_ = lean_ctor_get(v___x_3056_, 0);
lean_dec(v_unused_3065_);
v___x_3058_ = v___x_3056_;
v_isShared_3059_ = v_isSharedCheck_3064_;
goto v_resetjp_3057_;
}
else
{
lean_dec(v___x_3056_);
v___x_3058_ = lean_box(0);
v_isShared_3059_ = v_isSharedCheck_3064_;
goto v_resetjp_3057_;
}
v_resetjp_3057_:
{
lean_object* v___x_3060_; lean_object* v___x_3062_; 
v___x_3060_ = lean_box(0);
if (v_isShared_3059_ == 0)
{
lean_ctor_set(v___x_3058_, 0, v___x_3060_);
v___x_3062_ = v___x_3058_;
goto v_reusejp_3061_;
}
else
{
lean_object* v_reuseFailAlloc_3063_; 
v_reuseFailAlloc_3063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3063_, 0, v___x_3060_);
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
lean_object* v_a_3066_; lean_object* v___x_3068_; uint8_t v_isShared_3069_; uint8_t v_isSharedCheck_3073_; 
v_a_3066_ = lean_ctor_get(v___x_3056_, 0);
v_isSharedCheck_3073_ = !lean_is_exclusive(v___x_3056_);
if (v_isSharedCheck_3073_ == 0)
{
v___x_3068_ = v___x_3056_;
v_isShared_3069_ = v_isSharedCheck_3073_;
goto v_resetjp_3067_;
}
else
{
lean_inc(v_a_3066_);
lean_dec(v___x_3056_);
v___x_3068_ = lean_box(0);
v_isShared_3069_ = v_isSharedCheck_3073_;
goto v_resetjp_3067_;
}
v_resetjp_3067_:
{
lean_object* v___x_3071_; 
if (v_isShared_3069_ == 0)
{
v___x_3071_ = v___x_3068_;
goto v_reusejp_3070_;
}
else
{
lean_object* v_reuseFailAlloc_3072_; 
v_reuseFailAlloc_3072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3072_, 0, v_a_3066_);
v___x_3071_ = v_reuseFailAlloc_3072_;
goto v_reusejp_3070_;
}
v_reusejp_3070_:
{
return v___x_3071_;
}
}
}
}
else
{
lean_object* v_a_3074_; lean_object* v___x_3076_; uint8_t v_isShared_3077_; uint8_t v_isSharedCheck_3081_; 
lean_dec(v_s_3015_);
lean_dec(v_gs_3014_);
lean_dec(v_cs_3013_);
v_a_3074_ = lean_ctor_get(v___x_3050_, 0);
v_isSharedCheck_3081_ = !lean_is_exclusive(v___x_3050_);
if (v_isSharedCheck_3081_ == 0)
{
v___x_3076_ = v___x_3050_;
v_isShared_3077_ = v_isSharedCheck_3081_;
goto v_resetjp_3075_;
}
else
{
lean_inc(v_a_3074_);
lean_dec(v___x_3050_);
v___x_3076_ = lean_box(0);
v_isShared_3077_ = v_isSharedCheck_3081_;
goto v_resetjp_3075_;
}
v_resetjp_3075_:
{
lean_object* v___x_3079_; 
if (v_isShared_3077_ == 0)
{
v___x_3079_ = v___x_3076_;
goto v_reusejp_3078_;
}
else
{
lean_object* v_reuseFailAlloc_3080_; 
v_reuseFailAlloc_3080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3080_, 0, v_a_3074_);
v___x_3079_ = v_reuseFailAlloc_3080_;
goto v_reusejp_3078_;
}
v_reusejp_3078_:
{
return v___x_3079_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive___boxed(lean_object* v_mvar_3082_, lean_object* v_cs_3083_, lean_object* v_gs_3084_, lean_object* v_s_3085_, lean_object* v_h_3086_, lean_object* v_a_3087_, lean_object* v_a_3088_, lean_object* v_a_3089_, lean_object* v_a_3090_, lean_object* v_a_3091_){
_start:
{
lean_object* v_res_3092_; 
v_res_3092_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive(v_mvar_3082_, v_cs_3083_, v_gs_3084_, v_s_3085_, v_h_3086_, v_a_3087_, v_a_3088_, v_a_3089_, v_a_3090_);
lean_dec(v_a_3090_);
lean_dec_ref(v_a_3089_);
lean_dec(v_a_3088_);
lean_dec_ref(v_a_3087_);
return v_res_3092_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__1___redArg(lean_object* v_type_3093_, lean_object* v_k_3094_, uint8_t v_cleanupAnnotations_3095_, uint8_t v_whnfType_3096_, lean_object* v___y_3097_, lean_object* v___y_3098_, lean_object* v___y_3099_, lean_object* v___y_3100_){
_start:
{
lean_object* v___f_3102_; lean_object* v___x_3103_; 
v___f_3102_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__4___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_3102_, 0, v_k_3094_);
v___x_3103_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_3093_, v___f_3102_, v_cleanupAnnotations_3095_, v_whnfType_3096_, v___y_3097_, v___y_3098_, v___y_3099_, v___y_3100_);
if (lean_obj_tag(v___x_3103_) == 0)
{
lean_object* v_a_3104_; lean_object* v___x_3106_; uint8_t v_isShared_3107_; uint8_t v_isSharedCheck_3111_; 
v_a_3104_ = lean_ctor_get(v___x_3103_, 0);
v_isSharedCheck_3111_ = !lean_is_exclusive(v___x_3103_);
if (v_isSharedCheck_3111_ == 0)
{
v___x_3106_ = v___x_3103_;
v_isShared_3107_ = v_isSharedCheck_3111_;
goto v_resetjp_3105_;
}
else
{
lean_inc(v_a_3104_);
lean_dec(v___x_3103_);
v___x_3106_ = lean_box(0);
v_isShared_3107_ = v_isSharedCheck_3111_;
goto v_resetjp_3105_;
}
v_resetjp_3105_:
{
lean_object* v___x_3109_; 
if (v_isShared_3107_ == 0)
{
v___x_3109_ = v___x_3106_;
goto v_reusejp_3108_;
}
else
{
lean_object* v_reuseFailAlloc_3110_; 
v_reuseFailAlloc_3110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3110_, 0, v_a_3104_);
v___x_3109_ = v_reuseFailAlloc_3110_;
goto v_reusejp_3108_;
}
v_reusejp_3108_:
{
return v___x_3109_;
}
}
}
else
{
lean_object* v_a_3112_; lean_object* v___x_3114_; uint8_t v_isShared_3115_; uint8_t v_isSharedCheck_3119_; 
v_a_3112_ = lean_ctor_get(v___x_3103_, 0);
v_isSharedCheck_3119_ = !lean_is_exclusive(v___x_3103_);
if (v_isSharedCheck_3119_ == 0)
{
v___x_3114_ = v___x_3103_;
v_isShared_3115_ = v_isSharedCheck_3119_;
goto v_resetjp_3113_;
}
else
{
lean_inc(v_a_3112_);
lean_dec(v___x_3103_);
v___x_3114_ = lean_box(0);
v_isShared_3115_ = v_isSharedCheck_3119_;
goto v_resetjp_3113_;
}
v_resetjp_3113_:
{
lean_object* v___x_3117_; 
if (v_isShared_3115_ == 0)
{
v___x_3117_ = v___x_3114_;
goto v_reusejp_3116_;
}
else
{
lean_object* v_reuseFailAlloc_3118_; 
v_reuseFailAlloc_3118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3118_, 0, v_a_3112_);
v___x_3117_ = v_reuseFailAlloc_3118_;
goto v_reusejp_3116_;
}
v_reusejp_3116_:
{
return v___x_3117_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__1___redArg___boxed(lean_object* v_type_3120_, lean_object* v_k_3121_, lean_object* v_cleanupAnnotations_3122_, lean_object* v_whnfType_3123_, lean_object* v___y_3124_, lean_object* v___y_3125_, lean_object* v___y_3126_, lean_object* v___y_3127_, lean_object* v___y_3128_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3129_; uint8_t v_whnfType_boxed_3130_; lean_object* v_res_3131_; 
v_cleanupAnnotations_boxed_3129_ = lean_unbox(v_cleanupAnnotations_3122_);
v_whnfType_boxed_3130_ = lean_unbox(v_whnfType_3123_);
v_res_3131_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__1___redArg(v_type_3120_, v_k_3121_, v_cleanupAnnotations_boxed_3129_, v_whnfType_boxed_3130_, v___y_3124_, v___y_3125_, v___y_3126_, v___y_3127_);
lean_dec(v___y_3127_);
lean_dec_ref(v___y_3126_);
lean_dec(v___y_3125_);
lean_dec_ref(v___y_3124_);
return v_res_3131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__1(lean_object* v_00_u03b1_3132_, lean_object* v_type_3133_, lean_object* v_k_3134_, uint8_t v_cleanupAnnotations_3135_, uint8_t v_whnfType_3136_, lean_object* v___y_3137_, lean_object* v___y_3138_, lean_object* v___y_3139_, lean_object* v___y_3140_){
_start:
{
lean_object* v___x_3142_; 
v___x_3142_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__1___redArg(v_type_3133_, v_k_3134_, v_cleanupAnnotations_3135_, v_whnfType_3136_, v___y_3137_, v___y_3138_, v___y_3139_, v___y_3140_);
return v___x_3142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__1___boxed(lean_object* v_00_u03b1_3143_, lean_object* v_type_3144_, lean_object* v_k_3145_, lean_object* v_cleanupAnnotations_3146_, lean_object* v_whnfType_3147_, lean_object* v___y_3148_, lean_object* v___y_3149_, lean_object* v___y_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3153_; uint8_t v_whnfType_boxed_3154_; lean_object* v_res_3155_; 
v_cleanupAnnotations_boxed_3153_ = lean_unbox(v_cleanupAnnotations_3146_);
v_whnfType_boxed_3154_ = lean_unbox(v_whnfType_3147_);
v_res_3155_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__1(v_00_u03b1_3143_, v_type_3144_, v_k_3145_, v_cleanupAnnotations_boxed_3153_, v_whnfType_boxed_3154_, v___y_3148_, v___y_3149_, v___y_3150_, v___y_3151_);
lean_dec(v___y_3151_);
lean_dec_ref(v___y_3150_);
lean_dec(v___y_3149_);
lean_dec_ref(v___y_3148_);
return v_res_3155_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__3___redArg(lean_object* v_e_3156_, lean_object* v___y_3157_){
_start:
{
uint8_t v___x_3159_; 
v___x_3159_ = l_Lean_Expr_hasMVar(v_e_3156_);
if (v___x_3159_ == 0)
{
lean_object* v___x_3160_; 
v___x_3160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3160_, 0, v_e_3156_);
return v___x_3160_;
}
else
{
lean_object* v___x_3161_; lean_object* v_mctx_3162_; lean_object* v___x_3163_; lean_object* v_fst_3164_; lean_object* v_snd_3165_; lean_object* v___x_3166_; lean_object* v_cache_3167_; lean_object* v_zetaDeltaFVarIds_3168_; lean_object* v_postponed_3169_; lean_object* v_diag_3170_; lean_object* v___x_3172_; uint8_t v_isShared_3173_; uint8_t v_isSharedCheck_3179_; 
v___x_3161_ = lean_st_ref_get(v___y_3157_);
v_mctx_3162_ = lean_ctor_get(v___x_3161_, 0);
lean_inc_ref(v_mctx_3162_);
lean_dec(v___x_3161_);
v___x_3163_ = l_Lean_instantiateMVarsCore(v_mctx_3162_, v_e_3156_);
v_fst_3164_ = lean_ctor_get(v___x_3163_, 0);
lean_inc(v_fst_3164_);
v_snd_3165_ = lean_ctor_get(v___x_3163_, 1);
lean_inc(v_snd_3165_);
lean_dec_ref(v___x_3163_);
v___x_3166_ = lean_st_ref_take(v___y_3157_);
v_cache_3167_ = lean_ctor_get(v___x_3166_, 1);
v_zetaDeltaFVarIds_3168_ = lean_ctor_get(v___x_3166_, 2);
v_postponed_3169_ = lean_ctor_get(v___x_3166_, 3);
v_diag_3170_ = lean_ctor_get(v___x_3166_, 4);
v_isSharedCheck_3179_ = !lean_is_exclusive(v___x_3166_);
if (v_isSharedCheck_3179_ == 0)
{
lean_object* v_unused_3180_; 
v_unused_3180_ = lean_ctor_get(v___x_3166_, 0);
lean_dec(v_unused_3180_);
v___x_3172_ = v___x_3166_;
v_isShared_3173_ = v_isSharedCheck_3179_;
goto v_resetjp_3171_;
}
else
{
lean_inc(v_diag_3170_);
lean_inc(v_postponed_3169_);
lean_inc(v_zetaDeltaFVarIds_3168_);
lean_inc(v_cache_3167_);
lean_dec(v___x_3166_);
v___x_3172_ = lean_box(0);
v_isShared_3173_ = v_isSharedCheck_3179_;
goto v_resetjp_3171_;
}
v_resetjp_3171_:
{
lean_object* v___x_3175_; 
if (v_isShared_3173_ == 0)
{
lean_ctor_set(v___x_3172_, 0, v_snd_3165_);
v___x_3175_ = v___x_3172_;
goto v_reusejp_3174_;
}
else
{
lean_object* v_reuseFailAlloc_3178_; 
v_reuseFailAlloc_3178_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3178_, 0, v_snd_3165_);
lean_ctor_set(v_reuseFailAlloc_3178_, 1, v_cache_3167_);
lean_ctor_set(v_reuseFailAlloc_3178_, 2, v_zetaDeltaFVarIds_3168_);
lean_ctor_set(v_reuseFailAlloc_3178_, 3, v_postponed_3169_);
lean_ctor_set(v_reuseFailAlloc_3178_, 4, v_diag_3170_);
v___x_3175_ = v_reuseFailAlloc_3178_;
goto v_reusejp_3174_;
}
v_reusejp_3174_:
{
lean_object* v___x_3176_; lean_object* v___x_3177_; 
v___x_3176_ = lean_st_ref_put(v___y_3157_, v___x_3175_);
v___x_3177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3177_, 0, v_fst_3164_);
return v___x_3177_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__3___redArg___boxed(lean_object* v_e_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_){
_start:
{
lean_object* v_res_3184_; 
v_res_3184_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__3___redArg(v_e_3181_, v___y_3182_);
lean_dec(v___y_3182_);
return v_res_3184_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__3(lean_object* v_e_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_, lean_object* v___y_3188_, lean_object* v___y_3189_){
_start:
{
lean_object* v___x_3191_; 
v___x_3191_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__3___redArg(v_e_3185_, v___y_3187_);
return v___x_3191_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__3___boxed(lean_object* v_e_3192_, lean_object* v___y_3193_, lean_object* v___y_3194_, lean_object* v___y_3195_, lean_object* v___y_3196_, lean_object* v___y_3197_){
_start:
{
lean_object* v_res_3198_; 
v_res_3198_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__3(v_e_3192_, v___y_3193_, v___y_3194_, v___y_3195_, v___y_3196_);
lean_dec(v___y_3196_);
lean_dec_ref(v___y_3195_);
lean_dec(v___y_3194_);
lean_dec_ref(v___y_3193_);
return v_res_3198_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__4___redArg(lean_object* v_thm_3199_, lean_object* v___y_3200_){
_start:
{
lean_object* v___x_3202_; lean_object* v_env_3203_; lean_object* v_toConstantVal_3204_; lean_object* v_value_3205_; lean_object* v_all_3206_; lean_object* v_type_3213_; uint8_t v___x_3214_; 
v___x_3202_ = lean_st_ref_get(v___y_3200_);
v_env_3203_ = lean_ctor_get(v___x_3202_, 0);
lean_inc_ref_n(v_env_3203_, 2);
lean_dec(v___x_3202_);
v_toConstantVal_3204_ = lean_ctor_get(v_thm_3199_, 0);
v_value_3205_ = lean_ctor_get(v_thm_3199_, 1);
v_all_3206_ = lean_ctor_get(v_thm_3199_, 2);
v_type_3213_ = lean_ctor_get(v_toConstantVal_3204_, 2);
v___x_3214_ = l_Lean_Environment_hasUnsafe(v_env_3203_, v_type_3213_);
if (v___x_3214_ == 0)
{
uint8_t v___x_3215_; 
v___x_3215_ = l_Lean_Environment_hasUnsafe(v_env_3203_, v_value_3205_);
if (v___x_3215_ == 0)
{
lean_object* v___x_3216_; lean_object* v___x_3217_; 
v___x_3216_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3216_, 0, v_thm_3199_);
v___x_3217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3217_, 0, v___x_3216_);
return v___x_3217_;
}
else
{
lean_inc(v_all_3206_);
lean_inc_ref(v_value_3205_);
lean_inc_ref(v_toConstantVal_3204_);
lean_dec_ref(v_thm_3199_);
goto v___jp_3207_;
}
}
else
{
lean_inc(v_all_3206_);
lean_inc_ref(v_value_3205_);
lean_inc_ref(v_toConstantVal_3204_);
lean_dec_ref(v_env_3203_);
lean_dec_ref(v_thm_3199_);
goto v___jp_3207_;
}
v___jp_3207_:
{
lean_object* v___x_3208_; uint8_t v___x_3209_; lean_object* v___x_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; 
v___x_3208_ = lean_box(0);
v___x_3209_ = 0;
v___x_3210_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3210_, 0, v_toConstantVal_3204_);
lean_ctor_set(v___x_3210_, 1, v_value_3205_);
lean_ctor_set(v___x_3210_, 2, v___x_3208_);
lean_ctor_set(v___x_3210_, 3, v_all_3206_);
lean_ctor_set_uint8(v___x_3210_, sizeof(void*)*4, v___x_3209_);
v___x_3211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3211_, 0, v___x_3210_);
v___x_3212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3212_, 0, v___x_3211_);
return v___x_3212_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__4___redArg___boxed(lean_object* v_thm_3218_, lean_object* v___y_3219_, lean_object* v___y_3220_){
_start:
{
lean_object* v_res_3221_; 
v_res_3221_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__4___redArg(v_thm_3218_, v___y_3219_);
lean_dec(v___y_3219_);
return v_res_3221_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__4(lean_object* v_thm_3222_, lean_object* v___y_3223_, lean_object* v___y_3224_, lean_object* v___y_3225_, lean_object* v___y_3226_){
_start:
{
lean_object* v___x_3228_; 
v___x_3228_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__4___redArg(v_thm_3222_, v___y_3226_);
return v___x_3228_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__4___boxed(lean_object* v_thm_3229_, lean_object* v___y_3230_, lean_object* v___y_3231_, lean_object* v___y_3232_, lean_object* v___y_3233_, lean_object* v___y_3234_){
_start:
{
lean_object* v_res_3235_; 
v_res_3235_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__4(v_thm_3229_, v___y_3230_, v___y_3231_, v___y_3232_, v___y_3233_);
lean_dec(v___y_3233_);
lean_dec_ref(v___y_3232_);
lean_dec(v___y_3231_);
lean_dec_ref(v___y_3230_);
return v_res_3235_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__5___redArg(lean_object* v_name_3236_, lean_object* v_levelParams_3237_, lean_object* v_type_3238_, lean_object* v_value_3239_, lean_object* v_hints_3240_, lean_object* v___y_3241_){
_start:
{
lean_object* v___x_3243_; uint8_t v___y_3245_; lean_object* v_env_3253_; uint8_t v___x_3254_; 
v___x_3243_ = lean_st_ref_get(v___y_3241_);
v_env_3253_ = lean_ctor_get(v___x_3243_, 0);
lean_inc_ref_n(v_env_3253_, 2);
lean_dec(v___x_3243_);
v___x_3254_ = l_Lean_Environment_hasUnsafe(v_env_3253_, v_type_3238_);
if (v___x_3254_ == 0)
{
uint8_t v___x_3255_; 
v___x_3255_ = l_Lean_Environment_hasUnsafe(v_env_3253_, v_value_3239_);
if (v___x_3255_ == 0)
{
uint8_t v___x_3256_; 
v___x_3256_ = 1;
v___y_3245_ = v___x_3256_;
goto v___jp_3244_;
}
else
{
goto v___jp_3251_;
}
}
else
{
lean_dec_ref(v_env_3253_);
goto v___jp_3251_;
}
v___jp_3244_:
{
lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; lean_object* v___x_3249_; lean_object* v___x_3250_; 
lean_inc(v_name_3236_);
v___x_3246_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3246_, 0, v_name_3236_);
lean_ctor_set(v___x_3246_, 1, v_levelParams_3237_);
lean_ctor_set(v___x_3246_, 2, v_type_3238_);
v___x_3247_ = lean_box(0);
v___x_3248_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3248_, 0, v_name_3236_);
lean_ctor_set(v___x_3248_, 1, v___x_3247_);
v___x_3249_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3249_, 0, v___x_3246_);
lean_ctor_set(v___x_3249_, 1, v_value_3239_);
lean_ctor_set(v___x_3249_, 2, v_hints_3240_);
lean_ctor_set(v___x_3249_, 3, v___x_3248_);
lean_ctor_set_uint8(v___x_3249_, sizeof(void*)*4, v___y_3245_);
v___x_3250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3250_, 0, v___x_3249_);
return v___x_3250_;
}
v___jp_3251_:
{
uint8_t v___x_3252_; 
v___x_3252_ = 0;
v___y_3245_ = v___x_3252_;
goto v___jp_3244_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__5___redArg___boxed(lean_object* v_name_3257_, lean_object* v_levelParams_3258_, lean_object* v_type_3259_, lean_object* v_value_3260_, lean_object* v_hints_3261_, lean_object* v___y_3262_, lean_object* v___y_3263_){
_start:
{
lean_object* v_res_3264_; 
v_res_3264_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__5___redArg(v_name_3257_, v_levelParams_3258_, v_type_3259_, v_value_3260_, v_hints_3261_, v___y_3262_);
lean_dec(v___y_3262_);
return v_res_3264_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__5(lean_object* v_name_3265_, lean_object* v_levelParams_3266_, lean_object* v_type_3267_, lean_object* v_value_3268_, lean_object* v_hints_3269_, lean_object* v___y_3270_, lean_object* v___y_3271_, lean_object* v___y_3272_, lean_object* v___y_3273_){
_start:
{
lean_object* v___x_3275_; 
v___x_3275_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__5___redArg(v_name_3265_, v_levelParams_3266_, v_type_3267_, v_value_3268_, v_hints_3269_, v___y_3273_);
return v___x_3275_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__5___boxed(lean_object* v_name_3276_, lean_object* v_levelParams_3277_, lean_object* v_type_3278_, lean_object* v_value_3279_, lean_object* v_hints_3280_, lean_object* v___y_3281_, lean_object* v___y_3282_, lean_object* v___y_3283_, lean_object* v___y_3284_, lean_object* v___y_3285_){
_start:
{
lean_object* v_res_3286_; 
v_res_3286_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__5(v_name_3276_, v_levelParams_3277_, v_type_3278_, v_value_3279_, v_hints_3280_, v___y_3281_, v___y_3282_, v___y_3283_, v___y_3284_);
lean_dec(v___y_3284_);
lean_dec_ref(v___y_3283_);
lean_dec(v___y_3282_);
lean_dec_ref(v___y_3281_);
return v_res_3286_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__0(lean_object* v_univs_3287_, lean_object* v___x_3288_, lean_object* v___x_3289_, lean_object* v_x_3290_, lean_object* v_x_3291_, lean_object* v___y_3292_, lean_object* v___y_3293_, lean_object* v___y_3294_, lean_object* v___y_3295_){
_start:
{
if (lean_obj_tag(v_x_3290_) == 0)
{
lean_object* v___x_3297_; lean_object* v___x_3298_; 
lean_dec(v___x_3289_);
lean_dec(v___x_3288_);
v___x_3297_ = l_List_reverse___redArg(v_x_3291_);
v___x_3298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3298_, 0, v___x_3297_);
return v___x_3298_;
}
else
{
lean_object* v_head_3299_; lean_object* v_tail_3300_; lean_object* v___x_3302_; uint8_t v_isShared_3303_; uint8_t v_isSharedCheck_3318_; 
v_head_3299_ = lean_ctor_get(v_x_3290_, 0);
v_tail_3300_ = lean_ctor_get(v_x_3290_, 1);
v_isSharedCheck_3318_ = !lean_is_exclusive(v_x_3290_);
if (v_isSharedCheck_3318_ == 0)
{
v___x_3302_ = v_x_3290_;
v_isShared_3303_ = v_isSharedCheck_3318_;
goto v_resetjp_3301_;
}
else
{
lean_inc(v_tail_3300_);
lean_inc(v_head_3299_);
lean_dec(v_x_3290_);
v___x_3302_ = lean_box(0);
v_isShared_3303_ = v_isSharedCheck_3318_;
goto v_resetjp_3301_;
}
v_resetjp_3301_:
{
lean_object* v___x_3304_; 
lean_inc(v___x_3289_);
lean_inc(v___x_3288_);
v___x_3304_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp(v_univs_3287_, v___x_3288_, v___x_3289_, v_head_3299_, v___y_3292_, v___y_3293_, v___y_3294_, v___y_3295_);
if (lean_obj_tag(v___x_3304_) == 0)
{
lean_object* v_a_3305_; lean_object* v___x_3307_; 
v_a_3305_ = lean_ctor_get(v___x_3304_, 0);
lean_inc(v_a_3305_);
lean_dec_ref_known(v___x_3304_, 1);
if (v_isShared_3303_ == 0)
{
lean_ctor_set(v___x_3302_, 1, v_x_3291_);
lean_ctor_set(v___x_3302_, 0, v_a_3305_);
v___x_3307_ = v___x_3302_;
goto v_reusejp_3306_;
}
else
{
lean_object* v_reuseFailAlloc_3309_; 
v_reuseFailAlloc_3309_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3309_, 0, v_a_3305_);
lean_ctor_set(v_reuseFailAlloc_3309_, 1, v_x_3291_);
v___x_3307_ = v_reuseFailAlloc_3309_;
goto v_reusejp_3306_;
}
v_reusejp_3306_:
{
v_x_3290_ = v_tail_3300_;
v_x_3291_ = v___x_3307_;
goto _start;
}
}
else
{
lean_object* v_a_3310_; lean_object* v___x_3312_; uint8_t v_isShared_3313_; uint8_t v_isSharedCheck_3317_; 
lean_del_object(v___x_3302_);
lean_dec(v_tail_3300_);
lean_dec(v_x_3291_);
lean_dec(v___x_3289_);
lean_dec(v___x_3288_);
v_a_3310_ = lean_ctor_get(v___x_3304_, 0);
v_isSharedCheck_3317_ = !lean_is_exclusive(v___x_3304_);
if (v_isSharedCheck_3317_ == 0)
{
v___x_3312_ = v___x_3304_;
v_isShared_3313_ = v_isSharedCheck_3317_;
goto v_resetjp_3311_;
}
else
{
lean_inc(v_a_3310_);
lean_dec(v___x_3304_);
v___x_3312_ = lean_box(0);
v_isShared_3313_ = v_isSharedCheck_3317_;
goto v_resetjp_3311_;
}
v_resetjp_3311_:
{
lean_object* v___x_3315_; 
if (v_isShared_3313_ == 0)
{
v___x_3315_ = v___x_3312_;
goto v_reusejp_3314_;
}
else
{
lean_object* v_reuseFailAlloc_3316_; 
v_reuseFailAlloc_3316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3316_, 0, v_a_3310_);
v___x_3315_ = v_reuseFailAlloc_3316_;
goto v_reusejp_3314_;
}
v_reusejp_3314_:
{
return v___x_3315_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__0___boxed(lean_object* v_univs_3319_, lean_object* v___x_3320_, lean_object* v___x_3321_, lean_object* v_x_3322_, lean_object* v_x_3323_, lean_object* v___y_3324_, lean_object* v___y_3325_, lean_object* v___y_3326_, lean_object* v___y_3327_, lean_object* v___y_3328_){
_start:
{
lean_object* v_res_3329_; 
v_res_3329_ = l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__0(v_univs_3319_, v___x_3320_, v___x_3321_, v_x_3322_, v_x_3323_, v___y_3324_, v___y_3325_, v___y_3326_, v___y_3327_);
lean_dec(v___y_3327_);
lean_dec_ref(v___y_3326_);
lean_dec(v___y_3325_);
lean_dec_ref(v___y_3324_);
lean_dec(v_univs_3319_);
return v_res_3329_;
}
}
static lean_object* _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___lam__0___closed__4(void){
_start:
{
lean_object* v___x_3336_; lean_object* v___x_3337_; 
v___x_3336_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___lam__0___closed__3));
v___x_3337_ = l_Lean_stringToMessageData(v___x_3336_);
return v___x_3337_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___lam__0(lean_object* v_name_3338_, lean_object* v_univs_3339_, lean_object* v_numParams_3340_, lean_object* v_ctors_3341_, lean_object* v___x_3342_, lean_object* v_fvars_3343_, lean_object* v_ty_3344_, lean_object* v___y_3345_, lean_object* v___y_3346_, lean_object* v___y_3347_, lean_object* v___y_3348_){
_start:
{
uint8_t v___x_3413_; 
v___x_3413_ = l_Lean_Expr_isProp(v_ty_3344_);
if (v___x_3413_ == 0)
{
lean_object* v___x_3414_; lean_object* v___x_3415_; lean_object* v_a_3416_; lean_object* v___x_3418_; uint8_t v_isShared_3419_; uint8_t v_isSharedCheck_3423_; 
lean_dec_ref(v_fvars_3343_);
lean_dec(v___x_3342_);
lean_dec(v_ctors_3341_);
lean_dec(v_numParams_3340_);
lean_dec(v_univs_3339_);
lean_dec(v_name_3338_);
v___x_3414_ = lean_obj_once(&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___lam__0___closed__4, &l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___lam__0___closed__4_once, _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___lam__0___closed__4);
v___x_3415_ = l_Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0___redArg(v___x_3414_, v___y_3345_, v___y_3346_, v___y_3347_, v___y_3348_);
v_a_3416_ = lean_ctor_get(v___x_3415_, 0);
v_isSharedCheck_3423_ = !lean_is_exclusive(v___x_3415_);
if (v_isSharedCheck_3423_ == 0)
{
v___x_3418_ = v___x_3415_;
v_isShared_3419_ = v_isSharedCheck_3423_;
goto v_resetjp_3417_;
}
else
{
lean_inc(v_a_3416_);
lean_dec(v___x_3415_);
v___x_3418_ = lean_box(0);
v_isShared_3419_ = v_isSharedCheck_3423_;
goto v_resetjp_3417_;
}
v_resetjp_3417_:
{
lean_object* v___x_3421_; 
if (v_isShared_3419_ == 0)
{
v___x_3421_ = v___x_3418_;
goto v_reusejp_3420_;
}
else
{
lean_object* v_reuseFailAlloc_3422_; 
v_reuseFailAlloc_3422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3422_, 0, v_a_3416_);
v___x_3421_ = v_reuseFailAlloc_3422_;
goto v_reusejp_3420_;
}
v_reusejp_3420_:
{
return v___x_3421_;
}
}
}
else
{
goto v___jp_3350_;
}
v___jp_3350_:
{
lean_object* v___x_3351_; lean_object* v_lhs_3352_; lean_object* v_fvars_x27_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; 
lean_inc(v_univs_3339_);
v___x_3351_ = l_Lean_mkConst(v_name_3338_, v_univs_3339_);
v_lhs_3352_ = l_Lean_mkAppN(v___x_3351_, v_fvars_3343_);
lean_inc_ref(v_fvars_3343_);
v_fvars_x27_3353_ = lean_array_to_list(v_fvars_3343_);
v___x_3354_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___lam__0___closed__0));
lean_inc(v_numParams_3340_);
lean_inc(v_fvars_x27_3353_);
v___x_3355_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), v_fvars_x27_3353_, v_fvars_x27_3353_, v_numParams_3340_, v___x_3354_);
v___x_3356_ = l_List_drop___redArg(v_numParams_3340_, v_fvars_x27_3353_);
lean_dec(v_fvars_x27_3353_);
v___x_3357_ = lean_box(0);
v___x_3358_ = l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__0(v_univs_3339_, v___x_3355_, v___x_3356_, v_ctors_3341_, v___x_3357_, v___y_3345_, v___y_3346_, v___y_3347_, v___y_3348_);
lean_dec(v_univs_3339_);
if (lean_obj_tag(v___x_3358_) == 0)
{
lean_object* v_a_3359_; lean_object* v___x_3360_; lean_object* v_fst_3361_; lean_object* v_snd_3362_; lean_object* v___x_3364_; uint8_t v_isShared_3365_; uint8_t v_isSharedCheck_3404_; 
v_a_3359_ = lean_ctor_get(v___x_3358_, 0);
lean_inc(v_a_3359_);
lean_dec_ref_known(v___x_3358_, 1);
v___x_3360_ = l_List_unzipTR___redArg(v_a_3359_);
v_fst_3361_ = lean_ctor_get(v___x_3360_, 0);
v_snd_3362_ = lean_ctor_get(v___x_3360_, 1);
v_isSharedCheck_3404_ = !lean_is_exclusive(v___x_3360_);
if (v_isSharedCheck_3404_ == 0)
{
v___x_3364_ = v___x_3360_;
v_isShared_3365_ = v_isSharedCheck_3404_;
goto v_resetjp_3363_;
}
else
{
lean_inc(v_snd_3362_);
lean_inc(v_fst_3361_);
lean_dec(v___x_3360_);
v___x_3364_ = lean_box(0);
v_isShared_3365_ = v_isSharedCheck_3404_;
goto v_resetjp_3363_;
}
v_resetjp_3363_:
{
lean_object* v___x_3366_; uint8_t v___x_3367_; uint8_t v___x_3368_; uint8_t v___x_3369_; lean_object* v___x_3370_; 
v___x_3366_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkOrList(v_snd_3362_);
v___x_3367_ = 0;
v___x_3368_ = 1;
v___x_3369_ = 1;
lean_inc_ref(v___x_3366_);
v___x_3370_ = l_Lean_Meta_mkLambdaFVars(v_fvars_3343_, v___x_3366_, v___x_3367_, v___x_3368_, v___x_3367_, v___x_3368_, v___x_3369_, v___y_3345_, v___y_3346_, v___y_3347_, v___y_3348_);
if (lean_obj_tag(v___x_3370_) == 0)
{
lean_object* v_a_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; 
v_a_3371_ = lean_ctor_get(v___x_3370_, 0);
lean_inc(v_a_3371_);
lean_dec_ref_known(v___x_3370_, 1);
v___x_3372_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___lam__0___closed__2));
v___x_3373_ = l_Lean_mkConst(v___x_3372_, v___x_3342_);
v___x_3374_ = l_Lean_mkAppB(v___x_3373_, v_lhs_3352_, v___x_3366_);
v___x_3375_ = l_Lean_Meta_mkForallFVars(v_fvars_3343_, v___x_3374_, v___x_3367_, v___x_3368_, v___x_3368_, v___x_3369_, v___y_3345_, v___y_3346_, v___y_3347_, v___y_3348_);
lean_dec_ref(v_fvars_3343_);
if (lean_obj_tag(v___x_3375_) == 0)
{
lean_object* v_a_3376_; lean_object* v___x_3378_; uint8_t v_isShared_3379_; uint8_t v_isSharedCheck_3387_; 
v_a_3376_ = lean_ctor_get(v___x_3375_, 0);
v_isSharedCheck_3387_ = !lean_is_exclusive(v___x_3375_);
if (v_isSharedCheck_3387_ == 0)
{
v___x_3378_ = v___x_3375_;
v_isShared_3379_ = v_isSharedCheck_3387_;
goto v_resetjp_3377_;
}
else
{
lean_inc(v_a_3376_);
lean_dec(v___x_3375_);
v___x_3378_ = lean_box(0);
v_isShared_3379_ = v_isSharedCheck_3387_;
goto v_resetjp_3377_;
}
v_resetjp_3377_:
{
lean_object* v___x_3381_; 
if (v_isShared_3365_ == 0)
{
lean_ctor_set(v___x_3364_, 1, v_a_3371_);
v___x_3381_ = v___x_3364_;
goto v_reusejp_3380_;
}
else
{
lean_object* v_reuseFailAlloc_3386_; 
v_reuseFailAlloc_3386_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3386_, 0, v_fst_3361_);
lean_ctor_set(v_reuseFailAlloc_3386_, 1, v_a_3371_);
v___x_3381_ = v_reuseFailAlloc_3386_;
goto v_reusejp_3380_;
}
v_reusejp_3380_:
{
lean_object* v___x_3382_; lean_object* v___x_3384_; 
v___x_3382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3382_, 0, v_a_3376_);
lean_ctor_set(v___x_3382_, 1, v___x_3381_);
if (v_isShared_3379_ == 0)
{
lean_ctor_set(v___x_3378_, 0, v___x_3382_);
v___x_3384_ = v___x_3378_;
goto v_reusejp_3383_;
}
else
{
lean_object* v_reuseFailAlloc_3385_; 
v_reuseFailAlloc_3385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3385_, 0, v___x_3382_);
v___x_3384_ = v_reuseFailAlloc_3385_;
goto v_reusejp_3383_;
}
v_reusejp_3383_:
{
return v___x_3384_;
}
}
}
}
else
{
lean_object* v_a_3388_; lean_object* v___x_3390_; uint8_t v_isShared_3391_; uint8_t v_isSharedCheck_3395_; 
lean_dec(v_a_3371_);
lean_del_object(v___x_3364_);
lean_dec(v_fst_3361_);
v_a_3388_ = lean_ctor_get(v___x_3375_, 0);
v_isSharedCheck_3395_ = !lean_is_exclusive(v___x_3375_);
if (v_isSharedCheck_3395_ == 0)
{
v___x_3390_ = v___x_3375_;
v_isShared_3391_ = v_isSharedCheck_3395_;
goto v_resetjp_3389_;
}
else
{
lean_inc(v_a_3388_);
lean_dec(v___x_3375_);
v___x_3390_ = lean_box(0);
v_isShared_3391_ = v_isSharedCheck_3395_;
goto v_resetjp_3389_;
}
v_resetjp_3389_:
{
lean_object* v___x_3393_; 
if (v_isShared_3391_ == 0)
{
v___x_3393_ = v___x_3390_;
goto v_reusejp_3392_;
}
else
{
lean_object* v_reuseFailAlloc_3394_; 
v_reuseFailAlloc_3394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3394_, 0, v_a_3388_);
v___x_3393_ = v_reuseFailAlloc_3394_;
goto v_reusejp_3392_;
}
v_reusejp_3392_:
{
return v___x_3393_;
}
}
}
}
else
{
lean_object* v_a_3396_; lean_object* v___x_3398_; uint8_t v_isShared_3399_; uint8_t v_isSharedCheck_3403_; 
lean_dec_ref(v___x_3366_);
lean_del_object(v___x_3364_);
lean_dec(v_fst_3361_);
lean_dec_ref(v_lhs_3352_);
lean_dec_ref(v_fvars_3343_);
lean_dec(v___x_3342_);
v_a_3396_ = lean_ctor_get(v___x_3370_, 0);
v_isSharedCheck_3403_ = !lean_is_exclusive(v___x_3370_);
if (v_isSharedCheck_3403_ == 0)
{
v___x_3398_ = v___x_3370_;
v_isShared_3399_ = v_isSharedCheck_3403_;
goto v_resetjp_3397_;
}
else
{
lean_inc(v_a_3396_);
lean_dec(v___x_3370_);
v___x_3398_ = lean_box(0);
v_isShared_3399_ = v_isSharedCheck_3403_;
goto v_resetjp_3397_;
}
v_resetjp_3397_:
{
lean_object* v___x_3401_; 
if (v_isShared_3399_ == 0)
{
v___x_3401_ = v___x_3398_;
goto v_reusejp_3400_;
}
else
{
lean_object* v_reuseFailAlloc_3402_; 
v_reuseFailAlloc_3402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3402_, 0, v_a_3396_);
v___x_3401_ = v_reuseFailAlloc_3402_;
goto v_reusejp_3400_;
}
v_reusejp_3400_:
{
return v___x_3401_;
}
}
}
}
}
else
{
lean_object* v_a_3405_; lean_object* v___x_3407_; uint8_t v_isShared_3408_; uint8_t v_isSharedCheck_3412_; 
lean_dec_ref(v_lhs_3352_);
lean_dec_ref(v_fvars_3343_);
lean_dec(v___x_3342_);
v_a_3405_ = lean_ctor_get(v___x_3358_, 0);
v_isSharedCheck_3412_ = !lean_is_exclusive(v___x_3358_);
if (v_isSharedCheck_3412_ == 0)
{
v___x_3407_ = v___x_3358_;
v_isShared_3408_ = v_isSharedCheck_3412_;
goto v_resetjp_3406_;
}
else
{
lean_inc(v_a_3405_);
lean_dec(v___x_3358_);
v___x_3407_ = lean_box(0);
v_isShared_3408_ = v_isSharedCheck_3412_;
goto v_resetjp_3406_;
}
v_resetjp_3406_:
{
lean_object* v___x_3410_; 
if (v_isShared_3408_ == 0)
{
v___x_3410_ = v___x_3407_;
goto v_reusejp_3409_;
}
else
{
lean_object* v_reuseFailAlloc_3411_; 
v_reuseFailAlloc_3411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3411_, 0, v_a_3405_);
v___x_3410_ = v_reuseFailAlloc_3411_;
goto v_reusejp_3409_;
}
v_reusejp_3409_:
{
return v___x_3410_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___lam__0___boxed(lean_object* v_name_3424_, lean_object* v_univs_3425_, lean_object* v_numParams_3426_, lean_object* v_ctors_3427_, lean_object* v___x_3428_, lean_object* v_fvars_3429_, lean_object* v_ty_3430_, lean_object* v___y_3431_, lean_object* v___y_3432_, lean_object* v___y_3433_, lean_object* v___y_3434_, lean_object* v___y_3435_){
_start:
{
lean_object* v_res_3436_; 
v_res_3436_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___lam__0(v_name_3424_, v_univs_3425_, v_numParams_3426_, v_ctors_3427_, v___x_3428_, v_fvars_3429_, v_ty_3430_, v___y_3431_, v___y_3432_, v___y_3433_, v___y_3434_);
lean_dec(v___y_3434_);
lean_dec_ref(v___y_3433_);
lean_dec(v___y_3432_);
lean_dec_ref(v___y_3431_);
lean_dec_ref(v_ty_3430_);
return v_res_3436_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__2(lean_object* v_a_3437_, lean_object* v_a_3438_){
_start:
{
if (lean_obj_tag(v_a_3437_) == 0)
{
lean_object* v___x_3439_; 
v___x_3439_ = l_List_reverse___redArg(v_a_3438_);
return v___x_3439_;
}
else
{
lean_object* v_head_3440_; lean_object* v_tail_3441_; lean_object* v___x_3443_; uint8_t v_isShared_3444_; uint8_t v_isSharedCheck_3450_; 
v_head_3440_ = lean_ctor_get(v_a_3437_, 0);
v_tail_3441_ = lean_ctor_get(v_a_3437_, 1);
v_isSharedCheck_3450_ = !lean_is_exclusive(v_a_3437_);
if (v_isSharedCheck_3450_ == 0)
{
v___x_3443_ = v_a_3437_;
v_isShared_3444_ = v_isSharedCheck_3450_;
goto v_resetjp_3442_;
}
else
{
lean_inc(v_tail_3441_);
lean_inc(v_head_3440_);
lean_dec(v_a_3437_);
v___x_3443_ = lean_box(0);
v_isShared_3444_ = v_isSharedCheck_3450_;
goto v_resetjp_3442_;
}
v_resetjp_3442_:
{
lean_object* v___x_3445_; lean_object* v___x_3447_; 
v___x_3445_ = l_Lean_Expr_fvar___override(v_head_3440_);
if (v_isShared_3444_ == 0)
{
lean_ctor_set(v___x_3443_, 1, v_a_3438_);
lean_ctor_set(v___x_3443_, 0, v___x_3445_);
v___x_3447_ = v___x_3443_;
goto v_reusejp_3446_;
}
else
{
lean_object* v_reuseFailAlloc_3449_; 
v_reuseFailAlloc_3449_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3449_, 0, v___x_3445_);
lean_ctor_set(v_reuseFailAlloc_3449_, 1, v_a_3438_);
v___x_3447_ = v_reuseFailAlloc_3449_;
goto v_reusejp_3446_;
}
v_reusejp_3446_:
{
v_a_3437_ = v_tail_3441_;
v_a_3438_ = v___x_3447_;
goto _start;
}
}
}
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__6___closed__0(void){
_start:
{
lean_object* v___x_3451_; double v___x_3452_; 
v___x_3451_ = lean_unsigned_to_nat(0u);
v___x_3452_ = lean_float_of_nat(v___x_3451_);
return v___x_3452_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__6(lean_object* v_cls_3456_, lean_object* v_msg_3457_, lean_object* v___y_3458_, lean_object* v___y_3459_, lean_object* v___y_3460_, lean_object* v___y_3461_){
_start:
{
lean_object* v_ref_3463_; lean_object* v___x_3464_; lean_object* v_a_3465_; lean_object* v___x_3467_; uint8_t v_isShared_3468_; uint8_t v_isSharedCheck_3510_; 
v_ref_3463_ = lean_ctor_get(v___y_3460_, 2);
v___x_3464_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0_spec__0(v_msg_3457_, v___y_3458_, v___y_3459_, v___y_3460_, v___y_3461_);
v_a_3465_ = lean_ctor_get(v___x_3464_, 0);
v_isSharedCheck_3510_ = !lean_is_exclusive(v___x_3464_);
if (v_isSharedCheck_3510_ == 0)
{
v___x_3467_ = v___x_3464_;
v_isShared_3468_ = v_isSharedCheck_3510_;
goto v_resetjp_3466_;
}
else
{
lean_inc(v_a_3465_);
lean_dec(v___x_3464_);
v___x_3467_ = lean_box(0);
v_isShared_3468_ = v_isSharedCheck_3510_;
goto v_resetjp_3466_;
}
v_resetjp_3466_:
{
lean_object* v___x_3469_; lean_object* v_traceState_3470_; lean_object* v_env_3471_; lean_object* v_nextMacroScope_3472_; lean_object* v_ngen_3473_; lean_object* v_auxDeclNGen_3474_; lean_object* v_cache_3475_; lean_object* v_recordedDeps_3476_; lean_object* v_messages_3477_; lean_object* v_infoState_3478_; lean_object* v_snapshotTasks_3479_; lean_object* v___x_3481_; uint8_t v_isShared_3482_; uint8_t v_isSharedCheck_3509_; 
v___x_3469_ = lean_st_ref_take(v___y_3461_);
v_traceState_3470_ = lean_ctor_get(v___x_3469_, 4);
v_env_3471_ = lean_ctor_get(v___x_3469_, 0);
v_nextMacroScope_3472_ = lean_ctor_get(v___x_3469_, 1);
v_ngen_3473_ = lean_ctor_get(v___x_3469_, 2);
v_auxDeclNGen_3474_ = lean_ctor_get(v___x_3469_, 3);
v_cache_3475_ = lean_ctor_get(v___x_3469_, 5);
v_recordedDeps_3476_ = lean_ctor_get(v___x_3469_, 6);
v_messages_3477_ = lean_ctor_get(v___x_3469_, 7);
v_infoState_3478_ = lean_ctor_get(v___x_3469_, 8);
v_snapshotTasks_3479_ = lean_ctor_get(v___x_3469_, 9);
v_isSharedCheck_3509_ = !lean_is_exclusive(v___x_3469_);
if (v_isSharedCheck_3509_ == 0)
{
v___x_3481_ = v___x_3469_;
v_isShared_3482_ = v_isSharedCheck_3509_;
goto v_resetjp_3480_;
}
else
{
lean_inc(v_snapshotTasks_3479_);
lean_inc(v_infoState_3478_);
lean_inc(v_messages_3477_);
lean_inc(v_recordedDeps_3476_);
lean_inc(v_cache_3475_);
lean_inc(v_traceState_3470_);
lean_inc(v_auxDeclNGen_3474_);
lean_inc(v_ngen_3473_);
lean_inc(v_nextMacroScope_3472_);
lean_inc(v_env_3471_);
lean_dec(v___x_3469_);
v___x_3481_ = lean_box(0);
v_isShared_3482_ = v_isSharedCheck_3509_;
goto v_resetjp_3480_;
}
v_resetjp_3480_:
{
uint64_t v_tid_3483_; lean_object* v_traces_3484_; lean_object* v___x_3486_; uint8_t v_isShared_3487_; uint8_t v_isSharedCheck_3508_; 
v_tid_3483_ = lean_ctor_get_uint64(v_traceState_3470_, sizeof(void*)*1);
v_traces_3484_ = lean_ctor_get(v_traceState_3470_, 0);
v_isSharedCheck_3508_ = !lean_is_exclusive(v_traceState_3470_);
if (v_isSharedCheck_3508_ == 0)
{
v___x_3486_ = v_traceState_3470_;
v_isShared_3487_ = v_isSharedCheck_3508_;
goto v_resetjp_3485_;
}
else
{
lean_inc(v_traces_3484_);
lean_dec(v_traceState_3470_);
v___x_3486_ = lean_box(0);
v_isShared_3487_ = v_isSharedCheck_3508_;
goto v_resetjp_3485_;
}
v_resetjp_3485_:
{
lean_object* v___x_3488_; lean_object* v___x_3489_; double v___x_3490_; uint8_t v___x_3491_; lean_object* v___x_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; lean_object* v___x_3497_; lean_object* v___x_3499_; 
v___x_3488_ = lean_box(0);
v___x_3489_ = lean_box(0);
v___x_3490_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__6___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__6___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__6___closed__0);
v___x_3491_ = 0;
v___x_3492_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__6___closed__1));
v___x_3493_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3493_, 0, v_cls_3456_);
lean_ctor_set(v___x_3493_, 1, v___x_3489_);
lean_ctor_set(v___x_3493_, 2, v___x_3492_);
lean_ctor_set_float(v___x_3493_, sizeof(void*)*3, v___x_3490_);
lean_ctor_set_float(v___x_3493_, sizeof(void*)*3 + 8, v___x_3490_);
lean_ctor_set_uint8(v___x_3493_, sizeof(void*)*3 + 16, v___x_3491_);
v___x_3494_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__6___closed__2));
v___x_3495_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3495_, 0, v___x_3493_);
lean_ctor_set(v___x_3495_, 1, v_a_3465_);
lean_ctor_set(v___x_3495_, 2, v___x_3494_);
lean_inc(v_ref_3463_);
v___x_3496_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3496_, 0, v_ref_3463_);
lean_ctor_set(v___x_3496_, 1, v___x_3495_);
v___x_3497_ = l_Lean_PersistentArray_push___redArg(v_traces_3484_, v___x_3496_);
if (v_isShared_3487_ == 0)
{
lean_ctor_set(v___x_3486_, 0, v___x_3497_);
v___x_3499_ = v___x_3486_;
goto v_reusejp_3498_;
}
else
{
lean_object* v_reuseFailAlloc_3507_; 
v_reuseFailAlloc_3507_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3507_, 0, v___x_3497_);
lean_ctor_set_uint64(v_reuseFailAlloc_3507_, sizeof(void*)*1, v_tid_3483_);
v___x_3499_ = v_reuseFailAlloc_3507_;
goto v_reusejp_3498_;
}
v_reusejp_3498_:
{
lean_object* v___x_3501_; 
if (v_isShared_3482_ == 0)
{
lean_ctor_set(v___x_3481_, 4, v___x_3499_);
v___x_3501_ = v___x_3481_;
goto v_reusejp_3500_;
}
else
{
lean_object* v_reuseFailAlloc_3506_; 
v_reuseFailAlloc_3506_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3506_, 0, v_env_3471_);
lean_ctor_set(v_reuseFailAlloc_3506_, 1, v_nextMacroScope_3472_);
lean_ctor_set(v_reuseFailAlloc_3506_, 2, v_ngen_3473_);
lean_ctor_set(v_reuseFailAlloc_3506_, 3, v_auxDeclNGen_3474_);
lean_ctor_set(v_reuseFailAlloc_3506_, 4, v___x_3499_);
lean_ctor_set(v_reuseFailAlloc_3506_, 5, v_cache_3475_);
lean_ctor_set(v_reuseFailAlloc_3506_, 6, v_recordedDeps_3476_);
lean_ctor_set(v_reuseFailAlloc_3506_, 7, v_messages_3477_);
lean_ctor_set(v_reuseFailAlloc_3506_, 8, v_infoState_3478_);
lean_ctor_set(v_reuseFailAlloc_3506_, 9, v_snapshotTasks_3479_);
v___x_3501_ = v_reuseFailAlloc_3506_;
goto v_reusejp_3500_;
}
v_reusejp_3500_:
{
lean_object* v___x_3502_; lean_object* v___x_3504_; 
v___x_3502_ = lean_st_ref_put(v___y_3461_, v___x_3501_);
if (v_isShared_3468_ == 0)
{
lean_ctor_set(v___x_3467_, 0, v___x_3488_);
v___x_3504_ = v___x_3467_;
goto v_reusejp_3503_;
}
else
{
lean_object* v_reuseFailAlloc_3505_; 
v_reuseFailAlloc_3505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3505_, 0, v___x_3488_);
v___x_3504_ = v_reuseFailAlloc_3505_;
goto v_reusejp_3503_;
}
v_reusejp_3503_:
{
return v___x_3504_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__6___boxed(lean_object* v_cls_3511_, lean_object* v_msg_3512_, lean_object* v___y_3513_, lean_object* v___y_3514_, lean_object* v___y_3515_, lean_object* v___y_3516_, lean_object* v___y_3517_){
_start:
{
lean_object* v_res_3518_; 
v_res_3518_ = l_Lean_addTrace___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__6(v_cls_3511_, v_msg_3512_, v___y_3513_, v___y_3514_, v___y_3515_, v___y_3516_);
lean_dec(v___y_3516_);
lean_dec_ref(v___y_3515_);
lean_dec(v___y_3514_);
lean_dec_ref(v___y_3513_);
return v_res_3518_;
}
}
static lean_object* _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__1(void){
_start:
{
lean_object* v___x_3520_; lean_object* v___x_3521_; 
v___x_3520_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__0));
v___x_3521_ = l_Lean_stringToMessageData(v___x_3520_);
return v___x_3521_;
}
}
static lean_object* _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__4(void){
_start:
{
lean_object* v___x_3526_; lean_object* v___x_3527_; lean_object* v___x_3528_; 
v___x_3526_ = lean_box(0);
v___x_3527_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__3));
v___x_3528_ = l_Lean_mkConst(v___x_3527_, v___x_3526_);
return v___x_3528_;
}
}
static lean_object* _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__13(void){
_start:
{
lean_object* v___x_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; 
v___x_3544_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__10));
v___x_3545_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__12));
v___x_3546_ = l_Lean_Name_append(v___x_3545_, v___x_3544_);
return v___x_3546_;
}
}
static lean_object* _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__15(void){
_start:
{
lean_object* v___x_3548_; lean_object* v___x_3549_; 
v___x_3548_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__14));
v___x_3549_ = l_Lean_stringToMessageData(v___x_3548_);
return v___x_3549_;
}
}
static lean_object* _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__17(void){
_start:
{
lean_object* v___x_3551_; lean_object* v___x_3552_; 
v___x_3551_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__16));
v___x_3552_ = l_Lean_stringToMessageData(v___x_3551_);
return v___x_3552_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl(lean_object* v_inductVal_3553_, lean_object* v_rel_3554_, lean_object* v_a_3555_, lean_object* v_a_3556_, lean_object* v_a_3557_, lean_object* v_a_3558_){
_start:
{
lean_object* v___y_3561_; lean_object* v___y_3562_; lean_object* v___y_3563_; lean_object* v___y_3564_; lean_object* v_toConstantVal_3567_; lean_object* v_numParams_3568_; lean_object* v_ctors_3569_; lean_object* v_name_3570_; lean_object* v_levelParams_3571_; lean_object* v_type_3572_; lean_object* v___x_3574_; uint8_t v_isShared_3575_; uint8_t v_isSharedCheck_3736_; 
v_toConstantVal_3567_ = lean_ctor_get(v_inductVal_3553_, 0);
lean_inc_ref(v_toConstantVal_3567_);
v_numParams_3568_ = lean_ctor_get(v_inductVal_3553_, 1);
lean_inc(v_numParams_3568_);
v_ctors_3569_ = lean_ctor_get(v_inductVal_3553_, 4);
lean_inc(v_ctors_3569_);
lean_dec_ref(v_inductVal_3553_);
v_name_3570_ = lean_ctor_get(v_toConstantVal_3567_, 0);
v_levelParams_3571_ = lean_ctor_get(v_toConstantVal_3567_, 1);
v_type_3572_ = lean_ctor_get(v_toConstantVal_3567_, 2);
v_isSharedCheck_3736_ = !lean_is_exclusive(v_toConstantVal_3567_);
if (v_isSharedCheck_3736_ == 0)
{
v___x_3574_ = v_toConstantVal_3567_;
v_isShared_3575_ = v_isSharedCheck_3736_;
goto v_resetjp_3573_;
}
else
{
lean_inc(v_type_3572_);
lean_inc(v_levelParams_3571_);
lean_inc(v_name_3570_);
lean_dec(v_toConstantVal_3567_);
v___x_3574_ = lean_box(0);
v_isShared_3575_ = v_isSharedCheck_3736_;
goto v_resetjp_3573_;
}
v___jp_3560_:
{
lean_object* v___x_3565_; lean_object* v___x_3566_; 
v___x_3565_ = lean_obj_once(&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__1, &l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__1_once, _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__1);
v___x_3566_ = l_Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0___redArg(v___x_3565_, v___y_3561_, v___y_3562_, v___y_3563_, v___y_3564_);
return v___x_3566_;
}
v_resetjp_3573_:
{
lean_object* v___x_3576_; lean_object* v_univs_3577_; lean_object* v___f_3578_; uint8_t v___x_3579_; lean_object* v___x_3580_; 
v___x_3576_ = lean_box(0);
lean_inc(v_levelParams_3571_);
v_univs_3577_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__2_spec__3(v_levelParams_3571_, v___x_3576_);
lean_inc(v_ctors_3569_);
lean_inc(v_numParams_3568_);
lean_inc(v_name_3570_);
v___f_3578_ = lean_alloc_closure((void*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___lam__0___boxed), 12, 5);
lean_closure_set(v___f_3578_, 0, v_name_3570_);
lean_closure_set(v___f_3578_, 1, v_univs_3577_);
lean_closure_set(v___f_3578_, 2, v_numParams_3568_);
lean_closure_set(v___f_3578_, 3, v_ctors_3569_);
lean_closure_set(v___f_3578_, 4, v___x_3576_);
v___x_3579_ = 0;
v___x_3580_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__1___redArg(v_type_3572_, v___f_3578_, v___x_3579_, v___x_3579_, v_a_3555_, v_a_3556_, v_a_3557_, v_a_3558_);
if (lean_obj_tag(v___x_3580_) == 0)
{
lean_object* v_a_3581_; lean_object* v_snd_3582_; lean_object* v_fst_3583_; lean_object* v___x_3585_; uint8_t v_isShared_3586_; uint8_t v_isSharedCheck_3727_; 
v_a_3581_ = lean_ctor_get(v___x_3580_, 0);
lean_inc(v_a_3581_);
lean_dec_ref_known(v___x_3580_, 1);
v_snd_3582_ = lean_ctor_get(v_a_3581_, 1);
v_fst_3583_ = lean_ctor_get(v_a_3581_, 0);
v_isSharedCheck_3727_ = !lean_is_exclusive(v_a_3581_);
if (v_isSharedCheck_3727_ == 0)
{
v___x_3585_ = v_a_3581_;
v_isShared_3586_ = v_isSharedCheck_3727_;
goto v_resetjp_3584_;
}
else
{
lean_inc(v_snd_3582_);
lean_inc(v_fst_3583_);
lean_dec(v_a_3581_);
v___x_3585_ = lean_box(0);
v_isShared_3586_ = v_isSharedCheck_3727_;
goto v_resetjp_3584_;
}
v_resetjp_3584_:
{
lean_object* v_fst_3587_; lean_object* v_snd_3588_; lean_object* v___x_3590_; uint8_t v_isShared_3591_; uint8_t v_isSharedCheck_3726_; 
v_fst_3587_ = lean_ctor_get(v_snd_3582_, 0);
v_snd_3588_ = lean_ctor_get(v_snd_3582_, 1);
v_isSharedCheck_3726_ = !lean_is_exclusive(v_snd_3582_);
if (v_isSharedCheck_3726_ == 0)
{
v___x_3590_ = v_snd_3582_;
v_isShared_3591_ = v_isSharedCheck_3726_;
goto v_resetjp_3589_;
}
else
{
lean_inc(v_snd_3588_);
lean_inc(v_fst_3587_);
lean_dec(v_snd_3582_);
v___x_3590_ = lean_box(0);
v_isShared_3591_ = v_isSharedCheck_3726_;
goto v_resetjp_3589_;
}
v_resetjp_3589_:
{
lean_object* v___y_3593_; lean_object* v___y_3594_; lean_object* v___y_3595_; lean_object* v___y_3596_; lean_object* v_toCold_3698_; lean_object* v_options_3699_; uint8_t v_hasTrace_3700_; 
v_toCold_3698_ = lean_ctor_get(v_a_3557_, 0);
v_options_3699_ = lean_ctor_get(v_toCold_3698_, 2);
v_hasTrace_3700_ = lean_ctor_get_uint8(v_options_3699_, sizeof(void*)*1);
if (v_hasTrace_3700_ == 0)
{
lean_del_object(v___x_3590_);
lean_del_object(v___x_3585_);
v___y_3593_ = v_a_3555_;
v___y_3594_ = v_a_3556_;
v___y_3595_ = v_a_3557_;
v___y_3596_ = v_a_3558_;
goto v___jp_3592_;
}
else
{
lean_object* v_inheritedTraceOptions_3701_; lean_object* v___x_3702_; lean_object* v___y_3704_; lean_object* v___y_3705_; lean_object* v___y_3706_; lean_object* v_options_3707_; lean_object* v_inheritedTraceOptions_3708_; lean_object* v___y_3709_; lean_object* v___x_3718_; uint8_t v___x_3719_; 
v_inheritedTraceOptions_3701_ = lean_ctor_get(v_toCold_3698_, 11);
v___x_3702_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__10));
v___x_3718_ = lean_obj_once(&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__13, &l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__13_once, _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__13);
v___x_3719_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3701_, v_options_3699_, v___x_3718_);
if (v___x_3719_ == 0)
{
lean_del_object(v___x_3585_);
v___y_3704_ = v_a_3555_;
v___y_3705_ = v_a_3556_;
v___y_3706_ = v_a_3557_;
v_options_3707_ = v_options_3699_;
v_inheritedTraceOptions_3708_ = v_inheritedTraceOptions_3701_;
v___y_3709_ = v_a_3558_;
goto v___jp_3703_;
}
else
{
lean_object* v___x_3720_; lean_object* v___x_3721_; lean_object* v___x_3723_; 
v___x_3720_ = lean_obj_once(&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__17, &l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__17_once, _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__17);
lean_inc(v_snd_3588_);
v___x_3721_ = l_Lean_MessageData_ofExpr(v_snd_3588_);
if (v_isShared_3586_ == 0)
{
lean_ctor_set_tag(v___x_3585_, 7);
lean_ctor_set(v___x_3585_, 1, v___x_3721_);
lean_ctor_set(v___x_3585_, 0, v___x_3720_);
v___x_3723_ = v___x_3585_;
goto v_reusejp_3722_;
}
else
{
lean_object* v_reuseFailAlloc_3725_; 
v_reuseFailAlloc_3725_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3725_, 0, v___x_3720_);
lean_ctor_set(v_reuseFailAlloc_3725_, 1, v___x_3721_);
v___x_3723_ = v_reuseFailAlloc_3725_;
goto v_reusejp_3722_;
}
v_reusejp_3722_:
{
lean_object* v___x_3724_; 
v___x_3724_ = l_Lean_addTrace___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__6(v___x_3702_, v___x_3723_, v_a_3555_, v_a_3556_, v_a_3557_, v_a_3558_);
if (lean_obj_tag(v___x_3724_) == 0)
{
lean_dec_ref_known(v___x_3724_, 1);
v___y_3704_ = v_a_3555_;
v___y_3705_ = v_a_3556_;
v___y_3706_ = v_a_3557_;
v_options_3707_ = v_options_3699_;
v_inheritedTraceOptions_3708_ = v_inheritedTraceOptions_3701_;
v___y_3709_ = v_a_3558_;
goto v___jp_3703_;
}
else
{
lean_del_object(v___x_3590_);
lean_dec(v_snd_3588_);
lean_dec(v_fst_3587_);
lean_dec(v_fst_3583_);
lean_del_object(v___x_3574_);
lean_dec(v_levelParams_3571_);
lean_dec(v_name_3570_);
lean_dec(v_ctors_3569_);
lean_dec(v_numParams_3568_);
lean_dec(v_rel_3554_);
return v___x_3724_;
}
}
}
v___jp_3703_:
{
lean_object* v___x_3710_; uint8_t v___x_3711_; 
v___x_3710_ = lean_obj_once(&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__13, &l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__13_once, _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__13);
v___x_3711_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3708_, v_options_3707_, v___x_3710_);
if (v___x_3711_ == 0)
{
lean_del_object(v___x_3590_);
v___y_3593_ = v___y_3704_;
v___y_3594_ = v___y_3705_;
v___y_3595_ = v___y_3706_;
v___y_3596_ = v___y_3709_;
goto v___jp_3592_;
}
else
{
lean_object* v___x_3712_; lean_object* v___x_3713_; lean_object* v___x_3715_; 
v___x_3712_ = lean_obj_once(&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__15, &l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__15_once, _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__15);
lean_inc(v_fst_3583_);
v___x_3713_ = l_Lean_MessageData_ofExpr(v_fst_3583_);
if (v_isShared_3591_ == 0)
{
lean_ctor_set_tag(v___x_3590_, 7);
lean_ctor_set(v___x_3590_, 1, v___x_3713_);
lean_ctor_set(v___x_3590_, 0, v___x_3712_);
v___x_3715_ = v___x_3590_;
goto v_reusejp_3714_;
}
else
{
lean_object* v_reuseFailAlloc_3717_; 
v_reuseFailAlloc_3717_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3717_, 0, v___x_3712_);
lean_ctor_set(v_reuseFailAlloc_3717_, 1, v___x_3713_);
v___x_3715_ = v_reuseFailAlloc_3717_;
goto v_reusejp_3714_;
}
v_reusejp_3714_:
{
lean_object* v___x_3716_; 
v___x_3716_ = l_Lean_addTrace___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__6(v___x_3702_, v___x_3715_, v___y_3704_, v___y_3705_, v___y_3706_, v___y_3709_);
if (lean_obj_tag(v___x_3716_) == 0)
{
lean_dec_ref_known(v___x_3716_, 1);
v___y_3593_ = v___y_3704_;
v___y_3594_ = v___y_3705_;
v___y_3595_ = v___y_3706_;
v___y_3596_ = v___y_3709_;
goto v___jp_3592_;
}
else
{
lean_dec(v_snd_3588_);
lean_dec(v_fst_3587_);
lean_dec(v_fst_3583_);
lean_del_object(v___x_3574_);
lean_dec(v_levelParams_3571_);
lean_dec(v_name_3570_);
lean_dec(v_ctors_3569_);
lean_dec(v_numParams_3568_);
lean_dec(v_rel_3554_);
return v___x_3716_;
}
}
}
}
}
v___jp_3592_:
{
lean_object* v___x_3597_; uint8_t v___x_3598_; lean_object* v___x_3599_; lean_object* v___x_3600_; 
lean_inc(v_fst_3583_);
v___x_3597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3597_, 0, v_fst_3583_);
v___x_3598_ = 0;
v___x_3599_ = lean_box(0);
v___x_3600_ = l_Lean_Meta_mkFreshExprMVar(v___x_3597_, v___x_3598_, v___x_3599_, v___y_3593_, v___y_3594_, v___y_3595_, v___y_3596_);
if (lean_obj_tag(v___x_3600_) == 0)
{
lean_object* v_a_3601_; lean_object* v___x_3602_; lean_object* v___x_3603_; 
v_a_3601_ = lean_ctor_get(v___x_3600_, 0);
lean_inc(v_a_3601_);
lean_dec_ref_known(v___x_3600_, 1);
v___x_3602_ = l_Lean_Expr_mvarId_x21(v_a_3601_);
v___x_3603_ = l_Lean_MVarId_intros(v___x_3602_, v___y_3593_, v___y_3594_, v___y_3595_, v___y_3596_);
if (lean_obj_tag(v___x_3603_) == 0)
{
lean_object* v_a_3604_; lean_object* v_fst_3605_; lean_object* v_snd_3606_; lean_object* v___x_3607_; lean_object* v___x_3608_; lean_object* v___x_3609_; lean_object* v___x_3610_; 
v_a_3604_ = lean_ctor_get(v___x_3603_, 0);
lean_inc(v_a_3604_);
lean_dec_ref_known(v___x_3603_, 1);
v_fst_3605_ = lean_ctor_get(v_a_3604_, 0);
lean_inc(v_fst_3605_);
v_snd_3606_ = lean_ctor_get(v_a_3604_, 1);
lean_inc(v_snd_3606_);
lean_dec(v_a_3604_);
v___x_3607_ = lean_obj_once(&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__4, &l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__4_once, _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__4);
v___x_3608_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__5));
v___x_3609_ = lean_box(0);
v___x_3610_ = l_Lean_MVarId_apply(v_snd_3606_, v___x_3607_, v___x_3608_, v___x_3609_, v___y_3593_, v___y_3594_, v___y_3595_, v___y_3596_);
if (lean_obj_tag(v___x_3610_) == 0)
{
lean_object* v_a_3611_; 
v_a_3611_ = lean_ctor_get(v___x_3610_, 0);
lean_inc(v_a_3611_);
lean_dec_ref_known(v___x_3610_, 1);
if (lean_obj_tag(v_a_3611_) == 1)
{
lean_object* v_tail_3612_; 
v_tail_3612_ = lean_ctor_get(v_a_3611_, 1);
lean_inc(v_tail_3612_);
if (lean_obj_tag(v_tail_3612_) == 1)
{
lean_object* v_tail_3613_; 
v_tail_3613_ = lean_ctor_get(v_tail_3612_, 1);
if (lean_obj_tag(v_tail_3613_) == 0)
{
lean_object* v_head_3614_; lean_object* v_head_3615_; lean_object* v___x_3617_; uint8_t v_isShared_3618_; uint8_t v_isSharedCheck_3672_; 
v_head_3614_ = lean_ctor_get(v_a_3611_, 0);
lean_inc(v_head_3614_);
lean_dec_ref_known(v_a_3611_, 2);
v_head_3615_ = lean_ctor_get(v_tail_3612_, 0);
v_isSharedCheck_3672_ = !lean_is_exclusive(v_tail_3612_);
if (v_isSharedCheck_3672_ == 0)
{
lean_object* v_unused_3673_; 
v_unused_3673_ = lean_ctor_get(v_tail_3612_, 1);
lean_dec(v_unused_3673_);
v___x_3617_ = v_tail_3612_;
v_isShared_3618_ = v_isSharedCheck_3672_;
goto v_resetjp_3616_;
}
else
{
lean_inc(v_head_3615_);
lean_dec(v_tail_3612_);
v___x_3617_ = lean_box(0);
v_isShared_3618_ = v_isSharedCheck_3672_;
goto v_resetjp_3616_;
}
v_resetjp_3616_:
{
lean_object* v___x_3619_; 
lean_inc(v_fst_3587_);
v___x_3619_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toCases(v_head_3614_, v_fst_3587_, v___y_3593_, v___y_3594_, v___y_3595_, v___y_3596_);
if (lean_obj_tag(v___x_3619_) == 0)
{
lean_object* v___x_3620_; 
lean_dec_ref_known(v___x_3619_, 1);
v___x_3620_ = l_Lean_Meta_intro1Core(v_head_3615_, v___x_3579_, v___y_3593_, v___y_3594_, v___y_3595_, v___y_3596_);
if (lean_obj_tag(v___x_3620_) == 0)
{
lean_object* v_a_3621_; lean_object* v_fst_3622_; lean_object* v_snd_3623_; lean_object* v___x_3624_; lean_object* v___x_3625_; lean_object* v___x_3626_; lean_object* v___x_3627_; lean_object* v___x_3628_; 
v_a_3621_ = lean_ctor_get(v___x_3620_, 0);
lean_inc(v_a_3621_);
lean_dec_ref_known(v___x_3620_, 1);
v_fst_3622_ = lean_ctor_get(v_a_3621_, 0);
lean_inc(v_fst_3622_);
v_snd_3623_ = lean_ctor_get(v_a_3621_, 1);
lean_inc(v_snd_3623_);
lean_dec(v_a_3621_);
v___x_3624_ = lean_array_to_list(v_fst_3605_);
v___x_3625_ = ((lean_object*)(l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__5___lam__0___closed__0));
lean_inc(v___x_3624_);
v___x_3626_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), v___x_3624_, v___x_3624_, v_numParams_3568_, v___x_3625_);
lean_dec(v___x_3624_);
v___x_3627_ = l_List_mapTR_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__2(v___x_3626_, v___x_3576_);
v___x_3628_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive(v_snd_3623_, v_ctors_3569_, v___x_3627_, v_fst_3587_, v_fst_3622_, v___y_3593_, v___y_3594_, v___y_3595_, v___y_3596_);
if (lean_obj_tag(v___x_3628_) == 0)
{
lean_object* v___x_3629_; lean_object* v_a_3630_; lean_object* v___x_3632_; 
lean_dec_ref_known(v___x_3628_, 1);
v___x_3629_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__3___redArg(v_a_3601_, v___y_3594_);
v_a_3630_ = lean_ctor_get(v___x_3629_, 0);
lean_inc(v_a_3630_);
lean_dec_ref(v___x_3629_);
lean_inc(v_levelParams_3571_);
lean_inc(v_rel_3554_);
if (v_isShared_3575_ == 0)
{
lean_ctor_set(v___x_3574_, 2, v_fst_3583_);
lean_ctor_set(v___x_3574_, 0, v_rel_3554_);
v___x_3632_ = v___x_3574_;
goto v_reusejp_3631_;
}
else
{
lean_object* v_reuseFailAlloc_3663_; 
v_reuseFailAlloc_3663_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3663_, 0, v_rel_3554_);
lean_ctor_set(v_reuseFailAlloc_3663_, 1, v_levelParams_3571_);
lean_ctor_set(v_reuseFailAlloc_3663_, 2, v_fst_3583_);
v___x_3632_ = v_reuseFailAlloc_3663_;
goto v_reusejp_3631_;
}
v_reusejp_3631_:
{
lean_object* v___x_3634_; 
if (v_isShared_3618_ == 0)
{
lean_ctor_set(v___x_3617_, 1, v___x_3576_);
lean_ctor_set(v___x_3617_, 0, v_rel_3554_);
v___x_3634_ = v___x_3617_;
goto v_reusejp_3633_;
}
else
{
lean_object* v_reuseFailAlloc_3662_; 
v_reuseFailAlloc_3662_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3662_, 0, v_rel_3554_);
lean_ctor_set(v_reuseFailAlloc_3662_, 1, v___x_3576_);
v___x_3634_ = v_reuseFailAlloc_3662_;
goto v_reusejp_3633_;
}
v_reusejp_3633_:
{
lean_object* v___x_3635_; lean_object* v___x_3636_; lean_object* v_a_3637_; lean_object* v___x_3638_; 
v___x_3635_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3635_, 0, v___x_3632_);
lean_ctor_set(v___x_3635_, 1, v_a_3630_);
lean_ctor_set(v___x_3635_, 2, v___x_3634_);
v___x_3636_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__4___redArg(v___x_3635_, v___y_3596_);
v_a_3637_ = lean_ctor_get(v___x_3636_, 0);
lean_inc(v_a_3637_);
lean_dec_ref(v___x_3636_);
v___x_3638_ = l_Lean_addDecl(v_a_3637_, v___x_3579_, v___y_3595_, v___y_3596_);
if (lean_obj_tag(v___x_3638_) == 0)
{
lean_object* v___x_3639_; 
lean_dec_ref_known(v___x_3638_, 1);
lean_inc(v___y_3596_);
lean_inc_ref(v___y_3595_);
lean_inc(v___y_3594_);
lean_inc_ref(v___y_3593_);
lean_inc(v_snd_3588_);
v___x_3639_ = lean_infer_type(v_snd_3588_, v___y_3593_, v___y_3594_, v___y_3595_, v___y_3596_);
if (lean_obj_tag(v___x_3639_) == 0)
{
lean_object* v_a_3640_; lean_object* v___x_3641_; lean_object* v___x_3642_; lean_object* v___x_3643_; lean_object* v___x_3644_; lean_object* v_a_3645_; lean_object* v___x_3647_; uint8_t v_isShared_3648_; uint8_t v_isSharedCheck_3653_; 
v_a_3640_ = lean_ctor_get(v___x_3639_, 0);
lean_inc(v_a_3640_);
lean_dec_ref_known(v___x_3639_, 1);
v___x_3641_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__7));
v___x_3642_ = l_Lean_Name_append(v_name_3570_, v___x_3641_);
v___x_3643_ = lean_box(0);
v___x_3644_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__5___redArg(v___x_3642_, v_levelParams_3571_, v_a_3640_, v_snd_3588_, v___x_3643_, v___y_3596_);
v_a_3645_ = lean_ctor_get(v___x_3644_, 0);
v_isSharedCheck_3653_ = !lean_is_exclusive(v___x_3644_);
if (v_isSharedCheck_3653_ == 0)
{
v___x_3647_ = v___x_3644_;
v_isShared_3648_ = v_isSharedCheck_3653_;
goto v_resetjp_3646_;
}
else
{
lean_inc(v_a_3645_);
lean_dec(v___x_3644_);
v___x_3647_ = lean_box(0);
v_isShared_3648_ = v_isSharedCheck_3653_;
goto v_resetjp_3646_;
}
v_resetjp_3646_:
{
lean_object* v___x_3650_; 
if (v_isShared_3648_ == 0)
{
lean_ctor_set_tag(v___x_3647_, 1);
v___x_3650_ = v___x_3647_;
goto v_reusejp_3649_;
}
else
{
lean_object* v_reuseFailAlloc_3652_; 
v_reuseFailAlloc_3652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3652_, 0, v_a_3645_);
v___x_3650_ = v_reuseFailAlloc_3652_;
goto v_reusejp_3649_;
}
v_reusejp_3649_:
{
lean_object* v___x_3651_; 
v___x_3651_ = l_Lean_addDecl(v___x_3650_, v___x_3579_, v___y_3595_, v___y_3596_);
return v___x_3651_;
}
}
}
else
{
lean_object* v_a_3654_; lean_object* v___x_3656_; uint8_t v_isShared_3657_; uint8_t v_isSharedCheck_3661_; 
lean_dec(v_snd_3588_);
lean_dec(v_levelParams_3571_);
lean_dec(v_name_3570_);
v_a_3654_ = lean_ctor_get(v___x_3639_, 0);
v_isSharedCheck_3661_ = !lean_is_exclusive(v___x_3639_);
if (v_isSharedCheck_3661_ == 0)
{
v___x_3656_ = v___x_3639_;
v_isShared_3657_ = v_isSharedCheck_3661_;
goto v_resetjp_3655_;
}
else
{
lean_inc(v_a_3654_);
lean_dec(v___x_3639_);
v___x_3656_ = lean_box(0);
v_isShared_3657_ = v_isSharedCheck_3661_;
goto v_resetjp_3655_;
}
v_resetjp_3655_:
{
lean_object* v___x_3659_; 
if (v_isShared_3657_ == 0)
{
v___x_3659_ = v___x_3656_;
goto v_reusejp_3658_;
}
else
{
lean_object* v_reuseFailAlloc_3660_; 
v_reuseFailAlloc_3660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3660_, 0, v_a_3654_);
v___x_3659_ = v_reuseFailAlloc_3660_;
goto v_reusejp_3658_;
}
v_reusejp_3658_:
{
return v___x_3659_;
}
}
}
}
else
{
lean_dec(v_snd_3588_);
lean_dec(v_levelParams_3571_);
lean_dec(v_name_3570_);
return v___x_3638_;
}
}
}
}
else
{
lean_del_object(v___x_3617_);
lean_dec(v_a_3601_);
lean_dec(v_snd_3588_);
lean_dec(v_fst_3583_);
lean_del_object(v___x_3574_);
lean_dec(v_levelParams_3571_);
lean_dec(v_name_3570_);
lean_dec(v_rel_3554_);
return v___x_3628_;
}
}
else
{
lean_object* v_a_3664_; lean_object* v___x_3666_; uint8_t v_isShared_3667_; uint8_t v_isSharedCheck_3671_; 
lean_del_object(v___x_3617_);
lean_dec(v_fst_3605_);
lean_dec(v_a_3601_);
lean_dec(v_snd_3588_);
lean_dec(v_fst_3587_);
lean_dec(v_fst_3583_);
lean_del_object(v___x_3574_);
lean_dec(v_levelParams_3571_);
lean_dec(v_name_3570_);
lean_dec(v_ctors_3569_);
lean_dec(v_numParams_3568_);
lean_dec(v_rel_3554_);
v_a_3664_ = lean_ctor_get(v___x_3620_, 0);
v_isSharedCheck_3671_ = !lean_is_exclusive(v___x_3620_);
if (v_isSharedCheck_3671_ == 0)
{
v___x_3666_ = v___x_3620_;
v_isShared_3667_ = v_isSharedCheck_3671_;
goto v_resetjp_3665_;
}
else
{
lean_inc(v_a_3664_);
lean_dec(v___x_3620_);
v___x_3666_ = lean_box(0);
v_isShared_3667_ = v_isSharedCheck_3671_;
goto v_resetjp_3665_;
}
v_resetjp_3665_:
{
lean_object* v___x_3669_; 
if (v_isShared_3667_ == 0)
{
v___x_3669_ = v___x_3666_;
goto v_reusejp_3668_;
}
else
{
lean_object* v_reuseFailAlloc_3670_; 
v_reuseFailAlloc_3670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3670_, 0, v_a_3664_);
v___x_3669_ = v_reuseFailAlloc_3670_;
goto v_reusejp_3668_;
}
v_reusejp_3668_:
{
return v___x_3669_;
}
}
}
}
else
{
lean_del_object(v___x_3617_);
lean_dec(v_head_3615_);
lean_dec(v_fst_3605_);
lean_dec(v_a_3601_);
lean_dec(v_snd_3588_);
lean_dec(v_fst_3587_);
lean_dec(v_fst_3583_);
lean_del_object(v___x_3574_);
lean_dec(v_levelParams_3571_);
lean_dec(v_name_3570_);
lean_dec(v_ctors_3569_);
lean_dec(v_numParams_3568_);
lean_dec(v_rel_3554_);
return v___x_3619_;
}
}
}
else
{
lean_dec_ref_known(v_tail_3612_, 2);
lean_dec_ref_known(v_a_3611_, 2);
lean_dec(v_fst_3605_);
lean_dec(v_a_3601_);
lean_dec(v_snd_3588_);
lean_dec(v_fst_3587_);
lean_dec(v_fst_3583_);
lean_del_object(v___x_3574_);
lean_dec(v_levelParams_3571_);
lean_dec(v_name_3570_);
lean_dec(v_ctors_3569_);
lean_dec(v_numParams_3568_);
lean_dec(v_rel_3554_);
v___y_3561_ = v___y_3593_;
v___y_3562_ = v___y_3594_;
v___y_3563_ = v___y_3595_;
v___y_3564_ = v___y_3596_;
goto v___jp_3560_;
}
}
else
{
lean_dec_ref_known(v_a_3611_, 2);
lean_dec(v_tail_3612_);
lean_dec(v_fst_3605_);
lean_dec(v_a_3601_);
lean_dec(v_snd_3588_);
lean_dec(v_fst_3587_);
lean_dec(v_fst_3583_);
lean_del_object(v___x_3574_);
lean_dec(v_levelParams_3571_);
lean_dec(v_name_3570_);
lean_dec(v_ctors_3569_);
lean_dec(v_numParams_3568_);
lean_dec(v_rel_3554_);
v___y_3561_ = v___y_3593_;
v___y_3562_ = v___y_3594_;
v___y_3563_ = v___y_3595_;
v___y_3564_ = v___y_3596_;
goto v___jp_3560_;
}
}
else
{
lean_dec(v_a_3611_);
lean_dec(v_fst_3605_);
lean_dec(v_a_3601_);
lean_dec(v_snd_3588_);
lean_dec(v_fst_3587_);
lean_dec(v_fst_3583_);
lean_del_object(v___x_3574_);
lean_dec(v_levelParams_3571_);
lean_dec(v_name_3570_);
lean_dec(v_ctors_3569_);
lean_dec(v_numParams_3568_);
lean_dec(v_rel_3554_);
v___y_3561_ = v___y_3593_;
v___y_3562_ = v___y_3594_;
v___y_3563_ = v___y_3595_;
v___y_3564_ = v___y_3596_;
goto v___jp_3560_;
}
}
else
{
lean_object* v_a_3674_; lean_object* v___x_3676_; uint8_t v_isShared_3677_; uint8_t v_isSharedCheck_3681_; 
lean_dec(v_fst_3605_);
lean_dec(v_a_3601_);
lean_dec(v_snd_3588_);
lean_dec(v_fst_3587_);
lean_dec(v_fst_3583_);
lean_del_object(v___x_3574_);
lean_dec(v_levelParams_3571_);
lean_dec(v_name_3570_);
lean_dec(v_ctors_3569_);
lean_dec(v_numParams_3568_);
lean_dec(v_rel_3554_);
v_a_3674_ = lean_ctor_get(v___x_3610_, 0);
v_isSharedCheck_3681_ = !lean_is_exclusive(v___x_3610_);
if (v_isSharedCheck_3681_ == 0)
{
v___x_3676_ = v___x_3610_;
v_isShared_3677_ = v_isSharedCheck_3681_;
goto v_resetjp_3675_;
}
else
{
lean_inc(v_a_3674_);
lean_dec(v___x_3610_);
v___x_3676_ = lean_box(0);
v_isShared_3677_ = v_isSharedCheck_3681_;
goto v_resetjp_3675_;
}
v_resetjp_3675_:
{
lean_object* v___x_3679_; 
if (v_isShared_3677_ == 0)
{
v___x_3679_ = v___x_3676_;
goto v_reusejp_3678_;
}
else
{
lean_object* v_reuseFailAlloc_3680_; 
v_reuseFailAlloc_3680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3680_, 0, v_a_3674_);
v___x_3679_ = v_reuseFailAlloc_3680_;
goto v_reusejp_3678_;
}
v_reusejp_3678_:
{
return v___x_3679_;
}
}
}
}
else
{
lean_object* v_a_3682_; lean_object* v___x_3684_; uint8_t v_isShared_3685_; uint8_t v_isSharedCheck_3689_; 
lean_dec(v_a_3601_);
lean_dec(v_snd_3588_);
lean_dec(v_fst_3587_);
lean_dec(v_fst_3583_);
lean_del_object(v___x_3574_);
lean_dec(v_levelParams_3571_);
lean_dec(v_name_3570_);
lean_dec(v_ctors_3569_);
lean_dec(v_numParams_3568_);
lean_dec(v_rel_3554_);
v_a_3682_ = lean_ctor_get(v___x_3603_, 0);
v_isSharedCheck_3689_ = !lean_is_exclusive(v___x_3603_);
if (v_isSharedCheck_3689_ == 0)
{
v___x_3684_ = v___x_3603_;
v_isShared_3685_ = v_isSharedCheck_3689_;
goto v_resetjp_3683_;
}
else
{
lean_inc(v_a_3682_);
lean_dec(v___x_3603_);
v___x_3684_ = lean_box(0);
v_isShared_3685_ = v_isSharedCheck_3689_;
goto v_resetjp_3683_;
}
v_resetjp_3683_:
{
lean_object* v___x_3687_; 
if (v_isShared_3685_ == 0)
{
v___x_3687_ = v___x_3684_;
goto v_reusejp_3686_;
}
else
{
lean_object* v_reuseFailAlloc_3688_; 
v_reuseFailAlloc_3688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3688_, 0, v_a_3682_);
v___x_3687_ = v_reuseFailAlloc_3688_;
goto v_reusejp_3686_;
}
v_reusejp_3686_:
{
return v___x_3687_;
}
}
}
}
else
{
lean_object* v_a_3690_; lean_object* v___x_3692_; uint8_t v_isShared_3693_; uint8_t v_isSharedCheck_3697_; 
lean_dec(v_snd_3588_);
lean_dec(v_fst_3587_);
lean_dec(v_fst_3583_);
lean_del_object(v___x_3574_);
lean_dec(v_levelParams_3571_);
lean_dec(v_name_3570_);
lean_dec(v_ctors_3569_);
lean_dec(v_numParams_3568_);
lean_dec(v_rel_3554_);
v_a_3690_ = lean_ctor_get(v___x_3600_, 0);
v_isSharedCheck_3697_ = !lean_is_exclusive(v___x_3600_);
if (v_isSharedCheck_3697_ == 0)
{
v___x_3692_ = v___x_3600_;
v_isShared_3693_ = v_isSharedCheck_3697_;
goto v_resetjp_3691_;
}
else
{
lean_inc(v_a_3690_);
lean_dec(v___x_3600_);
v___x_3692_ = lean_box(0);
v_isShared_3693_ = v_isSharedCheck_3697_;
goto v_resetjp_3691_;
}
v_resetjp_3691_:
{
lean_object* v___x_3695_; 
if (v_isShared_3693_ == 0)
{
v___x_3695_ = v___x_3692_;
goto v_reusejp_3694_;
}
else
{
lean_object* v_reuseFailAlloc_3696_; 
v_reuseFailAlloc_3696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3696_, 0, v_a_3690_);
v___x_3695_ = v_reuseFailAlloc_3696_;
goto v_reusejp_3694_;
}
v_reusejp_3694_:
{
return v___x_3695_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3728_; lean_object* v___x_3730_; uint8_t v_isShared_3731_; uint8_t v_isSharedCheck_3735_; 
lean_del_object(v___x_3574_);
lean_dec(v_levelParams_3571_);
lean_dec(v_name_3570_);
lean_dec(v_ctors_3569_);
lean_dec(v_numParams_3568_);
lean_dec(v_rel_3554_);
v_a_3728_ = lean_ctor_get(v___x_3580_, 0);
v_isSharedCheck_3735_ = !lean_is_exclusive(v___x_3580_);
if (v_isSharedCheck_3735_ == 0)
{
v___x_3730_ = v___x_3580_;
v_isShared_3731_ = v_isSharedCheck_3735_;
goto v_resetjp_3729_;
}
else
{
lean_inc(v_a_3728_);
lean_dec(v___x_3580_);
v___x_3730_ = lean_box(0);
v_isShared_3731_ = v_isSharedCheck_3735_;
goto v_resetjp_3729_;
}
v_resetjp_3729_:
{
lean_object* v___x_3733_; 
if (v_isShared_3731_ == 0)
{
v___x_3733_ = v___x_3730_;
goto v_reusejp_3732_;
}
else
{
lean_object* v_reuseFailAlloc_3734_; 
v_reuseFailAlloc_3734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3734_, 0, v_a_3728_);
v___x_3733_ = v_reuseFailAlloc_3734_;
goto v_reusejp_3732_;
}
v_reusejp_3732_:
{
return v___x_3733_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___boxed(lean_object* v_inductVal_3737_, lean_object* v_rel_3738_, lean_object* v_a_3739_, lean_object* v_a_3740_, lean_object* v_a_3741_, lean_object* v_a_3742_, lean_object* v_a_3743_){
_start:
{
lean_object* v_res_3744_; 
v_res_3744_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl(v_inductVal_3737_, v_rel_3738_, v_a_3739_, v_a_3740_, v_a_3741_, v_a_3742_);
lean_dec(v_a_3742_);
lean_dec_ref(v_a_3741_);
lean_dec(v_a_3740_);
lean_dec_ref(v_a_3739_);
return v_res_3744_;
}
}
static lean_object* _init_l_Lean_Meta_mkSumOfProducts___closed__3(void){
_start:
{
lean_object* v___x_3749_; lean_object* v___x_3750_; 
v___x_3749_ = ((lean_object*)(l_Lean_Meta_mkSumOfProducts___closed__2));
v___x_3750_ = l_Lean_stringToMessageData(v___x_3749_);
return v___x_3750_;
}
}
static lean_object* _init_l_Lean_Meta_mkSumOfProducts___closed__5(void){
_start:
{
lean_object* v___x_3752_; lean_object* v___x_3753_; 
v___x_3752_ = ((lean_object*)(l_Lean_Meta_mkSumOfProducts___closed__4));
v___x_3753_ = l_Lean_stringToMessageData(v___x_3752_);
return v___x_3753_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSumOfProducts(lean_object* v_declName_3754_, lean_object* v_a_3755_, lean_object* v_a_3756_, lean_object* v_a_3757_, lean_object* v_a_3758_){
_start:
{
lean_object* v___y_3761_; lean_object* v___y_3762_; lean_object* v___y_3763_; lean_object* v___y_3764_; lean_object* v_toCold_3781_; lean_object* v_options_3782_; uint8_t v_hasTrace_3783_; 
v_toCold_3781_ = lean_ctor_get(v_a_3757_, 0);
v_options_3782_ = lean_ctor_get(v_toCold_3781_, 2);
v_hasTrace_3783_ = lean_ctor_get_uint8(v_options_3782_, sizeof(void*)*1);
if (v_hasTrace_3783_ == 0)
{
v___y_3761_ = v_a_3755_;
v___y_3762_ = v_a_3756_;
v___y_3763_ = v_a_3757_;
v___y_3764_ = v_a_3758_;
goto v___jp_3760_;
}
else
{
lean_object* v_inheritedTraceOptions_3784_; lean_object* v_cls_3785_; lean_object* v___x_3786_; uint8_t v___x_3787_; 
v_inheritedTraceOptions_3784_ = lean_ctor_get(v_toCold_3781_, 11);
v_cls_3785_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__10));
v___x_3786_ = lean_obj_once(&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__13, &l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__13_once, _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__13);
v___x_3787_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3784_, v_options_3782_, v___x_3786_);
if (v___x_3787_ == 0)
{
v___y_3761_ = v_a_3755_;
v___y_3762_ = v_a_3756_;
v___y_3763_ = v_a_3757_;
v___y_3764_ = v_a_3758_;
goto v___jp_3760_;
}
else
{
lean_object* v___x_3788_; lean_object* v___x_3789_; lean_object* v___x_3790_; lean_object* v___x_3791_; 
v___x_3788_ = lean_obj_once(&l_Lean_Meta_mkSumOfProducts___closed__5, &l_Lean_Meta_mkSumOfProducts___closed__5_once, _init_l_Lean_Meta_mkSumOfProducts___closed__5);
lean_inc(v_declName_3754_);
v___x_3789_ = l_Lean_MessageData_ofName(v_declName_3754_);
v___x_3790_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3790_, 0, v___x_3788_);
lean_ctor_set(v___x_3790_, 1, v___x_3789_);
v___x_3791_ = l_Lean_addTrace___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__6(v_cls_3785_, v___x_3790_, v_a_3755_, v_a_3756_, v_a_3757_, v_a_3758_);
if (lean_obj_tag(v___x_3791_) == 0)
{
lean_dec_ref_known(v___x_3791_, 1);
v___y_3761_ = v_a_3755_;
v___y_3762_ = v_a_3756_;
v___y_3763_ = v_a_3757_;
v___y_3764_ = v_a_3758_;
goto v___jp_3760_;
}
else
{
lean_dec(v_declName_3754_);
return v___x_3791_;
}
}
}
v___jp_3760_:
{
lean_object* v___x_3765_; 
lean_inc(v_declName_3754_);
v___x_3765_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0(v_declName_3754_, v___y_3761_, v___y_3762_, v___y_3763_, v___y_3764_);
if (lean_obj_tag(v___x_3765_) == 0)
{
lean_object* v_a_3766_; 
v_a_3766_ = lean_ctor_get(v___x_3765_, 0);
lean_inc(v_a_3766_);
lean_dec_ref_known(v___x_3765_, 1);
if (lean_obj_tag(v_a_3766_) == 5)
{
lean_object* v_val_3767_; lean_object* v___x_3768_; lean_object* v___x_3769_; lean_object* v___x_3770_; 
v_val_3767_ = lean_ctor_get(v_a_3766_, 0);
lean_inc_ref(v_val_3767_);
lean_dec_ref_known(v_a_3766_, 1);
v___x_3768_ = ((lean_object*)(l_Lean_Meta_mkSumOfProducts___closed__1));
v___x_3769_ = l_Lean_Name_append(v_declName_3754_, v___x_3768_);
v___x_3770_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl(v_val_3767_, v___x_3769_, v___y_3761_, v___y_3762_, v___y_3763_, v___y_3764_);
return v___x_3770_;
}
else
{
lean_object* v___x_3771_; lean_object* v___x_3772_; 
lean_dec(v_a_3766_);
lean_dec(v_declName_3754_);
v___x_3771_ = lean_obj_once(&l_Lean_Meta_mkSumOfProducts___closed__3, &l_Lean_Meta_mkSumOfProducts___closed__3_once, _init_l_Lean_Meta_mkSumOfProducts___closed__3);
v___x_3772_ = l_Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0___redArg(v___x_3771_, v___y_3761_, v___y_3762_, v___y_3763_, v___y_3764_);
return v___x_3772_;
}
}
else
{
lean_object* v_a_3773_; lean_object* v___x_3775_; uint8_t v_isShared_3776_; uint8_t v_isSharedCheck_3780_; 
lean_dec(v_declName_3754_);
v_a_3773_ = lean_ctor_get(v___x_3765_, 0);
v_isSharedCheck_3780_ = !lean_is_exclusive(v___x_3765_);
if (v_isSharedCheck_3780_ == 0)
{
v___x_3775_ = v___x_3765_;
v_isShared_3776_ = v_isSharedCheck_3780_;
goto v_resetjp_3774_;
}
else
{
lean_inc(v_a_3773_);
lean_dec(v___x_3765_);
v___x_3775_ = lean_box(0);
v_isShared_3776_ = v_isSharedCheck_3780_;
goto v_resetjp_3774_;
}
v_resetjp_3774_:
{
lean_object* v___x_3778_; 
if (v_isShared_3776_ == 0)
{
v___x_3778_ = v___x_3775_;
goto v_reusejp_3777_;
}
else
{
lean_object* v_reuseFailAlloc_3779_; 
v_reuseFailAlloc_3779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3779_, 0, v_a_3773_);
v___x_3778_ = v_reuseFailAlloc_3779_;
goto v_reusejp_3777_;
}
v_reusejp_3777_:
{
return v___x_3778_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSumOfProducts___boxed(lean_object* v_declName_3792_, lean_object* v_a_3793_, lean_object* v_a_3794_, lean_object* v_a_3795_, lean_object* v_a_3796_, lean_object* v_a_3797_){
_start:
{
lean_object* v_res_3798_; 
v_res_3798_ = l_Lean_Meta_mkSumOfProducts(v_declName_3792_, v_a_3793_, v_a_3794_, v_a_3795_, v_a_3796_);
lean_dec(v_a_3796_);
lean_dec_ref(v_a_3795_);
lean_dec(v_a_3794_);
lean_dec_ref(v_a_3793_);
return v_res_3798_;
}
}
static lean_object* _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3838_; lean_object* v___x_3839_; lean_object* v___x_3840_; 
v___x_3838_ = lean_unsigned_to_nat(3649998058u);
v___x_3839_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2_));
v___x_3840_ = l_Lean_Name_num___override(v___x_3839_, v___x_3838_);
return v___x_3840_;
}
}
static lean_object* _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3842_; lean_object* v___x_3843_; lean_object* v___x_3844_; 
v___x_3842_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2_));
v___x_3843_ = lean_obj_once(&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2_, &l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2_);
v___x_3844_ = l_Lean_Name_str___override(v___x_3843_, v___x_3842_);
return v___x_3844_;
}
}
static lean_object* _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3846_; lean_object* v___x_3847_; lean_object* v___x_3848_; 
v___x_3846_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2_));
v___x_3847_ = lean_obj_once(&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2_, &l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2_);
v___x_3848_ = l_Lean_Name_str___override(v___x_3847_, v___x_3846_);
return v___x_3848_;
}
}
static lean_object* _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3849_; lean_object* v___x_3850_; lean_object* v___x_3851_; 
v___x_3849_ = lean_unsigned_to_nat(2u);
v___x_3850_ = lean_obj_once(&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2_, &l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2_);
v___x_3851_ = l_Lean_Name_num___override(v___x_3850_, v___x_3849_);
return v___x_3851_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3853_; uint8_t v___x_3854_; lean_object* v___x_3855_; lean_object* v___x_3856_; 
v___x_3853_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__10));
v___x_3854_ = 0;
v___x_3855_ = lean_obj_once(&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2_, &l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2_);
v___x_3856_ = l_Lean_registerTraceClass(v___x_3853_, v___x_3854_, v___x_3855_);
return v___x_3856_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2____boxed(lean_object* v_a_3857_){
_start:
{
lean_object* v_res_3858_; 
v_res_3858_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2_();
return v_res_3858_;
}
}
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Apply(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Cases(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Impl(uint8_t builtin);
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
res = runtime_initialize_Init_Data_List_Impl(builtin);
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
lean_object* initialize_Init_Data_List_Impl(uint8_t builtin);
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
res = initialize_Init_Data_List_Impl(builtin);
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
