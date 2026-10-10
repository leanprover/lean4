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
lean_object* l_Lean_stringToMessageData(lean_object*);
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
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
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
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "A declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "` exists in the private scope of `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__19;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 56, .m_capacity = 56, .m_length = 55, .m_data = "`, which is accessible here through `import all`, but `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__20 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__20_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__21;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 66, .m_capacity = 66, .m_length = 65, .m_data = "` does not export it, so it cannot be accessed in a public scope."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__22 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__22_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__23;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__24 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__24_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__25;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__26 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__26_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__27;
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
uint8_t l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__0(lean_object* v_x_1_){
_start:
{
uint8_t v___x_2_; 
v___x_2_ = 0;
return v___x_2_;
}
}
LEAN_EXPORT void l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1_ = stack[0].m_obj;
uint8_t v_res_3_;
v_res_3_ = l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__0(v_x_1_);
stack->m_num = v_res_3_;
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__0___boxed(lean_object* v_x_4_){
_start:
{
uint8_t v_res_5_; lean_object* v_r_6_; 
v_res_5_ = l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__0(v_x_4_);
lean_dec(v_x_4_);
v_r_6_ = lean_box(v_res_5_);
return v_r_6_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3_spec__5_spec__6___redArg(lean_object* v_x_7_, lean_object* v_x_8_, lean_object* v_x_9_, lean_object* v_x_10_){
_start:
{
lean_object* v_ks_11_; lean_object* v_vs_12_; lean_object* v___x_14_; uint8_t v_isShared_15_; uint8_t v_isSharedCheck_36_; 
v_ks_11_ = lean_ctor_get(v_x_7_, 0);
v_vs_12_ = lean_ctor_get(v_x_7_, 1);
v_isSharedCheck_36_ = !lean_is_exclusive(v_x_7_);
if (v_isSharedCheck_36_ == 0)
{
v___x_14_ = v_x_7_;
v_isShared_15_ = v_isSharedCheck_36_;
goto v_resetjp_13_;
}
else
{
lean_inc(v_vs_12_);
lean_inc(v_ks_11_);
lean_dec(v_x_7_);
v___x_14_ = lean_box(0);
v_isShared_15_ = v_isSharedCheck_36_;
goto v_resetjp_13_;
}
v_resetjp_13_:
{
lean_object* v___x_16_; uint8_t v___x_17_; 
v___x_16_ = lean_array_get_size(v_ks_11_);
v___x_17_ = lean_nat_dec_lt(v_x_8_, v___x_16_);
if (v___x_17_ == 0)
{
lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_21_; 
lean_dec(v_x_8_);
v___x_18_ = lean_array_push(v_ks_11_, v_x_9_);
v___x_19_ = lean_array_push(v_vs_12_, v_x_10_);
if (v_isShared_15_ == 0)
{
lean_ctor_set(v___x_14_, 1, v___x_19_);
lean_ctor_set(v___x_14_, 0, v___x_18_);
v___x_21_ = v___x_14_;
goto v_reusejp_20_;
}
else
{
lean_object* v_reuseFailAlloc_22_; 
v_reuseFailAlloc_22_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_22_, 0, v___x_18_);
lean_ctor_set(v_reuseFailAlloc_22_, 1, v___x_19_);
v___x_21_ = v_reuseFailAlloc_22_;
goto v_reusejp_20_;
}
v_reusejp_20_:
{
return v___x_21_;
}
}
else
{
lean_object* v_k_x27_23_; uint8_t v___x_24_; 
v_k_x27_23_ = lean_array_fget_borrowed(v_ks_11_, v_x_8_);
v___x_24_ = l_Lean_instBEqMVarId_beq(v_x_9_, v_k_x27_23_);
if (v___x_24_ == 0)
{
lean_object* v___x_26_; 
if (v_isShared_15_ == 0)
{
v___x_26_ = v___x_14_;
goto v_reusejp_25_;
}
else
{
lean_object* v_reuseFailAlloc_30_; 
v_reuseFailAlloc_30_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_30_, 0, v_ks_11_);
lean_ctor_set(v_reuseFailAlloc_30_, 1, v_vs_12_);
v___x_26_ = v_reuseFailAlloc_30_;
goto v_reusejp_25_;
}
v_reusejp_25_:
{
lean_object* v___x_27_; lean_object* v___x_28_; 
v___x_27_ = lean_unsigned_to_nat(1u);
v___x_28_ = lean_nat_add(v_x_8_, v___x_27_);
lean_dec(v_x_8_);
v_x_7_ = v___x_26_;
v_x_8_ = v___x_28_;
goto _start;
}
}
else
{
lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_34_; 
v___x_31_ = lean_array_fset(v_ks_11_, v_x_8_, v_x_9_);
v___x_32_ = lean_array_fset(v_vs_12_, v_x_8_, v_x_10_);
lean_dec(v_x_8_);
if (v_isShared_15_ == 0)
{
lean_ctor_set(v___x_14_, 1, v___x_32_);
lean_ctor_set(v___x_14_, 0, v___x_31_);
v___x_34_ = v___x_14_;
goto v_reusejp_33_;
}
else
{
lean_object* v_reuseFailAlloc_35_; 
v_reuseFailAlloc_35_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_35_, 0, v___x_31_);
lean_ctor_set(v_reuseFailAlloc_35_, 1, v___x_32_);
v___x_34_ = v_reuseFailAlloc_35_;
goto v_reusejp_33_;
}
v_reusejp_33_:
{
return v___x_34_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3_spec__5___redArg(lean_object* v_n_37_, lean_object* v_k_38_, lean_object* v_v_39_){
_start:
{
lean_object* v___x_40_; lean_object* v___x_41_; 
v___x_40_ = lean_unsigned_to_nat(0u);
v___x_41_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3_spec__5_spec__6___redArg(v_n_37_, v___x_40_, v_k_38_, v_v_39_);
return v___x_41_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_42_; 
v___x_42_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_42_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3___redArg(lean_object* v_x_43_, size_t v_x_44_, size_t v_x_45_, lean_object* v_x_46_, lean_object* v_x_47_){
_start:
{
if (lean_obj_tag(v_x_43_) == 0)
{
lean_object* v_es_48_; size_t v___x_49_; size_t v___x_50_; lean_object* v_j_51_; lean_object* v___x_52_; uint8_t v___x_53_; 
v_es_48_ = lean_ctor_get(v_x_43_, 0);
v___x_49_ = ((size_t)31ULL);
v___x_50_ = lean_usize_land(v_x_44_, v___x_49_);
v_j_51_ = lean_usize_to_nat(v___x_50_);
v___x_52_ = lean_array_get_size(v_es_48_);
v___x_53_ = lean_nat_dec_lt(v_j_51_, v___x_52_);
if (v___x_53_ == 0)
{
lean_dec(v_j_51_);
lean_dec(v_x_47_);
lean_dec(v_x_46_);
return v_x_43_;
}
else
{
lean_object* v___x_55_; uint8_t v_isShared_56_; uint8_t v_isSharedCheck_92_; 
lean_inc_ref(v_es_48_);
v_isSharedCheck_92_ = !lean_is_exclusive(v_x_43_);
if (v_isSharedCheck_92_ == 0)
{
lean_object* v_unused_93_; 
v_unused_93_ = lean_ctor_get(v_x_43_, 0);
lean_dec(v_unused_93_);
v___x_55_ = v_x_43_;
v_isShared_56_ = v_isSharedCheck_92_;
goto v_resetjp_54_;
}
else
{
lean_dec(v_x_43_);
v___x_55_ = lean_box(0);
v_isShared_56_ = v_isSharedCheck_92_;
goto v_resetjp_54_;
}
v_resetjp_54_:
{
lean_object* v_v_57_; lean_object* v___x_58_; lean_object* v_xs_x27_59_; lean_object* v___y_61_; 
v_v_57_ = lean_array_fget(v_es_48_, v_j_51_);
v___x_58_ = lean_box(0);
v_xs_x27_59_ = lean_array_fset(v_es_48_, v_j_51_, v___x_58_);
switch(lean_obj_tag(v_v_57_))
{
case 0:
{
lean_object* v_key_66_; lean_object* v_val_67_; lean_object* v___x_69_; uint8_t v_isShared_70_; uint8_t v_isSharedCheck_77_; 
v_key_66_ = lean_ctor_get(v_v_57_, 0);
v_val_67_ = lean_ctor_get(v_v_57_, 1);
v_isSharedCheck_77_ = !lean_is_exclusive(v_v_57_);
if (v_isSharedCheck_77_ == 0)
{
v___x_69_ = v_v_57_;
v_isShared_70_ = v_isSharedCheck_77_;
goto v_resetjp_68_;
}
else
{
lean_inc(v_val_67_);
lean_inc(v_key_66_);
lean_dec(v_v_57_);
v___x_69_ = lean_box(0);
v_isShared_70_ = v_isSharedCheck_77_;
goto v_resetjp_68_;
}
v_resetjp_68_:
{
uint8_t v___x_71_; 
v___x_71_ = l_Lean_instBEqMVarId_beq(v_x_46_, v_key_66_);
if (v___x_71_ == 0)
{
lean_object* v___x_72_; lean_object* v___x_73_; 
lean_del_object(v___x_69_);
v___x_72_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_66_, v_val_67_, v_x_46_, v_x_47_);
v___x_73_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_73_, 0, v___x_72_);
v___y_61_ = v___x_73_;
goto v___jp_60_;
}
else
{
lean_object* v___x_75_; 
lean_dec(v_val_67_);
lean_dec(v_key_66_);
if (v_isShared_70_ == 0)
{
lean_ctor_set(v___x_69_, 1, v_x_47_);
lean_ctor_set(v___x_69_, 0, v_x_46_);
v___x_75_ = v___x_69_;
goto v_reusejp_74_;
}
else
{
lean_object* v_reuseFailAlloc_76_; 
v_reuseFailAlloc_76_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_76_, 0, v_x_46_);
lean_ctor_set(v_reuseFailAlloc_76_, 1, v_x_47_);
v___x_75_ = v_reuseFailAlloc_76_;
goto v_reusejp_74_;
}
v_reusejp_74_:
{
v___y_61_ = v___x_75_;
goto v___jp_60_;
}
}
}
}
case 1:
{
lean_object* v_node_78_; lean_object* v___x_80_; uint8_t v_isShared_81_; uint8_t v_isSharedCheck_90_; 
v_node_78_ = lean_ctor_get(v_v_57_, 0);
v_isSharedCheck_90_ = !lean_is_exclusive(v_v_57_);
if (v_isSharedCheck_90_ == 0)
{
v___x_80_ = v_v_57_;
v_isShared_81_ = v_isSharedCheck_90_;
goto v_resetjp_79_;
}
else
{
lean_inc(v_node_78_);
lean_dec(v_v_57_);
v___x_80_ = lean_box(0);
v_isShared_81_ = v_isSharedCheck_90_;
goto v_resetjp_79_;
}
v_resetjp_79_:
{
size_t v___x_82_; size_t v___x_83_; size_t v___x_84_; size_t v___x_85_; lean_object* v___x_86_; lean_object* v___x_88_; 
v___x_82_ = ((size_t)5ULL);
v___x_83_ = lean_usize_shift_right(v_x_44_, v___x_82_);
v___x_84_ = ((size_t)1ULL);
v___x_85_ = lean_usize_add(v_x_45_, v___x_84_);
v___x_86_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3___redArg(v_node_78_, v___x_83_, v___x_85_, v_x_46_, v_x_47_);
if (v_isShared_81_ == 0)
{
lean_ctor_set(v___x_80_, 0, v___x_86_);
v___x_88_ = v___x_80_;
goto v_reusejp_87_;
}
else
{
lean_object* v_reuseFailAlloc_89_; 
v_reuseFailAlloc_89_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_89_, 0, v___x_86_);
v___x_88_ = v_reuseFailAlloc_89_;
goto v_reusejp_87_;
}
v_reusejp_87_:
{
v___y_61_ = v___x_88_;
goto v___jp_60_;
}
}
}
default: 
{
lean_object* v___x_91_; 
v___x_91_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_91_, 0, v_x_46_);
lean_ctor_set(v___x_91_, 1, v_x_47_);
v___y_61_ = v___x_91_;
goto v___jp_60_;
}
}
v___jp_60_:
{
lean_object* v___x_62_; lean_object* v___x_64_; 
v___x_62_ = lean_array_fset(v_xs_x27_59_, v_j_51_, v___y_61_);
lean_dec(v_j_51_);
if (v_isShared_56_ == 0)
{
lean_ctor_set(v___x_55_, 0, v___x_62_);
v___x_64_ = v___x_55_;
goto v_reusejp_63_;
}
else
{
lean_object* v_reuseFailAlloc_65_; 
v_reuseFailAlloc_65_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_65_, 0, v___x_62_);
v___x_64_ = v_reuseFailAlloc_65_;
goto v_reusejp_63_;
}
v_reusejp_63_:
{
return v___x_64_;
}
}
}
}
}
else
{
lean_object* v_ks_94_; lean_object* v_vs_95_; lean_object* v___x_97_; uint8_t v_isShared_98_; uint8_t v_isSharedCheck_113_; 
v_ks_94_ = lean_ctor_get(v_x_43_, 0);
v_vs_95_ = lean_ctor_get(v_x_43_, 1);
v_isSharedCheck_113_ = !lean_is_exclusive(v_x_43_);
if (v_isSharedCheck_113_ == 0)
{
v___x_97_ = v_x_43_;
v_isShared_98_ = v_isSharedCheck_113_;
goto v_resetjp_96_;
}
else
{
lean_inc(v_vs_95_);
lean_inc(v_ks_94_);
lean_dec(v_x_43_);
v___x_97_ = lean_box(0);
v_isShared_98_ = v_isSharedCheck_113_;
goto v_resetjp_96_;
}
v_resetjp_96_:
{
lean_object* v___x_100_; 
if (v_isShared_98_ == 0)
{
v___x_100_ = v___x_97_;
goto v_reusejp_99_;
}
else
{
lean_object* v_reuseFailAlloc_112_; 
v_reuseFailAlloc_112_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_112_, 0, v_ks_94_);
lean_ctor_set(v_reuseFailAlloc_112_, 1, v_vs_95_);
v___x_100_ = v_reuseFailAlloc_112_;
goto v_reusejp_99_;
}
v_reusejp_99_:
{
lean_object* v_newNode_101_; size_t v___x_102_; uint8_t v___x_103_; 
v_newNode_101_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3_spec__5___redArg(v___x_100_, v_x_46_, v_x_47_);
v___x_102_ = ((size_t)7ULL);
v___x_103_ = lean_usize_dec_le(v___x_102_, v_x_45_);
if (v___x_103_ == 0)
{
lean_object* v___x_104_; lean_object* v___x_105_; uint8_t v___x_106_; 
v___x_104_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_101_);
v___x_105_ = lean_unsigned_to_nat(4u);
v___x_106_ = lean_nat_dec_lt(v___x_104_, v___x_105_);
lean_dec(v___x_104_);
if (v___x_106_ == 0)
{
lean_object* v_ks_107_; lean_object* v_vs_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; 
v_ks_107_ = lean_ctor_get(v_newNode_101_, 0);
lean_inc_ref(v_ks_107_);
v_vs_108_ = lean_ctor_get(v_newNode_101_, 1);
lean_inc_ref(v_vs_108_);
lean_dec_ref(v_newNode_101_);
v___x_109_ = lean_unsigned_to_nat(0u);
v___x_110_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3___redArg___closed__0);
v___x_111_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3_spec__6___redArg(v_x_45_, v_ks_107_, v_vs_108_, v___x_109_, v___x_110_);
lean_dec_ref(v_vs_108_);
lean_dec_ref(v_ks_107_);
return v___x_111_;
}
else
{
return v_newNode_101_;
}
}
else
{
return v_newNode_101_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_43_ = stack[0].m_obj;
size_t v_x_44_ = stack[1].m_num;
size_t v_x_45_ = stack[2].m_num;
lean_object* v_x_46_ = stack[3].m_obj;
lean_object* v_x_47_ = stack[4].m_obj;
lean_object* v_res_114_;
v_res_114_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3___redArg(v_x_43_, v_x_44_, v_x_45_, v_x_46_, v_x_47_);
stack->m_obj
 = v_res_114_;
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3_spec__6___redArg(size_t v_depth_115_, lean_object* v_keys_116_, lean_object* v_vals_117_, lean_object* v_i_118_, lean_object* v_entries_119_){
_start:
{
lean_object* v___x_120_; uint8_t v___x_121_; 
v___x_120_ = lean_array_get_size(v_keys_116_);
v___x_121_ = lean_nat_dec_lt(v_i_118_, v___x_120_);
if (v___x_121_ == 0)
{
lean_dec(v_i_118_);
return v_entries_119_;
}
else
{
lean_object* v_k_122_; lean_object* v_v_123_; uint64_t v___x_124_; size_t v_h_125_; size_t v___x_126_; lean_object* v___x_127_; size_t v___x_128_; size_t v___x_129_; size_t v___x_130_; size_t v_h_131_; lean_object* v___x_132_; lean_object* v___x_133_; 
v_k_122_ = lean_array_fget_borrowed(v_keys_116_, v_i_118_);
v_v_123_ = lean_array_fget_borrowed(v_vals_117_, v_i_118_);
v___x_124_ = l_Lean_instHashableMVarId_hash(v_k_122_);
v_h_125_ = lean_uint64_to_usize(v___x_124_);
v___x_126_ = ((size_t)5ULL);
v___x_127_ = lean_unsigned_to_nat(1u);
v___x_128_ = ((size_t)1ULL);
v___x_129_ = lean_usize_sub(v_depth_115_, v___x_128_);
v___x_130_ = lean_usize_mul(v___x_126_, v___x_129_);
v_h_131_ = lean_usize_shift_right(v_h_125_, v___x_130_);
v___x_132_ = lean_nat_add(v_i_118_, v___x_127_);
lean_dec(v_i_118_);
lean_inc(v_v_123_);
lean_inc(v_k_122_);
v___x_133_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3___redArg(v_entries_119_, v_h_131_, v_depth_115_, v_k_122_, v_v_123_);
v_i_118_ = v___x_132_;
v_entries_119_ = v___x_133_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_depth_115_ = stack[0].m_num;
lean_object* v_keys_116_ = stack[1].m_obj;
lean_object* v_vals_117_ = stack[2].m_obj;
lean_object* v_i_118_ = stack[3].m_obj;
lean_object* v_entries_119_ = stack[4].m_obj;
lean_object* v_res_135_;
v_res_135_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3_spec__6___redArg(v_depth_115_, v_keys_116_, v_vals_117_, v_i_118_, v_entries_119_);
stack->m_obj
 = v_res_135_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3_spec__6___redArg___boxed(lean_object* v_depth_136_, lean_object* v_keys_137_, lean_object* v_vals_138_, lean_object* v_i_139_, lean_object* v_entries_140_){
_start:
{
size_t v_depth_boxed_141_; lean_object* v_res_142_; 
v_depth_boxed_141_ = lean_unbox_usize(v_depth_136_);
lean_dec(v_depth_136_);
v_res_142_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3_spec__6___redArg(v_depth_boxed_141_, v_keys_137_, v_vals_138_, v_i_139_, v_entries_140_);
lean_dec_ref(v_vals_138_);
lean_dec_ref(v_keys_137_);
return v_res_142_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_x_143_, lean_object* v_x_144_, lean_object* v_x_145_, lean_object* v_x_146_, lean_object* v_x_147_){
_start:
{
size_t v_x_4236__boxed_148_; size_t v_x_4237__boxed_149_; lean_object* v_res_150_; 
v_x_4236__boxed_148_ = lean_unbox_usize(v_x_144_);
lean_dec(v_x_144_);
v_x_4237__boxed_149_ = lean_unbox_usize(v_x_145_);
lean_dec(v_x_145_);
v_res_150_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3___redArg(v_x_143_, v_x_4236__boxed_148_, v_x_4237__boxed_149_, v_x_146_, v_x_147_);
return v_res_150_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2___redArg(lean_object* v_x_151_, lean_object* v_x_152_, lean_object* v_x_153_){
_start:
{
uint64_t v___x_154_; size_t v___x_155_; size_t v___x_156_; lean_object* v___x_157_; 
v___x_154_ = l_Lean_instHashableMVarId_hash(v_x_152_);
v___x_155_ = lean_uint64_to_usize(v___x_154_);
v___x_156_ = ((size_t)1ULL);
v___x_157_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3___redArg(v_x_151_, v___x_155_, v___x_156_, v_x_152_, v_x_153_);
return v___x_157_;
}
}
lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1___redArg(lean_object* v_mvarId_158_, lean_object* v_val_159_, lean_object* v___y_160_){
_start:
{
lean_object* v___x_162_; lean_object* v_mctx_163_; lean_object* v_cache_164_; lean_object* v_zetaDeltaFVarIds_165_; lean_object* v_postponed_166_; lean_object* v_diag_167_; lean_object* v___x_169_; uint8_t v_isShared_170_; uint8_t v_isSharedCheck_197_; 
v___x_162_ = lean_st_ref_take(v___y_160_);
v_mctx_163_ = lean_ctor_get(v___x_162_, 0);
v_cache_164_ = lean_ctor_get(v___x_162_, 1);
v_zetaDeltaFVarIds_165_ = lean_ctor_get(v___x_162_, 2);
v_postponed_166_ = lean_ctor_get(v___x_162_, 3);
v_diag_167_ = lean_ctor_get(v___x_162_, 4);
v_isSharedCheck_197_ = !lean_is_exclusive(v___x_162_);
if (v_isSharedCheck_197_ == 0)
{
v___x_169_ = v___x_162_;
v_isShared_170_ = v_isSharedCheck_197_;
goto v_resetjp_168_;
}
else
{
lean_inc(v_diag_167_);
lean_inc(v_postponed_166_);
lean_inc(v_zetaDeltaFVarIds_165_);
lean_inc(v_cache_164_);
lean_inc(v_mctx_163_);
lean_dec(v___x_162_);
v___x_169_ = lean_box(0);
v_isShared_170_ = v_isSharedCheck_197_;
goto v_resetjp_168_;
}
v_resetjp_168_:
{
lean_object* v_depth_171_; lean_object* v_levelAssignDepth_172_; lean_object* v_lmvarCounter_173_; lean_object* v_mvarCounter_174_; lean_object* v_lDecls_175_; lean_object* v_decls_176_; lean_object* v_userNames_177_; lean_object* v_lAssignment_178_; lean_object* v_eAssignment_179_; lean_object* v_dAssignment_180_; lean_object* v_instanceTypedMVars_181_; lean_object* v_synthNormMemo_182_; lean_object* v___x_184_; uint8_t v_isShared_185_; uint8_t v_isSharedCheck_196_; 
v_depth_171_ = lean_ctor_get(v_mctx_163_, 0);
v_levelAssignDepth_172_ = lean_ctor_get(v_mctx_163_, 1);
v_lmvarCounter_173_ = lean_ctor_get(v_mctx_163_, 2);
v_mvarCounter_174_ = lean_ctor_get(v_mctx_163_, 3);
v_lDecls_175_ = lean_ctor_get(v_mctx_163_, 4);
v_decls_176_ = lean_ctor_get(v_mctx_163_, 5);
v_userNames_177_ = lean_ctor_get(v_mctx_163_, 6);
v_lAssignment_178_ = lean_ctor_get(v_mctx_163_, 7);
v_eAssignment_179_ = lean_ctor_get(v_mctx_163_, 8);
v_dAssignment_180_ = lean_ctor_get(v_mctx_163_, 9);
v_instanceTypedMVars_181_ = lean_ctor_get(v_mctx_163_, 10);
v_synthNormMemo_182_ = lean_ctor_get(v_mctx_163_, 11);
v_isSharedCheck_196_ = !lean_is_exclusive(v_mctx_163_);
if (v_isSharedCheck_196_ == 0)
{
v___x_184_ = v_mctx_163_;
v_isShared_185_ = v_isSharedCheck_196_;
goto v_resetjp_183_;
}
else
{
lean_inc(v_synthNormMemo_182_);
lean_inc(v_instanceTypedMVars_181_);
lean_inc(v_dAssignment_180_);
lean_inc(v_eAssignment_179_);
lean_inc(v_lAssignment_178_);
lean_inc(v_userNames_177_);
lean_inc(v_decls_176_);
lean_inc(v_lDecls_175_);
lean_inc(v_mvarCounter_174_);
lean_inc(v_lmvarCounter_173_);
lean_inc(v_levelAssignDepth_172_);
lean_inc(v_depth_171_);
lean_dec(v_mctx_163_);
v___x_184_ = lean_box(0);
v_isShared_185_ = v_isSharedCheck_196_;
goto v_resetjp_183_;
}
v_resetjp_183_:
{
lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_189_; 
v___x_186_ = lean_box(0);
v___x_187_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2___redArg(v_eAssignment_179_, v_mvarId_158_, v_val_159_);
if (v_isShared_185_ == 0)
{
lean_ctor_set(v___x_184_, 8, v___x_187_);
v___x_189_ = v___x_184_;
goto v_reusejp_188_;
}
else
{
lean_object* v_reuseFailAlloc_195_; 
v_reuseFailAlloc_195_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_195_, 0, v_depth_171_);
lean_ctor_set(v_reuseFailAlloc_195_, 1, v_levelAssignDepth_172_);
lean_ctor_set(v_reuseFailAlloc_195_, 2, v_lmvarCounter_173_);
lean_ctor_set(v_reuseFailAlloc_195_, 3, v_mvarCounter_174_);
lean_ctor_set(v_reuseFailAlloc_195_, 4, v_lDecls_175_);
lean_ctor_set(v_reuseFailAlloc_195_, 5, v_decls_176_);
lean_ctor_set(v_reuseFailAlloc_195_, 6, v_userNames_177_);
lean_ctor_set(v_reuseFailAlloc_195_, 7, v_lAssignment_178_);
lean_ctor_set(v_reuseFailAlloc_195_, 8, v___x_187_);
lean_ctor_set(v_reuseFailAlloc_195_, 9, v_dAssignment_180_);
lean_ctor_set(v_reuseFailAlloc_195_, 10, v_instanceTypedMVars_181_);
lean_ctor_set(v_reuseFailAlloc_195_, 11, v_synthNormMemo_182_);
v___x_189_ = v_reuseFailAlloc_195_;
goto v_reusejp_188_;
}
v_reusejp_188_:
{
lean_object* v___x_191_; 
if (v_isShared_170_ == 0)
{
lean_ctor_set(v___x_169_, 0, v___x_189_);
v___x_191_ = v___x_169_;
goto v_reusejp_190_;
}
else
{
lean_object* v_reuseFailAlloc_194_; 
v_reuseFailAlloc_194_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_194_, 0, v___x_189_);
lean_ctor_set(v_reuseFailAlloc_194_, 1, v_cache_164_);
lean_ctor_set(v_reuseFailAlloc_194_, 2, v_zetaDeltaFVarIds_165_);
lean_ctor_set(v_reuseFailAlloc_194_, 3, v_postponed_166_);
lean_ctor_set(v_reuseFailAlloc_194_, 4, v_diag_167_);
v___x_191_ = v_reuseFailAlloc_194_;
goto v_reusejp_190_;
}
v_reusejp_190_:
{
lean_object* v___x_192_; lean_object* v___x_193_; 
v___x_192_ = lean_st_ref_put(v___y_160_, v___x_191_);
v___x_193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_193_, 0, v___x_186_);
return v___x_193_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_158_ = stack[0].m_obj;
lean_object* v_val_159_ = stack[1].m_obj;
lean_object* v___y_160_ = stack[2].m_obj;
lean_object* v_res_198_;
v_res_198_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1___redArg(v_mvarId_158_, v_val_159_, v___y_160_);
stack->m_obj
 = v_res_198_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1___redArg___boxed(lean_object* v_mvarId_199_, lean_object* v_val_200_, lean_object* v___y_201_, lean_object* v___y_202_){
_start:
{
lean_object* v_res_203_; 
v_res_203_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1___redArg(v_mvarId_199_, v_val_200_, v___y_201_);
lean_dec(v___y_201_);
return v_res_203_;
}
}
lean_object* l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1(lean_object* v___y_234_, lean_object* v___y_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_, lean_object* v___y_241_){
_start:
{
lean_object* v_ref_243_; uint8_t v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; 
v_ref_243_ = lean_ctor_get(v___y_240_, 2);
v___x_244_ = 0;
v___x_245_ = l_Lean_SourceInfo_fromRef(v_ref_243_, v___x_244_);
v___x_246_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__3));
v___x_247_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__4));
lean_inc_n(v___x_245_, 9);
v___x_248_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_248_, 0, v___x_245_);
lean_ctor_set(v___x_248_, 1, v___x_246_);
v___x_249_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__7));
v___x_250_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__8));
v___x_251_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_251_, 0, v___x_245_);
lean_ctor_set(v___x_251_, 1, v___x_250_);
v___x_252_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__10));
v___x_253_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__12));
v___x_254_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__13));
v___x_255_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_255_, 0, v___x_245_);
lean_ctor_set(v___x_255_, 1, v___x_254_);
v___x_256_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__14));
v___x_257_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_257_, 0, v___x_245_);
lean_ctor_set(v___x_257_, 1, v___x_256_);
v___x_258_ = l_Lean_Syntax_node2(v___x_245_, v___x_253_, v___x_255_, v___x_257_);
v___x_259_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__15));
v___x_260_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_260_, 0, v___x_245_);
lean_ctor_set(v___x_260_, 1, v___x_259_);
lean_inc(v___x_258_);
v___x_261_ = l_Lean_Syntax_node3(v___x_245_, v___x_252_, v___x_258_, v___x_260_, v___x_258_);
v___x_262_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__16));
v___x_263_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_263_, 0, v___x_245_);
lean_ctor_set(v___x_263_, 1, v___x_262_);
v___x_264_ = l_Lean_Syntax_node3(v___x_245_, v___x_249_, v___x_251_, v___x_261_, v___x_263_);
v___x_265_ = l_Lean_Syntax_node2(v___x_245_, v___x_247_, v___x_248_, v___x_264_);
v___x_266_ = l_Lean_Elab_Tactic_evalTactic(v___x_265_, v___y_234_, v___y_235_, v___y_236_, v___y_237_, v___y_238_, v___y_239_, v___y_240_, v___y_241_);
return v___x_266_;
}
}
LEAN_EXPORT void l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_234_ = stack[0].m_obj;
lean_object* v___y_235_ = stack[1].m_obj;
lean_object* v___y_236_ = stack[2].m_obj;
lean_object* v___y_237_ = stack[3].m_obj;
lean_object* v___y_238_ = stack[4].m_obj;
lean_object* v___y_239_ = stack[5].m_obj;
lean_object* v___y_240_ = stack[6].m_obj;
lean_object* v___y_241_ = stack[7].m_obj;
lean_object* v_res_267_;
v_res_267_ = l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1(v___y_234_, v___y_235_, v___y_236_, v___y_237_, v___y_238_, v___y_239_, v___y_240_, v___y_241_);
stack->m_obj
 = v_res_267_;
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
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0_spec__0(lean_object* v_msgData_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_){
_start:
{
lean_object* v___x_284_; lean_object* v_env_285_; uint8_t v___x_286_; lean_object* v_env_287_; lean_object* v___x_288_; lean_object* v_toCold_289_; lean_object* v_mctx_290_; lean_object* v_lctx_291_; lean_object* v_options_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; 
v___x_284_ = lean_st_ref_get(v___y_282_);
v_env_285_ = lean_ctor_get(v___x_284_, 0);
lean_inc_ref(v_env_285_);
lean_dec(v___x_284_);
v___x_286_ = 0;
v_env_287_ = l_Lean_Environment_setRecordingDeps(v_env_285_, v___x_286_);
v___x_288_ = lean_st_ref_get(v___y_280_);
v_toCold_289_ = lean_ctor_get(v___y_281_, 0);
v_mctx_290_ = lean_ctor_get(v___x_288_, 0);
lean_inc_ref(v_mctx_290_);
lean_dec(v___x_288_);
v_lctx_291_ = lean_ctor_get(v___y_279_, 2);
v_options_292_ = lean_ctor_get(v_toCold_289_, 2);
lean_inc_ref(v_options_292_);
lean_inc_ref(v_lctx_291_);
v___x_293_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_293_, 0, v_env_287_);
lean_ctor_set(v___x_293_, 1, v_mctx_290_);
lean_ctor_set(v___x_293_, 2, v_lctx_291_);
lean_ctor_set(v___x_293_, 3, v_options_292_);
v___x_294_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_294_, 0, v___x_293_);
lean_ctor_set(v___x_294_, 1, v_msgData_278_);
v___x_295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_295_, 0, v___x_294_);
return v___x_295_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_278_ = stack[0].m_obj;
lean_object* v___y_279_ = stack[1].m_obj;
lean_object* v___y_280_ = stack[2].m_obj;
lean_object* v___y_281_ = stack[3].m_obj;
lean_object* v___y_282_ = stack[4].m_obj;
lean_object* v_res_296_;
v_res_296_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0_spec__0(v_msgData_278_, v___y_279_, v___y_280_, v___y_281_, v___y_282_);
stack->m_obj
 = v_res_296_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0_spec__0___boxed(lean_object* v_msgData_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_){
_start:
{
lean_object* v_res_303_; 
v_res_303_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0_spec__0(v_msgData_297_, v___y_298_, v___y_299_, v___y_300_, v___y_301_);
lean_dec(v___y_301_);
lean_dec_ref(v___y_300_);
lean_dec(v___y_299_);
lean_dec_ref(v___y_298_);
return v_res_303_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0___redArg(lean_object* v_msg_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_){
_start:
{
lean_object* v_ref_310_; lean_object* v___x_311_; lean_object* v_a_312_; lean_object* v___x_314_; uint8_t v_isShared_315_; uint8_t v_isSharedCheck_320_; 
v_ref_310_ = lean_ctor_get(v___y_307_, 2);
v___x_311_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0_spec__0(v_msg_304_, v___y_305_, v___y_306_, v___y_307_, v___y_308_);
v_a_312_ = lean_ctor_get(v___x_311_, 0);
v_isSharedCheck_320_ = !lean_is_exclusive(v___x_311_);
if (v_isSharedCheck_320_ == 0)
{
v___x_314_ = v___x_311_;
v_isShared_315_ = v_isSharedCheck_320_;
goto v_resetjp_313_;
}
else
{
lean_inc(v_a_312_);
lean_dec(v___x_311_);
v___x_314_ = lean_box(0);
v_isShared_315_ = v_isSharedCheck_320_;
goto v_resetjp_313_;
}
v_resetjp_313_:
{
lean_object* v___x_316_; lean_object* v___x_318_; 
lean_inc(v_ref_310_);
v___x_316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_316_, 0, v_ref_310_);
lean_ctor_set(v___x_316_, 1, v_a_312_);
if (v_isShared_315_ == 0)
{
lean_ctor_set_tag(v___x_314_, 1);
lean_ctor_set(v___x_314_, 0, v___x_316_);
v___x_318_ = v___x_314_;
goto v_reusejp_317_;
}
else
{
lean_object* v_reuseFailAlloc_319_; 
v_reuseFailAlloc_319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_319_, 0, v___x_316_);
v___x_318_ = v_reuseFailAlloc_319_;
goto v_reusejp_317_;
}
v_reusejp_317_:
{
return v___x_318_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_304_ = stack[0].m_obj;
lean_object* v___y_305_ = stack[1].m_obj;
lean_object* v___y_306_ = stack[2].m_obj;
lean_object* v___y_307_ = stack[3].m_obj;
lean_object* v___y_308_ = stack[4].m_obj;
lean_object* v_res_321_;
v_res_321_ = l_Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0___redArg(v_msg_304_, v___y_305_, v___y_306_, v___y_307_, v___y_308_);
stack->m_obj
 = v_res_321_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0___redArg___boxed(lean_object* v_msg_322_, lean_object* v___y_323_, lean_object* v___y_324_, lean_object* v___y_325_, lean_object* v___y_326_, lean_object* v___y_327_){
_start:
{
lean_object* v_res_328_; 
v_res_328_ = l_Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0___redArg(v_msg_322_, v___y_323_, v___y_324_, v___y_325_, v___y_326_);
lean_dec(v___y_326_);
lean_dec_ref(v___y_325_);
lean_dec(v___y_324_);
lean_dec_ref(v___y_323_);
return v_res_328_;
}
}
static lean_object* _init_l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___closed__1(void){
_start:
{
lean_object* v___x_330_; lean_object* v___x_331_; 
v___x_330_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___closed__0));
v___x_331_ = l_Lean_stringToMessageData(v___x_330_);
return v___x_331_;
}
}
lean_object* l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2(lean_object* v_x_347_, lean_object* v_x_348_, lean_object* v___y_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_){
_start:
{
if (lean_obj_tag(v_x_348_) == 0)
{
lean_object* v___x_354_; 
v___x_354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_354_, 0, v_x_347_);
return v___x_354_;
}
else
{
lean_object* v_head_355_; lean_object* v_tail_356_; lean_object* v___y_358_; lean_object* v___y_359_; lean_object* v___y_360_; lean_object* v___y_361_; lean_object* v___f_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; 
v_head_355_ = lean_ctor_get(v_x_348_, 0);
lean_inc(v_head_355_);
v_tail_356_ = lean_ctor_get(v_x_348_, 1);
lean_inc(v_tail_356_);
lean_dec_ref_known(v_x_348_, 2);
v___f_364_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___closed__3));
v___x_365_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_run___boxed), 9, 2);
lean_closure_set(v___x_365_, 0, v_x_347_);
lean_closure_set(v___x_365_, 1, v___f_364_);
v___x_366_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___closed__5));
v___x_367_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___closed__6));
v___x_368_ = l_Lean_Elab_Term_TermElabM_run___redArg(v___x_365_, v___x_366_, v___x_367_, v___y_349_, v___y_350_, v___y_351_, v___y_352_);
if (lean_obj_tag(v___x_368_) == 0)
{
lean_object* v_a_369_; lean_object* v_fst_370_; 
v_a_369_ = lean_ctor_get(v___x_368_, 0);
lean_inc(v_a_369_);
lean_dec_ref_known(v___x_368_, 1);
v_fst_370_ = lean_ctor_get(v_a_369_, 0);
lean_inc(v_fst_370_);
lean_dec(v_a_369_);
if (lean_obj_tag(v_fst_370_) == 1)
{
lean_object* v_tail_371_; 
v_tail_371_ = lean_ctor_get(v_fst_370_, 1);
lean_inc(v_tail_371_);
if (lean_obj_tag(v_tail_371_) == 1)
{
lean_object* v_tail_372_; 
v_tail_372_ = lean_ctor_get(v_tail_371_, 1);
if (lean_obj_tag(v_tail_372_) == 0)
{
lean_object* v_head_373_; lean_object* v_head_374_; lean_object* v___x_375_; 
v_head_373_ = lean_ctor_get(v_fst_370_, 0);
lean_inc(v_head_373_);
lean_dec_ref_known(v_fst_370_, 2);
v_head_374_ = lean_ctor_get(v_tail_371_, 0);
lean_inc(v_head_374_);
lean_dec_ref_known(v_tail_371_, 2);
v___x_375_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1___redArg(v_head_373_, v_head_355_, v___y_350_);
lean_dec_ref(v___x_375_);
v_x_347_ = v_head_374_;
v_x_348_ = v_tail_356_;
goto _start;
}
else
{
lean_dec_ref_known(v_tail_371_, 2);
lean_dec_ref_known(v_fst_370_, 2);
lean_dec(v_tail_356_);
lean_dec(v_head_355_);
v___y_358_ = v___y_349_;
v___y_359_ = v___y_350_;
v___y_360_ = v___y_351_;
v___y_361_ = v___y_352_;
goto v___jp_357_;
}
}
else
{
lean_dec(v_tail_371_);
lean_dec_ref_known(v_fst_370_, 2);
lean_dec(v_tail_356_);
lean_dec(v_head_355_);
v___y_358_ = v___y_349_;
v___y_359_ = v___y_350_;
v___y_360_ = v___y_351_;
v___y_361_ = v___y_352_;
goto v___jp_357_;
}
}
else
{
lean_dec(v_fst_370_);
lean_dec(v_tail_356_);
lean_dec(v_head_355_);
v___y_358_ = v___y_349_;
v___y_359_ = v___y_350_;
v___y_360_ = v___y_351_;
v___y_361_ = v___y_352_;
goto v___jp_357_;
}
}
else
{
lean_object* v_a_377_; lean_object* v___x_379_; uint8_t v_isShared_380_; uint8_t v_isSharedCheck_384_; 
lean_dec(v_tail_356_);
lean_dec(v_head_355_);
v_a_377_ = lean_ctor_get(v___x_368_, 0);
v_isSharedCheck_384_ = !lean_is_exclusive(v___x_368_);
if (v_isSharedCheck_384_ == 0)
{
v___x_379_ = v___x_368_;
v_isShared_380_ = v_isSharedCheck_384_;
goto v_resetjp_378_;
}
else
{
lean_inc(v_a_377_);
lean_dec(v___x_368_);
v___x_379_ = lean_box(0);
v_isShared_380_ = v_isSharedCheck_384_;
goto v_resetjp_378_;
}
v_resetjp_378_:
{
lean_object* v___x_382_; 
if (v_isShared_380_ == 0)
{
v___x_382_ = v___x_379_;
goto v_reusejp_381_;
}
else
{
lean_object* v_reuseFailAlloc_383_; 
v_reuseFailAlloc_383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_383_, 0, v_a_377_);
v___x_382_ = v_reuseFailAlloc_383_;
goto v_reusejp_381_;
}
v_reusejp_381_:
{
return v___x_382_;
}
}
}
v___jp_357_:
{
lean_object* v___x_362_; lean_object* v___x_363_; 
v___x_362_ = lean_obj_once(&l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___closed__1, &l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___closed__1_once, _init_l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___closed__1);
v___x_363_ = l_Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0___redArg(v___x_362_, v___y_358_, v___y_359_, v___y_360_, v___y_361_);
return v___x_363_;
}
}
}
}
LEAN_EXPORT void l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_347_ = stack[0].m_obj;
lean_object* v_x_348_ = stack[1].m_obj;
lean_object* v___y_349_ = stack[2].m_obj;
lean_object* v___y_350_ = stack[3].m_obj;
lean_object* v___y_351_ = stack[4].m_obj;
lean_object* v___y_352_ = stack[5].m_obj;
lean_object* v_res_385_;
v_res_385_ = l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2(v_x_347_, v_x_348_, v___y_349_, v___y_350_, v___y_351_, v___y_352_);
stack->m_obj
 = v_res_385_;
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___boxed(lean_object* v_x_386_, lean_object* v_x_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_){
_start:
{
lean_object* v_res_393_; 
v_res_393_ = l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2(v_x_386_, v_x_387_, v___y_388_, v___y_389_, v___y_390_, v___y_391_);
lean_dec(v___y_391_);
lean_dec_ref(v___y_390_);
lean_dec(v___y_389_);
lean_dec_ref(v___y_388_);
return v_res_393_;
}
}
lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi(lean_object* v_mvar_394_, lean_object* v_es_395_, lean_object* v_a_396_, lean_object* v_a_397_, lean_object* v_a_398_, lean_object* v_a_399_){
_start:
{
lean_object* v___x_401_; 
v___x_401_ = l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2(v_mvar_394_, v_es_395_, v_a_396_, v_a_397_, v_a_398_, v_a_399_);
return v___x_401_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvar_394_ = stack[0].m_obj;
lean_object* v_es_395_ = stack[1].m_obj;
lean_object* v_a_396_ = stack[2].m_obj;
lean_object* v_a_397_ = stack[3].m_obj;
lean_object* v_a_398_ = stack[4].m_obj;
lean_object* v_a_399_ = stack[5].m_obj;
lean_object* v_res_402_;
v_res_402_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi(v_mvar_394_, v_es_395_, v_a_396_, v_a_397_, v_a_398_, v_a_399_);
stack->m_obj
 = v_res_402_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi___boxed(lean_object* v_mvar_403_, lean_object* v_es_404_, lean_object* v_a_405_, lean_object* v_a_406_, lean_object* v_a_407_, lean_object* v_a_408_, lean_object* v_a_409_){
_start:
{
lean_object* v_res_410_; 
v_res_410_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi(v_mvar_403_, v_es_404_, v_a_405_, v_a_406_, v_a_407_, v_a_408_);
lean_dec(v_a_408_);
lean_dec_ref(v_a_407_);
lean_dec(v_a_406_);
lean_dec_ref(v_a_405_);
return v_res_410_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0(lean_object* v_00_u03b1_411_, lean_object* v_msg_412_, lean_object* v___y_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_){
_start:
{
lean_object* v___x_418_; 
v___x_418_ = l_Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0___redArg(v_msg_412_, v___y_413_, v___y_414_, v___y_415_, v___y_416_);
return v___x_418_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_412_ = stack[1].m_obj;
lean_object* v___y_413_ = stack[2].m_obj;
lean_object* v___y_414_ = stack[3].m_obj;
lean_object* v___y_415_ = stack[4].m_obj;
lean_object* v___y_416_ = stack[5].m_obj;
lean_object* v_res_419_;
v_res_419_ = l_Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0(lean_box(0), v_msg_412_, v___y_413_, v___y_414_, v___y_415_, v___y_416_);
stack->m_obj
 = v_res_419_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0___boxed(lean_object* v_00_u03b1_420_, lean_object* v_msg_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_){
_start:
{
lean_object* v_res_427_; 
v_res_427_ = l_Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0(v_00_u03b1_420_, v_msg_421_, v___y_422_, v___y_423_, v___y_424_, v___y_425_);
lean_dec(v___y_425_);
lean_dec_ref(v___y_424_);
lean_dec(v___y_423_);
lean_dec_ref(v___y_422_);
return v_res_427_;
}
}
lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1(lean_object* v_mvarId_428_, lean_object* v_val_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_){
_start:
{
lean_object* v___x_435_; 
v___x_435_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1___redArg(v_mvarId_428_, v_val_429_, v___y_431_);
return v___x_435_;
}
}
LEAN_EXPORT void l_Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_428_ = stack[0].m_obj;
lean_object* v_val_429_ = stack[1].m_obj;
lean_object* v___y_430_ = stack[2].m_obj;
lean_object* v___y_431_ = stack[3].m_obj;
lean_object* v___y_432_ = stack[4].m_obj;
lean_object* v___y_433_ = stack[5].m_obj;
lean_object* v_res_436_;
v_res_436_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1(v_mvarId_428_, v_val_429_, v___y_430_, v___y_431_, v___y_432_, v___y_433_);
stack->m_obj
 = v_res_436_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1___boxed(lean_object* v_mvarId_437_, lean_object* v_val_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_){
_start:
{
lean_object* v_res_444_; 
v_res_444_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1(v_mvarId_437_, v_val_438_, v___y_439_, v___y_440_, v___y_441_, v___y_442_);
lean_dec(v___y_442_);
lean_dec_ref(v___y_441_);
lean_dec(v___y_440_);
lean_dec_ref(v___y_439_);
return v_res_444_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2(lean_object* v_00_u03b2_445_, lean_object* v_x_446_, lean_object* v_x_447_, lean_object* v_x_448_){
_start:
{
lean_object* v___x_449_; 
v___x_449_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2___redArg(v_x_446_, v_x_447_, v_x_448_);
return v___x_449_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_450_, lean_object* v_x_451_, size_t v_x_452_, size_t v_x_453_, lean_object* v_x_454_, lean_object* v_x_455_){
_start:
{
lean_object* v___x_456_; 
v___x_456_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3___redArg(v_x_451_, v_x_452_, v_x_453_, v_x_454_, v_x_455_);
return v___x_456_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_451_ = stack[1].m_obj;
size_t v_x_452_ = stack[2].m_num;
size_t v_x_453_ = stack[3].m_num;
lean_object* v_x_454_ = stack[4].m_obj;
lean_object* v_x_455_ = stack[5].m_obj;
lean_object* v_res_457_;
v_res_457_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3(lean_box(0), v_x_451_, v_x_452_, v_x_453_, v_x_454_, v_x_455_);
stack->m_obj
 = v_res_457_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03b2_458_, lean_object* v_x_459_, lean_object* v_x_460_, lean_object* v_x_461_, lean_object* v_x_462_, lean_object* v_x_463_){
_start:
{
size_t v_x_5207__boxed_464_; size_t v_x_5208__boxed_465_; lean_object* v_res_466_; 
v_x_5207__boxed_464_ = lean_unbox_usize(v_x_460_);
lean_dec(v_x_460_);
v_x_5208__boxed_465_ = lean_unbox_usize(v_x_461_);
lean_dec(v_x_461_);
v_res_466_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3(v_00_u03b2_458_, v_x_459_, v_x_5207__boxed_464_, v_x_5208__boxed_465_, v_x_462_, v_x_463_);
return v_res_466_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3_spec__5(lean_object* v_00_u03b2_467_, lean_object* v_n_468_, lean_object* v_k_469_, lean_object* v_v_470_){
_start:
{
lean_object* v___x_471_; 
v___x_471_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3_spec__5___redArg(v_n_468_, v_k_469_, v_v_470_);
return v___x_471_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3_spec__6(lean_object* v_00_u03b2_472_, size_t v_depth_473_, lean_object* v_keys_474_, lean_object* v_vals_475_, lean_object* v_heq_476_, lean_object* v_i_477_, lean_object* v_entries_478_){
_start:
{
lean_object* v___x_479_; 
v___x_479_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3_spec__6___redArg(v_depth_473_, v_keys_474_, v_vals_475_, v_i_477_, v_entries_478_);
return v___x_479_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3_spec__6_0interp(lean_interpreter_value* stack)
{
size_t v_depth_473_ = stack[1].m_num;
lean_object* v_keys_474_ = stack[2].m_obj;
lean_object* v_vals_475_ = stack[3].m_obj;
lean_object* v_i_477_ = stack[5].m_obj;
lean_object* v_entries_478_ = stack[6].m_obj;
lean_object* v_res_480_;
v_res_480_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3_spec__6(lean_box(0), v_depth_473_, v_keys_474_, v_vals_475_, lean_box(0), v_i_477_, v_entries_478_);
stack->m_obj
 = v_res_480_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3_spec__6___boxed(lean_object* v_00_u03b2_481_, lean_object* v_depth_482_, lean_object* v_keys_483_, lean_object* v_vals_484_, lean_object* v_heq_485_, lean_object* v_i_486_, lean_object* v_entries_487_){
_start:
{
size_t v_depth_boxed_488_; lean_object* v_res_489_; 
v_depth_boxed_488_ = lean_unbox_usize(v_depth_482_);
lean_dec(v_depth_482_);
v_res_489_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3_spec__6(v_00_u03b2_481_, v_depth_boxed_488_, v_keys_483_, v_vals_484_, v_heq_485_, v_i_486_, v_entries_487_);
lean_dec_ref(v_vals_484_);
lean_dec_ref(v_keys_483_);
return v_res_489_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3_spec__5_spec__6(lean_object* v_00_u03b2_490_, lean_object* v_x_491_, lean_object* v_x_492_, lean_object* v_x_493_, lean_object* v_x_494_){
_start:
{
lean_object* v___x_495_; 
v___x_495_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3_spec__5_spec__6___redArg(v_x_491_, v_x_492_, v_x_493_, v_x_494_);
return v___x_495_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor_spec__0___redArg(lean_object* v_mvarId_496_, lean_object* v_x_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_){
_start:
{
lean_object* v___x_503_; 
v___x_503_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_496_, v_x_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_);
if (lean_obj_tag(v___x_503_) == 0)
{
lean_object* v_a_504_; lean_object* v___x_506_; uint8_t v_isShared_507_; uint8_t v_isSharedCheck_511_; 
v_a_504_ = lean_ctor_get(v___x_503_, 0);
v_isSharedCheck_511_ = !lean_is_exclusive(v___x_503_);
if (v_isSharedCheck_511_ == 0)
{
v___x_506_ = v___x_503_;
v_isShared_507_ = v_isSharedCheck_511_;
goto v_resetjp_505_;
}
else
{
lean_inc(v_a_504_);
lean_dec(v___x_503_);
v___x_506_ = lean_box(0);
v_isShared_507_ = v_isSharedCheck_511_;
goto v_resetjp_505_;
}
v_resetjp_505_:
{
lean_object* v___x_509_; 
if (v_isShared_507_ == 0)
{
v___x_509_ = v___x_506_;
goto v_reusejp_508_;
}
else
{
lean_object* v_reuseFailAlloc_510_; 
v_reuseFailAlloc_510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_510_, 0, v_a_504_);
v___x_509_ = v_reuseFailAlloc_510_;
goto v_reusejp_508_;
}
v_reusejp_508_:
{
return v___x_509_;
}
}
}
else
{
lean_object* v_a_512_; lean_object* v___x_514_; uint8_t v_isShared_515_; uint8_t v_isSharedCheck_519_; 
v_a_512_ = lean_ctor_get(v___x_503_, 0);
v_isSharedCheck_519_ = !lean_is_exclusive(v___x_503_);
if (v_isSharedCheck_519_ == 0)
{
v___x_514_ = v___x_503_;
v_isShared_515_ = v_isSharedCheck_519_;
goto v_resetjp_513_;
}
else
{
lean_inc(v_a_512_);
lean_dec(v___x_503_);
v___x_514_ = lean_box(0);
v_isShared_515_ = v_isSharedCheck_519_;
goto v_resetjp_513_;
}
v_resetjp_513_:
{
lean_object* v___x_517_; 
if (v_isShared_515_ == 0)
{
v___x_517_ = v___x_514_;
goto v_reusejp_516_;
}
else
{
lean_object* v_reuseFailAlloc_518_; 
v_reuseFailAlloc_518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_518_, 0, v_a_512_);
v___x_517_ = v_reuseFailAlloc_518_;
goto v_reusejp_516_;
}
v_reusejp_516_:
{
return v___x_517_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_496_ = stack[0].m_obj;
lean_object* v_x_497_ = stack[1].m_obj;
lean_object* v___y_498_ = stack[2].m_obj;
lean_object* v___y_499_ = stack[3].m_obj;
lean_object* v___y_500_ = stack[4].m_obj;
lean_object* v___y_501_ = stack[5].m_obj;
lean_object* v_res_520_;
v_res_520_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor_spec__0___redArg(v_mvarId_496_, v_x_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_);
stack->m_obj
 = v_res_520_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor_spec__0___redArg___boxed(lean_object* v_mvarId_521_, lean_object* v_x_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_){
_start:
{
lean_object* v_res_528_; 
v_res_528_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor_spec__0___redArg(v_mvarId_521_, v_x_522_, v___y_523_, v___y_524_, v___y_525_, v___y_526_);
lean_dec(v___y_526_);
lean_dec_ref(v___y_525_);
lean_dec(v___y_524_);
lean_dec_ref(v___y_523_);
return v_res_528_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor_spec__0(lean_object* v_00_u03b1_529_, lean_object* v_mvarId_530_, lean_object* v_x_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_){
_start:
{
lean_object* v___x_537_; 
v___x_537_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor_spec__0___redArg(v_mvarId_530_, v_x_531_, v___y_532_, v___y_533_, v___y_534_, v___y_535_);
return v___x_537_;
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_530_ = stack[1].m_obj;
lean_object* v_x_531_ = stack[2].m_obj;
lean_object* v___y_532_ = stack[3].m_obj;
lean_object* v___y_533_ = stack[4].m_obj;
lean_object* v___y_534_ = stack[5].m_obj;
lean_object* v___y_535_ = stack[6].m_obj;
lean_object* v_res_538_;
v_res_538_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor_spec__0(lean_box(0), v_mvarId_530_, v_x_531_, v___y_532_, v___y_533_, v___y_534_, v___y_535_);
stack->m_obj
 = v_res_538_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor_spec__0___boxed(lean_object* v_00_u03b1_539_, lean_object* v_mvarId_540_, lean_object* v_x_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_){
_start:
{
lean_object* v_res_547_; 
v_res_547_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor_spec__0(v_00_u03b1_539_, v_mvarId_540_, v_x_541_, v___y_542_, v___y_543_, v___y_544_, v___y_545_);
lean_dec(v___y_545_);
lean_dec_ref(v___y_544_);
lean_dec(v___y_543_);
lean_dec_ref(v___y_542_);
return v_res_547_;
}
}
static lean_object* _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0___closed__2(void){
_start:
{
lean_object* v___x_551_; lean_object* v___x_552_; 
v___x_551_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0___closed__1));
v___x_552_ = l_Lean_MessageData_ofFormat(v___x_551_);
return v___x_552_;
}
}
static lean_object* _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0___closed__3(void){
_start:
{
lean_object* v___x_553_; lean_object* v___x_554_; 
v___x_553_ = lean_obj_once(&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0___closed__2, &l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0___closed__2_once, _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0___closed__2);
v___x_554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_554_, 0, v___x_553_);
return v___x_554_;
}
}
lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0(lean_object* v_name_559_, lean_object* v_goal_560_, lean_object* v_idx_561_, lean_object* v_expected_x3f_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_){
_start:
{
lean_object* v___x_571_; 
lean_inc(v_name_559_);
lean_inc(v_goal_560_);
v___x_571_ = l_Lean_MVarId_checkNotAssigned(v_goal_560_, v_name_559_, v___y_563_, v___y_564_, v___y_565_, v___y_566_);
if (lean_obj_tag(v___x_571_) == 0)
{
lean_object* v___x_572_; 
lean_dec_ref_known(v___x_571_, 1);
lean_inc(v_goal_560_);
v___x_572_ = l_Lean_MVarId_getType_x27(v_goal_560_, v___y_563_, v___y_564_, v___y_565_, v___y_566_);
if (lean_obj_tag(v___x_572_) == 0)
{
lean_object* v_a_573_; lean_object* v___x_574_; 
v_a_573_ = lean_ctor_get(v___x_572_, 0);
lean_inc(v_a_573_);
lean_dec_ref_known(v___x_572_, 1);
v___x_574_ = l_Lean_Expr_getAppFn(v_a_573_);
lean_dec(v_a_573_);
if (lean_obj_tag(v___x_574_) == 4)
{
lean_object* v_declName_575_; lean_object* v_us_576_; lean_object* v___x_577_; lean_object* v_env_578_; uint8_t v___x_579_; lean_object* v___x_580_; 
v_declName_575_ = lean_ctor_get(v___x_574_, 0);
lean_inc(v_declName_575_);
v_us_576_ = lean_ctor_get(v___x_574_, 1);
lean_inc(v_us_576_);
lean_dec_ref_known(v___x_574_, 2);
v___x_577_ = lean_st_ref_get(v___y_566_);
v_env_578_ = lean_ctor_get(v___x_577_, 0);
lean_inc_ref(v_env_578_);
lean_dec(v___x_577_);
v___x_579_ = 0;
v___x_580_ = l_Lean_Environment_find_x3f(v_env_578_, v_declName_575_, v___x_579_);
if (lean_obj_tag(v___x_580_) == 0)
{
lean_dec(v_us_576_);
lean_dec(v_expected_x3f_562_);
lean_dec(v_idx_561_);
goto v___jp_568_;
}
else
{
lean_object* v_val_581_; lean_object* v___x_583_; uint8_t v_isShared_584_; uint8_t v_isSharedCheck_651_; 
v_val_581_ = lean_ctor_get(v___x_580_, 0);
v_isSharedCheck_651_ = !lean_is_exclusive(v___x_580_);
if (v_isSharedCheck_651_ == 0)
{
v___x_583_ = v___x_580_;
v_isShared_584_ = v_isSharedCheck_651_;
goto v_resetjp_582_;
}
else
{
lean_inc(v_val_581_);
lean_dec(v___x_580_);
v___x_583_ = lean_box(0);
v_isShared_584_ = v_isSharedCheck_651_;
goto v_resetjp_582_;
}
v_resetjp_582_:
{
if (lean_obj_tag(v_val_581_) == 5)
{
lean_object* v_val_585_; lean_object* v___x_587_; uint8_t v_isShared_588_; uint8_t v_isSharedCheck_650_; 
v_val_585_ = lean_ctor_get(v_val_581_, 0);
v_isSharedCheck_650_ = !lean_is_exclusive(v_val_581_);
if (v_isSharedCheck_650_ == 0)
{
v___x_587_ = v_val_581_;
v_isShared_588_ = v_isSharedCheck_650_;
goto v_resetjp_586_;
}
else
{
lean_inc(v_val_585_);
lean_dec(v_val_581_);
v___x_587_ = lean_box(0);
v_isShared_588_ = v_isSharedCheck_650_;
goto v_resetjp_586_;
}
v_resetjp_586_:
{
lean_object* v___y_590_; lean_object* v___y_591_; lean_object* v___y_592_; lean_object* v___y_593_; 
if (lean_obj_tag(v_expected_x3f_562_) == 1)
{
lean_object* v_val_620_; lean_object* v___x_622_; uint8_t v_isShared_623_; uint8_t v_isSharedCheck_649_; 
v_val_620_ = lean_ctor_get(v_expected_x3f_562_, 0);
v_isSharedCheck_649_ = !lean_is_exclusive(v_expected_x3f_562_);
if (v_isSharedCheck_649_ == 0)
{
v___x_622_ = v_expected_x3f_562_;
v_isShared_623_ = v_isSharedCheck_649_;
goto v_resetjp_621_;
}
else
{
lean_inc(v_val_620_);
lean_dec(v_expected_x3f_562_);
v___x_622_ = lean_box(0);
v_isShared_623_ = v_isSharedCheck_649_;
goto v_resetjp_621_;
}
v_resetjp_621_:
{
lean_object* v_ctors_624_; lean_object* v___x_625_; uint8_t v___x_626_; 
v_ctors_624_ = lean_ctor_get(v_val_585_, 4);
v___x_625_ = l_List_lengthTR___redArg(v_ctors_624_);
v___x_626_ = lean_nat_dec_eq(v___x_625_, v_val_620_);
lean_dec(v___x_625_);
if (v___x_626_ == 0)
{
uint8_t v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_638_; 
v___x_627_ = 1;
lean_inc(v_name_559_);
v___x_628_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_559_, v___x_627_);
v___x_629_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0___closed__7));
v___x_630_ = lean_string_append(v___x_628_, v___x_629_);
v___x_631_ = l_Nat_reprFast(v_val_620_);
v___x_632_ = lean_string_append(v___x_630_, v___x_631_);
lean_dec_ref(v___x_631_);
v___x_633_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0___closed__6));
v___x_634_ = lean_string_append(v___x_632_, v___x_633_);
v___x_635_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_635_, 0, v___x_634_);
v___x_636_ = l_Lean_MessageData_ofFormat(v___x_635_);
if (v_isShared_623_ == 0)
{
lean_ctor_set(v___x_622_, 0, v___x_636_);
v___x_638_ = v___x_622_;
goto v_reusejp_637_;
}
else
{
lean_object* v_reuseFailAlloc_648_; 
v_reuseFailAlloc_648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_648_, 0, v___x_636_);
v___x_638_ = v_reuseFailAlloc_648_;
goto v_reusejp_637_;
}
v_reusejp_637_:
{
lean_object* v___x_639_; 
lean_inc(v_goal_560_);
lean_inc(v_name_559_);
v___x_639_ = l_Lean_Meta_throwTacticEx___redArg(v_name_559_, v_goal_560_, v___x_638_, v___y_563_, v___y_564_, v___y_565_, v___y_566_);
if (lean_obj_tag(v___x_639_) == 0)
{
lean_dec_ref_known(v___x_639_, 1);
v___y_590_ = v___y_563_;
v___y_591_ = v___y_564_;
v___y_592_ = v___y_565_;
v___y_593_ = v___y_566_;
goto v___jp_589_;
}
else
{
lean_object* v_a_640_; lean_object* v___x_642_; uint8_t v_isShared_643_; uint8_t v_isSharedCheck_647_; 
lean_del_object(v___x_587_);
lean_dec_ref(v_val_585_);
lean_del_object(v___x_583_);
lean_dec(v_us_576_);
lean_dec(v_idx_561_);
lean_dec(v_goal_560_);
lean_dec(v_name_559_);
v_a_640_ = lean_ctor_get(v___x_639_, 0);
v_isSharedCheck_647_ = !lean_is_exclusive(v___x_639_);
if (v_isSharedCheck_647_ == 0)
{
v___x_642_ = v___x_639_;
v_isShared_643_ = v_isSharedCheck_647_;
goto v_resetjp_641_;
}
else
{
lean_inc(v_a_640_);
lean_dec(v___x_639_);
v___x_642_ = lean_box(0);
v_isShared_643_ = v_isSharedCheck_647_;
goto v_resetjp_641_;
}
v_resetjp_641_:
{
lean_object* v___x_645_; 
if (v_isShared_643_ == 0)
{
v___x_645_ = v___x_642_;
goto v_reusejp_644_;
}
else
{
lean_object* v_reuseFailAlloc_646_; 
v_reuseFailAlloc_646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_646_, 0, v_a_640_);
v___x_645_ = v_reuseFailAlloc_646_;
goto v_reusejp_644_;
}
v_reusejp_644_:
{
return v___x_645_;
}
}
}
}
}
else
{
lean_del_object(v___x_622_);
lean_dec(v_val_620_);
v___y_590_ = v___y_563_;
v___y_591_ = v___y_564_;
v___y_592_ = v___y_565_;
v___y_593_ = v___y_566_;
goto v___jp_589_;
}
}
}
else
{
lean_dec(v_expected_x3f_562_);
v___y_590_ = v___y_563_;
v___y_591_ = v___y_564_;
v___y_592_ = v___y_565_;
v___y_593_ = v___y_566_;
goto v___jp_589_;
}
v___jp_589_:
{
lean_object* v_ctors_594_; lean_object* v___x_595_; uint8_t v___x_596_; 
v_ctors_594_ = lean_ctor_get(v_val_585_, 4);
lean_inc(v_ctors_594_);
lean_dec_ref(v_val_585_);
v___x_595_ = l_List_lengthTR___redArg(v_ctors_594_);
v___x_596_ = lean_nat_dec_lt(v_idx_561_, v___x_595_);
if (v___x_596_ == 0)
{
lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_607_; 
lean_dec(v_ctors_594_);
lean_dec(v_us_576_);
v___x_597_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0___closed__4));
v___x_598_ = l_Nat_reprFast(v_idx_561_);
v___x_599_ = lean_string_append(v___x_597_, v___x_598_);
lean_dec_ref(v___x_598_);
v___x_600_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0___closed__5));
v___x_601_ = lean_string_append(v___x_599_, v___x_600_);
v___x_602_ = l_Nat_reprFast(v___x_595_);
v___x_603_ = lean_string_append(v___x_601_, v___x_602_);
lean_dec_ref(v___x_602_);
v___x_604_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0___closed__6));
v___x_605_ = lean_string_append(v___x_603_, v___x_604_);
if (v_isShared_588_ == 0)
{
lean_ctor_set_tag(v___x_587_, 3);
lean_ctor_set(v___x_587_, 0, v___x_605_);
v___x_607_ = v___x_587_;
goto v_reusejp_606_;
}
else
{
lean_object* v_reuseFailAlloc_613_; 
v_reuseFailAlloc_613_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_613_, 0, v___x_605_);
v___x_607_ = v_reuseFailAlloc_613_;
goto v_reusejp_606_;
}
v_reusejp_606_:
{
lean_object* v___x_608_; lean_object* v___x_610_; 
v___x_608_ = l_Lean_MessageData_ofFormat(v___x_607_);
if (v_isShared_584_ == 0)
{
lean_ctor_set(v___x_583_, 0, v___x_608_);
v___x_610_ = v___x_583_;
goto v_reusejp_609_;
}
else
{
lean_object* v_reuseFailAlloc_612_; 
v_reuseFailAlloc_612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_612_, 0, v___x_608_);
v___x_610_ = v_reuseFailAlloc_612_;
goto v_reusejp_609_;
}
v_reusejp_609_:
{
lean_object* v___x_611_; 
v___x_611_ = l_Lean_Meta_throwTacticEx___redArg(v_name_559_, v_goal_560_, v___x_610_, v___y_590_, v___y_591_, v___y_592_, v___y_593_);
return v___x_611_;
}
}
}
else
{
lean_object* v___x_614_; lean_object* v___x_615_; uint8_t v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; 
lean_dec(v___x_595_);
lean_del_object(v___x_587_);
lean_del_object(v___x_583_);
lean_dec(v_name_559_);
v___x_614_ = l_List_get___redArg(v_ctors_594_, v_idx_561_);
lean_dec(v_ctors_594_);
v___x_615_ = l_Lean_mkConst(v___x_614_, v_us_576_);
v___x_616_ = 0;
v___x_617_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_617_, 0, v___x_616_);
lean_ctor_set_uint8(v___x_617_, 1, v___x_596_);
lean_ctor_set_uint8(v___x_617_, 2, v___x_579_);
lean_ctor_set_uint8(v___x_617_, 3, v___x_596_);
v___x_618_ = lean_box(0);
v___x_619_ = l_Lean_MVarId_apply(v_goal_560_, v___x_615_, v___x_617_, v___x_618_, v___y_590_, v___y_591_, v___y_592_, v___y_593_);
return v___x_619_;
}
}
}
}
else
{
lean_del_object(v___x_583_);
lean_dec(v_val_581_);
lean_dec(v_us_576_);
lean_dec(v_expected_x3f_562_);
lean_dec(v_idx_561_);
goto v___jp_568_;
}
}
}
}
else
{
lean_dec_ref(v___x_574_);
lean_dec(v_expected_x3f_562_);
lean_dec(v_idx_561_);
goto v___jp_568_;
}
}
else
{
lean_object* v_a_652_; lean_object* v___x_654_; uint8_t v_isShared_655_; uint8_t v_isSharedCheck_659_; 
lean_dec(v_expected_x3f_562_);
lean_dec(v_idx_561_);
lean_dec(v_goal_560_);
lean_dec(v_name_559_);
v_a_652_ = lean_ctor_get(v___x_572_, 0);
v_isSharedCheck_659_ = !lean_is_exclusive(v___x_572_);
if (v_isSharedCheck_659_ == 0)
{
v___x_654_ = v___x_572_;
v_isShared_655_ = v_isSharedCheck_659_;
goto v_resetjp_653_;
}
else
{
lean_inc(v_a_652_);
lean_dec(v___x_572_);
v___x_654_ = lean_box(0);
v_isShared_655_ = v_isSharedCheck_659_;
goto v_resetjp_653_;
}
v_resetjp_653_:
{
lean_object* v___x_657_; 
if (v_isShared_655_ == 0)
{
v___x_657_ = v___x_654_;
goto v_reusejp_656_;
}
else
{
lean_object* v_reuseFailAlloc_658_; 
v_reuseFailAlloc_658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_658_, 0, v_a_652_);
v___x_657_ = v_reuseFailAlloc_658_;
goto v_reusejp_656_;
}
v_reusejp_656_:
{
return v___x_657_;
}
}
}
}
else
{
lean_object* v_a_660_; lean_object* v___x_662_; uint8_t v_isShared_663_; uint8_t v_isSharedCheck_667_; 
lean_dec(v_expected_x3f_562_);
lean_dec(v_idx_561_);
lean_dec(v_goal_560_);
lean_dec(v_name_559_);
v_a_660_ = lean_ctor_get(v___x_571_, 0);
v_isSharedCheck_667_ = !lean_is_exclusive(v___x_571_);
if (v_isSharedCheck_667_ == 0)
{
v___x_662_ = v___x_571_;
v_isShared_663_ = v_isSharedCheck_667_;
goto v_resetjp_661_;
}
else
{
lean_inc(v_a_660_);
lean_dec(v___x_571_);
v___x_662_ = lean_box(0);
v_isShared_663_ = v_isSharedCheck_667_;
goto v_resetjp_661_;
}
v_resetjp_661_:
{
lean_object* v___x_665_; 
if (v_isShared_663_ == 0)
{
v___x_665_ = v___x_662_;
goto v_reusejp_664_;
}
else
{
lean_object* v_reuseFailAlloc_666_; 
v_reuseFailAlloc_666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_666_, 0, v_a_660_);
v___x_665_ = v_reuseFailAlloc_666_;
goto v_reusejp_664_;
}
v_reusejp_664_:
{
return v___x_665_;
}
}
}
v___jp_568_:
{
lean_object* v___x_569_; lean_object* v___x_570_; 
v___x_569_ = lean_obj_once(&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0___closed__3, &l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0___closed__3_once, _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0___closed__3);
v___x_570_ = l_Lean_Meta_throwTacticEx___redArg(v_name_559_, v_goal_560_, v___x_569_, v___y_563_, v___y_564_, v___y_565_, v___y_566_);
return v___x_570_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_559_ = stack[0].m_obj;
lean_object* v_goal_560_ = stack[1].m_obj;
lean_object* v_idx_561_ = stack[2].m_obj;
lean_object* v_expected_x3f_562_ = stack[3].m_obj;
lean_object* v___y_563_ = stack[4].m_obj;
lean_object* v___y_564_ = stack[5].m_obj;
lean_object* v___y_565_ = stack[6].m_obj;
lean_object* v___y_566_ = stack[7].m_obj;
lean_object* v_res_668_;
v_res_668_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0(v_name_559_, v_goal_560_, v_idx_561_, v_expected_x3f_562_, v___y_563_, v___y_564_, v___y_565_, v___y_566_);
stack->m_obj
 = v_res_668_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0___boxed(lean_object* v_name_669_, lean_object* v_goal_670_, lean_object* v_idx_671_, lean_object* v_expected_x3f_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_){
_start:
{
lean_object* v_res_678_; 
v_res_678_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0(v_name_669_, v_goal_670_, v_idx_671_, v_expected_x3f_672_, v___y_673_, v___y_674_, v___y_675_, v___y_676_);
lean_dec(v___y_676_);
lean_dec_ref(v___y_675_);
lean_dec(v___y_674_);
lean_dec_ref(v___y_673_);
return v_res_678_;
}
}
lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor(lean_object* v_name_679_, lean_object* v_idx_680_, lean_object* v_expected_x3f_681_, lean_object* v_goal_682_, lean_object* v_a_683_, lean_object* v_a_684_, lean_object* v_a_685_, lean_object* v_a_686_){
_start:
{
lean_object* v___f_688_; lean_object* v___x_689_; 
lean_inc(v_goal_682_);
v___f_688_ = lean_alloc_closure((void*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0___boxed), 9, 4);
lean_closure_set(v___f_688_, 0, v_name_679_);
lean_closure_set(v___f_688_, 1, v_goal_682_);
lean_closure_set(v___f_688_, 2, v_idx_680_);
lean_closure_set(v___f_688_, 3, v_expected_x3f_681_);
v___x_689_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor_spec__0___redArg(v_goal_682_, v___f_688_, v_a_683_, v_a_684_, v_a_685_, v_a_686_);
return v___x_689_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_679_ = stack[0].m_obj;
lean_object* v_idx_680_ = stack[1].m_obj;
lean_object* v_expected_x3f_681_ = stack[2].m_obj;
lean_object* v_goal_682_ = stack[3].m_obj;
lean_object* v_a_683_ = stack[4].m_obj;
lean_object* v_a_684_ = stack[5].m_obj;
lean_object* v_a_685_ = stack[6].m_obj;
lean_object* v_a_686_ = stack[7].m_obj;
lean_object* v_res_690_;
v_res_690_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor(v_name_679_, v_idx_680_, v_expected_x3f_681_, v_goal_682_, v_a_683_, v_a_684_, v_a_685_, v_a_686_);
stack->m_obj
 = v_res_690_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___boxed(lean_object* v_name_691_, lean_object* v_idx_692_, lean_object* v_expected_x3f_693_, lean_object* v_goal_694_, lean_object* v_a_695_, lean_object* v_a_696_, lean_object* v_a_697_, lean_object* v_a_698_, lean_object* v_a_699_){
_start:
{
lean_object* v_res_700_; 
v_res_700_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor(v_name_691_, v_idx_692_, v_expected_x3f_693_, v_goal_694_, v_a_695_, v_a_696_, v_a_697_, v_a_698_);
lean_dec(v_a_698_);
lean_dec_ref(v_a_697_);
lean_dec(v_a_696_);
lean_dec_ref(v_a_695_);
return v_res_700_;
}
}
static lean_object* _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__1(void){
_start:
{
lean_object* v___x_702_; lean_object* v___x_703_; 
v___x_702_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__0));
v___x_703_ = l_Lean_stringToMessageData(v___x_702_);
return v___x_703_;
}
}
static lean_object* _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__8(void){
_start:
{
lean_object* v___x_713_; lean_object* v___x_714_; 
v___x_713_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__7));
v___x_714_ = l_Lean_stringToMessageData(v___x_713_);
return v___x_714_;
}
}
lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select(lean_object* v_m_715_, lean_object* v_n_716_, lean_object* v_goal_717_, lean_object* v_a_718_, lean_object* v_a_719_, lean_object* v_a_720_, lean_object* v_a_721_){
_start:
{
lean_object* v___y_724_; lean_object* v___y_725_; lean_object* v___y_726_; lean_object* v___y_727_; lean_object* v___y_731_; lean_object* v___y_732_; lean_object* v___y_733_; lean_object* v___y_734_; lean_object* v_zero_737_; uint8_t v_isZero_738_; 
v_zero_737_ = lean_unsigned_to_nat(0u);
v_isZero_738_ = lean_nat_dec_eq(v_m_715_, v_zero_737_);
if (v_isZero_738_ == 1)
{
uint8_t v_isZero_739_; 
lean_dec(v_m_715_);
v_isZero_739_ = lean_nat_dec_eq(v_n_716_, v_zero_737_);
lean_dec(v_n_716_);
if (v_isZero_739_ == 1)
{
lean_object* v___x_740_; 
v___x_740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_740_, 0, v_goal_717_);
return v___x_740_;
}
else
{
lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; 
v___x_741_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__3));
v___x_742_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__4));
v___x_743_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor(v___x_741_, v_zero_737_, v___x_742_, v_goal_717_, v_a_718_, v_a_719_, v_a_720_, v_a_721_);
if (lean_obj_tag(v___x_743_) == 0)
{
lean_object* v_a_744_; lean_object* v___x_746_; uint8_t v_isShared_747_; uint8_t v_isSharedCheck_753_; 
v_a_744_ = lean_ctor_get(v___x_743_, 0);
v_isSharedCheck_753_ = !lean_is_exclusive(v___x_743_);
if (v_isSharedCheck_753_ == 0)
{
v___x_746_ = v___x_743_;
v_isShared_747_ = v_isSharedCheck_753_;
goto v_resetjp_745_;
}
else
{
lean_inc(v_a_744_);
lean_dec(v___x_743_);
v___x_746_ = lean_box(0);
v_isShared_747_ = v_isSharedCheck_753_;
goto v_resetjp_745_;
}
v_resetjp_745_:
{
if (lean_obj_tag(v_a_744_) == 1)
{
lean_object* v_tail_748_; 
v_tail_748_ = lean_ctor_get(v_a_744_, 1);
if (lean_obj_tag(v_tail_748_) == 0)
{
lean_object* v_head_749_; lean_object* v___x_751_; 
v_head_749_ = lean_ctor_get(v_a_744_, 0);
lean_inc(v_head_749_);
lean_dec_ref_known(v_a_744_, 2);
if (v_isShared_747_ == 0)
{
lean_ctor_set(v___x_746_, 0, v_head_749_);
v___x_751_ = v___x_746_;
goto v_reusejp_750_;
}
else
{
lean_object* v_reuseFailAlloc_752_; 
v_reuseFailAlloc_752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_752_, 0, v_head_749_);
v___x_751_ = v_reuseFailAlloc_752_;
goto v_reusejp_750_;
}
v_reusejp_750_:
{
return v___x_751_;
}
}
else
{
lean_dec_ref_known(v_a_744_, 2);
lean_del_object(v___x_746_);
v___y_724_ = v_a_718_;
v___y_725_ = v_a_719_;
v___y_726_ = v_a_720_;
v___y_727_ = v_a_721_;
goto v___jp_723_;
}
}
else
{
lean_del_object(v___x_746_);
lean_dec(v_a_744_);
v___y_724_ = v_a_718_;
v___y_725_ = v_a_719_;
v___y_726_ = v_a_720_;
v___y_727_ = v_a_721_;
goto v___jp_723_;
}
}
}
else
{
lean_object* v_a_754_; lean_object* v___x_756_; uint8_t v_isShared_757_; uint8_t v_isSharedCheck_761_; 
v_a_754_ = lean_ctor_get(v___x_743_, 0);
v_isSharedCheck_761_ = !lean_is_exclusive(v___x_743_);
if (v_isSharedCheck_761_ == 0)
{
v___x_756_ = v___x_743_;
v_isShared_757_ = v_isSharedCheck_761_;
goto v_resetjp_755_;
}
else
{
lean_inc(v_a_754_);
lean_dec(v___x_743_);
v___x_756_ = lean_box(0);
v_isShared_757_ = v_isSharedCheck_761_;
goto v_resetjp_755_;
}
v_resetjp_755_:
{
lean_object* v___x_759_; 
if (v_isShared_757_ == 0)
{
v___x_759_ = v___x_756_;
goto v_reusejp_758_;
}
else
{
lean_object* v_reuseFailAlloc_760_; 
v_reuseFailAlloc_760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_760_, 0, v_a_754_);
v___x_759_ = v_reuseFailAlloc_760_;
goto v_reusejp_758_;
}
v_reusejp_758_:
{
return v___x_759_;
}
}
}
}
}
else
{
uint8_t v_isZero_762_; 
v_isZero_762_ = lean_nat_dec_eq(v_n_716_, v_zero_737_);
if (v_isZero_762_ == 0)
{
lean_object* v_one_763_; lean_object* v_n_764_; lean_object* v_n_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; 
v_one_763_ = lean_unsigned_to_nat(1u);
v_n_764_ = lean_nat_sub(v_m_715_, v_one_763_);
lean_dec(v_m_715_);
v_n_765_ = lean_nat_sub(v_n_716_, v_one_763_);
lean_dec(v_n_716_);
v___x_766_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__6));
v___x_767_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__4));
v___x_768_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor(v___x_766_, v_one_763_, v___x_767_, v_goal_717_, v_a_718_, v_a_719_, v_a_720_, v_a_721_);
if (lean_obj_tag(v___x_768_) == 0)
{
lean_object* v_a_769_; 
v_a_769_ = lean_ctor_get(v___x_768_, 0);
lean_inc(v_a_769_);
lean_dec_ref_known(v___x_768_, 1);
if (lean_obj_tag(v_a_769_) == 1)
{
lean_object* v_tail_770_; 
v_tail_770_ = lean_ctor_get(v_a_769_, 1);
if (lean_obj_tag(v_tail_770_) == 0)
{
lean_object* v_head_771_; 
v_head_771_ = lean_ctor_get(v_a_769_, 0);
lean_inc(v_head_771_);
lean_dec_ref_known(v_a_769_, 2);
v_m_715_ = v_n_764_;
v_n_716_ = v_n_765_;
v_goal_717_ = v_head_771_;
goto _start;
}
else
{
lean_dec_ref_known(v_a_769_, 2);
lean_dec(v_n_765_);
lean_dec(v_n_764_);
v___y_731_ = v_a_718_;
v___y_732_ = v_a_719_;
v___y_733_ = v_a_720_;
v___y_734_ = v_a_721_;
goto v___jp_730_;
}
}
else
{
lean_dec(v_a_769_);
lean_dec(v_n_765_);
lean_dec(v_n_764_);
v___y_731_ = v_a_718_;
v___y_732_ = v_a_719_;
v___y_733_ = v_a_720_;
v___y_734_ = v_a_721_;
goto v___jp_730_;
}
}
else
{
lean_object* v_a_773_; lean_object* v___x_775_; uint8_t v_isShared_776_; uint8_t v_isSharedCheck_780_; 
lean_dec(v_n_765_);
lean_dec(v_n_764_);
v_a_773_ = lean_ctor_get(v___x_768_, 0);
v_isSharedCheck_780_ = !lean_is_exclusive(v___x_768_);
if (v_isSharedCheck_780_ == 0)
{
v___x_775_ = v___x_768_;
v_isShared_776_ = v_isSharedCheck_780_;
goto v_resetjp_774_;
}
else
{
lean_inc(v_a_773_);
lean_dec(v___x_768_);
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
else
{
lean_object* v___x_781_; lean_object* v___x_782_; 
lean_dec(v_goal_717_);
lean_dec(v_n_716_);
lean_dec(v_m_715_);
v___x_781_ = lean_obj_once(&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__8, &l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__8_once, _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__8);
v___x_782_ = l_Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0___redArg(v___x_781_, v_a_718_, v_a_719_, v_a_720_, v_a_721_);
return v___x_782_;
}
}
v___jp_723_:
{
lean_object* v___x_728_; lean_object* v___x_729_; 
v___x_728_ = lean_obj_once(&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__1, &l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__1_once, _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__1);
v___x_729_ = l_Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0___redArg(v___x_728_, v___y_724_, v___y_725_, v___y_726_, v___y_727_);
return v___x_729_;
}
v___jp_730_:
{
lean_object* v___x_735_; lean_object* v___x_736_; 
v___x_735_ = lean_obj_once(&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__1, &l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__1_once, _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__1);
v___x_736_ = l_Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0___redArg(v___x_735_, v___y_731_, v___y_732_, v___y_733_, v___y_734_);
return v___x_736_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_715_ = stack[0].m_obj;
lean_object* v_n_716_ = stack[1].m_obj;
lean_object* v_goal_717_ = stack[2].m_obj;
lean_object* v_a_718_ = stack[3].m_obj;
lean_object* v_a_719_ = stack[4].m_obj;
lean_object* v_a_720_ = stack[5].m_obj;
lean_object* v_a_721_ = stack[6].m_obj;
lean_object* v_res_783_;
v_res_783_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select(v_m_715_, v_n_716_, v_goal_717_, v_a_718_, v_a_719_, v_a_720_, v_a_721_);
stack->m_obj
 = v_res_783_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___boxed(lean_object* v_m_784_, lean_object* v_n_785_, lean_object* v_goal_786_, lean_object* v_a_787_, lean_object* v_a_788_, lean_object* v_a_789_, lean_object* v_a_790_, lean_object* v_a_791_){
_start:
{
lean_object* v_res_792_; 
v_res_792_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select(v_m_784_, v_n_785_, v_goal_786_, v_a_787_, v_a_788_, v_a_789_, v_a_790_);
lean_dec(v_a_790_);
lean_dec_ref(v_a_789_);
lean_dec(v_a_788_);
lean_dec_ref(v_a_787_);
return v_res_792_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_compactRelation___lam__0(lean_object* v___y_793_){
_start:
{
lean_inc_ref(v___y_793_);
return v___y_793_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_compactRelation___lam__0___boxed(lean_object* v___y_794_){
_start:
{
lean_object* v_res_795_; 
v_res_795_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_compactRelation___lam__0(v___y_794_);
lean_dec_ref(v___y_794_);
return v_res_795_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_compactRelation___lam__1(lean_object* v_snd_796_, lean_object* v_head_797_, lean_object* v_fst_798_, lean_object* v___y_799_){
_start:
{
lean_object* v___x_800_; lean_object* v___x_801_; 
v___x_800_ = lean_apply_1(v_snd_796_, v___y_799_);
v___x_801_ = l_Lean_Expr_replaceFVar(v___x_800_, v_head_797_, v_fst_798_);
lean_dec_ref(v___x_800_);
return v___x_801_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_compactRelation___lam__1___boxed(lean_object* v_snd_802_, lean_object* v_head_803_, lean_object* v_fst_804_, lean_object* v___y_805_){
_start:
{
lean_object* v_res_806_; 
v_res_806_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_compactRelation___lam__1(v_snd_802_, v_head_803_, v_fst_804_, v___y_805_);
lean_dec_ref(v_fst_804_);
return v_res_806_;
}
}
LEAN_EXPORT lean_object* l_List_span_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_compactRelation_spec__0(lean_object* v_head_807_, lean_object* v_a_808_, lean_object* v_a_809_){
_start:
{
if (lean_obj_tag(v_a_808_) == 0)
{
lean_object* v___x_810_; lean_object* v___x_811_; 
v___x_810_ = l_List_reverse___redArg(v_a_809_);
v___x_811_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_811_, 0, v___x_810_);
lean_ctor_set(v___x_811_, 1, v_a_808_);
return v___x_811_;
}
else
{
lean_object* v_head_812_; lean_object* v_tail_813_; lean_object* v_snd_814_; uint8_t v___x_815_; 
v_head_812_ = lean_ctor_get(v_a_808_, 0);
lean_inc(v_head_812_);
v_tail_813_ = lean_ctor_get(v_a_808_, 1);
v_snd_814_ = lean_ctor_get(v_head_812_, 1);
v___x_815_ = lean_expr_eqv(v_snd_814_, v_head_807_);
if (v___x_815_ == 0)
{
lean_object* v___x_817_; uint8_t v_isShared_818_; uint8_t v_isSharedCheck_823_; 
lean_inc(v_tail_813_);
v_isSharedCheck_823_ = !lean_is_exclusive(v_a_808_);
if (v_isSharedCheck_823_ == 0)
{
lean_object* v_unused_824_; lean_object* v_unused_825_; 
v_unused_824_ = lean_ctor_get(v_a_808_, 1);
lean_dec(v_unused_824_);
v_unused_825_ = lean_ctor_get(v_a_808_, 0);
lean_dec(v_unused_825_);
v___x_817_ = v_a_808_;
v_isShared_818_ = v_isSharedCheck_823_;
goto v_resetjp_816_;
}
else
{
lean_dec(v_a_808_);
v___x_817_ = lean_box(0);
v_isShared_818_ = v_isSharedCheck_823_;
goto v_resetjp_816_;
}
v_resetjp_816_:
{
lean_object* v___x_820_; 
if (v_isShared_818_ == 0)
{
lean_ctor_set(v___x_817_, 1, v_a_809_);
v___x_820_ = v___x_817_;
goto v_reusejp_819_;
}
else
{
lean_object* v_reuseFailAlloc_822_; 
v_reuseFailAlloc_822_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_822_, 0, v_head_812_);
lean_ctor_set(v_reuseFailAlloc_822_, 1, v_a_809_);
v___x_820_ = v_reuseFailAlloc_822_;
goto v_reusejp_819_;
}
v_reusejp_819_:
{
v_a_808_ = v_tail_813_;
v_a_809_ = v___x_820_;
goto _start;
}
}
}
else
{
lean_object* v___x_827_; uint8_t v_isShared_828_; uint8_t v_isSharedCheck_833_; 
v_isSharedCheck_833_ = !lean_is_exclusive(v_head_812_);
if (v_isSharedCheck_833_ == 0)
{
lean_object* v_unused_834_; lean_object* v_unused_835_; 
v_unused_834_ = lean_ctor_get(v_head_812_, 1);
lean_dec(v_unused_834_);
v_unused_835_ = lean_ctor_get(v_head_812_, 0);
lean_dec(v_unused_835_);
v___x_827_ = v_head_812_;
v_isShared_828_ = v_isSharedCheck_833_;
goto v_resetjp_826_;
}
else
{
lean_dec(v_head_812_);
v___x_827_ = lean_box(0);
v_isShared_828_ = v_isSharedCheck_833_;
goto v_resetjp_826_;
}
v_resetjp_826_:
{
lean_object* v___x_829_; lean_object* v___x_831_; 
v___x_829_ = l_List_reverse___redArg(v_a_809_);
if (v_isShared_828_ == 0)
{
lean_ctor_set(v___x_827_, 1, v_a_808_);
lean_ctor_set(v___x_827_, 0, v___x_829_);
v___x_831_ = v___x_827_;
goto v_reusejp_830_;
}
else
{
lean_object* v_reuseFailAlloc_832_; 
v_reuseFailAlloc_832_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_832_, 0, v___x_829_);
lean_ctor_set(v_reuseFailAlloc_832_, 1, v_a_808_);
v___x_831_ = v_reuseFailAlloc_832_;
goto v_reusejp_830_;
}
v_reusejp_830_:
{
return v___x_831_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_span_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_compactRelation_spec__0___boxed(lean_object* v_head_836_, lean_object* v_a_837_, lean_object* v_a_838_){
_start:
{
lean_object* v_res_839_; 
v_res_839_ = l_List_span_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_compactRelation_spec__0(v_head_836_, v_a_837_, v_a_838_);
lean_dec_ref(v_head_836_);
return v_res_839_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_compactRelation_spec__2(lean_object* v_head_840_, lean_object* v_fst_841_, lean_object* v_a_842_, lean_object* v_a_843_){
_start:
{
if (lean_obj_tag(v_a_842_) == 0)
{
lean_object* v___x_844_; 
lean_dec_ref(v_head_840_);
v___x_844_ = l_List_reverse___redArg(v_a_843_);
return v___x_844_;
}
else
{
lean_object* v_head_845_; lean_object* v_tail_846_; lean_object* v___x_848_; uint8_t v_isShared_849_; uint8_t v_isSharedCheck_864_; 
v_head_845_ = lean_ctor_get(v_a_842_, 0);
v_tail_846_ = lean_ctor_get(v_a_842_, 1);
v_isSharedCheck_864_ = !lean_is_exclusive(v_a_842_);
if (v_isSharedCheck_864_ == 0)
{
v___x_848_ = v_a_842_;
v_isShared_849_ = v_isSharedCheck_864_;
goto v_resetjp_847_;
}
else
{
lean_inc(v_tail_846_);
lean_inc(v_head_845_);
lean_dec(v_a_842_);
v___x_848_ = lean_box(0);
v_isShared_849_ = v_isSharedCheck_864_;
goto v_resetjp_847_;
}
v_resetjp_847_:
{
lean_object* v_fst_850_; lean_object* v_snd_851_; lean_object* v___x_853_; uint8_t v_isShared_854_; uint8_t v_isSharedCheck_863_; 
v_fst_850_ = lean_ctor_get(v_head_845_, 0);
v_snd_851_ = lean_ctor_get(v_head_845_, 1);
v_isSharedCheck_863_ = !lean_is_exclusive(v_head_845_);
if (v_isSharedCheck_863_ == 0)
{
v___x_853_ = v_head_845_;
v_isShared_854_ = v_isSharedCheck_863_;
goto v_resetjp_852_;
}
else
{
lean_inc(v_snd_851_);
lean_inc(v_fst_850_);
lean_dec(v_head_845_);
v___x_853_ = lean_box(0);
v_isShared_854_ = v_isSharedCheck_863_;
goto v_resetjp_852_;
}
v_resetjp_852_:
{
lean_object* v___x_855_; lean_object* v___x_857_; 
lean_inc_ref(v_head_840_);
v___x_855_ = l_Lean_Expr_replaceFVar(v_snd_851_, v_head_840_, v_fst_841_);
lean_dec(v_snd_851_);
if (v_isShared_854_ == 0)
{
lean_ctor_set(v___x_853_, 1, v___x_855_);
v___x_857_ = v___x_853_;
goto v_reusejp_856_;
}
else
{
lean_object* v_reuseFailAlloc_862_; 
v_reuseFailAlloc_862_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_862_, 0, v_fst_850_);
lean_ctor_set(v_reuseFailAlloc_862_, 1, v___x_855_);
v___x_857_ = v_reuseFailAlloc_862_;
goto v_reusejp_856_;
}
v_reusejp_856_:
{
lean_object* v___x_859_; 
if (v_isShared_849_ == 0)
{
lean_ctor_set(v___x_848_, 1, v_a_843_);
lean_ctor_set(v___x_848_, 0, v___x_857_);
v___x_859_ = v___x_848_;
goto v_reusejp_858_;
}
else
{
lean_object* v_reuseFailAlloc_861_; 
v_reuseFailAlloc_861_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_861_, 0, v___x_857_);
lean_ctor_set(v_reuseFailAlloc_861_, 1, v_a_843_);
v___x_859_ = v_reuseFailAlloc_861_;
goto v_reusejp_858_;
}
v_reusejp_858_:
{
v_a_842_ = v_tail_846_;
v_a_843_ = v___x_859_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_compactRelation_spec__2___boxed(lean_object* v_head_865_, lean_object* v_fst_866_, lean_object* v_a_867_, lean_object* v_a_868_){
_start:
{
lean_object* v_res_869_; 
v_res_869_ = l_List_mapTR_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_compactRelation_spec__2(v_head_865_, v_fst_866_, v_a_867_, v_a_868_);
lean_dec_ref(v_fst_866_);
return v_res_869_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_compactRelation_spec__1(lean_object* v_head_870_, lean_object* v_fst_871_, lean_object* v_a_872_, lean_object* v_a_873_){
_start:
{
if (lean_obj_tag(v_a_872_) == 0)
{
lean_object* v___x_874_; 
lean_dec_ref(v_head_870_);
v___x_874_ = l_List_reverse___redArg(v_a_873_);
return v___x_874_;
}
else
{
lean_object* v_head_875_; lean_object* v_tail_876_; lean_object* v___x_878_; uint8_t v_isShared_879_; uint8_t v_isSharedCheck_885_; 
v_head_875_ = lean_ctor_get(v_a_872_, 0);
v_tail_876_ = lean_ctor_get(v_a_872_, 1);
v_isSharedCheck_885_ = !lean_is_exclusive(v_a_872_);
if (v_isSharedCheck_885_ == 0)
{
v___x_878_ = v_a_872_;
v_isShared_879_ = v_isSharedCheck_885_;
goto v_resetjp_877_;
}
else
{
lean_inc(v_tail_876_);
lean_inc(v_head_875_);
lean_dec(v_a_872_);
v___x_878_ = lean_box(0);
v_isShared_879_ = v_isSharedCheck_885_;
goto v_resetjp_877_;
}
v_resetjp_877_:
{
lean_object* v___x_880_; lean_object* v___x_882_; 
lean_inc_ref(v_head_870_);
v___x_880_ = l_Lean_Expr_replaceFVar(v_head_875_, v_head_870_, v_fst_871_);
lean_dec(v_head_875_);
if (v_isShared_879_ == 0)
{
lean_ctor_set(v___x_878_, 1, v_a_873_);
lean_ctor_set(v___x_878_, 0, v___x_880_);
v___x_882_ = v___x_878_;
goto v_reusejp_881_;
}
else
{
lean_object* v_reuseFailAlloc_884_; 
v_reuseFailAlloc_884_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_884_, 0, v___x_880_);
lean_ctor_set(v_reuseFailAlloc_884_, 1, v_a_873_);
v___x_882_ = v_reuseFailAlloc_884_;
goto v_reusejp_881_;
}
v_reusejp_881_:
{
v_a_872_ = v_tail_876_;
v_a_873_ = v___x_882_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_compactRelation_spec__1___boxed(lean_object* v_head_886_, lean_object* v_fst_887_, lean_object* v_a_888_, lean_object* v_a_889_){
_start:
{
lean_object* v_res_890_; 
v_res_890_ = l_List_mapTR_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_compactRelation_spec__1(v_head_886_, v_fst_887_, v_a_888_, v_a_889_);
lean_dec_ref(v_fst_887_);
return v_res_890_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_compactRelation(lean_object* v_x_892_, lean_object* v_x_893_){
_start:
{
if (lean_obj_tag(v_x_892_) == 0)
{
lean_object* v___f_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; 
v___f_894_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_compactRelation___closed__0));
v___x_895_ = lean_box(0);
v___x_896_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_896_, 0, v_x_893_);
lean_ctor_set(v___x_896_, 1, v___f_894_);
v___x_897_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_897_, 0, v___x_895_);
lean_ctor_set(v___x_897_, 1, v___x_896_);
return v___x_897_;
}
else
{
lean_object* v_head_898_; lean_object* v_tail_899_; lean_object* v___x_901_; uint8_t v_isShared_902_; uint8_t v_isSharedCheck_956_; 
v_head_898_ = lean_ctor_get(v_x_892_, 0);
v_tail_899_ = lean_ctor_get(v_x_892_, 1);
v_isSharedCheck_956_ = !lean_is_exclusive(v_x_892_);
if (v_isSharedCheck_956_ == 0)
{
v___x_901_ = v_x_892_;
v_isShared_902_ = v_isSharedCheck_956_;
goto v_resetjp_900_;
}
else
{
lean_inc(v_tail_899_);
lean_inc(v_head_898_);
lean_dec(v_x_892_);
v___x_901_ = lean_box(0);
v_isShared_902_ = v_isSharedCheck_956_;
goto v_resetjp_900_;
}
v_resetjp_900_:
{
lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v_snd_905_; 
v___x_903_ = lean_box(0);
lean_inc(v_x_893_);
v___x_904_ = l_List_span_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_compactRelation_spec__0(v_head_898_, v_x_893_, v___x_903_);
v_snd_905_ = lean_ctor_get(v___x_904_, 1);
lean_inc(v_snd_905_);
if (lean_obj_tag(v_snd_905_) == 0)
{
lean_object* v___x_906_; lean_object* v_fst_907_; lean_object* v_snd_908_; lean_object* v___x_910_; uint8_t v_isShared_911_; uint8_t v_isSharedCheck_919_; 
lean_dec_ref(v___x_904_);
v___x_906_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_compactRelation(v_tail_899_, v_x_893_);
v_fst_907_ = lean_ctor_get(v___x_906_, 0);
v_snd_908_ = lean_ctor_get(v___x_906_, 1);
v_isSharedCheck_919_ = !lean_is_exclusive(v___x_906_);
if (v_isSharedCheck_919_ == 0)
{
v___x_910_ = v___x_906_;
v_isShared_911_ = v_isSharedCheck_919_;
goto v_resetjp_909_;
}
else
{
lean_inc(v_snd_908_);
lean_inc(v_fst_907_);
lean_dec(v___x_906_);
v___x_910_ = lean_box(0);
v_isShared_911_ = v_isSharedCheck_919_;
goto v_resetjp_909_;
}
v_resetjp_909_:
{
lean_object* v___x_912_; lean_object* v___x_914_; 
v___x_912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_912_, 0, v_head_898_);
if (v_isShared_902_ == 0)
{
lean_ctor_set(v___x_901_, 1, v_fst_907_);
lean_ctor_set(v___x_901_, 0, v___x_912_);
v___x_914_ = v___x_901_;
goto v_reusejp_913_;
}
else
{
lean_object* v_reuseFailAlloc_918_; 
v_reuseFailAlloc_918_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_918_, 0, v___x_912_);
lean_ctor_set(v_reuseFailAlloc_918_, 1, v_fst_907_);
v___x_914_ = v_reuseFailAlloc_918_;
goto v_reusejp_913_;
}
v_reusejp_913_:
{
lean_object* v___x_916_; 
if (v_isShared_911_ == 0)
{
lean_ctor_set(v___x_910_, 0, v___x_914_);
v___x_916_ = v___x_910_;
goto v_reusejp_915_;
}
else
{
lean_object* v_reuseFailAlloc_917_; 
v_reuseFailAlloc_917_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_917_, 0, v___x_914_);
lean_ctor_set(v_reuseFailAlloc_917_, 1, v_snd_908_);
v___x_916_ = v_reuseFailAlloc_917_;
goto v_reusejp_915_;
}
v_reusejp_915_:
{
return v___x_916_;
}
}
}
}
else
{
lean_object* v_head_920_; lean_object* v_fst_921_; lean_object* v_tail_922_; lean_object* v___x_924_; uint8_t v_isShared_925_; uint8_t v_isSharedCheck_954_; 
lean_del_object(v___x_901_);
lean_dec(v_x_893_);
v_head_920_ = lean_ctor_get(v_snd_905_, 0);
lean_inc(v_head_920_);
v_fst_921_ = lean_ctor_get(v___x_904_, 0);
lean_inc(v_fst_921_);
lean_dec_ref(v___x_904_);
v_tail_922_ = lean_ctor_get(v_snd_905_, 1);
v_isSharedCheck_954_ = !lean_is_exclusive(v_snd_905_);
if (v_isSharedCheck_954_ == 0)
{
lean_object* v_unused_955_; 
v_unused_955_ = lean_ctor_get(v_snd_905_, 0);
lean_dec(v_unused_955_);
v___x_924_ = v_snd_905_;
v_isShared_925_ = v_isSharedCheck_954_;
goto v_resetjp_923_;
}
else
{
lean_inc(v_tail_922_);
lean_dec(v_snd_905_);
v___x_924_ = lean_box(0);
v_isShared_925_ = v_isSharedCheck_954_;
goto v_resetjp_923_;
}
v_resetjp_923_:
{
lean_object* v_fst_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v_snd_931_; lean_object* v_fst_932_; lean_object* v___x_934_; uint8_t v_isShared_935_; uint8_t v_isSharedCheck_953_; 
v_fst_926_ = lean_ctor_get(v_head_920_, 0);
lean_inc(v_fst_926_);
lean_dec(v_head_920_);
lean_inc_n(v_head_898_, 2);
v___x_927_ = l_List_mapTR_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_compactRelation_spec__1(v_head_898_, v_fst_926_, v_tail_899_, v___x_903_);
v___x_928_ = l_List_appendTR___redArg(v_fst_921_, v_tail_922_);
v___x_929_ = l_List_mapTR_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_compactRelation_spec__2(v_head_898_, v_fst_926_, v___x_928_, v___x_903_);
v___x_930_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_compactRelation(v___x_927_, v___x_929_);
v_snd_931_ = lean_ctor_get(v___x_930_, 1);
v_fst_932_ = lean_ctor_get(v___x_930_, 0);
v_isSharedCheck_953_ = !lean_is_exclusive(v___x_930_);
if (v_isSharedCheck_953_ == 0)
{
v___x_934_ = v___x_930_;
v_isShared_935_ = v_isSharedCheck_953_;
goto v_resetjp_933_;
}
else
{
lean_inc(v_snd_931_);
lean_inc(v_fst_932_);
lean_dec(v___x_930_);
v___x_934_ = lean_box(0);
v_isShared_935_ = v_isSharedCheck_953_;
goto v_resetjp_933_;
}
v_resetjp_933_:
{
lean_object* v_fst_936_; lean_object* v_snd_937_; lean_object* v___x_939_; uint8_t v_isShared_940_; uint8_t v_isSharedCheck_952_; 
v_fst_936_ = lean_ctor_get(v_snd_931_, 0);
v_snd_937_ = lean_ctor_get(v_snd_931_, 1);
v_isSharedCheck_952_ = !lean_is_exclusive(v_snd_931_);
if (v_isSharedCheck_952_ == 0)
{
v___x_939_ = v_snd_931_;
v_isShared_940_ = v_isSharedCheck_952_;
goto v_resetjp_938_;
}
else
{
lean_inc(v_snd_937_);
lean_inc(v_fst_936_);
lean_dec(v_snd_931_);
v___x_939_ = lean_box(0);
v_isShared_940_ = v_isSharedCheck_952_;
goto v_resetjp_938_;
}
v_resetjp_938_:
{
lean_object* v___f_941_; lean_object* v___x_942_; lean_object* v___x_944_; 
v___f_941_ = lean_alloc_closure((void*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_compactRelation___lam__1___boxed), 4, 3);
lean_closure_set(v___f_941_, 0, v_snd_937_);
lean_closure_set(v___f_941_, 1, v_head_898_);
lean_closure_set(v___f_941_, 2, v_fst_926_);
v___x_942_ = lean_box(0);
if (v_isShared_925_ == 0)
{
lean_ctor_set(v___x_924_, 1, v_fst_932_);
lean_ctor_set(v___x_924_, 0, v___x_942_);
v___x_944_ = v___x_924_;
goto v_reusejp_943_;
}
else
{
lean_object* v_reuseFailAlloc_951_; 
v_reuseFailAlloc_951_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_951_, 0, v___x_942_);
lean_ctor_set(v_reuseFailAlloc_951_, 1, v_fst_932_);
v___x_944_ = v_reuseFailAlloc_951_;
goto v_reusejp_943_;
}
v_reusejp_943_:
{
lean_object* v___x_946_; 
if (v_isShared_940_ == 0)
{
lean_ctor_set(v___x_939_, 1, v___f_941_);
v___x_946_ = v___x_939_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_950_; 
v_reuseFailAlloc_950_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_950_, 0, v_fst_936_);
lean_ctor_set(v_reuseFailAlloc_950_, 1, v___f_941_);
v___x_946_ = v_reuseFailAlloc_950_;
goto v_reusejp_945_;
}
v_reusejp_945_:
{
lean_object* v___x_948_; 
if (v_isShared_935_ == 0)
{
lean_ctor_set(v___x_934_, 1, v___x_946_);
lean_ctor_set(v___x_934_, 0, v___x_944_);
v___x_948_ = v___x_934_;
goto v_reusejp_947_;
}
else
{
lean_object* v_reuseFailAlloc_949_; 
v_reuseFailAlloc_949_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_949_, 0, v___x_944_);
lean_ctor_set(v_reuseFailAlloc_949_, 1, v___x_946_);
v___x_948_ = v_reuseFailAlloc_949_;
goto v_reusejp_947_;
}
v_reusejp_947_:
{
return v___x_948_;
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
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_updateLambdaBinderInfoD_x21_spec__0(lean_object* v_msg_957_){
_start:
{
lean_object* v___x_958_; lean_object* v___x_959_; 
v___x_958_ = l_Lean_instInhabitedExpr;
v___x_959_ = lean_panic_fn_borrowed(v___x_958_, v_msg_957_);
return v___x_959_;
}
}
static lean_object* _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_updateLambdaBinderInfoD_x21___closed__3(void){
_start:
{
lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; 
v___x_963_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_updateLambdaBinderInfoD_x21___closed__2));
v___x_964_ = lean_unsigned_to_nat(19u);
v___x_965_ = lean_unsigned_to_nat(96u);
v___x_966_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_updateLambdaBinderInfoD_x21___closed__1));
v___x_967_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_updateLambdaBinderInfoD_x21___closed__0));
v___x_968_ = l_mkPanicMessageWithDecl(v___x_967_, v___x_966_, v___x_965_, v___x_964_, v___x_963_);
return v___x_968_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_updateLambdaBinderInfoD_x21(lean_object* v_e_969_){
_start:
{
if (lean_obj_tag(v_e_969_) == 6)
{
lean_object* v_binderName_970_; lean_object* v_binderType_971_; lean_object* v_body_972_; uint8_t v___x_973_; lean_object* v___x_974_; 
v_binderName_970_ = lean_ctor_get(v_e_969_, 0);
lean_inc(v_binderName_970_);
v_binderType_971_ = lean_ctor_get(v_e_969_, 1);
lean_inc_ref(v_binderType_971_);
v_body_972_ = lean_ctor_get(v_e_969_, 2);
lean_inc_ref(v_body_972_);
lean_dec_ref_known(v_e_969_, 3);
v___x_973_ = 0;
v___x_974_ = l_Lean_Expr_lam___override(v_binderName_970_, v_binderType_971_, v_body_972_, v___x_973_);
return v___x_974_;
}
else
{
lean_object* v___x_975_; lean_object* v___x_976_; 
lean_dec_ref(v_e_969_);
v___x_975_ = lean_obj_once(&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_updateLambdaBinderInfoD_x21___closed__3, &l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_updateLambdaBinderInfoD_x21___closed__3_once, _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_updateLambdaBinderInfoD_x21___closed__3);
v___x_976_ = l_panic___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_updateLambdaBinderInfoD_x21_spec__0(v___x_975_);
return v___x_976_;
}
}
}
static lean_object* _init_l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkExistsList_spec__0___closed__4(void){
_start:
{
lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; 
v___x_983_ = lean_box(0);
v___x_984_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkExistsList_spec__0___closed__3));
v___x_985_ = l_Lean_mkConst(v___x_984_, v___x_983_);
return v___x_985_;
}
}
lean_object* l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkExistsList_spec__0(lean_object* v_x_986_, lean_object* v_x_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_){
_start:
{
if (lean_obj_tag(v_x_987_) == 0)
{
lean_object* v___x_993_; 
v___x_993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_993_, 0, v_x_986_);
return v___x_993_;
}
else
{
lean_object* v_head_994_; lean_object* v_tail_995_; lean_object* v___x_997_; uint8_t v_isShared_998_; uint8_t v_isSharedCheck_1034_; 
v_head_994_ = lean_ctor_get(v_x_987_, 0);
v_tail_995_ = lean_ctor_get(v_x_987_, 1);
v_isSharedCheck_1034_ = !lean_is_exclusive(v_x_987_);
if (v_isSharedCheck_1034_ == 0)
{
v___x_997_ = v_x_987_;
v_isShared_998_ = v_isSharedCheck_1034_;
goto v_resetjp_996_;
}
else
{
lean_inc(v_tail_995_);
lean_inc(v_head_994_);
lean_dec(v_x_987_);
v___x_997_ = lean_box(0);
v_isShared_998_ = v_isSharedCheck_1034_;
goto v_resetjp_996_;
}
v_resetjp_996_:
{
lean_object* v___y_1000_; lean_object* v___x_1003_; 
lean_inc(v___y_991_);
lean_inc_ref(v___y_990_);
lean_inc(v___y_989_);
lean_inc_ref(v___y_988_);
lean_inc(v_head_994_);
v___x_1003_ = lean_infer_type(v_head_994_, v___y_988_, v___y_989_, v___y_990_, v___y_991_);
if (lean_obj_tag(v___x_1003_) == 0)
{
lean_object* v_a_1004_; lean_object* v___x_1005_; 
v_a_1004_ = lean_ctor_get(v___x_1003_, 0);
lean_inc_n(v_a_1004_, 2);
lean_dec_ref_known(v___x_1003_, 1);
lean_inc(v___y_991_);
lean_inc_ref(v___y_990_);
lean_inc(v___y_989_);
lean_inc_ref(v___y_988_);
v___x_1005_ = lean_infer_type(v_a_1004_, v___y_988_, v___y_989_, v___y_990_, v___y_991_);
if (lean_obj_tag(v___x_1005_) == 0)
{
lean_object* v_a_1006_; lean_object* v___x_1007_; uint8_t v___y_1027_; uint8_t v___x_1031_; 
v_a_1006_ = lean_ctor_get(v___x_1005_, 0);
lean_inc(v_a_1006_);
lean_dec_ref_known(v___x_1005_, 1);
v___x_1007_ = l_Lean_Expr_sortLevel_x21(v_a_1006_);
lean_dec(v_a_1006_);
lean_inc(v_head_994_);
v___x_1031_ = l_Lean_Expr_occurs(v_head_994_, v_x_986_);
if (v___x_1031_ == 0)
{
lean_object* v___x_1032_; uint8_t v___x_1033_; 
v___x_1032_ = lean_box(0);
v___x_1033_ = lean_level_eq(v___x_1007_, v___x_1032_);
if (v___x_1033_ == 0)
{
goto v___jp_1008_;
}
else
{
v___y_1027_ = v___x_1031_;
goto v___jp_1026_;
}
}
else
{
v___y_1027_ = v___x_1031_;
goto v___jp_1026_;
}
v___jp_1008_:
{
uint8_t v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; uint8_t v___x_1013_; uint8_t v___x_1014_; lean_object* v___x_1015_; 
v___x_1009_ = 1;
v___x_1010_ = lean_unsigned_to_nat(1u);
v___x_1011_ = lean_mk_empty_array_with_capacity(v___x_1010_);
v___x_1012_ = lean_array_push(v___x_1011_, v_head_994_);
v___x_1013_ = 0;
v___x_1014_ = 1;
v___x_1015_ = l_Lean_Meta_mkLambdaFVars(v___x_1012_, v_x_986_, v___x_1013_, v___x_1009_, v___x_1013_, v___x_1009_, v___x_1014_, v___y_988_, v___y_989_, v___y_990_, v___y_991_);
lean_dec_ref(v___x_1012_);
if (lean_obj_tag(v___x_1015_) == 0)
{
lean_object* v_a_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1020_; 
v_a_1016_ = lean_ctor_get(v___x_1015_, 0);
lean_inc(v_a_1016_);
lean_dec_ref_known(v___x_1015_, 1);
v___x_1017_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkExistsList_spec__0___closed__1));
v___x_1018_ = lean_box(0);
if (v_isShared_998_ == 0)
{
lean_ctor_set(v___x_997_, 1, v___x_1018_);
lean_ctor_set(v___x_997_, 0, v___x_1007_);
v___x_1020_ = v___x_997_;
goto v_reusejp_1019_;
}
else
{
lean_object* v_reuseFailAlloc_1025_; 
v_reuseFailAlloc_1025_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1025_, 0, v___x_1007_);
lean_ctor_set(v_reuseFailAlloc_1025_, 1, v___x_1018_);
v___x_1020_ = v_reuseFailAlloc_1025_;
goto v_reusejp_1019_;
}
v_reusejp_1019_:
{
lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; 
v___x_1021_ = l_Lean_Expr_const___override(v___x_1017_, v___x_1020_);
v___x_1022_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_updateLambdaBinderInfoD_x21(v_a_1016_);
v___x_1023_ = l_Lean_mkAppB(v___x_1021_, v_a_1004_, v___x_1022_);
v_x_986_ = v___x_1023_;
v_x_987_ = v_tail_995_;
goto _start;
}
}
else
{
lean_dec(v___x_1007_);
lean_dec(v_a_1004_);
lean_del_object(v___x_997_);
v___y_1000_ = v___x_1015_;
goto v___jp_999_;
}
}
v___jp_1026_:
{
if (v___y_1027_ == 0)
{
lean_object* v___x_1028_; lean_object* v___x_1029_; 
lean_dec(v___x_1007_);
lean_del_object(v___x_997_);
lean_dec(v_head_994_);
v___x_1028_ = lean_obj_once(&l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkExistsList_spec__0___closed__4, &l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkExistsList_spec__0___closed__4_once, _init_l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkExistsList_spec__0___closed__4);
v___x_1029_ = l_Lean_mkAppB(v___x_1028_, v_a_1004_, v_x_986_);
v_x_986_ = v___x_1029_;
v_x_987_ = v_tail_995_;
goto _start;
}
else
{
goto v___jp_1008_;
}
}
}
else
{
lean_dec(v_a_1004_);
lean_del_object(v___x_997_);
lean_dec(v_head_994_);
lean_dec_ref(v_x_986_);
v___y_1000_ = v___x_1005_;
goto v___jp_999_;
}
}
else
{
lean_del_object(v___x_997_);
lean_dec(v_head_994_);
lean_dec_ref(v_x_986_);
v___y_1000_ = v___x_1003_;
goto v___jp_999_;
}
v___jp_999_:
{
if (lean_obj_tag(v___y_1000_) == 0)
{
lean_object* v_a_1001_; 
v_a_1001_ = lean_ctor_get(v___y_1000_, 0);
lean_inc(v_a_1001_);
lean_dec_ref_known(v___y_1000_, 1);
v_x_986_ = v_a_1001_;
v_x_987_ = v_tail_995_;
goto _start;
}
else
{
lean_dec(v_tail_995_);
return v___y_1000_;
}
}
}
}
}
}
LEAN_EXPORT void l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkExistsList_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_986_ = stack[0].m_obj;
lean_object* v_x_987_ = stack[1].m_obj;
lean_object* v___y_988_ = stack[2].m_obj;
lean_object* v___y_989_ = stack[3].m_obj;
lean_object* v___y_990_ = stack[4].m_obj;
lean_object* v___y_991_ = stack[5].m_obj;
lean_object* v_res_1035_;
v_res_1035_ = l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkExistsList_spec__0(v_x_986_, v_x_987_, v___y_988_, v___y_989_, v___y_990_, v___y_991_);
stack->m_obj
 = v_res_1035_;
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkExistsList_spec__0___boxed(lean_object* v_x_1036_, lean_object* v_x_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_){
_start:
{
lean_object* v_res_1043_; 
v_res_1043_ = l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkExistsList_spec__0(v_x_1036_, v_x_1037_, v___y_1038_, v___y_1039_, v___y_1040_, v___y_1041_);
lean_dec(v___y_1041_);
lean_dec_ref(v___y_1040_);
lean_dec(v___y_1039_);
lean_dec_ref(v___y_1038_);
return v_res_1043_;
}
}
lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkExistsList(lean_object* v_args_1044_, lean_object* v_inner_1045_, lean_object* v_a_1046_, lean_object* v_a_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_){
_start:
{
lean_object* v___x_1051_; lean_object* v___x_1052_; 
v___x_1051_ = l_List_reverse___redArg(v_args_1044_);
v___x_1052_ = l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkExistsList_spec__0(v_inner_1045_, v___x_1051_, v_a_1046_, v_a_1047_, v_a_1048_, v_a_1049_);
return v___x_1052_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkExistsList_0interp(lean_interpreter_value* stack)
{
lean_object* v_args_1044_ = stack[0].m_obj;
lean_object* v_inner_1045_ = stack[1].m_obj;
lean_object* v_a_1046_ = stack[2].m_obj;
lean_object* v_a_1047_ = stack[3].m_obj;
lean_object* v_a_1048_ = stack[4].m_obj;
lean_object* v_a_1049_ = stack[5].m_obj;
lean_object* v_res_1053_;
v_res_1053_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkExistsList(v_args_1044_, v_inner_1045_, v_a_1046_, v_a_1047_, v_a_1048_, v_a_1049_);
stack->m_obj
 = v_res_1053_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkExistsList___boxed(lean_object* v_args_1054_, lean_object* v_inner_1055_, lean_object* v_a_1056_, lean_object* v_a_1057_, lean_object* v_a_1058_, lean_object* v_a_1059_, lean_object* v_a_1060_){
_start:
{
lean_object* v_res_1061_; 
v_res_1061_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkExistsList(v_args_1054_, v_inner_1055_, v_a_1056_, v_a_1057_, v_a_1058_, v_a_1059_);
lean_dec(v_a_1059_);
lean_dec_ref(v_a_1058_);
lean_dec(v_a_1057_);
lean_dec_ref(v_a_1056_);
return v_res_1061_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkOpList(lean_object* v_op_1062_, lean_object* v_empty_1063_, lean_object* v_x_1064_){
_start:
{
if (lean_obj_tag(v_x_1064_) == 0)
{
lean_dec_ref(v_op_1062_);
lean_inc_ref(v_empty_1063_);
return v_empty_1063_;
}
else
{
lean_object* v_tail_1065_; 
v_tail_1065_ = lean_ctor_get(v_x_1064_, 1);
if (lean_obj_tag(v_tail_1065_) == 0)
{
lean_object* v_head_1066_; 
lean_dec_ref(v_op_1062_);
v_head_1066_ = lean_ctor_get(v_x_1064_, 0);
lean_inc(v_head_1066_);
lean_dec_ref_known(v_x_1064_, 2);
return v_head_1066_;
}
else
{
lean_object* v_head_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; 
lean_inc(v_tail_1065_);
v_head_1067_ = lean_ctor_get(v_x_1064_, 0);
lean_inc(v_head_1067_);
lean_dec_ref_known(v_x_1064_, 2);
lean_inc_ref(v_op_1062_);
v___x_1068_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkOpList(v_op_1062_, v_empty_1063_, v_tail_1065_);
v___x_1069_ = l_Lean_mkAppB(v_op_1062_, v_head_1067_, v___x_1068_);
return v___x_1069_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkOpList___boxed(lean_object* v_op_1070_, lean_object* v_empty_1071_, lean_object* v_x_1072_){
_start:
{
lean_object* v_res_1073_; 
v_res_1073_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkOpList(v_op_1070_, v_empty_1071_, v_x_1072_);
lean_dec_ref(v_empty_1071_);
return v_res_1073_;
}
}
static lean_object* _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkAndList___closed__2(void){
_start:
{
lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; 
v___x_1077_ = lean_box(0);
v___x_1078_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkAndList___closed__1));
v___x_1079_ = l_Lean_mkConst(v___x_1078_, v___x_1077_);
return v___x_1079_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkAndList(lean_object* v_a_1080_){
_start:
{
lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; 
v___x_1081_ = lean_obj_once(&l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkExistsList_spec__0___closed__4, &l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkExistsList_spec__0___closed__4_once, _init_l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkExistsList_spec__0___closed__4);
v___x_1082_ = lean_obj_once(&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkAndList___closed__2, &l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkAndList___closed__2_once, _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkAndList___closed__2);
v___x_1083_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkOpList(v___x_1081_, v___x_1082_, v_a_1080_);
return v___x_1083_;
}
}
static lean_object* _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkOrList___closed__2(void){
_start:
{
lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; 
v___x_1087_ = lean_box(0);
v___x_1088_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkOrList___closed__1));
v___x_1089_ = l_Lean_mkConst(v___x_1088_, v___x_1087_);
return v___x_1089_;
}
}
static lean_object* _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkOrList___closed__5(void){
_start:
{
lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; 
v___x_1093_ = lean_box(0);
v___x_1094_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkOrList___closed__4));
v___x_1095_ = l_Lean_mkConst(v___x_1094_, v___x_1093_);
return v___x_1095_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkOrList(lean_object* v_a_1096_){
_start:
{
lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; 
v___x_1097_ = lean_obj_once(&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkOrList___closed__2, &l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkOrList___closed__2_once, _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkOrList___closed__2);
v___x_1098_ = lean_obj_once(&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkOrList___closed__5, &l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkOrList___closed__5_once, _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkOrList___closed__5);
v___x_1099_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkOpList(v___x_1097_, v___x_1098_, v_a_1096_);
return v___x_1099_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_List_init___redArg(lean_object* v_x_1100_){
_start:
{
if (lean_obj_tag(v_x_1100_) == 0)
{
return v_x_1100_;
}
else
{
lean_object* v_tail_1101_; 
v_tail_1101_ = lean_ctor_get(v_x_1100_, 1);
lean_inc(v_tail_1101_);
if (lean_obj_tag(v_tail_1101_) == 0)
{
lean_dec_ref_known(v_x_1100_, 2);
return v_tail_1101_;
}
else
{
lean_object* v_head_1102_; lean_object* v___x_1104_; uint8_t v_isShared_1105_; uint8_t v_isSharedCheck_1110_; 
v_head_1102_ = lean_ctor_get(v_x_1100_, 0);
v_isSharedCheck_1110_ = !lean_is_exclusive(v_x_1100_);
if (v_isSharedCheck_1110_ == 0)
{
lean_object* v_unused_1111_; 
v_unused_1111_ = lean_ctor_get(v_x_1100_, 1);
lean_dec(v_unused_1111_);
v___x_1104_ = v_x_1100_;
v_isShared_1105_ = v_isSharedCheck_1110_;
goto v_resetjp_1103_;
}
else
{
lean_inc(v_head_1102_);
lean_dec(v_x_1100_);
v___x_1104_ = lean_box(0);
v_isShared_1105_ = v_isSharedCheck_1110_;
goto v_resetjp_1103_;
}
v_resetjp_1103_:
{
lean_object* v___x_1106_; lean_object* v___x_1108_; 
v___x_1106_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_List_init___redArg(v_tail_1101_);
if (v_isShared_1105_ == 0)
{
lean_ctor_set(v___x_1104_, 1, v___x_1106_);
v___x_1108_ = v___x_1104_;
goto v_reusejp_1107_;
}
else
{
lean_object* v_reuseFailAlloc_1109_; 
v_reuseFailAlloc_1109_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1109_, 0, v_head_1102_);
lean_ctor_set(v_reuseFailAlloc_1109_, 1, v___x_1106_);
v___x_1108_ = v_reuseFailAlloc_1109_;
goto v_reusejp_1107_;
}
v_reusejp_1107_:
{
return v___x_1108_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_List_init(lean_object* v_00_u03b1_1112_, lean_object* v_x_1113_){
_start:
{
lean_object* v___x_1114_; 
v___x_1114_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_List_init___redArg(v_x_1113_);
return v___x_1114_;
}
}
lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__4___redArg___lam__0(lean_object* v_k_1115_, lean_object* v_b_1116_, lean_object* v_c_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_){
_start:
{
lean_object* v___x_1123_; 
lean_inc(v___y_1121_);
lean_inc_ref(v___y_1120_);
lean_inc(v___y_1119_);
lean_inc_ref(v___y_1118_);
v___x_1123_ = lean_apply_7(v_k_1115_, v_b_1116_, v_c_1117_, v___y_1118_, v___y_1119_, v___y_1120_, v___y_1121_, lean_box(0));
return v___x_1123_;
}
}
LEAN_EXPORT void l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__4___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_1115_ = stack[0].m_obj;
lean_object* v_b_1116_ = stack[1].m_obj;
lean_object* v_c_1117_ = stack[2].m_obj;
lean_object* v___y_1118_ = stack[3].m_obj;
lean_object* v___y_1119_ = stack[4].m_obj;
lean_object* v___y_1120_ = stack[5].m_obj;
lean_object* v___y_1121_ = stack[6].m_obj;
lean_object* v_res_1124_;
v_res_1124_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__4___redArg___lam__0(v_k_1115_, v_b_1116_, v_c_1117_, v___y_1118_, v___y_1119_, v___y_1120_, v___y_1121_);
stack->m_obj
 = v_res_1124_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__4___redArg___lam__0___boxed(lean_object* v_k_1125_, lean_object* v_b_1126_, lean_object* v_c_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_){
_start:
{
lean_object* v_res_1133_; 
v_res_1133_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__4___redArg___lam__0(v_k_1125_, v_b_1126_, v_c_1127_, v___y_1128_, v___y_1129_, v___y_1130_, v___y_1131_);
lean_dec(v___y_1131_);
lean_dec_ref(v___y_1130_);
lean_dec(v___y_1129_);
lean_dec_ref(v___y_1128_);
return v_res_1133_;
}
}
lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__4___redArg(lean_object* v_type_1134_, lean_object* v_maxFVars_x3f_1135_, lean_object* v_k_1136_, uint8_t v_cleanupAnnotations_1137_, uint8_t v_whnfType_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_){
_start:
{
lean_object* v___f_1144_; lean_object* v___x_1145_; 
v___f_1144_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__4___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1144_, 0, v_k_1136_);
v___x_1145_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_1134_, v_maxFVars_x3f_1135_, v___f_1144_, v_cleanupAnnotations_1137_, v_whnfType_1138_, v___y_1139_, v___y_1140_, v___y_1141_, v___y_1142_);
if (lean_obj_tag(v___x_1145_) == 0)
{
lean_object* v_a_1146_; lean_object* v___x_1148_; uint8_t v_isShared_1149_; uint8_t v_isSharedCheck_1153_; 
v_a_1146_ = lean_ctor_get(v___x_1145_, 0);
v_isSharedCheck_1153_ = !lean_is_exclusive(v___x_1145_);
if (v_isSharedCheck_1153_ == 0)
{
v___x_1148_ = v___x_1145_;
v_isShared_1149_ = v_isSharedCheck_1153_;
goto v_resetjp_1147_;
}
else
{
lean_inc(v_a_1146_);
lean_dec(v___x_1145_);
v___x_1148_ = lean_box(0);
v_isShared_1149_ = v_isSharedCheck_1153_;
goto v_resetjp_1147_;
}
v_resetjp_1147_:
{
lean_object* v___x_1151_; 
if (v_isShared_1149_ == 0)
{
v___x_1151_ = v___x_1148_;
goto v_reusejp_1150_;
}
else
{
lean_object* v_reuseFailAlloc_1152_; 
v_reuseFailAlloc_1152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1152_, 0, v_a_1146_);
v___x_1151_ = v_reuseFailAlloc_1152_;
goto v_reusejp_1150_;
}
v_reusejp_1150_:
{
return v___x_1151_;
}
}
}
else
{
lean_object* v_a_1154_; lean_object* v___x_1156_; uint8_t v_isShared_1157_; uint8_t v_isSharedCheck_1161_; 
v_a_1154_ = lean_ctor_get(v___x_1145_, 0);
v_isSharedCheck_1161_ = !lean_is_exclusive(v___x_1145_);
if (v_isSharedCheck_1161_ == 0)
{
v___x_1156_ = v___x_1145_;
v_isShared_1157_ = v_isSharedCheck_1161_;
goto v_resetjp_1155_;
}
else
{
lean_inc(v_a_1154_);
lean_dec(v___x_1145_);
v___x_1156_ = lean_box(0);
v_isShared_1157_ = v_isSharedCheck_1161_;
goto v_resetjp_1155_;
}
v_resetjp_1155_:
{
lean_object* v___x_1159_; 
if (v_isShared_1157_ == 0)
{
v___x_1159_ = v___x_1156_;
goto v_reusejp_1158_;
}
else
{
lean_object* v_reuseFailAlloc_1160_; 
v_reuseFailAlloc_1160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1160_, 0, v_a_1154_);
v___x_1159_ = v_reuseFailAlloc_1160_;
goto v_reusejp_1158_;
}
v_reusejp_1158_:
{
return v___x_1159_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_1134_ = stack[0].m_obj;
lean_object* v_maxFVars_x3f_1135_ = stack[1].m_obj;
lean_object* v_k_1136_ = stack[2].m_obj;
uint8_t v_cleanupAnnotations_1137_ = stack[3].m_num;
uint8_t v_whnfType_1138_ = stack[4].m_num;
lean_object* v___y_1139_ = stack[5].m_obj;
lean_object* v___y_1140_ = stack[6].m_obj;
lean_object* v___y_1141_ = stack[7].m_obj;
lean_object* v___y_1142_ = stack[8].m_obj;
lean_object* v_res_1162_;
v_res_1162_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__4___redArg(v_type_1134_, v_maxFVars_x3f_1135_, v_k_1136_, v_cleanupAnnotations_1137_, v_whnfType_1138_, v___y_1139_, v___y_1140_, v___y_1141_, v___y_1142_);
stack->m_obj
 = v_res_1162_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__4___redArg___boxed(lean_object* v_type_1163_, lean_object* v_maxFVars_x3f_1164_, lean_object* v_k_1165_, lean_object* v_cleanupAnnotations_1166_, lean_object* v_whnfType_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1173_; uint8_t v_whnfType_boxed_1174_; lean_object* v_res_1175_; 
v_cleanupAnnotations_boxed_1173_ = lean_unbox(v_cleanupAnnotations_1166_);
v_whnfType_boxed_1174_ = lean_unbox(v_whnfType_1167_);
v_res_1175_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__4___redArg(v_type_1163_, v_maxFVars_x3f_1164_, v_k_1165_, v_cleanupAnnotations_boxed_1173_, v_whnfType_boxed_1174_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_);
lean_dec(v___y_1171_);
lean_dec_ref(v___y_1170_);
lean_dec(v___y_1169_);
lean_dec_ref(v___y_1168_);
return v_res_1175_;
}
}
lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__4(lean_object* v_00_u03b1_1176_, lean_object* v_type_1177_, lean_object* v_maxFVars_x3f_1178_, lean_object* v_k_1179_, uint8_t v_cleanupAnnotations_1180_, uint8_t v_whnfType_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_){
_start:
{
lean_object* v___x_1187_; 
v___x_1187_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__4___redArg(v_type_1177_, v_maxFVars_x3f_1178_, v_k_1179_, v_cleanupAnnotations_1180_, v_whnfType_1181_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_);
return v___x_1187_;
}
}
LEAN_EXPORT void l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_1177_ = stack[1].m_obj;
lean_object* v_maxFVars_x3f_1178_ = stack[2].m_obj;
lean_object* v_k_1179_ = stack[3].m_obj;
uint8_t v_cleanupAnnotations_1180_ = stack[4].m_num;
uint8_t v_whnfType_1181_ = stack[5].m_num;
lean_object* v___y_1182_ = stack[6].m_obj;
lean_object* v___y_1183_ = stack[7].m_obj;
lean_object* v___y_1184_ = stack[8].m_obj;
lean_object* v___y_1185_ = stack[9].m_obj;
lean_object* v_res_1188_;
v_res_1188_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__4(lean_box(0), v_type_1177_, v_maxFVars_x3f_1178_, v_k_1179_, v_cleanupAnnotations_1180_, v_whnfType_1181_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_);
stack->m_obj
 = v_res_1188_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__4___boxed(lean_object* v_00_u03b1_1189_, lean_object* v_type_1190_, lean_object* v_maxFVars_x3f_1191_, lean_object* v_k_1192_, lean_object* v_cleanupAnnotations_1193_, lean_object* v_whnfType_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1200_; uint8_t v_whnfType_boxed_1201_; lean_object* v_res_1202_; 
v_cleanupAnnotations_boxed_1200_ = lean_unbox(v_cleanupAnnotations_1193_);
v_whnfType_boxed_1201_ = lean_unbox(v_whnfType_1194_);
v_res_1202_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__4(v_00_u03b1_1189_, v_type_1190_, v_maxFVars_x3f_1191_, v_k_1192_, v_cleanupAnnotations_boxed_1200_, v_whnfType_boxed_1201_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_);
lean_dec(v___y_1198_);
lean_dec_ref(v___y_1197_);
lean_dec(v___y_1196_);
lean_dec_ref(v___y_1195_);
return v_res_1202_;
}
}
lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__5___redArg(lean_object* v_type_1203_, lean_object* v_k_1204_, uint8_t v_cleanupAnnotations_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_){
_start:
{
lean_object* v___f_1211_; uint8_t v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; 
v___f_1211_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__4___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1211_, 0, v_k_1204_);
v___x_1212_ = 0;
v___x_1213_ = lean_box(0);
v___x_1214_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_1212_, v___x_1213_, v_type_1203_, v___f_1211_, v_cleanupAnnotations_1205_, v___x_1212_, v___y_1206_, v___y_1207_, v___y_1208_, v___y_1209_);
if (lean_obj_tag(v___x_1214_) == 0)
{
lean_object* v_a_1215_; lean_object* v___x_1217_; uint8_t v_isShared_1218_; uint8_t v_isSharedCheck_1222_; 
v_a_1215_ = lean_ctor_get(v___x_1214_, 0);
v_isSharedCheck_1222_ = !lean_is_exclusive(v___x_1214_);
if (v_isSharedCheck_1222_ == 0)
{
v___x_1217_ = v___x_1214_;
v_isShared_1218_ = v_isSharedCheck_1222_;
goto v_resetjp_1216_;
}
else
{
lean_inc(v_a_1215_);
lean_dec(v___x_1214_);
v___x_1217_ = lean_box(0);
v_isShared_1218_ = v_isSharedCheck_1222_;
goto v_resetjp_1216_;
}
v_resetjp_1216_:
{
lean_object* v___x_1220_; 
if (v_isShared_1218_ == 0)
{
v___x_1220_ = v___x_1217_;
goto v_reusejp_1219_;
}
else
{
lean_object* v_reuseFailAlloc_1221_; 
v_reuseFailAlloc_1221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1221_, 0, v_a_1215_);
v___x_1220_ = v_reuseFailAlloc_1221_;
goto v_reusejp_1219_;
}
v_reusejp_1219_:
{
return v___x_1220_;
}
}
}
else
{
lean_object* v_a_1223_; lean_object* v___x_1225_; uint8_t v_isShared_1226_; uint8_t v_isSharedCheck_1230_; 
v_a_1223_ = lean_ctor_get(v___x_1214_, 0);
v_isSharedCheck_1230_ = !lean_is_exclusive(v___x_1214_);
if (v_isSharedCheck_1230_ == 0)
{
v___x_1225_ = v___x_1214_;
v_isShared_1226_ = v_isSharedCheck_1230_;
goto v_resetjp_1224_;
}
else
{
lean_inc(v_a_1223_);
lean_dec(v___x_1214_);
v___x_1225_ = lean_box(0);
v_isShared_1226_ = v_isSharedCheck_1230_;
goto v_resetjp_1224_;
}
v_resetjp_1224_:
{
lean_object* v___x_1228_; 
if (v_isShared_1226_ == 0)
{
v___x_1228_ = v___x_1225_;
goto v_reusejp_1227_;
}
else
{
lean_object* v_reuseFailAlloc_1229_; 
v_reuseFailAlloc_1229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1229_, 0, v_a_1223_);
v___x_1228_ = v_reuseFailAlloc_1229_;
goto v_reusejp_1227_;
}
v_reusejp_1227_:
{
return v___x_1228_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_1203_ = stack[0].m_obj;
lean_object* v_k_1204_ = stack[1].m_obj;
uint8_t v_cleanupAnnotations_1205_ = stack[2].m_num;
lean_object* v___y_1206_ = stack[3].m_obj;
lean_object* v___y_1207_ = stack[4].m_obj;
lean_object* v___y_1208_ = stack[5].m_obj;
lean_object* v___y_1209_ = stack[6].m_obj;
lean_object* v_res_1231_;
v_res_1231_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__5___redArg(v_type_1203_, v_k_1204_, v_cleanupAnnotations_1205_, v___y_1206_, v___y_1207_, v___y_1208_, v___y_1209_);
stack->m_obj
 = v_res_1231_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__5___redArg___boxed(lean_object* v_type_1232_, lean_object* v_k_1233_, lean_object* v_cleanupAnnotations_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1240_; lean_object* v_res_1241_; 
v_cleanupAnnotations_boxed_1240_ = lean_unbox(v_cleanupAnnotations_1234_);
v_res_1241_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__5___redArg(v_type_1232_, v_k_1233_, v_cleanupAnnotations_boxed_1240_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_);
lean_dec(v___y_1238_);
lean_dec_ref(v___y_1237_);
lean_dec(v___y_1236_);
lean_dec_ref(v___y_1235_);
return v_res_1241_;
}
}
lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__5(lean_object* v_00_u03b1_1242_, lean_object* v_type_1243_, lean_object* v_k_1244_, uint8_t v_cleanupAnnotations_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_){
_start:
{
lean_object* v___x_1251_; 
v___x_1251_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__5___redArg(v_type_1243_, v_k_1244_, v_cleanupAnnotations_1245_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_);
return v___x_1251_;
}
}
LEAN_EXPORT void l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_1243_ = stack[1].m_obj;
lean_object* v_k_1244_ = stack[2].m_obj;
uint8_t v_cleanupAnnotations_1245_ = stack[3].m_num;
lean_object* v___y_1246_ = stack[4].m_obj;
lean_object* v___y_1247_ = stack[5].m_obj;
lean_object* v___y_1248_ = stack[6].m_obj;
lean_object* v___y_1249_ = stack[7].m_obj;
lean_object* v_res_1252_;
v_res_1252_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__5(lean_box(0), v_type_1243_, v_k_1244_, v_cleanupAnnotations_1245_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_);
stack->m_obj
 = v_res_1252_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__5___boxed(lean_object* v_00_u03b1_1253_, lean_object* v_type_1254_, lean_object* v_k_1255_, lean_object* v_cleanupAnnotations_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1262_; lean_object* v_res_1263_; 
v_cleanupAnnotations_boxed_1262_ = lean_unbox(v_cleanupAnnotations_1256_);
v_res_1263_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__5(v_00_u03b1_1253_, v_type_1254_, v_k_1255_, v_cleanupAnnotations_boxed_1262_, v___y_1257_, v___y_1258_, v___y_1259_, v___y_1260_);
lean_dec(v___y_1260_);
lean_dec_ref(v___y_1259_);
lean_dec(v___y_1258_);
lean_dec_ref(v___y_1257_);
return v_res_1263_;
}
}
lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__0(lean_object* v_params_1264_, lean_object* v_fvars_1265_, lean_object* v_ty_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_){
_start:
{
lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; 
v___x_1272_ = lean_array_mk(v_params_1264_);
v___x_1273_ = l_Lean_Expr_replaceFVars(v_ty_1266_, v_fvars_1265_, v___x_1272_);
lean_dec_ref(v___x_1272_);
v___x_1274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1274_, 0, v___x_1273_);
return v___x_1274_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_params_1264_ = stack[0].m_obj;
lean_object* v_fvars_1265_ = stack[1].m_obj;
lean_object* v_ty_1266_ = stack[2].m_obj;
lean_object* v___y_1267_ = stack[3].m_obj;
lean_object* v___y_1268_ = stack[4].m_obj;
lean_object* v___y_1269_ = stack[5].m_obj;
lean_object* v___y_1270_ = stack[6].m_obj;
lean_object* v_res_1275_;
v_res_1275_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__0(v_params_1264_, v_fvars_1265_, v_ty_1266_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_);
stack->m_obj
 = v_res_1275_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__0___boxed(lean_object* v_params_1276_, lean_object* v_fvars_1277_, lean_object* v_ty_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_){
_start:
{
lean_object* v_res_1284_; 
v_res_1284_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__0(v_params_1276_, v_fvars_1277_, v_ty_1278_, v___y_1279_, v___y_1280_, v___y_1281_, v___y_1282_);
lean_dec(v___y_1282_);
lean_dec_ref(v___y_1281_);
lean_dec(v___y_1280_);
lean_dec_ref(v___y_1279_);
lean_dec_ref(v_ty_1278_);
lean_dec_ref(v_fvars_1277_);
return v_res_1284_;
}
}
lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__2(lean_object* v_x_1291_, lean_object* v_x_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_){
_start:
{
if (lean_obj_tag(v_x_1291_) == 0)
{
lean_object* v___x_1298_; lean_object* v___x_1299_; 
v___x_1298_ = l_List_reverse___redArg(v_x_1292_);
v___x_1299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1299_, 0, v___x_1298_);
return v___x_1299_;
}
else
{
lean_object* v_head_1300_; lean_object* v_tail_1301_; lean_object* v___x_1303_; uint8_t v_isShared_1304_; uint8_t v_isSharedCheck_1361_; 
v_head_1300_ = lean_ctor_get(v_x_1291_, 0);
v_tail_1301_ = lean_ctor_get(v_x_1291_, 1);
v_isSharedCheck_1361_ = !lean_is_exclusive(v_x_1291_);
if (v_isSharedCheck_1361_ == 0)
{
v___x_1303_ = v_x_1291_;
v_isShared_1304_ = v_isSharedCheck_1361_;
goto v_resetjp_1302_;
}
else
{
lean_inc(v_tail_1301_);
lean_inc(v_head_1300_);
lean_dec(v_x_1291_);
v___x_1303_ = lean_box(0);
v_isShared_1304_ = v_isSharedCheck_1361_;
goto v_resetjp_1302_;
}
v_resetjp_1302_:
{
lean_object* v_a_1306_; lean_object* v___y_1312_; lean_object* v_fst_1322_; lean_object* v_snd_1323_; lean_object* v___x_1325_; uint8_t v_isShared_1326_; uint8_t v_isSharedCheck_1360_; 
v_fst_1322_ = lean_ctor_get(v_head_1300_, 0);
v_snd_1323_ = lean_ctor_get(v_head_1300_, 1);
v_isSharedCheck_1360_ = !lean_is_exclusive(v_head_1300_);
if (v_isSharedCheck_1360_ == 0)
{
v___x_1325_ = v_head_1300_;
v_isShared_1326_ = v_isSharedCheck_1360_;
goto v_resetjp_1324_;
}
else
{
lean_inc(v_snd_1323_);
lean_inc(v_fst_1322_);
lean_dec(v_head_1300_);
v___x_1325_ = lean_box(0);
v_isShared_1326_ = v_isSharedCheck_1360_;
goto v_resetjp_1324_;
}
v___jp_1305_:
{
lean_object* v___x_1308_; 
if (v_isShared_1304_ == 0)
{
lean_ctor_set(v___x_1303_, 1, v_x_1292_);
lean_ctor_set(v___x_1303_, 0, v_a_1306_);
v___x_1308_ = v___x_1303_;
goto v_reusejp_1307_;
}
else
{
lean_object* v_reuseFailAlloc_1310_; 
v_reuseFailAlloc_1310_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1310_, 0, v_a_1306_);
lean_ctor_set(v_reuseFailAlloc_1310_, 1, v_x_1292_);
v___x_1308_ = v_reuseFailAlloc_1310_;
goto v_reusejp_1307_;
}
v_reusejp_1307_:
{
v_x_1291_ = v_tail_1301_;
v_x_1292_ = v___x_1308_;
goto _start;
}
}
v___jp_1311_:
{
if (lean_obj_tag(v___y_1312_) == 0)
{
lean_object* v_a_1313_; 
v_a_1313_ = lean_ctor_get(v___y_1312_, 0);
lean_inc(v_a_1313_);
lean_dec_ref_known(v___y_1312_, 1);
v_a_1306_ = v_a_1313_;
goto v___jp_1305_;
}
else
{
lean_object* v_a_1314_; lean_object* v___x_1316_; uint8_t v_isShared_1317_; uint8_t v_isSharedCheck_1321_; 
lean_del_object(v___x_1303_);
lean_dec(v_tail_1301_);
lean_dec(v_x_1292_);
v_a_1314_ = lean_ctor_get(v___y_1312_, 0);
v_isSharedCheck_1321_ = !lean_is_exclusive(v___y_1312_);
if (v_isSharedCheck_1321_ == 0)
{
v___x_1316_ = v___y_1312_;
v_isShared_1317_ = v_isSharedCheck_1321_;
goto v_resetjp_1315_;
}
else
{
lean_inc(v_a_1314_);
lean_dec(v___y_1312_);
v___x_1316_ = lean_box(0);
v_isShared_1317_ = v_isSharedCheck_1321_;
goto v_resetjp_1315_;
}
v_resetjp_1315_:
{
lean_object* v___x_1319_; 
if (v_isShared_1317_ == 0)
{
v___x_1319_ = v___x_1316_;
goto v_reusejp_1318_;
}
else
{
lean_object* v_reuseFailAlloc_1320_; 
v_reuseFailAlloc_1320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1320_, 0, v_a_1314_);
v___x_1319_ = v_reuseFailAlloc_1320_;
goto v_reusejp_1318_;
}
v_reusejp_1318_:
{
return v___x_1319_;
}
}
}
}
v_resetjp_1324_:
{
lean_object* v___x_1327_; lean_object* v___x_1328_; 
v___x_1327_ = l_Lean_Expr_fvarId_x21(v_fst_1322_);
v___x_1328_ = l_Lean_FVarId_getType___redArg(v___x_1327_, v___y_1293_, v___y_1295_, v___y_1296_);
if (lean_obj_tag(v___x_1328_) == 0)
{
lean_object* v_a_1329_; lean_object* v___x_1330_; 
v_a_1329_ = lean_ctor_get(v___x_1328_, 0);
lean_inc(v_a_1329_);
lean_dec_ref_known(v___x_1328_, 1);
lean_inc(v___y_1296_);
lean_inc_ref(v___y_1295_);
lean_inc(v___y_1294_);
lean_inc_ref(v___y_1293_);
lean_inc(v_snd_1323_);
v___x_1330_ = lean_infer_type(v_snd_1323_, v___y_1293_, v___y_1294_, v___y_1295_, v___y_1296_);
if (lean_obj_tag(v___x_1330_) == 0)
{
lean_object* v_a_1331_; lean_object* v___x_1332_; 
v_a_1331_ = lean_ctor_get(v___x_1330_, 0);
lean_inc(v_a_1331_);
lean_dec_ref_known(v___x_1330_, 1);
lean_inc(v___y_1296_);
lean_inc_ref(v___y_1295_);
lean_inc(v___y_1294_);
lean_inc_ref(v___y_1293_);
lean_inc(v_a_1329_);
v___x_1332_ = lean_infer_type(v_a_1329_, v___y_1293_, v___y_1294_, v___y_1295_, v___y_1296_);
if (lean_obj_tag(v___x_1332_) == 0)
{
lean_object* v_a_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; 
v_a_1333_ = lean_ctor_get(v___x_1332_, 0);
lean_inc(v_a_1333_);
lean_dec_ref_known(v___x_1332_, 1);
v___x_1334_ = l_Lean_Expr_sortLevel_x21(v_a_1333_);
lean_dec(v_a_1333_);
lean_inc(v_a_1331_);
lean_inc(v_a_1329_);
v___x_1335_ = l_Lean_Meta_isExprDefEq(v_a_1329_, v_a_1331_, v___y_1293_, v___y_1294_, v___y_1295_, v___y_1296_);
if (lean_obj_tag(v___x_1335_) == 0)
{
lean_object* v_a_1336_; uint8_t v___x_1337_; 
v_a_1336_ = lean_ctor_get(v___x_1335_, 0);
lean_inc(v_a_1336_);
lean_dec_ref_known(v___x_1335_, 1);
v___x_1337_ = lean_unbox(v_a_1336_);
lean_dec(v_a_1336_);
if (v___x_1337_ == 0)
{
lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1341_; 
v___x_1338_ = ((lean_object*)(l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__2___closed__1));
v___x_1339_ = lean_box(0);
if (v_isShared_1326_ == 0)
{
lean_ctor_set_tag(v___x_1325_, 1);
lean_ctor_set(v___x_1325_, 1, v___x_1339_);
lean_ctor_set(v___x_1325_, 0, v___x_1334_);
v___x_1341_ = v___x_1325_;
goto v_reusejp_1340_;
}
else
{
lean_object* v_reuseFailAlloc_1344_; 
v_reuseFailAlloc_1344_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1344_, 0, v___x_1334_);
lean_ctor_set(v_reuseFailAlloc_1344_, 1, v___x_1339_);
v___x_1341_ = v_reuseFailAlloc_1344_;
goto v_reusejp_1340_;
}
v_reusejp_1340_:
{
lean_object* v___x_1342_; lean_object* v___x_1343_; 
v___x_1342_ = l_Lean_Expr_const___override(v___x_1338_, v___x_1341_);
v___x_1343_ = l_Lean_mkApp4(v___x_1342_, v_a_1329_, v_fst_1322_, v_a_1331_, v_snd_1323_);
v_a_1306_ = v___x_1343_;
goto v___jp_1305_;
}
}
else
{
lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1348_; 
lean_dec(v_a_1331_);
v___x_1345_ = ((lean_object*)(l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__2___closed__3));
v___x_1346_ = lean_box(0);
if (v_isShared_1326_ == 0)
{
lean_ctor_set_tag(v___x_1325_, 1);
lean_ctor_set(v___x_1325_, 1, v___x_1346_);
lean_ctor_set(v___x_1325_, 0, v___x_1334_);
v___x_1348_ = v___x_1325_;
goto v_reusejp_1347_;
}
else
{
lean_object* v_reuseFailAlloc_1351_; 
v_reuseFailAlloc_1351_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1351_, 0, v___x_1334_);
lean_ctor_set(v_reuseFailAlloc_1351_, 1, v___x_1346_);
v___x_1348_ = v_reuseFailAlloc_1351_;
goto v_reusejp_1347_;
}
v_reusejp_1347_:
{
lean_object* v___x_1349_; lean_object* v___x_1350_; 
v___x_1349_ = l_Lean_Expr_const___override(v___x_1345_, v___x_1348_);
v___x_1350_ = l_Lean_mkApp3(v___x_1349_, v_a_1329_, v_fst_1322_, v_snd_1323_);
v_a_1306_ = v___x_1350_;
goto v___jp_1305_;
}
}
}
else
{
lean_object* v_a_1352_; lean_object* v___x_1354_; uint8_t v_isShared_1355_; uint8_t v_isSharedCheck_1359_; 
lean_dec(v___x_1334_);
lean_dec(v_a_1331_);
lean_dec(v_a_1329_);
lean_del_object(v___x_1325_);
lean_dec(v_snd_1323_);
lean_dec(v_fst_1322_);
lean_del_object(v___x_1303_);
lean_dec(v_tail_1301_);
lean_dec(v_x_1292_);
v_a_1352_ = lean_ctor_get(v___x_1335_, 0);
v_isSharedCheck_1359_ = !lean_is_exclusive(v___x_1335_);
if (v_isSharedCheck_1359_ == 0)
{
v___x_1354_ = v___x_1335_;
v_isShared_1355_ = v_isSharedCheck_1359_;
goto v_resetjp_1353_;
}
else
{
lean_inc(v_a_1352_);
lean_dec(v___x_1335_);
v___x_1354_ = lean_box(0);
v_isShared_1355_ = v_isSharedCheck_1359_;
goto v_resetjp_1353_;
}
v_resetjp_1353_:
{
lean_object* v___x_1357_; 
if (v_isShared_1355_ == 0)
{
v___x_1357_ = v___x_1354_;
goto v_reusejp_1356_;
}
else
{
lean_object* v_reuseFailAlloc_1358_; 
v_reuseFailAlloc_1358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1358_, 0, v_a_1352_);
v___x_1357_ = v_reuseFailAlloc_1358_;
goto v_reusejp_1356_;
}
v_reusejp_1356_:
{
return v___x_1357_;
}
}
}
}
else
{
lean_dec(v_a_1331_);
lean_dec(v_a_1329_);
lean_del_object(v___x_1325_);
lean_dec(v_snd_1323_);
lean_dec(v_fst_1322_);
v___y_1312_ = v___x_1332_;
goto v___jp_1311_;
}
}
else
{
lean_dec(v_a_1329_);
lean_del_object(v___x_1325_);
lean_dec(v_snd_1323_);
lean_dec(v_fst_1322_);
v___y_1312_ = v___x_1330_;
goto v___jp_1311_;
}
}
else
{
lean_del_object(v___x_1325_);
lean_dec(v_snd_1323_);
lean_dec(v_fst_1322_);
v___y_1312_ = v___x_1328_;
goto v___jp_1311_;
}
}
}
}
}
}
LEAN_EXPORT void l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1291_ = stack[0].m_obj;
lean_object* v_x_1292_ = stack[1].m_obj;
lean_object* v___y_1293_ = stack[2].m_obj;
lean_object* v___y_1294_ = stack[3].m_obj;
lean_object* v___y_1295_ = stack[4].m_obj;
lean_object* v___y_1296_ = stack[5].m_obj;
lean_object* v_res_1362_;
v_res_1362_ = l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__2(v_x_1291_, v_x_1292_, v___y_1293_, v___y_1294_, v___y_1295_, v___y_1296_);
stack->m_obj
 = v_res_1362_;
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__2___boxed(lean_object* v_x_1363_, lean_object* v_x_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_){
_start:
{
lean_object* v_res_1370_; 
v_res_1370_ = l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__2(v_x_1363_, v_x_1364_, v___y_1365_, v___y_1366_, v___y_1367_, v___y_1368_);
lean_dec(v___y_1368_);
lean_dec_ref(v___y_1367_);
lean_dec(v___y_1366_);
lean_dec_ref(v___y_1365_);
return v_res_1370_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__3(lean_object* v_a_1371_, lean_object* v_a_1372_){
_start:
{
if (lean_obj_tag(v_a_1371_) == 0)
{
lean_object* v___x_1373_; 
v___x_1373_ = lean_array_to_list(v_a_1372_);
return v___x_1373_;
}
else
{
lean_object* v_head_1374_; 
v_head_1374_ = lean_ctor_get(v_a_1371_, 0);
if (lean_obj_tag(v_head_1374_) == 0)
{
lean_object* v_tail_1375_; 
v_tail_1375_ = lean_ctor_get(v_a_1371_, 1);
lean_inc(v_tail_1375_);
lean_dec_ref_known(v_a_1371_, 2);
v_a_1371_ = v_tail_1375_;
goto _start;
}
else
{
lean_object* v_tail_1377_; lean_object* v_val_1378_; lean_object* v___x_1379_; 
lean_inc_ref(v_head_1374_);
v_tail_1377_ = lean_ctor_get(v_a_1371_, 1);
lean_inc(v_tail_1377_);
lean_dec_ref_known(v_a_1371_, 2);
v_val_1378_ = lean_ctor_get(v_head_1374_, 0);
lean_inc(v_val_1378_);
lean_dec_ref_known(v_head_1374_, 1);
v___x_1379_ = lean_array_push(v_a_1372_, v_val_1378_);
v_a_1371_ = v_tail_1377_;
v_a_1372_ = v___x_1379_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__1(lean_object* v_a_1381_, lean_object* v_a_1382_){
_start:
{
if (lean_obj_tag(v_a_1381_) == 0)
{
lean_object* v___x_1383_; 
v___x_1383_ = l_List_reverse___redArg(v_a_1382_);
return v___x_1383_;
}
else
{
lean_object* v_head_1384_; lean_object* v_tail_1385_; lean_object* v___x_1387_; uint8_t v_isShared_1388_; uint8_t v_isSharedCheck_1398_; 
v_head_1384_ = lean_ctor_get(v_a_1381_, 0);
v_tail_1385_ = lean_ctor_get(v_a_1381_, 1);
v_isSharedCheck_1398_ = !lean_is_exclusive(v_a_1381_);
if (v_isSharedCheck_1398_ == 0)
{
v___x_1387_ = v_a_1381_;
v_isShared_1388_ = v_isSharedCheck_1398_;
goto v_resetjp_1386_;
}
else
{
lean_inc(v_tail_1385_);
lean_inc(v_head_1384_);
lean_dec(v_a_1381_);
v___x_1387_ = lean_box(0);
v_isShared_1388_ = v_isSharedCheck_1398_;
goto v_resetjp_1386_;
}
v_resetjp_1386_:
{
uint8_t v___y_1390_; 
if (lean_obj_tag(v_head_1384_) == 0)
{
uint8_t v___x_1396_; 
v___x_1396_ = 0;
v___y_1390_ = v___x_1396_;
goto v___jp_1389_;
}
else
{
uint8_t v___x_1397_; 
lean_dec_ref_known(v_head_1384_, 1);
v___x_1397_ = 1;
v___y_1390_ = v___x_1397_;
goto v___jp_1389_;
}
v___jp_1389_:
{
lean_object* v___x_1391_; lean_object* v___x_1393_; 
v___x_1391_ = lean_box(v___y_1390_);
if (v_isShared_1388_ == 0)
{
lean_ctor_set(v___x_1387_, 1, v_a_1382_);
lean_ctor_set(v___x_1387_, 0, v___x_1391_);
v___x_1393_ = v___x_1387_;
goto v_reusejp_1392_;
}
else
{
lean_object* v_reuseFailAlloc_1395_; 
v_reuseFailAlloc_1395_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1395_, 0, v___x_1391_);
lean_ctor_set(v_reuseFailAlloc_1395_, 1, v_a_1382_);
v___x_1393_ = v_reuseFailAlloc_1395_;
goto v_reusejp_1392_;
}
v_reusejp_1392_:
{
v_a_1381_ = v_tail_1385_;
v_a_1382_ = v___x_1393_;
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
lean_object* v___x_1399_; lean_object* v_dummy_1400_; 
v___x_1399_ = lean_box(0);
v_dummy_1400_ = l_Lean_Expr_sort___override(v___x_1399_);
return v_dummy_1400_;
}
}
static lean_object* _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__1___closed__3(void){
_start:
{
lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; 
v___x_1405_ = lean_box(0);
v___x_1406_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkAndList___closed__1));
v___x_1407_ = l_Lean_mkConst(v___x_1406_, v___x_1405_);
return v___x_1407_;
}
}
lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__1(lean_object* v___x_1408_, lean_object* v_idxs_1409_, lean_object* v___x_1410_, lean_object* v_fvars_1411_, lean_object* v_ty_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_){
_start:
{
lean_object* v___x_1418_; lean_object* v_dummy_1419_; lean_object* v_nargs_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v_fst_1430_; lean_object* v_snd_1431_; lean_object* v___x_1433_; uint8_t v_isShared_1434_; uint8_t v_isSharedCheck_1532_; 
v___x_1418_ = lean_box(0);
v_dummy_1419_ = lean_obj_once(&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__1___closed__0, &l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__1___closed__0_once, _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__1___closed__0);
v_nargs_1420_ = l_Lean_Expr_getAppNumArgs(v_ty_1412_);
lean_inc(v_nargs_1420_);
v___x_1421_ = lean_mk_array(v_nargs_1420_, v_dummy_1419_);
v___x_1422_ = lean_unsigned_to_nat(1u);
v___x_1423_ = lean_nat_sub(v_nargs_1420_, v___x_1422_);
lean_dec(v_nargs_1420_);
v___x_1424_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_ty_1412_, v___x_1421_, v___x_1423_);
v___x_1425_ = lean_array_to_list(v___x_1424_);
v___x_1426_ = l_List_drop___redArg(v___x_1408_, v___x_1425_);
lean_dec(v___x_1425_);
v___x_1427_ = lean_array_to_list(v_fvars_1411_);
v___x_1428_ = l_List_zipWith___at___00List_zip_spec__0(lean_box(0), lean_box(0), v_idxs_1409_, v___x_1426_);
v___x_1429_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_compactRelation(v___x_1427_, v___x_1428_);
v_fst_1430_ = lean_ctor_get(v___x_1429_, 0);
v_snd_1431_ = lean_ctor_get(v___x_1429_, 1);
v_isSharedCheck_1532_ = !lean_is_exclusive(v___x_1429_);
if (v_isSharedCheck_1532_ == 0)
{
v___x_1433_ = v___x_1429_;
v_isShared_1434_ = v_isSharedCheck_1532_;
goto v_resetjp_1432_;
}
else
{
lean_inc(v_snd_1431_);
lean_inc(v_fst_1430_);
lean_dec(v___x_1429_);
v___x_1433_ = lean_box(0);
v_isShared_1434_ = v_isSharedCheck_1532_;
goto v_resetjp_1432_;
}
v_resetjp_1432_:
{
lean_object* v_fst_1436_; lean_object* v_snd_1437_; lean_object* v_fst_1445_; lean_object* v_snd_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; 
v_fst_1445_ = lean_ctor_get(v_snd_1431_, 0);
lean_inc(v_fst_1445_);
v_snd_1446_ = lean_ctor_get(v_snd_1431_, 1);
lean_inc(v_snd_1446_);
lean_dec(v_snd_1431_);
v___x_1447_ = lean_box(0);
v___x_1448_ = l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__2(v_fst_1445_, v___x_1447_, v___y_1413_, v___y_1414_, v___y_1415_, v___y_1416_);
if (lean_obj_tag(v___x_1448_) == 0)
{
lean_object* v_a_1449_; lean_object* v_bs_x27_1451_; lean_object* v___y_1452_; lean_object* v___y_1453_; lean_object* v___y_1454_; lean_object* v___y_1455_; lean_object* v___x_1470_; lean_object* v___x_1471_; 
v_a_1449_ = lean_ctor_get(v___x_1448_, 0);
lean_inc(v_a_1449_);
lean_dec_ref_known(v___x_1448_, 1);
v___x_1470_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__1___closed__1));
lean_inc(v_fst_1430_);
v___x_1471_ = l_List_filterMapTR_go___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__3(v_fst_1430_, v___x_1470_);
if (lean_obj_tag(v___x_1471_) == 0)
{
if (lean_obj_tag(v_a_1449_) == 0)
{
lean_object* v___x_1472_; lean_object* v___x_1473_; 
lean_dec(v_snd_1446_);
v___x_1472_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__1___closed__2));
v___x_1473_ = lean_obj_once(&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__1___closed__3, &l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__1___closed__3_once, _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__1___closed__3);
v_fst_1436_ = v___x_1472_;
v_snd_1437_ = v___x_1473_;
goto v___jp_1435_;
}
else
{
v_bs_x27_1451_ = v___x_1471_;
v___y_1452_ = v___y_1413_;
v___y_1453_ = v___y_1414_;
v___y_1454_ = v___y_1415_;
v___y_1455_ = v___y_1416_;
goto v___jp_1450_;
}
}
else
{
if (lean_obj_tag(v_a_1449_) == 0)
{
lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; 
v___x_1474_ = l_List_getLast_x21___redArg(v___x_1410_, v___x_1471_);
v___x_1475_ = l_Lean_Expr_fvarId_x21(v___x_1474_);
lean_dec(v___x_1474_);
v___x_1476_ = l_Lean_FVarId_getType___redArg(v___x_1475_, v___y_1413_, v___y_1415_, v___y_1416_);
if (lean_obj_tag(v___x_1476_) == 0)
{
lean_object* v_a_1477_; lean_object* v___x_1478_; 
v_a_1477_ = lean_ctor_get(v___x_1476_, 0);
lean_inc_n(v_a_1477_, 2);
lean_dec_ref_known(v___x_1476_, 1);
lean_inc(v___y_1416_);
lean_inc_ref(v___y_1415_);
lean_inc(v___y_1414_);
lean_inc_ref(v___y_1413_);
v___x_1478_ = lean_infer_type(v_a_1477_, v___y_1413_, v___y_1414_, v___y_1415_, v___y_1416_);
if (lean_obj_tag(v___x_1478_) == 0)
{
lean_object* v_a_1479_; lean_object* v___x_1480_; uint8_t v___x_1481_; 
v_a_1479_ = lean_ctor_get(v___x_1478_, 0);
lean_inc(v_a_1479_);
lean_dec_ref_known(v___x_1478_, 1);
v___x_1480_ = l_Lean_Expr_sortLevel_x21(v_a_1479_);
lean_dec(v_a_1479_);
v___x_1481_ = lean_level_eq(v___x_1480_, v___x_1418_);
lean_dec(v___x_1480_);
if (v___x_1481_ == 0)
{
lean_object* v___x_1482_; lean_object* v___x_1483_; 
lean_dec(v_a_1477_);
v___x_1482_ = lean_obj_once(&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__1___closed__3, &l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__1___closed__3_once, _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__1___closed__3);
v___x_1483_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkExistsList(v___x_1471_, v___x_1482_, v___y_1413_, v___y_1414_, v___y_1415_, v___y_1416_);
if (lean_obj_tag(v___x_1483_) == 0)
{
lean_object* v_a_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; 
v_a_1484_ = lean_ctor_get(v___x_1483_, 0);
lean_inc(v_a_1484_);
lean_dec_ref_known(v___x_1483_, 1);
v___x_1485_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__1___closed__2));
v___x_1486_ = lean_apply_1(v_snd_1446_, v_a_1484_);
v_fst_1436_ = v___x_1485_;
v_snd_1437_ = v___x_1486_;
goto v___jp_1435_;
}
else
{
lean_object* v_a_1487_; lean_object* v___x_1489_; uint8_t v_isShared_1490_; uint8_t v_isSharedCheck_1494_; 
lean_dec(v_snd_1446_);
lean_del_object(v___x_1433_);
lean_dec(v_fst_1430_);
v_a_1487_ = lean_ctor_get(v___x_1483_, 0);
v_isSharedCheck_1494_ = !lean_is_exclusive(v___x_1483_);
if (v_isSharedCheck_1494_ == 0)
{
v___x_1489_ = v___x_1483_;
v_isShared_1490_ = v_isSharedCheck_1494_;
goto v_resetjp_1488_;
}
else
{
lean_inc(v_a_1487_);
lean_dec(v___x_1483_);
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
lean_object* v___x_1495_; lean_object* v___x_1496_; 
v___x_1495_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_List_init___redArg(v___x_1471_);
v___x_1496_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkExistsList(v___x_1495_, v_a_1477_, v___y_1413_, v___y_1414_, v___y_1415_, v___y_1416_);
if (lean_obj_tag(v___x_1496_) == 0)
{
lean_object* v_a_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; 
v_a_1497_ = lean_ctor_get(v___x_1496_, 0);
lean_inc(v_a_1497_);
lean_dec_ref_known(v___x_1496_, 1);
v___x_1498_ = lean_box(0);
v___x_1499_ = lean_apply_1(v_snd_1446_, v_a_1497_);
v_fst_1436_ = v___x_1498_;
v_snd_1437_ = v___x_1499_;
goto v___jp_1435_;
}
else
{
lean_object* v_a_1500_; lean_object* v___x_1502_; uint8_t v_isShared_1503_; uint8_t v_isSharedCheck_1507_; 
lean_dec(v_snd_1446_);
lean_del_object(v___x_1433_);
lean_dec(v_fst_1430_);
v_a_1500_ = lean_ctor_get(v___x_1496_, 0);
v_isSharedCheck_1507_ = !lean_is_exclusive(v___x_1496_);
if (v_isSharedCheck_1507_ == 0)
{
v___x_1502_ = v___x_1496_;
v_isShared_1503_ = v_isSharedCheck_1507_;
goto v_resetjp_1501_;
}
else
{
lean_inc(v_a_1500_);
lean_dec(v___x_1496_);
v___x_1502_ = lean_box(0);
v_isShared_1503_ = v_isSharedCheck_1507_;
goto v_resetjp_1501_;
}
v_resetjp_1501_:
{
lean_object* v___x_1505_; 
if (v_isShared_1503_ == 0)
{
v___x_1505_ = v___x_1502_;
goto v_reusejp_1504_;
}
else
{
lean_object* v_reuseFailAlloc_1506_; 
v_reuseFailAlloc_1506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1506_, 0, v_a_1500_);
v___x_1505_ = v_reuseFailAlloc_1506_;
goto v_reusejp_1504_;
}
v_reusejp_1504_:
{
return v___x_1505_;
}
}
}
}
}
else
{
lean_object* v_a_1508_; lean_object* v___x_1510_; uint8_t v_isShared_1511_; uint8_t v_isSharedCheck_1515_; 
lean_dec(v_a_1477_);
lean_dec(v___x_1471_);
lean_dec(v_snd_1446_);
lean_del_object(v___x_1433_);
lean_dec(v_fst_1430_);
v_a_1508_ = lean_ctor_get(v___x_1478_, 0);
v_isSharedCheck_1515_ = !lean_is_exclusive(v___x_1478_);
if (v_isSharedCheck_1515_ == 0)
{
v___x_1510_ = v___x_1478_;
v_isShared_1511_ = v_isSharedCheck_1515_;
goto v_resetjp_1509_;
}
else
{
lean_inc(v_a_1508_);
lean_dec(v___x_1478_);
v___x_1510_ = lean_box(0);
v_isShared_1511_ = v_isSharedCheck_1515_;
goto v_resetjp_1509_;
}
v_resetjp_1509_:
{
lean_object* v___x_1513_; 
if (v_isShared_1511_ == 0)
{
v___x_1513_ = v___x_1510_;
goto v_reusejp_1512_;
}
else
{
lean_object* v_reuseFailAlloc_1514_; 
v_reuseFailAlloc_1514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1514_, 0, v_a_1508_);
v___x_1513_ = v_reuseFailAlloc_1514_;
goto v_reusejp_1512_;
}
v_reusejp_1512_:
{
return v___x_1513_;
}
}
}
}
else
{
lean_object* v_a_1516_; lean_object* v___x_1518_; uint8_t v_isShared_1519_; uint8_t v_isSharedCheck_1523_; 
lean_dec(v___x_1471_);
lean_dec(v_snd_1446_);
lean_del_object(v___x_1433_);
lean_dec(v_fst_1430_);
v_a_1516_ = lean_ctor_get(v___x_1476_, 0);
v_isSharedCheck_1523_ = !lean_is_exclusive(v___x_1476_);
if (v_isSharedCheck_1523_ == 0)
{
v___x_1518_ = v___x_1476_;
v_isShared_1519_ = v_isSharedCheck_1523_;
goto v_resetjp_1517_;
}
else
{
lean_inc(v_a_1516_);
lean_dec(v___x_1476_);
v___x_1518_ = lean_box(0);
v_isShared_1519_ = v_isSharedCheck_1523_;
goto v_resetjp_1517_;
}
v_resetjp_1517_:
{
lean_object* v___x_1521_; 
if (v_isShared_1519_ == 0)
{
v___x_1521_ = v___x_1518_;
goto v_reusejp_1520_;
}
else
{
lean_object* v_reuseFailAlloc_1522_; 
v_reuseFailAlloc_1522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1522_, 0, v_a_1516_);
v___x_1521_ = v_reuseFailAlloc_1522_;
goto v_reusejp_1520_;
}
v_reusejp_1520_:
{
return v___x_1521_;
}
}
}
}
else
{
v_bs_x27_1451_ = v___x_1471_;
v___y_1452_ = v___y_1413_;
v___y_1453_ = v___y_1414_;
v___y_1454_ = v___y_1415_;
v___y_1455_ = v___y_1416_;
goto v___jp_1450_;
}
}
v___jp_1450_:
{
lean_object* v___x_1456_; lean_object* v___x_1457_; 
lean_inc(v_a_1449_);
v___x_1456_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkAndList(v_a_1449_);
v___x_1457_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkExistsList(v_bs_x27_1451_, v___x_1456_, v___y_1452_, v___y_1453_, v___y_1454_, v___y_1455_);
if (lean_obj_tag(v___x_1457_) == 0)
{
lean_object* v_a_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; 
v_a_1458_ = lean_ctor_get(v___x_1457_, 0);
lean_inc(v_a_1458_);
lean_dec_ref_known(v___x_1457_, 1);
v___x_1459_ = l_List_lengthTR___redArg(v_a_1449_);
lean_dec(v_a_1449_);
v___x_1460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1460_, 0, v___x_1459_);
v___x_1461_ = lean_apply_1(v_snd_1446_, v_a_1458_);
v_fst_1436_ = v___x_1460_;
v_snd_1437_ = v___x_1461_;
goto v___jp_1435_;
}
else
{
lean_object* v_a_1462_; lean_object* v___x_1464_; uint8_t v_isShared_1465_; uint8_t v_isSharedCheck_1469_; 
lean_dec(v_a_1449_);
lean_dec(v_snd_1446_);
lean_del_object(v___x_1433_);
lean_dec(v_fst_1430_);
v_a_1462_ = lean_ctor_get(v___x_1457_, 0);
v_isSharedCheck_1469_ = !lean_is_exclusive(v___x_1457_);
if (v_isSharedCheck_1469_ == 0)
{
v___x_1464_ = v___x_1457_;
v_isShared_1465_ = v_isSharedCheck_1469_;
goto v_resetjp_1463_;
}
else
{
lean_inc(v_a_1462_);
lean_dec(v___x_1457_);
v___x_1464_ = lean_box(0);
v_isShared_1465_ = v_isSharedCheck_1469_;
goto v_resetjp_1463_;
}
v_resetjp_1463_:
{
lean_object* v___x_1467_; 
if (v_isShared_1465_ == 0)
{
v___x_1467_ = v___x_1464_;
goto v_reusejp_1466_;
}
else
{
lean_object* v_reuseFailAlloc_1468_; 
v_reuseFailAlloc_1468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1468_, 0, v_a_1462_);
v___x_1467_ = v_reuseFailAlloc_1468_;
goto v_reusejp_1466_;
}
v_reusejp_1466_:
{
return v___x_1467_;
}
}
}
}
}
else
{
lean_object* v_a_1524_; lean_object* v___x_1526_; uint8_t v_isShared_1527_; uint8_t v_isSharedCheck_1531_; 
lean_dec(v_snd_1446_);
lean_del_object(v___x_1433_);
lean_dec(v_fst_1430_);
v_a_1524_ = lean_ctor_get(v___x_1448_, 0);
v_isSharedCheck_1531_ = !lean_is_exclusive(v___x_1448_);
if (v_isSharedCheck_1531_ == 0)
{
v___x_1526_ = v___x_1448_;
v_isShared_1527_ = v_isSharedCheck_1531_;
goto v_resetjp_1525_;
}
else
{
lean_inc(v_a_1524_);
lean_dec(v___x_1448_);
v___x_1526_ = lean_box(0);
v_isShared_1527_ = v_isSharedCheck_1531_;
goto v_resetjp_1525_;
}
v_resetjp_1525_:
{
lean_object* v___x_1529_; 
if (v_isShared_1527_ == 0)
{
v___x_1529_ = v___x_1526_;
goto v_reusejp_1528_;
}
else
{
lean_object* v_reuseFailAlloc_1530_; 
v_reuseFailAlloc_1530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1530_, 0, v_a_1524_);
v___x_1529_ = v_reuseFailAlloc_1530_;
goto v_reusejp_1528_;
}
v_reusejp_1528_:
{
return v___x_1529_;
}
}
}
v___jp_1435_:
{
lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1442_; 
v___x_1438_ = lean_box(0);
v___x_1439_ = l_List_mapTR_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__1(v_fst_1430_, v___x_1438_);
v___x_1440_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1440_, 0, v___x_1439_);
lean_ctor_set(v___x_1440_, 1, v_fst_1436_);
if (v_isShared_1434_ == 0)
{
lean_ctor_set(v___x_1433_, 1, v_snd_1437_);
lean_ctor_set(v___x_1433_, 0, v___x_1440_);
v___x_1442_ = v___x_1433_;
goto v_reusejp_1441_;
}
else
{
lean_object* v_reuseFailAlloc_1444_; 
v_reuseFailAlloc_1444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1444_, 0, v___x_1440_);
lean_ctor_set(v_reuseFailAlloc_1444_, 1, v_snd_1437_);
v___x_1442_ = v_reuseFailAlloc_1444_;
goto v_reusejp_1441_;
}
v_reusejp_1441_:
{
lean_object* v___x_1443_; 
v___x_1443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1443_, 0, v___x_1442_);
return v___x_1443_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1408_ = stack[0].m_obj;
lean_object* v_idxs_1409_ = stack[1].m_obj;
lean_object* v___x_1410_ = stack[2].m_obj;
lean_object* v_fvars_1411_ = stack[3].m_obj;
lean_object* v_ty_1412_ = stack[4].m_obj;
lean_object* v___y_1413_ = stack[5].m_obj;
lean_object* v___y_1414_ = stack[6].m_obj;
lean_object* v___y_1415_ = stack[7].m_obj;
lean_object* v___y_1416_ = stack[8].m_obj;
lean_object* v_res_1533_;
v_res_1533_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__1(v___x_1408_, v_idxs_1409_, v___x_1410_, v_fvars_1411_, v_ty_1412_, v___y_1413_, v___y_1414_, v___y_1415_, v___y_1416_);
stack->m_obj
 = v_res_1533_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__1___boxed(lean_object* v___x_1534_, lean_object* v_idxs_1535_, lean_object* v___x_1536_, lean_object* v_fvars_1537_, lean_object* v_ty_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_){
_start:
{
lean_object* v_res_1544_; 
v_res_1544_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__1(v___x_1534_, v_idxs_1535_, v___x_1536_, v_fvars_1537_, v_ty_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_);
lean_dec(v___y_1542_);
lean_dec_ref(v___y_1541_);
lean_dec(v___y_1540_);
lean_dec_ref(v___y_1539_);
lean_dec_ref(v___x_1536_);
return v_res_1544_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__9___redArg(lean_object* v_ref_1545_, lean_object* v_msg_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_){
_start:
{
lean_object* v_toCold_1552_; lean_object* v_currRecDepth_1553_; lean_object* v_ref_1554_; uint16_t v_optionFlags_1555_; uint8_t v_suppressElabErrors_1556_; uint8_t v_isRecordingDeps_1557_; lean_object* v_ref_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; 
v_toCold_1552_ = lean_ctor_get(v___y_1549_, 0);
v_currRecDepth_1553_ = lean_ctor_get(v___y_1549_, 1);
v_ref_1554_ = lean_ctor_get(v___y_1549_, 2);
v_optionFlags_1555_ = lean_ctor_get_uint16(v___y_1549_, sizeof(void*)*3);
v_suppressElabErrors_1556_ = lean_ctor_get_uint8(v___y_1549_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1557_ = lean_ctor_get_uint8(v___y_1549_, sizeof(void*)*3 + 3);
v_ref_1558_ = l_Lean_replaceRef(v_ref_1545_, v_ref_1554_);
lean_inc(v_currRecDepth_1553_);
lean_inc_ref(v_toCold_1552_);
v___x_1559_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1559_, 0, v_toCold_1552_);
lean_ctor_set(v___x_1559_, 1, v_currRecDepth_1553_);
lean_ctor_set(v___x_1559_, 2, v_ref_1558_);
lean_ctor_set_uint16(v___x_1559_, sizeof(void*)*3, v_optionFlags_1555_);
lean_ctor_set_uint8(v___x_1559_, sizeof(void*)*3 + 2, v_suppressElabErrors_1556_);
lean_ctor_set_uint8(v___x_1559_, sizeof(void*)*3 + 3, v_isRecordingDeps_1557_);
v___x_1560_ = l_Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0___redArg(v_msg_1546_, v___y_1547_, v___y_1548_, v___x_1559_, v___y_1550_);
lean_dec_ref_known(v___x_1559_, 3);
return v___x_1560_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__9___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1545_ = stack[0].m_obj;
lean_object* v_msg_1546_ = stack[1].m_obj;
lean_object* v___y_1547_ = stack[2].m_obj;
lean_object* v___y_1548_ = stack[3].m_obj;
lean_object* v___y_1549_ = stack[4].m_obj;
lean_object* v___y_1550_ = stack[5].m_obj;
lean_object* v_res_1561_;
v_res_1561_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__9___redArg(v_ref_1545_, v_msg_1546_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_);
stack->m_obj
 = v_res_1561_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__9___redArg___boxed(lean_object* v_ref_1562_, lean_object* v_msg_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_){
_start:
{
lean_object* v_res_1569_; 
v_res_1569_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__9___redArg(v_ref_1562_, v_msg_1563_, v___y_1564_, v___y_1565_, v___y_1566_, v___y_1567_);
lean_dec(v___y_1567_);
lean_dec_ref(v___y_1566_);
lean_dec(v___y_1565_);
lean_dec_ref(v___y_1564_);
lean_dec(v_ref_1562_);
return v_res_1569_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__0(void){
_start:
{
lean_object* v___x_1570_; 
v___x_1570_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1570_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__1(void){
_start:
{
lean_object* v___x_1571_; lean_object* v___x_1572_; 
v___x_1571_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__0);
v___x_1572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1572_, 0, v___x_1571_);
return v___x_1572_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__2(void){
_start:
{
lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; 
v___x_1573_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_1574_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__1);
v___x_1575_ = lean_unsigned_to_nat(0u);
v___x_1576_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_1576_, 0, v___x_1575_);
lean_ctor_set(v___x_1576_, 1, v___x_1575_);
lean_ctor_set(v___x_1576_, 2, v___x_1575_);
lean_ctor_set(v___x_1576_, 3, v___x_1575_);
lean_ctor_set(v___x_1576_, 4, v___x_1574_);
lean_ctor_set(v___x_1576_, 5, v___x_1574_);
lean_ctor_set(v___x_1576_, 6, v___x_1574_);
lean_ctor_set(v___x_1576_, 7, v___x_1574_);
lean_ctor_set(v___x_1576_, 8, v___x_1574_);
lean_ctor_set(v___x_1576_, 9, v___x_1574_);
lean_ctor_set(v___x_1576_, 10, v___x_1574_);
lean_ctor_set(v___x_1576_, 11, v___x_1573_);
return v___x_1576_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__3(void){
_start:
{
lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; 
v___x_1577_ = lean_unsigned_to_nat(32u);
v___x_1578_ = lean_mk_empty_array_with_capacity(v___x_1577_);
v___x_1579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1579_, 0, v___x_1578_);
return v___x_1579_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__4(void){
_start:
{
size_t v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; 
v___x_1580_ = ((size_t)5ULL);
v___x_1581_ = lean_unsigned_to_nat(0u);
v___x_1582_ = lean_unsigned_to_nat(32u);
v___x_1583_ = lean_mk_empty_array_with_capacity(v___x_1582_);
v___x_1584_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__3);
v___x_1585_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1585_, 0, v___x_1584_);
lean_ctor_set(v___x_1585_, 1, v___x_1583_);
lean_ctor_set(v___x_1585_, 2, v___x_1581_);
lean_ctor_set(v___x_1585_, 3, v___x_1581_);
lean_ctor_set_usize(v___x_1585_, 4, v___x_1580_);
return v___x_1585_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__5(void){
_start:
{
lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; 
v___x_1586_ = lean_box(1);
v___x_1587_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__4);
v___x_1588_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__1);
v___x_1589_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1589_, 0, v___x_1588_);
lean_ctor_set(v___x_1589_, 1, v___x_1587_);
lean_ctor_set(v___x_1589_, 2, v___x_1586_);
return v___x_1589_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__7(void){
_start:
{
lean_object* v___x_1591_; lean_object* v___x_1592_; 
v___x_1591_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__6));
v___x_1592_ = l_Lean_stringToMessageData(v___x_1591_);
return v___x_1592_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__9(void){
_start:
{
lean_object* v___x_1594_; lean_object* v___x_1595_; 
v___x_1594_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__8));
v___x_1595_ = l_Lean_stringToMessageData(v___x_1594_);
return v___x_1595_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__11(void){
_start:
{
lean_object* v___x_1597_; lean_object* v___x_1598_; 
v___x_1597_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__10));
v___x_1598_ = l_Lean_stringToMessageData(v___x_1597_);
return v___x_1598_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__13(void){
_start:
{
lean_object* v___x_1600_; lean_object* v___x_1601_; 
v___x_1600_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__12));
v___x_1601_ = l_Lean_stringToMessageData(v___x_1600_);
return v___x_1601_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__15(void){
_start:
{
lean_object* v___x_1603_; lean_object* v___x_1604_; 
v___x_1603_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__14));
v___x_1604_ = l_Lean_stringToMessageData(v___x_1603_);
return v___x_1604_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__17(void){
_start:
{
lean_object* v___x_1606_; lean_object* v___x_1607_; 
v___x_1606_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__16));
v___x_1607_ = l_Lean_stringToMessageData(v___x_1606_);
return v___x_1607_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__19(void){
_start:
{
lean_object* v___x_1609_; lean_object* v___x_1610_; 
v___x_1609_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__18));
v___x_1610_ = l_Lean_stringToMessageData(v___x_1609_);
return v___x_1610_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__21(void){
_start:
{
lean_object* v___x_1612_; lean_object* v___x_1613_; 
v___x_1612_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__20));
v___x_1613_ = l_Lean_stringToMessageData(v___x_1612_);
return v___x_1613_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__23(void){
_start:
{
lean_object* v___x_1615_; lean_object* v___x_1616_; 
v___x_1615_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__22));
v___x_1616_ = l_Lean_stringToMessageData(v___x_1615_);
return v___x_1616_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__25(void){
_start:
{
lean_object* v___x_1618_; lean_object* v___x_1619_; 
v___x_1618_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__24));
v___x_1619_ = l_Lean_stringToMessageData(v___x_1618_);
return v___x_1619_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__27(void){
_start:
{
lean_object* v___x_1621_; lean_object* v___x_1622_; 
v___x_1621_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__26));
v___x_1622_ = l_Lean_stringToMessageData(v___x_1621_);
return v___x_1622_;
}
}
lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg(lean_object* v_msg_1623_, lean_object* v_declHint_1624_, lean_object* v___y_1625_){
_start:
{
lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v_env_1629_; uint8_t v___x_1630_; 
v___x_1627_ = lean_box(0);
v___x_1628_ = lean_st_ref_get(v___y_1625_);
v_env_1629_ = lean_ctor_get(v___x_1628_, 0);
lean_inc_ref(v_env_1629_);
lean_dec(v___x_1628_);
v___x_1630_ = l_Lean_Name_isAnonymous(v_declHint_1624_);
if (v___x_1630_ == 0)
{
uint8_t v_isExporting_1631_; 
v_isExporting_1631_ = lean_ctor_get_uint8(v_env_1629_, sizeof(void*)*13);
if (v_isExporting_1631_ == 0)
{
lean_object* v___x_1632_; 
lean_dec_ref(v_env_1629_);
lean_dec(v_declHint_1624_);
v___x_1632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1632_, 0, v_msg_1623_);
return v___x_1632_;
}
else
{
lean_object* v___x_1633_; uint8_t v___x_1634_; 
lean_inc_ref(v_env_1629_);
v___x_1633_ = l_Lean_Environment_setExporting(v_env_1629_, v___x_1630_);
lean_inc(v_declHint_1624_);
lean_inc_ref(v___x_1633_);
v___x_1634_ = l_Lean_Environment_contains(v___x_1633_, v_declHint_1624_, v_isExporting_1631_);
if (v___x_1634_ == 0)
{
lean_object* v___x_1635_; 
lean_dec_ref(v___x_1633_);
lean_dec_ref(v_env_1629_);
lean_dec(v_declHint_1624_);
v___x_1635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1635_, 0, v_msg_1623_);
return v___x_1635_;
}
else
{
lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v_c_1641_; lean_object* v___x_1642_; 
v___x_1636_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__2);
v___x_1637_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__5);
v___x_1638_ = l_Lean_Options_empty;
v___x_1639_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1639_, 0, v___x_1633_);
lean_ctor_set(v___x_1639_, 1, v___x_1636_);
lean_ctor_set(v___x_1639_, 2, v___x_1637_);
lean_ctor_set(v___x_1639_, 3, v___x_1638_);
lean_inc(v_declHint_1624_);
v___x_1640_ = l_Lean_MessageData_ofConstName(v_declHint_1624_, v___x_1630_);
v_c_1641_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1641_, 0, v___x_1639_);
lean_ctor_set(v_c_1641_, 1, v___x_1640_);
v___x_1642_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1629_, v_declHint_1624_);
if (lean_obj_tag(v___x_1642_) == 0)
{
lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; 
lean_dec_ref(v_env_1629_);
lean_dec(v_declHint_1624_);
v___x_1643_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__7);
v___x_1644_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1644_, 0, v___x_1643_);
lean_ctor_set(v___x_1644_, 1, v_c_1641_);
v___x_1645_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__9);
v___x_1646_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1646_, 0, v___x_1644_);
lean_ctor_set(v___x_1646_, 1, v___x_1645_);
v___x_1647_ = l_Lean_MessageData_note(v___x_1646_);
v___x_1648_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1648_, 0, v_msg_1623_);
lean_ctor_set(v___x_1648_, 1, v___x_1647_);
v___x_1649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1649_, 0, v___x_1648_);
return v___x_1649_;
}
else
{
lean_object* v_val_1650_; lean_object* v___x_1652_; uint8_t v_isShared_1653_; uint8_t v_isSharedCheck_1706_; 
v_val_1650_ = lean_ctor_get(v___x_1642_, 0);
v_isSharedCheck_1706_ = !lean_is_exclusive(v___x_1642_);
if (v_isSharedCheck_1706_ == 0)
{
v___x_1652_ = v___x_1642_;
v_isShared_1653_ = v_isSharedCheck_1706_;
goto v_resetjp_1651_;
}
else
{
lean_inc(v_val_1650_);
lean_dec(v___x_1642_);
v___x_1652_ = lean_box(0);
v_isShared_1653_ = v_isSharedCheck_1706_;
goto v_resetjp_1651_;
}
v_resetjp_1651_:
{
lean_object* v___x_1654_; lean_object* v_modules_1655_; lean_object* v_moduleNames_1656_; lean_object* v_mod_1657_; uint8_t v___y_1659_; uint8_t v___x_1689_; 
v___x_1654_ = l_Lean_Environment_header(v_env_1629_);
lean_dec_ref(v_env_1629_);
v_modules_1655_ = lean_ctor_get(v___x_1654_, 3);
lean_inc_ref(v_modules_1655_);
v_moduleNames_1656_ = lean_ctor_get(v___x_1654_, 4);
lean_inc_ref(v_moduleNames_1656_);
lean_dec_ref(v___x_1654_);
v_mod_1657_ = lean_array_get(v___x_1627_, v_moduleNames_1656_, v_val_1650_);
lean_dec_ref(v_moduleNames_1656_);
v___x_1689_ = l_Lean_isPrivateName(v_declHint_1624_);
lean_dec(v_declHint_1624_);
if (v___x_1689_ == 0)
{
lean_object* v___x_1690_; uint8_t v___x_1691_; 
v___x_1690_ = lean_array_get_size(v_modules_1655_);
v___x_1691_ = lean_nat_dec_lt(v_val_1650_, v___x_1690_);
if (v___x_1691_ == 0)
{
lean_dec_ref(v_modules_1655_);
lean_dec(v_val_1650_);
v___y_1659_ = v___x_1689_;
goto v___jp_1658_;
}
else
{
lean_object* v___x_1692_; lean_object* v_toImport_1693_; uint8_t v_isExported_1694_; 
v___x_1692_ = lean_array_fget(v_modules_1655_, v_val_1650_);
lean_dec(v_val_1650_);
lean_dec_ref(v_modules_1655_);
v_toImport_1693_ = lean_ctor_get(v___x_1692_, 0);
lean_inc_ref(v_toImport_1693_);
lean_dec(v___x_1692_);
v_isExported_1694_ = lean_ctor_get_uint8(v_toImport_1693_, sizeof(void*)*1 + 1);
lean_dec_ref(v_toImport_1693_);
v___y_1659_ = v_isExported_1694_;
goto v___jp_1658_;
}
}
else
{
lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; 
lean_dec_ref(v_modules_1655_);
lean_del_object(v___x_1652_);
lean_dec(v_val_1650_);
v___x_1695_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__7);
v___x_1696_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1696_, 0, v___x_1695_);
lean_ctor_set(v___x_1696_, 1, v_c_1641_);
v___x_1697_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__25, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__25_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__25);
v___x_1698_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1698_, 0, v___x_1696_);
lean_ctor_set(v___x_1698_, 1, v___x_1697_);
v___x_1699_ = l_Lean_MessageData_ofName(v_mod_1657_);
v___x_1700_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1700_, 0, v___x_1698_);
lean_ctor_set(v___x_1700_, 1, v___x_1699_);
v___x_1701_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__27, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__27_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__27);
v___x_1702_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1702_, 0, v___x_1700_);
lean_ctor_set(v___x_1702_, 1, v___x_1701_);
v___x_1703_ = l_Lean_MessageData_note(v___x_1702_);
v___x_1704_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1704_, 0, v_msg_1623_);
lean_ctor_set(v___x_1704_, 1, v___x_1703_);
v___x_1705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1705_, 0, v___x_1704_);
return v___x_1705_;
}
v___jp_1658_:
{
if (v___y_1659_ == 0)
{
lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1671_; 
v___x_1660_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__11);
v___x_1661_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1661_, 0, v___x_1660_);
lean_ctor_set(v___x_1661_, 1, v_c_1641_);
v___x_1662_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__13);
v___x_1663_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1663_, 0, v___x_1661_);
lean_ctor_set(v___x_1663_, 1, v___x_1662_);
v___x_1664_ = l_Lean_MessageData_ofName(v_mod_1657_);
v___x_1665_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1665_, 0, v___x_1663_);
lean_ctor_set(v___x_1665_, 1, v___x_1664_);
v___x_1666_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__15);
v___x_1667_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1667_, 0, v___x_1665_);
lean_ctor_set(v___x_1667_, 1, v___x_1666_);
v___x_1668_ = l_Lean_MessageData_note(v___x_1667_);
v___x_1669_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1669_, 0, v_msg_1623_);
lean_ctor_set(v___x_1669_, 1, v___x_1668_);
if (v_isShared_1653_ == 0)
{
lean_ctor_set_tag(v___x_1652_, 0);
lean_ctor_set(v___x_1652_, 0, v___x_1669_);
v___x_1671_ = v___x_1652_;
goto v_reusejp_1670_;
}
else
{
lean_object* v_reuseFailAlloc_1672_; 
v_reuseFailAlloc_1672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1672_, 0, v___x_1669_);
v___x_1671_ = v_reuseFailAlloc_1672_;
goto v_reusejp_1670_;
}
v_reusejp_1670_:
{
return v___x_1671_;
}
}
else
{
lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1687_; 
v___x_1673_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__17);
v___x_1674_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1674_, 0, v___x_1673_);
lean_ctor_set(v___x_1674_, 1, v_c_1641_);
v___x_1675_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__19);
v___x_1676_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1676_, 0, v___x_1674_);
lean_ctor_set(v___x_1676_, 1, v___x_1675_);
v___x_1677_ = l_Lean_MessageData_ofName(v_mod_1657_);
lean_inc_ref(v___x_1677_);
v___x_1678_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1678_, 0, v___x_1676_);
lean_ctor_set(v___x_1678_, 1, v___x_1677_);
v___x_1679_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__21, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__21_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__21);
v___x_1680_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1680_, 0, v___x_1678_);
lean_ctor_set(v___x_1680_, 1, v___x_1679_);
v___x_1681_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1681_, 0, v___x_1680_);
lean_ctor_set(v___x_1681_, 1, v___x_1677_);
v___x_1682_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__23, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__23_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__23);
v___x_1683_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1683_, 0, v___x_1681_);
lean_ctor_set(v___x_1683_, 1, v___x_1682_);
v___x_1684_ = l_Lean_MessageData_note(v___x_1683_);
v___x_1685_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1685_, 0, v_msg_1623_);
lean_ctor_set(v___x_1685_, 1, v___x_1684_);
if (v_isShared_1653_ == 0)
{
lean_ctor_set_tag(v___x_1652_, 0);
lean_ctor_set(v___x_1652_, 0, v___x_1685_);
v___x_1687_ = v___x_1652_;
goto v_reusejp_1686_;
}
else
{
lean_object* v_reuseFailAlloc_1688_; 
v_reuseFailAlloc_1688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1688_, 0, v___x_1685_);
v___x_1687_ = v_reuseFailAlloc_1688_;
goto v_reusejp_1686_;
}
v_reusejp_1686_:
{
return v___x_1687_;
}
}
}
}
}
}
}
}
else
{
lean_object* v___x_1707_; 
lean_dec_ref(v_env_1629_);
lean_dec(v_declHint_1624_);
v___x_1707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1707_, 0, v_msg_1623_);
return v___x_1707_;
}
}
}
LEAN_EXPORT void l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1623_ = stack[0].m_obj;
lean_object* v_declHint_1624_ = stack[1].m_obj;
lean_object* v___y_1625_ = stack[2].m_obj;
lean_object* v_res_1708_;
v_res_1708_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg(v_msg_1623_, v_declHint_1624_, v___y_1625_);
stack->m_obj
 = v_res_1708_;
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___boxed(lean_object* v_msg_1709_, lean_object* v_declHint_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_){
_start:
{
lean_object* v_res_1713_; 
v_res_1713_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg(v_msg_1709_, v_declHint_1710_, v___y_1711_);
lean_dec(v___y_1711_);
return v_res_1713_;
}
}
lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8(lean_object* v_msg_1714_, lean_object* v_declHint_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_){
_start:
{
lean_object* v___x_1721_; lean_object* v_a_1722_; lean_object* v___x_1724_; uint8_t v_isShared_1725_; uint8_t v_isSharedCheck_1731_; 
v___x_1721_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg(v_msg_1714_, v_declHint_1715_, v___y_1719_);
v_a_1722_ = lean_ctor_get(v___x_1721_, 0);
v_isSharedCheck_1731_ = !lean_is_exclusive(v___x_1721_);
if (v_isSharedCheck_1731_ == 0)
{
v___x_1724_ = v___x_1721_;
v_isShared_1725_ = v_isSharedCheck_1731_;
goto v_resetjp_1723_;
}
else
{
lean_inc(v_a_1722_);
lean_dec(v___x_1721_);
v___x_1724_ = lean_box(0);
v_isShared_1725_ = v_isSharedCheck_1731_;
goto v_resetjp_1723_;
}
v_resetjp_1723_:
{
lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1729_; 
v___x_1726_ = l_Lean_unknownIdentifierMessageTag;
v___x_1727_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1727_, 0, v___x_1726_);
lean_ctor_set(v___x_1727_, 1, v_a_1722_);
if (v_isShared_1725_ == 0)
{
lean_ctor_set(v___x_1724_, 0, v___x_1727_);
v___x_1729_ = v___x_1724_;
goto v_reusejp_1728_;
}
else
{
lean_object* v_reuseFailAlloc_1730_; 
v_reuseFailAlloc_1730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1730_, 0, v___x_1727_);
v___x_1729_ = v_reuseFailAlloc_1730_;
goto v_reusejp_1728_;
}
v_reusejp_1728_:
{
return v___x_1729_;
}
}
}
}
LEAN_EXPORT void l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1714_ = stack[0].m_obj;
lean_object* v_declHint_1715_ = stack[1].m_obj;
lean_object* v___y_1716_ = stack[2].m_obj;
lean_object* v___y_1717_ = stack[3].m_obj;
lean_object* v___y_1718_ = stack[4].m_obj;
lean_object* v___y_1719_ = stack[5].m_obj;
lean_object* v_res_1732_;
v_res_1732_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8(v_msg_1714_, v_declHint_1715_, v___y_1716_, v___y_1717_, v___y_1718_, v___y_1719_);
stack->m_obj
 = v_res_1732_;
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8___boxed(lean_object* v_msg_1733_, lean_object* v_declHint_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_){
_start:
{
lean_object* v_res_1740_; 
v_res_1740_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8(v_msg_1733_, v_declHint_1734_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_);
lean_dec(v___y_1738_);
lean_dec_ref(v___y_1737_);
lean_dec(v___y_1736_);
lean_dec_ref(v___y_1735_);
return v_res_1740_;
}
}
lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7___redArg(lean_object* v_ref_1741_, lean_object* v_msg_1742_, lean_object* v_declHint_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_){
_start:
{
lean_object* v___x_1749_; lean_object* v_a_1750_; lean_object* v___x_1751_; 
v___x_1749_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8(v_msg_1742_, v_declHint_1743_, v___y_1744_, v___y_1745_, v___y_1746_, v___y_1747_);
v_a_1750_ = lean_ctor_get(v___x_1749_, 0);
lean_inc(v_a_1750_);
lean_dec_ref(v___x_1749_);
v___x_1751_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__9___redArg(v_ref_1741_, v_a_1750_, v___y_1744_, v___y_1745_, v___y_1746_, v___y_1747_);
return v___x_1751_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1741_ = stack[0].m_obj;
lean_object* v_msg_1742_ = stack[1].m_obj;
lean_object* v_declHint_1743_ = stack[2].m_obj;
lean_object* v___y_1744_ = stack[3].m_obj;
lean_object* v___y_1745_ = stack[4].m_obj;
lean_object* v___y_1746_ = stack[5].m_obj;
lean_object* v___y_1747_ = stack[6].m_obj;
lean_object* v_res_1752_;
v_res_1752_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7___redArg(v_ref_1741_, v_msg_1742_, v_declHint_1743_, v___y_1744_, v___y_1745_, v___y_1746_, v___y_1747_);
stack->m_obj
 = v_res_1752_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7___redArg___boxed(lean_object* v_ref_1753_, lean_object* v_msg_1754_, lean_object* v_declHint_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_){
_start:
{
lean_object* v_res_1761_; 
v_res_1761_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7___redArg(v_ref_1753_, v_msg_1754_, v_declHint_1755_, v___y_1756_, v___y_1757_, v___y_1758_, v___y_1759_);
lean_dec(v___y_1759_);
lean_dec_ref(v___y_1758_);
lean_dec(v___y_1757_);
lean_dec_ref(v___y_1756_);
lean_dec(v_ref_1753_);
return v_res_1761_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_1763_; lean_object* v___x_1764_; 
v___x_1763_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3___redArg___closed__0));
v___x_1764_ = l_Lean_stringToMessageData(v___x_1763_);
return v___x_1764_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_1766_; lean_object* v___x_1767_; 
v___x_1766_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3___redArg___closed__2));
v___x_1767_ = l_Lean_stringToMessageData(v___x_1766_);
return v___x_1767_;
}
}
lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3___redArg(lean_object* v_ref_1768_, lean_object* v_constName_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_){
_start:
{
lean_object* v___x_1775_; uint8_t v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; 
v___x_1775_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3___redArg___closed__1);
v___x_1776_ = 0;
lean_inc(v_constName_1769_);
v___x_1777_ = l_Lean_MessageData_ofConstName(v_constName_1769_, v___x_1776_);
v___x_1778_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1778_, 0, v___x_1775_);
lean_ctor_set(v___x_1778_, 1, v___x_1777_);
v___x_1779_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3___redArg___closed__3);
v___x_1780_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1780_, 0, v___x_1778_);
lean_ctor_set(v___x_1780_, 1, v___x_1779_);
v___x_1781_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7___redArg(v_ref_1768_, v___x_1780_, v_constName_1769_, v___y_1770_, v___y_1771_, v___y_1772_, v___y_1773_);
return v___x_1781_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1768_ = stack[0].m_obj;
lean_object* v_constName_1769_ = stack[1].m_obj;
lean_object* v___y_1770_ = stack[2].m_obj;
lean_object* v___y_1771_ = stack[3].m_obj;
lean_object* v___y_1772_ = stack[4].m_obj;
lean_object* v___y_1773_ = stack[5].m_obj;
lean_object* v_res_1782_;
v_res_1782_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3___redArg(v_ref_1768_, v_constName_1769_, v___y_1770_, v___y_1771_, v___y_1772_, v___y_1773_);
stack->m_obj
 = v_res_1782_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_ref_1783_, lean_object* v_constName_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_){
_start:
{
lean_object* v_res_1790_; 
v_res_1790_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3___redArg(v_ref_1783_, v_constName_1784_, v___y_1785_, v___y_1786_, v___y_1787_, v___y_1788_);
lean_dec(v___y_1788_);
lean_dec_ref(v___y_1787_);
lean_dec(v___y_1786_);
lean_dec_ref(v___y_1785_);
lean_dec(v_ref_1783_);
return v_res_1790_;
}
}
lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0___redArg(lean_object* v_constName_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_){
_start:
{
lean_object* v_ref_1797_; lean_object* v___x_1798_; 
v_ref_1797_ = lean_ctor_get(v___y_1794_, 2);
v___x_1798_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3___redArg(v_ref_1797_, v_constName_1791_, v___y_1792_, v___y_1793_, v___y_1794_, v___y_1795_);
return v___x_1798_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_1791_ = stack[0].m_obj;
lean_object* v___y_1792_ = stack[1].m_obj;
lean_object* v___y_1793_ = stack[2].m_obj;
lean_object* v___y_1794_ = stack[3].m_obj;
lean_object* v___y_1795_ = stack[4].m_obj;
lean_object* v_res_1799_;
v_res_1799_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0___redArg(v_constName_1791_, v___y_1792_, v___y_1793_, v___y_1794_, v___y_1795_);
stack->m_obj
 = v_res_1799_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0___redArg___boxed(lean_object* v_constName_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_){
_start:
{
lean_object* v_res_1806_; 
v_res_1806_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0___redArg(v_constName_1800_, v___y_1801_, v___y_1802_, v___y_1803_, v___y_1804_);
lean_dec(v___y_1804_);
lean_dec_ref(v___y_1803_);
lean_dec(v___y_1802_);
lean_dec_ref(v___y_1801_);
return v_res_1806_;
}
}
lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0(lean_object* v_constName_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_){
_start:
{
lean_object* v___x_1813_; lean_object* v_env_1814_; uint8_t v___x_1815_; lean_object* v___x_1816_; 
v___x_1813_ = lean_st_ref_get(v___y_1811_);
v_env_1814_ = lean_ctor_get(v___x_1813_, 0);
lean_inc_ref(v_env_1814_);
lean_dec(v___x_1813_);
v___x_1815_ = 0;
lean_inc(v_constName_1807_);
v___x_1816_ = l_Lean_Environment_find_x3f(v_env_1814_, v_constName_1807_, v___x_1815_);
if (lean_obj_tag(v___x_1816_) == 0)
{
lean_object* v___x_1817_; 
v___x_1817_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0___redArg(v_constName_1807_, v___y_1808_, v___y_1809_, v___y_1810_, v___y_1811_);
return v___x_1817_;
}
else
{
lean_object* v_val_1818_; lean_object* v___x_1820_; uint8_t v_isShared_1821_; uint8_t v_isSharedCheck_1825_; 
lean_dec(v_constName_1807_);
v_val_1818_ = lean_ctor_get(v___x_1816_, 0);
v_isSharedCheck_1825_ = !lean_is_exclusive(v___x_1816_);
if (v_isSharedCheck_1825_ == 0)
{
v___x_1820_ = v___x_1816_;
v_isShared_1821_ = v_isSharedCheck_1825_;
goto v_resetjp_1819_;
}
else
{
lean_inc(v_val_1818_);
lean_dec(v___x_1816_);
v___x_1820_ = lean_box(0);
v_isShared_1821_ = v_isSharedCheck_1825_;
goto v_resetjp_1819_;
}
v_resetjp_1819_:
{
lean_object* v___x_1823_; 
if (v_isShared_1821_ == 0)
{
lean_ctor_set_tag(v___x_1820_, 0);
v___x_1823_ = v___x_1820_;
goto v_reusejp_1822_;
}
else
{
lean_object* v_reuseFailAlloc_1824_; 
v_reuseFailAlloc_1824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1824_, 0, v_val_1818_);
v___x_1823_ = v_reuseFailAlloc_1824_;
goto v_reusejp_1822_;
}
v_reusejp_1822_:
{
return v___x_1823_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_1807_ = stack[0].m_obj;
lean_object* v___y_1808_ = stack[1].m_obj;
lean_object* v___y_1809_ = stack[2].m_obj;
lean_object* v___y_1810_ = stack[3].m_obj;
lean_object* v___y_1811_ = stack[4].m_obj;
lean_object* v_res_1826_;
v_res_1826_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0(v_constName_1807_, v___y_1808_, v___y_1809_, v___y_1810_, v___y_1811_);
stack->m_obj
 = v_res_1826_;
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0___boxed(lean_object* v_constName_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_){
_start:
{
lean_object* v_res_1833_; 
v_res_1833_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0(v_constName_1827_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_);
lean_dec(v___y_1831_);
lean_dec_ref(v___y_1830_);
lean_dec(v___y_1829_);
lean_dec_ref(v___y_1828_);
return v_res_1833_;
}
}
lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp(lean_object* v_univs_1834_, lean_object* v_params_1835_, lean_object* v_idxs_1836_, lean_object* v_c_1837_, lean_object* v_a_1838_, lean_object* v_a_1839_, lean_object* v_a_1840_, lean_object* v_a_1841_){
_start:
{
lean_object* v___f_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; 
lean_inc(v_params_1835_);
v___f_1843_ = lean_alloc_closure((void*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1843_, 0, v_params_1835_);
v___x_1844_ = l_Lean_instInhabitedExpr;
v___x_1845_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0(v_c_1837_, v_a_1838_, v_a_1839_, v_a_1840_, v_a_1841_);
if (lean_obj_tag(v___x_1845_) == 0)
{
lean_object* v_a_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___f_1849_; lean_object* v___x_1850_; uint8_t v___x_1851_; lean_object* v___x_1852_; 
v_a_1846_ = lean_ctor_get(v___x_1845_, 0);
lean_inc(v_a_1846_);
lean_dec_ref_known(v___x_1845_, 1);
v___x_1847_ = l_Lean_ConstantInfo_instantiateTypeLevelParams(v_a_1846_, v_univs_1834_);
lean_dec(v_a_1846_);
v___x_1848_ = l_List_lengthTR___redArg(v_params_1835_);
lean_dec(v_params_1835_);
lean_inc(v___x_1848_);
v___f_1849_ = lean_alloc_closure((void*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__1___boxed), 10, 3);
lean_closure_set(v___f_1849_, 0, v___x_1848_);
lean_closure_set(v___f_1849_, 1, v_idxs_1836_);
lean_closure_set(v___f_1849_, 2, v___x_1844_);
v___x_1850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1850_, 0, v___x_1848_);
v___x_1851_ = 0;
v___x_1852_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__4___redArg(v___x_1847_, v___x_1850_, v___f_1843_, v___x_1851_, v___x_1851_, v_a_1838_, v_a_1839_, v_a_1840_, v_a_1841_);
if (lean_obj_tag(v___x_1852_) == 0)
{
lean_object* v_a_1853_; lean_object* v___x_1854_; 
v_a_1853_ = lean_ctor_get(v___x_1852_, 0);
lean_inc(v_a_1853_);
lean_dec_ref_known(v___x_1852_, 1);
v___x_1854_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__5___redArg(v_a_1853_, v___f_1849_, v___x_1851_, v_a_1838_, v_a_1839_, v_a_1840_, v_a_1841_);
return v___x_1854_;
}
else
{
lean_object* v_a_1855_; lean_object* v___x_1857_; uint8_t v_isShared_1858_; uint8_t v_isSharedCheck_1862_; 
lean_dec_ref(v___f_1849_);
v_a_1855_ = lean_ctor_get(v___x_1852_, 0);
v_isSharedCheck_1862_ = !lean_is_exclusive(v___x_1852_);
if (v_isSharedCheck_1862_ == 0)
{
v___x_1857_ = v___x_1852_;
v_isShared_1858_ = v_isSharedCheck_1862_;
goto v_resetjp_1856_;
}
else
{
lean_inc(v_a_1855_);
lean_dec(v___x_1852_);
v___x_1857_ = lean_box(0);
v_isShared_1858_ = v_isSharedCheck_1862_;
goto v_resetjp_1856_;
}
v_resetjp_1856_:
{
lean_object* v___x_1860_; 
if (v_isShared_1858_ == 0)
{
v___x_1860_ = v___x_1857_;
goto v_reusejp_1859_;
}
else
{
lean_object* v_reuseFailAlloc_1861_; 
v_reuseFailAlloc_1861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1861_, 0, v_a_1855_);
v___x_1860_ = v_reuseFailAlloc_1861_;
goto v_reusejp_1859_;
}
v_reusejp_1859_:
{
return v___x_1860_;
}
}
}
}
else
{
lean_object* v_a_1863_; lean_object* v___x_1865_; uint8_t v_isShared_1866_; uint8_t v_isSharedCheck_1870_; 
lean_dec_ref(v___f_1843_);
lean_dec(v_idxs_1836_);
lean_dec(v_params_1835_);
lean_dec(v_univs_1834_);
v_a_1863_ = lean_ctor_get(v___x_1845_, 0);
v_isSharedCheck_1870_ = !lean_is_exclusive(v___x_1845_);
if (v_isSharedCheck_1870_ == 0)
{
v___x_1865_ = v___x_1845_;
v_isShared_1866_ = v_isSharedCheck_1870_;
goto v_resetjp_1864_;
}
else
{
lean_inc(v_a_1863_);
lean_dec(v___x_1845_);
v___x_1865_ = lean_box(0);
v_isShared_1866_ = v_isSharedCheck_1870_;
goto v_resetjp_1864_;
}
v_resetjp_1864_:
{
lean_object* v___x_1868_; 
if (v_isShared_1866_ == 0)
{
v___x_1868_ = v___x_1865_;
goto v_reusejp_1867_;
}
else
{
lean_object* v_reuseFailAlloc_1869_; 
v_reuseFailAlloc_1869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1869_, 0, v_a_1863_);
v___x_1868_ = v_reuseFailAlloc_1869_;
goto v_reusejp_1867_;
}
v_reusejp_1867_:
{
return v___x_1868_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_0interp(lean_interpreter_value* stack)
{
lean_object* v_univs_1834_ = stack[0].m_obj;
lean_object* v_params_1835_ = stack[1].m_obj;
lean_object* v_idxs_1836_ = stack[2].m_obj;
lean_object* v_c_1837_ = stack[3].m_obj;
lean_object* v_a_1838_ = stack[4].m_obj;
lean_object* v_a_1839_ = stack[5].m_obj;
lean_object* v_a_1840_ = stack[6].m_obj;
lean_object* v_a_1841_ = stack[7].m_obj;
lean_object* v_res_1871_;
v_res_1871_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp(v_univs_1834_, v_params_1835_, v_idxs_1836_, v_c_1837_, v_a_1838_, v_a_1839_, v_a_1840_, v_a_1841_);
stack->m_obj
 = v_res_1871_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___boxed(lean_object* v_univs_1872_, lean_object* v_params_1873_, lean_object* v_idxs_1874_, lean_object* v_c_1875_, lean_object* v_a_1876_, lean_object* v_a_1877_, lean_object* v_a_1878_, lean_object* v_a_1879_, lean_object* v_a_1880_){
_start:
{
lean_object* v_res_1881_; 
v_res_1881_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp(v_univs_1872_, v_params_1873_, v_idxs_1874_, v_c_1875_, v_a_1876_, v_a_1877_, v_a_1878_, v_a_1879_);
lean_dec(v_a_1879_);
lean_dec_ref(v_a_1878_);
lean_dec(v_a_1877_);
lean_dec_ref(v_a_1876_);
return v_res_1881_;
}
}
lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0(lean_object* v_00_u03b1_1882_, lean_object* v_constName_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_){
_start:
{
lean_object* v___x_1889_; 
v___x_1889_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0___redArg(v_constName_1883_, v___y_1884_, v___y_1885_, v___y_1886_, v___y_1887_);
return v___x_1889_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_1883_ = stack[1].m_obj;
lean_object* v___y_1884_ = stack[2].m_obj;
lean_object* v___y_1885_ = stack[3].m_obj;
lean_object* v___y_1886_ = stack[4].m_obj;
lean_object* v___y_1887_ = stack[5].m_obj;
lean_object* v_res_1890_;
v_res_1890_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0(lean_box(0), v_constName_1883_, v___y_1884_, v___y_1885_, v___y_1886_, v___y_1887_);
stack->m_obj
 = v_res_1890_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1891_, lean_object* v_constName_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_){
_start:
{
lean_object* v_res_1898_; 
v_res_1898_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0(v_00_u03b1_1891_, v_constName_1892_, v___y_1893_, v___y_1894_, v___y_1895_, v___y_1896_);
lean_dec(v___y_1896_);
lean_dec_ref(v___y_1895_);
lean_dec(v___y_1894_);
lean_dec_ref(v___y_1893_);
return v_res_1898_;
}
}
lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3(lean_object* v_00_u03b1_1899_, lean_object* v_ref_1900_, lean_object* v_constName_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_){
_start:
{
lean_object* v___x_1907_; 
v___x_1907_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3___redArg(v_ref_1900_, v_constName_1901_, v___y_1902_, v___y_1903_, v___y_1904_, v___y_1905_);
return v___x_1907_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1900_ = stack[1].m_obj;
lean_object* v_constName_1901_ = stack[2].m_obj;
lean_object* v___y_1902_ = stack[3].m_obj;
lean_object* v___y_1903_ = stack[4].m_obj;
lean_object* v___y_1904_ = stack[5].m_obj;
lean_object* v___y_1905_ = stack[6].m_obj;
lean_object* v_res_1908_;
v_res_1908_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3(lean_box(0), v_ref_1900_, v_constName_1901_, v___y_1902_, v___y_1903_, v___y_1904_, v___y_1905_);
stack->m_obj
 = v_res_1908_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b1_1909_, lean_object* v_ref_1910_, lean_object* v_constName_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_){
_start:
{
lean_object* v_res_1917_; 
v_res_1917_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3(v_00_u03b1_1909_, v_ref_1910_, v_constName_1911_, v___y_1912_, v___y_1913_, v___y_1914_, v___y_1915_);
lean_dec(v___y_1915_);
lean_dec_ref(v___y_1914_);
lean_dec(v___y_1913_);
lean_dec_ref(v___y_1912_);
lean_dec(v_ref_1910_);
return v_res_1917_;
}
}
lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7(lean_object* v_00_u03b1_1918_, lean_object* v_ref_1919_, lean_object* v_msg_1920_, lean_object* v_declHint_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_){
_start:
{
lean_object* v___x_1927_; 
v___x_1927_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7___redArg(v_ref_1919_, v_msg_1920_, v_declHint_1921_, v___y_1922_, v___y_1923_, v___y_1924_, v___y_1925_);
return v___x_1927_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1919_ = stack[1].m_obj;
lean_object* v_msg_1920_ = stack[2].m_obj;
lean_object* v_declHint_1921_ = stack[3].m_obj;
lean_object* v___y_1922_ = stack[4].m_obj;
lean_object* v___y_1923_ = stack[5].m_obj;
lean_object* v___y_1924_ = stack[6].m_obj;
lean_object* v___y_1925_ = stack[7].m_obj;
lean_object* v_res_1928_;
v_res_1928_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7(lean_box(0), v_ref_1919_, v_msg_1920_, v_declHint_1921_, v___y_1922_, v___y_1923_, v___y_1924_, v___y_1925_);
stack->m_obj
 = v_res_1928_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7___boxed(lean_object* v_00_u03b1_1929_, lean_object* v_ref_1930_, lean_object* v_msg_1931_, lean_object* v_declHint_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_){
_start:
{
lean_object* v_res_1938_; 
v_res_1938_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7(v_00_u03b1_1929_, v_ref_1930_, v_msg_1931_, v_declHint_1932_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_);
lean_dec(v___y_1936_);
lean_dec_ref(v___y_1935_);
lean_dec(v___y_1934_);
lean_dec_ref(v___y_1933_);
lean_dec(v_ref_1930_);
return v_res_1938_;
}
}
lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9(lean_object* v_msg_1939_, lean_object* v_declHint_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_){
_start:
{
lean_object* v___x_1946_; 
v___x_1946_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg(v_msg_1939_, v_declHint_1940_, v___y_1944_);
return v___x_1946_;
}
}
LEAN_EXPORT void l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1939_ = stack[0].m_obj;
lean_object* v_declHint_1940_ = stack[1].m_obj;
lean_object* v___y_1941_ = stack[2].m_obj;
lean_object* v___y_1942_ = stack[3].m_obj;
lean_object* v___y_1943_ = stack[4].m_obj;
lean_object* v___y_1944_ = stack[5].m_obj;
lean_object* v_res_1947_;
v_res_1947_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9(v_msg_1939_, v_declHint_1940_, v___y_1941_, v___y_1942_, v___y_1943_, v___y_1944_);
stack->m_obj
 = v_res_1947_;
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___boxed(lean_object* v_msg_1948_, lean_object* v_declHint_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_){
_start:
{
lean_object* v_res_1955_; 
v_res_1955_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9(v_msg_1948_, v_declHint_1949_, v___y_1950_, v___y_1951_, v___y_1952_, v___y_1953_);
lean_dec(v___y_1953_);
lean_dec_ref(v___y_1952_);
lean_dec(v___y_1951_);
lean_dec_ref(v___y_1950_);
return v_res_1955_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__9(lean_object* v_00_u03b1_1956_, lean_object* v_ref_1957_, lean_object* v_msg_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_){
_start:
{
lean_object* v___x_1964_; 
v___x_1964_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__9___redArg(v_ref_1957_, v_msg_1958_, v___y_1959_, v___y_1960_, v___y_1961_, v___y_1962_);
return v___x_1964_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1957_ = stack[1].m_obj;
lean_object* v_msg_1958_ = stack[2].m_obj;
lean_object* v___y_1959_ = stack[3].m_obj;
lean_object* v___y_1960_ = stack[4].m_obj;
lean_object* v___y_1961_ = stack[5].m_obj;
lean_object* v___y_1962_ = stack[6].m_obj;
lean_object* v_res_1965_;
v_res_1965_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__9(lean_box(0), v_ref_1957_, v_msg_1958_, v___y_1959_, v___y_1960_, v___y_1961_, v___y_1962_);
stack->m_obj
 = v_res_1965_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__9___boxed(lean_object* v_00_u03b1_1966_, lean_object* v_ref_1967_, lean_object* v_msg_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_){
_start:
{
lean_object* v_res_1974_; 
v_res_1974_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__9(v_00_u03b1_1966_, v_ref_1967_, v_msg_1968_, v___y_1969_, v___y_1970_, v___y_1971_, v___y_1972_);
lean_dec(v___y_1972_);
lean_dec_ref(v___y_1971_);
lean_dec(v___y_1970_);
lean_dec_ref(v___y_1969_);
lean_dec(v_ref_1967_);
return v_res_1974_;
}
}
static lean_object* _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__1___closed__5(void){
_start:
{
lean_object* v___x_1988_; 
v___x_1988_ = l_Array_mkArray0___redArg();
return v___x_1988_;
}
}
lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__1(lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_){
_start:
{
lean_object* v_ref_1998_; uint8_t v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; 
v_ref_1998_ = lean_ctor_get(v___y_1995_, 2);
v___x_1999_ = 0;
v___x_2000_ = l_Lean_SourceInfo_fromRef(v_ref_1998_, v___x_1999_);
v___x_2001_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__1___closed__1));
v___x_2002_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__1___closed__2));
lean_inc_n(v___x_2000_, 3);
v___x_2003_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2003_, 0, v___x_2000_);
lean_ctor_set(v___x_2003_, 1, v___x_2002_);
v___x_2004_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__1___closed__4));
v___x_2005_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__10));
v___x_2006_ = lean_obj_once(&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__1___closed__5, &l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__1___closed__5_once, _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__1___closed__5);
v___x_2007_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2007_, 0, v___x_2000_);
lean_ctor_set(v___x_2007_, 1, v___x_2005_);
lean_ctor_set(v___x_2007_, 2, v___x_2006_);
v___x_2008_ = l_Lean_Syntax_node1(v___x_2000_, v___x_2004_, v___x_2007_);
v___x_2009_ = l_Lean_Syntax_node2(v___x_2000_, v___x_2001_, v___x_2003_, v___x_2008_);
v___x_2010_ = l_Lean_Elab_Tactic_evalTactic(v___x_2009_, v___y_1989_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_);
return v___x_2010_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_1989_ = stack[0].m_obj;
lean_object* v___y_1990_ = stack[1].m_obj;
lean_object* v___y_1991_ = stack[2].m_obj;
lean_object* v___y_1992_ = stack[3].m_obj;
lean_object* v___y_1993_ = stack[4].m_obj;
lean_object* v___y_1994_ = stack[5].m_obj;
lean_object* v___y_1995_ = stack[6].m_obj;
lean_object* v___y_1996_ = stack[7].m_obj;
lean_object* v_res_2011_;
v_res_2011_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__1(v___y_1989_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_);
stack->m_obj
 = v_res_2011_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__1___boxed(lean_object* v___y_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_){
_start:
{
lean_object* v_res_2021_; 
v_res_2021_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__1(v___y_2012_, v___y_2013_, v___y_2014_, v___y_2015_, v___y_2016_, v___y_2017_, v___y_2018_, v___y_2019_);
lean_dec(v___y_2019_);
lean_dec_ref(v___y_2018_);
lean_dec(v___y_2017_);
lean_dec_ref(v___y_2016_);
lean_dec(v___y_2015_);
lean_dec_ref(v___y_2014_);
lean_dec(v___y_2013_);
lean_dec_ref(v___y_2012_);
return v_res_2021_;
}
}
lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__0(uint8_t v_isZero_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_){
_start:
{
lean_object* v_ref_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; 
v_ref_2032_ = lean_ctor_get(v___y_2029_, 2);
v___x_2033_ = l_Lean_SourceInfo_fromRef(v_ref_2032_, v_isZero_2022_);
v___x_2034_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__1___closed__1));
v___x_2035_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__1___closed__2));
lean_inc_n(v___x_2033_, 3);
v___x_2036_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2036_, 0, v___x_2033_);
lean_ctor_set(v___x_2036_, 1, v___x_2035_);
v___x_2037_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__1___closed__4));
v___x_2038_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__10));
v___x_2039_ = lean_obj_once(&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__1___closed__5, &l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__1___closed__5_once, _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__1___closed__5);
v___x_2040_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2040_, 0, v___x_2033_);
lean_ctor_set(v___x_2040_, 1, v___x_2038_);
lean_ctor_set(v___x_2040_, 2, v___x_2039_);
v___x_2041_ = l_Lean_Syntax_node1(v___x_2033_, v___x_2037_, v___x_2040_);
v___x_2042_ = l_Lean_Syntax_node2(v___x_2033_, v___x_2034_, v___x_2036_, v___x_2041_);
v___x_2043_ = l_Lean_Elab_Tactic_evalTactic(v___x_2042_, v___y_2023_, v___y_2024_, v___y_2025_, v___y_2026_, v___y_2027_, v___y_2028_, v___y_2029_, v___y_2030_);
return v___x_2043_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_isZero_2022_ = stack[0].m_num;
lean_object* v___y_2023_ = stack[1].m_obj;
lean_object* v___y_2024_ = stack[2].m_obj;
lean_object* v___y_2025_ = stack[3].m_obj;
lean_object* v___y_2026_ = stack[4].m_obj;
lean_object* v___y_2027_ = stack[5].m_obj;
lean_object* v___y_2028_ = stack[6].m_obj;
lean_object* v___y_2029_ = stack[7].m_obj;
lean_object* v___y_2030_ = stack[8].m_obj;
lean_object* v_res_2044_;
v_res_2044_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__0(v_isZero_2022_, v___y_2023_, v___y_2024_, v___y_2025_, v___y_2026_, v___y_2027_, v___y_2028_, v___y_2029_, v___y_2030_);
stack->m_obj
 = v_res_2044_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__0___boxed(lean_object* v_isZero_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_){
_start:
{
uint8_t v_isZero_boxed_2055_; lean_object* v_res_2056_; 
v_isZero_boxed_2055_ = lean_unbox(v_isZero_2045_);
v_res_2056_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__0(v_isZero_boxed_2055_, v___y_2046_, v___y_2047_, v___y_2048_, v___y_2049_, v___y_2050_, v___y_2051_, v___y_2052_, v___y_2053_);
lean_dec(v___y_2053_);
lean_dec_ref(v___y_2052_);
lean_dec(v___y_2051_);
lean_dec_ref(v___y_2050_);
lean_dec(v___y_2049_);
lean_dec_ref(v___y_2048_);
lean_dec(v___y_2047_);
lean_dec_ref(v___y_2046_);
return v_res_2056_;
}
}
uint8_t l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__2(uint8_t v_isZero_2057_, lean_object* v_x_2058_){
_start:
{
return v_isZero_2057_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__2_0interp(lean_interpreter_value* stack)
{
uint8_t v_isZero_2057_ = stack[0].m_num;
lean_object* v_x_2058_ = stack[1].m_obj;
uint8_t v_res_2059_;
v_res_2059_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__2(v_isZero_2057_, v_x_2058_);
stack->m_num = v_res_2059_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__2___boxed(lean_object* v_isZero_2060_, lean_object* v_x_2061_){
_start:
{
uint8_t v_isZero_boxed_2062_; uint8_t v_res_2063_; lean_object* v_r_2064_; 
v_isZero_boxed_2062_ = lean_unbox(v_isZero_2060_);
v_res_2063_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__2(v_isZero_boxed_2062_, v_x_2061_);
lean_dec(v_x_2061_);
v_r_2064_ = lean_box(v_res_2063_);
return v_r_2064_;
}
}
lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__3(uint8_t v_isZero_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_){
_start:
{
lean_object* v_ref_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; 
v_ref_2075_ = lean_ctor_get(v___y_2072_, 2);
v___x_2076_ = l_Lean_SourceInfo_fromRef(v_ref_2075_, v_isZero_2065_);
v___x_2077_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__3));
v___x_2078_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__4));
lean_inc_n(v___x_2076_, 9);
v___x_2079_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2079_, 0, v___x_2076_);
lean_ctor_set(v___x_2079_, 1, v___x_2077_);
v___x_2080_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__7));
v___x_2081_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__8));
v___x_2082_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2082_, 0, v___x_2076_);
lean_ctor_set(v___x_2082_, 1, v___x_2081_);
v___x_2083_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__10));
v___x_2084_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__12));
v___x_2085_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__13));
v___x_2086_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2086_, 0, v___x_2076_);
lean_ctor_set(v___x_2086_, 1, v___x_2085_);
v___x_2087_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__14));
v___x_2088_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2088_, 0, v___x_2076_);
lean_ctor_set(v___x_2088_, 1, v___x_2087_);
v___x_2089_ = l_Lean_Syntax_node2(v___x_2076_, v___x_2084_, v___x_2086_, v___x_2088_);
v___x_2090_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__15));
v___x_2091_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2091_, 0, v___x_2076_);
lean_ctor_set(v___x_2091_, 1, v___x_2090_);
lean_inc(v___x_2089_);
v___x_2092_ = l_Lean_Syntax_node3(v___x_2076_, v___x_2083_, v___x_2089_, v___x_2091_, v___x_2089_);
v___x_2093_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__16));
v___x_2094_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2094_, 0, v___x_2076_);
lean_ctor_set(v___x_2094_, 1, v___x_2093_);
v___x_2095_ = l_Lean_Syntax_node3(v___x_2076_, v___x_2080_, v___x_2082_, v___x_2092_, v___x_2094_);
v___x_2096_ = l_Lean_Syntax_node2(v___x_2076_, v___x_2078_, v___x_2079_, v___x_2095_);
v___x_2097_ = l_Lean_Elab_Tactic_evalTactic(v___x_2096_, v___y_2066_, v___y_2067_, v___y_2068_, v___y_2069_, v___y_2070_, v___y_2071_, v___y_2072_, v___y_2073_);
return v___x_2097_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__3_0interp(lean_interpreter_value* stack)
{
uint8_t v_isZero_2065_ = stack[0].m_num;
lean_object* v___y_2066_ = stack[1].m_obj;
lean_object* v___y_2067_ = stack[2].m_obj;
lean_object* v___y_2068_ = stack[3].m_obj;
lean_object* v___y_2069_ = stack[4].m_obj;
lean_object* v___y_2070_ = stack[5].m_obj;
lean_object* v___y_2071_ = stack[6].m_obj;
lean_object* v___y_2072_ = stack[7].m_obj;
lean_object* v___y_2073_ = stack[8].m_obj;
lean_object* v_res_2098_;
v_res_2098_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__3(v_isZero_2065_, v___y_2066_, v___y_2067_, v___y_2068_, v___y_2069_, v___y_2070_, v___y_2071_, v___y_2072_, v___y_2073_);
stack->m_obj
 = v_res_2098_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__3___boxed(lean_object* v_isZero_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_){
_start:
{
uint8_t v_isZero_boxed_2109_; lean_object* v_res_2110_; 
v_isZero_boxed_2109_ = lean_unbox(v_isZero_2099_);
v_res_2110_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__3(v_isZero_boxed_2109_, v___y_2100_, v___y_2101_, v___y_2102_, v___y_2103_, v___y_2104_, v___y_2105_, v___y_2106_, v___y_2107_);
lean_dec(v___y_2107_);
lean_dec_ref(v___y_2106_);
lean_dec(v___y_2105_);
lean_dec_ref(v___y_2104_);
lean_dec(v___y_2103_);
lean_dec_ref(v___y_2102_);
lean_dec(v___y_2101_);
lean_dec_ref(v___y_2100_);
return v_res_2110_;
}
}
static lean_object* _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___closed__2(void){
_start:
{
lean_object* v___x_2113_; lean_object* v___x_2114_; 
v___x_2113_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___closed__1));
v___x_2114_ = l_Lean_stringToMessageData(v___x_2113_);
return v___x_2114_;
}
}
lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor(lean_object* v_mvar_2115_, lean_object* v_n_2116_, lean_object* v_a_2117_, lean_object* v_a_2118_, lean_object* v_a_2119_, lean_object* v_a_2120_){
_start:
{
lean_object* v___y_2123_; lean_object* v___y_2124_; lean_object* v___y_2125_; lean_object* v___y_2126_; lean_object* v_zero_2129_; uint8_t v_isZero_2130_; 
v_zero_2129_ = lean_unsigned_to_nat(0u);
v_isZero_2130_ = lean_nat_dec_eq(v_n_2116_, v_zero_2129_);
if (v_isZero_2130_ == 1)
{
lean_object* v___f_2131_; lean_object* v___f_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; uint8_t v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; 
lean_dec(v_n_2116_);
v___f_2131_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___closed__2));
v___f_2132_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___closed__0));
v___x_2133_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_run___boxed), 9, 2);
lean_closure_set(v___x_2133_, 0, v_mvar_2115_);
lean_closure_set(v___x_2133_, 1, v___f_2132_);
v___x_2134_ = lean_box(0);
v___x_2135_ = lean_box(0);
v___x_2136_ = lean_box(1);
v___x_2137_ = 0;
v___x_2138_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___closed__4));
v___x_2139_ = lean_alloc_ctor(0, 8, 11);
lean_ctor_set(v___x_2139_, 0, v___x_2134_);
lean_ctor_set(v___x_2139_, 1, v___x_2135_);
lean_ctor_set(v___x_2139_, 2, v___x_2134_);
lean_ctor_set(v___x_2139_, 3, v___f_2131_);
lean_ctor_set(v___x_2139_, 4, v___x_2136_);
lean_ctor_set(v___x_2139_, 5, v___x_2136_);
lean_ctor_set(v___x_2139_, 6, v___x_2134_);
lean_ctor_set(v___x_2139_, 7, v___x_2138_);
lean_ctor_set_uint8(v___x_2139_, sizeof(void*)*8, v_isZero_2130_);
lean_ctor_set_uint8(v___x_2139_, sizeof(void*)*8 + 1, v_isZero_2130_);
lean_ctor_set_uint8(v___x_2139_, sizeof(void*)*8 + 2, v_isZero_2130_);
lean_ctor_set_uint8(v___x_2139_, sizeof(void*)*8 + 3, v_isZero_2130_);
lean_ctor_set_uint8(v___x_2139_, sizeof(void*)*8 + 4, v___x_2137_);
lean_ctor_set_uint8(v___x_2139_, sizeof(void*)*8 + 5, v___x_2137_);
lean_ctor_set_uint8(v___x_2139_, sizeof(void*)*8 + 6, v___x_2137_);
lean_ctor_set_uint8(v___x_2139_, sizeof(void*)*8 + 7, v___x_2137_);
lean_ctor_set_uint8(v___x_2139_, sizeof(void*)*8 + 8, v_isZero_2130_);
lean_ctor_set_uint8(v___x_2139_, sizeof(void*)*8 + 9, v___x_2137_);
lean_ctor_set_uint8(v___x_2139_, sizeof(void*)*8 + 10, v_isZero_2130_);
v___x_2140_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___closed__6));
v___x_2141_ = l_Lean_Elab_Term_TermElabM_run___redArg(v___x_2133_, v___x_2139_, v___x_2140_, v_a_2117_, v_a_2118_, v_a_2119_, v_a_2120_);
if (lean_obj_tag(v___x_2141_) == 0)
{
lean_object* v_a_2142_; lean_object* v___x_2144_; uint8_t v_isShared_2145_; uint8_t v_isSharedCheck_2153_; 
v_a_2142_ = lean_ctor_get(v___x_2141_, 0);
v_isSharedCheck_2153_ = !lean_is_exclusive(v___x_2141_);
if (v_isSharedCheck_2153_ == 0)
{
v___x_2144_ = v___x_2141_;
v_isShared_2145_ = v_isSharedCheck_2153_;
goto v_resetjp_2143_;
}
else
{
lean_inc(v_a_2142_);
lean_dec(v___x_2141_);
v___x_2144_ = lean_box(0);
v_isShared_2145_ = v_isSharedCheck_2153_;
goto v_resetjp_2143_;
}
v_resetjp_2143_:
{
lean_object* v_fst_2146_; 
v_fst_2146_ = lean_ctor_get(v_a_2142_, 0);
lean_inc(v_fst_2146_);
lean_dec(v_a_2142_);
if (lean_obj_tag(v_fst_2146_) == 0)
{
lean_object* v___x_2147_; lean_object* v___x_2149_; 
v___x_2147_ = lean_box(0);
if (v_isShared_2145_ == 0)
{
lean_ctor_set(v___x_2144_, 0, v___x_2147_);
v___x_2149_ = v___x_2144_;
goto v_reusejp_2148_;
}
else
{
lean_object* v_reuseFailAlloc_2150_; 
v_reuseFailAlloc_2150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2150_, 0, v___x_2147_);
v___x_2149_ = v_reuseFailAlloc_2150_;
goto v_reusejp_2148_;
}
v_reusejp_2148_:
{
return v___x_2149_;
}
}
else
{
lean_object* v___x_2151_; lean_object* v___x_2152_; 
lean_dec(v_fst_2146_);
lean_del_object(v___x_2144_);
v___x_2151_ = lean_obj_once(&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___closed__2, &l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___closed__2_once, _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___closed__2);
v___x_2152_ = l_Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0___redArg(v___x_2151_, v_a_2117_, v_a_2118_, v_a_2119_, v_a_2120_);
return v___x_2152_;
}
}
}
else
{
lean_object* v_a_2154_; lean_object* v___x_2156_; uint8_t v_isShared_2157_; uint8_t v_isSharedCheck_2161_; 
v_a_2154_ = lean_ctor_get(v___x_2141_, 0);
v_isSharedCheck_2161_ = !lean_is_exclusive(v___x_2141_);
if (v_isSharedCheck_2161_ == 0)
{
v___x_2156_ = v___x_2141_;
v_isShared_2157_ = v_isSharedCheck_2161_;
goto v_resetjp_2155_;
}
else
{
lean_inc(v_a_2154_);
lean_dec(v___x_2141_);
v___x_2156_ = lean_box(0);
v_isShared_2157_ = v_isSharedCheck_2161_;
goto v_resetjp_2155_;
}
v_resetjp_2155_:
{
lean_object* v___x_2159_; 
if (v_isShared_2157_ == 0)
{
v___x_2159_ = v___x_2156_;
goto v_reusejp_2158_;
}
else
{
lean_object* v_reuseFailAlloc_2160_; 
v_reuseFailAlloc_2160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2160_, 0, v_a_2154_);
v___x_2159_ = v_reuseFailAlloc_2160_;
goto v_reusejp_2158_;
}
v_reusejp_2158_:
{
return v___x_2159_;
}
}
}
}
else
{
lean_object* v___x_2162_; lean_object* v___f_2163_; lean_object* v___x_2164_; lean_object* v___f_2165_; lean_object* v___x_2166_; lean_object* v___f_2167_; lean_object* v_one_2168_; lean_object* v_n_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; uint8_t v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; 
v___x_2162_ = lean_box(v_isZero_2130_);
v___f_2163_ = lean_alloc_closure((void*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__0___boxed), 10, 1);
lean_closure_set(v___f_2163_, 0, v___x_2162_);
v___x_2164_ = lean_box(v_isZero_2130_);
v___f_2165_ = lean_alloc_closure((void*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__2___boxed), 2, 1);
lean_closure_set(v___f_2165_, 0, v___x_2164_);
v___x_2166_ = lean_box(v_isZero_2130_);
v___f_2167_ = lean_alloc_closure((void*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__3___boxed), 10, 1);
lean_closure_set(v___f_2167_, 0, v___x_2166_);
v_one_2168_ = lean_unsigned_to_nat(1u);
v_n_2169_ = lean_nat_sub(v_n_2116_, v_one_2168_);
lean_dec(v_n_2116_);
v___x_2170_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_run___boxed), 9, 2);
lean_closure_set(v___x_2170_, 0, v_mvar_2115_);
lean_closure_set(v___x_2170_, 1, v___f_2167_);
v___x_2171_ = lean_box(0);
v___x_2172_ = lean_box(0);
v___x_2173_ = 1;
v___x_2174_ = lean_box(1);
v___x_2175_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___closed__4));
v___x_2176_ = lean_alloc_ctor(0, 8, 11);
lean_ctor_set(v___x_2176_, 0, v___x_2171_);
lean_ctor_set(v___x_2176_, 1, v___x_2172_);
lean_ctor_set(v___x_2176_, 2, v___x_2171_);
lean_ctor_set(v___x_2176_, 3, v___f_2165_);
lean_ctor_set(v___x_2176_, 4, v___x_2174_);
lean_ctor_set(v___x_2176_, 5, v___x_2174_);
lean_ctor_set(v___x_2176_, 6, v___x_2171_);
lean_ctor_set(v___x_2176_, 7, v___x_2175_);
lean_ctor_set_uint8(v___x_2176_, sizeof(void*)*8, v___x_2173_);
lean_ctor_set_uint8(v___x_2176_, sizeof(void*)*8 + 1, v___x_2173_);
lean_ctor_set_uint8(v___x_2176_, sizeof(void*)*8 + 2, v___x_2173_);
lean_ctor_set_uint8(v___x_2176_, sizeof(void*)*8 + 3, v___x_2173_);
lean_ctor_set_uint8(v___x_2176_, sizeof(void*)*8 + 4, v_isZero_2130_);
lean_ctor_set_uint8(v___x_2176_, sizeof(void*)*8 + 5, v_isZero_2130_);
lean_ctor_set_uint8(v___x_2176_, sizeof(void*)*8 + 6, v_isZero_2130_);
lean_ctor_set_uint8(v___x_2176_, sizeof(void*)*8 + 7, v_isZero_2130_);
lean_ctor_set_uint8(v___x_2176_, sizeof(void*)*8 + 8, v___x_2173_);
lean_ctor_set_uint8(v___x_2176_, sizeof(void*)*8 + 9, v_isZero_2130_);
lean_ctor_set_uint8(v___x_2176_, sizeof(void*)*8 + 10, v___x_2173_);
v___x_2177_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___closed__6));
lean_inc_ref(v___x_2176_);
v___x_2178_ = l_Lean_Elab_Term_TermElabM_run___redArg(v___x_2170_, v___x_2176_, v___x_2177_, v_a_2117_, v_a_2118_, v_a_2119_, v_a_2120_);
if (lean_obj_tag(v___x_2178_) == 0)
{
lean_object* v_a_2179_; lean_object* v_fst_2180_; 
v_a_2179_ = lean_ctor_get(v___x_2178_, 0);
lean_inc(v_a_2179_);
lean_dec_ref_known(v___x_2178_, 1);
v_fst_2180_ = lean_ctor_get(v_a_2179_, 0);
lean_inc(v_fst_2180_);
lean_dec(v_a_2179_);
if (lean_obj_tag(v_fst_2180_) == 1)
{
lean_object* v_tail_2181_; 
v_tail_2181_ = lean_ctor_get(v_fst_2180_, 1);
lean_inc(v_tail_2181_);
if (lean_obj_tag(v_tail_2181_) == 1)
{
lean_object* v_tail_2182_; 
v_tail_2182_ = lean_ctor_get(v_tail_2181_, 1);
if (lean_obj_tag(v_tail_2182_) == 0)
{
lean_object* v_head_2183_; lean_object* v_head_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; 
v_head_2183_ = lean_ctor_get(v_fst_2180_, 0);
lean_inc(v_head_2183_);
lean_dec_ref_known(v_fst_2180_, 2);
v_head_2184_ = lean_ctor_get(v_tail_2181_, 0);
lean_inc(v_head_2184_);
lean_dec_ref_known(v_tail_2181_, 2);
v___x_2185_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_run___boxed), 9, 2);
lean_closure_set(v___x_2185_, 0, v_head_2183_);
lean_closure_set(v___x_2185_, 1, v___f_2163_);
v___x_2186_ = l_Lean_Elab_Term_TermElabM_run___redArg(v___x_2185_, v___x_2176_, v___x_2177_, v_a_2117_, v_a_2118_, v_a_2119_, v_a_2120_);
if (lean_obj_tag(v___x_2186_) == 0)
{
lean_object* v_a_2187_; lean_object* v_fst_2188_; 
v_a_2187_ = lean_ctor_get(v___x_2186_, 0);
lean_inc(v_a_2187_);
lean_dec_ref_known(v___x_2186_, 1);
v_fst_2188_ = lean_ctor_get(v_a_2187_, 0);
lean_inc(v_fst_2188_);
lean_dec(v_a_2187_);
if (lean_obj_tag(v_fst_2188_) == 0)
{
v_mvar_2115_ = v_head_2184_;
v_n_2116_ = v_n_2169_;
goto _start;
}
else
{
lean_object* v___x_2190_; lean_object* v___x_2191_; 
lean_dec(v_fst_2188_);
lean_dec(v_head_2184_);
lean_dec(v_n_2169_);
v___x_2190_ = lean_obj_once(&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___closed__2, &l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___closed__2_once, _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___closed__2);
v___x_2191_ = l_Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0___redArg(v___x_2190_, v_a_2117_, v_a_2118_, v_a_2119_, v_a_2120_);
return v___x_2191_;
}
}
else
{
lean_object* v_a_2192_; lean_object* v___x_2194_; uint8_t v_isShared_2195_; uint8_t v_isSharedCheck_2199_; 
lean_dec(v_head_2184_);
lean_dec(v_n_2169_);
v_a_2192_ = lean_ctor_get(v___x_2186_, 0);
v_isSharedCheck_2199_ = !lean_is_exclusive(v___x_2186_);
if (v_isSharedCheck_2199_ == 0)
{
v___x_2194_ = v___x_2186_;
v_isShared_2195_ = v_isSharedCheck_2199_;
goto v_resetjp_2193_;
}
else
{
lean_inc(v_a_2192_);
lean_dec(v___x_2186_);
v___x_2194_ = lean_box(0);
v_isShared_2195_ = v_isSharedCheck_2199_;
goto v_resetjp_2193_;
}
v_resetjp_2193_:
{
lean_object* v___x_2197_; 
if (v_isShared_2195_ == 0)
{
v___x_2197_ = v___x_2194_;
goto v_reusejp_2196_;
}
else
{
lean_object* v_reuseFailAlloc_2198_; 
v_reuseFailAlloc_2198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2198_, 0, v_a_2192_);
v___x_2197_ = v_reuseFailAlloc_2198_;
goto v_reusejp_2196_;
}
v_reusejp_2196_:
{
return v___x_2197_;
}
}
}
}
else
{
lean_dec_ref_known(v_tail_2181_, 2);
lean_dec_ref_known(v_fst_2180_, 2);
lean_dec_ref_known(v___x_2176_, 8);
lean_dec(v_n_2169_);
lean_dec_ref(v___f_2163_);
v___y_2123_ = v_a_2117_;
v___y_2124_ = v_a_2118_;
v___y_2125_ = v_a_2119_;
v___y_2126_ = v_a_2120_;
goto v___jp_2122_;
}
}
else
{
lean_dec_ref_known(v_fst_2180_, 2);
lean_dec(v_tail_2181_);
lean_dec_ref_known(v___x_2176_, 8);
lean_dec(v_n_2169_);
lean_dec_ref(v___f_2163_);
v___y_2123_ = v_a_2117_;
v___y_2124_ = v_a_2118_;
v___y_2125_ = v_a_2119_;
v___y_2126_ = v_a_2120_;
goto v___jp_2122_;
}
}
else
{
lean_dec(v_fst_2180_);
lean_dec_ref_known(v___x_2176_, 8);
lean_dec(v_n_2169_);
lean_dec_ref(v___f_2163_);
v___y_2123_ = v_a_2117_;
v___y_2124_ = v_a_2118_;
v___y_2125_ = v_a_2119_;
v___y_2126_ = v_a_2120_;
goto v___jp_2122_;
}
}
else
{
lean_object* v_a_2200_; lean_object* v___x_2202_; uint8_t v_isShared_2203_; uint8_t v_isSharedCheck_2207_; 
lean_dec_ref_known(v___x_2176_, 8);
lean_dec(v_n_2169_);
lean_dec_ref(v___f_2163_);
v_a_2200_ = lean_ctor_get(v___x_2178_, 0);
v_isSharedCheck_2207_ = !lean_is_exclusive(v___x_2178_);
if (v_isSharedCheck_2207_ == 0)
{
v___x_2202_ = v___x_2178_;
v_isShared_2203_ = v_isSharedCheck_2207_;
goto v_resetjp_2201_;
}
else
{
lean_inc(v_a_2200_);
lean_dec(v___x_2178_);
v___x_2202_ = lean_box(0);
v_isShared_2203_ = v_isSharedCheck_2207_;
goto v_resetjp_2201_;
}
v_resetjp_2201_:
{
lean_object* v___x_2205_; 
if (v_isShared_2203_ == 0)
{
v___x_2205_ = v___x_2202_;
goto v_reusejp_2204_;
}
else
{
lean_object* v_reuseFailAlloc_2206_; 
v_reuseFailAlloc_2206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2206_, 0, v_a_2200_);
v___x_2205_ = v_reuseFailAlloc_2206_;
goto v_reusejp_2204_;
}
v_reusejp_2204_:
{
return v___x_2205_;
}
}
}
}
v___jp_2122_:
{
lean_object* v___x_2127_; lean_object* v___x_2128_; 
v___x_2127_ = lean_obj_once(&l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___closed__1, &l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___closed__1_once, _init_l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___closed__1);
v___x_2128_ = l_Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0___redArg(v___x_2127_, v___y_2123_, v___y_2124_, v___y_2125_, v___y_2126_);
return v___x_2128_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvar_2115_ = stack[0].m_obj;
lean_object* v_n_2116_ = stack[1].m_obj;
lean_object* v_a_2117_ = stack[2].m_obj;
lean_object* v_a_2118_ = stack[3].m_obj;
lean_object* v_a_2119_ = stack[4].m_obj;
lean_object* v_a_2120_ = stack[5].m_obj;
lean_object* v_res_2208_;
v_res_2208_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor(v_mvar_2115_, v_n_2116_, v_a_2117_, v_a_2118_, v_a_2119_, v_a_2120_);
stack->m_obj
 = v_res_2208_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___boxed(lean_object* v_mvar_2209_, lean_object* v_n_2210_, lean_object* v_a_2211_, lean_object* v_a_2212_, lean_object* v_a_2213_, lean_object* v_a_2214_, lean_object* v_a_2215_){
_start:
{
lean_object* v_res_2216_; 
v_res_2216_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor(v_mvar_2209_, v_n_2210_, v_a_2211_, v_a_2212_, v_a_2213_, v_a_2214_);
lean_dec(v_a_2214_);
lean_dec_ref(v_a_2213_);
lean_dec(v_a_2212_);
lean_dec_ref(v_a_2211_);
return v_res_2216_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toCases_spec__0(lean_object* v_a_2217_, lean_object* v_a_2218_){
_start:
{
if (lean_obj_tag(v_a_2217_) == 0)
{
lean_object* v___x_2219_; 
v___x_2219_ = lean_array_to_list(v_a_2218_);
return v___x_2219_;
}
else
{
lean_object* v_head_2220_; lean_object* v_fst_2221_; uint8_t v___x_2222_; 
v_head_2220_ = lean_ctor_get(v_a_2217_, 0);
v_fst_2221_ = lean_ctor_get(v_head_2220_, 0);
v___x_2222_ = lean_unbox(v_fst_2221_);
if (v___x_2222_ == 0)
{
lean_object* v_tail_2223_; 
v_tail_2223_ = lean_ctor_get(v_a_2217_, 1);
lean_inc(v_tail_2223_);
lean_dec_ref_known(v_a_2217_, 2);
v_a_2217_ = v_tail_2223_;
goto _start;
}
else
{
lean_object* v_tail_2225_; lean_object* v_snd_2226_; lean_object* v___x_2227_; 
lean_inc(v_head_2220_);
v_tail_2225_ = lean_ctor_get(v_a_2217_, 1);
lean_inc(v_tail_2225_);
lean_dec_ref_known(v_a_2217_, 2);
v_snd_2226_ = lean_ctor_get(v_head_2220_, 1);
lean_inc(v_snd_2226_);
lean_dec(v_head_2220_);
v___x_2227_ = lean_array_push(v_a_2218_, v_snd_2226_);
v_a_2217_ = v_tail_2225_;
v_a_2218_ = v___x_2227_;
goto _start;
}
}
}
}
lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toCases_spec__1(lean_object* v_a_2229_, lean_object* v_x_2230_, lean_object* v_x_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_){
_start:
{
if (lean_obj_tag(v_x_2230_) == 0)
{
lean_object* v___x_2237_; lean_object* v___x_2238_; 
v___x_2237_ = l_List_reverse___redArg(v_x_2231_);
v___x_2238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2238_, 0, v___x_2237_);
return v___x_2238_;
}
else
{
lean_object* v_head_2239_; lean_object* v_tail_2240_; lean_object* v___x_2242_; uint8_t v_isShared_2243_; uint8_t v_isSharedCheck_2315_; 
v_head_2239_ = lean_ctor_get(v_x_2230_, 0);
v_tail_2240_ = lean_ctor_get(v_x_2230_, 1);
v_isSharedCheck_2315_ = !lean_is_exclusive(v_x_2230_);
if (v_isSharedCheck_2315_ == 0)
{
v___x_2242_ = v_x_2230_;
v_isShared_2243_ = v_isSharedCheck_2315_;
goto v_resetjp_2241_;
}
else
{
lean_inc(v_tail_2240_);
lean_inc(v_head_2239_);
lean_dec(v_x_2230_);
v___x_2242_ = lean_box(0);
v_isShared_2243_ = v_isSharedCheck_2315_;
goto v_resetjp_2241_;
}
v_resetjp_2241_:
{
lean_object* v___y_2245_; lean_object* v_fst_2259_; lean_object* v_fst_2260_; lean_object* v_snd_2261_; lean_object* v_toInductionSubgoal_2262_; lean_object* v_snd_2263_; lean_object* v_variablesKept_2264_; lean_object* v_neqs_2265_; lean_object* v_mvarId_2266_; lean_object* v_fields_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; 
v_fst_2259_ = lean_ctor_get(v_head_2239_, 0);
v_fst_2260_ = lean_ctor_get(v_fst_2259_, 0);
lean_inc(v_fst_2260_);
v_snd_2261_ = lean_ctor_get(v_fst_2259_, 1);
v_toInductionSubgoal_2262_ = lean_ctor_get(v_snd_2261_, 0);
lean_inc_ref(v_toInductionSubgoal_2262_);
v_snd_2263_ = lean_ctor_get(v_head_2239_, 1);
lean_inc(v_snd_2263_);
lean_dec(v_head_2239_);
v_variablesKept_2264_ = lean_ctor_get(v_fst_2260_, 0);
lean_inc_n(v_variablesKept_2264_, 2);
v_neqs_2265_ = lean_ctor_get(v_fst_2260_, 1);
lean_inc(v_neqs_2265_);
lean_dec(v_fst_2260_);
v_mvarId_2266_ = lean_ctor_get(v_toInductionSubgoal_2262_, 0);
lean_inc(v_mvarId_2266_);
v_fields_2267_ = lean_ctor_get(v_toInductionSubgoal_2262_, 1);
lean_inc_ref_n(v_fields_2267_, 2);
lean_dec_ref(v_toInductionSubgoal_2262_);
v___x_2268_ = l_Lean_instInhabitedExpr;
v___x_2269_ = lean_array_to_list(v_fields_2267_);
v___x_2270_ = l_List_zipWith___at___00List_zip_spec__0(lean_box(0), lean_box(0), v_variablesKept_2264_, v___x_2269_);
v___x_2271_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__1___closed__1));
v___x_2272_ = l_List_filterMapTR_go___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toCases_spec__0(v___x_2270_, v___x_2271_);
v___x_2273_ = lean_array_get_size(v_a_2229_);
v___x_2274_ = lean_unsigned_to_nat(1u);
v___x_2275_ = lean_nat_sub(v___x_2273_, v___x_2274_);
v___x_2276_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select(v_snd_2263_, v___x_2275_, v_mvarId_2266_, v___y_2232_, v___y_2233_, v___y_2234_, v___y_2235_);
if (lean_obj_tag(v___x_2276_) == 0)
{
if (lean_obj_tag(v_neqs_2265_) == 0)
{
lean_object* v_a_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; 
v_a_2277_ = lean_ctor_get(v___x_2276_, 0);
lean_inc(v_a_2277_);
lean_dec_ref_known(v___x_2276_, 1);
v___x_2278_ = l_List_lengthTR___redArg(v_variablesKept_2264_);
lean_dec(v_variablesKept_2264_);
v___x_2279_ = lean_nat_sub(v___x_2278_, v___x_2274_);
lean_dec(v___x_2278_);
v___x_2280_ = lean_array_get(v___x_2268_, v_fields_2267_, v___x_2279_);
lean_dec(v___x_2279_);
lean_dec_ref(v_fields_2267_);
v___x_2281_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_List_init___redArg(v___x_2272_);
v___x_2282_ = l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2(v_a_2277_, v___x_2281_, v___y_2232_, v___y_2233_, v___y_2234_, v___y_2235_);
if (lean_obj_tag(v___x_2282_) == 0)
{
lean_object* v_a_2283_; lean_object* v___x_2284_; 
v_a_2283_ = lean_ctor_get(v___x_2282_, 0);
lean_inc(v_a_2283_);
lean_dec_ref_known(v___x_2282_, 1);
v___x_2284_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1___redArg(v_a_2283_, v___x_2280_, v___y_2233_);
v___y_2245_ = v___x_2284_;
goto v___jp_2244_;
}
else
{
lean_object* v_a_2285_; lean_object* v___x_2287_; uint8_t v_isShared_2288_; uint8_t v_isSharedCheck_2292_; 
lean_dec(v___x_2280_);
lean_del_object(v___x_2242_);
lean_dec(v_tail_2240_);
lean_dec(v_x_2231_);
v_a_2285_ = lean_ctor_get(v___x_2282_, 0);
v_isSharedCheck_2292_ = !lean_is_exclusive(v___x_2282_);
if (v_isSharedCheck_2292_ == 0)
{
v___x_2287_ = v___x_2282_;
v_isShared_2288_ = v_isSharedCheck_2292_;
goto v_resetjp_2286_;
}
else
{
lean_inc(v_a_2285_);
lean_dec(v___x_2282_);
v___x_2287_ = lean_box(0);
v_isShared_2288_ = v_isSharedCheck_2292_;
goto v_resetjp_2286_;
}
v_resetjp_2286_:
{
lean_object* v___x_2290_; 
if (v_isShared_2288_ == 0)
{
v___x_2290_ = v___x_2287_;
goto v_reusejp_2289_;
}
else
{
lean_object* v_reuseFailAlloc_2291_; 
v_reuseFailAlloc_2291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2291_, 0, v_a_2285_);
v___x_2290_ = v_reuseFailAlloc_2291_;
goto v_reusejp_2289_;
}
v_reusejp_2289_:
{
return v___x_2290_;
}
}
}
}
else
{
lean_object* v_a_2293_; lean_object* v_val_2294_; lean_object* v___x_2295_; 
lean_dec_ref(v_fields_2267_);
lean_dec(v_variablesKept_2264_);
v_a_2293_ = lean_ctor_get(v___x_2276_, 0);
lean_inc(v_a_2293_);
lean_dec_ref_known(v___x_2276_, 1);
v_val_2294_ = lean_ctor_get(v_neqs_2265_, 0);
lean_inc(v_val_2294_);
lean_dec_ref_known(v_neqs_2265_, 1);
v___x_2295_ = l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2(v_a_2293_, v___x_2272_, v___y_2232_, v___y_2233_, v___y_2234_, v___y_2235_);
if (lean_obj_tag(v___x_2295_) == 0)
{
lean_object* v_a_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; 
v_a_2296_ = lean_ctor_get(v___x_2295_, 0);
lean_inc(v_a_2296_);
lean_dec_ref_known(v___x_2295_, 1);
v___x_2297_ = lean_nat_sub(v_val_2294_, v___x_2274_);
lean_dec(v_val_2294_);
v___x_2298_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor(v_a_2296_, v___x_2297_, v___y_2232_, v___y_2233_, v___y_2234_, v___y_2235_);
v___y_2245_ = v___x_2298_;
goto v___jp_2244_;
}
else
{
lean_object* v_a_2299_; lean_object* v___x_2301_; uint8_t v_isShared_2302_; uint8_t v_isSharedCheck_2306_; 
lean_dec(v_val_2294_);
lean_del_object(v___x_2242_);
lean_dec(v_tail_2240_);
lean_dec(v_x_2231_);
v_a_2299_ = lean_ctor_get(v___x_2295_, 0);
v_isSharedCheck_2306_ = !lean_is_exclusive(v___x_2295_);
if (v_isSharedCheck_2306_ == 0)
{
v___x_2301_ = v___x_2295_;
v_isShared_2302_ = v_isSharedCheck_2306_;
goto v_resetjp_2300_;
}
else
{
lean_inc(v_a_2299_);
lean_dec(v___x_2295_);
v___x_2301_ = lean_box(0);
v_isShared_2302_ = v_isSharedCheck_2306_;
goto v_resetjp_2300_;
}
v_resetjp_2300_:
{
lean_object* v___x_2304_; 
if (v_isShared_2302_ == 0)
{
v___x_2304_ = v___x_2301_;
goto v_reusejp_2303_;
}
else
{
lean_object* v_reuseFailAlloc_2305_; 
v_reuseFailAlloc_2305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2305_, 0, v_a_2299_);
v___x_2304_ = v_reuseFailAlloc_2305_;
goto v_reusejp_2303_;
}
v_reusejp_2303_:
{
return v___x_2304_;
}
}
}
}
}
else
{
lean_object* v_a_2307_; lean_object* v___x_2309_; uint8_t v_isShared_2310_; uint8_t v_isSharedCheck_2314_; 
lean_dec(v___x_2272_);
lean_dec_ref(v_fields_2267_);
lean_dec(v_neqs_2265_);
lean_dec(v_variablesKept_2264_);
lean_del_object(v___x_2242_);
lean_dec(v_tail_2240_);
lean_dec(v_x_2231_);
v_a_2307_ = lean_ctor_get(v___x_2276_, 0);
v_isSharedCheck_2314_ = !lean_is_exclusive(v___x_2276_);
if (v_isSharedCheck_2314_ == 0)
{
v___x_2309_ = v___x_2276_;
v_isShared_2310_ = v_isSharedCheck_2314_;
goto v_resetjp_2308_;
}
else
{
lean_inc(v_a_2307_);
lean_dec(v___x_2276_);
v___x_2309_ = lean_box(0);
v_isShared_2310_ = v_isSharedCheck_2314_;
goto v_resetjp_2308_;
}
v_resetjp_2308_:
{
lean_object* v___x_2312_; 
if (v_isShared_2310_ == 0)
{
v___x_2312_ = v___x_2309_;
goto v_reusejp_2311_;
}
else
{
lean_object* v_reuseFailAlloc_2313_; 
v_reuseFailAlloc_2313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2313_, 0, v_a_2307_);
v___x_2312_ = v_reuseFailAlloc_2313_;
goto v_reusejp_2311_;
}
v_reusejp_2311_:
{
return v___x_2312_;
}
}
}
v___jp_2244_:
{
if (lean_obj_tag(v___y_2245_) == 0)
{
lean_object* v_a_2246_; lean_object* v___x_2248_; 
v_a_2246_ = lean_ctor_get(v___y_2245_, 0);
lean_inc(v_a_2246_);
lean_dec_ref_known(v___y_2245_, 1);
if (v_isShared_2243_ == 0)
{
lean_ctor_set(v___x_2242_, 1, v_x_2231_);
lean_ctor_set(v___x_2242_, 0, v_a_2246_);
v___x_2248_ = v___x_2242_;
goto v_reusejp_2247_;
}
else
{
lean_object* v_reuseFailAlloc_2250_; 
v_reuseFailAlloc_2250_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2250_, 0, v_a_2246_);
lean_ctor_set(v_reuseFailAlloc_2250_, 1, v_x_2231_);
v___x_2248_ = v_reuseFailAlloc_2250_;
goto v_reusejp_2247_;
}
v_reusejp_2247_:
{
v_x_2230_ = v_tail_2240_;
v_x_2231_ = v___x_2248_;
goto _start;
}
}
else
{
lean_object* v_a_2251_; lean_object* v___x_2253_; uint8_t v_isShared_2254_; uint8_t v_isSharedCheck_2258_; 
lean_del_object(v___x_2242_);
lean_dec(v_tail_2240_);
lean_dec(v_x_2231_);
v_a_2251_ = lean_ctor_get(v___y_2245_, 0);
v_isSharedCheck_2258_ = !lean_is_exclusive(v___y_2245_);
if (v_isSharedCheck_2258_ == 0)
{
v___x_2253_ = v___y_2245_;
v_isShared_2254_ = v_isSharedCheck_2258_;
goto v_resetjp_2252_;
}
else
{
lean_inc(v_a_2251_);
lean_dec(v___y_2245_);
v___x_2253_ = lean_box(0);
v_isShared_2254_ = v_isSharedCheck_2258_;
goto v_resetjp_2252_;
}
v_resetjp_2252_:
{
lean_object* v___x_2256_; 
if (v_isShared_2254_ == 0)
{
v___x_2256_ = v___x_2253_;
goto v_reusejp_2255_;
}
else
{
lean_object* v_reuseFailAlloc_2257_; 
v_reuseFailAlloc_2257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2257_, 0, v_a_2251_);
v___x_2256_ = v_reuseFailAlloc_2257_;
goto v_reusejp_2255_;
}
v_reusejp_2255_:
{
return v___x_2256_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toCases_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2229_ = stack[0].m_obj;
lean_object* v_x_2230_ = stack[1].m_obj;
lean_object* v_x_2231_ = stack[2].m_obj;
lean_object* v___y_2232_ = stack[3].m_obj;
lean_object* v___y_2233_ = stack[4].m_obj;
lean_object* v___y_2234_ = stack[5].m_obj;
lean_object* v___y_2235_ = stack[6].m_obj;
lean_object* v_res_2316_;
v_res_2316_ = l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toCases_spec__1(v_a_2229_, v_x_2230_, v_x_2231_, v___y_2232_, v___y_2233_, v___y_2234_, v___y_2235_);
stack->m_obj
 = v_res_2316_;
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toCases_spec__1___boxed(lean_object* v_a_2317_, lean_object* v_x_2318_, lean_object* v_x_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_){
_start:
{
lean_object* v_res_2325_; 
v_res_2325_ = l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toCases_spec__1(v_a_2317_, v_x_2318_, v_x_2319_, v___y_2320_, v___y_2321_, v___y_2322_, v___y_2323_);
lean_dec(v___y_2323_);
lean_dec_ref(v___y_2322_);
lean_dec(v___y_2321_);
lean_dec_ref(v___y_2320_);
lean_dec_ref(v_a_2317_);
return v_res_2325_;
}
}
lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toCases(lean_object* v_mvar_2328_, lean_object* v_shape_2329_, lean_object* v_a_2330_, lean_object* v_a_2331_, lean_object* v_a_2332_, lean_object* v_a_2333_){
_start:
{
uint8_t v___x_2335_; lean_object* v___x_2336_; 
v___x_2335_ = 0;
v___x_2336_ = l_Lean_Meta_intro1Core(v_mvar_2328_, v___x_2335_, v_a_2330_, v_a_2331_, v_a_2332_, v_a_2333_);
if (lean_obj_tag(v___x_2336_) == 0)
{
lean_object* v_a_2337_; lean_object* v_fst_2338_; lean_object* v_snd_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; 
v_a_2337_ = lean_ctor_get(v___x_2336_, 0);
lean_inc(v_a_2337_);
lean_dec_ref_known(v___x_2336_, 1);
v_fst_2338_ = lean_ctor_get(v_a_2337_, 0);
lean_inc(v_fst_2338_);
v_snd_2339_ = lean_ctor_get(v_a_2337_, 1);
lean_inc(v_snd_2339_);
lean_dec(v_a_2337_);
v___x_2340_ = lean_unsigned_to_nat(0u);
v___x_2341_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toCases___closed__0));
v___x_2342_ = lean_box(0);
v___x_2343_ = l_Lean_MVarId_cases(v_snd_2339_, v_fst_2338_, v___x_2341_, v___x_2335_, v___x_2342_, v_a_2330_, v_a_2331_, v_a_2332_, v_a_2333_);
if (lean_obj_tag(v___x_2343_) == 0)
{
lean_object* v_a_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; 
v_a_2344_ = lean_ctor_get(v___x_2343_, 0);
lean_inc_n(v_a_2344_, 2);
lean_dec_ref_known(v___x_2343_, 1);
v___x_2345_ = lean_array_to_list(v_a_2344_);
v___x_2346_ = l_List_zipWith___at___00List_zip_spec__0(lean_box(0), lean_box(0), v_shape_2329_, v___x_2345_);
v___x_2347_ = l_List_zipIdxTR___redArg(v___x_2346_, v___x_2340_);
v___x_2348_ = lean_box(0);
v___x_2349_ = l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toCases_spec__1(v_a_2344_, v___x_2347_, v___x_2348_, v_a_2330_, v_a_2331_, v_a_2332_, v_a_2333_);
lean_dec(v_a_2344_);
if (lean_obj_tag(v___x_2349_) == 0)
{
lean_object* v___x_2351_; uint8_t v_isShared_2352_; uint8_t v_isSharedCheck_2357_; 
v_isSharedCheck_2357_ = !lean_is_exclusive(v___x_2349_);
if (v_isSharedCheck_2357_ == 0)
{
lean_object* v_unused_2358_; 
v_unused_2358_ = lean_ctor_get(v___x_2349_, 0);
lean_dec(v_unused_2358_);
v___x_2351_ = v___x_2349_;
v_isShared_2352_ = v_isSharedCheck_2357_;
goto v_resetjp_2350_;
}
else
{
lean_dec(v___x_2349_);
v___x_2351_ = lean_box(0);
v_isShared_2352_ = v_isSharedCheck_2357_;
goto v_resetjp_2350_;
}
v_resetjp_2350_:
{
lean_object* v___x_2353_; lean_object* v___x_2355_; 
v___x_2353_ = lean_box(0);
if (v_isShared_2352_ == 0)
{
lean_ctor_set(v___x_2351_, 0, v___x_2353_);
v___x_2355_ = v___x_2351_;
goto v_reusejp_2354_;
}
else
{
lean_object* v_reuseFailAlloc_2356_; 
v_reuseFailAlloc_2356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2356_, 0, v___x_2353_);
v___x_2355_ = v_reuseFailAlloc_2356_;
goto v_reusejp_2354_;
}
v_reusejp_2354_:
{
return v___x_2355_;
}
}
}
else
{
lean_object* v_a_2359_; lean_object* v___x_2361_; uint8_t v_isShared_2362_; uint8_t v_isSharedCheck_2366_; 
v_a_2359_ = lean_ctor_get(v___x_2349_, 0);
v_isSharedCheck_2366_ = !lean_is_exclusive(v___x_2349_);
if (v_isSharedCheck_2366_ == 0)
{
v___x_2361_ = v___x_2349_;
v_isShared_2362_ = v_isSharedCheck_2366_;
goto v_resetjp_2360_;
}
else
{
lean_inc(v_a_2359_);
lean_dec(v___x_2349_);
v___x_2361_ = lean_box(0);
v_isShared_2362_ = v_isSharedCheck_2366_;
goto v_resetjp_2360_;
}
v_resetjp_2360_:
{
lean_object* v___x_2364_; 
if (v_isShared_2362_ == 0)
{
v___x_2364_ = v___x_2361_;
goto v_reusejp_2363_;
}
else
{
lean_object* v_reuseFailAlloc_2365_; 
v_reuseFailAlloc_2365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2365_, 0, v_a_2359_);
v___x_2364_ = v_reuseFailAlloc_2365_;
goto v_reusejp_2363_;
}
v_reusejp_2363_:
{
return v___x_2364_;
}
}
}
}
else
{
lean_object* v_a_2367_; lean_object* v___x_2369_; uint8_t v_isShared_2370_; uint8_t v_isSharedCheck_2374_; 
lean_dec(v_shape_2329_);
v_a_2367_ = lean_ctor_get(v___x_2343_, 0);
v_isSharedCheck_2374_ = !lean_is_exclusive(v___x_2343_);
if (v_isSharedCheck_2374_ == 0)
{
v___x_2369_ = v___x_2343_;
v_isShared_2370_ = v_isSharedCheck_2374_;
goto v_resetjp_2368_;
}
else
{
lean_inc(v_a_2367_);
lean_dec(v___x_2343_);
v___x_2369_ = lean_box(0);
v_isShared_2370_ = v_isSharedCheck_2374_;
goto v_resetjp_2368_;
}
v_resetjp_2368_:
{
lean_object* v___x_2372_; 
if (v_isShared_2370_ == 0)
{
v___x_2372_ = v___x_2369_;
goto v_reusejp_2371_;
}
else
{
lean_object* v_reuseFailAlloc_2373_; 
v_reuseFailAlloc_2373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2373_, 0, v_a_2367_);
v___x_2372_ = v_reuseFailAlloc_2373_;
goto v_reusejp_2371_;
}
v_reusejp_2371_:
{
return v___x_2372_;
}
}
}
}
else
{
lean_object* v_a_2375_; lean_object* v___x_2377_; uint8_t v_isShared_2378_; uint8_t v_isSharedCheck_2382_; 
lean_dec(v_shape_2329_);
v_a_2375_ = lean_ctor_get(v___x_2336_, 0);
v_isSharedCheck_2382_ = !lean_is_exclusive(v___x_2336_);
if (v_isSharedCheck_2382_ == 0)
{
v___x_2377_ = v___x_2336_;
v_isShared_2378_ = v_isSharedCheck_2382_;
goto v_resetjp_2376_;
}
else
{
lean_inc(v_a_2375_);
lean_dec(v___x_2336_);
v___x_2377_ = lean_box(0);
v_isShared_2378_ = v_isSharedCheck_2382_;
goto v_resetjp_2376_;
}
v_resetjp_2376_:
{
lean_object* v___x_2380_; 
if (v_isShared_2378_ == 0)
{
v___x_2380_ = v___x_2377_;
goto v_reusejp_2379_;
}
else
{
lean_object* v_reuseFailAlloc_2381_; 
v_reuseFailAlloc_2381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2381_, 0, v_a_2375_);
v___x_2380_ = v_reuseFailAlloc_2381_;
goto v_reusejp_2379_;
}
v_reusejp_2379_:
{
return v___x_2380_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toCases_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvar_2328_ = stack[0].m_obj;
lean_object* v_shape_2329_ = stack[1].m_obj;
lean_object* v_a_2330_ = stack[2].m_obj;
lean_object* v_a_2331_ = stack[3].m_obj;
lean_object* v_a_2332_ = stack[4].m_obj;
lean_object* v_a_2333_ = stack[5].m_obj;
lean_object* v_res_2383_;
v_res_2383_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toCases(v_mvar_2328_, v_shape_2329_, v_a_2330_, v_a_2331_, v_a_2332_, v_a_2333_);
stack->m_obj
 = v_res_2383_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toCases___boxed(lean_object* v_mvar_2384_, lean_object* v_shape_2385_, lean_object* v_a_2386_, lean_object* v_a_2387_, lean_object* v_a_2388_, lean_object* v_a_2389_, lean_object* v_a_2390_){
_start:
{
lean_object* v_res_2391_; 
v_res_2391_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toCases(v_mvar_2384_, v_shape_2385_, v_a_2386_, v_a_2387_, v_a_2388_, v_a_2389_);
lean_dec(v_a_2389_);
lean_dec_ref(v_a_2388_);
lean_dec(v_a_2387_);
lean_dec_ref(v_a_2386_);
return v_res_2391_;
}
}
static lean_object* _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesSum___closed__1(void){
_start:
{
lean_object* v___x_2393_; lean_object* v___x_2394_; 
v___x_2393_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesSum___closed__0));
v___x_2394_ = l_Lean_stringToMessageData(v___x_2393_);
return v___x_2394_;
}
}
static lean_object* _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesSum___closed__3(void){
_start:
{
lean_object* v___x_2396_; lean_object* v___x_2397_; 
v___x_2396_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesSum___closed__2));
v___x_2397_ = l_Lean_stringToMessageData(v___x_2396_);
return v___x_2397_;
}
}
lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesSum(lean_object* v_n_2398_, lean_object* v_mvar_2399_, lean_object* v_h_2400_, lean_object* v_a_2401_, lean_object* v_a_2402_, lean_object* v_a_2403_, lean_object* v_a_2404_){
_start:
{
lean_object* v___y_2407_; lean_object* v___y_2408_; lean_object* v___y_2409_; lean_object* v___y_2410_; lean_object* v___y_2414_; lean_object* v___y_2415_; lean_object* v___y_2416_; lean_object* v___y_2417_; lean_object* v_zero_2420_; uint8_t v_isZero_2421_; 
v_zero_2420_ = lean_unsigned_to_nat(0u);
v_isZero_2421_ = lean_nat_dec_eq(v_n_2398_, v_zero_2420_);
if (v_isZero_2421_ == 1)
{
lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; 
v___x_2422_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2422_, 0, v_h_2400_);
lean_ctor_set(v___x_2422_, 1, v_mvar_2399_);
v___x_2423_ = lean_box(0);
v___x_2424_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2424_, 0, v___x_2422_);
lean_ctor_set(v___x_2424_, 1, v___x_2423_);
v___x_2425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2425_, 0, v___x_2424_);
return v___x_2425_;
}
else
{
lean_object* v_one_2426_; lean_object* v_n_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; 
v_one_2426_ = lean_unsigned_to_nat(1u);
v_n_2427_ = lean_nat_sub(v_n_2398_, v_one_2426_);
v___x_2428_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toCases___closed__0));
v___x_2429_ = lean_box(0);
v___x_2430_ = l_Lean_MVarId_cases(v_mvar_2399_, v_h_2400_, v___x_2428_, v_isZero_2421_, v___x_2429_, v_a_2401_, v_a_2402_, v_a_2403_, v_a_2404_);
if (lean_obj_tag(v___x_2430_) == 0)
{
lean_object* v_a_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; uint8_t v___x_2434_; 
v_a_2431_ = lean_ctor_get(v___x_2430_, 0);
lean_inc(v_a_2431_);
lean_dec_ref_known(v___x_2430_, 1);
v___x_2432_ = lean_array_get_size(v_a_2431_);
v___x_2433_ = lean_unsigned_to_nat(2u);
v___x_2434_ = lean_nat_dec_eq(v___x_2432_, v___x_2433_);
if (v___x_2434_ == 0)
{
lean_object* v___x_2435_; lean_object* v___x_2436_; 
lean_dec(v_a_2431_);
lean_dec(v_n_2427_);
v___x_2435_ = lean_obj_once(&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesSum___closed__3, &l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesSum___closed__3_once, _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesSum___closed__3);
v___x_2436_ = l_Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0___redArg(v___x_2435_, v_a_2401_, v_a_2402_, v_a_2403_, v_a_2404_);
return v___x_2436_;
}
else
{
lean_object* v___x_2437_; lean_object* v_toInductionSubgoal_2438_; lean_object* v___x_2440_; uint8_t v_isShared_2441_; uint8_t v_isSharedCheck_2476_; 
v___x_2437_ = lean_array_fget(v_a_2431_, v_zero_2420_);
v_toInductionSubgoal_2438_ = lean_ctor_get(v___x_2437_, 0);
v_isSharedCheck_2476_ = !lean_is_exclusive(v___x_2437_);
if (v_isSharedCheck_2476_ == 0)
{
lean_object* v_unused_2477_; 
v_unused_2477_ = lean_ctor_get(v___x_2437_, 1);
lean_dec(v_unused_2477_);
v___x_2440_ = v___x_2437_;
v_isShared_2441_ = v_isSharedCheck_2476_;
goto v_resetjp_2439_;
}
else
{
lean_inc(v_toInductionSubgoal_2438_);
lean_dec(v___x_2437_);
v___x_2440_ = lean_box(0);
v_isShared_2441_ = v_isSharedCheck_2476_;
goto v_resetjp_2439_;
}
v_resetjp_2439_:
{
lean_object* v_mvarId_2442_; lean_object* v_fields_2443_; lean_object* v___x_2444_; uint8_t v___x_2445_; 
v_mvarId_2442_ = lean_ctor_get(v_toInductionSubgoal_2438_, 0);
lean_inc(v_mvarId_2442_);
v_fields_2443_ = lean_ctor_get(v_toInductionSubgoal_2438_, 1);
lean_inc_ref(v_fields_2443_);
lean_dec_ref(v_toInductionSubgoal_2438_);
v___x_2444_ = lean_array_get_size(v_fields_2443_);
v___x_2445_ = lean_nat_dec_eq(v___x_2444_, v_one_2426_);
if (v___x_2445_ == 0)
{
lean_dec_ref(v_fields_2443_);
lean_dec(v_mvarId_2442_);
lean_del_object(v___x_2440_);
lean_dec(v_a_2431_);
lean_dec(v_n_2427_);
v___y_2414_ = v_a_2401_;
v___y_2415_ = v_a_2402_;
v___y_2416_ = v_a_2403_;
v___y_2417_ = v_a_2404_;
goto v___jp_2413_;
}
else
{
lean_object* v___x_2446_; 
v___x_2446_ = lean_array_fget(v_fields_2443_, v_zero_2420_);
lean_dec_ref(v_fields_2443_);
if (lean_obj_tag(v___x_2446_) == 1)
{
lean_object* v_fvarId_2447_; lean_object* v___x_2448_; lean_object* v_toInductionSubgoal_2449_; lean_object* v___x_2451_; uint8_t v_isShared_2452_; uint8_t v_isSharedCheck_2474_; 
v_fvarId_2447_ = lean_ctor_get(v___x_2446_, 0);
lean_inc(v_fvarId_2447_);
lean_dec_ref_known(v___x_2446_, 1);
v___x_2448_ = lean_array_fget(v_a_2431_, v_one_2426_);
lean_dec(v_a_2431_);
v_toInductionSubgoal_2449_ = lean_ctor_get(v___x_2448_, 0);
v_isSharedCheck_2474_ = !lean_is_exclusive(v___x_2448_);
if (v_isSharedCheck_2474_ == 0)
{
lean_object* v_unused_2475_; 
v_unused_2475_ = lean_ctor_get(v___x_2448_, 1);
lean_dec(v_unused_2475_);
v___x_2451_ = v___x_2448_;
v_isShared_2452_ = v_isSharedCheck_2474_;
goto v_resetjp_2450_;
}
else
{
lean_inc(v_toInductionSubgoal_2449_);
lean_dec(v___x_2448_);
v___x_2451_ = lean_box(0);
v_isShared_2452_ = v_isSharedCheck_2474_;
goto v_resetjp_2450_;
}
v_resetjp_2450_:
{
lean_object* v_mvarId_2453_; lean_object* v_fields_2454_; lean_object* v___x_2455_; uint8_t v___x_2456_; 
v_mvarId_2453_ = lean_ctor_get(v_toInductionSubgoal_2449_, 0);
lean_inc(v_mvarId_2453_);
v_fields_2454_ = lean_ctor_get(v_toInductionSubgoal_2449_, 1);
lean_inc_ref(v_fields_2454_);
lean_dec_ref(v_toInductionSubgoal_2449_);
v___x_2455_ = lean_array_get_size(v_fields_2454_);
v___x_2456_ = lean_nat_dec_eq(v___x_2455_, v_one_2426_);
if (v___x_2456_ == 0)
{
lean_dec_ref(v_fields_2454_);
lean_dec(v_mvarId_2453_);
lean_del_object(v___x_2451_);
lean_dec(v_fvarId_2447_);
lean_dec(v_mvarId_2442_);
lean_del_object(v___x_2440_);
lean_dec(v_n_2427_);
v___y_2407_ = v_a_2401_;
v___y_2408_ = v_a_2402_;
v___y_2409_ = v_a_2403_;
v___y_2410_ = v_a_2404_;
goto v___jp_2406_;
}
else
{
lean_object* v___x_2457_; 
v___x_2457_ = lean_array_fget(v_fields_2454_, v_zero_2420_);
lean_dec_ref(v_fields_2454_);
if (lean_obj_tag(v___x_2457_) == 1)
{
lean_object* v_fvarId_2458_; lean_object* v___x_2459_; 
v_fvarId_2458_ = lean_ctor_get(v___x_2457_, 0);
lean_inc(v_fvarId_2458_);
lean_dec_ref_known(v___x_2457_, 1);
v___x_2459_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesSum(v_n_2427_, v_mvarId_2453_, v_fvarId_2458_, v_a_2401_, v_a_2402_, v_a_2403_, v_a_2404_);
lean_dec(v_n_2427_);
if (lean_obj_tag(v___x_2459_) == 0)
{
lean_object* v_a_2460_; lean_object* v___x_2462_; uint8_t v_isShared_2463_; uint8_t v_isSharedCheck_2473_; 
v_a_2460_ = lean_ctor_get(v___x_2459_, 0);
v_isSharedCheck_2473_ = !lean_is_exclusive(v___x_2459_);
if (v_isSharedCheck_2473_ == 0)
{
v___x_2462_ = v___x_2459_;
v_isShared_2463_ = v_isSharedCheck_2473_;
goto v_resetjp_2461_;
}
else
{
lean_inc(v_a_2460_);
lean_dec(v___x_2459_);
v___x_2462_ = lean_box(0);
v_isShared_2463_ = v_isSharedCheck_2473_;
goto v_resetjp_2461_;
}
v_resetjp_2461_:
{
lean_object* v___x_2465_; 
if (v_isShared_2452_ == 0)
{
lean_ctor_set(v___x_2451_, 1, v_mvarId_2442_);
lean_ctor_set(v___x_2451_, 0, v_fvarId_2447_);
v___x_2465_ = v___x_2451_;
goto v_reusejp_2464_;
}
else
{
lean_object* v_reuseFailAlloc_2472_; 
v_reuseFailAlloc_2472_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2472_, 0, v_fvarId_2447_);
lean_ctor_set(v_reuseFailAlloc_2472_, 1, v_mvarId_2442_);
v___x_2465_ = v_reuseFailAlloc_2472_;
goto v_reusejp_2464_;
}
v_reusejp_2464_:
{
lean_object* v___x_2467_; 
if (v_isShared_2441_ == 0)
{
lean_ctor_set_tag(v___x_2440_, 1);
lean_ctor_set(v___x_2440_, 1, v_a_2460_);
lean_ctor_set(v___x_2440_, 0, v___x_2465_);
v___x_2467_ = v___x_2440_;
goto v_reusejp_2466_;
}
else
{
lean_object* v_reuseFailAlloc_2471_; 
v_reuseFailAlloc_2471_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2471_, 0, v___x_2465_);
lean_ctor_set(v_reuseFailAlloc_2471_, 1, v_a_2460_);
v___x_2467_ = v_reuseFailAlloc_2471_;
goto v_reusejp_2466_;
}
v_reusejp_2466_:
{
lean_object* v___x_2469_; 
if (v_isShared_2463_ == 0)
{
lean_ctor_set(v___x_2462_, 0, v___x_2467_);
v___x_2469_ = v___x_2462_;
goto v_reusejp_2468_;
}
else
{
lean_object* v_reuseFailAlloc_2470_; 
v_reuseFailAlloc_2470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2470_, 0, v___x_2467_);
v___x_2469_ = v_reuseFailAlloc_2470_;
goto v_reusejp_2468_;
}
v_reusejp_2468_:
{
return v___x_2469_;
}
}
}
}
}
else
{
lean_del_object(v___x_2451_);
lean_dec(v_fvarId_2447_);
lean_dec(v_mvarId_2442_);
lean_del_object(v___x_2440_);
return v___x_2459_;
}
}
else
{
lean_dec(v___x_2457_);
lean_dec(v_mvarId_2453_);
lean_del_object(v___x_2451_);
lean_dec(v_fvarId_2447_);
lean_dec(v_mvarId_2442_);
lean_del_object(v___x_2440_);
lean_dec(v_n_2427_);
v___y_2407_ = v_a_2401_;
v___y_2408_ = v_a_2402_;
v___y_2409_ = v_a_2403_;
v___y_2410_ = v_a_2404_;
goto v___jp_2406_;
}
}
}
}
else
{
lean_dec(v___x_2446_);
lean_dec(v_mvarId_2442_);
lean_del_object(v___x_2440_);
lean_dec(v_a_2431_);
lean_dec(v_n_2427_);
v___y_2414_ = v_a_2401_;
v___y_2415_ = v_a_2402_;
v___y_2416_ = v_a_2403_;
v___y_2417_ = v_a_2404_;
goto v___jp_2413_;
}
}
}
}
}
else
{
lean_object* v_a_2478_; lean_object* v___x_2480_; uint8_t v_isShared_2481_; uint8_t v_isSharedCheck_2485_; 
lean_dec(v_n_2427_);
v_a_2478_ = lean_ctor_get(v___x_2430_, 0);
v_isSharedCheck_2485_ = !lean_is_exclusive(v___x_2430_);
if (v_isSharedCheck_2485_ == 0)
{
v___x_2480_ = v___x_2430_;
v_isShared_2481_ = v_isSharedCheck_2485_;
goto v_resetjp_2479_;
}
else
{
lean_inc(v_a_2478_);
lean_dec(v___x_2430_);
v___x_2480_ = lean_box(0);
v_isShared_2481_ = v_isSharedCheck_2485_;
goto v_resetjp_2479_;
}
v_resetjp_2479_:
{
lean_object* v___x_2483_; 
if (v_isShared_2481_ == 0)
{
v___x_2483_ = v___x_2480_;
goto v_reusejp_2482_;
}
else
{
lean_object* v_reuseFailAlloc_2484_; 
v_reuseFailAlloc_2484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2484_, 0, v_a_2478_);
v___x_2483_ = v_reuseFailAlloc_2484_;
goto v_reusejp_2482_;
}
v_reusejp_2482_:
{
return v___x_2483_;
}
}
}
}
v___jp_2406_:
{
lean_object* v___x_2411_; lean_object* v___x_2412_; 
v___x_2411_ = lean_obj_once(&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesSum___closed__1, &l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesSum___closed__1_once, _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesSum___closed__1);
v___x_2412_ = l_Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0___redArg(v___x_2411_, v___y_2407_, v___y_2408_, v___y_2409_, v___y_2410_);
return v___x_2412_;
}
v___jp_2413_:
{
lean_object* v___x_2418_; lean_object* v___x_2419_; 
v___x_2418_ = lean_obj_once(&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesSum___closed__1, &l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesSum___closed__1_once, _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesSum___closed__1);
v___x_2419_ = l_Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0___redArg(v___x_2418_, v___y_2414_, v___y_2415_, v___y_2416_, v___y_2417_);
return v___x_2419_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesSum_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_2398_ = stack[0].m_obj;
lean_object* v_mvar_2399_ = stack[1].m_obj;
lean_object* v_h_2400_ = stack[2].m_obj;
lean_object* v_a_2401_ = stack[3].m_obj;
lean_object* v_a_2402_ = stack[4].m_obj;
lean_object* v_a_2403_ = stack[5].m_obj;
lean_object* v_a_2404_ = stack[6].m_obj;
lean_object* v_res_2486_;
v_res_2486_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesSum(v_n_2398_, v_mvar_2399_, v_h_2400_, v_a_2401_, v_a_2402_, v_a_2403_, v_a_2404_);
stack->m_obj
 = v_res_2486_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesSum___boxed(lean_object* v_n_2487_, lean_object* v_mvar_2488_, lean_object* v_h_2489_, lean_object* v_a_2490_, lean_object* v_a_2491_, lean_object* v_a_2492_, lean_object* v_a_2493_, lean_object* v_a_2494_){
_start:
{
lean_object* v_res_2495_; 
v_res_2495_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesSum(v_n_2487_, v_mvar_2488_, v_h_2489_, v_a_2490_, v_a_2491_, v_a_2492_, v_a_2493_);
lean_dec(v_a_2493_);
lean_dec_ref(v_a_2492_);
lean_dec(v_a_2491_);
lean_dec_ref(v_a_2490_);
lean_dec(v_n_2487_);
return v_res_2495_;
}
}
static lean_object* _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesProd___closed__1(void){
_start:
{
lean_object* v___x_2497_; lean_object* v___x_2498_; 
v___x_2497_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesProd___closed__0));
v___x_2498_ = l_Lean_stringToMessageData(v___x_2497_);
return v___x_2498_;
}
}
lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesProd(lean_object* v_n_2499_, lean_object* v_mvar_2500_, lean_object* v_h_2501_, lean_object* v_a_2502_, lean_object* v_a_2503_, lean_object* v_a_2504_, lean_object* v_a_2505_){
_start:
{
lean_object* v___y_2508_; lean_object* v___y_2509_; lean_object* v___y_2510_; lean_object* v___y_2511_; lean_object* v_zero_2514_; uint8_t v_isZero_2515_; 
v_zero_2514_ = lean_unsigned_to_nat(0u);
v_isZero_2515_ = lean_nat_dec_eq(v_n_2499_, v_zero_2514_);
if (v_isZero_2515_ == 1)
{
lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; 
v___x_2516_ = lean_box(0);
v___x_2517_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2517_, 0, v_h_2501_);
lean_ctor_set(v___x_2517_, 1, v___x_2516_);
v___x_2518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2518_, 0, v_mvar_2500_);
lean_ctor_set(v___x_2518_, 1, v___x_2517_);
v___x_2519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2519_, 0, v___x_2518_);
return v___x_2519_;
}
else
{
lean_object* v_one_2520_; lean_object* v_n_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; 
v_one_2520_ = lean_unsigned_to_nat(1u);
v_n_2521_ = lean_nat_sub(v_n_2499_, v_one_2520_);
v___x_2522_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toCases___closed__0));
v___x_2523_ = lean_box(0);
v___x_2524_ = l_Lean_MVarId_cases(v_mvar_2500_, v_h_2501_, v___x_2522_, v_isZero_2515_, v___x_2523_, v_a_2502_, v_a_2503_, v_a_2504_, v_a_2505_);
if (lean_obj_tag(v___x_2524_) == 0)
{
lean_object* v_a_2525_; lean_object* v___x_2526_; uint8_t v___x_2527_; 
v_a_2525_ = lean_ctor_get(v___x_2524_, 0);
lean_inc(v_a_2525_);
lean_dec_ref_known(v___x_2524_, 1);
v___x_2526_ = lean_array_get_size(v_a_2525_);
v___x_2527_ = lean_nat_dec_eq(v___x_2526_, v_one_2520_);
if (v___x_2527_ == 0)
{
lean_object* v___x_2528_; lean_object* v___x_2529_; 
lean_dec(v_a_2525_);
lean_dec(v_n_2521_);
v___x_2528_ = lean_obj_once(&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesProd___closed__1, &l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesProd___closed__1_once, _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesProd___closed__1);
v___x_2529_ = l_Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0___redArg(v___x_2528_, v_a_2502_, v_a_2503_, v_a_2504_, v_a_2505_);
return v___x_2529_;
}
else
{
lean_object* v___x_2530_; lean_object* v_toInductionSubgoal_2531_; lean_object* v___x_2533_; uint8_t v_isShared_2534_; uint8_t v_isSharedCheck_2565_; 
v___x_2530_ = lean_array_fget(v_a_2525_, v_zero_2514_);
lean_dec(v_a_2525_);
v_toInductionSubgoal_2531_ = lean_ctor_get(v___x_2530_, 0);
v_isSharedCheck_2565_ = !lean_is_exclusive(v___x_2530_);
if (v_isSharedCheck_2565_ == 0)
{
lean_object* v_unused_2566_; 
v_unused_2566_ = lean_ctor_get(v___x_2530_, 1);
lean_dec(v_unused_2566_);
v___x_2533_ = v___x_2530_;
v_isShared_2534_ = v_isSharedCheck_2565_;
goto v_resetjp_2532_;
}
else
{
lean_inc(v_toInductionSubgoal_2531_);
lean_dec(v___x_2530_);
v___x_2533_ = lean_box(0);
v_isShared_2534_ = v_isSharedCheck_2565_;
goto v_resetjp_2532_;
}
v_resetjp_2532_:
{
lean_object* v_mvarId_2535_; lean_object* v_fields_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; uint8_t v___x_2539_; 
v_mvarId_2535_ = lean_ctor_get(v_toInductionSubgoal_2531_, 0);
lean_inc(v_mvarId_2535_);
v_fields_2536_ = lean_ctor_get(v_toInductionSubgoal_2531_, 1);
lean_inc_ref(v_fields_2536_);
lean_dec_ref(v_toInductionSubgoal_2531_);
v___x_2537_ = lean_array_get_size(v_fields_2536_);
v___x_2538_ = lean_unsigned_to_nat(2u);
v___x_2539_ = lean_nat_dec_eq(v___x_2537_, v___x_2538_);
if (v___x_2539_ == 0)
{
lean_dec_ref(v_fields_2536_);
lean_dec(v_mvarId_2535_);
lean_del_object(v___x_2533_);
lean_dec(v_n_2521_);
v___y_2508_ = v_a_2502_;
v___y_2509_ = v_a_2503_;
v___y_2510_ = v_a_2504_;
v___y_2511_ = v_a_2505_;
goto v___jp_2507_;
}
else
{
lean_object* v___x_2540_; 
v___x_2540_ = lean_array_fget_borrowed(v_fields_2536_, v_zero_2514_);
if (lean_obj_tag(v___x_2540_) == 1)
{
lean_object* v_fvarId_2541_; lean_object* v___x_2542_; 
v_fvarId_2541_ = lean_ctor_get(v___x_2540_, 0);
lean_inc(v_fvarId_2541_);
v___x_2542_ = lean_array_fget(v_fields_2536_, v_one_2520_);
lean_dec_ref(v_fields_2536_);
if (lean_obj_tag(v___x_2542_) == 1)
{
lean_object* v_fvarId_2543_; lean_object* v___x_2544_; 
v_fvarId_2543_ = lean_ctor_get(v___x_2542_, 0);
lean_inc(v_fvarId_2543_);
lean_dec_ref_known(v___x_2542_, 1);
v___x_2544_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesProd(v_n_2521_, v_mvarId_2535_, v_fvarId_2543_, v_a_2502_, v_a_2503_, v_a_2504_, v_a_2505_);
lean_dec(v_n_2521_);
if (lean_obj_tag(v___x_2544_) == 0)
{
lean_object* v_a_2545_; lean_object* v___x_2547_; uint8_t v_isShared_2548_; uint8_t v_isSharedCheck_2564_; 
v_a_2545_ = lean_ctor_get(v___x_2544_, 0);
v_isSharedCheck_2564_ = !lean_is_exclusive(v___x_2544_);
if (v_isSharedCheck_2564_ == 0)
{
v___x_2547_ = v___x_2544_;
v_isShared_2548_ = v_isSharedCheck_2564_;
goto v_resetjp_2546_;
}
else
{
lean_inc(v_a_2545_);
lean_dec(v___x_2544_);
v___x_2547_ = lean_box(0);
v_isShared_2548_ = v_isSharedCheck_2564_;
goto v_resetjp_2546_;
}
v_resetjp_2546_:
{
lean_object* v_fst_2549_; lean_object* v_snd_2550_; lean_object* v___x_2552_; uint8_t v_isShared_2553_; uint8_t v_isSharedCheck_2563_; 
v_fst_2549_ = lean_ctor_get(v_a_2545_, 0);
v_snd_2550_ = lean_ctor_get(v_a_2545_, 1);
v_isSharedCheck_2563_ = !lean_is_exclusive(v_a_2545_);
if (v_isSharedCheck_2563_ == 0)
{
v___x_2552_ = v_a_2545_;
v_isShared_2553_ = v_isSharedCheck_2563_;
goto v_resetjp_2551_;
}
else
{
lean_inc(v_snd_2550_);
lean_inc(v_fst_2549_);
lean_dec(v_a_2545_);
v___x_2552_ = lean_box(0);
v_isShared_2553_ = v_isSharedCheck_2563_;
goto v_resetjp_2551_;
}
v_resetjp_2551_:
{
lean_object* v___x_2555_; 
if (v_isShared_2534_ == 0)
{
lean_ctor_set_tag(v___x_2533_, 1);
lean_ctor_set(v___x_2533_, 1, v_snd_2550_);
lean_ctor_set(v___x_2533_, 0, v_fvarId_2541_);
v___x_2555_ = v___x_2533_;
goto v_reusejp_2554_;
}
else
{
lean_object* v_reuseFailAlloc_2562_; 
v_reuseFailAlloc_2562_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2562_, 0, v_fvarId_2541_);
lean_ctor_set(v_reuseFailAlloc_2562_, 1, v_snd_2550_);
v___x_2555_ = v_reuseFailAlloc_2562_;
goto v_reusejp_2554_;
}
v_reusejp_2554_:
{
lean_object* v___x_2557_; 
if (v_isShared_2553_ == 0)
{
lean_ctor_set(v___x_2552_, 1, v___x_2555_);
v___x_2557_ = v___x_2552_;
goto v_reusejp_2556_;
}
else
{
lean_object* v_reuseFailAlloc_2561_; 
v_reuseFailAlloc_2561_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2561_, 0, v_fst_2549_);
lean_ctor_set(v_reuseFailAlloc_2561_, 1, v___x_2555_);
v___x_2557_ = v_reuseFailAlloc_2561_;
goto v_reusejp_2556_;
}
v_reusejp_2556_:
{
lean_object* v___x_2559_; 
if (v_isShared_2548_ == 0)
{
lean_ctor_set(v___x_2547_, 0, v___x_2557_);
v___x_2559_ = v___x_2547_;
goto v_reusejp_2558_;
}
else
{
lean_object* v_reuseFailAlloc_2560_; 
v_reuseFailAlloc_2560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2560_, 0, v___x_2557_);
v___x_2559_ = v_reuseFailAlloc_2560_;
goto v_reusejp_2558_;
}
v_reusejp_2558_:
{
return v___x_2559_;
}
}
}
}
}
}
else
{
lean_dec(v_fvarId_2541_);
lean_del_object(v___x_2533_);
return v___x_2544_;
}
}
else
{
lean_dec(v___x_2542_);
lean_dec(v_fvarId_2541_);
lean_dec(v_mvarId_2535_);
lean_del_object(v___x_2533_);
lean_dec(v_n_2521_);
v___y_2508_ = v_a_2502_;
v___y_2509_ = v_a_2503_;
v___y_2510_ = v_a_2504_;
v___y_2511_ = v_a_2505_;
goto v___jp_2507_;
}
}
else
{
lean_dec_ref(v_fields_2536_);
lean_dec(v_mvarId_2535_);
lean_del_object(v___x_2533_);
lean_dec(v_n_2521_);
v___y_2508_ = v_a_2502_;
v___y_2509_ = v_a_2503_;
v___y_2510_ = v_a_2504_;
v___y_2511_ = v_a_2505_;
goto v___jp_2507_;
}
}
}
}
}
else
{
lean_object* v_a_2567_; lean_object* v___x_2569_; uint8_t v_isShared_2570_; uint8_t v_isSharedCheck_2574_; 
lean_dec(v_n_2521_);
v_a_2567_ = lean_ctor_get(v___x_2524_, 0);
v_isSharedCheck_2574_ = !lean_is_exclusive(v___x_2524_);
if (v_isSharedCheck_2574_ == 0)
{
v___x_2569_ = v___x_2524_;
v_isShared_2570_ = v_isSharedCheck_2574_;
goto v_resetjp_2568_;
}
else
{
lean_inc(v_a_2567_);
lean_dec(v___x_2524_);
v___x_2569_ = lean_box(0);
v_isShared_2570_ = v_isSharedCheck_2574_;
goto v_resetjp_2568_;
}
v_resetjp_2568_:
{
lean_object* v___x_2572_; 
if (v_isShared_2570_ == 0)
{
v___x_2572_ = v___x_2569_;
goto v_reusejp_2571_;
}
else
{
lean_object* v_reuseFailAlloc_2573_; 
v_reuseFailAlloc_2573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2573_, 0, v_a_2567_);
v___x_2572_ = v_reuseFailAlloc_2573_;
goto v_reusejp_2571_;
}
v_reusejp_2571_:
{
return v___x_2572_;
}
}
}
}
v___jp_2507_:
{
lean_object* v___x_2512_; lean_object* v___x_2513_; 
v___x_2512_ = lean_obj_once(&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesSum___closed__1, &l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesSum___closed__1_once, _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesSum___closed__1);
v___x_2513_ = l_Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0___redArg(v___x_2512_, v___y_2508_, v___y_2509_, v___y_2510_, v___y_2511_);
return v___x_2513_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesProd_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_2499_ = stack[0].m_obj;
lean_object* v_mvar_2500_ = stack[1].m_obj;
lean_object* v_h_2501_ = stack[2].m_obj;
lean_object* v_a_2502_ = stack[3].m_obj;
lean_object* v_a_2503_ = stack[4].m_obj;
lean_object* v_a_2504_ = stack[5].m_obj;
lean_object* v_a_2505_ = stack[6].m_obj;
lean_object* v_res_2575_;
v_res_2575_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesProd(v_n_2499_, v_mvar_2500_, v_h_2501_, v_a_2502_, v_a_2503_, v_a_2504_, v_a_2505_);
stack->m_obj
 = v_res_2575_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesProd___boxed(lean_object* v_n_2576_, lean_object* v_mvar_2577_, lean_object* v_h_2578_, lean_object* v_a_2579_, lean_object* v_a_2580_, lean_object* v_a_2581_, lean_object* v_a_2582_, lean_object* v_a_2583_){
_start:
{
lean_object* v_res_2584_; 
v_res_2584_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesProd(v_n_2576_, v_mvar_2577_, v_h_2578_, v_a_2579_, v_a_2580_, v_a_2581_, v_a_2582_);
lean_dec(v_a_2582_);
lean_dec_ref(v_a_2581_);
lean_dec(v_a_2580_);
lean_dec_ref(v_a_2579_);
lean_dec(v_n_2576_);
return v_res_2584_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_listBoolMerge___redArg(lean_object* v_x_2585_, lean_object* v_x_2586_){
_start:
{
if (lean_obj_tag(v_x_2585_) == 0)
{
lean_object* v___x_2587_; 
lean_dec(v_x_2586_);
v___x_2587_ = lean_box(0);
return v___x_2587_;
}
else
{
lean_object* v_head_2588_; uint8_t v___x_2589_; 
v_head_2588_ = lean_ctor_get(v_x_2585_, 0);
v___x_2589_ = lean_unbox(v_head_2588_);
if (v___x_2589_ == 0)
{
lean_object* v_tail_2590_; lean_object* v___x_2592_; uint8_t v_isShared_2593_; uint8_t v_isSharedCheck_2599_; 
v_tail_2590_ = lean_ctor_get(v_x_2585_, 1);
v_isSharedCheck_2599_ = !lean_is_exclusive(v_x_2585_);
if (v_isSharedCheck_2599_ == 0)
{
lean_object* v_unused_2600_; 
v_unused_2600_ = lean_ctor_get(v_x_2585_, 0);
lean_dec(v_unused_2600_);
v___x_2592_ = v_x_2585_;
v_isShared_2593_ = v_isSharedCheck_2599_;
goto v_resetjp_2591_;
}
else
{
lean_inc(v_tail_2590_);
lean_dec(v_x_2585_);
v___x_2592_ = lean_box(0);
v_isShared_2593_ = v_isSharedCheck_2599_;
goto v_resetjp_2591_;
}
v_resetjp_2591_:
{
lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2597_; 
v___x_2594_ = lean_box(0);
v___x_2595_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_listBoolMerge___redArg(v_tail_2590_, v_x_2586_);
if (v_isShared_2593_ == 0)
{
lean_ctor_set(v___x_2592_, 1, v___x_2595_);
lean_ctor_set(v___x_2592_, 0, v___x_2594_);
v___x_2597_ = v___x_2592_;
goto v_reusejp_2596_;
}
else
{
lean_object* v_reuseFailAlloc_2598_; 
v_reuseFailAlloc_2598_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2598_, 0, v___x_2594_);
lean_ctor_set(v_reuseFailAlloc_2598_, 1, v___x_2595_);
v___x_2597_ = v_reuseFailAlloc_2598_;
goto v_reusejp_2596_;
}
v_reusejp_2596_:
{
return v___x_2597_;
}
}
}
else
{
if (lean_obj_tag(v_x_2586_) == 0)
{
lean_object* v___x_2601_; 
lean_dec_ref_known(v_x_2585_, 2);
v___x_2601_ = lean_box(0);
return v___x_2601_;
}
else
{
lean_object* v_tail_2602_; lean_object* v_head_2603_; lean_object* v_tail_2604_; lean_object* v___x_2606_; uint8_t v_isShared_2607_; uint8_t v_isSharedCheck_2613_; 
v_tail_2602_ = lean_ctor_get(v_x_2585_, 1);
lean_inc(v_tail_2602_);
lean_dec_ref_known(v_x_2585_, 2);
v_head_2603_ = lean_ctor_get(v_x_2586_, 0);
v_tail_2604_ = lean_ctor_get(v_x_2586_, 1);
v_isSharedCheck_2613_ = !lean_is_exclusive(v_x_2586_);
if (v_isSharedCheck_2613_ == 0)
{
v___x_2606_ = v_x_2586_;
v_isShared_2607_ = v_isSharedCheck_2613_;
goto v_resetjp_2605_;
}
else
{
lean_inc(v_tail_2604_);
lean_inc(v_head_2603_);
lean_dec(v_x_2586_);
v___x_2606_ = lean_box(0);
v_isShared_2607_ = v_isSharedCheck_2613_;
goto v_resetjp_2605_;
}
v_resetjp_2605_:
{
lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2611_; 
v___x_2608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2608_, 0, v_head_2603_);
v___x_2609_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_listBoolMerge___redArg(v_tail_2602_, v_tail_2604_);
if (v_isShared_2607_ == 0)
{
lean_ctor_set(v___x_2606_, 1, v___x_2609_);
lean_ctor_set(v___x_2606_, 0, v___x_2608_);
v___x_2611_ = v___x_2606_;
goto v_reusejp_2610_;
}
else
{
lean_object* v_reuseFailAlloc_2612_; 
v_reuseFailAlloc_2612_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2612_, 0, v___x_2608_);
lean_ctor_set(v_reuseFailAlloc_2612_, 1, v___x_2609_);
v___x_2611_ = v_reuseFailAlloc_2612_;
goto v_reusejp_2610_;
}
v_reusejp_2610_:
{
return v___x_2611_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_listBoolMerge(lean_object* v_00_u03b1_2614_, lean_object* v_x_2615_, lean_object* v_x_2616_){
_start:
{
lean_object* v___x_2617_; 
v___x_2617_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_listBoolMerge___redArg(v_x_2615_, v_x_2616_);
return v___x_2617_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__2_spec__3(lean_object* v_a_2618_, lean_object* v_a_2619_){
_start:
{
if (lean_obj_tag(v_a_2618_) == 0)
{
lean_object* v___x_2620_; 
v___x_2620_ = l_List_reverse___redArg(v_a_2619_);
return v___x_2620_;
}
else
{
lean_object* v_head_2621_; lean_object* v_tail_2622_; lean_object* v___x_2624_; uint8_t v_isShared_2625_; uint8_t v_isSharedCheck_2631_; 
v_head_2621_ = lean_ctor_get(v_a_2618_, 0);
v_tail_2622_ = lean_ctor_get(v_a_2618_, 1);
v_isSharedCheck_2631_ = !lean_is_exclusive(v_a_2618_);
if (v_isSharedCheck_2631_ == 0)
{
v___x_2624_ = v_a_2618_;
v_isShared_2625_ = v_isSharedCheck_2631_;
goto v_resetjp_2623_;
}
else
{
lean_inc(v_tail_2622_);
lean_inc(v_head_2621_);
lean_dec(v_a_2618_);
v___x_2624_ = lean_box(0);
v_isShared_2625_ = v_isSharedCheck_2631_;
goto v_resetjp_2623_;
}
v_resetjp_2623_:
{
lean_object* v___x_2626_; lean_object* v___x_2628_; 
v___x_2626_ = l_Lean_mkLevelParam(v_head_2621_);
if (v_isShared_2625_ == 0)
{
lean_ctor_set(v___x_2624_, 1, v_a_2619_);
lean_ctor_set(v___x_2624_, 0, v___x_2626_);
v___x_2628_ = v___x_2624_;
goto v_reusejp_2627_;
}
else
{
lean_object* v_reuseFailAlloc_2630_; 
v_reuseFailAlloc_2630_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2630_, 0, v___x_2626_);
lean_ctor_set(v_reuseFailAlloc_2630_, 1, v_a_2619_);
v___x_2628_ = v_reuseFailAlloc_2630_;
goto v_reusejp_2627_;
}
v_reusejp_2627_:
{
v_a_2618_ = v_tail_2622_;
v_a_2619_ = v___x_2628_;
goto _start;
}
}
}
}
}
lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__2_spec__2(lean_object* v_constName_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_){
_start:
{
lean_object* v___x_2638_; lean_object* v_env_2639_; uint8_t v___x_2640_; lean_object* v___x_2641_; 
v___x_2638_ = lean_st_ref_get(v___y_2636_);
v_env_2639_ = lean_ctor_get(v___x_2638_, 0);
lean_inc_ref(v_env_2639_);
lean_dec(v___x_2638_);
v___x_2640_ = 0;
lean_inc(v_constName_2632_);
v___x_2641_ = l_Lean_Environment_findConstVal_x3f(v_env_2639_, v_constName_2632_, v___x_2640_);
if (lean_obj_tag(v___x_2641_) == 0)
{
lean_object* v___x_2642_; 
v___x_2642_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0___redArg(v_constName_2632_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_);
return v___x_2642_;
}
else
{
lean_object* v_val_2643_; lean_object* v___x_2645_; uint8_t v_isShared_2646_; uint8_t v_isSharedCheck_2650_; 
lean_dec(v_constName_2632_);
v_val_2643_ = lean_ctor_get(v___x_2641_, 0);
v_isSharedCheck_2650_ = !lean_is_exclusive(v___x_2641_);
if (v_isSharedCheck_2650_ == 0)
{
v___x_2645_ = v___x_2641_;
v_isShared_2646_ = v_isSharedCheck_2650_;
goto v_resetjp_2644_;
}
else
{
lean_inc(v_val_2643_);
lean_dec(v___x_2641_);
v___x_2645_ = lean_box(0);
v_isShared_2646_ = v_isSharedCheck_2650_;
goto v_resetjp_2644_;
}
v_resetjp_2644_:
{
lean_object* v___x_2648_; 
if (v_isShared_2646_ == 0)
{
lean_ctor_set_tag(v___x_2645_, 0);
v___x_2648_ = v___x_2645_;
goto v_reusejp_2647_;
}
else
{
lean_object* v_reuseFailAlloc_2649_; 
v_reuseFailAlloc_2649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2649_, 0, v_val_2643_);
v___x_2648_ = v_reuseFailAlloc_2649_;
goto v_reusejp_2647_;
}
v_reusejp_2647_:
{
return v___x_2648_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__2_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_2632_ = stack[0].m_obj;
lean_object* v___y_2633_ = stack[1].m_obj;
lean_object* v___y_2634_ = stack[2].m_obj;
lean_object* v___y_2635_ = stack[3].m_obj;
lean_object* v___y_2636_ = stack[4].m_obj;
lean_object* v_res_2651_;
v_res_2651_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__2_spec__2(v_constName_2632_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_);
stack->m_obj
 = v_res_2651_;
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__2_spec__2___boxed(lean_object* v_constName_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_){
_start:
{
lean_object* v_res_2658_; 
v_res_2658_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__2_spec__2(v_constName_2652_, v___y_2653_, v___y_2654_, v___y_2655_, v___y_2656_);
lean_dec(v___y_2656_);
lean_dec_ref(v___y_2655_);
lean_dec(v___y_2654_);
lean_dec_ref(v___y_2653_);
return v_res_2658_;
}
}
lean_object* l_Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__2(lean_object* v_constName_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_){
_start:
{
lean_object* v___x_2665_; 
lean_inc(v_constName_2659_);
v___x_2665_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__2_spec__2(v_constName_2659_, v___y_2660_, v___y_2661_, v___y_2662_, v___y_2663_);
if (lean_obj_tag(v___x_2665_) == 0)
{
lean_object* v_a_2666_; lean_object* v___x_2668_; uint8_t v_isShared_2669_; uint8_t v_isSharedCheck_2677_; 
v_a_2666_ = lean_ctor_get(v___x_2665_, 0);
v_isSharedCheck_2677_ = !lean_is_exclusive(v___x_2665_);
if (v_isSharedCheck_2677_ == 0)
{
v___x_2668_ = v___x_2665_;
v_isShared_2669_ = v_isSharedCheck_2677_;
goto v_resetjp_2667_;
}
else
{
lean_inc(v_a_2666_);
lean_dec(v___x_2665_);
v___x_2668_ = lean_box(0);
v_isShared_2669_ = v_isSharedCheck_2677_;
goto v_resetjp_2667_;
}
v_resetjp_2667_:
{
lean_object* v_levelParams_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2675_; 
v_levelParams_2670_ = lean_ctor_get(v_a_2666_, 1);
lean_inc(v_levelParams_2670_);
lean_dec(v_a_2666_);
v___x_2671_ = lean_box(0);
v___x_2672_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__2_spec__3(v_levelParams_2670_, v___x_2671_);
v___x_2673_ = l_Lean_mkConst(v_constName_2659_, v___x_2672_);
if (v_isShared_2669_ == 0)
{
lean_ctor_set(v___x_2668_, 0, v___x_2673_);
v___x_2675_ = v___x_2668_;
goto v_reusejp_2674_;
}
else
{
lean_object* v_reuseFailAlloc_2676_; 
v_reuseFailAlloc_2676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2676_, 0, v___x_2673_);
v___x_2675_ = v_reuseFailAlloc_2676_;
goto v_reusejp_2674_;
}
v_reusejp_2674_:
{
return v___x_2675_;
}
}
}
else
{
lean_object* v_a_2678_; lean_object* v___x_2680_; uint8_t v_isShared_2681_; uint8_t v_isSharedCheck_2685_; 
lean_dec(v_constName_2659_);
v_a_2678_ = lean_ctor_get(v___x_2665_, 0);
v_isSharedCheck_2685_ = !lean_is_exclusive(v___x_2665_);
if (v_isSharedCheck_2685_ == 0)
{
v___x_2680_ = v___x_2665_;
v_isShared_2681_ = v_isSharedCheck_2685_;
goto v_resetjp_2679_;
}
else
{
lean_inc(v_a_2678_);
lean_dec(v___x_2665_);
v___x_2680_ = lean_box(0);
v_isShared_2681_ = v_isSharedCheck_2685_;
goto v_resetjp_2679_;
}
v_resetjp_2679_:
{
lean_object* v___x_2683_; 
if (v_isShared_2681_ == 0)
{
v___x_2683_ = v___x_2680_;
goto v_reusejp_2682_;
}
else
{
lean_object* v_reuseFailAlloc_2684_; 
v_reuseFailAlloc_2684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2684_, 0, v_a_2678_);
v___x_2683_ = v_reuseFailAlloc_2684_;
goto v_reusejp_2682_;
}
v_reusejp_2682_:
{
return v___x_2683_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_2659_ = stack[0].m_obj;
lean_object* v___y_2660_ = stack[1].m_obj;
lean_object* v___y_2661_ = stack[2].m_obj;
lean_object* v___y_2662_ = stack[3].m_obj;
lean_object* v___y_2663_ = stack[4].m_obj;
lean_object* v_res_2686_;
v_res_2686_ = l_Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__2(v_constName_2659_, v___y_2660_, v___y_2661_, v___y_2662_, v___y_2663_);
stack->m_obj
 = v_res_2686_;
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__2___boxed(lean_object* v_constName_2687_, lean_object* v___y_2688_, lean_object* v___y_2689_, lean_object* v___y_2690_, lean_object* v___y_2691_, lean_object* v___y_2692_){
_start:
{
lean_object* v_res_2693_; 
v_res_2693_ = l_Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__2(v_constName_2687_, v___y_2688_, v___y_2689_, v___y_2690_, v___y_2691_);
lean_dec(v___y_2691_);
lean_dec_ref(v___y_2690_);
lean_dec(v___y_2689_);
lean_dec_ref(v___y_2688_);
return v_res_2693_;
}
}
lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__1(lean_object* v_x_2694_, lean_object* v_x_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_){
_start:
{
if (lean_obj_tag(v_x_2694_) == 0)
{
lean_object* v___x_2701_; lean_object* v___x_2702_; 
v___x_2701_ = l_List_reverse___redArg(v_x_2695_);
v___x_2702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2702_, 0, v___x_2701_);
return v___x_2702_;
}
else
{
lean_object* v_head_2703_; lean_object* v_tail_2704_; lean_object* v___x_2706_; uint8_t v_isShared_2707_; uint8_t v_isSharedCheck_2729_; 
v_head_2703_ = lean_ctor_get(v_x_2694_, 0);
v_tail_2704_ = lean_ctor_get(v_x_2694_, 1);
v_isSharedCheck_2729_ = !lean_is_exclusive(v_x_2694_);
if (v_isSharedCheck_2729_ == 0)
{
v___x_2706_ = v_x_2694_;
v_isShared_2707_ = v_isSharedCheck_2729_;
goto v_resetjp_2705_;
}
else
{
lean_inc(v_tail_2704_);
lean_inc(v_head_2703_);
lean_dec(v_x_2694_);
v___x_2706_ = lean_box(0);
v_isShared_2707_ = v_isSharedCheck_2729_;
goto v_resetjp_2705_;
}
v_resetjp_2705_:
{
lean_object* v_a_2709_; 
if (lean_obj_tag(v_head_2703_) == 0)
{
lean_object* v___x_2714_; uint8_t v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; 
v___x_2714_ = lean_box(0);
v___x_2715_ = 0;
v___x_2716_ = lean_box(0);
v___x_2717_ = l_Lean_Meta_mkFreshExprMVar(v___x_2714_, v___x_2715_, v___x_2716_, v___y_2696_, v___y_2697_, v___y_2698_, v___y_2699_);
if (lean_obj_tag(v___x_2717_) == 0)
{
lean_object* v_a_2718_; 
v_a_2718_ = lean_ctor_get(v___x_2717_, 0);
lean_inc(v_a_2718_);
lean_dec_ref_known(v___x_2717_, 1);
v_a_2709_ = v_a_2718_;
goto v___jp_2708_;
}
else
{
lean_object* v_a_2719_; lean_object* v___x_2721_; uint8_t v_isShared_2722_; uint8_t v_isSharedCheck_2726_; 
lean_del_object(v___x_2706_);
lean_dec(v_tail_2704_);
lean_dec(v_x_2695_);
v_a_2719_ = lean_ctor_get(v___x_2717_, 0);
v_isSharedCheck_2726_ = !lean_is_exclusive(v___x_2717_);
if (v_isSharedCheck_2726_ == 0)
{
v___x_2721_ = v___x_2717_;
v_isShared_2722_ = v_isSharedCheck_2726_;
goto v_resetjp_2720_;
}
else
{
lean_inc(v_a_2719_);
lean_dec(v___x_2717_);
v___x_2721_ = lean_box(0);
v_isShared_2722_ = v_isSharedCheck_2726_;
goto v_resetjp_2720_;
}
v_resetjp_2720_:
{
lean_object* v___x_2724_; 
if (v_isShared_2722_ == 0)
{
v___x_2724_ = v___x_2721_;
goto v_reusejp_2723_;
}
else
{
lean_object* v_reuseFailAlloc_2725_; 
v_reuseFailAlloc_2725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2725_, 0, v_a_2719_);
v___x_2724_ = v_reuseFailAlloc_2725_;
goto v_reusejp_2723_;
}
v_reusejp_2723_:
{
return v___x_2724_;
}
}
}
}
else
{
lean_object* v_val_2727_; lean_object* v___x_2728_; 
v_val_2727_ = lean_ctor_get(v_head_2703_, 0);
lean_inc(v_val_2727_);
lean_dec_ref_known(v_head_2703_, 1);
v___x_2728_ = l_Lean_mkFVar(v_val_2727_);
v_a_2709_ = v___x_2728_;
goto v___jp_2708_;
}
v___jp_2708_:
{
lean_object* v___x_2711_; 
if (v_isShared_2707_ == 0)
{
lean_ctor_set(v___x_2706_, 1, v_x_2695_);
lean_ctor_set(v___x_2706_, 0, v_a_2709_);
v___x_2711_ = v___x_2706_;
goto v_reusejp_2710_;
}
else
{
lean_object* v_reuseFailAlloc_2713_; 
v_reuseFailAlloc_2713_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2713_, 0, v_a_2709_);
lean_ctor_set(v_reuseFailAlloc_2713_, 1, v_x_2695_);
v___x_2711_ = v_reuseFailAlloc_2713_;
goto v_reusejp_2710_;
}
v_reusejp_2710_:
{
v_x_2694_ = v_tail_2704_;
v_x_2695_ = v___x_2711_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT void l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2694_ = stack[0].m_obj;
lean_object* v_x_2695_ = stack[1].m_obj;
lean_object* v___y_2696_ = stack[2].m_obj;
lean_object* v___y_2697_ = stack[3].m_obj;
lean_object* v___y_2698_ = stack[4].m_obj;
lean_object* v___y_2699_ = stack[5].m_obj;
lean_object* v_res_2730_;
v_res_2730_ = l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__1(v_x_2694_, v_x_2695_, v___y_2696_, v___y_2697_, v___y_2698_, v___y_2699_);
stack->m_obj
 = v_res_2730_;
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__1___boxed(lean_object* v_x_2731_, lean_object* v_x_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_){
_start:
{
lean_object* v_res_2738_; 
v_res_2738_ = l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__1(v_x_2731_, v_x_2732_, v___y_2733_, v___y_2734_, v___y_2735_, v___y_2736_);
lean_dec(v___y_2736_);
lean_dec_ref(v___y_2735_);
lean_dec(v___y_2734_);
lean_dec_ref(v___y_2733_);
return v_res_2738_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__0(lean_object* v_a_2739_, lean_object* v_a_2740_){
_start:
{
if (lean_obj_tag(v_a_2739_) == 0)
{
lean_object* v___x_2741_; 
v___x_2741_ = l_List_reverse___redArg(v_a_2740_);
return v___x_2741_;
}
else
{
lean_object* v_head_2742_; lean_object* v_tail_2743_; lean_object* v___x_2745_; uint8_t v_isShared_2746_; uint8_t v_isSharedCheck_2752_; 
v_head_2742_ = lean_ctor_get(v_a_2739_, 0);
v_tail_2743_ = lean_ctor_get(v_a_2739_, 1);
v_isSharedCheck_2752_ = !lean_is_exclusive(v_a_2739_);
if (v_isSharedCheck_2752_ == 0)
{
v___x_2745_ = v_a_2739_;
v_isShared_2746_ = v_isSharedCheck_2752_;
goto v_resetjp_2744_;
}
else
{
lean_inc(v_tail_2743_);
lean_inc(v_head_2742_);
lean_dec(v_a_2739_);
v___x_2745_ = lean_box(0);
v_isShared_2746_ = v_isSharedCheck_2752_;
goto v_resetjp_2744_;
}
v_resetjp_2744_:
{
lean_object* v___x_2747_; lean_object* v___x_2749_; 
v___x_2747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2747_, 0, v_head_2742_);
if (v_isShared_2746_ == 0)
{
lean_ctor_set(v___x_2745_, 1, v_a_2740_);
lean_ctor_set(v___x_2745_, 0, v___x_2747_);
v___x_2749_ = v___x_2745_;
goto v_reusejp_2748_;
}
else
{
lean_object* v_reuseFailAlloc_2751_; 
v_reuseFailAlloc_2751_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2751_, 0, v___x_2747_);
lean_ctor_set(v_reuseFailAlloc_2751_, 1, v_a_2740_);
v___x_2749_ = v_reuseFailAlloc_2751_;
goto v_reusejp_2748_;
}
v_reusejp_2748_:
{
v_a_2739_ = v_tail_2743_;
v_a_2740_ = v___x_2749_;
goto _start;
}
}
}
}
}
lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__5___lam__0(lean_object* v_gs_2755_, lean_object* v_variablesKept_2756_, lean_object* v_snd_2757_, lean_object* v_fst_2758_, lean_object* v_fst_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_, lean_object* v___y_2762_, lean_object* v___y_2763_){
_start:
{
lean_object* v_lctx_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; 
v_lctx_2765_ = lean_ctor_get(v___y_2760_, 2);
v___x_2766_ = l_Lean_LocalContext_getFVarIds(v_lctx_2765_);
v___x_2767_ = lean_array_to_list(v___x_2766_);
v___x_2768_ = l_List_lengthTR___redArg(v_gs_2755_);
v___x_2769_ = ((lean_object*)(l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__5___lam__0___closed__0));
lean_inc(v___x_2767_);
v___x_2770_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), v___x_2767_, v___x_2767_, v___x_2768_, v___x_2769_);
lean_dec(v___x_2767_);
v___x_2771_ = lean_box(0);
v___x_2772_ = l_List_mapTR_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__0(v___x_2770_, v___x_2771_);
v___x_2773_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_listBoolMerge___redArg(v_variablesKept_2756_, v_snd_2757_);
v___x_2774_ = l_List_appendTR___redArg(v___x_2772_, v___x_2773_);
v___x_2775_ = l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__1(v___x_2774_, v___x_2771_, v___y_2760_, v___y_2761_, v___y_2762_, v___y_2763_);
if (lean_obj_tag(v___x_2775_) == 0)
{
lean_object* v_a_2776_; lean_object* v___x_2777_; 
v_a_2776_ = lean_ctor_get(v___x_2775_, 0);
lean_inc(v_a_2776_);
lean_dec_ref_known(v___x_2775_, 1);
v___x_2777_ = l_Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__2(v_fst_2758_, v___y_2760_, v___y_2761_, v___y_2762_, v___y_2763_);
if (lean_obj_tag(v___x_2777_) == 0)
{
lean_object* v_a_2778_; lean_object* v___x_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; 
v_a_2778_ = lean_ctor_get(v___x_2777_, 0);
lean_inc(v_a_2778_);
lean_dec_ref_known(v___x_2777_, 1);
v___x_2779_ = lean_array_mk(v_a_2776_);
v___x_2780_ = l_Lean_mkAppN(v_a_2778_, v___x_2779_);
lean_dec_ref(v___x_2779_);
lean_inc(v___y_2763_);
lean_inc_ref(v___y_2762_);
lean_inc(v___y_2761_);
lean_inc_ref(v___y_2760_);
lean_inc_ref(v___x_2780_);
v___x_2781_ = lean_infer_type(v___x_2780_, v___y_2760_, v___y_2761_, v___y_2762_, v___y_2763_);
if (lean_obj_tag(v___x_2781_) == 0)
{
lean_object* v_a_2782_; lean_object* v___x_2783_; 
v_a_2782_ = lean_ctor_get(v___x_2781_, 0);
lean_inc(v_a_2782_);
lean_dec_ref_known(v___x_2781_, 1);
lean_inc(v_fst_2759_);
v___x_2783_ = l_Lean_MVarId_getType(v_fst_2759_, v___y_2760_, v___y_2761_, v___y_2762_, v___y_2763_);
if (lean_obj_tag(v___x_2783_) == 0)
{
lean_object* v_a_2784_; lean_object* v___x_2785_; 
v_a_2784_ = lean_ctor_get(v___x_2783_, 0);
lean_inc(v_a_2784_);
lean_dec_ref_known(v___x_2783_, 1);
v___x_2785_ = l_Lean_Meta_isExprDefEq(v_a_2782_, v_a_2784_, v___y_2760_, v___y_2761_, v___y_2762_, v___y_2763_);
lean_dec(v___y_2763_);
lean_dec_ref(v___y_2762_);
lean_dec_ref(v___y_2760_);
if (lean_obj_tag(v___x_2785_) == 0)
{
lean_object* v___x_2786_; 
lean_dec_ref_known(v___x_2785_, 1);
v___x_2786_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1___redArg(v_fst_2759_, v___x_2780_, v___y_2761_);
lean_dec(v___y_2761_);
return v___x_2786_;
}
else
{
lean_object* v_a_2787_; lean_object* v___x_2789_; uint8_t v_isShared_2790_; uint8_t v_isSharedCheck_2794_; 
lean_dec_ref(v___x_2780_);
lean_dec(v___y_2761_);
lean_dec(v_fst_2759_);
v_a_2787_ = lean_ctor_get(v___x_2785_, 0);
v_isSharedCheck_2794_ = !lean_is_exclusive(v___x_2785_);
if (v_isSharedCheck_2794_ == 0)
{
v___x_2789_ = v___x_2785_;
v_isShared_2790_ = v_isSharedCheck_2794_;
goto v_resetjp_2788_;
}
else
{
lean_inc(v_a_2787_);
lean_dec(v___x_2785_);
v___x_2789_ = lean_box(0);
v_isShared_2790_ = v_isSharedCheck_2794_;
goto v_resetjp_2788_;
}
v_resetjp_2788_:
{
lean_object* v___x_2792_; 
if (v_isShared_2790_ == 0)
{
v___x_2792_ = v___x_2789_;
goto v_reusejp_2791_;
}
else
{
lean_object* v_reuseFailAlloc_2793_; 
v_reuseFailAlloc_2793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2793_, 0, v_a_2787_);
v___x_2792_ = v_reuseFailAlloc_2793_;
goto v_reusejp_2791_;
}
v_reusejp_2791_:
{
return v___x_2792_;
}
}
}
}
else
{
lean_object* v_a_2795_; lean_object* v___x_2797_; uint8_t v_isShared_2798_; uint8_t v_isSharedCheck_2802_; 
lean_dec(v_a_2782_);
lean_dec_ref(v___x_2780_);
lean_dec(v___y_2763_);
lean_dec_ref(v___y_2762_);
lean_dec(v___y_2761_);
lean_dec_ref(v___y_2760_);
lean_dec(v_fst_2759_);
v_a_2795_ = lean_ctor_get(v___x_2783_, 0);
v_isSharedCheck_2802_ = !lean_is_exclusive(v___x_2783_);
if (v_isSharedCheck_2802_ == 0)
{
v___x_2797_ = v___x_2783_;
v_isShared_2798_ = v_isSharedCheck_2802_;
goto v_resetjp_2796_;
}
else
{
lean_inc(v_a_2795_);
lean_dec(v___x_2783_);
v___x_2797_ = lean_box(0);
v_isShared_2798_ = v_isSharedCheck_2802_;
goto v_resetjp_2796_;
}
v_resetjp_2796_:
{
lean_object* v___x_2800_; 
if (v_isShared_2798_ == 0)
{
v___x_2800_ = v___x_2797_;
goto v_reusejp_2799_;
}
else
{
lean_object* v_reuseFailAlloc_2801_; 
v_reuseFailAlloc_2801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2801_, 0, v_a_2795_);
v___x_2800_ = v_reuseFailAlloc_2801_;
goto v_reusejp_2799_;
}
v_reusejp_2799_:
{
return v___x_2800_;
}
}
}
}
else
{
lean_object* v_a_2803_; lean_object* v___x_2805_; uint8_t v_isShared_2806_; uint8_t v_isSharedCheck_2810_; 
lean_dec_ref(v___x_2780_);
lean_dec(v___y_2763_);
lean_dec_ref(v___y_2762_);
lean_dec(v___y_2761_);
lean_dec_ref(v___y_2760_);
lean_dec(v_fst_2759_);
v_a_2803_ = lean_ctor_get(v___x_2781_, 0);
v_isSharedCheck_2810_ = !lean_is_exclusive(v___x_2781_);
if (v_isSharedCheck_2810_ == 0)
{
v___x_2805_ = v___x_2781_;
v_isShared_2806_ = v_isSharedCheck_2810_;
goto v_resetjp_2804_;
}
else
{
lean_inc(v_a_2803_);
lean_dec(v___x_2781_);
v___x_2805_ = lean_box(0);
v_isShared_2806_ = v_isSharedCheck_2810_;
goto v_resetjp_2804_;
}
v_resetjp_2804_:
{
lean_object* v___x_2808_; 
if (v_isShared_2806_ == 0)
{
v___x_2808_ = v___x_2805_;
goto v_reusejp_2807_;
}
else
{
lean_object* v_reuseFailAlloc_2809_; 
v_reuseFailAlloc_2809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2809_, 0, v_a_2803_);
v___x_2808_ = v_reuseFailAlloc_2809_;
goto v_reusejp_2807_;
}
v_reusejp_2807_:
{
return v___x_2808_;
}
}
}
}
else
{
lean_object* v_a_2811_; lean_object* v___x_2813_; uint8_t v_isShared_2814_; uint8_t v_isSharedCheck_2818_; 
lean_dec(v_a_2776_);
lean_dec(v___y_2763_);
lean_dec_ref(v___y_2762_);
lean_dec(v___y_2761_);
lean_dec_ref(v___y_2760_);
lean_dec(v_fst_2759_);
v_a_2811_ = lean_ctor_get(v___x_2777_, 0);
v_isSharedCheck_2818_ = !lean_is_exclusive(v___x_2777_);
if (v_isSharedCheck_2818_ == 0)
{
v___x_2813_ = v___x_2777_;
v_isShared_2814_ = v_isSharedCheck_2818_;
goto v_resetjp_2812_;
}
else
{
lean_inc(v_a_2811_);
lean_dec(v___x_2777_);
v___x_2813_ = lean_box(0);
v_isShared_2814_ = v_isSharedCheck_2818_;
goto v_resetjp_2812_;
}
v_resetjp_2812_:
{
lean_object* v___x_2816_; 
if (v_isShared_2814_ == 0)
{
v___x_2816_ = v___x_2813_;
goto v_reusejp_2815_;
}
else
{
lean_object* v_reuseFailAlloc_2817_; 
v_reuseFailAlloc_2817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2817_, 0, v_a_2811_);
v___x_2816_ = v_reuseFailAlloc_2817_;
goto v_reusejp_2815_;
}
v_reusejp_2815_:
{
return v___x_2816_;
}
}
}
}
else
{
lean_object* v_a_2819_; lean_object* v___x_2821_; uint8_t v_isShared_2822_; uint8_t v_isSharedCheck_2826_; 
lean_dec(v___y_2763_);
lean_dec_ref(v___y_2762_);
lean_dec(v___y_2761_);
lean_dec_ref(v___y_2760_);
lean_dec(v_fst_2759_);
lean_dec(v_fst_2758_);
v_a_2819_ = lean_ctor_get(v___x_2775_, 0);
v_isSharedCheck_2826_ = !lean_is_exclusive(v___x_2775_);
if (v_isSharedCheck_2826_ == 0)
{
v___x_2821_ = v___x_2775_;
v_isShared_2822_ = v_isSharedCheck_2826_;
goto v_resetjp_2820_;
}
else
{
lean_inc(v_a_2819_);
lean_dec(v___x_2775_);
v___x_2821_ = lean_box(0);
v_isShared_2822_ = v_isSharedCheck_2826_;
goto v_resetjp_2820_;
}
v_resetjp_2820_:
{
lean_object* v___x_2824_; 
if (v_isShared_2822_ == 0)
{
v___x_2824_ = v___x_2821_;
goto v_reusejp_2823_;
}
else
{
lean_object* v_reuseFailAlloc_2825_; 
v_reuseFailAlloc_2825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2825_, 0, v_a_2819_);
v___x_2824_ = v_reuseFailAlloc_2825_;
goto v_reusejp_2823_;
}
v_reusejp_2823_:
{
return v___x_2824_;
}
}
}
}
}
LEAN_EXPORT void l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__5___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_gs_2755_ = stack[0].m_obj;
lean_object* v_variablesKept_2756_ = stack[1].m_obj;
lean_object* v_snd_2757_ = stack[2].m_obj;
lean_object* v_fst_2758_ = stack[3].m_obj;
lean_object* v_fst_2759_ = stack[4].m_obj;
lean_object* v___y_2760_ = stack[5].m_obj;
lean_object* v___y_2761_ = stack[6].m_obj;
lean_object* v___y_2762_ = stack[7].m_obj;
lean_object* v___y_2763_ = stack[8].m_obj;
lean_object* v_res_2827_;
v_res_2827_ = l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__5___lam__0(v_gs_2755_, v_variablesKept_2756_, v_snd_2757_, v_fst_2758_, v_fst_2759_, v___y_2760_, v___y_2761_, v___y_2762_, v___y_2763_);
stack->m_obj
 = v_res_2827_;
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__5___lam__0___boxed(lean_object* v_gs_2828_, lean_object* v_variablesKept_2829_, lean_object* v_snd_2830_, lean_object* v_fst_2831_, lean_object* v_fst_2832_, lean_object* v___y_2833_, lean_object* v___y_2834_, lean_object* v___y_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_){
_start:
{
lean_object* v_res_2838_; 
v_res_2838_ = l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__5___lam__0(v_gs_2828_, v_variablesKept_2829_, v_snd_2830_, v_fst_2831_, v_fst_2832_, v___y_2833_, v___y_2834_, v___y_2835_, v___y_2836_);
lean_dec(v_gs_2828_);
return v_res_2838_;
}
}
static lean_object* _init_l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__4___closed__1(void){
_start:
{
lean_object* v___x_2840_; lean_object* v___x_2841_; 
v___x_2840_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__4___closed__0));
v___x_2841_ = l_Lean_stringToMessageData(v___x_2840_);
return v___x_2841_;
}
}
lean_object* l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__4(lean_object* v_x_2842_, lean_object* v_x_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_, lean_object* v___y_2846_, lean_object* v___y_2847_){
_start:
{
if (lean_obj_tag(v_x_2843_) == 0)
{
lean_object* v___x_2849_; 
v___x_2849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2849_, 0, v_x_2842_);
return v___x_2849_;
}
else
{
lean_object* v_tail_2850_; uint8_t v___x_2851_; lean_object* v___x_2852_; 
v_tail_2850_ = lean_ctor_get(v_x_2843_, 1);
v___x_2851_ = 0;
v___x_2852_ = l_Lean_Meta_intro1Core(v_x_2842_, v___x_2851_, v___y_2844_, v___y_2845_, v___y_2846_, v___y_2847_);
if (lean_obj_tag(v___x_2852_) == 0)
{
lean_object* v_a_2853_; lean_object* v_fst_2854_; lean_object* v_snd_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; 
v_a_2853_ = lean_ctor_get(v___x_2852_, 0);
lean_inc(v_a_2853_);
lean_dec_ref_known(v___x_2852_, 1);
v_fst_2854_ = lean_ctor_get(v_a_2853_, 0);
lean_inc(v_fst_2854_);
v_snd_2855_ = lean_ctor_get(v_a_2853_, 1);
lean_inc(v_snd_2855_);
lean_dec(v_a_2853_);
v___x_2856_ = lean_unsigned_to_nat(0u);
v___x_2857_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toCases___closed__0));
v___x_2858_ = lean_box(0);
v___x_2859_ = l_Lean_MVarId_cases(v_snd_2855_, v_fst_2854_, v___x_2857_, v___x_2851_, v___x_2858_, v___y_2844_, v___y_2845_, v___y_2846_, v___y_2847_);
if (lean_obj_tag(v___x_2859_) == 0)
{
lean_object* v_a_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; uint8_t v___x_2863_; 
v_a_2860_ = lean_ctor_get(v___x_2859_, 0);
lean_inc(v_a_2860_);
lean_dec_ref_known(v___x_2859_, 1);
v___x_2861_ = lean_array_get_size(v_a_2860_);
v___x_2862_ = lean_unsigned_to_nat(1u);
v___x_2863_ = lean_nat_dec_eq(v___x_2861_, v___x_2862_);
if (v___x_2863_ == 0)
{
lean_object* v___x_2864_; lean_object* v___x_2865_; 
lean_dec(v_a_2860_);
v___x_2864_ = lean_obj_once(&l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__4___closed__1, &l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__4___closed__1_once, _init_l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__4___closed__1);
v___x_2865_ = l_Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0___redArg(v___x_2864_, v___y_2844_, v___y_2845_, v___y_2846_, v___y_2847_);
return v___x_2865_;
}
else
{
lean_object* v___x_2866_; lean_object* v_toInductionSubgoal_2867_; lean_object* v_mvarId_2868_; 
v___x_2866_ = lean_array_fget(v_a_2860_, v___x_2856_);
lean_dec(v_a_2860_);
v_toInductionSubgoal_2867_ = lean_ctor_get(v___x_2866_, 0);
lean_inc_ref(v_toInductionSubgoal_2867_);
lean_dec(v___x_2866_);
v_mvarId_2868_ = lean_ctor_get(v_toInductionSubgoal_2867_, 0);
lean_inc(v_mvarId_2868_);
lean_dec_ref(v_toInductionSubgoal_2867_);
v_x_2842_ = v_mvarId_2868_;
v_x_2843_ = v_tail_2850_;
goto _start;
}
}
else
{
lean_object* v_a_2870_; lean_object* v___x_2872_; uint8_t v_isShared_2873_; uint8_t v_isSharedCheck_2877_; 
v_a_2870_ = lean_ctor_get(v___x_2859_, 0);
v_isSharedCheck_2877_ = !lean_is_exclusive(v___x_2859_);
if (v_isSharedCheck_2877_ == 0)
{
v___x_2872_ = v___x_2859_;
v_isShared_2873_ = v_isSharedCheck_2877_;
goto v_resetjp_2871_;
}
else
{
lean_inc(v_a_2870_);
lean_dec(v___x_2859_);
v___x_2872_ = lean_box(0);
v_isShared_2873_ = v_isSharedCheck_2877_;
goto v_resetjp_2871_;
}
v_resetjp_2871_:
{
lean_object* v___x_2875_; 
if (v_isShared_2873_ == 0)
{
v___x_2875_ = v___x_2872_;
goto v_reusejp_2874_;
}
else
{
lean_object* v_reuseFailAlloc_2876_; 
v_reuseFailAlloc_2876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2876_, 0, v_a_2870_);
v___x_2875_ = v_reuseFailAlloc_2876_;
goto v_reusejp_2874_;
}
v_reusejp_2874_:
{
return v___x_2875_;
}
}
}
}
else
{
lean_object* v_a_2878_; lean_object* v___x_2880_; uint8_t v_isShared_2881_; uint8_t v_isSharedCheck_2885_; 
v_a_2878_ = lean_ctor_get(v___x_2852_, 0);
v_isSharedCheck_2885_ = !lean_is_exclusive(v___x_2852_);
if (v_isSharedCheck_2885_ == 0)
{
v___x_2880_ = v___x_2852_;
v_isShared_2881_ = v_isSharedCheck_2885_;
goto v_resetjp_2879_;
}
else
{
lean_inc(v_a_2878_);
lean_dec(v___x_2852_);
v___x_2880_ = lean_box(0);
v_isShared_2881_ = v_isSharedCheck_2885_;
goto v_resetjp_2879_;
}
v_resetjp_2879_:
{
lean_object* v___x_2883_; 
if (v_isShared_2881_ == 0)
{
v___x_2883_ = v___x_2880_;
goto v_reusejp_2882_;
}
else
{
lean_object* v_reuseFailAlloc_2884_; 
v_reuseFailAlloc_2884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2884_, 0, v_a_2878_);
v___x_2883_ = v_reuseFailAlloc_2884_;
goto v_reusejp_2882_;
}
v_reusejp_2882_:
{
return v___x_2883_;
}
}
}
}
}
}
LEAN_EXPORT void l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2842_ = stack[0].m_obj;
lean_object* v_x_2843_ = stack[1].m_obj;
lean_object* v___y_2844_ = stack[2].m_obj;
lean_object* v___y_2845_ = stack[3].m_obj;
lean_object* v___y_2846_ = stack[4].m_obj;
lean_object* v___y_2847_ = stack[5].m_obj;
lean_object* v_res_2886_;
v_res_2886_ = l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__4(v_x_2842_, v_x_2843_, v___y_2844_, v___y_2845_, v___y_2846_, v___y_2847_);
stack->m_obj
 = v_res_2886_;
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__4___boxed(lean_object* v_x_2887_, lean_object* v_x_2888_, lean_object* v___y_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_, lean_object* v___y_2892_, lean_object* v___y_2893_){
_start:
{
lean_object* v_res_2894_; 
v_res_2894_ = l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__4(v_x_2887_, v_x_2888_, v___y_2889_, v___y_2890_, v___y_2891_, v___y_2892_);
lean_dec(v___y_2892_);
lean_dec_ref(v___y_2891_);
lean_dec(v___y_2890_);
lean_dec_ref(v___y_2889_);
lean_dec(v_x_2888_);
return v_res_2894_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__3(lean_object* v_a_2895_, lean_object* v_a_2896_){
_start:
{
if (lean_obj_tag(v_a_2895_) == 0)
{
lean_object* v___x_2897_; 
v___x_2897_ = l_List_reverse___redArg(v_a_2896_);
return v___x_2897_;
}
else
{
lean_object* v_head_2898_; uint8_t v___x_2899_; 
v_head_2898_ = lean_ctor_get(v_a_2895_, 0);
v___x_2899_ = lean_unbox(v_head_2898_);
if (v___x_2899_ == 0)
{
lean_object* v_tail_2900_; 
v_tail_2900_ = lean_ctor_get(v_a_2895_, 1);
lean_inc(v_tail_2900_);
lean_dec_ref_known(v_a_2895_, 2);
v_a_2895_ = v_tail_2900_;
goto _start;
}
else
{
lean_object* v_tail_2902_; lean_object* v___x_2904_; uint8_t v_isShared_2905_; uint8_t v_isSharedCheck_2910_; 
lean_inc(v_head_2898_);
v_tail_2902_ = lean_ctor_get(v_a_2895_, 1);
v_isSharedCheck_2910_ = !lean_is_exclusive(v_a_2895_);
if (v_isSharedCheck_2910_ == 0)
{
lean_object* v_unused_2911_; 
v_unused_2911_ = lean_ctor_get(v_a_2895_, 0);
lean_dec(v_unused_2911_);
v___x_2904_ = v_a_2895_;
v_isShared_2905_ = v_isSharedCheck_2910_;
goto v_resetjp_2903_;
}
else
{
lean_inc(v_tail_2902_);
lean_dec(v_a_2895_);
v___x_2904_ = lean_box(0);
v_isShared_2905_ = v_isSharedCheck_2910_;
goto v_resetjp_2903_;
}
v_resetjp_2903_:
{
lean_object* v___x_2907_; 
if (v_isShared_2905_ == 0)
{
lean_ctor_set(v___x_2904_, 1, v_a_2896_);
v___x_2907_ = v___x_2904_;
goto v_reusejp_2906_;
}
else
{
lean_object* v_reuseFailAlloc_2909_; 
v_reuseFailAlloc_2909_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2909_, 0, v_head_2898_);
lean_ctor_set(v_reuseFailAlloc_2909_, 1, v_a_2896_);
v___x_2907_ = v_reuseFailAlloc_2909_;
goto v_reusejp_2906_;
}
v_reusejp_2906_:
{
v_a_2895_ = v_tail_2902_;
v_a_2896_ = v___x_2907_;
goto _start;
}
}
}
}
}
}
lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__5(lean_object* v_gs_2912_, lean_object* v_x_2913_, lean_object* v_x_2914_, lean_object* v___y_2915_, lean_object* v___y_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_){
_start:
{
if (lean_obj_tag(v_x_2913_) == 0)
{
lean_object* v___x_2920_; lean_object* v___x_2921_; 
lean_dec(v_gs_2912_);
v___x_2920_ = l_List_reverse___redArg(v_x_2914_);
v___x_2921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2921_, 0, v___x_2920_);
return v___x_2921_;
}
else
{
lean_object* v_head_2922_; lean_object* v_snd_2923_; lean_object* v_fst_2924_; lean_object* v_snd_2925_; lean_object* v_tail_2926_; lean_object* v___x_2928_; uint8_t v_isShared_2929_; uint8_t v_isSharedCheck_3050_; 
v_head_2922_ = lean_ctor_get(v_x_2913_, 0);
lean_inc(v_head_2922_);
v_snd_2923_ = lean_ctor_get(v_head_2922_, 1);
v_fst_2924_ = lean_ctor_get(v_snd_2923_, 0);
lean_inc(v_fst_2924_);
v_snd_2925_ = lean_ctor_get(v_snd_2923_, 1);
lean_inc(v_snd_2925_);
v_tail_2926_ = lean_ctor_get(v_x_2913_, 1);
v_isSharedCheck_3050_ = !lean_is_exclusive(v_x_2913_);
if (v_isSharedCheck_3050_ == 0)
{
lean_object* v_unused_3051_; 
v_unused_3051_ = lean_ctor_get(v_x_2913_, 0);
lean_dec(v_unused_3051_);
v___x_2928_ = v_x_2913_;
v_isShared_2929_ = v_isSharedCheck_3050_;
goto v_resetjp_2927_;
}
else
{
lean_inc(v_tail_2926_);
lean_dec(v_x_2913_);
v___x_2928_ = lean_box(0);
v_isShared_2929_ = v_isSharedCheck_3050_;
goto v_resetjp_2927_;
}
v_resetjp_2927_:
{
lean_object* v_fst_2930_; lean_object* v_fst_2931_; lean_object* v_snd_2932_; lean_object* v_variablesKept_2933_; lean_object* v_neqs_2934_; lean_object* v_fst_2936_; lean_object* v_snd_2937_; lean_object* v___y_2938_; lean_object* v___y_2939_; lean_object* v___y_2940_; lean_object* v___y_2941_; lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; 
v_fst_2930_ = lean_ctor_get(v_head_2922_, 0);
lean_inc(v_fst_2930_);
lean_dec(v_head_2922_);
v_fst_2931_ = lean_ctor_get(v_fst_2924_, 0);
lean_inc(v_fst_2931_);
v_snd_2932_ = lean_ctor_get(v_fst_2924_, 1);
lean_inc(v_snd_2932_);
lean_dec(v_fst_2924_);
v_variablesKept_2933_ = lean_ctor_get(v_snd_2925_, 0);
lean_inc_n(v_variablesKept_2933_, 2);
v_neqs_2934_ = lean_ctor_get(v_snd_2925_, 1);
lean_inc(v_neqs_2934_);
lean_dec(v_snd_2925_);
v___x_2957_ = lean_box(0);
v___x_2958_ = l_List_filterTR_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__3(v_variablesKept_2933_, v___x_2957_);
v___x_2959_ = l_List_lengthTR___redArg(v___x_2958_);
lean_dec(v___x_2958_);
if (lean_obj_tag(v_neqs_2934_) == 0)
{
lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; 
v___x_2960_ = lean_unsigned_to_nat(1u);
v___x_2961_ = lean_nat_sub(v___x_2959_, v___x_2960_);
lean_dec(v___x_2959_);
v___x_2962_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesProd(v___x_2961_, v_snd_2932_, v_fst_2931_, v___y_2915_, v___y_2916_, v___y_2917_, v___y_2918_);
lean_dec(v___x_2961_);
if (lean_obj_tag(v___x_2962_) == 0)
{
lean_object* v_a_2963_; lean_object* v_fst_2964_; lean_object* v_snd_2965_; 
v_a_2963_ = lean_ctor_get(v___x_2962_, 0);
lean_inc(v_a_2963_);
lean_dec_ref_known(v___x_2962_, 1);
v_fst_2964_ = lean_ctor_get(v_a_2963_, 0);
lean_inc(v_fst_2964_);
v_snd_2965_ = lean_ctor_get(v_a_2963_, 1);
lean_inc(v_snd_2965_);
lean_dec(v_a_2963_);
v_fst_2936_ = v_fst_2964_;
v_snd_2937_ = v_snd_2965_;
v___y_2938_ = v___y_2915_;
v___y_2939_ = v___y_2916_;
v___y_2940_ = v___y_2917_;
v___y_2941_ = v___y_2918_;
goto v___jp_2935_;
}
else
{
lean_object* v_a_2966_; lean_object* v___x_2968_; uint8_t v_isShared_2969_; uint8_t v_isSharedCheck_2973_; 
lean_dec(v_variablesKept_2933_);
lean_dec(v_fst_2930_);
lean_del_object(v___x_2928_);
lean_dec(v_tail_2926_);
lean_dec(v_x_2914_);
lean_dec(v_gs_2912_);
v_a_2966_ = lean_ctor_get(v___x_2962_, 0);
v_isSharedCheck_2973_ = !lean_is_exclusive(v___x_2962_);
if (v_isSharedCheck_2973_ == 0)
{
v___x_2968_ = v___x_2962_;
v_isShared_2969_ = v_isSharedCheck_2973_;
goto v_resetjp_2967_;
}
else
{
lean_inc(v_a_2966_);
lean_dec(v___x_2962_);
v___x_2968_ = lean_box(0);
v_isShared_2969_ = v_isSharedCheck_2973_;
goto v_resetjp_2967_;
}
v_resetjp_2967_:
{
lean_object* v___x_2971_; 
if (v_isShared_2969_ == 0)
{
v___x_2971_ = v___x_2968_;
goto v_reusejp_2970_;
}
else
{
lean_object* v_reuseFailAlloc_2972_; 
v_reuseFailAlloc_2972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2972_, 0, v_a_2966_);
v___x_2971_ = v_reuseFailAlloc_2972_;
goto v_reusejp_2970_;
}
v_reusejp_2970_:
{
return v___x_2971_;
}
}
}
}
else
{
lean_object* v_val_2974_; lean_object* v___x_2975_; lean_object* v_zero_2976_; uint8_t v_isZero_2977_; 
v_val_2974_ = lean_ctor_get(v_neqs_2934_, 0);
lean_inc(v_val_2974_);
lean_dec_ref_known(v_neqs_2934_, 1);
v___x_2975_ = lean_box(0);
v_zero_2976_ = lean_unsigned_to_nat(0u);
v_isZero_2977_ = lean_nat_dec_eq(v_val_2974_, v_zero_2976_);
if (v_isZero_2977_ == 1)
{
lean_object* v___x_2978_; 
lean_dec(v_val_2974_);
v___x_2978_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesProd(v___x_2959_, v_snd_2932_, v_fst_2931_, v___y_2915_, v___y_2916_, v___y_2917_, v___y_2918_);
lean_dec(v___x_2959_);
if (lean_obj_tag(v___x_2978_) == 0)
{
lean_object* v_a_2979_; lean_object* v_fst_2980_; lean_object* v_snd_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; 
v_a_2979_ = lean_ctor_get(v___x_2978_, 0);
lean_inc(v_a_2979_);
lean_dec_ref_known(v___x_2978_, 1);
v_fst_2980_ = lean_ctor_get(v_a_2979_, 0);
lean_inc(v_fst_2980_);
v_snd_2981_ = lean_ctor_get(v_a_2979_, 1);
lean_inc(v_snd_2981_);
lean_dec(v_a_2979_);
v___x_2982_ = l_List_getLast_x21___redArg(v___x_2975_, v_snd_2981_);
v___x_2983_ = l_Lean_MVarId_tryClear(v_fst_2980_, v___x_2982_, v___y_2915_, v___y_2916_, v___y_2917_, v___y_2918_);
if (lean_obj_tag(v___x_2983_) == 0)
{
lean_object* v_a_2984_; 
v_a_2984_ = lean_ctor_get(v___x_2983_, 0);
lean_inc(v_a_2984_);
lean_dec_ref_known(v___x_2983_, 1);
v_fst_2936_ = v_a_2984_;
v_snd_2937_ = v_snd_2981_;
v___y_2938_ = v___y_2915_;
v___y_2939_ = v___y_2916_;
v___y_2940_ = v___y_2917_;
v___y_2941_ = v___y_2918_;
goto v___jp_2935_;
}
else
{
lean_object* v_a_2985_; lean_object* v___x_2987_; uint8_t v_isShared_2988_; uint8_t v_isSharedCheck_2992_; 
lean_dec(v_snd_2981_);
lean_dec(v_variablesKept_2933_);
lean_dec(v_fst_2930_);
lean_del_object(v___x_2928_);
lean_dec(v_tail_2926_);
lean_dec(v_x_2914_);
lean_dec(v_gs_2912_);
v_a_2985_ = lean_ctor_get(v___x_2983_, 0);
v_isSharedCheck_2992_ = !lean_is_exclusive(v___x_2983_);
if (v_isSharedCheck_2992_ == 0)
{
v___x_2987_ = v___x_2983_;
v_isShared_2988_ = v_isSharedCheck_2992_;
goto v_resetjp_2986_;
}
else
{
lean_inc(v_a_2985_);
lean_dec(v___x_2983_);
v___x_2987_ = lean_box(0);
v_isShared_2988_ = v_isSharedCheck_2992_;
goto v_resetjp_2986_;
}
v_resetjp_2986_:
{
lean_object* v___x_2990_; 
if (v_isShared_2988_ == 0)
{
v___x_2990_ = v___x_2987_;
goto v_reusejp_2989_;
}
else
{
lean_object* v_reuseFailAlloc_2991_; 
v_reuseFailAlloc_2991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2991_, 0, v_a_2985_);
v___x_2990_ = v_reuseFailAlloc_2991_;
goto v_reusejp_2989_;
}
v_reusejp_2989_:
{
return v___x_2990_;
}
}
}
}
else
{
lean_object* v_a_2993_; lean_object* v___x_2995_; uint8_t v_isShared_2996_; uint8_t v_isSharedCheck_3000_; 
lean_dec(v_variablesKept_2933_);
lean_dec(v_fst_2930_);
lean_del_object(v___x_2928_);
lean_dec(v_tail_2926_);
lean_dec(v_x_2914_);
lean_dec(v_gs_2912_);
v_a_2993_ = lean_ctor_get(v___x_2978_, 0);
v_isSharedCheck_3000_ = !lean_is_exclusive(v___x_2978_);
if (v_isSharedCheck_3000_ == 0)
{
v___x_2995_ = v___x_2978_;
v_isShared_2996_ = v_isSharedCheck_3000_;
goto v_resetjp_2994_;
}
else
{
lean_inc(v_a_2993_);
lean_dec(v___x_2978_);
v___x_2995_ = lean_box(0);
v_isShared_2996_ = v_isSharedCheck_3000_;
goto v_resetjp_2994_;
}
v_resetjp_2994_:
{
lean_object* v___x_2998_; 
if (v_isShared_2996_ == 0)
{
v___x_2998_ = v___x_2995_;
goto v_reusejp_2997_;
}
else
{
lean_object* v_reuseFailAlloc_2999_; 
v_reuseFailAlloc_2999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2999_, 0, v_a_2993_);
v___x_2998_ = v_reuseFailAlloc_2999_;
goto v_reusejp_2997_;
}
v_reusejp_2997_:
{
return v___x_2998_;
}
}
}
}
else
{
lean_object* v_one_3001_; lean_object* v_n_3002_; lean_object* v___x_3003_; 
v_one_3001_ = lean_unsigned_to_nat(1u);
v_n_3002_ = lean_nat_sub(v_val_2974_, v_one_3001_);
lean_dec(v_val_2974_);
v___x_3003_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesProd(v___x_2959_, v_snd_2932_, v_fst_2931_, v___y_2915_, v___y_2916_, v___y_2917_, v___y_2918_);
lean_dec(v___x_2959_);
if (lean_obj_tag(v___x_3003_) == 0)
{
lean_object* v_a_3004_; lean_object* v_fst_3005_; lean_object* v_snd_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; 
v_a_3004_ = lean_ctor_get(v___x_3003_, 0);
lean_inc(v_a_3004_);
lean_dec_ref_known(v___x_3003_, 1);
v_fst_3005_ = lean_ctor_get(v_a_3004_, 0);
lean_inc(v_fst_3005_);
v_snd_3006_ = lean_ctor_get(v_a_3004_, 1);
lean_inc(v_snd_3006_);
lean_dec(v_a_3004_);
v___x_3007_ = l_List_getLast_x21___redArg(v___x_2975_, v_snd_3006_);
v___x_3008_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesProd(v_n_3002_, v_fst_3005_, v___x_3007_, v___y_2915_, v___y_2916_, v___y_2917_, v___y_2918_);
lean_dec(v_n_3002_);
if (lean_obj_tag(v___x_3008_) == 0)
{
lean_object* v_a_3009_; lean_object* v_fst_3010_; lean_object* v_snd_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; 
v_a_3009_ = lean_ctor_get(v___x_3008_, 0);
lean_inc(v_a_3009_);
lean_dec_ref_known(v___x_3008_, 1);
v_fst_3010_ = lean_ctor_get(v_a_3009_, 0);
lean_inc(v_fst_3010_);
v_snd_3011_ = lean_ctor_get(v_a_3009_, 1);
lean_inc_n(v_snd_3011_, 2);
lean_dec(v_a_3009_);
v___x_3012_ = lean_array_mk(v_snd_3011_);
v___x_3013_ = l_Lean_MVarId_revert(v_fst_3010_, v___x_3012_, v_isZero_2977_, v_isZero_2977_, v___y_2915_, v___y_2916_, v___y_2917_, v___y_2918_);
if (lean_obj_tag(v___x_3013_) == 0)
{
lean_object* v_a_3014_; lean_object* v_snd_3015_; lean_object* v___x_3016_; 
v_a_3014_ = lean_ctor_get(v___x_3013_, 0);
lean_inc(v_a_3014_);
lean_dec_ref_known(v___x_3013_, 1);
v_snd_3015_ = lean_ctor_get(v_a_3014_, 1);
lean_inc(v_snd_3015_);
lean_dec(v_a_3014_);
v___x_3016_ = l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__4(v_snd_3015_, v_snd_3011_, v___y_2915_, v___y_2916_, v___y_2917_, v___y_2918_);
lean_dec(v_snd_3011_);
if (lean_obj_tag(v___x_3016_) == 0)
{
lean_object* v_a_3017_; 
v_a_3017_ = lean_ctor_get(v___x_3016_, 0);
lean_inc(v_a_3017_);
lean_dec_ref_known(v___x_3016_, 1);
v_fst_2936_ = v_a_3017_;
v_snd_2937_ = v_snd_3006_;
v___y_2938_ = v___y_2915_;
v___y_2939_ = v___y_2916_;
v___y_2940_ = v___y_2917_;
v___y_2941_ = v___y_2918_;
goto v___jp_2935_;
}
else
{
lean_object* v_a_3018_; lean_object* v___x_3020_; uint8_t v_isShared_3021_; uint8_t v_isSharedCheck_3025_; 
lean_dec(v_snd_3006_);
lean_dec(v_variablesKept_2933_);
lean_dec(v_fst_2930_);
lean_del_object(v___x_2928_);
lean_dec(v_tail_2926_);
lean_dec(v_x_2914_);
lean_dec(v_gs_2912_);
v_a_3018_ = lean_ctor_get(v___x_3016_, 0);
v_isSharedCheck_3025_ = !lean_is_exclusive(v___x_3016_);
if (v_isSharedCheck_3025_ == 0)
{
v___x_3020_ = v___x_3016_;
v_isShared_3021_ = v_isSharedCheck_3025_;
goto v_resetjp_3019_;
}
else
{
lean_inc(v_a_3018_);
lean_dec(v___x_3016_);
v___x_3020_ = lean_box(0);
v_isShared_3021_ = v_isSharedCheck_3025_;
goto v_resetjp_3019_;
}
v_resetjp_3019_:
{
lean_object* v___x_3023_; 
if (v_isShared_3021_ == 0)
{
v___x_3023_ = v___x_3020_;
goto v_reusejp_3022_;
}
else
{
lean_object* v_reuseFailAlloc_3024_; 
v_reuseFailAlloc_3024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3024_, 0, v_a_3018_);
v___x_3023_ = v_reuseFailAlloc_3024_;
goto v_reusejp_3022_;
}
v_reusejp_3022_:
{
return v___x_3023_;
}
}
}
}
else
{
lean_object* v_a_3026_; lean_object* v___x_3028_; uint8_t v_isShared_3029_; uint8_t v_isSharedCheck_3033_; 
lean_dec(v_snd_3011_);
lean_dec(v_snd_3006_);
lean_dec(v_variablesKept_2933_);
lean_dec(v_fst_2930_);
lean_del_object(v___x_2928_);
lean_dec(v_tail_2926_);
lean_dec(v_x_2914_);
lean_dec(v_gs_2912_);
v_a_3026_ = lean_ctor_get(v___x_3013_, 0);
v_isSharedCheck_3033_ = !lean_is_exclusive(v___x_3013_);
if (v_isSharedCheck_3033_ == 0)
{
v___x_3028_ = v___x_3013_;
v_isShared_3029_ = v_isSharedCheck_3033_;
goto v_resetjp_3027_;
}
else
{
lean_inc(v_a_3026_);
lean_dec(v___x_3013_);
v___x_3028_ = lean_box(0);
v_isShared_3029_ = v_isSharedCheck_3033_;
goto v_resetjp_3027_;
}
v_resetjp_3027_:
{
lean_object* v___x_3031_; 
if (v_isShared_3029_ == 0)
{
v___x_3031_ = v___x_3028_;
goto v_reusejp_3030_;
}
else
{
lean_object* v_reuseFailAlloc_3032_; 
v_reuseFailAlloc_3032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3032_, 0, v_a_3026_);
v___x_3031_ = v_reuseFailAlloc_3032_;
goto v_reusejp_3030_;
}
v_reusejp_3030_:
{
return v___x_3031_;
}
}
}
}
else
{
lean_object* v_a_3034_; lean_object* v___x_3036_; uint8_t v_isShared_3037_; uint8_t v_isSharedCheck_3041_; 
lean_dec(v_snd_3006_);
lean_dec(v_variablesKept_2933_);
lean_dec(v_fst_2930_);
lean_del_object(v___x_2928_);
lean_dec(v_tail_2926_);
lean_dec(v_x_2914_);
lean_dec(v_gs_2912_);
v_a_3034_ = lean_ctor_get(v___x_3008_, 0);
v_isSharedCheck_3041_ = !lean_is_exclusive(v___x_3008_);
if (v_isSharedCheck_3041_ == 0)
{
v___x_3036_ = v___x_3008_;
v_isShared_3037_ = v_isSharedCheck_3041_;
goto v_resetjp_3035_;
}
else
{
lean_inc(v_a_3034_);
lean_dec(v___x_3008_);
v___x_3036_ = lean_box(0);
v_isShared_3037_ = v_isSharedCheck_3041_;
goto v_resetjp_3035_;
}
v_resetjp_3035_:
{
lean_object* v___x_3039_; 
if (v_isShared_3037_ == 0)
{
v___x_3039_ = v___x_3036_;
goto v_reusejp_3038_;
}
else
{
lean_object* v_reuseFailAlloc_3040_; 
v_reuseFailAlloc_3040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3040_, 0, v_a_3034_);
v___x_3039_ = v_reuseFailAlloc_3040_;
goto v_reusejp_3038_;
}
v_reusejp_3038_:
{
return v___x_3039_;
}
}
}
}
else
{
lean_object* v_a_3042_; lean_object* v___x_3044_; uint8_t v_isShared_3045_; uint8_t v_isSharedCheck_3049_; 
lean_dec(v_n_3002_);
lean_dec(v_variablesKept_2933_);
lean_dec(v_fst_2930_);
lean_del_object(v___x_2928_);
lean_dec(v_tail_2926_);
lean_dec(v_x_2914_);
lean_dec(v_gs_2912_);
v_a_3042_ = lean_ctor_get(v___x_3003_, 0);
v_isSharedCheck_3049_ = !lean_is_exclusive(v___x_3003_);
if (v_isSharedCheck_3049_ == 0)
{
v___x_3044_ = v___x_3003_;
v_isShared_3045_ = v_isSharedCheck_3049_;
goto v_resetjp_3043_;
}
else
{
lean_inc(v_a_3042_);
lean_dec(v___x_3003_);
v___x_3044_ = lean_box(0);
v_isShared_3045_ = v_isSharedCheck_3049_;
goto v_resetjp_3043_;
}
v_resetjp_3043_:
{
lean_object* v___x_3047_; 
if (v_isShared_3045_ == 0)
{
v___x_3047_ = v___x_3044_;
goto v_reusejp_3046_;
}
else
{
lean_object* v_reuseFailAlloc_3048_; 
v_reuseFailAlloc_3048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3048_, 0, v_a_3042_);
v___x_3047_ = v_reuseFailAlloc_3048_;
goto v_reusejp_3046_;
}
v_reusejp_3046_:
{
return v___x_3047_;
}
}
}
}
}
v___jp_2935_:
{
lean_object* v___f_2942_; lean_object* v___x_2943_; 
lean_inc(v_fst_2936_);
lean_inc(v_gs_2912_);
v___f_2942_ = lean_alloc_closure((void*)(l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__5___lam__0___boxed), 10, 5);
lean_closure_set(v___f_2942_, 0, v_gs_2912_);
lean_closure_set(v___f_2942_, 1, v_variablesKept_2933_);
lean_closure_set(v___f_2942_, 2, v_snd_2937_);
lean_closure_set(v___f_2942_, 3, v_fst_2930_);
lean_closure_set(v___f_2942_, 4, v_fst_2936_);
v___x_2943_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor_spec__0___redArg(v_fst_2936_, v___f_2942_, v___y_2938_, v___y_2939_, v___y_2940_, v___y_2941_);
if (lean_obj_tag(v___x_2943_) == 0)
{
lean_object* v_a_2944_; lean_object* v___x_2946_; 
v_a_2944_ = lean_ctor_get(v___x_2943_, 0);
lean_inc(v_a_2944_);
lean_dec_ref_known(v___x_2943_, 1);
if (v_isShared_2929_ == 0)
{
lean_ctor_set(v___x_2928_, 1, v_x_2914_);
lean_ctor_set(v___x_2928_, 0, v_a_2944_);
v___x_2946_ = v___x_2928_;
goto v_reusejp_2945_;
}
else
{
lean_object* v_reuseFailAlloc_2948_; 
v_reuseFailAlloc_2948_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2948_, 0, v_a_2944_);
lean_ctor_set(v_reuseFailAlloc_2948_, 1, v_x_2914_);
v___x_2946_ = v_reuseFailAlloc_2948_;
goto v_reusejp_2945_;
}
v_reusejp_2945_:
{
v_x_2913_ = v_tail_2926_;
v_x_2914_ = v___x_2946_;
goto _start;
}
}
else
{
lean_object* v_a_2949_; lean_object* v___x_2951_; uint8_t v_isShared_2952_; uint8_t v_isSharedCheck_2956_; 
lean_del_object(v___x_2928_);
lean_dec(v_tail_2926_);
lean_dec(v_x_2914_);
lean_dec(v_gs_2912_);
v_a_2949_ = lean_ctor_get(v___x_2943_, 0);
v_isSharedCheck_2956_ = !lean_is_exclusive(v___x_2943_);
if (v_isSharedCheck_2956_ == 0)
{
v___x_2951_ = v___x_2943_;
v_isShared_2952_ = v_isSharedCheck_2956_;
goto v_resetjp_2950_;
}
else
{
lean_inc(v_a_2949_);
lean_dec(v___x_2943_);
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
}
}
}
LEAN_EXPORT void l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_gs_2912_ = stack[0].m_obj;
lean_object* v_x_2913_ = stack[1].m_obj;
lean_object* v_x_2914_ = stack[2].m_obj;
lean_object* v___y_2915_ = stack[3].m_obj;
lean_object* v___y_2916_ = stack[4].m_obj;
lean_object* v___y_2917_ = stack[5].m_obj;
lean_object* v___y_2918_ = stack[6].m_obj;
lean_object* v_res_3052_;
v_res_3052_ = l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__5(v_gs_2912_, v_x_2913_, v_x_2914_, v___y_2915_, v___y_2916_, v___y_2917_, v___y_2918_);
stack->m_obj
 = v_res_3052_;
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__5___boxed(lean_object* v_gs_3053_, lean_object* v_x_3054_, lean_object* v_x_3055_, lean_object* v___y_3056_, lean_object* v___y_3057_, lean_object* v___y_3058_, lean_object* v___y_3059_, lean_object* v___y_3060_){
_start:
{
lean_object* v_res_3061_; 
v_res_3061_ = l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__5(v_gs_3053_, v_x_3054_, v_x_3055_, v___y_3056_, v___y_3057_, v___y_3058_, v___y_3059_);
lean_dec(v___y_3059_);
lean_dec_ref(v___y_3058_);
lean_dec(v___y_3057_);
lean_dec_ref(v___y_3056_);
return v_res_3061_;
}
}
lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive(lean_object* v_mvar_3062_, lean_object* v_cs_3063_, lean_object* v_gs_3064_, lean_object* v_s_3065_, lean_object* v_h_3066_, lean_object* v_a_3067_, lean_object* v_a_3068_, lean_object* v_a_3069_, lean_object* v_a_3070_){
_start:
{
lean_object* v___x_3072_; lean_object* v_zero_3073_; uint8_t v_isZero_3074_; 
v___x_3072_ = l_List_lengthTR___redArg(v_s_3065_);
v_zero_3073_ = lean_unsigned_to_nat(0u);
v_isZero_3074_ = lean_nat_dec_eq(v___x_3072_, v_zero_3073_);
if (v_isZero_3074_ == 1)
{
lean_object* v___x_3075_; uint8_t v___x_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; 
lean_dec(v___x_3072_);
lean_dec(v_s_3065_);
lean_dec(v_gs_3064_);
lean_dec(v_cs_3063_);
v___x_3075_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toCases___closed__0));
v___x_3076_ = 0;
v___x_3077_ = lean_box(0);
v___x_3078_ = l_Lean_MVarId_cases(v_mvar_3062_, v_h_3066_, v___x_3075_, v___x_3076_, v___x_3077_, v_a_3067_, v_a_3068_, v_a_3069_, v_a_3070_);
if (lean_obj_tag(v___x_3078_) == 0)
{
lean_object* v___x_3080_; uint8_t v_isShared_3081_; uint8_t v_isSharedCheck_3086_; 
v_isSharedCheck_3086_ = !lean_is_exclusive(v___x_3078_);
if (v_isSharedCheck_3086_ == 0)
{
lean_object* v_unused_3087_; 
v_unused_3087_ = lean_ctor_get(v___x_3078_, 0);
lean_dec(v_unused_3087_);
v___x_3080_ = v___x_3078_;
v_isShared_3081_ = v_isSharedCheck_3086_;
goto v_resetjp_3079_;
}
else
{
lean_dec(v___x_3078_);
v___x_3080_ = lean_box(0);
v_isShared_3081_ = v_isSharedCheck_3086_;
goto v_resetjp_3079_;
}
v_resetjp_3079_:
{
lean_object* v___x_3082_; lean_object* v___x_3084_; 
v___x_3082_ = lean_box(0);
if (v_isShared_3081_ == 0)
{
lean_ctor_set(v___x_3080_, 0, v___x_3082_);
v___x_3084_ = v___x_3080_;
goto v_reusejp_3083_;
}
else
{
lean_object* v_reuseFailAlloc_3085_; 
v_reuseFailAlloc_3085_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3085_, 0, v___x_3082_);
v___x_3084_ = v_reuseFailAlloc_3085_;
goto v_reusejp_3083_;
}
v_reusejp_3083_:
{
return v___x_3084_;
}
}
}
else
{
lean_object* v_a_3088_; lean_object* v___x_3090_; uint8_t v_isShared_3091_; uint8_t v_isSharedCheck_3095_; 
v_a_3088_ = lean_ctor_get(v___x_3078_, 0);
v_isSharedCheck_3095_ = !lean_is_exclusive(v___x_3078_);
if (v_isSharedCheck_3095_ == 0)
{
v___x_3090_ = v___x_3078_;
v_isShared_3091_ = v_isSharedCheck_3095_;
goto v_resetjp_3089_;
}
else
{
lean_inc(v_a_3088_);
lean_dec(v___x_3078_);
v___x_3090_ = lean_box(0);
v_isShared_3091_ = v_isSharedCheck_3095_;
goto v_resetjp_3089_;
}
v_resetjp_3089_:
{
lean_object* v___x_3093_; 
if (v_isShared_3091_ == 0)
{
v___x_3093_ = v___x_3090_;
goto v_reusejp_3092_;
}
else
{
lean_object* v_reuseFailAlloc_3094_; 
v_reuseFailAlloc_3094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3094_, 0, v_a_3088_);
v___x_3093_ = v_reuseFailAlloc_3094_;
goto v_reusejp_3092_;
}
v_reusejp_3092_:
{
return v___x_3093_;
}
}
}
}
else
{
lean_object* v_one_3096_; lean_object* v_n_3097_; lean_object* v___x_3098_; 
v_one_3096_ = lean_unsigned_to_nat(1u);
v_n_3097_ = lean_nat_sub(v___x_3072_, v_one_3096_);
lean_dec(v___x_3072_);
v___x_3098_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesSum(v_n_3097_, v_mvar_3062_, v_h_3066_, v_a_3067_, v_a_3068_, v_a_3069_, v_a_3070_);
lean_dec(v_n_3097_);
if (lean_obj_tag(v___x_3098_) == 0)
{
lean_object* v_a_3099_; lean_object* v___x_3100_; lean_object* v___x_3101_; lean_object* v___x_3102_; lean_object* v___x_3103_; 
v_a_3099_ = lean_ctor_get(v___x_3098_, 0);
lean_inc(v_a_3099_);
lean_dec_ref_known(v___x_3098_, 1);
v___x_3100_ = l_List_zipWith___at___00List_zip_spec__0(lean_box(0), lean_box(0), v_a_3099_, v_s_3065_);
v___x_3101_ = l_List_zipWith___at___00List_zip_spec__0(lean_box(0), lean_box(0), v_cs_3063_, v___x_3100_);
v___x_3102_ = lean_box(0);
v___x_3103_ = l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__5(v_gs_3064_, v___x_3101_, v___x_3102_, v_a_3067_, v_a_3068_, v_a_3069_, v_a_3070_);
if (lean_obj_tag(v___x_3103_) == 0)
{
lean_object* v___x_3105_; uint8_t v_isShared_3106_; uint8_t v_isSharedCheck_3111_; 
v_isSharedCheck_3111_ = !lean_is_exclusive(v___x_3103_);
if (v_isSharedCheck_3111_ == 0)
{
lean_object* v_unused_3112_; 
v_unused_3112_ = lean_ctor_get(v___x_3103_, 0);
lean_dec(v_unused_3112_);
v___x_3105_ = v___x_3103_;
v_isShared_3106_ = v_isSharedCheck_3111_;
goto v_resetjp_3104_;
}
else
{
lean_dec(v___x_3103_);
v___x_3105_ = lean_box(0);
v_isShared_3106_ = v_isSharedCheck_3111_;
goto v_resetjp_3104_;
}
v_resetjp_3104_:
{
lean_object* v___x_3107_; lean_object* v___x_3109_; 
v___x_3107_ = lean_box(0);
if (v_isShared_3106_ == 0)
{
lean_ctor_set(v___x_3105_, 0, v___x_3107_);
v___x_3109_ = v___x_3105_;
goto v_reusejp_3108_;
}
else
{
lean_object* v_reuseFailAlloc_3110_; 
v_reuseFailAlloc_3110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3110_, 0, v___x_3107_);
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
lean_object* v_a_3113_; lean_object* v___x_3115_; uint8_t v_isShared_3116_; uint8_t v_isSharedCheck_3120_; 
v_a_3113_ = lean_ctor_get(v___x_3103_, 0);
v_isSharedCheck_3120_ = !lean_is_exclusive(v___x_3103_);
if (v_isSharedCheck_3120_ == 0)
{
v___x_3115_ = v___x_3103_;
v_isShared_3116_ = v_isSharedCheck_3120_;
goto v_resetjp_3114_;
}
else
{
lean_inc(v_a_3113_);
lean_dec(v___x_3103_);
v___x_3115_ = lean_box(0);
v_isShared_3116_ = v_isSharedCheck_3120_;
goto v_resetjp_3114_;
}
v_resetjp_3114_:
{
lean_object* v___x_3118_; 
if (v_isShared_3116_ == 0)
{
v___x_3118_ = v___x_3115_;
goto v_reusejp_3117_;
}
else
{
lean_object* v_reuseFailAlloc_3119_; 
v_reuseFailAlloc_3119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3119_, 0, v_a_3113_);
v___x_3118_ = v_reuseFailAlloc_3119_;
goto v_reusejp_3117_;
}
v_reusejp_3117_:
{
return v___x_3118_;
}
}
}
}
else
{
lean_object* v_a_3121_; lean_object* v___x_3123_; uint8_t v_isShared_3124_; uint8_t v_isSharedCheck_3128_; 
lean_dec(v_s_3065_);
lean_dec(v_gs_3064_);
lean_dec(v_cs_3063_);
v_a_3121_ = lean_ctor_get(v___x_3098_, 0);
v_isSharedCheck_3128_ = !lean_is_exclusive(v___x_3098_);
if (v_isSharedCheck_3128_ == 0)
{
v___x_3123_ = v___x_3098_;
v_isShared_3124_ = v_isSharedCheck_3128_;
goto v_resetjp_3122_;
}
else
{
lean_inc(v_a_3121_);
lean_dec(v___x_3098_);
v___x_3123_ = lean_box(0);
v_isShared_3124_ = v_isSharedCheck_3128_;
goto v_resetjp_3122_;
}
v_resetjp_3122_:
{
lean_object* v___x_3126_; 
if (v_isShared_3124_ == 0)
{
v___x_3126_ = v___x_3123_;
goto v_reusejp_3125_;
}
else
{
lean_object* v_reuseFailAlloc_3127_; 
v_reuseFailAlloc_3127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3127_, 0, v_a_3121_);
v___x_3126_ = v_reuseFailAlloc_3127_;
goto v_reusejp_3125_;
}
v_reusejp_3125_:
{
return v___x_3126_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvar_3062_ = stack[0].m_obj;
lean_object* v_cs_3063_ = stack[1].m_obj;
lean_object* v_gs_3064_ = stack[2].m_obj;
lean_object* v_s_3065_ = stack[3].m_obj;
lean_object* v_h_3066_ = stack[4].m_obj;
lean_object* v_a_3067_ = stack[5].m_obj;
lean_object* v_a_3068_ = stack[6].m_obj;
lean_object* v_a_3069_ = stack[7].m_obj;
lean_object* v_a_3070_ = stack[8].m_obj;
lean_object* v_res_3129_;
v_res_3129_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive(v_mvar_3062_, v_cs_3063_, v_gs_3064_, v_s_3065_, v_h_3066_, v_a_3067_, v_a_3068_, v_a_3069_, v_a_3070_);
stack->m_obj
 = v_res_3129_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive___boxed(lean_object* v_mvar_3130_, lean_object* v_cs_3131_, lean_object* v_gs_3132_, lean_object* v_s_3133_, lean_object* v_h_3134_, lean_object* v_a_3135_, lean_object* v_a_3136_, lean_object* v_a_3137_, lean_object* v_a_3138_, lean_object* v_a_3139_){
_start:
{
lean_object* v_res_3140_; 
v_res_3140_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive(v_mvar_3130_, v_cs_3131_, v_gs_3132_, v_s_3133_, v_h_3134_, v_a_3135_, v_a_3136_, v_a_3137_, v_a_3138_);
lean_dec(v_a_3138_);
lean_dec_ref(v_a_3137_);
lean_dec(v_a_3136_);
lean_dec_ref(v_a_3135_);
return v_res_3140_;
}
}
lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__1___redArg(lean_object* v_type_3141_, lean_object* v_k_3142_, uint8_t v_cleanupAnnotations_3143_, uint8_t v_whnfType_3144_, lean_object* v___y_3145_, lean_object* v___y_3146_, lean_object* v___y_3147_, lean_object* v___y_3148_){
_start:
{
lean_object* v___f_3150_; lean_object* v___x_3151_; 
v___f_3150_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__4___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_3150_, 0, v_k_3142_);
v___x_3151_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_3141_, v___f_3150_, v_cleanupAnnotations_3143_, v_whnfType_3144_, v___y_3145_, v___y_3146_, v___y_3147_, v___y_3148_);
if (lean_obj_tag(v___x_3151_) == 0)
{
lean_object* v_a_3152_; lean_object* v___x_3154_; uint8_t v_isShared_3155_; uint8_t v_isSharedCheck_3159_; 
v_a_3152_ = lean_ctor_get(v___x_3151_, 0);
v_isSharedCheck_3159_ = !lean_is_exclusive(v___x_3151_);
if (v_isSharedCheck_3159_ == 0)
{
v___x_3154_ = v___x_3151_;
v_isShared_3155_ = v_isSharedCheck_3159_;
goto v_resetjp_3153_;
}
else
{
lean_inc(v_a_3152_);
lean_dec(v___x_3151_);
v___x_3154_ = lean_box(0);
v_isShared_3155_ = v_isSharedCheck_3159_;
goto v_resetjp_3153_;
}
v_resetjp_3153_:
{
lean_object* v___x_3157_; 
if (v_isShared_3155_ == 0)
{
v___x_3157_ = v___x_3154_;
goto v_reusejp_3156_;
}
else
{
lean_object* v_reuseFailAlloc_3158_; 
v_reuseFailAlloc_3158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3158_, 0, v_a_3152_);
v___x_3157_ = v_reuseFailAlloc_3158_;
goto v_reusejp_3156_;
}
v_reusejp_3156_:
{
return v___x_3157_;
}
}
}
else
{
lean_object* v_a_3160_; lean_object* v___x_3162_; uint8_t v_isShared_3163_; uint8_t v_isSharedCheck_3167_; 
v_a_3160_ = lean_ctor_get(v___x_3151_, 0);
v_isSharedCheck_3167_ = !lean_is_exclusive(v___x_3151_);
if (v_isSharedCheck_3167_ == 0)
{
v___x_3162_ = v___x_3151_;
v_isShared_3163_ = v_isSharedCheck_3167_;
goto v_resetjp_3161_;
}
else
{
lean_inc(v_a_3160_);
lean_dec(v___x_3151_);
v___x_3162_ = lean_box(0);
v_isShared_3163_ = v_isSharedCheck_3167_;
goto v_resetjp_3161_;
}
v_resetjp_3161_:
{
lean_object* v___x_3165_; 
if (v_isShared_3163_ == 0)
{
v___x_3165_ = v___x_3162_;
goto v_reusejp_3164_;
}
else
{
lean_object* v_reuseFailAlloc_3166_; 
v_reuseFailAlloc_3166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3166_, 0, v_a_3160_);
v___x_3165_ = v_reuseFailAlloc_3166_;
goto v_reusejp_3164_;
}
v_reusejp_3164_:
{
return v___x_3165_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_3141_ = stack[0].m_obj;
lean_object* v_k_3142_ = stack[1].m_obj;
uint8_t v_cleanupAnnotations_3143_ = stack[2].m_num;
uint8_t v_whnfType_3144_ = stack[3].m_num;
lean_object* v___y_3145_ = stack[4].m_obj;
lean_object* v___y_3146_ = stack[5].m_obj;
lean_object* v___y_3147_ = stack[6].m_obj;
lean_object* v___y_3148_ = stack[7].m_obj;
lean_object* v_res_3168_;
v_res_3168_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__1___redArg(v_type_3141_, v_k_3142_, v_cleanupAnnotations_3143_, v_whnfType_3144_, v___y_3145_, v___y_3146_, v___y_3147_, v___y_3148_);
stack->m_obj
 = v_res_3168_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__1___redArg___boxed(lean_object* v_type_3169_, lean_object* v_k_3170_, lean_object* v_cleanupAnnotations_3171_, lean_object* v_whnfType_3172_, lean_object* v___y_3173_, lean_object* v___y_3174_, lean_object* v___y_3175_, lean_object* v___y_3176_, lean_object* v___y_3177_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3178_; uint8_t v_whnfType_boxed_3179_; lean_object* v_res_3180_; 
v_cleanupAnnotations_boxed_3178_ = lean_unbox(v_cleanupAnnotations_3171_);
v_whnfType_boxed_3179_ = lean_unbox(v_whnfType_3172_);
v_res_3180_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__1___redArg(v_type_3169_, v_k_3170_, v_cleanupAnnotations_boxed_3178_, v_whnfType_boxed_3179_, v___y_3173_, v___y_3174_, v___y_3175_, v___y_3176_);
lean_dec(v___y_3176_);
lean_dec_ref(v___y_3175_);
lean_dec(v___y_3174_);
lean_dec_ref(v___y_3173_);
return v_res_3180_;
}
}
lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__1(lean_object* v_00_u03b1_3181_, lean_object* v_type_3182_, lean_object* v_k_3183_, uint8_t v_cleanupAnnotations_3184_, uint8_t v_whnfType_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_, lean_object* v___y_3188_, lean_object* v___y_3189_){
_start:
{
lean_object* v___x_3191_; 
v___x_3191_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__1___redArg(v_type_3182_, v_k_3183_, v_cleanupAnnotations_3184_, v_whnfType_3185_, v___y_3186_, v___y_3187_, v___y_3188_, v___y_3189_);
return v___x_3191_;
}
}
LEAN_EXPORT void l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_3182_ = stack[1].m_obj;
lean_object* v_k_3183_ = stack[2].m_obj;
uint8_t v_cleanupAnnotations_3184_ = stack[3].m_num;
uint8_t v_whnfType_3185_ = stack[4].m_num;
lean_object* v___y_3186_ = stack[5].m_obj;
lean_object* v___y_3187_ = stack[6].m_obj;
lean_object* v___y_3188_ = stack[7].m_obj;
lean_object* v___y_3189_ = stack[8].m_obj;
lean_object* v_res_3192_;
v_res_3192_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__1(lean_box(0), v_type_3182_, v_k_3183_, v_cleanupAnnotations_3184_, v_whnfType_3185_, v___y_3186_, v___y_3187_, v___y_3188_, v___y_3189_);
stack->m_obj
 = v_res_3192_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__1___boxed(lean_object* v_00_u03b1_3193_, lean_object* v_type_3194_, lean_object* v_k_3195_, lean_object* v_cleanupAnnotations_3196_, lean_object* v_whnfType_3197_, lean_object* v___y_3198_, lean_object* v___y_3199_, lean_object* v___y_3200_, lean_object* v___y_3201_, lean_object* v___y_3202_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3203_; uint8_t v_whnfType_boxed_3204_; lean_object* v_res_3205_; 
v_cleanupAnnotations_boxed_3203_ = lean_unbox(v_cleanupAnnotations_3196_);
v_whnfType_boxed_3204_ = lean_unbox(v_whnfType_3197_);
v_res_3205_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__1(v_00_u03b1_3193_, v_type_3194_, v_k_3195_, v_cleanupAnnotations_boxed_3203_, v_whnfType_boxed_3204_, v___y_3198_, v___y_3199_, v___y_3200_, v___y_3201_);
lean_dec(v___y_3201_);
lean_dec_ref(v___y_3200_);
lean_dec(v___y_3199_);
lean_dec_ref(v___y_3198_);
return v_res_3205_;
}
}
lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__3___redArg(lean_object* v_e_3206_, lean_object* v___y_3207_){
_start:
{
uint8_t v___x_3209_; 
v___x_3209_ = l_Lean_Expr_hasMVar(v_e_3206_);
if (v___x_3209_ == 0)
{
lean_object* v___x_3210_; 
v___x_3210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3210_, 0, v_e_3206_);
return v___x_3210_;
}
else
{
lean_object* v___x_3211_; lean_object* v_mctx_3212_; lean_object* v___x_3213_; lean_object* v_fst_3214_; lean_object* v_snd_3215_; lean_object* v___x_3216_; lean_object* v_cache_3217_; lean_object* v_zetaDeltaFVarIds_3218_; lean_object* v_postponed_3219_; lean_object* v_diag_3220_; lean_object* v___x_3222_; uint8_t v_isShared_3223_; uint8_t v_isSharedCheck_3229_; 
v___x_3211_ = lean_st_ref_get(v___y_3207_);
v_mctx_3212_ = lean_ctor_get(v___x_3211_, 0);
lean_inc_ref(v_mctx_3212_);
lean_dec(v___x_3211_);
v___x_3213_ = l_Lean_instantiateMVarsCore(v_mctx_3212_, v_e_3206_);
v_fst_3214_ = lean_ctor_get(v___x_3213_, 0);
lean_inc(v_fst_3214_);
v_snd_3215_ = lean_ctor_get(v___x_3213_, 1);
lean_inc(v_snd_3215_);
lean_dec_ref(v___x_3213_);
v___x_3216_ = lean_st_ref_take(v___y_3207_);
v_cache_3217_ = lean_ctor_get(v___x_3216_, 1);
v_zetaDeltaFVarIds_3218_ = lean_ctor_get(v___x_3216_, 2);
v_postponed_3219_ = lean_ctor_get(v___x_3216_, 3);
v_diag_3220_ = lean_ctor_get(v___x_3216_, 4);
v_isSharedCheck_3229_ = !lean_is_exclusive(v___x_3216_);
if (v_isSharedCheck_3229_ == 0)
{
lean_object* v_unused_3230_; 
v_unused_3230_ = lean_ctor_get(v___x_3216_, 0);
lean_dec(v_unused_3230_);
v___x_3222_ = v___x_3216_;
v_isShared_3223_ = v_isSharedCheck_3229_;
goto v_resetjp_3221_;
}
else
{
lean_inc(v_diag_3220_);
lean_inc(v_postponed_3219_);
lean_inc(v_zetaDeltaFVarIds_3218_);
lean_inc(v_cache_3217_);
lean_dec(v___x_3216_);
v___x_3222_ = lean_box(0);
v_isShared_3223_ = v_isSharedCheck_3229_;
goto v_resetjp_3221_;
}
v_resetjp_3221_:
{
lean_object* v___x_3225_; 
if (v_isShared_3223_ == 0)
{
lean_ctor_set(v___x_3222_, 0, v_snd_3215_);
v___x_3225_ = v___x_3222_;
goto v_reusejp_3224_;
}
else
{
lean_object* v_reuseFailAlloc_3228_; 
v_reuseFailAlloc_3228_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3228_, 0, v_snd_3215_);
lean_ctor_set(v_reuseFailAlloc_3228_, 1, v_cache_3217_);
lean_ctor_set(v_reuseFailAlloc_3228_, 2, v_zetaDeltaFVarIds_3218_);
lean_ctor_set(v_reuseFailAlloc_3228_, 3, v_postponed_3219_);
lean_ctor_set(v_reuseFailAlloc_3228_, 4, v_diag_3220_);
v___x_3225_ = v_reuseFailAlloc_3228_;
goto v_reusejp_3224_;
}
v_reusejp_3224_:
{
lean_object* v___x_3226_; lean_object* v___x_3227_; 
v___x_3226_ = lean_st_ref_put(v___y_3207_, v___x_3225_);
v___x_3227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3227_, 0, v_fst_3214_);
return v___x_3227_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_3206_ = stack[0].m_obj;
lean_object* v___y_3207_ = stack[1].m_obj;
lean_object* v_res_3231_;
v_res_3231_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__3___redArg(v_e_3206_, v___y_3207_);
stack->m_obj
 = v_res_3231_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__3___redArg___boxed(lean_object* v_e_3232_, lean_object* v___y_3233_, lean_object* v___y_3234_){
_start:
{
lean_object* v_res_3235_; 
v_res_3235_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__3___redArg(v_e_3232_, v___y_3233_);
lean_dec(v___y_3233_);
return v_res_3235_;
}
}
lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__3(lean_object* v_e_3236_, lean_object* v___y_3237_, lean_object* v___y_3238_, lean_object* v___y_3239_, lean_object* v___y_3240_){
_start:
{
lean_object* v___x_3242_; 
v___x_3242_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__3___redArg(v_e_3236_, v___y_3238_);
return v___x_3242_;
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_3236_ = stack[0].m_obj;
lean_object* v___y_3237_ = stack[1].m_obj;
lean_object* v___y_3238_ = stack[2].m_obj;
lean_object* v___y_3239_ = stack[3].m_obj;
lean_object* v___y_3240_ = stack[4].m_obj;
lean_object* v_res_3243_;
v_res_3243_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__3(v_e_3236_, v___y_3237_, v___y_3238_, v___y_3239_, v___y_3240_);
stack->m_obj
 = v_res_3243_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__3___boxed(lean_object* v_e_3244_, lean_object* v___y_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_, lean_object* v___y_3248_, lean_object* v___y_3249_){
_start:
{
lean_object* v_res_3250_; 
v_res_3250_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__3(v_e_3244_, v___y_3245_, v___y_3246_, v___y_3247_, v___y_3248_);
lean_dec(v___y_3248_);
lean_dec_ref(v___y_3247_);
lean_dec(v___y_3246_);
lean_dec_ref(v___y_3245_);
return v_res_3250_;
}
}
lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__4___redArg(lean_object* v_thm_3251_, lean_object* v___y_3252_){
_start:
{
lean_object* v___x_3254_; lean_object* v_env_3255_; lean_object* v_toConstantVal_3256_; lean_object* v_value_3257_; lean_object* v_all_3258_; uint8_t v___y_3260_; lean_object* v_type_3268_; uint8_t v___x_3269_; 
v___x_3254_ = lean_st_ref_get(v___y_3252_);
v_env_3255_ = lean_ctor_get(v___x_3254_, 0);
lean_inc_ref_n(v_env_3255_, 2);
lean_dec(v___x_3254_);
v_toConstantVal_3256_ = lean_ctor_get(v_thm_3251_, 0);
v_value_3257_ = lean_ctor_get(v_thm_3251_, 1);
v_all_3258_ = lean_ctor_get(v_thm_3251_, 2);
v_type_3268_ = lean_ctor_get(v_toConstantVal_3256_, 2);
v___x_3269_ = l_Lean_Environment_hasUnsafe(v_env_3255_, v_type_3268_);
if (v___x_3269_ == 0)
{
uint8_t v___x_3270_; 
v___x_3270_ = l_Lean_Environment_hasUnsafe(v_env_3255_, v_value_3257_);
v___y_3260_ = v___x_3270_;
goto v___jp_3259_;
}
else
{
lean_dec_ref(v_env_3255_);
v___y_3260_ = v___x_3269_;
goto v___jp_3259_;
}
v___jp_3259_:
{
if (v___y_3260_ == 0)
{
lean_object* v___x_3261_; lean_object* v___x_3262_; 
v___x_3261_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3261_, 0, v_thm_3251_);
v___x_3262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3262_, 0, v___x_3261_);
return v___x_3262_;
}
else
{
lean_object* v___x_3263_; uint8_t v___x_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; 
lean_inc(v_all_3258_);
lean_inc_ref(v_value_3257_);
lean_inc_ref(v_toConstantVal_3256_);
lean_dec_ref(v_thm_3251_);
v___x_3263_ = lean_box(0);
v___x_3264_ = 0;
v___x_3265_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3265_, 0, v_toConstantVal_3256_);
lean_ctor_set(v___x_3265_, 1, v_value_3257_);
lean_ctor_set(v___x_3265_, 2, v___x_3263_);
lean_ctor_set(v___x_3265_, 3, v_all_3258_);
lean_ctor_set_uint8(v___x_3265_, sizeof(void*)*4, v___x_3264_);
v___x_3266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3266_, 0, v___x_3265_);
v___x_3267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3267_, 0, v___x_3266_);
return v___x_3267_;
}
}
}
}
LEAN_EXPORT void l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_thm_3251_ = stack[0].m_obj;
lean_object* v___y_3252_ = stack[1].m_obj;
lean_object* v_res_3271_;
v_res_3271_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__4___redArg(v_thm_3251_, v___y_3252_);
stack->m_obj
 = v_res_3271_;
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__4___redArg___boxed(lean_object* v_thm_3272_, lean_object* v___y_3273_, lean_object* v___y_3274_){
_start:
{
lean_object* v_res_3275_; 
v_res_3275_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__4___redArg(v_thm_3272_, v___y_3273_);
lean_dec(v___y_3273_);
return v_res_3275_;
}
}
lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__4(lean_object* v_thm_3276_, lean_object* v___y_3277_, lean_object* v___y_3278_, lean_object* v___y_3279_, lean_object* v___y_3280_){
_start:
{
lean_object* v___x_3282_; 
v___x_3282_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__4___redArg(v_thm_3276_, v___y_3280_);
return v___x_3282_;
}
}
LEAN_EXPORT void l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_thm_3276_ = stack[0].m_obj;
lean_object* v___y_3277_ = stack[1].m_obj;
lean_object* v___y_3278_ = stack[2].m_obj;
lean_object* v___y_3279_ = stack[3].m_obj;
lean_object* v___y_3280_ = stack[4].m_obj;
lean_object* v_res_3283_;
v_res_3283_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__4(v_thm_3276_, v___y_3277_, v___y_3278_, v___y_3279_, v___y_3280_);
stack->m_obj
 = v_res_3283_;
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__4___boxed(lean_object* v_thm_3284_, lean_object* v___y_3285_, lean_object* v___y_3286_, lean_object* v___y_3287_, lean_object* v___y_3288_, lean_object* v___y_3289_){
_start:
{
lean_object* v_res_3290_; 
v_res_3290_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__4(v_thm_3284_, v___y_3285_, v___y_3286_, v___y_3287_, v___y_3288_);
lean_dec(v___y_3288_);
lean_dec_ref(v___y_3287_);
lean_dec(v___y_3286_);
lean_dec_ref(v___y_3285_);
return v_res_3290_;
}
}
lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__5___redArg(lean_object* v_name_3291_, lean_object* v_levelParams_3292_, lean_object* v_type_3293_, lean_object* v_value_3294_, lean_object* v_hints_3295_, lean_object* v___y_3296_){
_start:
{
lean_object* v___x_3298_; uint8_t v___y_3300_; uint8_t v___y_3307_; lean_object* v_env_3310_; uint8_t v___x_3311_; 
v___x_3298_ = lean_st_ref_get(v___y_3296_);
v_env_3310_ = lean_ctor_get(v___x_3298_, 0);
lean_inc_ref_n(v_env_3310_, 2);
lean_dec(v___x_3298_);
v___x_3311_ = l_Lean_Environment_hasUnsafe(v_env_3310_, v_type_3293_);
if (v___x_3311_ == 0)
{
uint8_t v___x_3312_; 
v___x_3312_ = l_Lean_Environment_hasUnsafe(v_env_3310_, v_value_3294_);
v___y_3307_ = v___x_3312_;
goto v___jp_3306_;
}
else
{
lean_dec_ref(v_env_3310_);
v___y_3307_ = v___x_3311_;
goto v___jp_3306_;
}
v___jp_3299_:
{
lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; 
lean_inc(v_name_3291_);
v___x_3301_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3301_, 0, v_name_3291_);
lean_ctor_set(v___x_3301_, 1, v_levelParams_3292_);
lean_ctor_set(v___x_3301_, 2, v_type_3293_);
v___x_3302_ = lean_box(0);
v___x_3303_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3303_, 0, v_name_3291_);
lean_ctor_set(v___x_3303_, 1, v___x_3302_);
v___x_3304_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3304_, 0, v___x_3301_);
lean_ctor_set(v___x_3304_, 1, v_value_3294_);
lean_ctor_set(v___x_3304_, 2, v_hints_3295_);
lean_ctor_set(v___x_3304_, 3, v___x_3303_);
lean_ctor_set_uint8(v___x_3304_, sizeof(void*)*4, v___y_3300_);
v___x_3305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3305_, 0, v___x_3304_);
return v___x_3305_;
}
v___jp_3306_:
{
if (v___y_3307_ == 0)
{
uint8_t v___x_3308_; 
v___x_3308_ = 1;
v___y_3300_ = v___x_3308_;
goto v___jp_3299_;
}
else
{
uint8_t v___x_3309_; 
v___x_3309_ = 0;
v___y_3300_ = v___x_3309_;
goto v___jp_3299_;
}
}
}
}
LEAN_EXPORT void l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_3291_ = stack[0].m_obj;
lean_object* v_levelParams_3292_ = stack[1].m_obj;
lean_object* v_type_3293_ = stack[2].m_obj;
lean_object* v_value_3294_ = stack[3].m_obj;
lean_object* v_hints_3295_ = stack[4].m_obj;
lean_object* v___y_3296_ = stack[5].m_obj;
lean_object* v_res_3313_;
v_res_3313_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__5___redArg(v_name_3291_, v_levelParams_3292_, v_type_3293_, v_value_3294_, v_hints_3295_, v___y_3296_);
stack->m_obj
 = v_res_3313_;
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__5___redArg___boxed(lean_object* v_name_3314_, lean_object* v_levelParams_3315_, lean_object* v_type_3316_, lean_object* v_value_3317_, lean_object* v_hints_3318_, lean_object* v___y_3319_, lean_object* v___y_3320_){
_start:
{
lean_object* v_res_3321_; 
v_res_3321_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__5___redArg(v_name_3314_, v_levelParams_3315_, v_type_3316_, v_value_3317_, v_hints_3318_, v___y_3319_);
lean_dec(v___y_3319_);
return v_res_3321_;
}
}
lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__5(lean_object* v_name_3322_, lean_object* v_levelParams_3323_, lean_object* v_type_3324_, lean_object* v_value_3325_, lean_object* v_hints_3326_, lean_object* v___y_3327_, lean_object* v___y_3328_, lean_object* v___y_3329_, lean_object* v___y_3330_){
_start:
{
lean_object* v___x_3332_; 
v___x_3332_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__5___redArg(v_name_3322_, v_levelParams_3323_, v_type_3324_, v_value_3325_, v_hints_3326_, v___y_3330_);
return v___x_3332_;
}
}
LEAN_EXPORT void l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_3322_ = stack[0].m_obj;
lean_object* v_levelParams_3323_ = stack[1].m_obj;
lean_object* v_type_3324_ = stack[2].m_obj;
lean_object* v_value_3325_ = stack[3].m_obj;
lean_object* v_hints_3326_ = stack[4].m_obj;
lean_object* v___y_3327_ = stack[5].m_obj;
lean_object* v___y_3328_ = stack[6].m_obj;
lean_object* v___y_3329_ = stack[7].m_obj;
lean_object* v___y_3330_ = stack[8].m_obj;
lean_object* v_res_3333_;
v_res_3333_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__5(v_name_3322_, v_levelParams_3323_, v_type_3324_, v_value_3325_, v_hints_3326_, v___y_3327_, v___y_3328_, v___y_3329_, v___y_3330_);
stack->m_obj
 = v_res_3333_;
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__5___boxed(lean_object* v_name_3334_, lean_object* v_levelParams_3335_, lean_object* v_type_3336_, lean_object* v_value_3337_, lean_object* v_hints_3338_, lean_object* v___y_3339_, lean_object* v___y_3340_, lean_object* v___y_3341_, lean_object* v___y_3342_, lean_object* v___y_3343_){
_start:
{
lean_object* v_res_3344_; 
v_res_3344_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__5(v_name_3334_, v_levelParams_3335_, v_type_3336_, v_value_3337_, v_hints_3338_, v___y_3339_, v___y_3340_, v___y_3341_, v___y_3342_);
lean_dec(v___y_3342_);
lean_dec_ref(v___y_3341_);
lean_dec(v___y_3340_);
lean_dec_ref(v___y_3339_);
return v_res_3344_;
}
}
lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__0(lean_object* v_univs_3345_, lean_object* v___x_3346_, lean_object* v___x_3347_, lean_object* v_x_3348_, lean_object* v_x_3349_, lean_object* v___y_3350_, lean_object* v___y_3351_, lean_object* v___y_3352_, lean_object* v___y_3353_){
_start:
{
if (lean_obj_tag(v_x_3348_) == 0)
{
lean_object* v___x_3355_; lean_object* v___x_3356_; 
lean_dec(v___x_3347_);
lean_dec(v___x_3346_);
lean_dec(v_univs_3345_);
v___x_3355_ = l_List_reverse___redArg(v_x_3349_);
v___x_3356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3356_, 0, v___x_3355_);
return v___x_3356_;
}
else
{
lean_object* v_head_3357_; lean_object* v_tail_3358_; lean_object* v___x_3360_; uint8_t v_isShared_3361_; uint8_t v_isSharedCheck_3376_; 
v_head_3357_ = lean_ctor_get(v_x_3348_, 0);
v_tail_3358_ = lean_ctor_get(v_x_3348_, 1);
v_isSharedCheck_3376_ = !lean_is_exclusive(v_x_3348_);
if (v_isSharedCheck_3376_ == 0)
{
v___x_3360_ = v_x_3348_;
v_isShared_3361_ = v_isSharedCheck_3376_;
goto v_resetjp_3359_;
}
else
{
lean_inc(v_tail_3358_);
lean_inc(v_head_3357_);
lean_dec(v_x_3348_);
v___x_3360_ = lean_box(0);
v_isShared_3361_ = v_isSharedCheck_3376_;
goto v_resetjp_3359_;
}
v_resetjp_3359_:
{
lean_object* v___x_3362_; 
lean_inc(v___x_3347_);
lean_inc(v___x_3346_);
lean_inc(v_univs_3345_);
v___x_3362_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp(v_univs_3345_, v___x_3346_, v___x_3347_, v_head_3357_, v___y_3350_, v___y_3351_, v___y_3352_, v___y_3353_);
if (lean_obj_tag(v___x_3362_) == 0)
{
lean_object* v_a_3363_; lean_object* v___x_3365_; 
v_a_3363_ = lean_ctor_get(v___x_3362_, 0);
lean_inc(v_a_3363_);
lean_dec_ref_known(v___x_3362_, 1);
if (v_isShared_3361_ == 0)
{
lean_ctor_set(v___x_3360_, 1, v_x_3349_);
lean_ctor_set(v___x_3360_, 0, v_a_3363_);
v___x_3365_ = v___x_3360_;
goto v_reusejp_3364_;
}
else
{
lean_object* v_reuseFailAlloc_3367_; 
v_reuseFailAlloc_3367_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3367_, 0, v_a_3363_);
lean_ctor_set(v_reuseFailAlloc_3367_, 1, v_x_3349_);
v___x_3365_ = v_reuseFailAlloc_3367_;
goto v_reusejp_3364_;
}
v_reusejp_3364_:
{
v_x_3348_ = v_tail_3358_;
v_x_3349_ = v___x_3365_;
goto _start;
}
}
else
{
lean_object* v_a_3368_; lean_object* v___x_3370_; uint8_t v_isShared_3371_; uint8_t v_isSharedCheck_3375_; 
lean_del_object(v___x_3360_);
lean_dec(v_tail_3358_);
lean_dec(v_x_3349_);
lean_dec(v___x_3347_);
lean_dec(v___x_3346_);
lean_dec(v_univs_3345_);
v_a_3368_ = lean_ctor_get(v___x_3362_, 0);
v_isSharedCheck_3375_ = !lean_is_exclusive(v___x_3362_);
if (v_isSharedCheck_3375_ == 0)
{
v___x_3370_ = v___x_3362_;
v_isShared_3371_ = v_isSharedCheck_3375_;
goto v_resetjp_3369_;
}
else
{
lean_inc(v_a_3368_);
lean_dec(v___x_3362_);
v___x_3370_ = lean_box(0);
v_isShared_3371_ = v_isSharedCheck_3375_;
goto v_resetjp_3369_;
}
v_resetjp_3369_:
{
lean_object* v___x_3373_; 
if (v_isShared_3371_ == 0)
{
v___x_3373_ = v___x_3370_;
goto v_reusejp_3372_;
}
else
{
lean_object* v_reuseFailAlloc_3374_; 
v_reuseFailAlloc_3374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3374_, 0, v_a_3368_);
v___x_3373_ = v_reuseFailAlloc_3374_;
goto v_reusejp_3372_;
}
v_reusejp_3372_:
{
return v___x_3373_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_univs_3345_ = stack[0].m_obj;
lean_object* v___x_3346_ = stack[1].m_obj;
lean_object* v___x_3347_ = stack[2].m_obj;
lean_object* v_x_3348_ = stack[3].m_obj;
lean_object* v_x_3349_ = stack[4].m_obj;
lean_object* v___y_3350_ = stack[5].m_obj;
lean_object* v___y_3351_ = stack[6].m_obj;
lean_object* v___y_3352_ = stack[7].m_obj;
lean_object* v___y_3353_ = stack[8].m_obj;
lean_object* v_res_3377_;
v_res_3377_ = l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__0(v_univs_3345_, v___x_3346_, v___x_3347_, v_x_3348_, v_x_3349_, v___y_3350_, v___y_3351_, v___y_3352_, v___y_3353_);
stack->m_obj
 = v_res_3377_;
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__0___boxed(lean_object* v_univs_3378_, lean_object* v___x_3379_, lean_object* v___x_3380_, lean_object* v_x_3381_, lean_object* v_x_3382_, lean_object* v___y_3383_, lean_object* v___y_3384_, lean_object* v___y_3385_, lean_object* v___y_3386_, lean_object* v___y_3387_){
_start:
{
lean_object* v_res_3388_; 
v_res_3388_ = l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__0(v_univs_3378_, v___x_3379_, v___x_3380_, v_x_3381_, v_x_3382_, v___y_3383_, v___y_3384_, v___y_3385_, v___y_3386_);
lean_dec(v___y_3386_);
lean_dec_ref(v___y_3385_);
lean_dec(v___y_3384_);
lean_dec_ref(v___y_3383_);
return v_res_3388_;
}
}
static lean_object* _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___lam__0___closed__3(void){
_start:
{
lean_object* v___x_3393_; lean_object* v___x_3394_; 
v___x_3393_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___lam__0___closed__2));
v___x_3394_ = l_Lean_stringToMessageData(v___x_3393_);
return v___x_3394_;
}
}
lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___lam__0(lean_object* v_name_3395_, lean_object* v_univs_3396_, lean_object* v_numParams_3397_, lean_object* v_ctors_3398_, lean_object* v___x_3399_, lean_object* v_fvars_3400_, lean_object* v_ty_3401_, lean_object* v___y_3402_, lean_object* v___y_3403_, lean_object* v___y_3404_, lean_object* v___y_3405_){
_start:
{
uint8_t v___x_3470_; 
v___x_3470_ = l_Lean_Expr_isProp(v_ty_3401_);
if (v___x_3470_ == 0)
{
lean_object* v___x_3471_; lean_object* v___x_3472_; lean_object* v_a_3473_; lean_object* v___x_3475_; uint8_t v_isShared_3476_; uint8_t v_isSharedCheck_3480_; 
lean_dec_ref(v_fvars_3400_);
lean_dec(v___x_3399_);
lean_dec(v_ctors_3398_);
lean_dec(v_numParams_3397_);
lean_dec(v_univs_3396_);
lean_dec(v_name_3395_);
v___x_3471_ = lean_obj_once(&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___lam__0___closed__3, &l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___lam__0___closed__3_once, _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___lam__0___closed__3);
v___x_3472_ = l_Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0___redArg(v___x_3471_, v___y_3402_, v___y_3403_, v___y_3404_, v___y_3405_);
v_a_3473_ = lean_ctor_get(v___x_3472_, 0);
v_isSharedCheck_3480_ = !lean_is_exclusive(v___x_3472_);
if (v_isSharedCheck_3480_ == 0)
{
v___x_3475_ = v___x_3472_;
v_isShared_3476_ = v_isSharedCheck_3480_;
goto v_resetjp_3474_;
}
else
{
lean_inc(v_a_3473_);
lean_dec(v___x_3472_);
v___x_3475_ = lean_box(0);
v_isShared_3476_ = v_isSharedCheck_3480_;
goto v_resetjp_3474_;
}
v_resetjp_3474_:
{
lean_object* v___x_3478_; 
if (v_isShared_3476_ == 0)
{
v___x_3478_ = v___x_3475_;
goto v_reusejp_3477_;
}
else
{
lean_object* v_reuseFailAlloc_3479_; 
v_reuseFailAlloc_3479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3479_, 0, v_a_3473_);
v___x_3478_ = v_reuseFailAlloc_3479_;
goto v_reusejp_3477_;
}
v_reusejp_3477_:
{
return v___x_3478_;
}
}
}
else
{
goto v___jp_3407_;
}
v___jp_3407_:
{
lean_object* v___x_3408_; lean_object* v_lhs_3409_; lean_object* v_fvars_x27_3410_; lean_object* v___x_3411_; lean_object* v___x_3412_; lean_object* v___x_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; 
lean_inc(v_univs_3396_);
v___x_3408_ = l_Lean_mkConst(v_name_3395_, v_univs_3396_);
v_lhs_3409_ = l_Lean_mkAppN(v___x_3408_, v_fvars_3400_);
lean_inc_ref(v_fvars_3400_);
v_fvars_x27_3410_ = lean_array_to_list(v_fvars_3400_);
v___x_3411_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__1___closed__1));
lean_inc(v_numParams_3397_);
lean_inc(v_fvars_x27_3410_);
v___x_3412_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), v_fvars_x27_3410_, v_fvars_x27_3410_, v_numParams_3397_, v___x_3411_);
v___x_3413_ = l_List_drop___redArg(v_numParams_3397_, v_fvars_x27_3410_);
lean_dec(v_fvars_x27_3410_);
v___x_3414_ = lean_box(0);
v___x_3415_ = l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__0(v_univs_3396_, v___x_3412_, v___x_3413_, v_ctors_3398_, v___x_3414_, v___y_3402_, v___y_3403_, v___y_3404_, v___y_3405_);
if (lean_obj_tag(v___x_3415_) == 0)
{
lean_object* v_a_3416_; lean_object* v___x_3417_; lean_object* v_fst_3418_; lean_object* v_snd_3419_; lean_object* v___x_3421_; uint8_t v_isShared_3422_; uint8_t v_isSharedCheck_3461_; 
v_a_3416_ = lean_ctor_get(v___x_3415_, 0);
lean_inc(v_a_3416_);
lean_dec_ref_known(v___x_3415_, 1);
v___x_3417_ = l_List_unzipTR___redArg(v_a_3416_);
v_fst_3418_ = lean_ctor_get(v___x_3417_, 0);
v_snd_3419_ = lean_ctor_get(v___x_3417_, 1);
v_isSharedCheck_3461_ = !lean_is_exclusive(v___x_3417_);
if (v_isSharedCheck_3461_ == 0)
{
v___x_3421_ = v___x_3417_;
v_isShared_3422_ = v_isSharedCheck_3461_;
goto v_resetjp_3420_;
}
else
{
lean_inc(v_snd_3419_);
lean_inc(v_fst_3418_);
lean_dec(v___x_3417_);
v___x_3421_ = lean_box(0);
v_isShared_3422_ = v_isSharedCheck_3461_;
goto v_resetjp_3420_;
}
v_resetjp_3420_:
{
lean_object* v___x_3423_; uint8_t v___x_3424_; uint8_t v___x_3425_; uint8_t v___x_3426_; lean_object* v___x_3427_; 
v___x_3423_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkOrList(v_snd_3419_);
v___x_3424_ = 0;
v___x_3425_ = 1;
v___x_3426_ = 1;
lean_inc_ref(v___x_3423_);
v___x_3427_ = l_Lean_Meta_mkLambdaFVars(v_fvars_3400_, v___x_3423_, v___x_3424_, v___x_3425_, v___x_3424_, v___x_3425_, v___x_3426_, v___y_3402_, v___y_3403_, v___y_3404_, v___y_3405_);
if (lean_obj_tag(v___x_3427_) == 0)
{
lean_object* v_a_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; 
v_a_3428_ = lean_ctor_get(v___x_3427_, 0);
lean_inc(v_a_3428_);
lean_dec_ref_known(v___x_3427_, 1);
v___x_3429_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___lam__0___closed__1));
v___x_3430_ = l_Lean_mkConst(v___x_3429_, v___x_3399_);
v___x_3431_ = l_Lean_mkAppB(v___x_3430_, v_lhs_3409_, v___x_3423_);
v___x_3432_ = l_Lean_Meta_mkForallFVars(v_fvars_3400_, v___x_3431_, v___x_3424_, v___x_3425_, v___x_3425_, v___x_3426_, v___y_3402_, v___y_3403_, v___y_3404_, v___y_3405_);
lean_dec_ref(v_fvars_3400_);
if (lean_obj_tag(v___x_3432_) == 0)
{
lean_object* v_a_3433_; lean_object* v___x_3435_; uint8_t v_isShared_3436_; uint8_t v_isSharedCheck_3444_; 
v_a_3433_ = lean_ctor_get(v___x_3432_, 0);
v_isSharedCheck_3444_ = !lean_is_exclusive(v___x_3432_);
if (v_isSharedCheck_3444_ == 0)
{
v___x_3435_ = v___x_3432_;
v_isShared_3436_ = v_isSharedCheck_3444_;
goto v_resetjp_3434_;
}
else
{
lean_inc(v_a_3433_);
lean_dec(v___x_3432_);
v___x_3435_ = lean_box(0);
v_isShared_3436_ = v_isSharedCheck_3444_;
goto v_resetjp_3434_;
}
v_resetjp_3434_:
{
lean_object* v___x_3438_; 
if (v_isShared_3422_ == 0)
{
lean_ctor_set(v___x_3421_, 1, v_a_3428_);
v___x_3438_ = v___x_3421_;
goto v_reusejp_3437_;
}
else
{
lean_object* v_reuseFailAlloc_3443_; 
v_reuseFailAlloc_3443_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3443_, 0, v_fst_3418_);
lean_ctor_set(v_reuseFailAlloc_3443_, 1, v_a_3428_);
v___x_3438_ = v_reuseFailAlloc_3443_;
goto v_reusejp_3437_;
}
v_reusejp_3437_:
{
lean_object* v___x_3439_; lean_object* v___x_3441_; 
v___x_3439_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3439_, 0, v_a_3433_);
lean_ctor_set(v___x_3439_, 1, v___x_3438_);
if (v_isShared_3436_ == 0)
{
lean_ctor_set(v___x_3435_, 0, v___x_3439_);
v___x_3441_ = v___x_3435_;
goto v_reusejp_3440_;
}
else
{
lean_object* v_reuseFailAlloc_3442_; 
v_reuseFailAlloc_3442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3442_, 0, v___x_3439_);
v___x_3441_ = v_reuseFailAlloc_3442_;
goto v_reusejp_3440_;
}
v_reusejp_3440_:
{
return v___x_3441_;
}
}
}
}
else
{
lean_object* v_a_3445_; lean_object* v___x_3447_; uint8_t v_isShared_3448_; uint8_t v_isSharedCheck_3452_; 
lean_dec(v_a_3428_);
lean_del_object(v___x_3421_);
lean_dec(v_fst_3418_);
v_a_3445_ = lean_ctor_get(v___x_3432_, 0);
v_isSharedCheck_3452_ = !lean_is_exclusive(v___x_3432_);
if (v_isSharedCheck_3452_ == 0)
{
v___x_3447_ = v___x_3432_;
v_isShared_3448_ = v_isSharedCheck_3452_;
goto v_resetjp_3446_;
}
else
{
lean_inc(v_a_3445_);
lean_dec(v___x_3432_);
v___x_3447_ = lean_box(0);
v_isShared_3448_ = v_isSharedCheck_3452_;
goto v_resetjp_3446_;
}
v_resetjp_3446_:
{
lean_object* v___x_3450_; 
if (v_isShared_3448_ == 0)
{
v___x_3450_ = v___x_3447_;
goto v_reusejp_3449_;
}
else
{
lean_object* v_reuseFailAlloc_3451_; 
v_reuseFailAlloc_3451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3451_, 0, v_a_3445_);
v___x_3450_ = v_reuseFailAlloc_3451_;
goto v_reusejp_3449_;
}
v_reusejp_3449_:
{
return v___x_3450_;
}
}
}
}
else
{
lean_object* v_a_3453_; lean_object* v___x_3455_; uint8_t v_isShared_3456_; uint8_t v_isSharedCheck_3460_; 
lean_dec_ref(v___x_3423_);
lean_del_object(v___x_3421_);
lean_dec(v_fst_3418_);
lean_dec_ref(v_lhs_3409_);
lean_dec_ref(v_fvars_3400_);
lean_dec(v___x_3399_);
v_a_3453_ = lean_ctor_get(v___x_3427_, 0);
v_isSharedCheck_3460_ = !lean_is_exclusive(v___x_3427_);
if (v_isSharedCheck_3460_ == 0)
{
v___x_3455_ = v___x_3427_;
v_isShared_3456_ = v_isSharedCheck_3460_;
goto v_resetjp_3454_;
}
else
{
lean_inc(v_a_3453_);
lean_dec(v___x_3427_);
v___x_3455_ = lean_box(0);
v_isShared_3456_ = v_isSharedCheck_3460_;
goto v_resetjp_3454_;
}
v_resetjp_3454_:
{
lean_object* v___x_3458_; 
if (v_isShared_3456_ == 0)
{
v___x_3458_ = v___x_3455_;
goto v_reusejp_3457_;
}
else
{
lean_object* v_reuseFailAlloc_3459_; 
v_reuseFailAlloc_3459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3459_, 0, v_a_3453_);
v___x_3458_ = v_reuseFailAlloc_3459_;
goto v_reusejp_3457_;
}
v_reusejp_3457_:
{
return v___x_3458_;
}
}
}
}
}
else
{
lean_object* v_a_3462_; lean_object* v___x_3464_; uint8_t v_isShared_3465_; uint8_t v_isSharedCheck_3469_; 
lean_dec_ref(v_lhs_3409_);
lean_dec_ref(v_fvars_3400_);
lean_dec(v___x_3399_);
v_a_3462_ = lean_ctor_get(v___x_3415_, 0);
v_isSharedCheck_3469_ = !lean_is_exclusive(v___x_3415_);
if (v_isSharedCheck_3469_ == 0)
{
v___x_3464_ = v___x_3415_;
v_isShared_3465_ = v_isSharedCheck_3469_;
goto v_resetjp_3463_;
}
else
{
lean_inc(v_a_3462_);
lean_dec(v___x_3415_);
v___x_3464_ = lean_box(0);
v_isShared_3465_ = v_isSharedCheck_3469_;
goto v_resetjp_3463_;
}
v_resetjp_3463_:
{
lean_object* v___x_3467_; 
if (v_isShared_3465_ == 0)
{
v___x_3467_ = v___x_3464_;
goto v_reusejp_3466_;
}
else
{
lean_object* v_reuseFailAlloc_3468_; 
v_reuseFailAlloc_3468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3468_, 0, v_a_3462_);
v___x_3467_ = v_reuseFailAlloc_3468_;
goto v_reusejp_3466_;
}
v_reusejp_3466_:
{
return v___x_3467_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_3395_ = stack[0].m_obj;
lean_object* v_univs_3396_ = stack[1].m_obj;
lean_object* v_numParams_3397_ = stack[2].m_obj;
lean_object* v_ctors_3398_ = stack[3].m_obj;
lean_object* v___x_3399_ = stack[4].m_obj;
lean_object* v_fvars_3400_ = stack[5].m_obj;
lean_object* v_ty_3401_ = stack[6].m_obj;
lean_object* v___y_3402_ = stack[7].m_obj;
lean_object* v___y_3403_ = stack[8].m_obj;
lean_object* v___y_3404_ = stack[9].m_obj;
lean_object* v___y_3405_ = stack[10].m_obj;
lean_object* v_res_3481_;
v_res_3481_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___lam__0(v_name_3395_, v_univs_3396_, v_numParams_3397_, v_ctors_3398_, v___x_3399_, v_fvars_3400_, v_ty_3401_, v___y_3402_, v___y_3403_, v___y_3404_, v___y_3405_);
stack->m_obj
 = v_res_3481_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___lam__0___boxed(lean_object* v_name_3482_, lean_object* v_univs_3483_, lean_object* v_numParams_3484_, lean_object* v_ctors_3485_, lean_object* v___x_3486_, lean_object* v_fvars_3487_, lean_object* v_ty_3488_, lean_object* v___y_3489_, lean_object* v___y_3490_, lean_object* v___y_3491_, lean_object* v___y_3492_, lean_object* v___y_3493_){
_start:
{
lean_object* v_res_3494_; 
v_res_3494_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___lam__0(v_name_3482_, v_univs_3483_, v_numParams_3484_, v_ctors_3485_, v___x_3486_, v_fvars_3487_, v_ty_3488_, v___y_3489_, v___y_3490_, v___y_3491_, v___y_3492_);
lean_dec(v___y_3492_);
lean_dec_ref(v___y_3491_);
lean_dec(v___y_3490_);
lean_dec_ref(v___y_3489_);
lean_dec_ref(v_ty_3488_);
return v_res_3494_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__2(lean_object* v_a_3495_, lean_object* v_a_3496_){
_start:
{
if (lean_obj_tag(v_a_3495_) == 0)
{
lean_object* v___x_3497_; 
v___x_3497_ = l_List_reverse___redArg(v_a_3496_);
return v___x_3497_;
}
else
{
lean_object* v_head_3498_; lean_object* v_tail_3499_; lean_object* v___x_3501_; uint8_t v_isShared_3502_; uint8_t v_isSharedCheck_3508_; 
v_head_3498_ = lean_ctor_get(v_a_3495_, 0);
v_tail_3499_ = lean_ctor_get(v_a_3495_, 1);
v_isSharedCheck_3508_ = !lean_is_exclusive(v_a_3495_);
if (v_isSharedCheck_3508_ == 0)
{
v___x_3501_ = v_a_3495_;
v_isShared_3502_ = v_isSharedCheck_3508_;
goto v_resetjp_3500_;
}
else
{
lean_inc(v_tail_3499_);
lean_inc(v_head_3498_);
lean_dec(v_a_3495_);
v___x_3501_ = lean_box(0);
v_isShared_3502_ = v_isSharedCheck_3508_;
goto v_resetjp_3500_;
}
v_resetjp_3500_:
{
lean_object* v___x_3503_; lean_object* v___x_3505_; 
v___x_3503_ = l_Lean_Expr_fvar___override(v_head_3498_);
if (v_isShared_3502_ == 0)
{
lean_ctor_set(v___x_3501_, 1, v_a_3496_);
lean_ctor_set(v___x_3501_, 0, v___x_3503_);
v___x_3505_ = v___x_3501_;
goto v_reusejp_3504_;
}
else
{
lean_object* v_reuseFailAlloc_3507_; 
v_reuseFailAlloc_3507_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3507_, 0, v___x_3503_);
lean_ctor_set(v_reuseFailAlloc_3507_, 1, v_a_3496_);
v___x_3505_ = v_reuseFailAlloc_3507_;
goto v_reusejp_3504_;
}
v_reusejp_3504_:
{
v_a_3495_ = v_tail_3499_;
v_a_3496_ = v___x_3505_;
goto _start;
}
}
}
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__6___closed__0(void){
_start:
{
lean_object* v___x_3509_; double v___x_3510_; 
v___x_3509_ = lean_unsigned_to_nat(0u);
v___x_3510_ = lean_float_of_nat(v___x_3509_);
return v___x_3510_;
}
}
lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__6(lean_object* v_cls_3514_, lean_object* v_msg_3515_, lean_object* v___y_3516_, lean_object* v___y_3517_, lean_object* v___y_3518_, lean_object* v___y_3519_){
_start:
{
lean_object* v_ref_3521_; lean_object* v___x_3522_; lean_object* v_a_3523_; lean_object* v___x_3525_; uint8_t v_isShared_3526_; uint8_t v_isSharedCheck_3568_; 
v_ref_3521_ = lean_ctor_get(v___y_3518_, 2);
v___x_3522_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0_spec__0(v_msg_3515_, v___y_3516_, v___y_3517_, v___y_3518_, v___y_3519_);
v_a_3523_ = lean_ctor_get(v___x_3522_, 0);
v_isSharedCheck_3568_ = !lean_is_exclusive(v___x_3522_);
if (v_isSharedCheck_3568_ == 0)
{
v___x_3525_ = v___x_3522_;
v_isShared_3526_ = v_isSharedCheck_3568_;
goto v_resetjp_3524_;
}
else
{
lean_inc(v_a_3523_);
lean_dec(v___x_3522_);
v___x_3525_ = lean_box(0);
v_isShared_3526_ = v_isSharedCheck_3568_;
goto v_resetjp_3524_;
}
v_resetjp_3524_:
{
lean_object* v___x_3527_; lean_object* v_traceState_3528_; lean_object* v_env_3529_; lean_object* v_nextMacroScope_3530_; lean_object* v_ngen_3531_; lean_object* v_auxDeclNGen_3532_; lean_object* v_cache_3533_; lean_object* v_recordedDeps_3534_; lean_object* v_messages_3535_; lean_object* v_infoState_3536_; lean_object* v_snapshotTasks_3537_; lean_object* v___x_3539_; uint8_t v_isShared_3540_; uint8_t v_isSharedCheck_3567_; 
v___x_3527_ = lean_st_ref_take(v___y_3519_);
v_traceState_3528_ = lean_ctor_get(v___x_3527_, 4);
v_env_3529_ = lean_ctor_get(v___x_3527_, 0);
v_nextMacroScope_3530_ = lean_ctor_get(v___x_3527_, 1);
v_ngen_3531_ = lean_ctor_get(v___x_3527_, 2);
v_auxDeclNGen_3532_ = lean_ctor_get(v___x_3527_, 3);
v_cache_3533_ = lean_ctor_get(v___x_3527_, 5);
v_recordedDeps_3534_ = lean_ctor_get(v___x_3527_, 6);
v_messages_3535_ = lean_ctor_get(v___x_3527_, 7);
v_infoState_3536_ = lean_ctor_get(v___x_3527_, 8);
v_snapshotTasks_3537_ = lean_ctor_get(v___x_3527_, 9);
v_isSharedCheck_3567_ = !lean_is_exclusive(v___x_3527_);
if (v_isSharedCheck_3567_ == 0)
{
v___x_3539_ = v___x_3527_;
v_isShared_3540_ = v_isSharedCheck_3567_;
goto v_resetjp_3538_;
}
else
{
lean_inc(v_snapshotTasks_3537_);
lean_inc(v_infoState_3536_);
lean_inc(v_messages_3535_);
lean_inc(v_recordedDeps_3534_);
lean_inc(v_cache_3533_);
lean_inc(v_traceState_3528_);
lean_inc(v_auxDeclNGen_3532_);
lean_inc(v_ngen_3531_);
lean_inc(v_nextMacroScope_3530_);
lean_inc(v_env_3529_);
lean_dec(v___x_3527_);
v___x_3539_ = lean_box(0);
v_isShared_3540_ = v_isSharedCheck_3567_;
goto v_resetjp_3538_;
}
v_resetjp_3538_:
{
uint64_t v_tid_3541_; lean_object* v_traces_3542_; lean_object* v___x_3544_; uint8_t v_isShared_3545_; uint8_t v_isSharedCheck_3566_; 
v_tid_3541_ = lean_ctor_get_uint64(v_traceState_3528_, sizeof(void*)*1);
v_traces_3542_ = lean_ctor_get(v_traceState_3528_, 0);
v_isSharedCheck_3566_ = !lean_is_exclusive(v_traceState_3528_);
if (v_isSharedCheck_3566_ == 0)
{
v___x_3544_ = v_traceState_3528_;
v_isShared_3545_ = v_isSharedCheck_3566_;
goto v_resetjp_3543_;
}
else
{
lean_inc(v_traces_3542_);
lean_dec(v_traceState_3528_);
v___x_3544_ = lean_box(0);
v_isShared_3545_ = v_isSharedCheck_3566_;
goto v_resetjp_3543_;
}
v_resetjp_3543_:
{
lean_object* v___x_3546_; lean_object* v___x_3547_; double v___x_3548_; uint8_t v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; lean_object* v___x_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; lean_object* v___x_3557_; 
v___x_3546_ = lean_box(0);
v___x_3547_ = lean_box(0);
v___x_3548_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__6___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__6___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__6___closed__0);
v___x_3549_ = 0;
v___x_3550_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__6___closed__1));
v___x_3551_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3551_, 0, v_cls_3514_);
lean_ctor_set(v___x_3551_, 1, v___x_3547_);
lean_ctor_set(v___x_3551_, 2, v___x_3550_);
lean_ctor_set_float(v___x_3551_, sizeof(void*)*3, v___x_3548_);
lean_ctor_set_float(v___x_3551_, sizeof(void*)*3 + 8, v___x_3548_);
lean_ctor_set_uint8(v___x_3551_, sizeof(void*)*3 + 16, v___x_3549_);
v___x_3552_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__6___closed__2));
v___x_3553_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3553_, 0, v___x_3551_);
lean_ctor_set(v___x_3553_, 1, v_a_3523_);
lean_ctor_set(v___x_3553_, 2, v___x_3552_);
lean_inc(v_ref_3521_);
v___x_3554_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3554_, 0, v_ref_3521_);
lean_ctor_set(v___x_3554_, 1, v___x_3553_);
v___x_3555_ = l_Lean_PersistentArray_push___redArg(v_traces_3542_, v___x_3554_);
if (v_isShared_3545_ == 0)
{
lean_ctor_set(v___x_3544_, 0, v___x_3555_);
v___x_3557_ = v___x_3544_;
goto v_reusejp_3556_;
}
else
{
lean_object* v_reuseFailAlloc_3565_; 
v_reuseFailAlloc_3565_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3565_, 0, v___x_3555_);
lean_ctor_set_uint64(v_reuseFailAlloc_3565_, sizeof(void*)*1, v_tid_3541_);
v___x_3557_ = v_reuseFailAlloc_3565_;
goto v_reusejp_3556_;
}
v_reusejp_3556_:
{
lean_object* v___x_3559_; 
if (v_isShared_3540_ == 0)
{
lean_ctor_set(v___x_3539_, 4, v___x_3557_);
v___x_3559_ = v___x_3539_;
goto v_reusejp_3558_;
}
else
{
lean_object* v_reuseFailAlloc_3564_; 
v_reuseFailAlloc_3564_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3564_, 0, v_env_3529_);
lean_ctor_set(v_reuseFailAlloc_3564_, 1, v_nextMacroScope_3530_);
lean_ctor_set(v_reuseFailAlloc_3564_, 2, v_ngen_3531_);
lean_ctor_set(v_reuseFailAlloc_3564_, 3, v_auxDeclNGen_3532_);
lean_ctor_set(v_reuseFailAlloc_3564_, 4, v___x_3557_);
lean_ctor_set(v_reuseFailAlloc_3564_, 5, v_cache_3533_);
lean_ctor_set(v_reuseFailAlloc_3564_, 6, v_recordedDeps_3534_);
lean_ctor_set(v_reuseFailAlloc_3564_, 7, v_messages_3535_);
lean_ctor_set(v_reuseFailAlloc_3564_, 8, v_infoState_3536_);
lean_ctor_set(v_reuseFailAlloc_3564_, 9, v_snapshotTasks_3537_);
v___x_3559_ = v_reuseFailAlloc_3564_;
goto v_reusejp_3558_;
}
v_reusejp_3558_:
{
lean_object* v___x_3560_; lean_object* v___x_3562_; 
v___x_3560_ = lean_st_ref_put(v___y_3519_, v___x_3559_);
if (v_isShared_3526_ == 0)
{
lean_ctor_set(v___x_3525_, 0, v___x_3546_);
v___x_3562_ = v___x_3525_;
goto v_reusejp_3561_;
}
else
{
lean_object* v_reuseFailAlloc_3563_; 
v_reuseFailAlloc_3563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3563_, 0, v___x_3546_);
v___x_3562_ = v_reuseFailAlloc_3563_;
goto v_reusejp_3561_;
}
v_reusejp_3561_:
{
return v___x_3562_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_3514_ = stack[0].m_obj;
lean_object* v_msg_3515_ = stack[1].m_obj;
lean_object* v___y_3516_ = stack[2].m_obj;
lean_object* v___y_3517_ = stack[3].m_obj;
lean_object* v___y_3518_ = stack[4].m_obj;
lean_object* v___y_3519_ = stack[5].m_obj;
lean_object* v_res_3569_;
v_res_3569_ = l_Lean_addTrace___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__6(v_cls_3514_, v_msg_3515_, v___y_3516_, v___y_3517_, v___y_3518_, v___y_3519_);
stack->m_obj
 = v_res_3569_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__6___boxed(lean_object* v_cls_3570_, lean_object* v_msg_3571_, lean_object* v___y_3572_, lean_object* v___y_3573_, lean_object* v___y_3574_, lean_object* v___y_3575_, lean_object* v___y_3576_){
_start:
{
lean_object* v_res_3577_; 
v_res_3577_ = l_Lean_addTrace___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__6(v_cls_3570_, v_msg_3571_, v___y_3572_, v___y_3573_, v___y_3574_, v___y_3575_);
lean_dec(v___y_3575_);
lean_dec_ref(v___y_3574_);
lean_dec(v___y_3573_);
lean_dec_ref(v___y_3572_);
return v_res_3577_;
}
}
static lean_object* _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__1(void){
_start:
{
lean_object* v___x_3579_; lean_object* v___x_3580_; 
v___x_3579_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__0));
v___x_3580_ = l_Lean_stringToMessageData(v___x_3579_);
return v___x_3580_;
}
}
static lean_object* _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__4(void){
_start:
{
lean_object* v___x_3585_; lean_object* v___x_3586_; lean_object* v___x_3587_; 
v___x_3585_ = lean_box(0);
v___x_3586_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__3));
v___x_3587_ = l_Lean_mkConst(v___x_3586_, v___x_3585_);
return v___x_3587_;
}
}
static lean_object* _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__13(void){
_start:
{
lean_object* v___x_3603_; lean_object* v___x_3604_; lean_object* v___x_3605_; 
v___x_3603_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__10));
v___x_3604_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__12));
v___x_3605_ = l_Lean_Name_append(v___x_3604_, v___x_3603_);
return v___x_3605_;
}
}
static lean_object* _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__15(void){
_start:
{
lean_object* v___x_3607_; lean_object* v___x_3608_; 
v___x_3607_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__14));
v___x_3608_ = l_Lean_stringToMessageData(v___x_3607_);
return v___x_3608_;
}
}
static lean_object* _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__17(void){
_start:
{
lean_object* v___x_3610_; lean_object* v___x_3611_; 
v___x_3610_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__16));
v___x_3611_ = l_Lean_stringToMessageData(v___x_3610_);
return v___x_3611_;
}
}
lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl(lean_object* v_inductVal_3612_, lean_object* v_rel_3613_, lean_object* v_a_3614_, lean_object* v_a_3615_, lean_object* v_a_3616_, lean_object* v_a_3617_){
_start:
{
lean_object* v___y_3620_; lean_object* v___y_3621_; lean_object* v___y_3622_; lean_object* v___y_3623_; lean_object* v_toConstantVal_3626_; lean_object* v_numParams_3627_; lean_object* v_ctors_3628_; lean_object* v_name_3629_; lean_object* v_levelParams_3630_; lean_object* v_type_3631_; lean_object* v___x_3633_; uint8_t v_isShared_3634_; uint8_t v_isSharedCheck_3795_; 
v_toConstantVal_3626_ = lean_ctor_get(v_inductVal_3612_, 0);
lean_inc_ref(v_toConstantVal_3626_);
v_numParams_3627_ = lean_ctor_get(v_inductVal_3612_, 1);
lean_inc(v_numParams_3627_);
v_ctors_3628_ = lean_ctor_get(v_inductVal_3612_, 4);
lean_inc(v_ctors_3628_);
lean_dec_ref(v_inductVal_3612_);
v_name_3629_ = lean_ctor_get(v_toConstantVal_3626_, 0);
v_levelParams_3630_ = lean_ctor_get(v_toConstantVal_3626_, 1);
v_type_3631_ = lean_ctor_get(v_toConstantVal_3626_, 2);
v_isSharedCheck_3795_ = !lean_is_exclusive(v_toConstantVal_3626_);
if (v_isSharedCheck_3795_ == 0)
{
v___x_3633_ = v_toConstantVal_3626_;
v_isShared_3634_ = v_isSharedCheck_3795_;
goto v_resetjp_3632_;
}
else
{
lean_inc(v_type_3631_);
lean_inc(v_levelParams_3630_);
lean_inc(v_name_3629_);
lean_dec(v_toConstantVal_3626_);
v___x_3633_ = lean_box(0);
v_isShared_3634_ = v_isSharedCheck_3795_;
goto v_resetjp_3632_;
}
v___jp_3619_:
{
lean_object* v___x_3624_; lean_object* v___x_3625_; 
v___x_3624_ = lean_obj_once(&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__1, &l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__1_once, _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__1);
v___x_3625_ = l_Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0___redArg(v___x_3624_, v___y_3620_, v___y_3621_, v___y_3622_, v___y_3623_);
return v___x_3625_;
}
v_resetjp_3632_:
{
lean_object* v___x_3635_; lean_object* v_univs_3636_; lean_object* v___f_3637_; uint8_t v___x_3638_; lean_object* v___x_3639_; 
v___x_3635_ = lean_box(0);
lean_inc(v_levelParams_3630_);
v_univs_3636_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__2_spec__3(v_levelParams_3630_, v___x_3635_);
lean_inc(v_ctors_3628_);
lean_inc(v_numParams_3627_);
lean_inc(v_name_3629_);
v___f_3637_ = lean_alloc_closure((void*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___lam__0___boxed), 12, 5);
lean_closure_set(v___f_3637_, 0, v_name_3629_);
lean_closure_set(v___f_3637_, 1, v_univs_3636_);
lean_closure_set(v___f_3637_, 2, v_numParams_3627_);
lean_closure_set(v___f_3637_, 3, v_ctors_3628_);
lean_closure_set(v___f_3637_, 4, v___x_3635_);
v___x_3638_ = 0;
v___x_3639_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__1___redArg(v_type_3631_, v___f_3637_, v___x_3638_, v___x_3638_, v_a_3614_, v_a_3615_, v_a_3616_, v_a_3617_);
if (lean_obj_tag(v___x_3639_) == 0)
{
lean_object* v_a_3640_; lean_object* v_snd_3641_; lean_object* v_fst_3642_; lean_object* v___x_3644_; uint8_t v_isShared_3645_; uint8_t v_isSharedCheck_3786_; 
v_a_3640_ = lean_ctor_get(v___x_3639_, 0);
lean_inc(v_a_3640_);
lean_dec_ref_known(v___x_3639_, 1);
v_snd_3641_ = lean_ctor_get(v_a_3640_, 1);
v_fst_3642_ = lean_ctor_get(v_a_3640_, 0);
v_isSharedCheck_3786_ = !lean_is_exclusive(v_a_3640_);
if (v_isSharedCheck_3786_ == 0)
{
v___x_3644_ = v_a_3640_;
v_isShared_3645_ = v_isSharedCheck_3786_;
goto v_resetjp_3643_;
}
else
{
lean_inc(v_snd_3641_);
lean_inc(v_fst_3642_);
lean_dec(v_a_3640_);
v___x_3644_ = lean_box(0);
v_isShared_3645_ = v_isSharedCheck_3786_;
goto v_resetjp_3643_;
}
v_resetjp_3643_:
{
lean_object* v_fst_3646_; lean_object* v_snd_3647_; lean_object* v___x_3649_; uint8_t v_isShared_3650_; uint8_t v_isSharedCheck_3785_; 
v_fst_3646_ = lean_ctor_get(v_snd_3641_, 0);
v_snd_3647_ = lean_ctor_get(v_snd_3641_, 1);
v_isSharedCheck_3785_ = !lean_is_exclusive(v_snd_3641_);
if (v_isSharedCheck_3785_ == 0)
{
v___x_3649_ = v_snd_3641_;
v_isShared_3650_ = v_isSharedCheck_3785_;
goto v_resetjp_3648_;
}
else
{
lean_inc(v_snd_3647_);
lean_inc(v_fst_3646_);
lean_dec(v_snd_3641_);
v___x_3649_ = lean_box(0);
v_isShared_3650_ = v_isSharedCheck_3785_;
goto v_resetjp_3648_;
}
v_resetjp_3648_:
{
lean_object* v___y_3652_; lean_object* v___y_3653_; lean_object* v___y_3654_; lean_object* v___y_3655_; lean_object* v_toCold_3757_; lean_object* v_options_3758_; uint8_t v_hasTrace_3759_; 
v_toCold_3757_ = lean_ctor_get(v_a_3616_, 0);
v_options_3758_ = lean_ctor_get(v_toCold_3757_, 2);
v_hasTrace_3759_ = lean_ctor_get_uint8(v_options_3758_, sizeof(void*)*1);
if (v_hasTrace_3759_ == 0)
{
lean_del_object(v___x_3649_);
lean_del_object(v___x_3644_);
v___y_3652_ = v_a_3614_;
v___y_3653_ = v_a_3615_;
v___y_3654_ = v_a_3616_;
v___y_3655_ = v_a_3617_;
goto v___jp_3651_;
}
else
{
lean_object* v_inheritedTraceOptions_3760_; lean_object* v___x_3761_; lean_object* v___y_3763_; lean_object* v___y_3764_; lean_object* v___y_3765_; lean_object* v_options_3766_; lean_object* v_inheritedTraceOptions_3767_; lean_object* v___y_3768_; lean_object* v___x_3777_; uint8_t v___x_3778_; 
v_inheritedTraceOptions_3760_ = lean_ctor_get(v_toCold_3757_, 11);
v___x_3761_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__10));
v___x_3777_ = lean_obj_once(&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__13, &l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__13_once, _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__13);
v___x_3778_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3760_, v_options_3758_, v___x_3777_);
if (v___x_3778_ == 0)
{
lean_del_object(v___x_3644_);
v___y_3763_ = v_a_3614_;
v___y_3764_ = v_a_3615_;
v___y_3765_ = v_a_3616_;
v_options_3766_ = v_options_3758_;
v_inheritedTraceOptions_3767_ = v_inheritedTraceOptions_3760_;
v___y_3768_ = v_a_3617_;
goto v___jp_3762_;
}
else
{
lean_object* v___x_3779_; lean_object* v___x_3780_; lean_object* v___x_3782_; 
v___x_3779_ = lean_obj_once(&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__17, &l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__17_once, _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__17);
lean_inc(v_snd_3647_);
v___x_3780_ = l_Lean_MessageData_ofExpr(v_snd_3647_);
if (v_isShared_3645_ == 0)
{
lean_ctor_set_tag(v___x_3644_, 7);
lean_ctor_set(v___x_3644_, 1, v___x_3780_);
lean_ctor_set(v___x_3644_, 0, v___x_3779_);
v___x_3782_ = v___x_3644_;
goto v_reusejp_3781_;
}
else
{
lean_object* v_reuseFailAlloc_3784_; 
v_reuseFailAlloc_3784_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3784_, 0, v___x_3779_);
lean_ctor_set(v_reuseFailAlloc_3784_, 1, v___x_3780_);
v___x_3782_ = v_reuseFailAlloc_3784_;
goto v_reusejp_3781_;
}
v_reusejp_3781_:
{
lean_object* v___x_3783_; 
v___x_3783_ = l_Lean_addTrace___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__6(v___x_3761_, v___x_3782_, v_a_3614_, v_a_3615_, v_a_3616_, v_a_3617_);
if (lean_obj_tag(v___x_3783_) == 0)
{
lean_dec_ref_known(v___x_3783_, 1);
v___y_3763_ = v_a_3614_;
v___y_3764_ = v_a_3615_;
v___y_3765_ = v_a_3616_;
v_options_3766_ = v_options_3758_;
v_inheritedTraceOptions_3767_ = v_inheritedTraceOptions_3760_;
v___y_3768_ = v_a_3617_;
goto v___jp_3762_;
}
else
{
lean_del_object(v___x_3649_);
lean_dec(v_snd_3647_);
lean_dec(v_fst_3646_);
lean_dec(v_fst_3642_);
lean_del_object(v___x_3633_);
lean_dec(v_levelParams_3630_);
lean_dec(v_name_3629_);
lean_dec(v_ctors_3628_);
lean_dec(v_numParams_3627_);
lean_dec(v_rel_3613_);
return v___x_3783_;
}
}
}
v___jp_3762_:
{
lean_object* v___x_3769_; uint8_t v___x_3770_; 
v___x_3769_ = lean_obj_once(&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__13, &l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__13_once, _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__13);
v___x_3770_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3767_, v_options_3766_, v___x_3769_);
if (v___x_3770_ == 0)
{
lean_del_object(v___x_3649_);
v___y_3652_ = v___y_3763_;
v___y_3653_ = v___y_3764_;
v___y_3654_ = v___y_3765_;
v___y_3655_ = v___y_3768_;
goto v___jp_3651_;
}
else
{
lean_object* v___x_3771_; lean_object* v___x_3772_; lean_object* v___x_3774_; 
v___x_3771_ = lean_obj_once(&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__15, &l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__15_once, _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__15);
lean_inc(v_fst_3642_);
v___x_3772_ = l_Lean_MessageData_ofExpr(v_fst_3642_);
if (v_isShared_3650_ == 0)
{
lean_ctor_set_tag(v___x_3649_, 7);
lean_ctor_set(v___x_3649_, 1, v___x_3772_);
lean_ctor_set(v___x_3649_, 0, v___x_3771_);
v___x_3774_ = v___x_3649_;
goto v_reusejp_3773_;
}
else
{
lean_object* v_reuseFailAlloc_3776_; 
v_reuseFailAlloc_3776_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3776_, 0, v___x_3771_);
lean_ctor_set(v_reuseFailAlloc_3776_, 1, v___x_3772_);
v___x_3774_ = v_reuseFailAlloc_3776_;
goto v_reusejp_3773_;
}
v_reusejp_3773_:
{
lean_object* v___x_3775_; 
v___x_3775_ = l_Lean_addTrace___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__6(v___x_3761_, v___x_3774_, v___y_3763_, v___y_3764_, v___y_3765_, v___y_3768_);
if (lean_obj_tag(v___x_3775_) == 0)
{
lean_dec_ref_known(v___x_3775_, 1);
v___y_3652_ = v___y_3763_;
v___y_3653_ = v___y_3764_;
v___y_3654_ = v___y_3765_;
v___y_3655_ = v___y_3768_;
goto v___jp_3651_;
}
else
{
lean_dec(v_snd_3647_);
lean_dec(v_fst_3646_);
lean_dec(v_fst_3642_);
lean_del_object(v___x_3633_);
lean_dec(v_levelParams_3630_);
lean_dec(v_name_3629_);
lean_dec(v_ctors_3628_);
lean_dec(v_numParams_3627_);
lean_dec(v_rel_3613_);
return v___x_3775_;
}
}
}
}
}
v___jp_3651_:
{
lean_object* v___x_3656_; uint8_t v___x_3657_; lean_object* v___x_3658_; lean_object* v___x_3659_; 
lean_inc(v_fst_3642_);
v___x_3656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3656_, 0, v_fst_3642_);
v___x_3657_ = 0;
v___x_3658_ = lean_box(0);
v___x_3659_ = l_Lean_Meta_mkFreshExprMVar(v___x_3656_, v___x_3657_, v___x_3658_, v___y_3652_, v___y_3653_, v___y_3654_, v___y_3655_);
if (lean_obj_tag(v___x_3659_) == 0)
{
lean_object* v_a_3660_; lean_object* v___x_3661_; lean_object* v___x_3662_; 
v_a_3660_ = lean_ctor_get(v___x_3659_, 0);
lean_inc(v_a_3660_);
lean_dec_ref_known(v___x_3659_, 1);
v___x_3661_ = l_Lean_Expr_mvarId_x21(v_a_3660_);
v___x_3662_ = l_Lean_MVarId_intros(v___x_3661_, v___y_3652_, v___y_3653_, v___y_3654_, v___y_3655_);
if (lean_obj_tag(v___x_3662_) == 0)
{
lean_object* v_a_3663_; lean_object* v_fst_3664_; lean_object* v_snd_3665_; lean_object* v___x_3666_; lean_object* v___x_3667_; lean_object* v___x_3668_; lean_object* v___x_3669_; 
v_a_3663_ = lean_ctor_get(v___x_3662_, 0);
lean_inc(v_a_3663_);
lean_dec_ref_known(v___x_3662_, 1);
v_fst_3664_ = lean_ctor_get(v_a_3663_, 0);
lean_inc(v_fst_3664_);
v_snd_3665_ = lean_ctor_get(v_a_3663_, 1);
lean_inc(v_snd_3665_);
lean_dec(v_a_3663_);
v___x_3666_ = lean_obj_once(&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__4, &l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__4_once, _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__4);
v___x_3667_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__5));
v___x_3668_ = lean_box(0);
v___x_3669_ = l_Lean_MVarId_apply(v_snd_3665_, v___x_3666_, v___x_3667_, v___x_3668_, v___y_3652_, v___y_3653_, v___y_3654_, v___y_3655_);
if (lean_obj_tag(v___x_3669_) == 0)
{
lean_object* v_a_3670_; 
v_a_3670_ = lean_ctor_get(v___x_3669_, 0);
lean_inc(v_a_3670_);
lean_dec_ref_known(v___x_3669_, 1);
if (lean_obj_tag(v_a_3670_) == 1)
{
lean_object* v_tail_3671_; 
v_tail_3671_ = lean_ctor_get(v_a_3670_, 1);
lean_inc(v_tail_3671_);
if (lean_obj_tag(v_tail_3671_) == 1)
{
lean_object* v_tail_3672_; 
v_tail_3672_ = lean_ctor_get(v_tail_3671_, 1);
if (lean_obj_tag(v_tail_3672_) == 0)
{
lean_object* v_head_3673_; lean_object* v_head_3674_; lean_object* v___x_3676_; uint8_t v_isShared_3677_; uint8_t v_isSharedCheck_3731_; 
v_head_3673_ = lean_ctor_get(v_a_3670_, 0);
lean_inc(v_head_3673_);
lean_dec_ref_known(v_a_3670_, 2);
v_head_3674_ = lean_ctor_get(v_tail_3671_, 0);
v_isSharedCheck_3731_ = !lean_is_exclusive(v_tail_3671_);
if (v_isSharedCheck_3731_ == 0)
{
lean_object* v_unused_3732_; 
v_unused_3732_ = lean_ctor_get(v_tail_3671_, 1);
lean_dec(v_unused_3732_);
v___x_3676_ = v_tail_3671_;
v_isShared_3677_ = v_isSharedCheck_3731_;
goto v_resetjp_3675_;
}
else
{
lean_inc(v_head_3674_);
lean_dec(v_tail_3671_);
v___x_3676_ = lean_box(0);
v_isShared_3677_ = v_isSharedCheck_3731_;
goto v_resetjp_3675_;
}
v_resetjp_3675_:
{
lean_object* v___x_3678_; 
lean_inc(v_fst_3646_);
v___x_3678_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toCases(v_head_3673_, v_fst_3646_, v___y_3652_, v___y_3653_, v___y_3654_, v___y_3655_);
if (lean_obj_tag(v___x_3678_) == 0)
{
lean_object* v___x_3679_; 
lean_dec_ref_known(v___x_3678_, 1);
v___x_3679_ = l_Lean_Meta_intro1Core(v_head_3674_, v___x_3638_, v___y_3652_, v___y_3653_, v___y_3654_, v___y_3655_);
if (lean_obj_tag(v___x_3679_) == 0)
{
lean_object* v_a_3680_; lean_object* v_fst_3681_; lean_object* v_snd_3682_; lean_object* v___x_3683_; lean_object* v___x_3684_; lean_object* v___x_3685_; lean_object* v___x_3686_; lean_object* v___x_3687_; 
v_a_3680_ = lean_ctor_get(v___x_3679_, 0);
lean_inc(v_a_3680_);
lean_dec_ref_known(v___x_3679_, 1);
v_fst_3681_ = lean_ctor_get(v_a_3680_, 0);
lean_inc(v_fst_3681_);
v_snd_3682_ = lean_ctor_get(v_a_3680_, 1);
lean_inc(v_snd_3682_);
lean_dec(v_a_3680_);
v___x_3683_ = lean_array_to_list(v_fst_3664_);
v___x_3684_ = ((lean_object*)(l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__5___lam__0___closed__0));
lean_inc(v___x_3683_);
v___x_3685_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), v___x_3683_, v___x_3683_, v_numParams_3627_, v___x_3684_);
lean_dec(v___x_3683_);
v___x_3686_ = l_List_mapTR_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__2(v___x_3685_, v___x_3635_);
v___x_3687_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive(v_snd_3682_, v_ctors_3628_, v___x_3686_, v_fst_3646_, v_fst_3681_, v___y_3652_, v___y_3653_, v___y_3654_, v___y_3655_);
if (lean_obj_tag(v___x_3687_) == 0)
{
lean_object* v___x_3688_; lean_object* v_a_3689_; lean_object* v___x_3691_; 
lean_dec_ref_known(v___x_3687_, 1);
v___x_3688_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__3___redArg(v_a_3660_, v___y_3653_);
v_a_3689_ = lean_ctor_get(v___x_3688_, 0);
lean_inc(v_a_3689_);
lean_dec_ref(v___x_3688_);
lean_inc(v_levelParams_3630_);
lean_inc(v_rel_3613_);
if (v_isShared_3634_ == 0)
{
lean_ctor_set(v___x_3633_, 2, v_fst_3642_);
lean_ctor_set(v___x_3633_, 0, v_rel_3613_);
v___x_3691_ = v___x_3633_;
goto v_reusejp_3690_;
}
else
{
lean_object* v_reuseFailAlloc_3722_; 
v_reuseFailAlloc_3722_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3722_, 0, v_rel_3613_);
lean_ctor_set(v_reuseFailAlloc_3722_, 1, v_levelParams_3630_);
lean_ctor_set(v_reuseFailAlloc_3722_, 2, v_fst_3642_);
v___x_3691_ = v_reuseFailAlloc_3722_;
goto v_reusejp_3690_;
}
v_reusejp_3690_:
{
lean_object* v___x_3693_; 
if (v_isShared_3677_ == 0)
{
lean_ctor_set(v___x_3676_, 1, v___x_3635_);
lean_ctor_set(v___x_3676_, 0, v_rel_3613_);
v___x_3693_ = v___x_3676_;
goto v_reusejp_3692_;
}
else
{
lean_object* v_reuseFailAlloc_3721_; 
v_reuseFailAlloc_3721_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3721_, 0, v_rel_3613_);
lean_ctor_set(v_reuseFailAlloc_3721_, 1, v___x_3635_);
v___x_3693_ = v_reuseFailAlloc_3721_;
goto v_reusejp_3692_;
}
v_reusejp_3692_:
{
lean_object* v___x_3694_; lean_object* v___x_3695_; lean_object* v_a_3696_; lean_object* v___x_3697_; 
v___x_3694_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3694_, 0, v___x_3691_);
lean_ctor_set(v___x_3694_, 1, v_a_3689_);
lean_ctor_set(v___x_3694_, 2, v___x_3693_);
v___x_3695_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__4___redArg(v___x_3694_, v___y_3655_);
v_a_3696_ = lean_ctor_get(v___x_3695_, 0);
lean_inc(v_a_3696_);
lean_dec_ref(v___x_3695_);
v___x_3697_ = l_Lean_addDecl(v_a_3696_, v___x_3638_, v___y_3654_, v___y_3655_);
if (lean_obj_tag(v___x_3697_) == 0)
{
lean_object* v___x_3698_; 
lean_dec_ref_known(v___x_3697_, 1);
lean_inc(v___y_3655_);
lean_inc_ref(v___y_3654_);
lean_inc(v___y_3653_);
lean_inc_ref(v___y_3652_);
lean_inc(v_snd_3647_);
v___x_3698_ = lean_infer_type(v_snd_3647_, v___y_3652_, v___y_3653_, v___y_3654_, v___y_3655_);
if (lean_obj_tag(v___x_3698_) == 0)
{
lean_object* v_a_3699_; lean_object* v___x_3700_; lean_object* v___x_3701_; lean_object* v___x_3702_; lean_object* v___x_3703_; lean_object* v_a_3704_; lean_object* v___x_3706_; uint8_t v_isShared_3707_; uint8_t v_isSharedCheck_3712_; 
v_a_3699_ = lean_ctor_get(v___x_3698_, 0);
lean_inc(v_a_3699_);
lean_dec_ref_known(v___x_3698_, 1);
v___x_3700_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__7));
v___x_3701_ = l_Lean_Name_append(v_name_3629_, v___x_3700_);
v___x_3702_ = lean_box(0);
v___x_3703_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__5___redArg(v___x_3701_, v_levelParams_3630_, v_a_3699_, v_snd_3647_, v___x_3702_, v___y_3655_);
v_a_3704_ = lean_ctor_get(v___x_3703_, 0);
v_isSharedCheck_3712_ = !lean_is_exclusive(v___x_3703_);
if (v_isSharedCheck_3712_ == 0)
{
v___x_3706_ = v___x_3703_;
v_isShared_3707_ = v_isSharedCheck_3712_;
goto v_resetjp_3705_;
}
else
{
lean_inc(v_a_3704_);
lean_dec(v___x_3703_);
v___x_3706_ = lean_box(0);
v_isShared_3707_ = v_isSharedCheck_3712_;
goto v_resetjp_3705_;
}
v_resetjp_3705_:
{
lean_object* v___x_3709_; 
if (v_isShared_3707_ == 0)
{
lean_ctor_set_tag(v___x_3706_, 1);
v___x_3709_ = v___x_3706_;
goto v_reusejp_3708_;
}
else
{
lean_object* v_reuseFailAlloc_3711_; 
v_reuseFailAlloc_3711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3711_, 0, v_a_3704_);
v___x_3709_ = v_reuseFailAlloc_3711_;
goto v_reusejp_3708_;
}
v_reusejp_3708_:
{
lean_object* v___x_3710_; 
v___x_3710_ = l_Lean_addDecl(v___x_3709_, v___x_3638_, v___y_3654_, v___y_3655_);
return v___x_3710_;
}
}
}
else
{
lean_object* v_a_3713_; lean_object* v___x_3715_; uint8_t v_isShared_3716_; uint8_t v_isSharedCheck_3720_; 
lean_dec(v_snd_3647_);
lean_dec(v_levelParams_3630_);
lean_dec(v_name_3629_);
v_a_3713_ = lean_ctor_get(v___x_3698_, 0);
v_isSharedCheck_3720_ = !lean_is_exclusive(v___x_3698_);
if (v_isSharedCheck_3720_ == 0)
{
v___x_3715_ = v___x_3698_;
v_isShared_3716_ = v_isSharedCheck_3720_;
goto v_resetjp_3714_;
}
else
{
lean_inc(v_a_3713_);
lean_dec(v___x_3698_);
v___x_3715_ = lean_box(0);
v_isShared_3716_ = v_isSharedCheck_3720_;
goto v_resetjp_3714_;
}
v_resetjp_3714_:
{
lean_object* v___x_3718_; 
if (v_isShared_3716_ == 0)
{
v___x_3718_ = v___x_3715_;
goto v_reusejp_3717_;
}
else
{
lean_object* v_reuseFailAlloc_3719_; 
v_reuseFailAlloc_3719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3719_, 0, v_a_3713_);
v___x_3718_ = v_reuseFailAlloc_3719_;
goto v_reusejp_3717_;
}
v_reusejp_3717_:
{
return v___x_3718_;
}
}
}
}
else
{
lean_dec(v_snd_3647_);
lean_dec(v_levelParams_3630_);
lean_dec(v_name_3629_);
return v___x_3697_;
}
}
}
}
else
{
lean_del_object(v___x_3676_);
lean_dec(v_a_3660_);
lean_dec(v_snd_3647_);
lean_dec(v_fst_3642_);
lean_del_object(v___x_3633_);
lean_dec(v_levelParams_3630_);
lean_dec(v_name_3629_);
lean_dec(v_rel_3613_);
return v___x_3687_;
}
}
else
{
lean_object* v_a_3723_; lean_object* v___x_3725_; uint8_t v_isShared_3726_; uint8_t v_isSharedCheck_3730_; 
lean_del_object(v___x_3676_);
lean_dec(v_fst_3664_);
lean_dec(v_a_3660_);
lean_dec(v_snd_3647_);
lean_dec(v_fst_3646_);
lean_dec(v_fst_3642_);
lean_del_object(v___x_3633_);
lean_dec(v_levelParams_3630_);
lean_dec(v_name_3629_);
lean_dec(v_ctors_3628_);
lean_dec(v_numParams_3627_);
lean_dec(v_rel_3613_);
v_a_3723_ = lean_ctor_get(v___x_3679_, 0);
v_isSharedCheck_3730_ = !lean_is_exclusive(v___x_3679_);
if (v_isSharedCheck_3730_ == 0)
{
v___x_3725_ = v___x_3679_;
v_isShared_3726_ = v_isSharedCheck_3730_;
goto v_resetjp_3724_;
}
else
{
lean_inc(v_a_3723_);
lean_dec(v___x_3679_);
v___x_3725_ = lean_box(0);
v_isShared_3726_ = v_isSharedCheck_3730_;
goto v_resetjp_3724_;
}
v_resetjp_3724_:
{
lean_object* v___x_3728_; 
if (v_isShared_3726_ == 0)
{
v___x_3728_ = v___x_3725_;
goto v_reusejp_3727_;
}
else
{
lean_object* v_reuseFailAlloc_3729_; 
v_reuseFailAlloc_3729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3729_, 0, v_a_3723_);
v___x_3728_ = v_reuseFailAlloc_3729_;
goto v_reusejp_3727_;
}
v_reusejp_3727_:
{
return v___x_3728_;
}
}
}
}
else
{
lean_del_object(v___x_3676_);
lean_dec(v_head_3674_);
lean_dec(v_fst_3664_);
lean_dec(v_a_3660_);
lean_dec(v_snd_3647_);
lean_dec(v_fst_3646_);
lean_dec(v_fst_3642_);
lean_del_object(v___x_3633_);
lean_dec(v_levelParams_3630_);
lean_dec(v_name_3629_);
lean_dec(v_ctors_3628_);
lean_dec(v_numParams_3627_);
lean_dec(v_rel_3613_);
return v___x_3678_;
}
}
}
else
{
lean_dec_ref_known(v_tail_3671_, 2);
lean_dec_ref_known(v_a_3670_, 2);
lean_dec(v_fst_3664_);
lean_dec(v_a_3660_);
lean_dec(v_snd_3647_);
lean_dec(v_fst_3646_);
lean_dec(v_fst_3642_);
lean_del_object(v___x_3633_);
lean_dec(v_levelParams_3630_);
lean_dec(v_name_3629_);
lean_dec(v_ctors_3628_);
lean_dec(v_numParams_3627_);
lean_dec(v_rel_3613_);
v___y_3620_ = v___y_3652_;
v___y_3621_ = v___y_3653_;
v___y_3622_ = v___y_3654_;
v___y_3623_ = v___y_3655_;
goto v___jp_3619_;
}
}
else
{
lean_dec_ref_known(v_a_3670_, 2);
lean_dec(v_tail_3671_);
lean_dec(v_fst_3664_);
lean_dec(v_a_3660_);
lean_dec(v_snd_3647_);
lean_dec(v_fst_3646_);
lean_dec(v_fst_3642_);
lean_del_object(v___x_3633_);
lean_dec(v_levelParams_3630_);
lean_dec(v_name_3629_);
lean_dec(v_ctors_3628_);
lean_dec(v_numParams_3627_);
lean_dec(v_rel_3613_);
v___y_3620_ = v___y_3652_;
v___y_3621_ = v___y_3653_;
v___y_3622_ = v___y_3654_;
v___y_3623_ = v___y_3655_;
goto v___jp_3619_;
}
}
else
{
lean_dec(v_a_3670_);
lean_dec(v_fst_3664_);
lean_dec(v_a_3660_);
lean_dec(v_snd_3647_);
lean_dec(v_fst_3646_);
lean_dec(v_fst_3642_);
lean_del_object(v___x_3633_);
lean_dec(v_levelParams_3630_);
lean_dec(v_name_3629_);
lean_dec(v_ctors_3628_);
lean_dec(v_numParams_3627_);
lean_dec(v_rel_3613_);
v___y_3620_ = v___y_3652_;
v___y_3621_ = v___y_3653_;
v___y_3622_ = v___y_3654_;
v___y_3623_ = v___y_3655_;
goto v___jp_3619_;
}
}
else
{
lean_object* v_a_3733_; lean_object* v___x_3735_; uint8_t v_isShared_3736_; uint8_t v_isSharedCheck_3740_; 
lean_dec(v_fst_3664_);
lean_dec(v_a_3660_);
lean_dec(v_snd_3647_);
lean_dec(v_fst_3646_);
lean_dec(v_fst_3642_);
lean_del_object(v___x_3633_);
lean_dec(v_levelParams_3630_);
lean_dec(v_name_3629_);
lean_dec(v_ctors_3628_);
lean_dec(v_numParams_3627_);
lean_dec(v_rel_3613_);
v_a_3733_ = lean_ctor_get(v___x_3669_, 0);
v_isSharedCheck_3740_ = !lean_is_exclusive(v___x_3669_);
if (v_isSharedCheck_3740_ == 0)
{
v___x_3735_ = v___x_3669_;
v_isShared_3736_ = v_isSharedCheck_3740_;
goto v_resetjp_3734_;
}
else
{
lean_inc(v_a_3733_);
lean_dec(v___x_3669_);
v___x_3735_ = lean_box(0);
v_isShared_3736_ = v_isSharedCheck_3740_;
goto v_resetjp_3734_;
}
v_resetjp_3734_:
{
lean_object* v___x_3738_; 
if (v_isShared_3736_ == 0)
{
v___x_3738_ = v___x_3735_;
goto v_reusejp_3737_;
}
else
{
lean_object* v_reuseFailAlloc_3739_; 
v_reuseFailAlloc_3739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3739_, 0, v_a_3733_);
v___x_3738_ = v_reuseFailAlloc_3739_;
goto v_reusejp_3737_;
}
v_reusejp_3737_:
{
return v___x_3738_;
}
}
}
}
else
{
lean_object* v_a_3741_; lean_object* v___x_3743_; uint8_t v_isShared_3744_; uint8_t v_isSharedCheck_3748_; 
lean_dec(v_a_3660_);
lean_dec(v_snd_3647_);
lean_dec(v_fst_3646_);
lean_dec(v_fst_3642_);
lean_del_object(v___x_3633_);
lean_dec(v_levelParams_3630_);
lean_dec(v_name_3629_);
lean_dec(v_ctors_3628_);
lean_dec(v_numParams_3627_);
lean_dec(v_rel_3613_);
v_a_3741_ = lean_ctor_get(v___x_3662_, 0);
v_isSharedCheck_3748_ = !lean_is_exclusive(v___x_3662_);
if (v_isSharedCheck_3748_ == 0)
{
v___x_3743_ = v___x_3662_;
v_isShared_3744_ = v_isSharedCheck_3748_;
goto v_resetjp_3742_;
}
else
{
lean_inc(v_a_3741_);
lean_dec(v___x_3662_);
v___x_3743_ = lean_box(0);
v_isShared_3744_ = v_isSharedCheck_3748_;
goto v_resetjp_3742_;
}
v_resetjp_3742_:
{
lean_object* v___x_3746_; 
if (v_isShared_3744_ == 0)
{
v___x_3746_ = v___x_3743_;
goto v_reusejp_3745_;
}
else
{
lean_object* v_reuseFailAlloc_3747_; 
v_reuseFailAlloc_3747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3747_, 0, v_a_3741_);
v___x_3746_ = v_reuseFailAlloc_3747_;
goto v_reusejp_3745_;
}
v_reusejp_3745_:
{
return v___x_3746_;
}
}
}
}
else
{
lean_object* v_a_3749_; lean_object* v___x_3751_; uint8_t v_isShared_3752_; uint8_t v_isSharedCheck_3756_; 
lean_dec(v_snd_3647_);
lean_dec(v_fst_3646_);
lean_dec(v_fst_3642_);
lean_del_object(v___x_3633_);
lean_dec(v_levelParams_3630_);
lean_dec(v_name_3629_);
lean_dec(v_ctors_3628_);
lean_dec(v_numParams_3627_);
lean_dec(v_rel_3613_);
v_a_3749_ = lean_ctor_get(v___x_3659_, 0);
v_isSharedCheck_3756_ = !lean_is_exclusive(v___x_3659_);
if (v_isSharedCheck_3756_ == 0)
{
v___x_3751_ = v___x_3659_;
v_isShared_3752_ = v_isSharedCheck_3756_;
goto v_resetjp_3750_;
}
else
{
lean_inc(v_a_3749_);
lean_dec(v___x_3659_);
v___x_3751_ = lean_box(0);
v_isShared_3752_ = v_isSharedCheck_3756_;
goto v_resetjp_3750_;
}
v_resetjp_3750_:
{
lean_object* v___x_3754_; 
if (v_isShared_3752_ == 0)
{
v___x_3754_ = v___x_3751_;
goto v_reusejp_3753_;
}
else
{
lean_object* v_reuseFailAlloc_3755_; 
v_reuseFailAlloc_3755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3755_, 0, v_a_3749_);
v___x_3754_ = v_reuseFailAlloc_3755_;
goto v_reusejp_3753_;
}
v_reusejp_3753_:
{
return v___x_3754_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3787_; lean_object* v___x_3789_; uint8_t v_isShared_3790_; uint8_t v_isSharedCheck_3794_; 
lean_del_object(v___x_3633_);
lean_dec(v_levelParams_3630_);
lean_dec(v_name_3629_);
lean_dec(v_ctors_3628_);
lean_dec(v_numParams_3627_);
lean_dec(v_rel_3613_);
v_a_3787_ = lean_ctor_get(v___x_3639_, 0);
v_isSharedCheck_3794_ = !lean_is_exclusive(v___x_3639_);
if (v_isSharedCheck_3794_ == 0)
{
v___x_3789_ = v___x_3639_;
v_isShared_3790_ = v_isSharedCheck_3794_;
goto v_resetjp_3788_;
}
else
{
lean_inc(v_a_3787_);
lean_dec(v___x_3639_);
v___x_3789_ = lean_box(0);
v_isShared_3790_ = v_isSharedCheck_3794_;
goto v_resetjp_3788_;
}
v_resetjp_3788_:
{
lean_object* v___x_3792_; 
if (v_isShared_3790_ == 0)
{
v___x_3792_ = v___x_3789_;
goto v_reusejp_3791_;
}
else
{
lean_object* v_reuseFailAlloc_3793_; 
v_reuseFailAlloc_3793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3793_, 0, v_a_3787_);
v___x_3792_ = v_reuseFailAlloc_3793_;
goto v_reusejp_3791_;
}
v_reusejp_3791_:
{
return v___x_3792_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_0interp(lean_interpreter_value* stack)
{
lean_object* v_inductVal_3612_ = stack[0].m_obj;
lean_object* v_rel_3613_ = stack[1].m_obj;
lean_object* v_a_3614_ = stack[2].m_obj;
lean_object* v_a_3615_ = stack[3].m_obj;
lean_object* v_a_3616_ = stack[4].m_obj;
lean_object* v_a_3617_ = stack[5].m_obj;
lean_object* v_res_3796_;
v_res_3796_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl(v_inductVal_3612_, v_rel_3613_, v_a_3614_, v_a_3615_, v_a_3616_, v_a_3617_);
stack->m_obj
 = v_res_3796_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___boxed(lean_object* v_inductVal_3797_, lean_object* v_rel_3798_, lean_object* v_a_3799_, lean_object* v_a_3800_, lean_object* v_a_3801_, lean_object* v_a_3802_, lean_object* v_a_3803_){
_start:
{
lean_object* v_res_3804_; 
v_res_3804_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl(v_inductVal_3797_, v_rel_3798_, v_a_3799_, v_a_3800_, v_a_3801_, v_a_3802_);
lean_dec(v_a_3802_);
lean_dec_ref(v_a_3801_);
lean_dec(v_a_3800_);
lean_dec_ref(v_a_3799_);
return v_res_3804_;
}
}
static lean_object* _init_l_Lean_Meta_mkSumOfProducts___closed__3(void){
_start:
{
lean_object* v___x_3809_; lean_object* v___x_3810_; 
v___x_3809_ = ((lean_object*)(l_Lean_Meta_mkSumOfProducts___closed__2));
v___x_3810_ = l_Lean_stringToMessageData(v___x_3809_);
return v___x_3810_;
}
}
static lean_object* _init_l_Lean_Meta_mkSumOfProducts___closed__5(void){
_start:
{
lean_object* v___x_3812_; lean_object* v___x_3813_; 
v___x_3812_ = ((lean_object*)(l_Lean_Meta_mkSumOfProducts___closed__4));
v___x_3813_ = l_Lean_stringToMessageData(v___x_3812_);
return v___x_3813_;
}
}
lean_object* l_Lean_Meta_mkSumOfProducts(lean_object* v_declName_3814_, lean_object* v_a_3815_, lean_object* v_a_3816_, lean_object* v_a_3817_, lean_object* v_a_3818_){
_start:
{
lean_object* v___y_3821_; lean_object* v___y_3822_; lean_object* v___y_3823_; lean_object* v___y_3824_; lean_object* v_toCold_3841_; lean_object* v_options_3842_; uint8_t v_hasTrace_3843_; 
v_toCold_3841_ = lean_ctor_get(v_a_3817_, 0);
v_options_3842_ = lean_ctor_get(v_toCold_3841_, 2);
v_hasTrace_3843_ = lean_ctor_get_uint8(v_options_3842_, sizeof(void*)*1);
if (v_hasTrace_3843_ == 0)
{
v___y_3821_ = v_a_3815_;
v___y_3822_ = v_a_3816_;
v___y_3823_ = v_a_3817_;
v___y_3824_ = v_a_3818_;
goto v___jp_3820_;
}
else
{
lean_object* v_inheritedTraceOptions_3844_; lean_object* v_cls_3845_; lean_object* v___x_3846_; uint8_t v___x_3847_; 
v_inheritedTraceOptions_3844_ = lean_ctor_get(v_toCold_3841_, 11);
v_cls_3845_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__10));
v___x_3846_ = lean_obj_once(&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__13, &l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__13_once, _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__13);
v___x_3847_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3844_, v_options_3842_, v___x_3846_);
if (v___x_3847_ == 0)
{
v___y_3821_ = v_a_3815_;
v___y_3822_ = v_a_3816_;
v___y_3823_ = v_a_3817_;
v___y_3824_ = v_a_3818_;
goto v___jp_3820_;
}
else
{
lean_object* v___x_3848_; lean_object* v___x_3849_; lean_object* v___x_3850_; lean_object* v___x_3851_; 
v___x_3848_ = lean_obj_once(&l_Lean_Meta_mkSumOfProducts___closed__5, &l_Lean_Meta_mkSumOfProducts___closed__5_once, _init_l_Lean_Meta_mkSumOfProducts___closed__5);
lean_inc(v_declName_3814_);
v___x_3849_ = l_Lean_MessageData_ofName(v_declName_3814_);
v___x_3850_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3850_, 0, v___x_3848_);
lean_ctor_set(v___x_3850_, 1, v___x_3849_);
v___x_3851_ = l_Lean_addTrace___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__6(v_cls_3845_, v___x_3850_, v_a_3815_, v_a_3816_, v_a_3817_, v_a_3818_);
if (lean_obj_tag(v___x_3851_) == 0)
{
lean_dec_ref_known(v___x_3851_, 1);
v___y_3821_ = v_a_3815_;
v___y_3822_ = v_a_3816_;
v___y_3823_ = v_a_3817_;
v___y_3824_ = v_a_3818_;
goto v___jp_3820_;
}
else
{
lean_dec(v_declName_3814_);
return v___x_3851_;
}
}
}
v___jp_3820_:
{
lean_object* v___x_3825_; 
lean_inc(v_declName_3814_);
v___x_3825_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0(v_declName_3814_, v___y_3821_, v___y_3822_, v___y_3823_, v___y_3824_);
if (lean_obj_tag(v___x_3825_) == 0)
{
lean_object* v_a_3826_; 
v_a_3826_ = lean_ctor_get(v___x_3825_, 0);
lean_inc(v_a_3826_);
lean_dec_ref_known(v___x_3825_, 1);
if (lean_obj_tag(v_a_3826_) == 5)
{
lean_object* v_val_3827_; lean_object* v___x_3828_; lean_object* v___x_3829_; lean_object* v___x_3830_; 
v_val_3827_ = lean_ctor_get(v_a_3826_, 0);
lean_inc_ref(v_val_3827_);
lean_dec_ref_known(v_a_3826_, 1);
v___x_3828_ = ((lean_object*)(l_Lean_Meta_mkSumOfProducts___closed__1));
v___x_3829_ = l_Lean_Name_append(v_declName_3814_, v___x_3828_);
v___x_3830_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl(v_val_3827_, v___x_3829_, v___y_3821_, v___y_3822_, v___y_3823_, v___y_3824_);
return v___x_3830_;
}
else
{
lean_object* v___x_3831_; lean_object* v___x_3832_; 
lean_dec(v_a_3826_);
lean_dec(v_declName_3814_);
v___x_3831_ = lean_obj_once(&l_Lean_Meta_mkSumOfProducts___closed__3, &l_Lean_Meta_mkSumOfProducts___closed__3_once, _init_l_Lean_Meta_mkSumOfProducts___closed__3);
v___x_3832_ = l_Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0___redArg(v___x_3831_, v___y_3821_, v___y_3822_, v___y_3823_, v___y_3824_);
return v___x_3832_;
}
}
else
{
lean_object* v_a_3833_; lean_object* v___x_3835_; uint8_t v_isShared_3836_; uint8_t v_isSharedCheck_3840_; 
lean_dec(v_declName_3814_);
v_a_3833_ = lean_ctor_get(v___x_3825_, 0);
v_isSharedCheck_3840_ = !lean_is_exclusive(v___x_3825_);
if (v_isSharedCheck_3840_ == 0)
{
v___x_3835_ = v___x_3825_;
v_isShared_3836_ = v_isSharedCheck_3840_;
goto v_resetjp_3834_;
}
else
{
lean_inc(v_a_3833_);
lean_dec(v___x_3825_);
v___x_3835_ = lean_box(0);
v_isShared_3836_ = v_isSharedCheck_3840_;
goto v_resetjp_3834_;
}
v_resetjp_3834_:
{
lean_object* v___x_3838_; 
if (v_isShared_3836_ == 0)
{
v___x_3838_ = v___x_3835_;
goto v_reusejp_3837_;
}
else
{
lean_object* v_reuseFailAlloc_3839_; 
v_reuseFailAlloc_3839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3839_, 0, v_a_3833_);
v___x_3838_ = v_reuseFailAlloc_3839_;
goto v_reusejp_3837_;
}
v_reusejp_3837_:
{
return v___x_3838_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_mkSumOfProducts_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_3814_ = stack[0].m_obj;
lean_object* v_a_3815_ = stack[1].m_obj;
lean_object* v_a_3816_ = stack[2].m_obj;
lean_object* v_a_3817_ = stack[3].m_obj;
lean_object* v_a_3818_ = stack[4].m_obj;
lean_object* v_res_3852_;
v_res_3852_ = l_Lean_Meta_mkSumOfProducts(v_declName_3814_, v_a_3815_, v_a_3816_, v_a_3817_, v_a_3818_);
stack->m_obj
 = v_res_3852_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSumOfProducts___boxed(lean_object* v_declName_3853_, lean_object* v_a_3854_, lean_object* v_a_3855_, lean_object* v_a_3856_, lean_object* v_a_3857_, lean_object* v_a_3858_){
_start:
{
lean_object* v_res_3859_; 
v_res_3859_ = l_Lean_Meta_mkSumOfProducts(v_declName_3853_, v_a_3854_, v_a_3855_, v_a_3856_, v_a_3857_);
lean_dec(v_a_3857_);
lean_dec_ref(v_a_3856_);
lean_dec(v_a_3855_);
lean_dec_ref(v_a_3854_);
return v_res_3859_;
}
}
static lean_object* _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3899_; lean_object* v___x_3900_; lean_object* v___x_3901_; 
v___x_3899_ = lean_unsigned_to_nat(3649998058u);
v___x_3900_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2_));
v___x_3901_ = l_Lean_Name_num___override(v___x_3900_, v___x_3899_);
return v___x_3901_;
}
}
static lean_object* _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3903_; lean_object* v___x_3904_; lean_object* v___x_3905_; 
v___x_3903_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2_));
v___x_3904_ = lean_obj_once(&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2_, &l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2_);
v___x_3905_ = l_Lean_Name_str___override(v___x_3904_, v___x_3903_);
return v___x_3905_;
}
}
static lean_object* _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3907_; lean_object* v___x_3908_; lean_object* v___x_3909_; 
v___x_3907_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2_));
v___x_3908_ = lean_obj_once(&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2_, &l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2_);
v___x_3909_ = l_Lean_Name_str___override(v___x_3908_, v___x_3907_);
return v___x_3909_;
}
}
static lean_object* _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3910_; lean_object* v___x_3911_; lean_object* v___x_3912_; 
v___x_3910_ = lean_unsigned_to_nat(2u);
v___x_3911_ = lean_obj_once(&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2_, &l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2_);
v___x_3912_ = l_Lean_Name_num___override(v___x_3911_, v___x_3910_);
return v___x_3912_;
}
}
lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3914_; uint8_t v___x_3915_; lean_object* v___x_3916_; lean_object* v___x_3917_; 
v___x_3914_ = ((lean_object*)(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__10));
v___x_3915_ = 0;
v___x_3916_ = lean_obj_once(&l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2_, &l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2_);
v___x_3917_ = l_Lean_registerTraceClass(v___x_3914_, v___x_3915_, v___x_3916_);
return v___x_3917_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3918_;
v_res_3918_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2_();
stack->m_obj
 = v_res_3918_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2____boxed(lean_object* v_a_3919_){
_start:
{
lean_object* v_res_3920_; 
v_res_3920_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2_();
return v_res_3920_;
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
