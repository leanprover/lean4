// Lean compiler output
// Module: Lean.Elab.Tactic.Conv.Lets
// Imports: public import Lean.Elab.Tactic.Lets public import Lean.Elab.Tactic.Conv.Basic
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
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Elab_Tactic_getNameOfIdent_x27(lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_Elab_Tactic_Conv_getLhsRhs___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Conv_mkConvGoalFor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_Meta_mkLetFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvar___override(lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Meta_throwTacticEx___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_checkNotAssigned(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_replaceMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withMainContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_extractLetsAddVarInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Conv_getLhs___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_letToHave(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Conv_changeLhs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_liftLets(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__5___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__5___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6_spec__7_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6_spec__7___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6_spec__8___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "(internal error) non-defeq in assignment"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__0___closed__1;
static lean_once_cell_t l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__0___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__1(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__2___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "made no progress"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2___closed__1;
static lean_once_cell_t l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2(lean_object*, lean_object*, lean_object*, size_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2___boxed(lean_object**);
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "extract_lets"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__3___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__3___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(104, 33, 143, 120, 246, 234, 114, 64)}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__3___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__3___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__3(lean_object*, lean_object*, size_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__3___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Conv"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__3_value;
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "extractLets"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__5_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__5_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__5_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__5_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__3_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__5_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__4_value),LEAN_SCALAR_PTR_LITERAL(84, 111, 123, 142, 92, 98, 88, 43)}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__5_value;
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "optConfig"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__6_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__7_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__7_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__7_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__6_value),LEAN_SCALAR_PTR_LITERAL(137, 208, 10, 74, 108, 50, 106, 48)}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__7_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalExtractLets___boxed__const__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + sizeof(size_t)*1, .m_other = 0, .m_tag = 0}, .m_objs = {(lean_object*)(size_t)(0ULL)}};
LEAN_EXPORT const lean_object* l_Lean_Elab_Tactic_Conv_evalExtractLets___boxed__const__1 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalExtractLets___boxed__const__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalExtractLets(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalExtractLets___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6_spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6_spec__8(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6_spec__7_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalExtractLets___regBuiltin_Lean_Elab_Tactic_Conv_evalExtractLets__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalExtractLets___regBuiltin_Lean_Elab_Tactic_Conv_evalExtractLets__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalExtractLets___regBuiltin_Lean_Elab_Tactic_Conv_evalExtractLets__1___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalExtractLets___regBuiltin_Lean_Elab_Tactic_Conv_evalExtractLets__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "evalExtractLets"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalExtractLets___regBuiltin_Lean_Elab_Tactic_Conv_evalExtractLets__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalExtractLets___regBuiltin_Lean_Elab_Tactic_Conv_evalExtractLets__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalExtractLets___regBuiltin_Lean_Elab_Tactic_Conv_evalExtractLets__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalExtractLets___regBuiltin_Lean_Elab_Tactic_Conv_evalExtractLets__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalExtractLets___regBuiltin_Lean_Elab_Tactic_Conv_evalExtractLets__1___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalExtractLets___regBuiltin_Lean_Elab_Tactic_Conv_evalExtractLets__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalExtractLets___regBuiltin_Lean_Elab_Tactic_Conv_evalExtractLets__1___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalExtractLets___regBuiltin_Lean_Elab_Tactic_Conv_evalExtractLets__1___closed__2_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalExtractLets___regBuiltin_Lean_Elab_Tactic_Conv_evalExtractLets__1___closed__2_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalExtractLets___regBuiltin_Lean_Elab_Tactic_Conv_evalExtractLets__1___closed__2_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__3_value),LEAN_SCALAR_PTR_LITERAL(32, 213, 99, 98, 130, 128, 15, 129)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalExtractLets___regBuiltin_Lean_Elab_Tactic_Conv_evalExtractLets__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalExtractLets___regBuiltin_Lean_Elab_Tactic_Conv_evalExtractLets__1___closed__2_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalExtractLets___regBuiltin_Lean_Elab_Tactic_Conv_evalExtractLets__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(165, 244, 234, 55, 146, 240, 50, 65)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalExtractLets___regBuiltin_Lean_Elab_Tactic_Conv_evalExtractLets__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalExtractLets___regBuiltin_Lean_Elab_Tactic_Conv_evalExtractLets__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalExtractLets___regBuiltin_Lean_Elab_Tactic_Conv_evalExtractLets__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalExtractLets___regBuiltin_Lean_Elab_Tactic_Conv_evalExtractLets__1___boxed(lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalLiftLets___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "lift_lets"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalLiftLets___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalLiftLets___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalLiftLets___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalLiftLets___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 227, 82, 255, 128, 171, 101)}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalLiftLets___lam__0___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalLiftLets___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalLiftLets___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalLiftLets___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalLiftLets___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "liftLets"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalLiftLets___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalLiftLets___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalLiftLets___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalLiftLets___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalLiftLets___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalLiftLets___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalLiftLets___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalLiftLets___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalLiftLets___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__3_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalLiftLets___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalLiftLets___closed__1_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalLiftLets___closed__0_value),LEAN_SCALAR_PTR_LITERAL(89, 68, 102, 93, 72, 158, 25, 211)}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalLiftLets___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalLiftLets___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalLiftLets(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalLiftLets___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLiftLets___regBuiltin_Lean_Elab_Tactic_Conv_evalLiftLets__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "evalLiftLets"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLiftLets___regBuiltin_Lean_Elab_Tactic_Conv_evalLiftLets__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLiftLets___regBuiltin_Lean_Elab_Tactic_Conv_evalLiftLets__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLiftLets___regBuiltin_Lean_Elab_Tactic_Conv_evalLiftLets__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLiftLets___regBuiltin_Lean_Elab_Tactic_Conv_evalLiftLets__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLiftLets___regBuiltin_Lean_Elab_Tactic_Conv_evalLiftLets__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalExtractLets___regBuiltin_Lean_Elab_Tactic_Conv_evalExtractLets__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLiftLets___regBuiltin_Lean_Elab_Tactic_Conv_evalLiftLets__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLiftLets___regBuiltin_Lean_Elab_Tactic_Conv_evalLiftLets__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLiftLets___regBuiltin_Lean_Elab_Tactic_Conv_evalLiftLets__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLiftLets___regBuiltin_Lean_Elab_Tactic_Conv_evalLiftLets__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__3_value),LEAN_SCALAR_PTR_LITERAL(32, 213, 99, 98, 130, 128, 15, 129)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLiftLets___regBuiltin_Lean_Elab_Tactic_Conv_evalLiftLets__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLiftLets___regBuiltin_Lean_Elab_Tactic_Conv_evalLiftLets__1___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLiftLets___regBuiltin_Lean_Elab_Tactic_Conv_evalLiftLets__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(123, 101, 191, 197, 167, 255, 65, 77)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLiftLets___regBuiltin_Lean_Elab_Tactic_Conv_evalLiftLets__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLiftLets___regBuiltin_Lean_Elab_Tactic_Conv_evalLiftLets__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLiftLets___regBuiltin_Lean_Elab_Tactic_Conv_evalLiftLets__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLiftLets___regBuiltin_Lean_Elab_Tactic_Conv_evalLiftLets__1___boxed(lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalLetToHave___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "let_to_have"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalLetToHave___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalLetToHave___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalLetToHave___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalLetToHave___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(13, 121, 21, 93, 142, 174, 18, 85)}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalLetToHave___lam__0___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalLetToHave___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalLetToHave___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalLetToHave___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalLetToHave___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "letToHave"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalLetToHave___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalLetToHave___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalLetToHave___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalLetToHave___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalLetToHave___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalLetToHave___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalLetToHave___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalLetToHave___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalLetToHave___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__3_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalLetToHave___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalLetToHave___closed__1_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalLetToHave___closed__0_value),LEAN_SCALAR_PTR_LITERAL(45, 168, 69, 201, 229, 158, 224, 21)}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalLetToHave___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalLetToHave___closed__1_value;
static const lean_closure_object l_Lean_Elab_Tactic_Conv_evalLetToHave___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Conv_evalLetToHave___lam__0___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Conv_evalLetToHave___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalLetToHave___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalLetToHave(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalLetToHave___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLetToHave___regBuiltin_Lean_Elab_Tactic_Conv_evalLetToHave__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "evalLetToHave"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLetToHave___regBuiltin_Lean_Elab_Tactic_Conv_evalLetToHave__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLetToHave___regBuiltin_Lean_Elab_Tactic_Conv_evalLetToHave__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLetToHave___regBuiltin_Lean_Elab_Tactic_Conv_evalLetToHave__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLetToHave___regBuiltin_Lean_Elab_Tactic_Conv_evalLetToHave__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLetToHave___regBuiltin_Lean_Elab_Tactic_Conv_evalLetToHave__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalExtractLets___regBuiltin_Lean_Elab_Tactic_Conv_evalExtractLets__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLetToHave___regBuiltin_Lean_Elab_Tactic_Conv_evalLetToHave__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLetToHave___regBuiltin_Lean_Elab_Tactic_Conv_evalLetToHave__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLetToHave___regBuiltin_Lean_Elab_Tactic_Conv_evalLetToHave__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLetToHave___regBuiltin_Lean_Elab_Tactic_Conv_evalLetToHave__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__3_value),LEAN_SCALAR_PTR_LITERAL(32, 213, 99, 98, 130, 128, 15, 129)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLetToHave___regBuiltin_Lean_Elab_Tactic_Conv_evalLetToHave__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLetToHave___regBuiltin_Lean_Elab_Tactic_Conv_evalLetToHave__1___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLetToHave___regBuiltin_Lean_Elab_Tactic_Conv_evalLetToHave__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(46, 117, 55, 170, 83, 87, 254, 102)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLetToHave___regBuiltin_Lean_Elab_Tactic_Conv_evalLetToHave__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLetToHave___regBuiltin_Lean_Elab_Tactic_Conv_evalLetToHave__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLetToHave___regBuiltin_Lean_Elab_Tactic_Conv_evalLetToHave__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLetToHave___regBuiltin_Lean_Elab_Tactic_Conv_evalLetToHave__1___boxed(lean_object*);
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_1_ = lean_box(0);
v___x_2_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_3_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3_, 0, v___x_2_);
lean_ctor_set(v___x_3_, 1, v___x_1_);
return v___x_3_;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__0___redArg(){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_5_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__0___redArg___closed__0);
v___x_6_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6_, 0, v___x_5_);
return v___x_6_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_7_;
v_res_7_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__0___redArg();
stack->m_obj
 = v_res_7_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__0___redArg___boxed(lean_object* v___y_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__0___redArg();
return v_res_9_;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__0(lean_object* v_00_u03b1_10_, lean_object* v___y_11_, lean_object* v___y_12_, lean_object* v___y_13_, lean_object* v___y_14_, lean_object* v___y_15_, lean_object* v___y_16_, lean_object* v___y_17_, lean_object* v___y_18_){
_start:
{
lean_object* v___x_20_; 
v___x_20_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__0___redArg();
return v___x_20_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_11_ = stack[1].m_obj;
lean_object* v___y_12_ = stack[2].m_obj;
lean_object* v___y_13_ = stack[3].m_obj;
lean_object* v___y_14_ = stack[4].m_obj;
lean_object* v___y_15_ = stack[5].m_obj;
lean_object* v___y_16_ = stack[6].m_obj;
lean_object* v___y_17_ = stack[7].m_obj;
lean_object* v___y_18_ = stack[8].m_obj;
lean_object* v_res_21_;
v_res_21_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__0(lean_box(0), v___y_11_, v___y_12_, v___y_13_, v___y_14_, v___y_15_, v___y_16_, v___y_17_, v___y_18_);
stack->m_obj
 = v_res_21_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__0___boxed(lean_object* v_00_u03b1_22_, lean_object* v___y_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_, lean_object* v___y_28_, lean_object* v___y_29_, lean_object* v___y_30_, lean_object* v___y_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__0(v_00_u03b1_22_, v___y_23_, v___y_24_, v___y_25_, v___y_26_, v___y_27_, v___y_28_, v___y_29_, v___y_30_);
lean_dec(v___y_30_);
lean_dec_ref(v___y_29_);
lean_dec(v___y_28_);
lean_dec_ref(v___y_27_);
lean_dec(v___y_26_);
lean_dec_ref(v___y_25_);
lean_dec(v___y_24_);
lean_dec_ref(v___y_23_);
return v_res_32_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__4___redArg(lean_object* v_mvarId_33_, lean_object* v_x_34_, lean_object* v___y_35_, lean_object* v___y_36_, lean_object* v___y_37_, lean_object* v___y_38_){
_start:
{
lean_object* v___x_40_; 
v___x_40_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_33_, v_x_34_, v___y_35_, v___y_36_, v___y_37_, v___y_38_);
if (lean_obj_tag(v___x_40_) == 0)
{
lean_object* v_a_41_; lean_object* v___x_43_; uint8_t v_isShared_44_; uint8_t v_isSharedCheck_48_; 
v_a_41_ = lean_ctor_get(v___x_40_, 0);
v_isSharedCheck_48_ = !lean_is_exclusive(v___x_40_);
if (v_isSharedCheck_48_ == 0)
{
v___x_43_ = v___x_40_;
v_isShared_44_ = v_isSharedCheck_48_;
goto v_resetjp_42_;
}
else
{
lean_inc(v_a_41_);
lean_dec(v___x_40_);
v___x_43_ = lean_box(0);
v_isShared_44_ = v_isSharedCheck_48_;
goto v_resetjp_42_;
}
v_resetjp_42_:
{
lean_object* v___x_46_; 
if (v_isShared_44_ == 0)
{
v___x_46_ = v___x_43_;
goto v_reusejp_45_;
}
else
{
lean_object* v_reuseFailAlloc_47_; 
v_reuseFailAlloc_47_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_47_, 0, v_a_41_);
v___x_46_ = v_reuseFailAlloc_47_;
goto v_reusejp_45_;
}
v_reusejp_45_:
{
return v___x_46_;
}
}
}
else
{
lean_object* v_a_49_; lean_object* v___x_51_; uint8_t v_isShared_52_; uint8_t v_isSharedCheck_56_; 
v_a_49_ = lean_ctor_get(v___x_40_, 0);
v_isSharedCheck_56_ = !lean_is_exclusive(v___x_40_);
if (v_isSharedCheck_56_ == 0)
{
v___x_51_ = v___x_40_;
v_isShared_52_ = v_isSharedCheck_56_;
goto v_resetjp_50_;
}
else
{
lean_inc(v_a_49_);
lean_dec(v___x_40_);
v___x_51_ = lean_box(0);
v_isShared_52_ = v_isSharedCheck_56_;
goto v_resetjp_50_;
}
v_resetjp_50_:
{
lean_object* v___x_54_; 
if (v_isShared_52_ == 0)
{
v___x_54_ = v___x_51_;
goto v_reusejp_53_;
}
else
{
lean_object* v_reuseFailAlloc_55_; 
v_reuseFailAlloc_55_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_55_, 0, v_a_49_);
v___x_54_ = v_reuseFailAlloc_55_;
goto v_reusejp_53_;
}
v_reusejp_53_:
{
return v___x_54_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_33_ = stack[0].m_obj;
lean_object* v_x_34_ = stack[1].m_obj;
lean_object* v___y_35_ = stack[2].m_obj;
lean_object* v___y_36_ = stack[3].m_obj;
lean_object* v___y_37_ = stack[4].m_obj;
lean_object* v___y_38_ = stack[5].m_obj;
lean_object* v_res_57_;
v_res_57_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__4___redArg(v_mvarId_33_, v_x_34_, v___y_35_, v___y_36_, v___y_37_, v___y_38_);
stack->m_obj
 = v_res_57_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__4___redArg___boxed(lean_object* v_mvarId_58_, lean_object* v_x_59_, lean_object* v___y_60_, lean_object* v___y_61_, lean_object* v___y_62_, lean_object* v___y_63_, lean_object* v___y_64_){
_start:
{
lean_object* v_res_65_; 
v_res_65_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__4___redArg(v_mvarId_58_, v_x_59_, v___y_60_, v___y_61_, v___y_62_, v___y_63_);
lean_dec(v___y_63_);
lean_dec_ref(v___y_62_);
lean_dec(v___y_61_);
lean_dec_ref(v___y_60_);
return v_res_65_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__4(lean_object* v_00_u03b1_66_, lean_object* v_mvarId_67_, lean_object* v_x_68_, lean_object* v___y_69_, lean_object* v___y_70_, lean_object* v___y_71_, lean_object* v___y_72_){
_start:
{
lean_object* v___x_74_; 
v___x_74_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__4___redArg(v_mvarId_67_, v_x_68_, v___y_69_, v___y_70_, v___y_71_, v___y_72_);
return v___x_74_;
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_67_ = stack[1].m_obj;
lean_object* v_x_68_ = stack[2].m_obj;
lean_object* v___y_69_ = stack[3].m_obj;
lean_object* v___y_70_ = stack[4].m_obj;
lean_object* v___y_71_ = stack[5].m_obj;
lean_object* v___y_72_ = stack[6].m_obj;
lean_object* v_res_75_;
v_res_75_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__4(lean_box(0), v_mvarId_67_, v_x_68_, v___y_69_, v___y_70_, v___y_71_, v___y_72_);
stack->m_obj
 = v_res_75_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__4___boxed(lean_object* v_00_u03b1_76_, lean_object* v_mvarId_77_, lean_object* v_x_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_){
_start:
{
lean_object* v_res_84_; 
v_res_84_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__4(v_00_u03b1_76_, v_mvarId_77_, v_x_78_, v___y_79_, v___y_80_, v___y_81_, v___y_82_);
lean_dec(v___y_82_);
lean_dec_ref(v___y_81_);
lean_dec(v___y_80_);
lean_dec_ref(v___y_79_);
return v_res_84_;
}
}
lean_object* l_Lean_Meta_extractLets___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__5___redArg___lam__0(lean_object* v_k_85_, lean_object* v_b_86_, lean_object* v_c_87_, lean_object* v_d_88_, lean_object* v___y_89_, lean_object* v___y_90_, lean_object* v___y_91_, lean_object* v___y_92_){
_start:
{
lean_object* v___x_94_; 
lean_inc(v___y_92_);
lean_inc_ref(v___y_91_);
lean_inc(v___y_90_);
lean_inc_ref(v___y_89_);
v___x_94_ = lean_apply_8(v_k_85_, v_b_86_, v_c_87_, v_d_88_, v___y_89_, v___y_90_, v___y_91_, v___y_92_, lean_box(0));
return v___x_94_;
}
}
LEAN_EXPORT void l_Lean_Meta_extractLets___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__5___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_85_ = stack[0].m_obj;
lean_object* v_b_86_ = stack[1].m_obj;
lean_object* v_c_87_ = stack[2].m_obj;
lean_object* v_d_88_ = stack[3].m_obj;
lean_object* v___y_89_ = stack[4].m_obj;
lean_object* v___y_90_ = stack[5].m_obj;
lean_object* v___y_91_ = stack[6].m_obj;
lean_object* v___y_92_ = stack[7].m_obj;
lean_object* v_res_95_;
v_res_95_ = l_Lean_Meta_extractLets___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__5___redArg___lam__0(v_k_85_, v_b_86_, v_c_87_, v_d_88_, v___y_89_, v___y_90_, v___y_91_, v___y_92_);
stack->m_obj
 = v_res_95_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__5___redArg___lam__0___boxed(lean_object* v_k_96_, lean_object* v_b_97_, lean_object* v_c_98_, lean_object* v_d_99_, lean_object* v___y_100_, lean_object* v___y_101_, lean_object* v___y_102_, lean_object* v___y_103_, lean_object* v___y_104_){
_start:
{
lean_object* v_res_105_; 
v_res_105_ = l_Lean_Meta_extractLets___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__5___redArg___lam__0(v_k_96_, v_b_97_, v_c_98_, v_d_99_, v___y_100_, v___y_101_, v___y_102_, v___y_103_);
lean_dec(v___y_103_);
lean_dec_ref(v___y_102_);
lean_dec(v___y_101_);
lean_dec_ref(v___y_100_);
return v_res_105_;
}
}
lean_object* l_Lean_Meta_extractLets___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__5___redArg(lean_object* v_es_106_, lean_object* v_givenNames_107_, lean_object* v_k_108_, lean_object* v_config_109_, lean_object* v___y_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_){
_start:
{
lean_object* v___f_115_; lean_object* v___x_116_; 
v___f_115_ = lean_alloc_closure((void*)(l_Lean_Meta_extractLets___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__5___redArg___lam__0___boxed), 9, 1);
lean_closure_set(v___f_115_, 0, v_k_108_);
v___x_116_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp(lean_box(0), v_es_106_, v_givenNames_107_, v___f_115_, v_config_109_, v___y_110_, v___y_111_, v___y_112_, v___y_113_);
if (lean_obj_tag(v___x_116_) == 0)
{
lean_object* v_a_117_; lean_object* v___x_119_; uint8_t v_isShared_120_; uint8_t v_isSharedCheck_124_; 
v_a_117_ = lean_ctor_get(v___x_116_, 0);
v_isSharedCheck_124_ = !lean_is_exclusive(v___x_116_);
if (v_isSharedCheck_124_ == 0)
{
v___x_119_ = v___x_116_;
v_isShared_120_ = v_isSharedCheck_124_;
goto v_resetjp_118_;
}
else
{
lean_inc(v_a_117_);
lean_dec(v___x_116_);
v___x_119_ = lean_box(0);
v_isShared_120_ = v_isSharedCheck_124_;
goto v_resetjp_118_;
}
v_resetjp_118_:
{
lean_object* v___x_122_; 
if (v_isShared_120_ == 0)
{
v___x_122_ = v___x_119_;
goto v_reusejp_121_;
}
else
{
lean_object* v_reuseFailAlloc_123_; 
v_reuseFailAlloc_123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_123_, 0, v_a_117_);
v___x_122_ = v_reuseFailAlloc_123_;
goto v_reusejp_121_;
}
v_reusejp_121_:
{
return v___x_122_;
}
}
}
else
{
lean_object* v_a_125_; lean_object* v___x_127_; uint8_t v_isShared_128_; uint8_t v_isSharedCheck_132_; 
v_a_125_ = lean_ctor_get(v___x_116_, 0);
v_isSharedCheck_132_ = !lean_is_exclusive(v___x_116_);
if (v_isSharedCheck_132_ == 0)
{
v___x_127_ = v___x_116_;
v_isShared_128_ = v_isSharedCheck_132_;
goto v_resetjp_126_;
}
else
{
lean_inc(v_a_125_);
lean_dec(v___x_116_);
v___x_127_ = lean_box(0);
v_isShared_128_ = v_isSharedCheck_132_;
goto v_resetjp_126_;
}
v_resetjp_126_:
{
lean_object* v___x_130_; 
if (v_isShared_128_ == 0)
{
v___x_130_ = v___x_127_;
goto v_reusejp_129_;
}
else
{
lean_object* v_reuseFailAlloc_131_; 
v_reuseFailAlloc_131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_131_, 0, v_a_125_);
v___x_130_ = v_reuseFailAlloc_131_;
goto v_reusejp_129_;
}
v_reusejp_129_:
{
return v___x_130_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_extractLets___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_es_106_ = stack[0].m_obj;
lean_object* v_givenNames_107_ = stack[1].m_obj;
lean_object* v_k_108_ = stack[2].m_obj;
lean_object* v_config_109_ = stack[3].m_obj;
lean_object* v___y_110_ = stack[4].m_obj;
lean_object* v___y_111_ = stack[5].m_obj;
lean_object* v___y_112_ = stack[6].m_obj;
lean_object* v___y_113_ = stack[7].m_obj;
lean_object* v_res_133_;
v_res_133_ = l_Lean_Meta_extractLets___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__5___redArg(v_es_106_, v_givenNames_107_, v_k_108_, v_config_109_, v___y_110_, v___y_111_, v___y_112_, v___y_113_);
stack->m_obj
 = v_res_133_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__5___redArg___boxed(lean_object* v_es_134_, lean_object* v_givenNames_135_, lean_object* v_k_136_, lean_object* v_config_137_, lean_object* v___y_138_, lean_object* v___y_139_, lean_object* v___y_140_, lean_object* v___y_141_, lean_object* v___y_142_){
_start:
{
lean_object* v_res_143_; 
v_res_143_ = l_Lean_Meta_extractLets___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__5___redArg(v_es_134_, v_givenNames_135_, v_k_136_, v_config_137_, v___y_138_, v___y_139_, v___y_140_, v___y_141_);
lean_dec(v___y_141_);
lean_dec_ref(v___y_140_);
lean_dec(v___y_139_);
lean_dec_ref(v___y_138_);
lean_dec_ref(v_config_137_);
return v_res_143_;
}
}
lean_object* l_Lean_Meta_extractLets___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__5(lean_object* v_00_u03b1_144_, lean_object* v_es_145_, lean_object* v_givenNames_146_, lean_object* v_k_147_, lean_object* v_config_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_, lean_object* v___y_152_){
_start:
{
lean_object* v___x_154_; 
v___x_154_ = l_Lean_Meta_extractLets___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__5___redArg(v_es_145_, v_givenNames_146_, v_k_147_, v_config_148_, v___y_149_, v___y_150_, v___y_151_, v___y_152_);
return v___x_154_;
}
}
LEAN_EXPORT void l_Lean_Meta_extractLets___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_es_145_ = stack[1].m_obj;
lean_object* v_givenNames_146_ = stack[2].m_obj;
lean_object* v_k_147_ = stack[3].m_obj;
lean_object* v_config_148_ = stack[4].m_obj;
lean_object* v___y_149_ = stack[5].m_obj;
lean_object* v___y_150_ = stack[6].m_obj;
lean_object* v___y_151_ = stack[7].m_obj;
lean_object* v___y_152_ = stack[8].m_obj;
lean_object* v_res_155_;
v_res_155_ = l_Lean_Meta_extractLets___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__5(lean_box(0), v_es_145_, v_givenNames_146_, v_k_147_, v_config_148_, v___y_149_, v___y_150_, v___y_151_, v___y_152_);
stack->m_obj
 = v_res_155_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__5___boxed(lean_object* v_00_u03b1_156_, lean_object* v_es_157_, lean_object* v_givenNames_158_, lean_object* v_k_159_, lean_object* v_config_160_, lean_object* v___y_161_, lean_object* v___y_162_, lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v___y_165_){
_start:
{
lean_object* v_res_166_; 
v_res_166_ = l_Lean_Meta_extractLets___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__5(v_00_u03b1_156_, v_es_157_, v_givenNames_158_, v_k_159_, v_config_160_, v___y_161_, v___y_162_, v___y_163_, v___y_164_);
lean_dec(v___y_164_);
lean_dec_ref(v___y_163_);
lean_dec(v___y_162_);
lean_dec_ref(v___y_161_);
lean_dec_ref(v_config_160_);
return v_res_166_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6_spec__7_spec__8___redArg(lean_object* v_x_167_, lean_object* v_x_168_, lean_object* v_x_169_, lean_object* v_x_170_){
_start:
{
lean_object* v_ks_171_; lean_object* v_vs_172_; lean_object* v___x_174_; uint8_t v_isShared_175_; uint8_t v_isSharedCheck_196_; 
v_ks_171_ = lean_ctor_get(v_x_167_, 0);
v_vs_172_ = lean_ctor_get(v_x_167_, 1);
v_isSharedCheck_196_ = !lean_is_exclusive(v_x_167_);
if (v_isSharedCheck_196_ == 0)
{
v___x_174_ = v_x_167_;
v_isShared_175_ = v_isSharedCheck_196_;
goto v_resetjp_173_;
}
else
{
lean_inc(v_vs_172_);
lean_inc(v_ks_171_);
lean_dec(v_x_167_);
v___x_174_ = lean_box(0);
v_isShared_175_ = v_isSharedCheck_196_;
goto v_resetjp_173_;
}
v_resetjp_173_:
{
lean_object* v___x_176_; uint8_t v___x_177_; 
v___x_176_ = lean_array_get_size(v_ks_171_);
v___x_177_ = lean_nat_dec_lt(v_x_168_, v___x_176_);
if (v___x_177_ == 0)
{
lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_181_; 
lean_dec(v_x_168_);
v___x_178_ = lean_array_push(v_ks_171_, v_x_169_);
v___x_179_ = lean_array_push(v_vs_172_, v_x_170_);
if (v_isShared_175_ == 0)
{
lean_ctor_set(v___x_174_, 1, v___x_179_);
lean_ctor_set(v___x_174_, 0, v___x_178_);
v___x_181_ = v___x_174_;
goto v_reusejp_180_;
}
else
{
lean_object* v_reuseFailAlloc_182_; 
v_reuseFailAlloc_182_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_182_, 0, v___x_178_);
lean_ctor_set(v_reuseFailAlloc_182_, 1, v___x_179_);
v___x_181_ = v_reuseFailAlloc_182_;
goto v_reusejp_180_;
}
v_reusejp_180_:
{
return v___x_181_;
}
}
else
{
lean_object* v_k_x27_183_; uint8_t v___x_184_; 
v_k_x27_183_ = lean_array_fget_borrowed(v_ks_171_, v_x_168_);
v___x_184_ = l_Lean_instBEqMVarId_beq(v_x_169_, v_k_x27_183_);
if (v___x_184_ == 0)
{
lean_object* v___x_186_; 
if (v_isShared_175_ == 0)
{
v___x_186_ = v___x_174_;
goto v_reusejp_185_;
}
else
{
lean_object* v_reuseFailAlloc_190_; 
v_reuseFailAlloc_190_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_190_, 0, v_ks_171_);
lean_ctor_set(v_reuseFailAlloc_190_, 1, v_vs_172_);
v___x_186_ = v_reuseFailAlloc_190_;
goto v_reusejp_185_;
}
v_reusejp_185_:
{
lean_object* v___x_187_; lean_object* v___x_188_; 
v___x_187_ = lean_unsigned_to_nat(1u);
v___x_188_ = lean_nat_add(v_x_168_, v___x_187_);
lean_dec(v_x_168_);
v_x_167_ = v___x_186_;
v_x_168_ = v___x_188_;
goto _start;
}
}
else
{
lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_194_; 
v___x_191_ = lean_array_fset(v_ks_171_, v_x_168_, v_x_169_);
v___x_192_ = lean_array_fset(v_vs_172_, v_x_168_, v_x_170_);
lean_dec(v_x_168_);
if (v_isShared_175_ == 0)
{
lean_ctor_set(v___x_174_, 1, v___x_192_);
lean_ctor_set(v___x_174_, 0, v___x_191_);
v___x_194_ = v___x_174_;
goto v_reusejp_193_;
}
else
{
lean_object* v_reuseFailAlloc_195_; 
v_reuseFailAlloc_195_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_195_, 0, v___x_191_);
lean_ctor_set(v_reuseFailAlloc_195_, 1, v___x_192_);
v___x_194_ = v_reuseFailAlloc_195_;
goto v_reusejp_193_;
}
v_reusejp_193_:
{
return v___x_194_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6_spec__7___redArg(lean_object* v_n_197_, lean_object* v_k_198_, lean_object* v_v_199_){
_start:
{
lean_object* v___x_200_; lean_object* v___x_201_; 
v___x_200_ = lean_unsigned_to_nat(0u);
v___x_201_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6_spec__7_spec__8___redArg(v_n_197_, v___x_200_, v_k_198_, v_v_199_);
return v___x_201_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_202_; 
v___x_202_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_202_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___redArg(lean_object* v_x_203_, size_t v_x_204_, size_t v_x_205_, lean_object* v_x_206_, lean_object* v_x_207_){
_start:
{
if (lean_obj_tag(v_x_203_) == 0)
{
lean_object* v_es_208_; size_t v___x_209_; size_t v___x_210_; lean_object* v_j_211_; lean_object* v___x_212_; uint8_t v___x_213_; 
v_es_208_ = lean_ctor_get(v_x_203_, 0);
v___x_209_ = ((size_t)31ULL);
v___x_210_ = lean_usize_land(v_x_204_, v___x_209_);
v_j_211_ = lean_usize_to_nat(v___x_210_);
v___x_212_ = lean_array_get_size(v_es_208_);
v___x_213_ = lean_nat_dec_lt(v_j_211_, v___x_212_);
if (v___x_213_ == 0)
{
lean_dec(v_j_211_);
lean_dec(v_x_207_);
lean_dec(v_x_206_);
return v_x_203_;
}
else
{
lean_object* v___x_215_; uint8_t v_isShared_216_; uint8_t v_isSharedCheck_252_; 
lean_inc_ref(v_es_208_);
v_isSharedCheck_252_ = !lean_is_exclusive(v_x_203_);
if (v_isSharedCheck_252_ == 0)
{
lean_object* v_unused_253_; 
v_unused_253_ = lean_ctor_get(v_x_203_, 0);
lean_dec(v_unused_253_);
v___x_215_ = v_x_203_;
v_isShared_216_ = v_isSharedCheck_252_;
goto v_resetjp_214_;
}
else
{
lean_dec(v_x_203_);
v___x_215_ = lean_box(0);
v_isShared_216_ = v_isSharedCheck_252_;
goto v_resetjp_214_;
}
v_resetjp_214_:
{
lean_object* v_v_217_; lean_object* v___x_218_; lean_object* v_xs_x27_219_; lean_object* v___y_221_; 
v_v_217_ = lean_array_fget(v_es_208_, v_j_211_);
v___x_218_ = lean_box(0);
v_xs_x27_219_ = lean_array_fset(v_es_208_, v_j_211_, v___x_218_);
switch(lean_obj_tag(v_v_217_))
{
case 0:
{
lean_object* v_key_226_; lean_object* v_val_227_; lean_object* v___x_229_; uint8_t v_isShared_230_; uint8_t v_isSharedCheck_237_; 
v_key_226_ = lean_ctor_get(v_v_217_, 0);
v_val_227_ = lean_ctor_get(v_v_217_, 1);
v_isSharedCheck_237_ = !lean_is_exclusive(v_v_217_);
if (v_isSharedCheck_237_ == 0)
{
v___x_229_ = v_v_217_;
v_isShared_230_ = v_isSharedCheck_237_;
goto v_resetjp_228_;
}
else
{
lean_inc(v_val_227_);
lean_inc(v_key_226_);
lean_dec(v_v_217_);
v___x_229_ = lean_box(0);
v_isShared_230_ = v_isSharedCheck_237_;
goto v_resetjp_228_;
}
v_resetjp_228_:
{
uint8_t v___x_231_; 
v___x_231_ = l_Lean_instBEqMVarId_beq(v_x_206_, v_key_226_);
if (v___x_231_ == 0)
{
lean_object* v___x_232_; lean_object* v___x_233_; 
lean_del_object(v___x_229_);
v___x_232_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_226_, v_val_227_, v_x_206_, v_x_207_);
v___x_233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_233_, 0, v___x_232_);
v___y_221_ = v___x_233_;
goto v___jp_220_;
}
else
{
lean_object* v___x_235_; 
lean_dec(v_val_227_);
lean_dec(v_key_226_);
if (v_isShared_230_ == 0)
{
lean_ctor_set(v___x_229_, 1, v_x_207_);
lean_ctor_set(v___x_229_, 0, v_x_206_);
v___x_235_ = v___x_229_;
goto v_reusejp_234_;
}
else
{
lean_object* v_reuseFailAlloc_236_; 
v_reuseFailAlloc_236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_236_, 0, v_x_206_);
lean_ctor_set(v_reuseFailAlloc_236_, 1, v_x_207_);
v___x_235_ = v_reuseFailAlloc_236_;
goto v_reusejp_234_;
}
v_reusejp_234_:
{
v___y_221_ = v___x_235_;
goto v___jp_220_;
}
}
}
}
case 1:
{
lean_object* v_node_238_; lean_object* v___x_240_; uint8_t v_isShared_241_; uint8_t v_isSharedCheck_250_; 
v_node_238_ = lean_ctor_get(v_v_217_, 0);
v_isSharedCheck_250_ = !lean_is_exclusive(v_v_217_);
if (v_isSharedCheck_250_ == 0)
{
v___x_240_ = v_v_217_;
v_isShared_241_ = v_isSharedCheck_250_;
goto v_resetjp_239_;
}
else
{
lean_inc(v_node_238_);
lean_dec(v_v_217_);
v___x_240_ = lean_box(0);
v_isShared_241_ = v_isSharedCheck_250_;
goto v_resetjp_239_;
}
v_resetjp_239_:
{
size_t v___x_242_; size_t v___x_243_; size_t v___x_244_; size_t v___x_245_; lean_object* v___x_246_; lean_object* v___x_248_; 
v___x_242_ = ((size_t)5ULL);
v___x_243_ = lean_usize_shift_right(v_x_204_, v___x_242_);
v___x_244_ = ((size_t)1ULL);
v___x_245_ = lean_usize_add(v_x_205_, v___x_244_);
v___x_246_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___redArg(v_node_238_, v___x_243_, v___x_245_, v_x_206_, v_x_207_);
if (v_isShared_241_ == 0)
{
lean_ctor_set(v___x_240_, 0, v___x_246_);
v___x_248_ = v___x_240_;
goto v_reusejp_247_;
}
else
{
lean_object* v_reuseFailAlloc_249_; 
v_reuseFailAlloc_249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_249_, 0, v___x_246_);
v___x_248_ = v_reuseFailAlloc_249_;
goto v_reusejp_247_;
}
v_reusejp_247_:
{
v___y_221_ = v___x_248_;
goto v___jp_220_;
}
}
}
default: 
{
lean_object* v___x_251_; 
v___x_251_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_251_, 0, v_x_206_);
lean_ctor_set(v___x_251_, 1, v_x_207_);
v___y_221_ = v___x_251_;
goto v___jp_220_;
}
}
v___jp_220_:
{
lean_object* v___x_222_; lean_object* v___x_224_; 
v___x_222_ = lean_array_fset(v_xs_x27_219_, v_j_211_, v___y_221_);
lean_dec(v_j_211_);
if (v_isShared_216_ == 0)
{
lean_ctor_set(v___x_215_, 0, v___x_222_);
v___x_224_ = v___x_215_;
goto v_reusejp_223_;
}
else
{
lean_object* v_reuseFailAlloc_225_; 
v_reuseFailAlloc_225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_225_, 0, v___x_222_);
v___x_224_ = v_reuseFailAlloc_225_;
goto v_reusejp_223_;
}
v_reusejp_223_:
{
return v___x_224_;
}
}
}
}
}
else
{
lean_object* v_ks_254_; lean_object* v_vs_255_; lean_object* v___x_257_; uint8_t v_isShared_258_; uint8_t v_isSharedCheck_273_; 
v_ks_254_ = lean_ctor_get(v_x_203_, 0);
v_vs_255_ = lean_ctor_get(v_x_203_, 1);
v_isSharedCheck_273_ = !lean_is_exclusive(v_x_203_);
if (v_isSharedCheck_273_ == 0)
{
v___x_257_ = v_x_203_;
v_isShared_258_ = v_isSharedCheck_273_;
goto v_resetjp_256_;
}
else
{
lean_inc(v_vs_255_);
lean_inc(v_ks_254_);
lean_dec(v_x_203_);
v___x_257_ = lean_box(0);
v_isShared_258_ = v_isSharedCheck_273_;
goto v_resetjp_256_;
}
v_resetjp_256_:
{
lean_object* v___x_260_; 
if (v_isShared_258_ == 0)
{
v___x_260_ = v___x_257_;
goto v_reusejp_259_;
}
else
{
lean_object* v_reuseFailAlloc_272_; 
v_reuseFailAlloc_272_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_272_, 0, v_ks_254_);
lean_ctor_set(v_reuseFailAlloc_272_, 1, v_vs_255_);
v___x_260_ = v_reuseFailAlloc_272_;
goto v_reusejp_259_;
}
v_reusejp_259_:
{
lean_object* v_newNode_261_; size_t v___x_262_; uint8_t v___x_263_; 
v_newNode_261_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6_spec__7___redArg(v___x_260_, v_x_206_, v_x_207_);
v___x_262_ = ((size_t)7ULL);
v___x_263_ = lean_usize_dec_le(v___x_262_, v_x_205_);
if (v___x_263_ == 0)
{
lean_object* v___x_264_; lean_object* v___x_265_; uint8_t v___x_266_; 
v___x_264_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_261_);
v___x_265_ = lean_unsigned_to_nat(4u);
v___x_266_ = lean_nat_dec_lt(v___x_264_, v___x_265_);
lean_dec(v___x_264_);
if (v___x_266_ == 0)
{
lean_object* v_ks_267_; lean_object* v_vs_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; 
v_ks_267_ = lean_ctor_get(v_newNode_261_, 0);
lean_inc_ref(v_ks_267_);
v_vs_268_ = lean_ctor_get(v_newNode_261_, 1);
lean_inc_ref(v_vs_268_);
lean_dec_ref(v_newNode_261_);
v___x_269_ = lean_unsigned_to_nat(0u);
v___x_270_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___redArg___closed__0);
v___x_271_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6_spec__8___redArg(v_x_205_, v_ks_267_, v_vs_268_, v___x_269_, v___x_270_);
lean_dec_ref(v_vs_268_);
lean_dec_ref(v_ks_267_);
return v___x_271_;
}
else
{
return v_newNode_261_;
}
}
else
{
return v_newNode_261_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_203_ = stack[0].m_obj;
size_t v_x_204_ = stack[1].m_num;
size_t v_x_205_ = stack[2].m_num;
lean_object* v_x_206_ = stack[3].m_obj;
lean_object* v_x_207_ = stack[4].m_obj;
lean_object* v_res_274_;
v_res_274_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___redArg(v_x_203_, v_x_204_, v_x_205_, v_x_206_, v_x_207_);
stack->m_obj
 = v_res_274_;
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6_spec__8___redArg(size_t v_depth_275_, lean_object* v_keys_276_, lean_object* v_vals_277_, lean_object* v_i_278_, lean_object* v_entries_279_){
_start:
{
lean_object* v___x_280_; uint8_t v___x_281_; 
v___x_280_ = lean_array_get_size(v_keys_276_);
v___x_281_ = lean_nat_dec_lt(v_i_278_, v___x_280_);
if (v___x_281_ == 0)
{
lean_dec(v_i_278_);
return v_entries_279_;
}
else
{
lean_object* v_k_282_; lean_object* v_v_283_; uint64_t v___x_284_; size_t v_h_285_; size_t v___x_286_; lean_object* v___x_287_; size_t v___x_288_; size_t v___x_289_; size_t v___x_290_; size_t v_h_291_; lean_object* v___x_292_; lean_object* v___x_293_; 
v_k_282_ = lean_array_fget_borrowed(v_keys_276_, v_i_278_);
v_v_283_ = lean_array_fget_borrowed(v_vals_277_, v_i_278_);
v___x_284_ = l_Lean_instHashableMVarId_hash(v_k_282_);
v_h_285_ = lean_uint64_to_usize(v___x_284_);
v___x_286_ = ((size_t)5ULL);
v___x_287_ = lean_unsigned_to_nat(1u);
v___x_288_ = ((size_t)1ULL);
v___x_289_ = lean_usize_sub(v_depth_275_, v___x_288_);
v___x_290_ = lean_usize_mul(v___x_286_, v___x_289_);
v_h_291_ = lean_usize_shift_right(v_h_285_, v___x_290_);
v___x_292_ = lean_nat_add(v_i_278_, v___x_287_);
lean_dec(v_i_278_);
lean_inc(v_v_283_);
lean_inc(v_k_282_);
v___x_293_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___redArg(v_entries_279_, v_h_291_, v_depth_275_, v_k_282_, v_v_283_);
v_i_278_ = v___x_292_;
v_entries_279_ = v___x_293_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6_spec__8___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_depth_275_ = stack[0].m_num;
lean_object* v_keys_276_ = stack[1].m_obj;
lean_object* v_vals_277_ = stack[2].m_obj;
lean_object* v_i_278_ = stack[3].m_obj;
lean_object* v_entries_279_ = stack[4].m_obj;
lean_object* v_res_295_;
v_res_295_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6_spec__8___redArg(v_depth_275_, v_keys_276_, v_vals_277_, v_i_278_, v_entries_279_);
stack->m_obj
 = v_res_295_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6_spec__8___redArg___boxed(lean_object* v_depth_296_, lean_object* v_keys_297_, lean_object* v_vals_298_, lean_object* v_i_299_, lean_object* v_entries_300_){
_start:
{
size_t v_depth_boxed_301_; lean_object* v_res_302_; 
v_depth_boxed_301_ = lean_unbox_usize(v_depth_296_);
lean_dec(v_depth_296_);
v_res_302_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6_spec__8___redArg(v_depth_boxed_301_, v_keys_297_, v_vals_298_, v_i_299_, v_entries_300_);
lean_dec_ref(v_vals_298_);
lean_dec_ref(v_keys_297_);
return v_res_302_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___redArg___boxed(lean_object* v_x_303_, lean_object* v_x_304_, lean_object* v_x_305_, lean_object* v_x_306_, lean_object* v_x_307_){
_start:
{
size_t v_x_5255__boxed_308_; size_t v_x_5256__boxed_309_; lean_object* v_res_310_; 
v_x_5255__boxed_308_ = lean_unbox_usize(v_x_304_);
lean_dec(v_x_304_);
v_x_5256__boxed_309_ = lean_unbox_usize(v_x_305_);
lean_dec(v_x_305_);
v_res_310_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___redArg(v_x_303_, v_x_5255__boxed_308_, v_x_5256__boxed_309_, v_x_306_, v_x_307_);
return v_res_310_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3___redArg(lean_object* v_x_311_, lean_object* v_x_312_, lean_object* v_x_313_){
_start:
{
uint64_t v___x_314_; size_t v___x_315_; size_t v___x_316_; lean_object* v___x_317_; 
v___x_314_ = l_Lean_instHashableMVarId_hash(v_x_312_);
v___x_315_ = lean_uint64_to_usize(v___x_314_);
v___x_316_ = ((size_t)1ULL);
v___x_317_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___redArg(v_x_311_, v___x_315_, v___x_316_, v_x_312_, v_x_313_);
return v___x_317_;
}
}
lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3___redArg(lean_object* v_mvarId_318_, lean_object* v_val_319_, lean_object* v___y_320_){
_start:
{
lean_object* v___x_322_; lean_object* v_mctx_323_; lean_object* v_cache_324_; lean_object* v_zetaDeltaFVarIds_325_; lean_object* v_postponed_326_; lean_object* v_diag_327_; lean_object* v___x_329_; uint8_t v_isShared_330_; uint8_t v_isSharedCheck_357_; 
v___x_322_ = lean_st_ref_take(v___y_320_);
v_mctx_323_ = lean_ctor_get(v___x_322_, 0);
v_cache_324_ = lean_ctor_get(v___x_322_, 1);
v_zetaDeltaFVarIds_325_ = lean_ctor_get(v___x_322_, 2);
v_postponed_326_ = lean_ctor_get(v___x_322_, 3);
v_diag_327_ = lean_ctor_get(v___x_322_, 4);
v_isSharedCheck_357_ = !lean_is_exclusive(v___x_322_);
if (v_isSharedCheck_357_ == 0)
{
v___x_329_ = v___x_322_;
v_isShared_330_ = v_isSharedCheck_357_;
goto v_resetjp_328_;
}
else
{
lean_inc(v_diag_327_);
lean_inc(v_postponed_326_);
lean_inc(v_zetaDeltaFVarIds_325_);
lean_inc(v_cache_324_);
lean_inc(v_mctx_323_);
lean_dec(v___x_322_);
v___x_329_ = lean_box(0);
v_isShared_330_ = v_isSharedCheck_357_;
goto v_resetjp_328_;
}
v_resetjp_328_:
{
lean_object* v_depth_331_; lean_object* v_levelAssignDepth_332_; lean_object* v_lmvarCounter_333_; lean_object* v_mvarCounter_334_; lean_object* v_lDecls_335_; lean_object* v_decls_336_; lean_object* v_userNames_337_; lean_object* v_lAssignment_338_; lean_object* v_eAssignment_339_; lean_object* v_dAssignment_340_; lean_object* v_instanceTypedMVars_341_; lean_object* v_synthNormMemo_342_; lean_object* v___x_344_; uint8_t v_isShared_345_; uint8_t v_isSharedCheck_356_; 
v_depth_331_ = lean_ctor_get(v_mctx_323_, 0);
v_levelAssignDepth_332_ = lean_ctor_get(v_mctx_323_, 1);
v_lmvarCounter_333_ = lean_ctor_get(v_mctx_323_, 2);
v_mvarCounter_334_ = lean_ctor_get(v_mctx_323_, 3);
v_lDecls_335_ = lean_ctor_get(v_mctx_323_, 4);
v_decls_336_ = lean_ctor_get(v_mctx_323_, 5);
v_userNames_337_ = lean_ctor_get(v_mctx_323_, 6);
v_lAssignment_338_ = lean_ctor_get(v_mctx_323_, 7);
v_eAssignment_339_ = lean_ctor_get(v_mctx_323_, 8);
v_dAssignment_340_ = lean_ctor_get(v_mctx_323_, 9);
v_instanceTypedMVars_341_ = lean_ctor_get(v_mctx_323_, 10);
v_synthNormMemo_342_ = lean_ctor_get(v_mctx_323_, 11);
v_isSharedCheck_356_ = !lean_is_exclusive(v_mctx_323_);
if (v_isSharedCheck_356_ == 0)
{
v___x_344_ = v_mctx_323_;
v_isShared_345_ = v_isSharedCheck_356_;
goto v_resetjp_343_;
}
else
{
lean_inc(v_synthNormMemo_342_);
lean_inc(v_instanceTypedMVars_341_);
lean_inc(v_dAssignment_340_);
lean_inc(v_eAssignment_339_);
lean_inc(v_lAssignment_338_);
lean_inc(v_userNames_337_);
lean_inc(v_decls_336_);
lean_inc(v_lDecls_335_);
lean_inc(v_mvarCounter_334_);
lean_inc(v_lmvarCounter_333_);
lean_inc(v_levelAssignDepth_332_);
lean_inc(v_depth_331_);
lean_dec(v_mctx_323_);
v___x_344_ = lean_box(0);
v_isShared_345_ = v_isSharedCheck_356_;
goto v_resetjp_343_;
}
v_resetjp_343_:
{
lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_349_; 
v___x_346_ = lean_box(0);
v___x_347_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3___redArg(v_eAssignment_339_, v_mvarId_318_, v_val_319_);
if (v_isShared_345_ == 0)
{
lean_ctor_set(v___x_344_, 8, v___x_347_);
v___x_349_ = v___x_344_;
goto v_reusejp_348_;
}
else
{
lean_object* v_reuseFailAlloc_355_; 
v_reuseFailAlloc_355_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_355_, 0, v_depth_331_);
lean_ctor_set(v_reuseFailAlloc_355_, 1, v_levelAssignDepth_332_);
lean_ctor_set(v_reuseFailAlloc_355_, 2, v_lmvarCounter_333_);
lean_ctor_set(v_reuseFailAlloc_355_, 3, v_mvarCounter_334_);
lean_ctor_set(v_reuseFailAlloc_355_, 4, v_lDecls_335_);
lean_ctor_set(v_reuseFailAlloc_355_, 5, v_decls_336_);
lean_ctor_set(v_reuseFailAlloc_355_, 6, v_userNames_337_);
lean_ctor_set(v_reuseFailAlloc_355_, 7, v_lAssignment_338_);
lean_ctor_set(v_reuseFailAlloc_355_, 8, v___x_347_);
lean_ctor_set(v_reuseFailAlloc_355_, 9, v_dAssignment_340_);
lean_ctor_set(v_reuseFailAlloc_355_, 10, v_instanceTypedMVars_341_);
lean_ctor_set(v_reuseFailAlloc_355_, 11, v_synthNormMemo_342_);
v___x_349_ = v_reuseFailAlloc_355_;
goto v_reusejp_348_;
}
v_reusejp_348_:
{
lean_object* v___x_351_; 
if (v_isShared_330_ == 0)
{
lean_ctor_set(v___x_329_, 0, v___x_349_);
v___x_351_ = v___x_329_;
goto v_reusejp_350_;
}
else
{
lean_object* v_reuseFailAlloc_354_; 
v_reuseFailAlloc_354_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_354_, 0, v___x_349_);
lean_ctor_set(v_reuseFailAlloc_354_, 1, v_cache_324_);
lean_ctor_set(v_reuseFailAlloc_354_, 2, v_zetaDeltaFVarIds_325_);
lean_ctor_set(v_reuseFailAlloc_354_, 3, v_postponed_326_);
lean_ctor_set(v_reuseFailAlloc_354_, 4, v_diag_327_);
v___x_351_ = v_reuseFailAlloc_354_;
goto v_reusejp_350_;
}
v_reusejp_350_:
{
lean_object* v___x_352_; lean_object* v___x_353_; 
v___x_352_ = lean_st_ref_put(v___y_320_, v___x_351_);
v___x_353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_353_, 0, v___x_346_);
return v___x_353_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_318_ = stack[0].m_obj;
lean_object* v_val_319_ = stack[1].m_obj;
lean_object* v___y_320_ = stack[2].m_obj;
lean_object* v_res_358_;
v_res_358_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3___redArg(v_mvarId_318_, v_val_319_, v___y_320_);
stack->m_obj
 = v_res_358_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3___redArg___boxed(lean_object* v_mvarId_359_, lean_object* v_val_360_, lean_object* v___y_361_, lean_object* v___y_362_){
_start:
{
lean_object* v_res_363_; 
v_res_363_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3___redArg(v_mvarId_359_, v_val_360_, v___y_361_);
lean_dec(v___y_361_);
return v_res_363_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__0___closed__1(void){
_start:
{
lean_object* v___x_365_; lean_object* v___x_366_; 
v___x_365_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__0___closed__0));
v___x_366_ = l_Lean_stringToMessageData(v___x_365_);
return v___x_366_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__0___closed__2(void){
_start:
{
lean_object* v___x_367_; lean_object* v___x_368_; 
v___x_367_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__0___closed__1, &l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__0___closed__1);
v___x_368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_368_, 0, v___x_367_);
return v___x_368_;
}
}
lean_object* l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__0(lean_object* v___x_369_, lean_object* v_a_370_, lean_object* v___x_371_, lean_object* v_a_372_, lean_object* v_mvar_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_){
_start:
{
lean_object* v___x_379_; 
lean_inc_ref(v_a_370_);
v___x_379_ = l_Lean_Meta_isExprDefEq(v___x_369_, v_a_370_, v___y_374_, v___y_375_, v___y_376_, v___y_377_);
if (lean_obj_tag(v___x_379_) == 0)
{
lean_object* v_a_380_; uint8_t v___x_381_; 
v_a_380_ = lean_ctor_get(v___x_379_, 0);
lean_inc(v_a_380_);
lean_dec_ref_known(v___x_379_, 1);
v___x_381_ = lean_unbox(v_a_380_);
lean_dec(v_a_380_);
if (v___x_381_ == 0)
{
lean_object* v___x_382_; lean_object* v___x_383_; 
v___x_382_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__0___closed__2, &l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__0___closed__2_once, _init_l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__0___closed__2);
v___x_383_ = l_Lean_Meta_throwTacticEx___redArg(v___x_371_, v_a_372_, v___x_382_, v___y_374_, v___y_375_, v___y_376_, v___y_377_);
if (lean_obj_tag(v___x_383_) == 0)
{
lean_object* v___x_384_; 
lean_dec_ref_known(v___x_383_, 1);
v___x_384_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3___redArg(v_mvar_373_, v_a_370_, v___y_375_);
return v___x_384_;
}
else
{
lean_dec(v_mvar_373_);
lean_dec_ref(v_a_370_);
return v___x_383_;
}
}
else
{
lean_object* v___x_385_; 
lean_dec(v_a_372_);
lean_dec(v___x_371_);
v___x_385_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3___redArg(v_mvar_373_, v_a_370_, v___y_375_);
return v___x_385_;
}
}
else
{
lean_object* v_a_386_; lean_object* v___x_388_; uint8_t v_isShared_389_; uint8_t v_isSharedCheck_393_; 
lean_dec(v_mvar_373_);
lean_dec(v_a_372_);
lean_dec(v___x_371_);
lean_dec_ref(v_a_370_);
v_a_386_ = lean_ctor_get(v___x_379_, 0);
v_isSharedCheck_393_ = !lean_is_exclusive(v___x_379_);
if (v_isSharedCheck_393_ == 0)
{
v___x_388_ = v___x_379_;
v_isShared_389_ = v_isSharedCheck_393_;
goto v_resetjp_387_;
}
else
{
lean_inc(v_a_386_);
lean_dec(v___x_379_);
v___x_388_ = lean_box(0);
v_isShared_389_ = v_isSharedCheck_393_;
goto v_resetjp_387_;
}
v_resetjp_387_:
{
lean_object* v___x_391_; 
if (v_isShared_389_ == 0)
{
v___x_391_ = v___x_388_;
goto v_reusejp_390_;
}
else
{
lean_object* v_reuseFailAlloc_392_; 
v_reuseFailAlloc_392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_392_, 0, v_a_386_);
v___x_391_ = v_reuseFailAlloc_392_;
goto v_reusejp_390_;
}
v_reusejp_390_:
{
return v___x_391_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_369_ = stack[0].m_obj;
lean_object* v_a_370_ = stack[1].m_obj;
lean_object* v___x_371_ = stack[2].m_obj;
lean_object* v_a_372_ = stack[3].m_obj;
lean_object* v_mvar_373_ = stack[4].m_obj;
lean_object* v___y_374_ = stack[5].m_obj;
lean_object* v___y_375_ = stack[6].m_obj;
lean_object* v___y_376_ = stack[7].m_obj;
lean_object* v___y_377_ = stack[8].m_obj;
lean_object* v_res_394_;
v_res_394_ = l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__0(v___x_369_, v_a_370_, v___x_371_, v_a_372_, v_mvar_373_, v___y_374_, v___y_375_, v___y_376_, v___y_377_);
stack->m_obj
 = v_res_394_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__0___boxed(lean_object* v___x_395_, lean_object* v_a_396_, lean_object* v___x_397_, lean_object* v_a_398_, lean_object* v_mvar_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_){
_start:
{
lean_object* v_res_405_; 
v_res_405_ = l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__0(v___x_395_, v_a_396_, v___x_397_, v_a_398_, v_mvar_399_, v___y_400_, v___y_401_, v___y_402_, v___y_403_);
lean_dec(v___y_403_);
lean_dec_ref(v___y_402_);
lean_dec(v___y_401_);
lean_dec_ref(v___y_400_);
return v_res_405_;
}
}
lean_object* l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__1(lean_object* v___x_406_, uint8_t v___x_407_, uint8_t v___x_408_, lean_object* v___x_409_, lean_object* v_a_410_, lean_object* v_mvar_411_, lean_object* v_e_412_, lean_object* v___y_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_){
_start:
{
uint8_t v___x_418_; lean_object* v___x_419_; 
v___x_418_ = 1;
v___x_419_ = l_Lean_Meta_mkLetFVars(v___x_406_, v_e_412_, v___x_407_, v___x_408_, v___x_418_, v___y_413_, v___y_414_, v___y_415_, v___y_416_);
if (lean_obj_tag(v___x_419_) == 0)
{
lean_object* v_a_420_; lean_object* v___x_421_; lean_object* v___f_422_; lean_object* v___x_423_; 
v_a_420_ = lean_ctor_get(v___x_419_, 0);
lean_inc(v_a_420_);
lean_dec_ref_known(v___x_419_, 1);
lean_inc_n(v_mvar_411_, 2);
v___x_421_ = l_Lean_Expr_mvar___override(v_mvar_411_);
v___f_422_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__0___boxed), 10, 5);
lean_closure_set(v___f_422_, 0, v___x_421_);
lean_closure_set(v___f_422_, 1, v_a_420_);
lean_closure_set(v___f_422_, 2, v___x_409_);
lean_closure_set(v___f_422_, 3, v_a_410_);
lean_closure_set(v___f_422_, 4, v_mvar_411_);
v___x_423_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__4___redArg(v_mvar_411_, v___f_422_, v___y_413_, v___y_414_, v___y_415_, v___y_416_);
return v___x_423_;
}
else
{
lean_object* v_a_424_; lean_object* v___x_426_; uint8_t v_isShared_427_; uint8_t v_isSharedCheck_431_; 
lean_dec(v_mvar_411_);
lean_dec(v_a_410_);
lean_dec(v___x_409_);
v_a_424_ = lean_ctor_get(v___x_419_, 0);
v_isSharedCheck_431_ = !lean_is_exclusive(v___x_419_);
if (v_isSharedCheck_431_ == 0)
{
v___x_426_ = v___x_419_;
v_isShared_427_ = v_isSharedCheck_431_;
goto v_resetjp_425_;
}
else
{
lean_inc(v_a_424_);
lean_dec(v___x_419_);
v___x_426_ = lean_box(0);
v_isShared_427_ = v_isSharedCheck_431_;
goto v_resetjp_425_;
}
v_resetjp_425_:
{
lean_object* v___x_429_; 
if (v_isShared_427_ == 0)
{
v___x_429_ = v___x_426_;
goto v_reusejp_428_;
}
else
{
lean_object* v_reuseFailAlloc_430_; 
v_reuseFailAlloc_430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_430_, 0, v_a_424_);
v___x_429_ = v_reuseFailAlloc_430_;
goto v_reusejp_428_;
}
v_reusejp_428_:
{
return v___x_429_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_406_ = stack[0].m_obj;
uint8_t v___x_407_ = stack[1].m_num;
uint8_t v___x_408_ = stack[2].m_num;
lean_object* v___x_409_ = stack[3].m_obj;
lean_object* v_a_410_ = stack[4].m_obj;
lean_object* v_mvar_411_ = stack[5].m_obj;
lean_object* v_e_412_ = stack[6].m_obj;
lean_object* v___y_413_ = stack[7].m_obj;
lean_object* v___y_414_ = stack[8].m_obj;
lean_object* v___y_415_ = stack[9].m_obj;
lean_object* v___y_416_ = stack[10].m_obj;
lean_object* v_res_432_;
v_res_432_ = l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__1(v___x_406_, v___x_407_, v___x_408_, v___x_409_, v_a_410_, v_mvar_411_, v_e_412_, v___y_413_, v___y_414_, v___y_415_, v___y_416_);
stack->m_obj
 = v_res_432_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__1___boxed(lean_object* v___x_433_, lean_object* v___x_434_, lean_object* v___x_435_, lean_object* v___x_436_, lean_object* v_a_437_, lean_object* v_mvar_438_, lean_object* v_e_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_){
_start:
{
uint8_t v___x_5691__boxed_445_; uint8_t v___x_5692__boxed_446_; lean_object* v_res_447_; 
v___x_5691__boxed_445_ = lean_unbox(v___x_434_);
v___x_5692__boxed_446_ = lean_unbox(v___x_435_);
v_res_447_ = l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__1(v___x_433_, v___x_5691__boxed_445_, v___x_5692__boxed_446_, v___x_436_, v_a_437_, v_mvar_438_, v_e_439_, v___y_440_, v___y_441_, v___y_442_, v___y_443_);
lean_dec(v___y_443_);
lean_dec_ref(v___y_442_);
lean_dec(v___y_441_);
lean_dec_ref(v___y_440_);
lean_dec_ref(v___x_433_);
return v_res_447_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__2(size_t v_sz_448_, size_t v_i_449_, lean_object* v_bs_450_){
_start:
{
uint8_t v___x_451_; 
v___x_451_ = lean_usize_dec_lt(v_i_449_, v_sz_448_);
if (v___x_451_ == 0)
{
return v_bs_450_;
}
else
{
lean_object* v_v_452_; lean_object* v___x_453_; lean_object* v_bs_x27_454_; lean_object* v___x_455_; size_t v___x_456_; size_t v___x_457_; lean_object* v___x_458_; 
v_v_452_ = lean_array_uget(v_bs_450_, v_i_449_);
v___x_453_ = lean_unsigned_to_nat(0u);
v_bs_x27_454_ = lean_array_uset(v_bs_450_, v_i_449_, v___x_453_);
v___x_455_ = l_Lean_Expr_fvar___override(v_v_452_);
v___x_456_ = ((size_t)1ULL);
v___x_457_ = lean_usize_add(v_i_449_, v___x_456_);
v___x_458_ = lean_array_uset(v_bs_x27_454_, v_i_449_, v___x_455_);
v_i_449_ = v___x_457_;
v_bs_450_ = v___x_458_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__2_0interp(lean_interpreter_value* stack)
{
size_t v_sz_448_ = stack[0].m_num;
size_t v_i_449_ = stack[1].m_num;
lean_object* v_bs_450_ = stack[2].m_obj;
lean_object* v_res_460_;
v_res_460_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__2(v_sz_448_, v_i_449_, v_bs_450_);
stack->m_obj
 = v_res_460_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__2___boxed(lean_object* v_sz_461_, lean_object* v_i_462_, lean_object* v_bs_463_){
_start:
{
size_t v_sz_boxed_464_; size_t v_i_boxed_465_; lean_object* v_res_466_; 
v_sz_boxed_464_ = lean_unbox_usize(v_sz_461_);
lean_dec(v_sz_461_);
v_i_boxed_465_ = lean_unbox_usize(v_i_462_);
lean_dec(v_i_462_);
v_res_466_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__2(v_sz_boxed_464_, v_i_boxed_465_, v_bs_463_);
return v_res_466_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2___closed__1(void){
_start:
{
lean_object* v___x_468_; lean_object* v___x_469_; 
v___x_468_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2___closed__0));
v___x_469_ = l_Lean_stringToMessageData(v___x_468_);
return v___x_469_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2___closed__2(void){
_start:
{
lean_object* v___x_470_; lean_object* v___x_471_; 
v___x_470_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2___closed__1, &l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2___closed__1_once, _init_l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2___closed__1);
v___x_471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_471_, 0, v___x_470_);
return v___x_471_;
}
}
lean_object* l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2(lean_object* v___x_472_, lean_object* v___x_473_, lean_object* v_a_474_, size_t v___x_475_, uint8_t v___x_476_, uint8_t v___x_477_, lean_object* v___x_478_, lean_object* v_snd_479_, lean_object* v_fst_480_, lean_object* v_fvarIds_481_, lean_object* v_es_482_, lean_object* v_x_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_){
_start:
{
lean_object* v___x_489_; lean_object* v___x_552_; uint8_t v___x_553_; 
v___x_489_ = lean_array_get_borrowed(v___x_472_, v_es_482_, v___x_473_);
v___x_552_ = lean_array_get_size(v_fvarIds_481_);
v___x_553_ = lean_nat_dec_eq(v___x_552_, v___x_473_);
if (v___x_553_ == 0)
{
goto v___jp_490_;
}
else
{
uint8_t v___x_554_; 
v___x_554_ = lean_expr_eqv(v_fst_480_, v___x_489_);
if (v___x_554_ == 0)
{
goto v___jp_490_;
}
else
{
lean_object* v___x_555_; lean_object* v___x_556_; 
v___x_555_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2___closed__2, &l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2___closed__2_once, _init_l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2___closed__2);
lean_inc(v_a_474_);
lean_inc(v___x_478_);
v___x_556_ = l_Lean_Meta_throwTacticEx___redArg(v___x_478_, v_a_474_, v___x_555_, v___y_484_, v___y_485_, v___y_486_, v___y_487_);
if (lean_obj_tag(v___x_556_) == 0)
{
lean_dec_ref_known(v___x_556_, 1);
goto v___jp_490_;
}
else
{
lean_object* v_a_557_; lean_object* v___x_559_; uint8_t v_isShared_560_; uint8_t v_isSharedCheck_564_; 
lean_dec_ref(v_fvarIds_481_);
lean_dec_ref(v_snd_479_);
lean_dec(v___x_478_);
lean_dec(v_a_474_);
v_a_557_ = lean_ctor_get(v___x_556_, 0);
v_isSharedCheck_564_ = !lean_is_exclusive(v___x_556_);
if (v_isSharedCheck_564_ == 0)
{
v___x_559_ = v___x_556_;
v_isShared_560_ = v_isSharedCheck_564_;
goto v_resetjp_558_;
}
else
{
lean_inc(v_a_557_);
lean_dec(v___x_556_);
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
v___jp_490_:
{
lean_object* v___x_491_; 
lean_inc(v_a_474_);
v___x_491_ = l_Lean_MVarId_getTag(v_a_474_, v___y_484_, v___y_485_, v___y_486_, v___y_487_);
if (lean_obj_tag(v___x_491_) == 0)
{
lean_object* v_a_492_; lean_object* v___x_493_; 
v_a_492_ = lean_ctor_get(v___x_491_, 0);
lean_inc(v_a_492_);
lean_dec_ref_known(v___x_491_, 1);
lean_inc(v___x_489_);
v___x_493_ = l_Lean_Elab_Tactic_Conv_mkConvGoalFor(v___x_489_, v_a_492_, v___y_484_, v___y_485_, v___y_486_, v___y_487_);
if (lean_obj_tag(v___x_493_) == 0)
{
lean_object* v_a_494_; lean_object* v_fst_495_; lean_object* v_snd_496_; lean_object* v___x_498_; uint8_t v_isShared_499_; uint8_t v_isSharedCheck_535_; 
v_a_494_ = lean_ctor_get(v___x_493_, 0);
lean_inc(v_a_494_);
lean_dec_ref_known(v___x_493_, 1);
v_fst_495_ = lean_ctor_get(v_a_494_, 0);
v_snd_496_ = lean_ctor_get(v_a_494_, 1);
v_isSharedCheck_535_ = !lean_is_exclusive(v_a_494_);
if (v_isSharedCheck_535_ == 0)
{
v___x_498_ = v_a_494_;
v_isShared_499_ = v_isSharedCheck_535_;
goto v_resetjp_497_;
}
else
{
lean_inc(v_snd_496_);
lean_inc(v_fst_495_);
lean_dec(v_a_494_);
v___x_498_ = lean_box(0);
v_isShared_499_ = v_isSharedCheck_535_;
goto v_resetjp_497_;
}
v_resetjp_497_:
{
size_t v_sz_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; 
v_sz_500_ = lean_array_size(v_fvarIds_481_);
lean_inc_ref(v_fvarIds_481_);
v___x_501_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__2(v_sz_500_, v___x_475_, v_fvarIds_481_);
v___x_502_ = l_Lean_Expr_mvarId_x21(v_fst_495_);
lean_dec(v_fst_495_);
lean_inc(v_a_474_);
lean_inc(v___x_478_);
v___x_503_ = l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__1(v___x_501_, v___x_476_, v___x_477_, v___x_478_, v_a_474_, v___x_502_, v_snd_479_, v___y_484_, v___y_485_, v___y_486_, v___y_487_);
if (lean_obj_tag(v___x_503_) == 0)
{
lean_object* v___x_504_; 
lean_dec_ref_known(v___x_503_, 1);
lean_inc(v_snd_496_);
lean_inc(v_a_474_);
v___x_504_ = l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__1(v___x_501_, v___x_476_, v___x_477_, v___x_478_, v_a_474_, v_a_474_, v_snd_496_, v___y_484_, v___y_485_, v___y_486_, v___y_487_);
lean_dec_ref(v___x_501_);
if (lean_obj_tag(v___x_504_) == 0)
{
lean_object* v___x_506_; uint8_t v_isShared_507_; uint8_t v_isSharedCheck_517_; 
v_isSharedCheck_517_ = !lean_is_exclusive(v___x_504_);
if (v_isSharedCheck_517_ == 0)
{
lean_object* v_unused_518_; 
v_unused_518_ = lean_ctor_get(v___x_504_, 0);
lean_dec(v_unused_518_);
v___x_506_ = v___x_504_;
v_isShared_507_ = v_isSharedCheck_517_;
goto v_resetjp_505_;
}
else
{
lean_dec(v___x_504_);
v___x_506_ = lean_box(0);
v_isShared_507_ = v_isSharedCheck_517_;
goto v_resetjp_505_;
}
v_resetjp_505_:
{
lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_512_; 
v___x_508_ = l_Lean_Expr_mvarId_x21(v_snd_496_);
lean_dec(v_snd_496_);
v___x_509_ = lean_box(0);
v___x_510_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_510_, 0, v___x_508_);
lean_ctor_set(v___x_510_, 1, v___x_509_);
if (v_isShared_499_ == 0)
{
lean_ctor_set(v___x_498_, 1, v___x_510_);
lean_ctor_set(v___x_498_, 0, v_fvarIds_481_);
v___x_512_ = v___x_498_;
goto v_reusejp_511_;
}
else
{
lean_object* v_reuseFailAlloc_516_; 
v_reuseFailAlloc_516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_516_, 0, v_fvarIds_481_);
lean_ctor_set(v_reuseFailAlloc_516_, 1, v___x_510_);
v___x_512_ = v_reuseFailAlloc_516_;
goto v_reusejp_511_;
}
v_reusejp_511_:
{
lean_object* v___x_514_; 
if (v_isShared_507_ == 0)
{
lean_ctor_set(v___x_506_, 0, v___x_512_);
v___x_514_ = v___x_506_;
goto v_reusejp_513_;
}
else
{
lean_object* v_reuseFailAlloc_515_; 
v_reuseFailAlloc_515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_515_, 0, v___x_512_);
v___x_514_ = v_reuseFailAlloc_515_;
goto v_reusejp_513_;
}
v_reusejp_513_:
{
return v___x_514_;
}
}
}
}
else
{
lean_object* v_a_519_; lean_object* v___x_521_; uint8_t v_isShared_522_; uint8_t v_isSharedCheck_526_; 
lean_del_object(v___x_498_);
lean_dec(v_snd_496_);
lean_dec_ref(v_fvarIds_481_);
v_a_519_ = lean_ctor_get(v___x_504_, 0);
v_isSharedCheck_526_ = !lean_is_exclusive(v___x_504_);
if (v_isSharedCheck_526_ == 0)
{
v___x_521_ = v___x_504_;
v_isShared_522_ = v_isSharedCheck_526_;
goto v_resetjp_520_;
}
else
{
lean_inc(v_a_519_);
lean_dec(v___x_504_);
v___x_521_ = lean_box(0);
v_isShared_522_ = v_isSharedCheck_526_;
goto v_resetjp_520_;
}
v_resetjp_520_:
{
lean_object* v___x_524_; 
if (v_isShared_522_ == 0)
{
v___x_524_ = v___x_521_;
goto v_reusejp_523_;
}
else
{
lean_object* v_reuseFailAlloc_525_; 
v_reuseFailAlloc_525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_525_, 0, v_a_519_);
v___x_524_ = v_reuseFailAlloc_525_;
goto v_reusejp_523_;
}
v_reusejp_523_:
{
return v___x_524_;
}
}
}
}
else
{
lean_object* v_a_527_; lean_object* v___x_529_; uint8_t v_isShared_530_; uint8_t v_isSharedCheck_534_; 
lean_dec_ref(v___x_501_);
lean_del_object(v___x_498_);
lean_dec(v_snd_496_);
lean_dec_ref(v_fvarIds_481_);
lean_dec(v___x_478_);
lean_dec(v_a_474_);
v_a_527_ = lean_ctor_get(v___x_503_, 0);
v_isSharedCheck_534_ = !lean_is_exclusive(v___x_503_);
if (v_isSharedCheck_534_ == 0)
{
v___x_529_ = v___x_503_;
v_isShared_530_ = v_isSharedCheck_534_;
goto v_resetjp_528_;
}
else
{
lean_inc(v_a_527_);
lean_dec(v___x_503_);
v___x_529_ = lean_box(0);
v_isShared_530_ = v_isSharedCheck_534_;
goto v_resetjp_528_;
}
v_resetjp_528_:
{
lean_object* v___x_532_; 
if (v_isShared_530_ == 0)
{
v___x_532_ = v___x_529_;
goto v_reusejp_531_;
}
else
{
lean_object* v_reuseFailAlloc_533_; 
v_reuseFailAlloc_533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_533_, 0, v_a_527_);
v___x_532_ = v_reuseFailAlloc_533_;
goto v_reusejp_531_;
}
v_reusejp_531_:
{
return v___x_532_;
}
}
}
}
}
else
{
lean_object* v_a_536_; lean_object* v___x_538_; uint8_t v_isShared_539_; uint8_t v_isSharedCheck_543_; 
lean_dec_ref(v_fvarIds_481_);
lean_dec_ref(v_snd_479_);
lean_dec(v___x_478_);
lean_dec(v_a_474_);
v_a_536_ = lean_ctor_get(v___x_493_, 0);
v_isSharedCheck_543_ = !lean_is_exclusive(v___x_493_);
if (v_isSharedCheck_543_ == 0)
{
v___x_538_ = v___x_493_;
v_isShared_539_ = v_isSharedCheck_543_;
goto v_resetjp_537_;
}
else
{
lean_inc(v_a_536_);
lean_dec(v___x_493_);
v___x_538_ = lean_box(0);
v_isShared_539_ = v_isSharedCheck_543_;
goto v_resetjp_537_;
}
v_resetjp_537_:
{
lean_object* v___x_541_; 
if (v_isShared_539_ == 0)
{
v___x_541_ = v___x_538_;
goto v_reusejp_540_;
}
else
{
lean_object* v_reuseFailAlloc_542_; 
v_reuseFailAlloc_542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_542_, 0, v_a_536_);
v___x_541_ = v_reuseFailAlloc_542_;
goto v_reusejp_540_;
}
v_reusejp_540_:
{
return v___x_541_;
}
}
}
}
else
{
lean_object* v_a_544_; lean_object* v___x_546_; uint8_t v_isShared_547_; uint8_t v_isSharedCheck_551_; 
lean_dec_ref(v_fvarIds_481_);
lean_dec_ref(v_snd_479_);
lean_dec(v___x_478_);
lean_dec(v_a_474_);
v_a_544_ = lean_ctor_get(v___x_491_, 0);
v_isSharedCheck_551_ = !lean_is_exclusive(v___x_491_);
if (v_isSharedCheck_551_ == 0)
{
v___x_546_ = v___x_491_;
v_isShared_547_ = v_isSharedCheck_551_;
goto v_resetjp_545_;
}
else
{
lean_inc(v_a_544_);
lean_dec(v___x_491_);
v___x_546_ = lean_box(0);
v_isShared_547_ = v_isSharedCheck_551_;
goto v_resetjp_545_;
}
v_resetjp_545_:
{
lean_object* v___x_549_; 
if (v_isShared_547_ == 0)
{
v___x_549_ = v___x_546_;
goto v_reusejp_548_;
}
else
{
lean_object* v_reuseFailAlloc_550_; 
v_reuseFailAlloc_550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_550_, 0, v_a_544_);
v___x_549_ = v_reuseFailAlloc_550_;
goto v_reusejp_548_;
}
v_reusejp_548_:
{
return v___x_549_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_472_ = stack[0].m_obj;
lean_object* v___x_473_ = stack[1].m_obj;
lean_object* v_a_474_ = stack[2].m_obj;
size_t v___x_475_ = stack[3].m_num;
uint8_t v___x_476_ = stack[4].m_num;
uint8_t v___x_477_ = stack[5].m_num;
lean_object* v___x_478_ = stack[6].m_obj;
lean_object* v_snd_479_ = stack[7].m_obj;
lean_object* v_fst_480_ = stack[8].m_obj;
lean_object* v_fvarIds_481_ = stack[9].m_obj;
lean_object* v_es_482_ = stack[10].m_obj;
lean_object* v_x_483_ = stack[11].m_obj;
lean_object* v___y_484_ = stack[12].m_obj;
lean_object* v___y_485_ = stack[13].m_obj;
lean_object* v___y_486_ = stack[14].m_obj;
lean_object* v___y_487_ = stack[15].m_obj;
lean_object* v_res_565_;
v_res_565_ = l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2(v___x_472_, v___x_473_, v_a_474_, v___x_475_, v___x_476_, v___x_477_, v___x_478_, v_snd_479_, v_fst_480_, v_fvarIds_481_, v_es_482_, v_x_483_, v___y_484_, v___y_485_, v___y_486_, v___y_487_);
stack->m_obj
 = v_res_565_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2___boxed(lean_object** _args){
lean_object* v___x_566_ = _args[0];
lean_object* v___x_567_ = _args[1];
lean_object* v_a_568_ = _args[2];
lean_object* v___x_569_ = _args[3];
lean_object* v___x_570_ = _args[4];
lean_object* v___x_571_ = _args[5];
lean_object* v___x_572_ = _args[6];
lean_object* v_snd_573_ = _args[7];
lean_object* v_fst_574_ = _args[8];
lean_object* v_fvarIds_575_ = _args[9];
lean_object* v_es_576_ = _args[10];
lean_object* v_x_577_ = _args[11];
lean_object* v___y_578_ = _args[12];
lean_object* v___y_579_ = _args[13];
lean_object* v___y_580_ = _args[14];
lean_object* v___y_581_ = _args[15];
lean_object* v___y_582_ = _args[16];
_start:
{
size_t v___x_5816__boxed_583_; uint8_t v___x_5817__boxed_584_; uint8_t v___x_5818__boxed_585_; lean_object* v_res_586_; 
v___x_5816__boxed_583_ = lean_unbox_usize(v___x_569_);
lean_dec(v___x_569_);
v___x_5817__boxed_584_ = lean_unbox(v___x_570_);
v___x_5818__boxed_585_ = lean_unbox(v___x_571_);
v_res_586_ = l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2(v___x_566_, v___x_567_, v_a_568_, v___x_5816__boxed_583_, v___x_5817__boxed_584_, v___x_5818__boxed_585_, v___x_572_, v_snd_573_, v_fst_574_, v_fvarIds_575_, v_es_576_, v_x_577_, v___y_578_, v___y_579_, v___y_580_, v___y_581_);
lean_dec(v___y_581_);
lean_dec_ref(v___y_580_);
lean_dec(v___y_579_);
lean_dec_ref(v___y_578_);
lean_dec(v_x_577_);
lean_dec_ref(v_es_576_);
lean_dec_ref(v_fst_574_);
lean_dec(v___x_567_);
lean_dec_ref(v___x_566_);
return v_res_586_;
}
}
lean_object* l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__3(lean_object* v___x_590_, lean_object* v___x_591_, size_t v___x_592_, uint8_t v___x_593_, uint8_t v___x_594_, lean_object* v_snd_595_, lean_object* v_fst_596_, lean_object* v___x_597_, lean_object* v___x_598_, lean_object* v_a_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_){
_start:
{
lean_object* v___x_609_; 
v___x_609_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_601_, v___y_604_, v___y_605_, v___y_606_, v___y_607_);
if (lean_obj_tag(v___x_609_) == 0)
{
lean_object* v_a_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___f_615_; lean_object* v___x_616_; 
v_a_610_ = lean_ctor_get(v___x_609_, 0);
lean_inc_n(v_a_610_, 2);
lean_dec_ref_known(v___x_609_, 1);
v___x_611_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__3___closed__1));
v___x_612_ = lean_box_usize(v___x_592_);
v___x_613_ = lean_box(v___x_593_);
v___x_614_ = lean_box(v___x_594_);
lean_inc_ref(v_fst_596_);
v___f_615_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2___boxed), 17, 9);
lean_closure_set(v___f_615_, 0, v___x_590_);
lean_closure_set(v___f_615_, 1, v___x_591_);
lean_closure_set(v___f_615_, 2, v_a_610_);
lean_closure_set(v___f_615_, 3, v___x_612_);
lean_closure_set(v___f_615_, 4, v___x_613_);
lean_closure_set(v___f_615_, 5, v___x_614_);
lean_closure_set(v___f_615_, 6, v___x_611_);
lean_closure_set(v___f_615_, 7, v_snd_595_);
lean_closure_set(v___f_615_, 8, v_fst_596_);
v___x_616_ = l_Lean_MVarId_checkNotAssigned(v_a_610_, v___x_611_, v___y_604_, v___y_605_, v___y_606_, v___y_607_);
if (lean_obj_tag(v___x_616_) == 0)
{
lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; 
lean_dec_ref_known(v___x_616_, 1);
v___x_617_ = lean_mk_empty_array_with_capacity(v___x_597_);
v___x_618_ = lean_array_push(v___x_617_, v_fst_596_);
v___x_619_ = l_Lean_Meta_extractLets___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__5___redArg(v___x_618_, v___x_598_, v___f_615_, v_a_599_, v___y_604_, v___y_605_, v___y_606_, v___y_607_);
if (lean_obj_tag(v___x_619_) == 0)
{
lean_object* v_a_620_; lean_object* v_fst_621_; lean_object* v_snd_622_; lean_object* v___x_623_; 
v_a_620_ = lean_ctor_get(v___x_619_, 0);
lean_inc(v_a_620_);
lean_dec_ref_known(v___x_619_, 1);
v_fst_621_ = lean_ctor_get(v_a_620_, 0);
lean_inc(v_fst_621_);
v_snd_622_ = lean_ctor_get(v_a_620_, 1);
lean_inc(v_snd_622_);
lean_dec(v_a_620_);
v___x_623_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v_snd_622_, v___y_601_, v___y_604_, v___y_605_, v___y_606_, v___y_607_);
if (lean_obj_tag(v___x_623_) == 0)
{
lean_object* v___x_625_; uint8_t v_isShared_626_; uint8_t v_isSharedCheck_630_; 
v_isSharedCheck_630_ = !lean_is_exclusive(v___x_623_);
if (v_isSharedCheck_630_ == 0)
{
lean_object* v_unused_631_; 
v_unused_631_ = lean_ctor_get(v___x_623_, 0);
lean_dec(v_unused_631_);
v___x_625_ = v___x_623_;
v_isShared_626_ = v_isSharedCheck_630_;
goto v_resetjp_624_;
}
else
{
lean_dec(v___x_623_);
v___x_625_ = lean_box(0);
v_isShared_626_ = v_isSharedCheck_630_;
goto v_resetjp_624_;
}
v_resetjp_624_:
{
lean_object* v___x_628_; 
if (v_isShared_626_ == 0)
{
lean_ctor_set(v___x_625_, 0, v_fst_621_);
v___x_628_ = v___x_625_;
goto v_reusejp_627_;
}
else
{
lean_object* v_reuseFailAlloc_629_; 
v_reuseFailAlloc_629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_629_, 0, v_fst_621_);
v___x_628_ = v_reuseFailAlloc_629_;
goto v_reusejp_627_;
}
v_reusejp_627_:
{
return v___x_628_;
}
}
}
else
{
lean_object* v_a_632_; lean_object* v___x_634_; uint8_t v_isShared_635_; uint8_t v_isSharedCheck_639_; 
lean_dec(v_fst_621_);
v_a_632_ = lean_ctor_get(v___x_623_, 0);
v_isSharedCheck_639_ = !lean_is_exclusive(v___x_623_);
if (v_isSharedCheck_639_ == 0)
{
v___x_634_ = v___x_623_;
v_isShared_635_ = v_isSharedCheck_639_;
goto v_resetjp_633_;
}
else
{
lean_inc(v_a_632_);
lean_dec(v___x_623_);
v___x_634_ = lean_box(0);
v_isShared_635_ = v_isSharedCheck_639_;
goto v_resetjp_633_;
}
v_resetjp_633_:
{
lean_object* v___x_637_; 
if (v_isShared_635_ == 0)
{
v___x_637_ = v___x_634_;
goto v_reusejp_636_;
}
else
{
lean_object* v_reuseFailAlloc_638_; 
v_reuseFailAlloc_638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_638_, 0, v_a_632_);
v___x_637_ = v_reuseFailAlloc_638_;
goto v_reusejp_636_;
}
v_reusejp_636_:
{
return v___x_637_;
}
}
}
}
else
{
lean_object* v_a_640_; lean_object* v___x_642_; uint8_t v_isShared_643_; uint8_t v_isSharedCheck_647_; 
v_a_640_ = lean_ctor_get(v___x_619_, 0);
v_isSharedCheck_647_ = !lean_is_exclusive(v___x_619_);
if (v_isSharedCheck_647_ == 0)
{
v___x_642_ = v___x_619_;
v_isShared_643_ = v_isSharedCheck_647_;
goto v_resetjp_641_;
}
else
{
lean_inc(v_a_640_);
lean_dec(v___x_619_);
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
else
{
lean_object* v_a_648_; lean_object* v___x_650_; uint8_t v_isShared_651_; uint8_t v_isSharedCheck_655_; 
lean_dec_ref(v___f_615_);
lean_dec(v___x_598_);
lean_dec_ref(v_fst_596_);
v_a_648_ = lean_ctor_get(v___x_616_, 0);
v_isSharedCheck_655_ = !lean_is_exclusive(v___x_616_);
if (v_isSharedCheck_655_ == 0)
{
v___x_650_ = v___x_616_;
v_isShared_651_ = v_isSharedCheck_655_;
goto v_resetjp_649_;
}
else
{
lean_inc(v_a_648_);
lean_dec(v___x_616_);
v___x_650_ = lean_box(0);
v_isShared_651_ = v_isSharedCheck_655_;
goto v_resetjp_649_;
}
v_resetjp_649_:
{
lean_object* v___x_653_; 
if (v_isShared_651_ == 0)
{
v___x_653_ = v___x_650_;
goto v_reusejp_652_;
}
else
{
lean_object* v_reuseFailAlloc_654_; 
v_reuseFailAlloc_654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_654_, 0, v_a_648_);
v___x_653_ = v_reuseFailAlloc_654_;
goto v_reusejp_652_;
}
v_reusejp_652_:
{
return v___x_653_;
}
}
}
}
else
{
lean_object* v_a_656_; lean_object* v___x_658_; uint8_t v_isShared_659_; uint8_t v_isSharedCheck_663_; 
lean_dec(v___x_598_);
lean_dec_ref(v_fst_596_);
lean_dec_ref(v_snd_595_);
lean_dec(v___x_591_);
lean_dec_ref(v___x_590_);
v_a_656_ = lean_ctor_get(v___x_609_, 0);
v_isSharedCheck_663_ = !lean_is_exclusive(v___x_609_);
if (v_isSharedCheck_663_ == 0)
{
v___x_658_ = v___x_609_;
v_isShared_659_ = v_isSharedCheck_663_;
goto v_resetjp_657_;
}
else
{
lean_inc(v_a_656_);
lean_dec(v___x_609_);
v___x_658_ = lean_box(0);
v_isShared_659_ = v_isSharedCheck_663_;
goto v_resetjp_657_;
}
v_resetjp_657_:
{
lean_object* v___x_661_; 
if (v_isShared_659_ == 0)
{
v___x_661_ = v___x_658_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_662_; 
v_reuseFailAlloc_662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_662_, 0, v_a_656_);
v___x_661_ = v_reuseFailAlloc_662_;
goto v_reusejp_660_;
}
v_reusejp_660_:
{
return v___x_661_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_590_ = stack[0].m_obj;
lean_object* v___x_591_ = stack[1].m_obj;
size_t v___x_592_ = stack[2].m_num;
uint8_t v___x_593_ = stack[3].m_num;
uint8_t v___x_594_ = stack[4].m_num;
lean_object* v_snd_595_ = stack[5].m_obj;
lean_object* v_fst_596_ = stack[6].m_obj;
lean_object* v___x_597_ = stack[7].m_obj;
lean_object* v___x_598_ = stack[8].m_obj;
lean_object* v_a_599_ = stack[9].m_obj;
lean_object* v___y_600_ = stack[10].m_obj;
lean_object* v___y_601_ = stack[11].m_obj;
lean_object* v___y_602_ = stack[12].m_obj;
lean_object* v___y_603_ = stack[13].m_obj;
lean_object* v___y_604_ = stack[14].m_obj;
lean_object* v___y_605_ = stack[15].m_obj;
lean_object* v___y_606_ = stack[16].m_obj;
lean_object* v___y_607_ = stack[17].m_obj;
lean_object* v_res_664_;
v_res_664_ = l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__3(v___x_590_, v___x_591_, v___x_592_, v___x_593_, v___x_594_, v_snd_595_, v_fst_596_, v___x_597_, v___x_598_, v_a_599_, v___y_600_, v___y_601_, v___y_602_, v___y_603_, v___y_604_, v___y_605_, v___y_606_, v___y_607_);
stack->m_obj
 = v_res_664_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__3___boxed(lean_object** _args){
lean_object* v___x_665_ = _args[0];
lean_object* v___x_666_ = _args[1];
lean_object* v___x_667_ = _args[2];
lean_object* v___x_668_ = _args[3];
lean_object* v___x_669_ = _args[4];
lean_object* v_snd_670_ = _args[5];
lean_object* v_fst_671_ = _args[6];
lean_object* v___x_672_ = _args[7];
lean_object* v___x_673_ = _args[8];
lean_object* v_a_674_ = _args[9];
lean_object* v___y_675_ = _args[10];
lean_object* v___y_676_ = _args[11];
lean_object* v___y_677_ = _args[12];
lean_object* v___y_678_ = _args[13];
lean_object* v___y_679_ = _args[14];
lean_object* v___y_680_ = _args[15];
lean_object* v___y_681_ = _args[16];
lean_object* v___y_682_ = _args[17];
lean_object* v___y_683_ = _args[18];
_start:
{
size_t v___x_6134__boxed_684_; uint8_t v___x_6135__boxed_685_; uint8_t v___x_6136__boxed_686_; lean_object* v_res_687_; 
v___x_6134__boxed_684_ = lean_unbox_usize(v___x_667_);
lean_dec(v___x_667_);
v___x_6135__boxed_685_ = lean_unbox(v___x_668_);
v___x_6136__boxed_686_ = lean_unbox(v___x_669_);
v_res_687_ = l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__3(v___x_665_, v___x_666_, v___x_6134__boxed_684_, v___x_6135__boxed_685_, v___x_6136__boxed_686_, v_snd_670_, v_fst_671_, v___x_672_, v___x_673_, v_a_674_, v___y_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_, v___y_682_);
lean_dec(v___y_682_);
lean_dec_ref(v___y_681_);
lean_dec(v___y_680_);
lean_dec_ref(v___y_679_);
lean_dec(v___y_678_);
lean_dec_ref(v___y_677_);
lean_dec(v___y_676_);
lean_dec_ref(v___y_675_);
lean_dec_ref(v_a_674_);
lean_dec(v___x_672_);
return v_res_687_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__1(size_t v_sz_688_, size_t v_i_689_, lean_object* v_bs_690_){
_start:
{
uint8_t v___x_691_; 
v___x_691_ = lean_usize_dec_lt(v_i_689_, v_sz_688_);
if (v___x_691_ == 0)
{
return v_bs_690_;
}
else
{
lean_object* v_v_692_; lean_object* v___x_693_; lean_object* v_bs_x27_694_; lean_object* v___x_695_; size_t v___x_696_; size_t v___x_697_; lean_object* v___x_698_; 
v_v_692_ = lean_array_uget(v_bs_690_, v_i_689_);
v___x_693_ = lean_unsigned_to_nat(0u);
v_bs_x27_694_ = lean_array_uset(v_bs_690_, v_i_689_, v___x_693_);
v___x_695_ = l_Lean_Elab_Tactic_getNameOfIdent_x27(v_v_692_);
lean_dec(v_v_692_);
v___x_696_ = ((size_t)1ULL);
v___x_697_ = lean_usize_add(v_i_689_, v___x_696_);
v___x_698_ = lean_array_uset(v_bs_x27_694_, v_i_689_, v___x_695_);
v_i_689_ = v___x_697_;
v_bs_690_ = v___x_698_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__1_0interp(lean_interpreter_value* stack)
{
size_t v_sz_688_ = stack[0].m_num;
size_t v_i_689_ = stack[1].m_num;
lean_object* v_bs_690_ = stack[2].m_obj;
lean_object* v_res_700_;
v_res_700_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__1(v_sz_688_, v_i_689_, v_bs_690_);
stack->m_obj
 = v_res_700_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__1___boxed(lean_object* v_sz_701_, lean_object* v_i_702_, lean_object* v_bs_703_){
_start:
{
size_t v_sz_boxed_704_; size_t v_i_boxed_705_; lean_object* v_res_706_; 
v_sz_boxed_704_ = lean_unbox_usize(v_sz_701_);
lean_dec(v_sz_701_);
v_i_boxed_705_ = lean_unbox_usize(v_i_702_);
lean_dec(v_i_702_);
v_res_706_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__1(v_sz_boxed_704_, v_i_boxed_705_, v_bs_703_);
return v_res_706_;
}
}
lean_object* l_Lean_Elab_Tactic_Conv_evalExtractLets(lean_object* v_x_726_, lean_object* v_a_727_, lean_object* v_a_728_, lean_object* v_a_729_, lean_object* v_a_730_, lean_object* v_a_731_, lean_object* v_a_732_, lean_object* v_a_733_, lean_object* v_a_734_){
_start:
{
lean_object* v___x_736_; uint8_t v___x_737_; 
v___x_736_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__5));
lean_inc(v_x_726_);
v___x_737_ = l_Lean_Syntax_isOfKind(v_x_726_, v___x_736_);
if (v___x_737_ == 0)
{
lean_object* v___x_738_; 
lean_dec(v_x_726_);
v___x_738_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__0___redArg();
return v___x_738_;
}
else
{
lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; uint8_t v___x_742_; 
v___x_739_ = lean_unsigned_to_nat(1u);
v___x_740_ = l_Lean_Syntax_getArg(v_x_726_, v___x_739_);
v___x_741_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__7));
lean_inc(v___x_740_);
v___x_742_ = l_Lean_Syntax_isOfKind(v___x_740_, v___x_741_);
if (v___x_742_ == 0)
{
lean_object* v___x_743_; 
lean_dec(v___x_740_);
lean_dec(v_x_726_);
v___x_743_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__0___redArg();
return v___x_743_;
}
else
{
lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v_ids_748_; uint8_t v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; 
v___x_744_ = l_Lean_instInhabitedExpr;
v___x_745_ = lean_unsigned_to_nat(0u);
v___x_746_ = lean_unsigned_to_nat(2u);
v___x_747_ = l_Lean_Syntax_getArg(v_x_726_, v___x_746_);
lean_dec(v_x_726_);
v_ids_748_ = l_Lean_Syntax_getArgs(v___x_747_);
lean_dec(v___x_747_);
v___x_749_ = 0;
v___x_750_ = lean_alloc_ctor(0, 0, 11);
lean_ctor_set_uint8(v___x_750_, 0, v___x_749_);
lean_ctor_set_uint8(v___x_750_, 1, v___x_742_);
lean_ctor_set_uint8(v___x_750_, 2, v___x_749_);
lean_ctor_set_uint8(v___x_750_, 3, v___x_742_);
lean_ctor_set_uint8(v___x_750_, 4, v___x_742_);
lean_ctor_set_uint8(v___x_750_, 5, v___x_749_);
lean_ctor_set_uint8(v___x_750_, 6, v___x_742_);
lean_ctor_set_uint8(v___x_750_, 7, v___x_742_);
lean_ctor_set_uint8(v___x_750_, 8, v___x_749_);
lean_ctor_set_uint8(v___x_750_, 9, v___x_749_);
lean_ctor_set_uint8(v___x_750_, 10, v___x_749_);
v___x_751_ = l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg(v___x_740_, v___x_750_, v___x_742_, v_a_727_, v_a_733_, v_a_734_);
if (lean_obj_tag(v___x_751_) == 0)
{
lean_object* v_a_752_; size_t v_sz_753_; size_t v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; 
v_a_752_ = lean_ctor_get(v___x_751_, 0);
lean_inc(v_a_752_);
lean_dec_ref_known(v___x_751_, 1);
v_sz_753_ = lean_array_size(v_ids_748_);
v___x_754_ = ((size_t)0ULL);
lean_inc_ref(v_ids_748_);
v___x_755_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__1(v_sz_753_, v___x_754_, v_ids_748_);
v___x_756_ = lean_array_to_list(v___x_755_);
v___x_757_ = l_Lean_Elab_Tactic_Conv_getLhsRhs___redArg(v_a_728_, v_a_731_, v_a_732_, v_a_733_, v_a_734_);
if (lean_obj_tag(v___x_757_) == 0)
{
lean_object* v_a_758_; lean_object* v_fst_759_; lean_object* v_snd_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___f_764_; lean_object* v___x_765_; 
v_a_758_ = lean_ctor_get(v___x_757_, 0);
lean_inc(v_a_758_);
lean_dec_ref_known(v___x_757_, 1);
v_fst_759_ = lean_ctor_get(v_a_758_, 0);
lean_inc(v_fst_759_);
v_snd_760_ = lean_ctor_get(v_a_758_, 1);
lean_inc(v_snd_760_);
lean_dec(v_a_758_);
v___x_761_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalExtractLets___boxed__const__1));
v___x_762_ = lean_box(v___x_749_);
v___x_763_ = lean_box(v___x_742_);
v___f_764_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__3___boxed), 19, 10);
lean_closure_set(v___f_764_, 0, v___x_744_);
lean_closure_set(v___f_764_, 1, v___x_745_);
lean_closure_set(v___f_764_, 2, v___x_761_);
lean_closure_set(v___f_764_, 3, v___x_762_);
lean_closure_set(v___f_764_, 4, v___x_763_);
lean_closure_set(v___f_764_, 5, v_snd_760_);
lean_closure_set(v___f_764_, 6, v_fst_759_);
lean_closure_set(v___f_764_, 7, v___x_739_);
lean_closure_set(v___f_764_, 8, v___x_756_);
lean_closure_set(v___f_764_, 9, v_a_752_);
v___x_765_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_764_, v_a_727_, v_a_728_, v_a_729_, v_a_730_, v_a_731_, v_a_732_, v_a_733_, v_a_734_);
if (lean_obj_tag(v___x_765_) == 0)
{
lean_object* v_a_766_; lean_object* v___x_767_; 
v_a_766_ = lean_ctor_get(v___x_765_, 0);
lean_inc(v_a_766_);
lean_dec_ref_known(v___x_765_, 1);
v___x_767_ = l_Lean_Elab_Tactic_extractLetsAddVarInfo(v_ids_748_, v_a_766_, v_a_727_, v_a_728_, v_a_729_, v_a_730_, v_a_731_, v_a_732_, v_a_733_, v_a_734_);
return v___x_767_;
}
else
{
lean_object* v_a_768_; lean_object* v___x_770_; uint8_t v_isShared_771_; uint8_t v_isSharedCheck_775_; 
lean_dec_ref(v_ids_748_);
v_a_768_ = lean_ctor_get(v___x_765_, 0);
v_isSharedCheck_775_ = !lean_is_exclusive(v___x_765_);
if (v_isSharedCheck_775_ == 0)
{
v___x_770_ = v___x_765_;
v_isShared_771_ = v_isSharedCheck_775_;
goto v_resetjp_769_;
}
else
{
lean_inc(v_a_768_);
lean_dec(v___x_765_);
v___x_770_ = lean_box(0);
v_isShared_771_ = v_isSharedCheck_775_;
goto v_resetjp_769_;
}
v_resetjp_769_:
{
lean_object* v___x_773_; 
if (v_isShared_771_ == 0)
{
v___x_773_ = v___x_770_;
goto v_reusejp_772_;
}
else
{
lean_object* v_reuseFailAlloc_774_; 
v_reuseFailAlloc_774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_774_, 0, v_a_768_);
v___x_773_ = v_reuseFailAlloc_774_;
goto v_reusejp_772_;
}
v_reusejp_772_:
{
return v___x_773_;
}
}
}
}
else
{
lean_object* v_a_776_; lean_object* v___x_778_; uint8_t v_isShared_779_; uint8_t v_isSharedCheck_783_; 
lean_dec(v___x_756_);
lean_dec(v_a_752_);
lean_dec_ref(v_ids_748_);
v_a_776_ = lean_ctor_get(v___x_757_, 0);
v_isSharedCheck_783_ = !lean_is_exclusive(v___x_757_);
if (v_isSharedCheck_783_ == 0)
{
v___x_778_ = v___x_757_;
v_isShared_779_ = v_isSharedCheck_783_;
goto v_resetjp_777_;
}
else
{
lean_inc(v_a_776_);
lean_dec(v___x_757_);
v___x_778_ = lean_box(0);
v_isShared_779_ = v_isSharedCheck_783_;
goto v_resetjp_777_;
}
v_resetjp_777_:
{
lean_object* v___x_781_; 
if (v_isShared_779_ == 0)
{
v___x_781_ = v___x_778_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v_a_776_);
v___x_781_ = v_reuseFailAlloc_782_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
return v___x_781_;
}
}
}
}
else
{
lean_object* v_a_784_; lean_object* v___x_786_; uint8_t v_isShared_787_; uint8_t v_isSharedCheck_791_; 
lean_dec_ref(v_ids_748_);
v_a_784_ = lean_ctor_get(v___x_751_, 0);
v_isSharedCheck_791_ = !lean_is_exclusive(v___x_751_);
if (v_isSharedCheck_791_ == 0)
{
v___x_786_ = v___x_751_;
v_isShared_787_ = v_isSharedCheck_791_;
goto v_resetjp_785_;
}
else
{
lean_inc(v_a_784_);
lean_dec(v___x_751_);
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
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Conv_evalExtractLets_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_726_ = stack[0].m_obj;
lean_object* v_a_727_ = stack[1].m_obj;
lean_object* v_a_728_ = stack[2].m_obj;
lean_object* v_a_729_ = stack[3].m_obj;
lean_object* v_a_730_ = stack[4].m_obj;
lean_object* v_a_731_ = stack[5].m_obj;
lean_object* v_a_732_ = stack[6].m_obj;
lean_object* v_a_733_ = stack[7].m_obj;
lean_object* v_a_734_ = stack[8].m_obj;
lean_object* v_res_792_;
v_res_792_ = l_Lean_Elab_Tactic_Conv_evalExtractLets(v_x_726_, v_a_727_, v_a_728_, v_a_729_, v_a_730_, v_a_731_, v_a_732_, v_a_733_, v_a_734_);
stack->m_obj
 = v_res_792_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalExtractLets___boxed(lean_object* v_x_793_, lean_object* v_a_794_, lean_object* v_a_795_, lean_object* v_a_796_, lean_object* v_a_797_, lean_object* v_a_798_, lean_object* v_a_799_, lean_object* v_a_800_, lean_object* v_a_801_, lean_object* v_a_802_){
_start:
{
lean_object* v_res_803_; 
v_res_803_ = l_Lean_Elab_Tactic_Conv_evalExtractLets(v_x_793_, v_a_794_, v_a_795_, v_a_796_, v_a_797_, v_a_798_, v_a_799_, v_a_800_, v_a_801_);
lean_dec(v_a_801_);
lean_dec_ref(v_a_800_);
lean_dec(v_a_799_);
lean_dec_ref(v_a_798_);
lean_dec(v_a_797_);
lean_dec_ref(v_a_796_);
lean_dec(v_a_795_);
lean_dec_ref(v_a_794_);
return v_res_803_;
}
}
lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3(lean_object* v_mvarId_804_, lean_object* v_val_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_){
_start:
{
lean_object* v___x_811_; 
v___x_811_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3___redArg(v_mvarId_804_, v_val_805_, v___y_807_);
return v___x_811_;
}
}
LEAN_EXPORT void l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_804_ = stack[0].m_obj;
lean_object* v_val_805_ = stack[1].m_obj;
lean_object* v___y_806_ = stack[2].m_obj;
lean_object* v___y_807_ = stack[3].m_obj;
lean_object* v___y_808_ = stack[4].m_obj;
lean_object* v___y_809_ = stack[5].m_obj;
lean_object* v_res_812_;
v_res_812_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3(v_mvarId_804_, v_val_805_, v___y_806_, v___y_807_, v___y_808_, v___y_809_);
stack->m_obj
 = v_res_812_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3___boxed(lean_object* v_mvarId_813_, lean_object* v_val_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_){
_start:
{
lean_object* v_res_820_; 
v_res_820_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3(v_mvarId_813_, v_val_814_, v___y_815_, v___y_816_, v___y_817_, v___y_818_);
lean_dec(v___y_818_);
lean_dec_ref(v___y_817_);
lean_dec(v___y_816_);
lean_dec_ref(v___y_815_);
return v_res_820_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3(lean_object* v_00_u03b2_821_, lean_object* v_x_822_, lean_object* v_x_823_, lean_object* v_x_824_){
_start:
{
lean_object* v___x_825_; 
v___x_825_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3___redArg(v_x_822_, v_x_823_, v_x_824_);
return v___x_825_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6(lean_object* v_00_u03b2_826_, lean_object* v_x_827_, size_t v_x_828_, size_t v_x_829_, lean_object* v_x_830_, lean_object* v_x_831_){
_start:
{
lean_object* v___x_832_; 
v___x_832_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___redArg(v_x_827_, v_x_828_, v_x_829_, v_x_830_, v_x_831_);
return v___x_832_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_827_ = stack[1].m_obj;
size_t v_x_828_ = stack[2].m_num;
size_t v_x_829_ = stack[3].m_num;
lean_object* v_x_830_ = stack[4].m_obj;
lean_object* v_x_831_ = stack[5].m_obj;
lean_object* v_res_833_;
v_res_833_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6(lean_box(0), v_x_827_, v_x_828_, v_x_829_, v_x_830_, v_x_831_);
stack->m_obj
 = v_res_833_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___boxed(lean_object* v_00_u03b2_834_, lean_object* v_x_835_, lean_object* v_x_836_, lean_object* v_x_837_, lean_object* v_x_838_, lean_object* v_x_839_){
_start:
{
size_t v_x_6708__boxed_840_; size_t v_x_6709__boxed_841_; lean_object* v_res_842_; 
v_x_6708__boxed_840_ = lean_unbox_usize(v_x_836_);
lean_dec(v_x_836_);
v_x_6709__boxed_841_ = lean_unbox_usize(v_x_837_);
lean_dec(v_x_837_);
v_res_842_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6(v_00_u03b2_834_, v_x_835_, v_x_6708__boxed_840_, v_x_6709__boxed_841_, v_x_838_, v_x_839_);
return v_res_842_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6_spec__7(lean_object* v_00_u03b2_843_, lean_object* v_n_844_, lean_object* v_k_845_, lean_object* v_v_846_){
_start:
{
lean_object* v___x_847_; 
v___x_847_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6_spec__7___redArg(v_n_844_, v_k_845_, v_v_846_);
return v___x_847_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6_spec__8(lean_object* v_00_u03b2_848_, size_t v_depth_849_, lean_object* v_keys_850_, lean_object* v_vals_851_, lean_object* v_heq_852_, lean_object* v_i_853_, lean_object* v_entries_854_){
_start:
{
lean_object* v___x_855_; 
v___x_855_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6_spec__8___redArg(v_depth_849_, v_keys_850_, v_vals_851_, v_i_853_, v_entries_854_);
return v___x_855_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6_spec__8_0interp(lean_interpreter_value* stack)
{
size_t v_depth_849_ = stack[1].m_num;
lean_object* v_keys_850_ = stack[2].m_obj;
lean_object* v_vals_851_ = stack[3].m_obj;
lean_object* v_i_853_ = stack[5].m_obj;
lean_object* v_entries_854_ = stack[6].m_obj;
lean_object* v_res_856_;
v_res_856_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6_spec__8(lean_box(0), v_depth_849_, v_keys_850_, v_vals_851_, lean_box(0), v_i_853_, v_entries_854_);
stack->m_obj
 = v_res_856_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6_spec__8___boxed(lean_object* v_00_u03b2_857_, lean_object* v_depth_858_, lean_object* v_keys_859_, lean_object* v_vals_860_, lean_object* v_heq_861_, lean_object* v_i_862_, lean_object* v_entries_863_){
_start:
{
size_t v_depth_boxed_864_; lean_object* v_res_865_; 
v_depth_boxed_864_ = lean_unbox_usize(v_depth_858_);
lean_dec(v_depth_858_);
v_res_865_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6_spec__8(v_00_u03b2_857_, v_depth_boxed_864_, v_keys_859_, v_vals_860_, v_heq_861_, v_i_862_, v_entries_863_);
lean_dec_ref(v_vals_860_);
lean_dec_ref(v_keys_859_);
return v_res_865_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6_spec__7_spec__8(lean_object* v_00_u03b2_866_, lean_object* v_x_867_, lean_object* v_x_868_, lean_object* v_x_869_, lean_object* v_x_870_){
_start:
{
lean_object* v___x_871_; 
v___x_871_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6_spec__7_spec__8___redArg(v_x_867_, v_x_868_, v_x_869_, v_x_870_);
return v___x_871_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalExtractLets___regBuiltin_Lean_Elab_Tactic_Conv_evalExtractLets__1(){
_start:
{
lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; 
v___x_881_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_882_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__5));
v___x_883_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalExtractLets___regBuiltin_Lean_Elab_Tactic_Conv_evalExtractLets__1___closed__2));
v___x_884_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalExtractLets___boxed), 10, 0);
v___x_885_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_881_, v___x_882_, v___x_883_, v___x_884_);
return v___x_885_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalExtractLets___regBuiltin_Lean_Elab_Tactic_Conv_evalExtractLets__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_886_;
v_res_886_ = l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalExtractLets___regBuiltin_Lean_Elab_Tactic_Conv_evalExtractLets__1();
stack->m_obj
 = v_res_886_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalExtractLets___regBuiltin_Lean_Elab_Tactic_Conv_evalExtractLets__1___boxed(lean_object* v_a_887_){
_start:
{
lean_object* v_res_888_; 
v_res_888_ = l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalExtractLets___regBuiltin_Lean_Elab_Tactic_Conv_evalExtractLets__1();
return v_res_888_;
}
}
lean_object* l_Lean_Elab_Tactic_Conv_evalLiftLets___lam__0(lean_object* v_a_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_){
_start:
{
lean_object* v___x_902_; 
v___x_902_ = l_Lean_Elab_Tactic_Conv_getLhs___redArg(v___y_894_, v___y_897_, v___y_898_, v___y_899_, v___y_900_);
if (lean_obj_tag(v___x_902_) == 0)
{
lean_object* v_a_903_; lean_object* v___x_904_; 
v_a_903_ = lean_ctor_get(v___x_902_, 0);
lean_inc_n(v_a_903_, 2);
lean_dec_ref_known(v___x_902_, 1);
v___x_904_ = l_Lean_Meta_liftLets(v_a_903_, v_a_892_, v___y_897_, v___y_898_, v___y_899_, v___y_900_);
if (lean_obj_tag(v___x_904_) == 0)
{
lean_object* v_a_905_; uint8_t v___x_906_; 
v_a_905_ = lean_ctor_get(v___x_904_, 0);
lean_inc(v_a_905_);
lean_dec_ref_known(v___x_904_, 1);
v___x_906_ = lean_expr_eqv(v_a_903_, v_a_905_);
lean_dec(v_a_903_);
if (v___x_906_ == 0)
{
lean_object* v___x_907_; 
v___x_907_ = l_Lean_Elab_Tactic_Conv_changeLhs(v_a_905_, v___y_893_, v___y_894_, v___y_895_, v___y_896_, v___y_897_, v___y_898_, v___y_899_, v___y_900_);
return v___x_907_;
}
else
{
lean_object* v___x_908_; 
v___x_908_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_894_, v___y_897_, v___y_898_, v___y_899_, v___y_900_);
if (lean_obj_tag(v___x_908_) == 0)
{
lean_object* v_a_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; 
v_a_909_ = lean_ctor_get(v___x_908_, 0);
lean_inc(v_a_909_);
lean_dec_ref_known(v___x_908_, 1);
v___x_910_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalLiftLets___lam__0___closed__1));
v___x_911_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2___closed__2, &l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2___closed__2_once, _init_l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2___closed__2);
v___x_912_ = l_Lean_Meta_throwTacticEx___redArg(v___x_910_, v_a_909_, v___x_911_, v___y_897_, v___y_898_, v___y_899_, v___y_900_);
if (lean_obj_tag(v___x_912_) == 0)
{
lean_object* v___x_913_; 
lean_dec_ref_known(v___x_912_, 1);
v___x_913_ = l_Lean_Elab_Tactic_Conv_changeLhs(v_a_905_, v___y_893_, v___y_894_, v___y_895_, v___y_896_, v___y_897_, v___y_898_, v___y_899_, v___y_900_);
return v___x_913_;
}
else
{
lean_dec(v_a_905_);
return v___x_912_;
}
}
else
{
lean_object* v_a_914_; lean_object* v___x_916_; uint8_t v_isShared_917_; uint8_t v_isSharedCheck_921_; 
lean_dec(v_a_905_);
v_a_914_ = lean_ctor_get(v___x_908_, 0);
v_isSharedCheck_921_ = !lean_is_exclusive(v___x_908_);
if (v_isSharedCheck_921_ == 0)
{
v___x_916_ = v___x_908_;
v_isShared_917_ = v_isSharedCheck_921_;
goto v_resetjp_915_;
}
else
{
lean_inc(v_a_914_);
lean_dec(v___x_908_);
v___x_916_ = lean_box(0);
v_isShared_917_ = v_isSharedCheck_921_;
goto v_resetjp_915_;
}
v_resetjp_915_:
{
lean_object* v___x_919_; 
if (v_isShared_917_ == 0)
{
v___x_919_ = v___x_916_;
goto v_reusejp_918_;
}
else
{
lean_object* v_reuseFailAlloc_920_; 
v_reuseFailAlloc_920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_920_, 0, v_a_914_);
v___x_919_ = v_reuseFailAlloc_920_;
goto v_reusejp_918_;
}
v_reusejp_918_:
{
return v___x_919_;
}
}
}
}
}
else
{
lean_object* v_a_922_; lean_object* v___x_924_; uint8_t v_isShared_925_; uint8_t v_isSharedCheck_929_; 
lean_dec(v_a_903_);
v_a_922_ = lean_ctor_get(v___x_904_, 0);
v_isSharedCheck_929_ = !lean_is_exclusive(v___x_904_);
if (v_isSharedCheck_929_ == 0)
{
v___x_924_ = v___x_904_;
v_isShared_925_ = v_isSharedCheck_929_;
goto v_resetjp_923_;
}
else
{
lean_inc(v_a_922_);
lean_dec(v___x_904_);
v___x_924_ = lean_box(0);
v_isShared_925_ = v_isSharedCheck_929_;
goto v_resetjp_923_;
}
v_resetjp_923_:
{
lean_object* v___x_927_; 
if (v_isShared_925_ == 0)
{
v___x_927_ = v___x_924_;
goto v_reusejp_926_;
}
else
{
lean_object* v_reuseFailAlloc_928_; 
v_reuseFailAlloc_928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_928_, 0, v_a_922_);
v___x_927_ = v_reuseFailAlloc_928_;
goto v_reusejp_926_;
}
v_reusejp_926_:
{
return v___x_927_;
}
}
}
}
else
{
lean_object* v_a_930_; lean_object* v___x_932_; uint8_t v_isShared_933_; uint8_t v_isSharedCheck_937_; 
lean_dec_ref(v_a_892_);
v_a_930_ = lean_ctor_get(v___x_902_, 0);
v_isSharedCheck_937_ = !lean_is_exclusive(v___x_902_);
if (v_isSharedCheck_937_ == 0)
{
v___x_932_ = v___x_902_;
v_isShared_933_ = v_isSharedCheck_937_;
goto v_resetjp_931_;
}
else
{
lean_inc(v_a_930_);
lean_dec(v___x_902_);
v___x_932_ = lean_box(0);
v_isShared_933_ = v_isSharedCheck_937_;
goto v_resetjp_931_;
}
v_resetjp_931_:
{
lean_object* v___x_935_; 
if (v_isShared_933_ == 0)
{
v___x_935_ = v___x_932_;
goto v_reusejp_934_;
}
else
{
lean_object* v_reuseFailAlloc_936_; 
v_reuseFailAlloc_936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_936_, 0, v_a_930_);
v___x_935_ = v_reuseFailAlloc_936_;
goto v_reusejp_934_;
}
v_reusejp_934_:
{
return v___x_935_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Conv_evalLiftLets___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_892_ = stack[0].m_obj;
lean_object* v___y_893_ = stack[1].m_obj;
lean_object* v___y_894_ = stack[2].m_obj;
lean_object* v___y_895_ = stack[3].m_obj;
lean_object* v___y_896_ = stack[4].m_obj;
lean_object* v___y_897_ = stack[5].m_obj;
lean_object* v___y_898_ = stack[6].m_obj;
lean_object* v___y_899_ = stack[7].m_obj;
lean_object* v___y_900_ = stack[8].m_obj;
lean_object* v_res_938_;
v_res_938_ = l_Lean_Elab_Tactic_Conv_evalLiftLets___lam__0(v_a_892_, v___y_893_, v___y_894_, v___y_895_, v___y_896_, v___y_897_, v___y_898_, v___y_899_, v___y_900_);
stack->m_obj
 = v_res_938_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalLiftLets___lam__0___boxed(lean_object* v_a_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_){
_start:
{
lean_object* v_res_949_; 
v_res_949_ = l_Lean_Elab_Tactic_Conv_evalLiftLets___lam__0(v_a_939_, v___y_940_, v___y_941_, v___y_942_, v___y_943_, v___y_944_, v___y_945_, v___y_946_, v___y_947_);
lean_dec(v___y_947_);
lean_dec_ref(v___y_946_);
lean_dec(v___y_945_);
lean_dec_ref(v___y_944_);
lean_dec(v___y_943_);
lean_dec_ref(v___y_942_);
lean_dec(v___y_941_);
lean_dec_ref(v___y_940_);
return v_res_949_;
}
}
lean_object* l_Lean_Elab_Tactic_Conv_evalLiftLets(lean_object* v_x_957_, lean_object* v_a_958_, lean_object* v_a_959_, lean_object* v_a_960_, lean_object* v_a_961_, lean_object* v_a_962_, lean_object* v_a_963_, lean_object* v_a_964_, lean_object* v_a_965_){
_start:
{
lean_object* v___x_967_; uint8_t v___x_968_; 
v___x_967_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalLiftLets___closed__1));
lean_inc(v_x_957_);
v___x_968_ = l_Lean_Syntax_isOfKind(v_x_957_, v___x_967_);
if (v___x_968_ == 0)
{
lean_object* v___x_969_; 
lean_dec(v_x_957_);
v___x_969_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__0___redArg();
return v___x_969_;
}
else
{
lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; uint8_t v___x_973_; 
v___x_970_ = lean_unsigned_to_nat(1u);
v___x_971_ = l_Lean_Syntax_getArg(v_x_957_, v___x_970_);
lean_dec(v_x_957_);
v___x_972_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__7));
lean_inc(v___x_971_);
v___x_973_ = l_Lean_Syntax_isOfKind(v___x_971_, v___x_972_);
if (v___x_973_ == 0)
{
lean_object* v___x_974_; 
lean_dec(v___x_971_);
v___x_974_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__0___redArg();
return v___x_974_;
}
else
{
uint8_t v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; 
v___x_975_ = 0;
v___x_976_ = lean_alloc_ctor(0, 0, 11);
lean_ctor_set_uint8(v___x_976_, 0, v___x_975_);
lean_ctor_set_uint8(v___x_976_, 1, v___x_973_);
lean_ctor_set_uint8(v___x_976_, 2, v___x_975_);
lean_ctor_set_uint8(v___x_976_, 3, v___x_973_);
lean_ctor_set_uint8(v___x_976_, 4, v___x_973_);
lean_ctor_set_uint8(v___x_976_, 5, v___x_975_);
lean_ctor_set_uint8(v___x_976_, 6, v___x_973_);
lean_ctor_set_uint8(v___x_976_, 7, v___x_973_);
lean_ctor_set_uint8(v___x_976_, 8, v___x_975_);
lean_ctor_set_uint8(v___x_976_, 9, v___x_973_);
lean_ctor_set_uint8(v___x_976_, 10, v___x_973_);
v___x_977_ = l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg(v___x_971_, v___x_976_, v___x_973_, v_a_958_, v_a_964_, v_a_965_);
if (lean_obj_tag(v___x_977_) == 0)
{
lean_object* v_a_978_; lean_object* v___f_979_; lean_object* v___x_980_; 
v_a_978_ = lean_ctor_get(v___x_977_, 0);
lean_inc(v_a_978_);
lean_dec_ref_known(v___x_977_, 1);
v___f_979_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalLiftLets___lam__0___boxed), 10, 1);
lean_closure_set(v___f_979_, 0, v_a_978_);
v___x_980_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_979_, v_a_958_, v_a_959_, v_a_960_, v_a_961_, v_a_962_, v_a_963_, v_a_964_, v_a_965_);
return v___x_980_;
}
else
{
lean_object* v_a_981_; lean_object* v___x_983_; uint8_t v_isShared_984_; uint8_t v_isSharedCheck_988_; 
v_a_981_ = lean_ctor_get(v___x_977_, 0);
v_isSharedCheck_988_ = !lean_is_exclusive(v___x_977_);
if (v_isSharedCheck_988_ == 0)
{
v___x_983_ = v___x_977_;
v_isShared_984_ = v_isSharedCheck_988_;
goto v_resetjp_982_;
}
else
{
lean_inc(v_a_981_);
lean_dec(v___x_977_);
v___x_983_ = lean_box(0);
v_isShared_984_ = v_isSharedCheck_988_;
goto v_resetjp_982_;
}
v_resetjp_982_:
{
lean_object* v___x_986_; 
if (v_isShared_984_ == 0)
{
v___x_986_ = v___x_983_;
goto v_reusejp_985_;
}
else
{
lean_object* v_reuseFailAlloc_987_; 
v_reuseFailAlloc_987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_987_, 0, v_a_981_);
v___x_986_ = v_reuseFailAlloc_987_;
goto v_reusejp_985_;
}
v_reusejp_985_:
{
return v___x_986_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Conv_evalLiftLets_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_957_ = stack[0].m_obj;
lean_object* v_a_958_ = stack[1].m_obj;
lean_object* v_a_959_ = stack[2].m_obj;
lean_object* v_a_960_ = stack[3].m_obj;
lean_object* v_a_961_ = stack[4].m_obj;
lean_object* v_a_962_ = stack[5].m_obj;
lean_object* v_a_963_ = stack[6].m_obj;
lean_object* v_a_964_ = stack[7].m_obj;
lean_object* v_a_965_ = stack[8].m_obj;
lean_object* v_res_989_;
v_res_989_ = l_Lean_Elab_Tactic_Conv_evalLiftLets(v_x_957_, v_a_958_, v_a_959_, v_a_960_, v_a_961_, v_a_962_, v_a_963_, v_a_964_, v_a_965_);
stack->m_obj
 = v_res_989_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalLiftLets___boxed(lean_object* v_x_990_, lean_object* v_a_991_, lean_object* v_a_992_, lean_object* v_a_993_, lean_object* v_a_994_, lean_object* v_a_995_, lean_object* v_a_996_, lean_object* v_a_997_, lean_object* v_a_998_, lean_object* v_a_999_){
_start:
{
lean_object* v_res_1000_; 
v_res_1000_ = l_Lean_Elab_Tactic_Conv_evalLiftLets(v_x_990_, v_a_991_, v_a_992_, v_a_993_, v_a_994_, v_a_995_, v_a_996_, v_a_997_, v_a_998_);
lean_dec(v_a_998_);
lean_dec_ref(v_a_997_);
lean_dec(v_a_996_);
lean_dec_ref(v_a_995_);
lean_dec(v_a_994_);
lean_dec_ref(v_a_993_);
lean_dec(v_a_992_);
lean_dec_ref(v_a_991_);
return v_res_1000_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLiftLets___regBuiltin_Lean_Elab_Tactic_Conv_evalLiftLets__1(){
_start:
{
lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; 
v___x_1009_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_1010_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalLiftLets___closed__1));
v___x_1011_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLiftLets___regBuiltin_Lean_Elab_Tactic_Conv_evalLiftLets__1___closed__1));
v___x_1012_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalLiftLets___boxed), 10, 0);
v___x_1013_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1009_, v___x_1010_, v___x_1011_, v___x_1012_);
return v___x_1013_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLiftLets___regBuiltin_Lean_Elab_Tactic_Conv_evalLiftLets__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1014_;
v_res_1014_ = l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLiftLets___regBuiltin_Lean_Elab_Tactic_Conv_evalLiftLets__1();
stack->m_obj
 = v_res_1014_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLiftLets___regBuiltin_Lean_Elab_Tactic_Conv_evalLiftLets__1___boxed(lean_object* v_a_1015_){
_start:
{
lean_object* v_res_1016_; 
v_res_1016_ = l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLiftLets___regBuiltin_Lean_Elab_Tactic_Conv_evalLiftLets__1();
return v_res_1016_;
}
}
lean_object* l_Lean_Elab_Tactic_Conv_evalLetToHave___lam__0(lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_){
_start:
{
lean_object* v___x_1029_; 
v___x_1029_ = l_Lean_Elab_Tactic_Conv_getLhs___redArg(v___y_1021_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_);
if (lean_obj_tag(v___x_1029_) == 0)
{
lean_object* v_a_1030_; lean_object* v___x_1031_; 
v_a_1030_ = lean_ctor_get(v___x_1029_, 0);
lean_inc_n(v_a_1030_, 2);
lean_dec_ref_known(v___x_1029_, 1);
v___x_1031_ = l_Lean_Meta_letToHave(v_a_1030_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_);
if (lean_obj_tag(v___x_1031_) == 0)
{
lean_object* v_a_1032_; uint8_t v___x_1033_; 
v_a_1032_ = lean_ctor_get(v___x_1031_, 0);
lean_inc(v_a_1032_);
lean_dec_ref_known(v___x_1031_, 1);
v___x_1033_ = lean_expr_eqv(v_a_1030_, v_a_1032_);
lean_dec(v_a_1030_);
if (v___x_1033_ == 0)
{
lean_object* v___x_1034_; 
v___x_1034_ = l_Lean_Elab_Tactic_Conv_changeLhs(v_a_1032_, v___y_1020_, v___y_1021_, v___y_1022_, v___y_1023_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_);
return v___x_1034_;
}
else
{
lean_object* v___x_1035_; 
v___x_1035_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_1021_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_);
if (lean_obj_tag(v___x_1035_) == 0)
{
lean_object* v_a_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; 
v_a_1036_ = lean_ctor_get(v___x_1035_, 0);
lean_inc(v_a_1036_);
lean_dec_ref_known(v___x_1035_, 1);
v___x_1037_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalLetToHave___lam__0___closed__1));
v___x_1038_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2___closed__2, &l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2___closed__2_once, _init_l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2___closed__2);
v___x_1039_ = l_Lean_Meta_throwTacticEx___redArg(v___x_1037_, v_a_1036_, v___x_1038_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_);
if (lean_obj_tag(v___x_1039_) == 0)
{
lean_object* v___x_1040_; 
lean_dec_ref_known(v___x_1039_, 1);
v___x_1040_ = l_Lean_Elab_Tactic_Conv_changeLhs(v_a_1032_, v___y_1020_, v___y_1021_, v___y_1022_, v___y_1023_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_);
return v___x_1040_;
}
else
{
lean_dec(v_a_1032_);
return v___x_1039_;
}
}
else
{
lean_object* v_a_1041_; lean_object* v___x_1043_; uint8_t v_isShared_1044_; uint8_t v_isSharedCheck_1048_; 
lean_dec(v_a_1032_);
v_a_1041_ = lean_ctor_get(v___x_1035_, 0);
v_isSharedCheck_1048_ = !lean_is_exclusive(v___x_1035_);
if (v_isSharedCheck_1048_ == 0)
{
v___x_1043_ = v___x_1035_;
v_isShared_1044_ = v_isSharedCheck_1048_;
goto v_resetjp_1042_;
}
else
{
lean_inc(v_a_1041_);
lean_dec(v___x_1035_);
v___x_1043_ = lean_box(0);
v_isShared_1044_ = v_isSharedCheck_1048_;
goto v_resetjp_1042_;
}
v_resetjp_1042_:
{
lean_object* v___x_1046_; 
if (v_isShared_1044_ == 0)
{
v___x_1046_ = v___x_1043_;
goto v_reusejp_1045_;
}
else
{
lean_object* v_reuseFailAlloc_1047_; 
v_reuseFailAlloc_1047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1047_, 0, v_a_1041_);
v___x_1046_ = v_reuseFailAlloc_1047_;
goto v_reusejp_1045_;
}
v_reusejp_1045_:
{
return v___x_1046_;
}
}
}
}
}
else
{
lean_object* v_a_1049_; lean_object* v___x_1051_; uint8_t v_isShared_1052_; uint8_t v_isSharedCheck_1056_; 
lean_dec(v_a_1030_);
v_a_1049_ = lean_ctor_get(v___x_1031_, 0);
v_isSharedCheck_1056_ = !lean_is_exclusive(v___x_1031_);
if (v_isSharedCheck_1056_ == 0)
{
v___x_1051_ = v___x_1031_;
v_isShared_1052_ = v_isSharedCheck_1056_;
goto v_resetjp_1050_;
}
else
{
lean_inc(v_a_1049_);
lean_dec(v___x_1031_);
v___x_1051_ = lean_box(0);
v_isShared_1052_ = v_isSharedCheck_1056_;
goto v_resetjp_1050_;
}
v_resetjp_1050_:
{
lean_object* v___x_1054_; 
if (v_isShared_1052_ == 0)
{
v___x_1054_ = v___x_1051_;
goto v_reusejp_1053_;
}
else
{
lean_object* v_reuseFailAlloc_1055_; 
v_reuseFailAlloc_1055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1055_, 0, v_a_1049_);
v___x_1054_ = v_reuseFailAlloc_1055_;
goto v_reusejp_1053_;
}
v_reusejp_1053_:
{
return v___x_1054_;
}
}
}
}
else
{
lean_object* v_a_1057_; lean_object* v___x_1059_; uint8_t v_isShared_1060_; uint8_t v_isSharedCheck_1064_; 
v_a_1057_ = lean_ctor_get(v___x_1029_, 0);
v_isSharedCheck_1064_ = !lean_is_exclusive(v___x_1029_);
if (v_isSharedCheck_1064_ == 0)
{
v___x_1059_ = v___x_1029_;
v_isShared_1060_ = v_isSharedCheck_1064_;
goto v_resetjp_1058_;
}
else
{
lean_inc(v_a_1057_);
lean_dec(v___x_1029_);
v___x_1059_ = lean_box(0);
v_isShared_1060_ = v_isSharedCheck_1064_;
goto v_resetjp_1058_;
}
v_resetjp_1058_:
{
lean_object* v___x_1062_; 
if (v_isShared_1060_ == 0)
{
v___x_1062_ = v___x_1059_;
goto v_reusejp_1061_;
}
else
{
lean_object* v_reuseFailAlloc_1063_; 
v_reuseFailAlloc_1063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1063_, 0, v_a_1057_);
v___x_1062_ = v_reuseFailAlloc_1063_;
goto v_reusejp_1061_;
}
v_reusejp_1061_:
{
return v___x_1062_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Conv_evalLetToHave___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_1020_ = stack[0].m_obj;
lean_object* v___y_1021_ = stack[1].m_obj;
lean_object* v___y_1022_ = stack[2].m_obj;
lean_object* v___y_1023_ = stack[3].m_obj;
lean_object* v___y_1024_ = stack[4].m_obj;
lean_object* v___y_1025_ = stack[5].m_obj;
lean_object* v___y_1026_ = stack[6].m_obj;
lean_object* v___y_1027_ = stack[7].m_obj;
lean_object* v_res_1065_;
v_res_1065_ = l_Lean_Elab_Tactic_Conv_evalLetToHave___lam__0(v___y_1020_, v___y_1021_, v___y_1022_, v___y_1023_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_);
stack->m_obj
 = v_res_1065_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalLetToHave___lam__0___boxed(lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_){
_start:
{
lean_object* v_res_1075_; 
v_res_1075_ = l_Lean_Elab_Tactic_Conv_evalLetToHave___lam__0(v___y_1066_, v___y_1067_, v___y_1068_, v___y_1069_, v___y_1070_, v___y_1071_, v___y_1072_, v___y_1073_);
lean_dec(v___y_1073_);
lean_dec_ref(v___y_1072_);
lean_dec(v___y_1071_);
lean_dec_ref(v___y_1070_);
lean_dec(v___y_1069_);
lean_dec_ref(v___y_1068_);
lean_dec(v___y_1067_);
lean_dec_ref(v___y_1066_);
return v_res_1075_;
}
}
lean_object* l_Lean_Elab_Tactic_Conv_evalLetToHave(lean_object* v_x_1084_, lean_object* v_a_1085_, lean_object* v_a_1086_, lean_object* v_a_1087_, lean_object* v_a_1088_, lean_object* v_a_1089_, lean_object* v_a_1090_, lean_object* v_a_1091_, lean_object* v_a_1092_){
_start:
{
lean_object* v___x_1094_; uint8_t v___x_1095_; 
v___x_1094_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalLetToHave___closed__1));
v___x_1095_ = l_Lean_Syntax_isOfKind(v_x_1084_, v___x_1094_);
if (v___x_1095_ == 0)
{
lean_object* v___x_1096_; 
v___x_1096_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__0___redArg();
return v___x_1096_;
}
else
{
lean_object* v___f_1097_; lean_object* v___x_1098_; 
v___f_1097_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalLetToHave___closed__2));
v___x_1098_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_1097_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_, v_a_1092_);
return v___x_1098_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Conv_evalLetToHave_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1084_ = stack[0].m_obj;
lean_object* v_a_1085_ = stack[1].m_obj;
lean_object* v_a_1086_ = stack[2].m_obj;
lean_object* v_a_1087_ = stack[3].m_obj;
lean_object* v_a_1088_ = stack[4].m_obj;
lean_object* v_a_1089_ = stack[5].m_obj;
lean_object* v_a_1090_ = stack[6].m_obj;
lean_object* v_a_1091_ = stack[7].m_obj;
lean_object* v_a_1092_ = stack[8].m_obj;
lean_object* v_res_1099_;
v_res_1099_ = l_Lean_Elab_Tactic_Conv_evalLetToHave(v_x_1084_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_, v_a_1092_);
stack->m_obj
 = v_res_1099_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalLetToHave___boxed(lean_object* v_x_1100_, lean_object* v_a_1101_, lean_object* v_a_1102_, lean_object* v_a_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_, lean_object* v_a_1108_, lean_object* v_a_1109_){
_start:
{
lean_object* v_res_1110_; 
v_res_1110_ = l_Lean_Elab_Tactic_Conv_evalLetToHave(v_x_1100_, v_a_1101_, v_a_1102_, v_a_1103_, v_a_1104_, v_a_1105_, v_a_1106_, v_a_1107_, v_a_1108_);
lean_dec(v_a_1108_);
lean_dec_ref(v_a_1107_);
lean_dec(v_a_1106_);
lean_dec_ref(v_a_1105_);
lean_dec(v_a_1104_);
lean_dec_ref(v_a_1103_);
lean_dec(v_a_1102_);
lean_dec_ref(v_a_1101_);
return v_res_1110_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLetToHave___regBuiltin_Lean_Elab_Tactic_Conv_evalLetToHave__1(){
_start:
{
lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; 
v___x_1119_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_1120_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalLetToHave___closed__1));
v___x_1121_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLetToHave___regBuiltin_Lean_Elab_Tactic_Conv_evalLetToHave__1___closed__1));
v___x_1122_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalLetToHave___boxed), 10, 0);
v___x_1123_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1119_, v___x_1120_, v___x_1121_, v___x_1122_);
return v___x_1123_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLetToHave___regBuiltin_Lean_Elab_Tactic_Conv_evalLetToHave__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1124_;
v_res_1124_ = l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLetToHave___regBuiltin_Lean_Elab_Tactic_Conv_evalLetToHave__1();
stack->m_obj
 = v_res_1124_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLetToHave___regBuiltin_Lean_Elab_Tactic_Conv_evalLetToHave__1___boxed(lean_object* v_a_1125_){
_start:
{
lean_object* v_res_1126_; 
v_res_1126_ = l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLetToHave___regBuiltin_Lean_Elab_Tactic_Conv_evalLetToHave__1();
return v_res_1126_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_Lets(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Conv_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Conv_Lets(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Elab_Tactic_Lets(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Conv_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalExtractLets___regBuiltin_Lean_Elab_Tactic_Conv_evalExtractLets__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLiftLets___regBuiltin_Lean_Elab_Tactic_Conv_evalLiftLets__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLetToHave___regBuiltin_Lean_Elab_Tactic_Conv_evalLetToHave__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_Conv_Lets(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Tactic_Lets(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Conv_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Conv_Lets(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Tactic_Lets(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Conv_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Conv_Lets(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_Conv_Lets(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_Conv_Lets(builtin);
}
#ifdef __cplusplus
}
#endif
