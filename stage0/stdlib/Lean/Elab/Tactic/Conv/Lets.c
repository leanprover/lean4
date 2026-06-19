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
lean_object* l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Conv_getLhsRhs___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Elab_Tactic_getNameOfIdent_x27(lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_MVarId_checkNotAssigned(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
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
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
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
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___redArg___closed__2;
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2(lean_object*, lean_object*, size_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "extract_lets"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__3___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__3___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(104, 33, 143, 120, 246, 234, 114, 64)}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__3___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__3___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__3(lean_object*, size_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__0___redArg(){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_5_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__0___redArg___closed__0);
v___x_6_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6_, 0, v___x_5_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__0___redArg___boxed(lean_object* v___y_7_){
_start:
{
lean_object* v_res_8_; 
v_res_8_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__0___redArg();
return v_res_8_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__0(lean_object* v_00_u03b1_9_, lean_object* v___y_10_, lean_object* v___y_11_, lean_object* v___y_12_, lean_object* v___y_13_, lean_object* v___y_14_, lean_object* v___y_15_, lean_object* v___y_16_, lean_object* v___y_17_){
_start:
{
lean_object* v___x_19_; 
v___x_19_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__0___redArg();
return v___x_19_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__0___boxed(lean_object* v_00_u03b1_20_, lean_object* v___y_21_, lean_object* v___y_22_, lean_object* v___y_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_, lean_object* v___y_28_, lean_object* v___y_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__0(v_00_u03b1_20_, v___y_21_, v___y_22_, v___y_23_, v___y_24_, v___y_25_, v___y_26_, v___y_27_, v___y_28_);
lean_dec(v___y_28_);
lean_dec_ref(v___y_27_);
lean_dec(v___y_26_);
lean_dec_ref(v___y_25_);
lean_dec(v___y_24_);
lean_dec_ref(v___y_23_);
lean_dec(v___y_22_);
lean_dec_ref(v___y_21_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__4___redArg(lean_object* v_mvarId_31_, lean_object* v_x_32_, lean_object* v___y_33_, lean_object* v___y_34_, lean_object* v___y_35_, lean_object* v___y_36_){
_start:
{
lean_object* v___x_38_; 
v___x_38_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_31_, v_x_32_, v___y_33_, v___y_34_, v___y_35_, v___y_36_);
if (lean_obj_tag(v___x_38_) == 0)
{
lean_object* v_a_39_; lean_object* v___x_41_; uint8_t v_isShared_42_; uint8_t v_isSharedCheck_46_; 
v_a_39_ = lean_ctor_get(v___x_38_, 0);
v_isSharedCheck_46_ = !lean_is_exclusive(v___x_38_);
if (v_isSharedCheck_46_ == 0)
{
v___x_41_ = v___x_38_;
v_isShared_42_ = v_isSharedCheck_46_;
goto v_resetjp_40_;
}
else
{
lean_inc(v_a_39_);
lean_dec(v___x_38_);
v___x_41_ = lean_box(0);
v_isShared_42_ = v_isSharedCheck_46_;
goto v_resetjp_40_;
}
v_resetjp_40_:
{
lean_object* v___x_44_; 
if (v_isShared_42_ == 0)
{
v___x_44_ = v___x_41_;
goto v_reusejp_43_;
}
else
{
lean_object* v_reuseFailAlloc_45_; 
v_reuseFailAlloc_45_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_45_, 0, v_a_39_);
v___x_44_ = v_reuseFailAlloc_45_;
goto v_reusejp_43_;
}
v_reusejp_43_:
{
return v___x_44_;
}
}
}
else
{
lean_object* v_a_47_; lean_object* v___x_49_; uint8_t v_isShared_50_; uint8_t v_isSharedCheck_54_; 
v_a_47_ = lean_ctor_get(v___x_38_, 0);
v_isSharedCheck_54_ = !lean_is_exclusive(v___x_38_);
if (v_isSharedCheck_54_ == 0)
{
v___x_49_ = v___x_38_;
v_isShared_50_ = v_isSharedCheck_54_;
goto v_resetjp_48_;
}
else
{
lean_inc(v_a_47_);
lean_dec(v___x_38_);
v___x_49_ = lean_box(0);
v_isShared_50_ = v_isSharedCheck_54_;
goto v_resetjp_48_;
}
v_resetjp_48_:
{
lean_object* v___x_52_; 
if (v_isShared_50_ == 0)
{
v___x_52_ = v___x_49_;
goto v_reusejp_51_;
}
else
{
lean_object* v_reuseFailAlloc_53_; 
v_reuseFailAlloc_53_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_53_, 0, v_a_47_);
v___x_52_ = v_reuseFailAlloc_53_;
goto v_reusejp_51_;
}
v_reusejp_51_:
{
return v___x_52_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__4___redArg___boxed(lean_object* v_mvarId_55_, lean_object* v_x_56_, lean_object* v___y_57_, lean_object* v___y_58_, lean_object* v___y_59_, lean_object* v___y_60_, lean_object* v___y_61_){
_start:
{
lean_object* v_res_62_; 
v_res_62_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__4___redArg(v_mvarId_55_, v_x_56_, v___y_57_, v___y_58_, v___y_59_, v___y_60_);
lean_dec(v___y_60_);
lean_dec_ref(v___y_59_);
lean_dec(v___y_58_);
lean_dec_ref(v___y_57_);
return v_res_62_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__4(lean_object* v_00_u03b1_63_, lean_object* v_mvarId_64_, lean_object* v_x_65_, lean_object* v___y_66_, lean_object* v___y_67_, lean_object* v___y_68_, lean_object* v___y_69_){
_start:
{
lean_object* v___x_71_; 
v___x_71_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__4___redArg(v_mvarId_64_, v_x_65_, v___y_66_, v___y_67_, v___y_68_, v___y_69_);
return v___x_71_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__4___boxed(lean_object* v_00_u03b1_72_, lean_object* v_mvarId_73_, lean_object* v_x_74_, lean_object* v___y_75_, lean_object* v___y_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_){
_start:
{
lean_object* v_res_80_; 
v_res_80_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__4(v_00_u03b1_72_, v_mvarId_73_, v_x_74_, v___y_75_, v___y_76_, v___y_77_, v___y_78_);
lean_dec(v___y_78_);
lean_dec_ref(v___y_77_);
lean_dec(v___y_76_);
lean_dec_ref(v___y_75_);
return v_res_80_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__5___redArg___lam__0(lean_object* v_k_81_, lean_object* v_b_82_, lean_object* v_c_83_, lean_object* v_d_84_, lean_object* v___y_85_, lean_object* v___y_86_, lean_object* v___y_87_, lean_object* v___y_88_){
_start:
{
lean_object* v___x_90_; 
lean_inc(v___y_88_);
lean_inc_ref(v___y_87_);
lean_inc(v___y_86_);
lean_inc_ref(v___y_85_);
v___x_90_ = lean_apply_8(v_k_81_, v_b_82_, v_c_83_, v_d_84_, v___y_85_, v___y_86_, v___y_87_, v___y_88_, lean_box(0));
return v___x_90_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__5___redArg___lam__0___boxed(lean_object* v_k_91_, lean_object* v_b_92_, lean_object* v_c_93_, lean_object* v_d_94_, lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_, lean_object* v___y_99_){
_start:
{
lean_object* v_res_100_; 
v_res_100_ = l_Lean_Meta_extractLets___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__5___redArg___lam__0(v_k_91_, v_b_92_, v_c_93_, v_d_94_, v___y_95_, v___y_96_, v___y_97_, v___y_98_);
lean_dec(v___y_98_);
lean_dec_ref(v___y_97_);
lean_dec(v___y_96_);
lean_dec_ref(v___y_95_);
return v_res_100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__5___redArg(lean_object* v_es_101_, lean_object* v_givenNames_102_, lean_object* v_k_103_, lean_object* v_config_104_, lean_object* v___y_105_, lean_object* v___y_106_, lean_object* v___y_107_, lean_object* v___y_108_){
_start:
{
lean_object* v___f_110_; lean_object* v___x_111_; 
v___f_110_ = lean_alloc_closure((void*)(l_Lean_Meta_extractLets___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__5___redArg___lam__0___boxed), 9, 1);
lean_closure_set(v___f_110_, 0, v_k_103_);
v___x_111_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp(lean_box(0), v_es_101_, v_givenNames_102_, v___f_110_, v_config_104_, v___y_105_, v___y_106_, v___y_107_, v___y_108_);
if (lean_obj_tag(v___x_111_) == 0)
{
lean_object* v_a_112_; lean_object* v___x_114_; uint8_t v_isShared_115_; uint8_t v_isSharedCheck_119_; 
v_a_112_ = lean_ctor_get(v___x_111_, 0);
v_isSharedCheck_119_ = !lean_is_exclusive(v___x_111_);
if (v_isSharedCheck_119_ == 0)
{
v___x_114_ = v___x_111_;
v_isShared_115_ = v_isSharedCheck_119_;
goto v_resetjp_113_;
}
else
{
lean_inc(v_a_112_);
lean_dec(v___x_111_);
v___x_114_ = lean_box(0);
v_isShared_115_ = v_isSharedCheck_119_;
goto v_resetjp_113_;
}
v_resetjp_113_:
{
lean_object* v___x_117_; 
if (v_isShared_115_ == 0)
{
v___x_117_ = v___x_114_;
goto v_reusejp_116_;
}
else
{
lean_object* v_reuseFailAlloc_118_; 
v_reuseFailAlloc_118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_118_, 0, v_a_112_);
v___x_117_ = v_reuseFailAlloc_118_;
goto v_reusejp_116_;
}
v_reusejp_116_:
{
return v___x_117_;
}
}
}
else
{
lean_object* v_a_120_; lean_object* v___x_122_; uint8_t v_isShared_123_; uint8_t v_isSharedCheck_127_; 
v_a_120_ = lean_ctor_get(v___x_111_, 0);
v_isSharedCheck_127_ = !lean_is_exclusive(v___x_111_);
if (v_isSharedCheck_127_ == 0)
{
v___x_122_ = v___x_111_;
v_isShared_123_ = v_isSharedCheck_127_;
goto v_resetjp_121_;
}
else
{
lean_inc(v_a_120_);
lean_dec(v___x_111_);
v___x_122_ = lean_box(0);
v_isShared_123_ = v_isSharedCheck_127_;
goto v_resetjp_121_;
}
v_resetjp_121_:
{
lean_object* v___x_125_; 
if (v_isShared_123_ == 0)
{
v___x_125_ = v___x_122_;
goto v_reusejp_124_;
}
else
{
lean_object* v_reuseFailAlloc_126_; 
v_reuseFailAlloc_126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_126_, 0, v_a_120_);
v___x_125_ = v_reuseFailAlloc_126_;
goto v_reusejp_124_;
}
v_reusejp_124_:
{
return v___x_125_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__5___redArg___boxed(lean_object* v_es_128_, lean_object* v_givenNames_129_, lean_object* v_k_130_, lean_object* v_config_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_){
_start:
{
lean_object* v_res_137_; 
v_res_137_ = l_Lean_Meta_extractLets___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__5___redArg(v_es_128_, v_givenNames_129_, v_k_130_, v_config_131_, v___y_132_, v___y_133_, v___y_134_, v___y_135_);
lean_dec(v___y_135_);
lean_dec_ref(v___y_134_);
lean_dec(v___y_133_);
lean_dec_ref(v___y_132_);
lean_dec_ref(v_config_131_);
return v_res_137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__5(lean_object* v_00_u03b1_138_, lean_object* v_es_139_, lean_object* v_givenNames_140_, lean_object* v_k_141_, lean_object* v_config_142_, lean_object* v___y_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_){
_start:
{
lean_object* v___x_148_; 
v___x_148_ = l_Lean_Meta_extractLets___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__5___redArg(v_es_139_, v_givenNames_140_, v_k_141_, v_config_142_, v___y_143_, v___y_144_, v___y_145_, v___y_146_);
return v___x_148_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__5___boxed(lean_object* v_00_u03b1_149_, lean_object* v_es_150_, lean_object* v_givenNames_151_, lean_object* v_k_152_, lean_object* v_config_153_, lean_object* v___y_154_, lean_object* v___y_155_, lean_object* v___y_156_, lean_object* v___y_157_, lean_object* v___y_158_){
_start:
{
lean_object* v_res_159_; 
v_res_159_ = l_Lean_Meta_extractLets___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__5(v_00_u03b1_149_, v_es_150_, v_givenNames_151_, v_k_152_, v_config_153_, v___y_154_, v___y_155_, v___y_156_, v___y_157_);
lean_dec(v___y_157_);
lean_dec_ref(v___y_156_);
lean_dec(v___y_155_);
lean_dec_ref(v___y_154_);
lean_dec_ref(v_config_153_);
return v_res_159_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6_spec__7_spec__8___redArg(lean_object* v_x_160_, lean_object* v_x_161_, lean_object* v_x_162_, lean_object* v_x_163_){
_start:
{
lean_object* v_ks_164_; lean_object* v_vs_165_; lean_object* v___x_167_; uint8_t v_isShared_168_; uint8_t v_isSharedCheck_189_; 
v_ks_164_ = lean_ctor_get(v_x_160_, 0);
v_vs_165_ = lean_ctor_get(v_x_160_, 1);
v_isSharedCheck_189_ = !lean_is_exclusive(v_x_160_);
if (v_isSharedCheck_189_ == 0)
{
v___x_167_ = v_x_160_;
v_isShared_168_ = v_isSharedCheck_189_;
goto v_resetjp_166_;
}
else
{
lean_inc(v_vs_165_);
lean_inc(v_ks_164_);
lean_dec(v_x_160_);
v___x_167_ = lean_box(0);
v_isShared_168_ = v_isSharedCheck_189_;
goto v_resetjp_166_;
}
v_resetjp_166_:
{
lean_object* v___x_169_; uint8_t v___x_170_; 
v___x_169_ = lean_array_get_size(v_ks_164_);
v___x_170_ = lean_nat_dec_lt(v_x_161_, v___x_169_);
if (v___x_170_ == 0)
{
lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_174_; 
lean_dec(v_x_161_);
v___x_171_ = lean_array_push(v_ks_164_, v_x_162_);
v___x_172_ = lean_array_push(v_vs_165_, v_x_163_);
if (v_isShared_168_ == 0)
{
lean_ctor_set(v___x_167_, 1, v___x_172_);
lean_ctor_set(v___x_167_, 0, v___x_171_);
v___x_174_ = v___x_167_;
goto v_reusejp_173_;
}
else
{
lean_object* v_reuseFailAlloc_175_; 
v_reuseFailAlloc_175_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_175_, 0, v___x_171_);
lean_ctor_set(v_reuseFailAlloc_175_, 1, v___x_172_);
v___x_174_ = v_reuseFailAlloc_175_;
goto v_reusejp_173_;
}
v_reusejp_173_:
{
return v___x_174_;
}
}
else
{
lean_object* v_k_x27_176_; uint8_t v___x_177_; 
v_k_x27_176_ = lean_array_fget_borrowed(v_ks_164_, v_x_161_);
v___x_177_ = l_Lean_instBEqMVarId_beq(v_x_162_, v_k_x27_176_);
if (v___x_177_ == 0)
{
lean_object* v___x_179_; 
if (v_isShared_168_ == 0)
{
v___x_179_ = v___x_167_;
goto v_reusejp_178_;
}
else
{
lean_object* v_reuseFailAlloc_183_; 
v_reuseFailAlloc_183_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_183_, 0, v_ks_164_);
lean_ctor_set(v_reuseFailAlloc_183_, 1, v_vs_165_);
v___x_179_ = v_reuseFailAlloc_183_;
goto v_reusejp_178_;
}
v_reusejp_178_:
{
lean_object* v___x_180_; lean_object* v___x_181_; 
v___x_180_ = lean_unsigned_to_nat(1u);
v___x_181_ = lean_nat_add(v_x_161_, v___x_180_);
lean_dec(v_x_161_);
v_x_160_ = v___x_179_;
v_x_161_ = v___x_181_;
goto _start;
}
}
else
{
lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_187_; 
v___x_184_ = lean_array_fset(v_ks_164_, v_x_161_, v_x_162_);
v___x_185_ = lean_array_fset(v_vs_165_, v_x_161_, v_x_163_);
lean_dec(v_x_161_);
if (v_isShared_168_ == 0)
{
lean_ctor_set(v___x_167_, 1, v___x_185_);
lean_ctor_set(v___x_167_, 0, v___x_184_);
v___x_187_ = v___x_167_;
goto v_reusejp_186_;
}
else
{
lean_object* v_reuseFailAlloc_188_; 
v_reuseFailAlloc_188_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_188_, 0, v___x_184_);
lean_ctor_set(v_reuseFailAlloc_188_, 1, v___x_185_);
v___x_187_ = v_reuseFailAlloc_188_;
goto v_reusejp_186_;
}
v_reusejp_186_:
{
return v___x_187_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6_spec__7___redArg(lean_object* v_n_190_, lean_object* v_k_191_, lean_object* v_v_192_){
_start:
{
lean_object* v___x_193_; lean_object* v___x_194_; 
v___x_193_ = lean_unsigned_to_nat(0u);
v___x_194_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6_spec__7_spec__8___redArg(v_n_190_, v___x_193_, v_k_191_, v_v_192_);
return v___x_194_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___redArg___closed__0(void){
_start:
{
size_t v___x_195_; size_t v___x_196_; size_t v___x_197_; 
v___x_195_ = ((size_t)5ULL);
v___x_196_ = ((size_t)1ULL);
v___x_197_ = lean_usize_shift_left(v___x_196_, v___x_195_);
return v___x_197_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___redArg___closed__1(void){
_start:
{
size_t v___x_198_; size_t v___x_199_; size_t v___x_200_; 
v___x_198_ = ((size_t)1ULL);
v___x_199_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___redArg___closed__0);
v___x_200_ = lean_usize_sub(v___x_199_, v___x_198_);
return v___x_200_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___redArg___closed__2(void){
_start:
{
lean_object* v___x_201_; 
v___x_201_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_201_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___redArg(lean_object* v_x_202_, size_t v_x_203_, size_t v_x_204_, lean_object* v_x_205_, lean_object* v_x_206_){
_start:
{
if (lean_obj_tag(v_x_202_) == 0)
{
lean_object* v_es_207_; size_t v___x_208_; size_t v___x_209_; size_t v___x_210_; size_t v___x_211_; lean_object* v_j_212_; lean_object* v___x_213_; uint8_t v___x_214_; 
v_es_207_ = lean_ctor_get(v_x_202_, 0);
v___x_208_ = ((size_t)5ULL);
v___x_209_ = ((size_t)1ULL);
v___x_210_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___redArg___closed__1);
v___x_211_ = lean_usize_land(v_x_203_, v___x_210_);
v_j_212_ = lean_usize_to_nat(v___x_211_);
v___x_213_ = lean_array_get_size(v_es_207_);
v___x_214_ = lean_nat_dec_lt(v_j_212_, v___x_213_);
if (v___x_214_ == 0)
{
lean_dec(v_j_212_);
lean_dec(v_x_206_);
lean_dec(v_x_205_);
return v_x_202_;
}
else
{
lean_object* v___x_216_; uint8_t v_isShared_217_; uint8_t v_isSharedCheck_251_; 
lean_inc_ref(v_es_207_);
v_isSharedCheck_251_ = !lean_is_exclusive(v_x_202_);
if (v_isSharedCheck_251_ == 0)
{
lean_object* v_unused_252_; 
v_unused_252_ = lean_ctor_get(v_x_202_, 0);
lean_dec(v_unused_252_);
v___x_216_ = v_x_202_;
v_isShared_217_ = v_isSharedCheck_251_;
goto v_resetjp_215_;
}
else
{
lean_dec(v_x_202_);
v___x_216_ = lean_box(0);
v_isShared_217_ = v_isSharedCheck_251_;
goto v_resetjp_215_;
}
v_resetjp_215_:
{
lean_object* v_v_218_; lean_object* v___x_219_; lean_object* v_xs_x27_220_; lean_object* v___y_222_; 
v_v_218_ = lean_array_fget(v_es_207_, v_j_212_);
v___x_219_ = lean_box(0);
v_xs_x27_220_ = lean_array_fset(v_es_207_, v_j_212_, v___x_219_);
switch(lean_obj_tag(v_v_218_))
{
case 0:
{
lean_object* v_key_227_; lean_object* v_val_228_; lean_object* v___x_230_; uint8_t v_isShared_231_; uint8_t v_isSharedCheck_238_; 
v_key_227_ = lean_ctor_get(v_v_218_, 0);
v_val_228_ = lean_ctor_get(v_v_218_, 1);
v_isSharedCheck_238_ = !lean_is_exclusive(v_v_218_);
if (v_isSharedCheck_238_ == 0)
{
v___x_230_ = v_v_218_;
v_isShared_231_ = v_isSharedCheck_238_;
goto v_resetjp_229_;
}
else
{
lean_inc(v_val_228_);
lean_inc(v_key_227_);
lean_dec(v_v_218_);
v___x_230_ = lean_box(0);
v_isShared_231_ = v_isSharedCheck_238_;
goto v_resetjp_229_;
}
v_resetjp_229_:
{
uint8_t v___x_232_; 
v___x_232_ = l_Lean_instBEqMVarId_beq(v_x_205_, v_key_227_);
if (v___x_232_ == 0)
{
lean_object* v___x_233_; lean_object* v___x_234_; 
lean_del_object(v___x_230_);
v___x_233_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_227_, v_val_228_, v_x_205_, v_x_206_);
v___x_234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_234_, 0, v___x_233_);
v___y_222_ = v___x_234_;
goto v___jp_221_;
}
else
{
lean_object* v___x_236_; 
lean_dec(v_val_228_);
lean_dec(v_key_227_);
if (v_isShared_231_ == 0)
{
lean_ctor_set(v___x_230_, 1, v_x_206_);
lean_ctor_set(v___x_230_, 0, v_x_205_);
v___x_236_ = v___x_230_;
goto v_reusejp_235_;
}
else
{
lean_object* v_reuseFailAlloc_237_; 
v_reuseFailAlloc_237_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_237_, 0, v_x_205_);
lean_ctor_set(v_reuseFailAlloc_237_, 1, v_x_206_);
v___x_236_ = v_reuseFailAlloc_237_;
goto v_reusejp_235_;
}
v_reusejp_235_:
{
v___y_222_ = v___x_236_;
goto v___jp_221_;
}
}
}
}
case 1:
{
lean_object* v_node_239_; lean_object* v___x_241_; uint8_t v_isShared_242_; uint8_t v_isSharedCheck_249_; 
v_node_239_ = lean_ctor_get(v_v_218_, 0);
v_isSharedCheck_249_ = !lean_is_exclusive(v_v_218_);
if (v_isSharedCheck_249_ == 0)
{
v___x_241_ = v_v_218_;
v_isShared_242_ = v_isSharedCheck_249_;
goto v_resetjp_240_;
}
else
{
lean_inc(v_node_239_);
lean_dec(v_v_218_);
v___x_241_ = lean_box(0);
v_isShared_242_ = v_isSharedCheck_249_;
goto v_resetjp_240_;
}
v_resetjp_240_:
{
size_t v___x_243_; size_t v___x_244_; lean_object* v___x_245_; lean_object* v___x_247_; 
v___x_243_ = lean_usize_shift_right(v_x_203_, v___x_208_);
v___x_244_ = lean_usize_add(v_x_204_, v___x_209_);
v___x_245_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___redArg(v_node_239_, v___x_243_, v___x_244_, v_x_205_, v_x_206_);
if (v_isShared_242_ == 0)
{
lean_ctor_set(v___x_241_, 0, v___x_245_);
v___x_247_ = v___x_241_;
goto v_reusejp_246_;
}
else
{
lean_object* v_reuseFailAlloc_248_; 
v_reuseFailAlloc_248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_248_, 0, v___x_245_);
v___x_247_ = v_reuseFailAlloc_248_;
goto v_reusejp_246_;
}
v_reusejp_246_:
{
v___y_222_ = v___x_247_;
goto v___jp_221_;
}
}
}
default: 
{
lean_object* v___x_250_; 
v___x_250_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_250_, 0, v_x_205_);
lean_ctor_set(v___x_250_, 1, v_x_206_);
v___y_222_ = v___x_250_;
goto v___jp_221_;
}
}
v___jp_221_:
{
lean_object* v___x_223_; lean_object* v___x_225_; 
v___x_223_ = lean_array_fset(v_xs_x27_220_, v_j_212_, v___y_222_);
lean_dec(v_j_212_);
if (v_isShared_217_ == 0)
{
lean_ctor_set(v___x_216_, 0, v___x_223_);
v___x_225_ = v___x_216_;
goto v_reusejp_224_;
}
else
{
lean_object* v_reuseFailAlloc_226_; 
v_reuseFailAlloc_226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_226_, 0, v___x_223_);
v___x_225_ = v_reuseFailAlloc_226_;
goto v_reusejp_224_;
}
v_reusejp_224_:
{
return v___x_225_;
}
}
}
}
}
else
{
lean_object* v_ks_253_; lean_object* v_vs_254_; lean_object* v___x_256_; uint8_t v_isShared_257_; uint8_t v_isSharedCheck_274_; 
v_ks_253_ = lean_ctor_get(v_x_202_, 0);
v_vs_254_ = lean_ctor_get(v_x_202_, 1);
v_isSharedCheck_274_ = !lean_is_exclusive(v_x_202_);
if (v_isSharedCheck_274_ == 0)
{
v___x_256_ = v_x_202_;
v_isShared_257_ = v_isSharedCheck_274_;
goto v_resetjp_255_;
}
else
{
lean_inc(v_vs_254_);
lean_inc(v_ks_253_);
lean_dec(v_x_202_);
v___x_256_ = lean_box(0);
v_isShared_257_ = v_isSharedCheck_274_;
goto v_resetjp_255_;
}
v_resetjp_255_:
{
lean_object* v___x_259_; 
if (v_isShared_257_ == 0)
{
v___x_259_ = v___x_256_;
goto v_reusejp_258_;
}
else
{
lean_object* v_reuseFailAlloc_273_; 
v_reuseFailAlloc_273_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_273_, 0, v_ks_253_);
lean_ctor_set(v_reuseFailAlloc_273_, 1, v_vs_254_);
v___x_259_ = v_reuseFailAlloc_273_;
goto v_reusejp_258_;
}
v_reusejp_258_:
{
lean_object* v_newNode_260_; uint8_t v___y_262_; size_t v___x_268_; uint8_t v___x_269_; 
v_newNode_260_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6_spec__7___redArg(v___x_259_, v_x_205_, v_x_206_);
v___x_268_ = ((size_t)7ULL);
v___x_269_ = lean_usize_dec_le(v___x_268_, v_x_204_);
if (v___x_269_ == 0)
{
lean_object* v___x_270_; lean_object* v___x_271_; uint8_t v___x_272_; 
v___x_270_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_260_);
v___x_271_ = lean_unsigned_to_nat(4u);
v___x_272_ = lean_nat_dec_lt(v___x_270_, v___x_271_);
lean_dec(v___x_270_);
v___y_262_ = v___x_272_;
goto v___jp_261_;
}
else
{
v___y_262_ = v___x_269_;
goto v___jp_261_;
}
v___jp_261_:
{
if (v___y_262_ == 0)
{
lean_object* v_ks_263_; lean_object* v_vs_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; 
v_ks_263_ = lean_ctor_get(v_newNode_260_, 0);
lean_inc_ref(v_ks_263_);
v_vs_264_ = lean_ctor_get(v_newNode_260_, 1);
lean_inc_ref(v_vs_264_);
lean_dec_ref(v_newNode_260_);
v___x_265_ = lean_unsigned_to_nat(0u);
v___x_266_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___redArg___closed__2);
v___x_267_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6_spec__8___redArg(v_x_204_, v_ks_263_, v_vs_264_, v___x_265_, v___x_266_);
lean_dec_ref(v_vs_264_);
lean_dec_ref(v_ks_263_);
return v___x_267_;
}
else
{
return v_newNode_260_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6_spec__8___redArg(size_t v_depth_275_, lean_object* v_keys_276_, lean_object* v_vals_277_, lean_object* v_i_278_, lean_object* v_entries_279_){
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
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6_spec__8___redArg___boxed(lean_object* v_depth_295_, lean_object* v_keys_296_, lean_object* v_vals_297_, lean_object* v_i_298_, lean_object* v_entries_299_){
_start:
{
size_t v_depth_boxed_300_; lean_object* v_res_301_; 
v_depth_boxed_300_ = lean_unbox_usize(v_depth_295_);
lean_dec(v_depth_295_);
v_res_301_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6_spec__8___redArg(v_depth_boxed_300_, v_keys_296_, v_vals_297_, v_i_298_, v_entries_299_);
lean_dec_ref(v_vals_297_);
lean_dec_ref(v_keys_296_);
return v_res_301_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___redArg___boxed(lean_object* v_x_302_, lean_object* v_x_303_, lean_object* v_x_304_, lean_object* v_x_305_, lean_object* v_x_306_){
_start:
{
size_t v_x_6152__boxed_307_; size_t v_x_6153__boxed_308_; lean_object* v_res_309_; 
v_x_6152__boxed_307_ = lean_unbox_usize(v_x_303_);
lean_dec(v_x_303_);
v_x_6153__boxed_308_ = lean_unbox_usize(v_x_304_);
lean_dec(v_x_304_);
v_res_309_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___redArg(v_x_302_, v_x_6152__boxed_307_, v_x_6153__boxed_308_, v_x_305_, v_x_306_);
return v_res_309_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3___redArg(lean_object* v_x_310_, lean_object* v_x_311_, lean_object* v_x_312_){
_start:
{
uint64_t v___x_313_; size_t v___x_314_; size_t v___x_315_; lean_object* v___x_316_; 
v___x_313_ = l_Lean_instHashableMVarId_hash(v_x_311_);
v___x_314_ = lean_uint64_to_usize(v___x_313_);
v___x_315_ = ((size_t)1ULL);
v___x_316_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___redArg(v_x_310_, v___x_314_, v___x_315_, v_x_311_, v_x_312_);
return v___x_316_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3___redArg(lean_object* v_mvarId_317_, lean_object* v_val_318_, lean_object* v___y_319_){
_start:
{
lean_object* v___x_321_; lean_object* v_mctx_322_; lean_object* v_cache_323_; lean_object* v_zetaDeltaFVarIds_324_; lean_object* v_postponed_325_; lean_object* v_diag_326_; lean_object* v___x_328_; uint8_t v_isShared_329_; uint8_t v_isSharedCheck_354_; 
v___x_321_ = lean_st_ref_take(v___y_319_);
v_mctx_322_ = lean_ctor_get(v___x_321_, 0);
v_cache_323_ = lean_ctor_get(v___x_321_, 1);
v_zetaDeltaFVarIds_324_ = lean_ctor_get(v___x_321_, 2);
v_postponed_325_ = lean_ctor_get(v___x_321_, 3);
v_diag_326_ = lean_ctor_get(v___x_321_, 4);
v_isSharedCheck_354_ = !lean_is_exclusive(v___x_321_);
if (v_isSharedCheck_354_ == 0)
{
v___x_328_ = v___x_321_;
v_isShared_329_ = v_isSharedCheck_354_;
goto v_resetjp_327_;
}
else
{
lean_inc(v_diag_326_);
lean_inc(v_postponed_325_);
lean_inc(v_zetaDeltaFVarIds_324_);
lean_inc(v_cache_323_);
lean_inc(v_mctx_322_);
lean_dec(v___x_321_);
v___x_328_ = lean_box(0);
v_isShared_329_ = v_isSharedCheck_354_;
goto v_resetjp_327_;
}
v_resetjp_327_:
{
lean_object* v_depth_330_; lean_object* v_levelAssignDepth_331_; lean_object* v_lmvarCounter_332_; lean_object* v_mvarCounter_333_; lean_object* v_lDecls_334_; lean_object* v_decls_335_; lean_object* v_userNames_336_; lean_object* v_lAssignment_337_; lean_object* v_eAssignment_338_; lean_object* v_dAssignment_339_; lean_object* v___x_341_; uint8_t v_isShared_342_; uint8_t v_isSharedCheck_353_; 
v_depth_330_ = lean_ctor_get(v_mctx_322_, 0);
v_levelAssignDepth_331_ = lean_ctor_get(v_mctx_322_, 1);
v_lmvarCounter_332_ = lean_ctor_get(v_mctx_322_, 2);
v_mvarCounter_333_ = lean_ctor_get(v_mctx_322_, 3);
v_lDecls_334_ = lean_ctor_get(v_mctx_322_, 4);
v_decls_335_ = lean_ctor_get(v_mctx_322_, 5);
v_userNames_336_ = lean_ctor_get(v_mctx_322_, 6);
v_lAssignment_337_ = lean_ctor_get(v_mctx_322_, 7);
v_eAssignment_338_ = lean_ctor_get(v_mctx_322_, 8);
v_dAssignment_339_ = lean_ctor_get(v_mctx_322_, 9);
v_isSharedCheck_353_ = !lean_is_exclusive(v_mctx_322_);
if (v_isSharedCheck_353_ == 0)
{
v___x_341_ = v_mctx_322_;
v_isShared_342_ = v_isSharedCheck_353_;
goto v_resetjp_340_;
}
else
{
lean_inc(v_dAssignment_339_);
lean_inc(v_eAssignment_338_);
lean_inc(v_lAssignment_337_);
lean_inc(v_userNames_336_);
lean_inc(v_decls_335_);
lean_inc(v_lDecls_334_);
lean_inc(v_mvarCounter_333_);
lean_inc(v_lmvarCounter_332_);
lean_inc(v_levelAssignDepth_331_);
lean_inc(v_depth_330_);
lean_dec(v_mctx_322_);
v___x_341_ = lean_box(0);
v_isShared_342_ = v_isSharedCheck_353_;
goto v_resetjp_340_;
}
v_resetjp_340_:
{
lean_object* v___x_343_; lean_object* v___x_345_; 
v___x_343_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3___redArg(v_eAssignment_338_, v_mvarId_317_, v_val_318_);
if (v_isShared_342_ == 0)
{
lean_ctor_set(v___x_341_, 8, v___x_343_);
v___x_345_ = v___x_341_;
goto v_reusejp_344_;
}
else
{
lean_object* v_reuseFailAlloc_352_; 
v_reuseFailAlloc_352_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_352_, 0, v_depth_330_);
lean_ctor_set(v_reuseFailAlloc_352_, 1, v_levelAssignDepth_331_);
lean_ctor_set(v_reuseFailAlloc_352_, 2, v_lmvarCounter_332_);
lean_ctor_set(v_reuseFailAlloc_352_, 3, v_mvarCounter_333_);
lean_ctor_set(v_reuseFailAlloc_352_, 4, v_lDecls_334_);
lean_ctor_set(v_reuseFailAlloc_352_, 5, v_decls_335_);
lean_ctor_set(v_reuseFailAlloc_352_, 6, v_userNames_336_);
lean_ctor_set(v_reuseFailAlloc_352_, 7, v_lAssignment_337_);
lean_ctor_set(v_reuseFailAlloc_352_, 8, v___x_343_);
lean_ctor_set(v_reuseFailAlloc_352_, 9, v_dAssignment_339_);
v___x_345_ = v_reuseFailAlloc_352_;
goto v_reusejp_344_;
}
v_reusejp_344_:
{
lean_object* v___x_347_; 
if (v_isShared_329_ == 0)
{
lean_ctor_set(v___x_328_, 0, v___x_345_);
v___x_347_ = v___x_328_;
goto v_reusejp_346_;
}
else
{
lean_object* v_reuseFailAlloc_351_; 
v_reuseFailAlloc_351_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_351_, 0, v___x_345_);
lean_ctor_set(v_reuseFailAlloc_351_, 1, v_cache_323_);
lean_ctor_set(v_reuseFailAlloc_351_, 2, v_zetaDeltaFVarIds_324_);
lean_ctor_set(v_reuseFailAlloc_351_, 3, v_postponed_325_);
lean_ctor_set(v_reuseFailAlloc_351_, 4, v_diag_326_);
v___x_347_ = v_reuseFailAlloc_351_;
goto v_reusejp_346_;
}
v_reusejp_346_:
{
lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; 
v___x_348_ = lean_st_ref_set(v___y_319_, v___x_347_);
v___x_349_ = lean_box(0);
v___x_350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_350_, 0, v___x_349_);
return v___x_350_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3___redArg___boxed(lean_object* v_mvarId_355_, lean_object* v_val_356_, lean_object* v___y_357_, lean_object* v___y_358_){
_start:
{
lean_object* v_res_359_; 
v_res_359_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3___redArg(v_mvarId_355_, v_val_356_, v___y_357_);
lean_dec(v___y_357_);
return v_res_359_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__0___closed__1(void){
_start:
{
lean_object* v___x_361_; lean_object* v___x_362_; 
v___x_361_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__0___closed__0));
v___x_362_ = l_Lean_stringToMessageData(v___x_361_);
return v___x_362_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__0___closed__2(void){
_start:
{
lean_object* v___x_363_; lean_object* v___x_364_; 
v___x_363_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__0___closed__1, &l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__0___closed__1);
v___x_364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_364_, 0, v___x_363_);
return v___x_364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__0(lean_object* v___x_365_, lean_object* v_a_366_, lean_object* v___x_367_, lean_object* v_a_368_, lean_object* v_mvar_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_){
_start:
{
lean_object* v___x_375_; 
lean_inc_ref(v_a_366_);
v___x_375_ = l_Lean_Meta_isExprDefEq(v___x_365_, v_a_366_, v___y_370_, v___y_371_, v___y_372_, v___y_373_);
if (lean_obj_tag(v___x_375_) == 0)
{
lean_object* v_a_376_; uint8_t v___x_377_; 
v_a_376_ = lean_ctor_get(v___x_375_, 0);
lean_inc(v_a_376_);
lean_dec_ref_known(v___x_375_, 1);
v___x_377_ = lean_unbox(v_a_376_);
lean_dec(v_a_376_);
if (v___x_377_ == 0)
{
lean_object* v___x_378_; lean_object* v___x_379_; 
v___x_378_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__0___closed__2, &l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__0___closed__2_once, _init_l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__0___closed__2);
v___x_379_ = l_Lean_Meta_throwTacticEx___redArg(v___x_367_, v_a_368_, v___x_378_, v___y_370_, v___y_371_, v___y_372_, v___y_373_);
if (lean_obj_tag(v___x_379_) == 0)
{
lean_object* v___x_380_; 
lean_dec_ref_known(v___x_379_, 1);
v___x_380_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3___redArg(v_mvar_369_, v_a_366_, v___y_371_);
return v___x_380_;
}
else
{
lean_dec(v_mvar_369_);
lean_dec_ref(v_a_366_);
return v___x_379_;
}
}
else
{
lean_object* v___x_381_; 
lean_dec(v_a_368_);
lean_dec(v___x_367_);
v___x_381_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3___redArg(v_mvar_369_, v_a_366_, v___y_371_);
return v___x_381_;
}
}
else
{
lean_object* v_a_382_; lean_object* v___x_384_; uint8_t v_isShared_385_; uint8_t v_isSharedCheck_389_; 
lean_dec(v_mvar_369_);
lean_dec(v_a_368_);
lean_dec(v___x_367_);
lean_dec_ref(v_a_366_);
v_a_382_ = lean_ctor_get(v___x_375_, 0);
v_isSharedCheck_389_ = !lean_is_exclusive(v___x_375_);
if (v_isSharedCheck_389_ == 0)
{
v___x_384_ = v___x_375_;
v_isShared_385_ = v_isSharedCheck_389_;
goto v_resetjp_383_;
}
else
{
lean_inc(v_a_382_);
lean_dec(v___x_375_);
v___x_384_ = lean_box(0);
v_isShared_385_ = v_isSharedCheck_389_;
goto v_resetjp_383_;
}
v_resetjp_383_:
{
lean_object* v___x_387_; 
if (v_isShared_385_ == 0)
{
v___x_387_ = v___x_384_;
goto v_reusejp_386_;
}
else
{
lean_object* v_reuseFailAlloc_388_; 
v_reuseFailAlloc_388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_388_, 0, v_a_382_);
v___x_387_ = v_reuseFailAlloc_388_;
goto v_reusejp_386_;
}
v_reusejp_386_:
{
return v___x_387_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__0___boxed(lean_object* v___x_390_, lean_object* v_a_391_, lean_object* v___x_392_, lean_object* v_a_393_, lean_object* v_mvar_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_){
_start:
{
lean_object* v_res_400_; 
v_res_400_ = l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__0(v___x_390_, v_a_391_, v___x_392_, v_a_393_, v_mvar_394_, v___y_395_, v___y_396_, v___y_397_, v___y_398_);
lean_dec(v___y_398_);
lean_dec_ref(v___y_397_);
lean_dec(v___y_396_);
lean_dec_ref(v___y_395_);
return v_res_400_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__1(lean_object* v___x_401_, uint8_t v___x_402_, uint8_t v___x_403_, lean_object* v___x_404_, lean_object* v_a_405_, lean_object* v_mvar_406_, lean_object* v_e_407_, lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_, lean_object* v___y_411_){
_start:
{
uint8_t v___x_413_; lean_object* v___x_414_; 
v___x_413_ = 1;
v___x_414_ = l_Lean_Meta_mkLetFVars(v___x_401_, v_e_407_, v___x_402_, v___x_403_, v___x_413_, v___y_408_, v___y_409_, v___y_410_, v___y_411_);
if (lean_obj_tag(v___x_414_) == 0)
{
lean_object* v_a_415_; lean_object* v___x_416_; lean_object* v___f_417_; lean_object* v___x_418_; 
v_a_415_ = lean_ctor_get(v___x_414_, 0);
lean_inc(v_a_415_);
lean_dec_ref_known(v___x_414_, 1);
lean_inc_n(v_mvar_406_, 2);
v___x_416_ = l_Lean_Expr_mvar___override(v_mvar_406_);
v___f_417_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__0___boxed), 10, 5);
lean_closure_set(v___f_417_, 0, v___x_416_);
lean_closure_set(v___f_417_, 1, v_a_415_);
lean_closure_set(v___f_417_, 2, v___x_404_);
lean_closure_set(v___f_417_, 3, v_a_405_);
lean_closure_set(v___f_417_, 4, v_mvar_406_);
v___x_418_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__4___redArg(v_mvar_406_, v___f_417_, v___y_408_, v___y_409_, v___y_410_, v___y_411_);
return v___x_418_;
}
else
{
lean_object* v_a_419_; lean_object* v___x_421_; uint8_t v_isShared_422_; uint8_t v_isSharedCheck_426_; 
lean_dec(v_mvar_406_);
lean_dec(v_a_405_);
lean_dec(v___x_404_);
v_a_419_ = lean_ctor_get(v___x_414_, 0);
v_isSharedCheck_426_ = !lean_is_exclusive(v___x_414_);
if (v_isSharedCheck_426_ == 0)
{
v___x_421_ = v___x_414_;
v_isShared_422_ = v_isSharedCheck_426_;
goto v_resetjp_420_;
}
else
{
lean_inc(v_a_419_);
lean_dec(v___x_414_);
v___x_421_ = lean_box(0);
v_isShared_422_ = v_isSharedCheck_426_;
goto v_resetjp_420_;
}
v_resetjp_420_:
{
lean_object* v___x_424_; 
if (v_isShared_422_ == 0)
{
v___x_424_ = v___x_421_;
goto v_reusejp_423_;
}
else
{
lean_object* v_reuseFailAlloc_425_; 
v_reuseFailAlloc_425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_425_, 0, v_a_419_);
v___x_424_ = v_reuseFailAlloc_425_;
goto v_reusejp_423_;
}
v_reusejp_423_:
{
return v___x_424_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__1___boxed(lean_object* v___x_427_, lean_object* v___x_428_, lean_object* v___x_429_, lean_object* v___x_430_, lean_object* v_a_431_, lean_object* v_mvar_432_, lean_object* v_e_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_){
_start:
{
uint8_t v___x_6446__boxed_439_; uint8_t v___x_6447__boxed_440_; lean_object* v_res_441_; 
v___x_6446__boxed_439_ = lean_unbox(v___x_428_);
v___x_6447__boxed_440_ = lean_unbox(v___x_429_);
v_res_441_ = l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__1(v___x_427_, v___x_6446__boxed_439_, v___x_6447__boxed_440_, v___x_430_, v_a_431_, v_mvar_432_, v_e_433_, v___y_434_, v___y_435_, v___y_436_, v___y_437_);
lean_dec(v___y_437_);
lean_dec_ref(v___y_436_);
lean_dec(v___y_435_);
lean_dec_ref(v___y_434_);
lean_dec_ref(v___x_427_);
return v_res_441_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__2(size_t v_sz_442_, size_t v_i_443_, lean_object* v_bs_444_){
_start:
{
uint8_t v___x_445_; 
v___x_445_ = lean_usize_dec_lt(v_i_443_, v_sz_442_);
if (v___x_445_ == 0)
{
return v_bs_444_;
}
else
{
lean_object* v_v_446_; lean_object* v___x_447_; lean_object* v_bs_x27_448_; lean_object* v___x_449_; size_t v___x_450_; size_t v___x_451_; lean_object* v___x_452_; 
v_v_446_ = lean_array_uget(v_bs_444_, v_i_443_);
v___x_447_ = lean_unsigned_to_nat(0u);
v_bs_x27_448_ = lean_array_uset(v_bs_444_, v_i_443_, v___x_447_);
v___x_449_ = l_Lean_Expr_fvar___override(v_v_446_);
v___x_450_ = ((size_t)1ULL);
v___x_451_ = lean_usize_add(v_i_443_, v___x_450_);
v___x_452_ = lean_array_uset(v_bs_x27_448_, v_i_443_, v___x_449_);
v_i_443_ = v___x_451_;
v_bs_444_ = v___x_452_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__2___boxed(lean_object* v_sz_454_, lean_object* v_i_455_, lean_object* v_bs_456_){
_start:
{
size_t v_sz_boxed_457_; size_t v_i_boxed_458_; lean_object* v_res_459_; 
v_sz_boxed_457_ = lean_unbox_usize(v_sz_454_);
lean_dec(v_sz_454_);
v_i_boxed_458_ = lean_unbox_usize(v_i_455_);
lean_dec(v_i_455_);
v_res_459_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__2(v_sz_boxed_457_, v_i_boxed_458_, v_bs_456_);
return v_res_459_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2___closed__1(void){
_start:
{
lean_object* v___x_461_; lean_object* v___x_462_; 
v___x_461_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2___closed__0));
v___x_462_ = l_Lean_stringToMessageData(v___x_461_);
return v___x_462_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2___closed__2(void){
_start:
{
lean_object* v___x_463_; lean_object* v___x_464_; 
v___x_463_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2___closed__1, &l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2___closed__1_once, _init_l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2___closed__1);
v___x_464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_464_, 0, v___x_463_);
return v___x_464_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2(lean_object* v___x_465_, lean_object* v_a_466_, size_t v___x_467_, uint8_t v___x_468_, uint8_t v___x_469_, lean_object* v___x_470_, lean_object* v_snd_471_, lean_object* v_fst_472_, lean_object* v_fvarIds_473_, lean_object* v_es_474_, lean_object* v_x_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_){
_start:
{
lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_545_; uint8_t v___x_546_; 
v___x_481_ = l_Lean_instInhabitedExpr;
v___x_482_ = lean_array_get_borrowed(v___x_481_, v_es_474_, v___x_465_);
v___x_545_ = lean_array_get_size(v_fvarIds_473_);
v___x_546_ = lean_nat_dec_eq(v___x_545_, v___x_465_);
if (v___x_546_ == 0)
{
goto v___jp_483_;
}
else
{
uint8_t v___x_547_; 
v___x_547_ = lean_expr_eqv(v_fst_472_, v___x_482_);
if (v___x_547_ == 0)
{
goto v___jp_483_;
}
else
{
lean_object* v___x_548_; lean_object* v___x_549_; 
v___x_548_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2___closed__2, &l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2___closed__2_once, _init_l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2___closed__2);
lean_inc(v_a_466_);
lean_inc(v___x_470_);
v___x_549_ = l_Lean_Meta_throwTacticEx___redArg(v___x_470_, v_a_466_, v___x_548_, v___y_476_, v___y_477_, v___y_478_, v___y_479_);
if (lean_obj_tag(v___x_549_) == 0)
{
lean_dec_ref_known(v___x_549_, 1);
goto v___jp_483_;
}
else
{
lean_object* v_a_550_; lean_object* v___x_552_; uint8_t v_isShared_553_; uint8_t v_isSharedCheck_557_; 
lean_dec_ref(v_fvarIds_473_);
lean_dec_ref(v_snd_471_);
lean_dec(v___x_470_);
lean_dec(v_a_466_);
v_a_550_ = lean_ctor_get(v___x_549_, 0);
v_isSharedCheck_557_ = !lean_is_exclusive(v___x_549_);
if (v_isSharedCheck_557_ == 0)
{
v___x_552_ = v___x_549_;
v_isShared_553_ = v_isSharedCheck_557_;
goto v_resetjp_551_;
}
else
{
lean_inc(v_a_550_);
lean_dec(v___x_549_);
v___x_552_ = lean_box(0);
v_isShared_553_ = v_isSharedCheck_557_;
goto v_resetjp_551_;
}
v_resetjp_551_:
{
lean_object* v___x_555_; 
if (v_isShared_553_ == 0)
{
v___x_555_ = v___x_552_;
goto v_reusejp_554_;
}
else
{
lean_object* v_reuseFailAlloc_556_; 
v_reuseFailAlloc_556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_556_, 0, v_a_550_);
v___x_555_ = v_reuseFailAlloc_556_;
goto v_reusejp_554_;
}
v_reusejp_554_:
{
return v___x_555_;
}
}
}
}
}
v___jp_483_:
{
lean_object* v___x_484_; 
lean_inc(v_a_466_);
v___x_484_ = l_Lean_MVarId_getTag(v_a_466_, v___y_476_, v___y_477_, v___y_478_, v___y_479_);
if (lean_obj_tag(v___x_484_) == 0)
{
lean_object* v_a_485_; lean_object* v___x_486_; 
v_a_485_ = lean_ctor_get(v___x_484_, 0);
lean_inc(v_a_485_);
lean_dec_ref_known(v___x_484_, 1);
lean_inc(v___x_482_);
v___x_486_ = l_Lean_Elab_Tactic_Conv_mkConvGoalFor(v___x_482_, v_a_485_, v___y_476_, v___y_477_, v___y_478_, v___y_479_);
if (lean_obj_tag(v___x_486_) == 0)
{
lean_object* v_a_487_; lean_object* v_fst_488_; lean_object* v_snd_489_; lean_object* v___x_491_; uint8_t v_isShared_492_; uint8_t v_isSharedCheck_528_; 
v_a_487_ = lean_ctor_get(v___x_486_, 0);
lean_inc(v_a_487_);
lean_dec_ref_known(v___x_486_, 1);
v_fst_488_ = lean_ctor_get(v_a_487_, 0);
v_snd_489_ = lean_ctor_get(v_a_487_, 1);
v_isSharedCheck_528_ = !lean_is_exclusive(v_a_487_);
if (v_isSharedCheck_528_ == 0)
{
v___x_491_ = v_a_487_;
v_isShared_492_ = v_isSharedCheck_528_;
goto v_resetjp_490_;
}
else
{
lean_inc(v_snd_489_);
lean_inc(v_fst_488_);
lean_dec(v_a_487_);
v___x_491_ = lean_box(0);
v_isShared_492_ = v_isSharedCheck_528_;
goto v_resetjp_490_;
}
v_resetjp_490_:
{
size_t v_sz_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; 
v_sz_493_ = lean_array_size(v_fvarIds_473_);
lean_inc_ref(v_fvarIds_473_);
v___x_494_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__2(v_sz_493_, v___x_467_, v_fvarIds_473_);
v___x_495_ = l_Lean_Expr_mvarId_x21(v_fst_488_);
lean_dec(v_fst_488_);
lean_inc(v_a_466_);
lean_inc(v___x_470_);
v___x_496_ = l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__1(v___x_494_, v___x_468_, v___x_469_, v___x_470_, v_a_466_, v___x_495_, v_snd_471_, v___y_476_, v___y_477_, v___y_478_, v___y_479_);
if (lean_obj_tag(v___x_496_) == 0)
{
lean_object* v___x_497_; 
lean_dec_ref_known(v___x_496_, 1);
lean_inc(v_snd_489_);
lean_inc(v_a_466_);
v___x_497_ = l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__1(v___x_494_, v___x_468_, v___x_469_, v___x_470_, v_a_466_, v_a_466_, v_snd_489_, v___y_476_, v___y_477_, v___y_478_, v___y_479_);
lean_dec_ref(v___x_494_);
if (lean_obj_tag(v___x_497_) == 0)
{
lean_object* v___x_499_; uint8_t v_isShared_500_; uint8_t v_isSharedCheck_510_; 
v_isSharedCheck_510_ = !lean_is_exclusive(v___x_497_);
if (v_isSharedCheck_510_ == 0)
{
lean_object* v_unused_511_; 
v_unused_511_ = lean_ctor_get(v___x_497_, 0);
lean_dec(v_unused_511_);
v___x_499_ = v___x_497_;
v_isShared_500_ = v_isSharedCheck_510_;
goto v_resetjp_498_;
}
else
{
lean_dec(v___x_497_);
v___x_499_ = lean_box(0);
v_isShared_500_ = v_isSharedCheck_510_;
goto v_resetjp_498_;
}
v_resetjp_498_:
{
lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_505_; 
v___x_501_ = l_Lean_Expr_mvarId_x21(v_snd_489_);
lean_dec(v_snd_489_);
v___x_502_ = lean_box(0);
v___x_503_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_503_, 0, v___x_501_);
lean_ctor_set(v___x_503_, 1, v___x_502_);
if (v_isShared_492_ == 0)
{
lean_ctor_set(v___x_491_, 1, v___x_503_);
lean_ctor_set(v___x_491_, 0, v_fvarIds_473_);
v___x_505_ = v___x_491_;
goto v_reusejp_504_;
}
else
{
lean_object* v_reuseFailAlloc_509_; 
v_reuseFailAlloc_509_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_509_, 0, v_fvarIds_473_);
lean_ctor_set(v_reuseFailAlloc_509_, 1, v___x_503_);
v___x_505_ = v_reuseFailAlloc_509_;
goto v_reusejp_504_;
}
v_reusejp_504_:
{
lean_object* v___x_507_; 
if (v_isShared_500_ == 0)
{
lean_ctor_set(v___x_499_, 0, v___x_505_);
v___x_507_ = v___x_499_;
goto v_reusejp_506_;
}
else
{
lean_object* v_reuseFailAlloc_508_; 
v_reuseFailAlloc_508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_508_, 0, v___x_505_);
v___x_507_ = v_reuseFailAlloc_508_;
goto v_reusejp_506_;
}
v_reusejp_506_:
{
return v___x_507_;
}
}
}
}
else
{
lean_object* v_a_512_; lean_object* v___x_514_; uint8_t v_isShared_515_; uint8_t v_isSharedCheck_519_; 
lean_del_object(v___x_491_);
lean_dec(v_snd_489_);
lean_dec_ref(v_fvarIds_473_);
v_a_512_ = lean_ctor_get(v___x_497_, 0);
v_isSharedCheck_519_ = !lean_is_exclusive(v___x_497_);
if (v_isSharedCheck_519_ == 0)
{
v___x_514_ = v___x_497_;
v_isShared_515_ = v_isSharedCheck_519_;
goto v_resetjp_513_;
}
else
{
lean_inc(v_a_512_);
lean_dec(v___x_497_);
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
else
{
lean_object* v_a_520_; lean_object* v___x_522_; uint8_t v_isShared_523_; uint8_t v_isSharedCheck_527_; 
lean_dec_ref(v___x_494_);
lean_del_object(v___x_491_);
lean_dec(v_snd_489_);
lean_dec_ref(v_fvarIds_473_);
lean_dec(v___x_470_);
lean_dec(v_a_466_);
v_a_520_ = lean_ctor_get(v___x_496_, 0);
v_isSharedCheck_527_ = !lean_is_exclusive(v___x_496_);
if (v_isSharedCheck_527_ == 0)
{
v___x_522_ = v___x_496_;
v_isShared_523_ = v_isSharedCheck_527_;
goto v_resetjp_521_;
}
else
{
lean_inc(v_a_520_);
lean_dec(v___x_496_);
v___x_522_ = lean_box(0);
v_isShared_523_ = v_isSharedCheck_527_;
goto v_resetjp_521_;
}
v_resetjp_521_:
{
lean_object* v___x_525_; 
if (v_isShared_523_ == 0)
{
v___x_525_ = v___x_522_;
goto v_reusejp_524_;
}
else
{
lean_object* v_reuseFailAlloc_526_; 
v_reuseFailAlloc_526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_526_, 0, v_a_520_);
v___x_525_ = v_reuseFailAlloc_526_;
goto v_reusejp_524_;
}
v_reusejp_524_:
{
return v___x_525_;
}
}
}
}
}
else
{
lean_object* v_a_529_; lean_object* v___x_531_; uint8_t v_isShared_532_; uint8_t v_isSharedCheck_536_; 
lean_dec_ref(v_fvarIds_473_);
lean_dec_ref(v_snd_471_);
lean_dec(v___x_470_);
lean_dec(v_a_466_);
v_a_529_ = lean_ctor_get(v___x_486_, 0);
v_isSharedCheck_536_ = !lean_is_exclusive(v___x_486_);
if (v_isSharedCheck_536_ == 0)
{
v___x_531_ = v___x_486_;
v_isShared_532_ = v_isSharedCheck_536_;
goto v_resetjp_530_;
}
else
{
lean_inc(v_a_529_);
lean_dec(v___x_486_);
v___x_531_ = lean_box(0);
v_isShared_532_ = v_isSharedCheck_536_;
goto v_resetjp_530_;
}
v_resetjp_530_:
{
lean_object* v___x_534_; 
if (v_isShared_532_ == 0)
{
v___x_534_ = v___x_531_;
goto v_reusejp_533_;
}
else
{
lean_object* v_reuseFailAlloc_535_; 
v_reuseFailAlloc_535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_535_, 0, v_a_529_);
v___x_534_ = v_reuseFailAlloc_535_;
goto v_reusejp_533_;
}
v_reusejp_533_:
{
return v___x_534_;
}
}
}
}
else
{
lean_object* v_a_537_; lean_object* v___x_539_; uint8_t v_isShared_540_; uint8_t v_isSharedCheck_544_; 
lean_dec_ref(v_fvarIds_473_);
lean_dec_ref(v_snd_471_);
lean_dec(v___x_470_);
lean_dec(v_a_466_);
v_a_537_ = lean_ctor_get(v___x_484_, 0);
v_isSharedCheck_544_ = !lean_is_exclusive(v___x_484_);
if (v_isSharedCheck_544_ == 0)
{
v___x_539_ = v___x_484_;
v_isShared_540_ = v_isSharedCheck_544_;
goto v_resetjp_538_;
}
else
{
lean_inc(v_a_537_);
lean_dec(v___x_484_);
v___x_539_ = lean_box(0);
v_isShared_540_ = v_isSharedCheck_544_;
goto v_resetjp_538_;
}
v_resetjp_538_:
{
lean_object* v___x_542_; 
if (v_isShared_540_ == 0)
{
v___x_542_ = v___x_539_;
goto v_reusejp_541_;
}
else
{
lean_object* v_reuseFailAlloc_543_; 
v_reuseFailAlloc_543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_543_, 0, v_a_537_);
v___x_542_ = v_reuseFailAlloc_543_;
goto v_reusejp_541_;
}
v_reusejp_541_:
{
return v___x_542_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2___boxed(lean_object* v___x_558_, lean_object* v_a_559_, lean_object* v___x_560_, lean_object* v___x_561_, lean_object* v___x_562_, lean_object* v___x_563_, lean_object* v_snd_564_, lean_object* v_fst_565_, lean_object* v_fvarIds_566_, lean_object* v_es_567_, lean_object* v_x_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_){
_start:
{
size_t v___x_6529__boxed_574_; uint8_t v___x_6530__boxed_575_; uint8_t v___x_6531__boxed_576_; lean_object* v_res_577_; 
v___x_6529__boxed_574_ = lean_unbox_usize(v___x_560_);
lean_dec(v___x_560_);
v___x_6530__boxed_575_ = lean_unbox(v___x_561_);
v___x_6531__boxed_576_ = lean_unbox(v___x_562_);
v_res_577_ = l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2(v___x_558_, v_a_559_, v___x_6529__boxed_574_, v___x_6530__boxed_575_, v___x_6531__boxed_576_, v___x_563_, v_snd_564_, v_fst_565_, v_fvarIds_566_, v_es_567_, v_x_568_, v___y_569_, v___y_570_, v___y_571_, v___y_572_);
lean_dec(v___y_572_);
lean_dec_ref(v___y_571_);
lean_dec(v___y_570_);
lean_dec_ref(v___y_569_);
lean_dec(v_x_568_);
lean_dec_ref(v_es_567_);
lean_dec_ref(v_fst_565_);
lean_dec(v___x_558_);
return v_res_577_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__3(lean_object* v___x_581_, size_t v___x_582_, uint8_t v___x_583_, uint8_t v___x_584_, lean_object* v_snd_585_, lean_object* v_fst_586_, lean_object* v___x_587_, lean_object* v___x_588_, lean_object* v_a_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_){
_start:
{
lean_object* v___x_599_; 
v___x_599_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_591_, v___y_594_, v___y_595_, v___y_596_, v___y_597_);
if (lean_obj_tag(v___x_599_) == 0)
{
lean_object* v_a_600_; lean_object* v___x_601_; lean_object* v___x_602_; 
v_a_600_ = lean_ctor_get(v___x_599_, 0);
lean_inc_n(v_a_600_, 2);
lean_dec_ref_known(v___x_599_, 1);
v___x_601_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__3___closed__1));
v___x_602_ = l_Lean_MVarId_checkNotAssigned(v_a_600_, v___x_601_, v___y_594_, v___y_595_, v___y_596_, v___y_597_);
if (lean_obj_tag(v___x_602_) == 0)
{
lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___f_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; 
lean_dec_ref_known(v___x_602_, 1);
v___x_603_ = lean_box_usize(v___x_582_);
v___x_604_ = lean_box(v___x_583_);
v___x_605_ = lean_box(v___x_584_);
lean_inc_ref(v_fst_586_);
v___f_606_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2___boxed), 16, 8);
lean_closure_set(v___f_606_, 0, v___x_581_);
lean_closure_set(v___f_606_, 1, v_a_600_);
lean_closure_set(v___f_606_, 2, v___x_603_);
lean_closure_set(v___f_606_, 3, v___x_604_);
lean_closure_set(v___f_606_, 4, v___x_605_);
lean_closure_set(v___f_606_, 5, v___x_601_);
lean_closure_set(v___f_606_, 6, v_snd_585_);
lean_closure_set(v___f_606_, 7, v_fst_586_);
v___x_607_ = lean_mk_empty_array_with_capacity(v___x_587_);
v___x_608_ = lean_array_push(v___x_607_, v_fst_586_);
v___x_609_ = l_Lean_Meta_extractLets___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__5___redArg(v___x_608_, v___x_588_, v___f_606_, v_a_589_, v___y_594_, v___y_595_, v___y_596_, v___y_597_);
if (lean_obj_tag(v___x_609_) == 0)
{
lean_object* v_a_610_; lean_object* v_fst_611_; lean_object* v_snd_612_; lean_object* v___x_613_; 
v_a_610_ = lean_ctor_get(v___x_609_, 0);
lean_inc(v_a_610_);
lean_dec_ref_known(v___x_609_, 1);
v_fst_611_ = lean_ctor_get(v_a_610_, 0);
lean_inc(v_fst_611_);
v_snd_612_ = lean_ctor_get(v_a_610_, 1);
lean_inc(v_snd_612_);
lean_dec(v_a_610_);
v___x_613_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v_snd_612_, v___y_591_, v___y_594_, v___y_595_, v___y_596_, v___y_597_);
if (lean_obj_tag(v___x_613_) == 0)
{
lean_object* v___x_615_; uint8_t v_isShared_616_; uint8_t v_isSharedCheck_620_; 
v_isSharedCheck_620_ = !lean_is_exclusive(v___x_613_);
if (v_isSharedCheck_620_ == 0)
{
lean_object* v_unused_621_; 
v_unused_621_ = lean_ctor_get(v___x_613_, 0);
lean_dec(v_unused_621_);
v___x_615_ = v___x_613_;
v_isShared_616_ = v_isSharedCheck_620_;
goto v_resetjp_614_;
}
else
{
lean_dec(v___x_613_);
v___x_615_ = lean_box(0);
v_isShared_616_ = v_isSharedCheck_620_;
goto v_resetjp_614_;
}
v_resetjp_614_:
{
lean_object* v___x_618_; 
if (v_isShared_616_ == 0)
{
lean_ctor_set(v___x_615_, 0, v_fst_611_);
v___x_618_ = v___x_615_;
goto v_reusejp_617_;
}
else
{
lean_object* v_reuseFailAlloc_619_; 
v_reuseFailAlloc_619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_619_, 0, v_fst_611_);
v___x_618_ = v_reuseFailAlloc_619_;
goto v_reusejp_617_;
}
v_reusejp_617_:
{
return v___x_618_;
}
}
}
else
{
lean_object* v_a_622_; lean_object* v___x_624_; uint8_t v_isShared_625_; uint8_t v_isSharedCheck_629_; 
lean_dec(v_fst_611_);
v_a_622_ = lean_ctor_get(v___x_613_, 0);
v_isSharedCheck_629_ = !lean_is_exclusive(v___x_613_);
if (v_isSharedCheck_629_ == 0)
{
v___x_624_ = v___x_613_;
v_isShared_625_ = v_isSharedCheck_629_;
goto v_resetjp_623_;
}
else
{
lean_inc(v_a_622_);
lean_dec(v___x_613_);
v___x_624_ = lean_box(0);
v_isShared_625_ = v_isSharedCheck_629_;
goto v_resetjp_623_;
}
v_resetjp_623_:
{
lean_object* v___x_627_; 
if (v_isShared_625_ == 0)
{
v___x_627_ = v___x_624_;
goto v_reusejp_626_;
}
else
{
lean_object* v_reuseFailAlloc_628_; 
v_reuseFailAlloc_628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_628_, 0, v_a_622_);
v___x_627_ = v_reuseFailAlloc_628_;
goto v_reusejp_626_;
}
v_reusejp_626_:
{
return v___x_627_;
}
}
}
}
else
{
lean_object* v_a_630_; lean_object* v___x_632_; uint8_t v_isShared_633_; uint8_t v_isSharedCheck_637_; 
v_a_630_ = lean_ctor_get(v___x_609_, 0);
v_isSharedCheck_637_ = !lean_is_exclusive(v___x_609_);
if (v_isSharedCheck_637_ == 0)
{
v___x_632_ = v___x_609_;
v_isShared_633_ = v_isSharedCheck_637_;
goto v_resetjp_631_;
}
else
{
lean_inc(v_a_630_);
lean_dec(v___x_609_);
v___x_632_ = lean_box(0);
v_isShared_633_ = v_isSharedCheck_637_;
goto v_resetjp_631_;
}
v_resetjp_631_:
{
lean_object* v___x_635_; 
if (v_isShared_633_ == 0)
{
v___x_635_ = v___x_632_;
goto v_reusejp_634_;
}
else
{
lean_object* v_reuseFailAlloc_636_; 
v_reuseFailAlloc_636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_636_, 0, v_a_630_);
v___x_635_ = v_reuseFailAlloc_636_;
goto v_reusejp_634_;
}
v_reusejp_634_:
{
return v___x_635_;
}
}
}
}
else
{
lean_object* v_a_638_; lean_object* v___x_640_; uint8_t v_isShared_641_; uint8_t v_isSharedCheck_645_; 
lean_dec(v_a_600_);
lean_dec(v___x_588_);
lean_dec_ref(v_fst_586_);
lean_dec_ref(v_snd_585_);
lean_dec(v___x_581_);
v_a_638_ = lean_ctor_get(v___x_602_, 0);
v_isSharedCheck_645_ = !lean_is_exclusive(v___x_602_);
if (v_isSharedCheck_645_ == 0)
{
v___x_640_ = v___x_602_;
v_isShared_641_ = v_isSharedCheck_645_;
goto v_resetjp_639_;
}
else
{
lean_inc(v_a_638_);
lean_dec(v___x_602_);
v___x_640_ = lean_box(0);
v_isShared_641_ = v_isSharedCheck_645_;
goto v_resetjp_639_;
}
v_resetjp_639_:
{
lean_object* v___x_643_; 
if (v_isShared_641_ == 0)
{
v___x_643_ = v___x_640_;
goto v_reusejp_642_;
}
else
{
lean_object* v_reuseFailAlloc_644_; 
v_reuseFailAlloc_644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_644_, 0, v_a_638_);
v___x_643_ = v_reuseFailAlloc_644_;
goto v_reusejp_642_;
}
v_reusejp_642_:
{
return v___x_643_;
}
}
}
}
else
{
lean_object* v_a_646_; lean_object* v___x_648_; uint8_t v_isShared_649_; uint8_t v_isSharedCheck_653_; 
lean_dec(v___x_588_);
lean_dec_ref(v_fst_586_);
lean_dec_ref(v_snd_585_);
lean_dec(v___x_581_);
v_a_646_ = lean_ctor_get(v___x_599_, 0);
v_isSharedCheck_653_ = !lean_is_exclusive(v___x_599_);
if (v_isSharedCheck_653_ == 0)
{
v___x_648_ = v___x_599_;
v_isShared_649_ = v_isSharedCheck_653_;
goto v_resetjp_647_;
}
else
{
lean_inc(v_a_646_);
lean_dec(v___x_599_);
v___x_648_ = lean_box(0);
v_isShared_649_ = v_isSharedCheck_653_;
goto v_resetjp_647_;
}
v_resetjp_647_:
{
lean_object* v___x_651_; 
if (v_isShared_649_ == 0)
{
v___x_651_ = v___x_648_;
goto v_reusejp_650_;
}
else
{
lean_object* v_reuseFailAlloc_652_; 
v_reuseFailAlloc_652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_652_, 0, v_a_646_);
v___x_651_ = v_reuseFailAlloc_652_;
goto v_reusejp_650_;
}
v_reusejp_650_:
{
return v___x_651_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__3___boxed(lean_object** _args){
lean_object* v___x_654_ = _args[0];
lean_object* v___x_655_ = _args[1];
lean_object* v___x_656_ = _args[2];
lean_object* v___x_657_ = _args[3];
lean_object* v_snd_658_ = _args[4];
lean_object* v_fst_659_ = _args[5];
lean_object* v___x_660_ = _args[6];
lean_object* v___x_661_ = _args[7];
lean_object* v_a_662_ = _args[8];
lean_object* v___y_663_ = _args[9];
lean_object* v___y_664_ = _args[10];
lean_object* v___y_665_ = _args[11];
lean_object* v___y_666_ = _args[12];
lean_object* v___y_667_ = _args[13];
lean_object* v___y_668_ = _args[14];
lean_object* v___y_669_ = _args[15];
lean_object* v___y_670_ = _args[16];
lean_object* v___y_671_ = _args[17];
_start:
{
size_t v___x_6736__boxed_672_; uint8_t v___x_6737__boxed_673_; uint8_t v___x_6738__boxed_674_; lean_object* v_res_675_; 
v___x_6736__boxed_672_ = lean_unbox_usize(v___x_655_);
lean_dec(v___x_655_);
v___x_6737__boxed_673_ = lean_unbox(v___x_656_);
v___x_6738__boxed_674_ = lean_unbox(v___x_657_);
v_res_675_ = l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__3(v___x_654_, v___x_6736__boxed_672_, v___x_6737__boxed_673_, v___x_6738__boxed_674_, v_snd_658_, v_fst_659_, v___x_660_, v___x_661_, v_a_662_, v___y_663_, v___y_664_, v___y_665_, v___y_666_, v___y_667_, v___y_668_, v___y_669_, v___y_670_);
lean_dec(v___y_670_);
lean_dec_ref(v___y_669_);
lean_dec(v___y_668_);
lean_dec_ref(v___y_667_);
lean_dec(v___y_666_);
lean_dec_ref(v___y_665_);
lean_dec(v___y_664_);
lean_dec_ref(v___y_663_);
lean_dec_ref(v_a_662_);
lean_dec(v___x_660_);
return v_res_675_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__1(size_t v_sz_676_, size_t v_i_677_, lean_object* v_bs_678_){
_start:
{
uint8_t v___x_679_; 
v___x_679_ = lean_usize_dec_lt(v_i_677_, v_sz_676_);
if (v___x_679_ == 0)
{
return v_bs_678_;
}
else
{
lean_object* v_v_680_; lean_object* v___x_681_; lean_object* v_bs_x27_682_; lean_object* v___x_683_; size_t v___x_684_; size_t v___x_685_; lean_object* v___x_686_; 
v_v_680_ = lean_array_uget(v_bs_678_, v_i_677_);
v___x_681_ = lean_unsigned_to_nat(0u);
v_bs_x27_682_ = lean_array_uset(v_bs_678_, v_i_677_, v___x_681_);
v___x_683_ = l_Lean_Elab_Tactic_getNameOfIdent_x27(v_v_680_);
lean_dec(v_v_680_);
v___x_684_ = ((size_t)1ULL);
v___x_685_ = lean_usize_add(v_i_677_, v___x_684_);
v___x_686_ = lean_array_uset(v_bs_x27_682_, v_i_677_, v___x_683_);
v_i_677_ = v___x_685_;
v_bs_678_ = v___x_686_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__1___boxed(lean_object* v_sz_688_, lean_object* v_i_689_, lean_object* v_bs_690_){
_start:
{
size_t v_sz_boxed_691_; size_t v_i_boxed_692_; lean_object* v_res_693_; 
v_sz_boxed_691_ = lean_unbox_usize(v_sz_688_);
lean_dec(v_sz_688_);
v_i_boxed_692_ = lean_unbox_usize(v_i_689_);
lean_dec(v_i_689_);
v_res_693_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__1(v_sz_boxed_691_, v_i_boxed_692_, v_bs_690_);
return v_res_693_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalExtractLets(lean_object* v_x_713_, lean_object* v_a_714_, lean_object* v_a_715_, lean_object* v_a_716_, lean_object* v_a_717_, lean_object* v_a_718_, lean_object* v_a_719_, lean_object* v_a_720_, lean_object* v_a_721_){
_start:
{
lean_object* v___x_723_; uint8_t v___x_724_; 
v___x_723_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__5));
lean_inc(v_x_713_);
v___x_724_ = l_Lean_Syntax_isOfKind(v_x_713_, v___x_723_);
if (v___x_724_ == 0)
{
lean_object* v___x_725_; 
lean_dec(v_x_713_);
v___x_725_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__0___redArg();
return v___x_725_;
}
else
{
lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; uint8_t v___x_729_; 
v___x_726_ = lean_unsigned_to_nat(1u);
v___x_727_ = l_Lean_Syntax_getArg(v_x_713_, v___x_726_);
v___x_728_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__7));
lean_inc(v___x_727_);
v___x_729_ = l_Lean_Syntax_isOfKind(v___x_727_, v___x_728_);
if (v___x_729_ == 0)
{
lean_object* v___x_730_; 
lean_dec(v___x_727_);
lean_dec(v_x_713_);
v___x_730_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__0___redArg();
return v___x_730_;
}
else
{
uint8_t v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; 
v___x_731_ = 0;
v___x_732_ = lean_alloc_ctor(0, 0, 11);
lean_ctor_set_uint8(v___x_732_, 0, v___x_731_);
lean_ctor_set_uint8(v___x_732_, 1, v___x_729_);
lean_ctor_set_uint8(v___x_732_, 2, v___x_731_);
lean_ctor_set_uint8(v___x_732_, 3, v___x_729_);
lean_ctor_set_uint8(v___x_732_, 4, v___x_729_);
lean_ctor_set_uint8(v___x_732_, 5, v___x_731_);
lean_ctor_set_uint8(v___x_732_, 6, v___x_729_);
lean_ctor_set_uint8(v___x_732_, 7, v___x_729_);
lean_ctor_set_uint8(v___x_732_, 8, v___x_731_);
lean_ctor_set_uint8(v___x_732_, 9, v___x_731_);
lean_ctor_set_uint8(v___x_732_, 10, v___x_731_);
v___x_733_ = l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg(v___x_727_, v___x_732_, v___x_729_, v_a_714_, v_a_720_, v_a_721_);
if (lean_obj_tag(v___x_733_) == 0)
{
lean_object* v_a_734_; lean_object* v___x_735_; 
v_a_734_ = lean_ctor_get(v___x_733_, 0);
lean_inc(v_a_734_);
lean_dec_ref_known(v___x_733_, 1);
v___x_735_ = l_Lean_Elab_Tactic_Conv_getLhsRhs___redArg(v_a_715_, v_a_718_, v_a_719_, v_a_720_, v_a_721_);
if (lean_obj_tag(v___x_735_) == 0)
{
lean_object* v_a_736_; lean_object* v_fst_737_; lean_object* v_snd_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v_ids_741_; size_t v_sz_742_; lean_object* v___x_743_; size_t v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___f_750_; lean_object* v___x_751_; 
v_a_736_ = lean_ctor_get(v___x_735_, 0);
lean_inc(v_a_736_);
lean_dec_ref_known(v___x_735_, 1);
v_fst_737_ = lean_ctor_get(v_a_736_, 0);
lean_inc(v_fst_737_);
v_snd_738_ = lean_ctor_get(v_a_736_, 1);
lean_inc(v_snd_738_);
lean_dec(v_a_736_);
v___x_739_ = lean_unsigned_to_nat(2u);
v___x_740_ = l_Lean_Syntax_getArg(v_x_713_, v___x_739_);
lean_dec(v_x_713_);
v_ids_741_ = l_Lean_Syntax_getArgs(v___x_740_);
lean_dec(v___x_740_);
v_sz_742_ = lean_array_size(v_ids_741_);
v___x_743_ = lean_unsigned_to_nat(0u);
v___x_744_ = ((size_t)0ULL);
lean_inc_ref(v_ids_741_);
v___x_745_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__1(v_sz_742_, v___x_744_, v_ids_741_);
v___x_746_ = lean_array_to_list(v___x_745_);
v___x_747_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalExtractLets___boxed__const__1));
v___x_748_ = lean_box(v___x_731_);
v___x_749_ = lean_box(v___x_729_);
v___f_750_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__3___boxed), 18, 9);
lean_closure_set(v___f_750_, 0, v___x_743_);
lean_closure_set(v___f_750_, 1, v___x_747_);
lean_closure_set(v___f_750_, 2, v___x_748_);
lean_closure_set(v___f_750_, 3, v___x_749_);
lean_closure_set(v___f_750_, 4, v_snd_738_);
lean_closure_set(v___f_750_, 5, v_fst_737_);
lean_closure_set(v___f_750_, 6, v___x_726_);
lean_closure_set(v___f_750_, 7, v___x_746_);
lean_closure_set(v___f_750_, 8, v_a_734_);
v___x_751_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_750_, v_a_714_, v_a_715_, v_a_716_, v_a_717_, v_a_718_, v_a_719_, v_a_720_, v_a_721_);
if (lean_obj_tag(v___x_751_) == 0)
{
lean_object* v_a_752_; lean_object* v___x_753_; 
v_a_752_ = lean_ctor_get(v___x_751_, 0);
lean_inc(v_a_752_);
lean_dec_ref_known(v___x_751_, 1);
v___x_753_ = l_Lean_Elab_Tactic_extractLetsAddVarInfo(v_ids_741_, v_a_752_, v_a_714_, v_a_715_, v_a_716_, v_a_717_, v_a_718_, v_a_719_, v_a_720_, v_a_721_);
return v___x_753_;
}
else
{
lean_object* v_a_754_; lean_object* v___x_756_; uint8_t v_isShared_757_; uint8_t v_isSharedCheck_761_; 
lean_dec_ref(v_ids_741_);
v_a_754_ = lean_ctor_get(v___x_751_, 0);
v_isSharedCheck_761_ = !lean_is_exclusive(v___x_751_);
if (v_isSharedCheck_761_ == 0)
{
v___x_756_ = v___x_751_;
v_isShared_757_ = v_isSharedCheck_761_;
goto v_resetjp_755_;
}
else
{
lean_inc(v_a_754_);
lean_dec(v___x_751_);
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
else
{
lean_object* v_a_762_; lean_object* v___x_764_; uint8_t v_isShared_765_; uint8_t v_isSharedCheck_769_; 
lean_dec(v_a_734_);
lean_dec(v_x_713_);
v_a_762_ = lean_ctor_get(v___x_735_, 0);
v_isSharedCheck_769_ = !lean_is_exclusive(v___x_735_);
if (v_isSharedCheck_769_ == 0)
{
v___x_764_ = v___x_735_;
v_isShared_765_ = v_isSharedCheck_769_;
goto v_resetjp_763_;
}
else
{
lean_inc(v_a_762_);
lean_dec(v___x_735_);
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
lean_object* v_a_770_; lean_object* v___x_772_; uint8_t v_isShared_773_; uint8_t v_isSharedCheck_777_; 
lean_dec(v_x_713_);
v_a_770_ = lean_ctor_get(v___x_733_, 0);
v_isSharedCheck_777_ = !lean_is_exclusive(v___x_733_);
if (v_isSharedCheck_777_ == 0)
{
v___x_772_ = v___x_733_;
v_isShared_773_ = v_isSharedCheck_777_;
goto v_resetjp_771_;
}
else
{
lean_inc(v_a_770_);
lean_dec(v___x_733_);
v___x_772_ = lean_box(0);
v_isShared_773_ = v_isSharedCheck_777_;
goto v_resetjp_771_;
}
v_resetjp_771_:
{
lean_object* v___x_775_; 
if (v_isShared_773_ == 0)
{
v___x_775_ = v___x_772_;
goto v_reusejp_774_;
}
else
{
lean_object* v_reuseFailAlloc_776_; 
v_reuseFailAlloc_776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_776_, 0, v_a_770_);
v___x_775_ = v_reuseFailAlloc_776_;
goto v_reusejp_774_;
}
v_reusejp_774_:
{
return v___x_775_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalExtractLets___boxed(lean_object* v_x_778_, lean_object* v_a_779_, lean_object* v_a_780_, lean_object* v_a_781_, lean_object* v_a_782_, lean_object* v_a_783_, lean_object* v_a_784_, lean_object* v_a_785_, lean_object* v_a_786_, lean_object* v_a_787_){
_start:
{
lean_object* v_res_788_; 
v_res_788_ = l_Lean_Elab_Tactic_Conv_evalExtractLets(v_x_778_, v_a_779_, v_a_780_, v_a_781_, v_a_782_, v_a_783_, v_a_784_, v_a_785_, v_a_786_);
lean_dec(v_a_786_);
lean_dec_ref(v_a_785_);
lean_dec(v_a_784_);
lean_dec_ref(v_a_783_);
lean_dec(v_a_782_);
lean_dec_ref(v_a_781_);
lean_dec(v_a_780_);
lean_dec_ref(v_a_779_);
return v_res_788_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3(lean_object* v_mvarId_789_, lean_object* v_val_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_, lean_object* v___y_794_){
_start:
{
lean_object* v___x_796_; 
v___x_796_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3___redArg(v_mvarId_789_, v_val_790_, v___y_792_);
return v___x_796_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3___boxed(lean_object* v_mvarId_797_, lean_object* v_val_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_){
_start:
{
lean_object* v_res_804_; 
v_res_804_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3(v_mvarId_797_, v_val_798_, v___y_799_, v___y_800_, v___y_801_, v___y_802_);
lean_dec(v___y_802_);
lean_dec_ref(v___y_801_);
lean_dec(v___y_800_);
lean_dec_ref(v___y_799_);
return v_res_804_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3(lean_object* v_00_u03b2_805_, lean_object* v_x_806_, lean_object* v_x_807_, lean_object* v_x_808_){
_start:
{
lean_object* v___x_809_; 
v___x_809_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3___redArg(v_x_806_, v_x_807_, v_x_808_);
return v___x_809_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6(lean_object* v_00_u03b2_810_, lean_object* v_x_811_, size_t v_x_812_, size_t v_x_813_, lean_object* v_x_814_, lean_object* v_x_815_){
_start:
{
lean_object* v___x_816_; 
v___x_816_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___redArg(v_x_811_, v_x_812_, v_x_813_, v_x_814_, v_x_815_);
return v___x_816_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___boxed(lean_object* v_00_u03b2_817_, lean_object* v_x_818_, lean_object* v_x_819_, lean_object* v_x_820_, lean_object* v_x_821_, lean_object* v_x_822_){
_start:
{
size_t v_x_7111__boxed_823_; size_t v_x_7112__boxed_824_; lean_object* v_res_825_; 
v_x_7111__boxed_823_ = lean_unbox_usize(v_x_819_);
lean_dec(v_x_819_);
v_x_7112__boxed_824_ = lean_unbox_usize(v_x_820_);
lean_dec(v_x_820_);
v_res_825_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6(v_00_u03b2_817_, v_x_818_, v_x_7111__boxed_823_, v_x_7112__boxed_824_, v_x_821_, v_x_822_);
return v_res_825_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6_spec__7(lean_object* v_00_u03b2_826_, lean_object* v_n_827_, lean_object* v_k_828_, lean_object* v_v_829_){
_start:
{
lean_object* v___x_830_; 
v___x_830_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6_spec__7___redArg(v_n_827_, v_k_828_, v_v_829_);
return v___x_830_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6_spec__8(lean_object* v_00_u03b2_831_, size_t v_depth_832_, lean_object* v_keys_833_, lean_object* v_vals_834_, lean_object* v_heq_835_, lean_object* v_i_836_, lean_object* v_entries_837_){
_start:
{
lean_object* v___x_838_; 
v___x_838_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6_spec__8___redArg(v_depth_832_, v_keys_833_, v_vals_834_, v_i_836_, v_entries_837_);
return v___x_838_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6_spec__8___boxed(lean_object* v_00_u03b2_839_, lean_object* v_depth_840_, lean_object* v_keys_841_, lean_object* v_vals_842_, lean_object* v_heq_843_, lean_object* v_i_844_, lean_object* v_entries_845_){
_start:
{
size_t v_depth_boxed_846_; lean_object* v_res_847_; 
v_depth_boxed_846_ = lean_unbox_usize(v_depth_840_);
lean_dec(v_depth_840_);
v_res_847_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6_spec__8(v_00_u03b2_839_, v_depth_boxed_846_, v_keys_841_, v_vals_842_, v_heq_843_, v_i_844_, v_entries_845_);
lean_dec_ref(v_vals_842_);
lean_dec_ref(v_keys_841_);
return v_res_847_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6_spec__7_spec__8(lean_object* v_00_u03b2_848_, lean_object* v_x_849_, lean_object* v_x_850_, lean_object* v_x_851_, lean_object* v_x_852_){
_start:
{
lean_object* v___x_853_; 
v___x_853_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6_spec__7_spec__8___redArg(v_x_849_, v_x_850_, v_x_851_, v_x_852_);
return v___x_853_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalExtractLets___regBuiltin_Lean_Elab_Tactic_Conv_evalExtractLets__1(){
_start:
{
lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; 
v___x_863_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_864_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__5));
v___x_865_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalExtractLets___regBuiltin_Lean_Elab_Tactic_Conv_evalExtractLets__1___closed__2));
v___x_866_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalExtractLets___boxed), 10, 0);
v___x_867_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_863_, v___x_864_, v___x_865_, v___x_866_);
return v___x_867_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalExtractLets___regBuiltin_Lean_Elab_Tactic_Conv_evalExtractLets__1___boxed(lean_object* v_a_868_){
_start:
{
lean_object* v_res_869_; 
v_res_869_ = l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalExtractLets___regBuiltin_Lean_Elab_Tactic_Conv_evalExtractLets__1();
return v_res_869_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalLiftLets___lam__0(lean_object* v_a_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_){
_start:
{
lean_object* v___x_883_; 
v___x_883_ = l_Lean_Elab_Tactic_Conv_getLhs___redArg(v___y_875_, v___y_878_, v___y_879_, v___y_880_, v___y_881_);
if (lean_obj_tag(v___x_883_) == 0)
{
lean_object* v_a_884_; lean_object* v___x_885_; 
v_a_884_ = lean_ctor_get(v___x_883_, 0);
lean_inc_n(v_a_884_, 2);
lean_dec_ref_known(v___x_883_, 1);
v___x_885_ = l_Lean_Meta_liftLets(v_a_884_, v_a_873_, v___y_878_, v___y_879_, v___y_880_, v___y_881_);
if (lean_obj_tag(v___x_885_) == 0)
{
lean_object* v_a_886_; uint8_t v___x_887_; 
v_a_886_ = lean_ctor_get(v___x_885_, 0);
lean_inc(v_a_886_);
lean_dec_ref_known(v___x_885_, 1);
v___x_887_ = lean_expr_eqv(v_a_884_, v_a_886_);
lean_dec(v_a_884_);
if (v___x_887_ == 0)
{
lean_object* v___x_888_; 
v___x_888_ = l_Lean_Elab_Tactic_Conv_changeLhs(v_a_886_, v___y_874_, v___y_875_, v___y_876_, v___y_877_, v___y_878_, v___y_879_, v___y_880_, v___y_881_);
return v___x_888_;
}
else
{
lean_object* v___x_889_; 
v___x_889_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_875_, v___y_878_, v___y_879_, v___y_880_, v___y_881_);
if (lean_obj_tag(v___x_889_) == 0)
{
lean_object* v_a_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; 
v_a_890_ = lean_ctor_get(v___x_889_, 0);
lean_inc(v_a_890_);
lean_dec_ref_known(v___x_889_, 1);
v___x_891_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalLiftLets___lam__0___closed__1));
v___x_892_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2___closed__2, &l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2___closed__2_once, _init_l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2___closed__2);
v___x_893_ = l_Lean_Meta_throwTacticEx___redArg(v___x_891_, v_a_890_, v___x_892_, v___y_878_, v___y_879_, v___y_880_, v___y_881_);
if (lean_obj_tag(v___x_893_) == 0)
{
lean_object* v___x_894_; 
lean_dec_ref_known(v___x_893_, 1);
v___x_894_ = l_Lean_Elab_Tactic_Conv_changeLhs(v_a_886_, v___y_874_, v___y_875_, v___y_876_, v___y_877_, v___y_878_, v___y_879_, v___y_880_, v___y_881_);
return v___x_894_;
}
else
{
lean_dec(v_a_886_);
return v___x_893_;
}
}
else
{
lean_object* v_a_895_; lean_object* v___x_897_; uint8_t v_isShared_898_; uint8_t v_isSharedCheck_902_; 
lean_dec(v_a_886_);
v_a_895_ = lean_ctor_get(v___x_889_, 0);
v_isSharedCheck_902_ = !lean_is_exclusive(v___x_889_);
if (v_isSharedCheck_902_ == 0)
{
v___x_897_ = v___x_889_;
v_isShared_898_ = v_isSharedCheck_902_;
goto v_resetjp_896_;
}
else
{
lean_inc(v_a_895_);
lean_dec(v___x_889_);
v___x_897_ = lean_box(0);
v_isShared_898_ = v_isSharedCheck_902_;
goto v_resetjp_896_;
}
v_resetjp_896_:
{
lean_object* v___x_900_; 
if (v_isShared_898_ == 0)
{
v___x_900_ = v___x_897_;
goto v_reusejp_899_;
}
else
{
lean_object* v_reuseFailAlloc_901_; 
v_reuseFailAlloc_901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_901_, 0, v_a_895_);
v___x_900_ = v_reuseFailAlloc_901_;
goto v_reusejp_899_;
}
v_reusejp_899_:
{
return v___x_900_;
}
}
}
}
}
else
{
lean_object* v_a_903_; lean_object* v___x_905_; uint8_t v_isShared_906_; uint8_t v_isSharedCheck_910_; 
lean_dec(v_a_884_);
v_a_903_ = lean_ctor_get(v___x_885_, 0);
v_isSharedCheck_910_ = !lean_is_exclusive(v___x_885_);
if (v_isSharedCheck_910_ == 0)
{
v___x_905_ = v___x_885_;
v_isShared_906_ = v_isSharedCheck_910_;
goto v_resetjp_904_;
}
else
{
lean_inc(v_a_903_);
lean_dec(v___x_885_);
v___x_905_ = lean_box(0);
v_isShared_906_ = v_isSharedCheck_910_;
goto v_resetjp_904_;
}
v_resetjp_904_:
{
lean_object* v___x_908_; 
if (v_isShared_906_ == 0)
{
v___x_908_ = v___x_905_;
goto v_reusejp_907_;
}
else
{
lean_object* v_reuseFailAlloc_909_; 
v_reuseFailAlloc_909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_909_, 0, v_a_903_);
v___x_908_ = v_reuseFailAlloc_909_;
goto v_reusejp_907_;
}
v_reusejp_907_:
{
return v___x_908_;
}
}
}
}
else
{
lean_object* v_a_911_; lean_object* v___x_913_; uint8_t v_isShared_914_; uint8_t v_isSharedCheck_918_; 
lean_dec_ref(v_a_873_);
v_a_911_ = lean_ctor_get(v___x_883_, 0);
v_isSharedCheck_918_ = !lean_is_exclusive(v___x_883_);
if (v_isSharedCheck_918_ == 0)
{
v___x_913_ = v___x_883_;
v_isShared_914_ = v_isSharedCheck_918_;
goto v_resetjp_912_;
}
else
{
lean_inc(v_a_911_);
lean_dec(v___x_883_);
v___x_913_ = lean_box(0);
v_isShared_914_ = v_isSharedCheck_918_;
goto v_resetjp_912_;
}
v_resetjp_912_:
{
lean_object* v___x_916_; 
if (v_isShared_914_ == 0)
{
v___x_916_ = v___x_913_;
goto v_reusejp_915_;
}
else
{
lean_object* v_reuseFailAlloc_917_; 
v_reuseFailAlloc_917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_917_, 0, v_a_911_);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalLiftLets___lam__0___boxed(lean_object* v_a_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_){
_start:
{
lean_object* v_res_929_; 
v_res_929_ = l_Lean_Elab_Tactic_Conv_evalLiftLets___lam__0(v_a_919_, v___y_920_, v___y_921_, v___y_922_, v___y_923_, v___y_924_, v___y_925_, v___y_926_, v___y_927_);
lean_dec(v___y_927_);
lean_dec_ref(v___y_926_);
lean_dec(v___y_925_);
lean_dec_ref(v___y_924_);
lean_dec(v___y_923_);
lean_dec_ref(v___y_922_);
lean_dec(v___y_921_);
lean_dec_ref(v___y_920_);
return v_res_929_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalLiftLets(lean_object* v_x_937_, lean_object* v_a_938_, lean_object* v_a_939_, lean_object* v_a_940_, lean_object* v_a_941_, lean_object* v_a_942_, lean_object* v_a_943_, lean_object* v_a_944_, lean_object* v_a_945_){
_start:
{
lean_object* v___x_947_; uint8_t v___x_948_; 
v___x_947_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalLiftLets___closed__1));
lean_inc(v_x_937_);
v___x_948_ = l_Lean_Syntax_isOfKind(v_x_937_, v___x_947_);
if (v___x_948_ == 0)
{
lean_object* v___x_949_; 
lean_dec(v_x_937_);
v___x_949_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__0___redArg();
return v___x_949_;
}
else
{
lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; uint8_t v___x_953_; 
v___x_950_ = lean_unsigned_to_nat(1u);
v___x_951_ = l_Lean_Syntax_getArg(v_x_937_, v___x_950_);
lean_dec(v_x_937_);
v___x_952_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__7));
lean_inc(v___x_951_);
v___x_953_ = l_Lean_Syntax_isOfKind(v___x_951_, v___x_952_);
if (v___x_953_ == 0)
{
lean_object* v___x_954_; 
lean_dec(v___x_951_);
v___x_954_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__0___redArg();
return v___x_954_;
}
else
{
uint8_t v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; 
v___x_955_ = 0;
v___x_956_ = lean_alloc_ctor(0, 0, 11);
lean_ctor_set_uint8(v___x_956_, 0, v___x_955_);
lean_ctor_set_uint8(v___x_956_, 1, v___x_953_);
lean_ctor_set_uint8(v___x_956_, 2, v___x_955_);
lean_ctor_set_uint8(v___x_956_, 3, v___x_953_);
lean_ctor_set_uint8(v___x_956_, 4, v___x_953_);
lean_ctor_set_uint8(v___x_956_, 5, v___x_955_);
lean_ctor_set_uint8(v___x_956_, 6, v___x_953_);
lean_ctor_set_uint8(v___x_956_, 7, v___x_953_);
lean_ctor_set_uint8(v___x_956_, 8, v___x_955_);
lean_ctor_set_uint8(v___x_956_, 9, v___x_953_);
lean_ctor_set_uint8(v___x_956_, 10, v___x_953_);
v___x_957_ = l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg(v___x_951_, v___x_956_, v___x_953_, v_a_938_, v_a_944_, v_a_945_);
if (lean_obj_tag(v___x_957_) == 0)
{
lean_object* v_a_958_; lean_object* v___f_959_; lean_object* v___x_960_; 
v_a_958_ = lean_ctor_get(v___x_957_, 0);
lean_inc(v_a_958_);
lean_dec_ref_known(v___x_957_, 1);
v___f_959_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalLiftLets___lam__0___boxed), 10, 1);
lean_closure_set(v___f_959_, 0, v_a_958_);
v___x_960_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_959_, v_a_938_, v_a_939_, v_a_940_, v_a_941_, v_a_942_, v_a_943_, v_a_944_, v_a_945_);
return v___x_960_;
}
else
{
lean_object* v_a_961_; lean_object* v___x_963_; uint8_t v_isShared_964_; uint8_t v_isSharedCheck_968_; 
v_a_961_ = lean_ctor_get(v___x_957_, 0);
v_isSharedCheck_968_ = !lean_is_exclusive(v___x_957_);
if (v_isSharedCheck_968_ == 0)
{
v___x_963_ = v___x_957_;
v_isShared_964_ = v_isSharedCheck_968_;
goto v_resetjp_962_;
}
else
{
lean_inc(v_a_961_);
lean_dec(v___x_957_);
v___x_963_ = lean_box(0);
v_isShared_964_ = v_isSharedCheck_968_;
goto v_resetjp_962_;
}
v_resetjp_962_:
{
lean_object* v___x_966_; 
if (v_isShared_964_ == 0)
{
v___x_966_ = v___x_963_;
goto v_reusejp_965_;
}
else
{
lean_object* v_reuseFailAlloc_967_; 
v_reuseFailAlloc_967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_967_, 0, v_a_961_);
v___x_966_ = v_reuseFailAlloc_967_;
goto v_reusejp_965_;
}
v_reusejp_965_:
{
return v___x_966_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalLiftLets___boxed(lean_object* v_x_969_, lean_object* v_a_970_, lean_object* v_a_971_, lean_object* v_a_972_, lean_object* v_a_973_, lean_object* v_a_974_, lean_object* v_a_975_, lean_object* v_a_976_, lean_object* v_a_977_, lean_object* v_a_978_){
_start:
{
lean_object* v_res_979_; 
v_res_979_ = l_Lean_Elab_Tactic_Conv_evalLiftLets(v_x_969_, v_a_970_, v_a_971_, v_a_972_, v_a_973_, v_a_974_, v_a_975_, v_a_976_, v_a_977_);
lean_dec(v_a_977_);
lean_dec_ref(v_a_976_);
lean_dec(v_a_975_);
lean_dec_ref(v_a_974_);
lean_dec(v_a_973_);
lean_dec_ref(v_a_972_);
lean_dec(v_a_971_);
lean_dec_ref(v_a_970_);
return v_res_979_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLiftLets___regBuiltin_Lean_Elab_Tactic_Conv_evalLiftLets__1(){
_start:
{
lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; 
v___x_988_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_989_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalLiftLets___closed__1));
v___x_990_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLiftLets___regBuiltin_Lean_Elab_Tactic_Conv_evalLiftLets__1___closed__1));
v___x_991_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalLiftLets___boxed), 10, 0);
v___x_992_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_988_, v___x_989_, v___x_990_, v___x_991_);
return v___x_992_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLiftLets___regBuiltin_Lean_Elab_Tactic_Conv_evalLiftLets__1___boxed(lean_object* v_a_993_){
_start:
{
lean_object* v_res_994_; 
v_res_994_ = l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLiftLets___regBuiltin_Lean_Elab_Tactic_Conv_evalLiftLets__1();
return v_res_994_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalLetToHave___lam__0(lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_){
_start:
{
lean_object* v___x_1007_; 
v___x_1007_ = l_Lean_Elab_Tactic_Conv_getLhs___redArg(v___y_999_, v___y_1002_, v___y_1003_, v___y_1004_, v___y_1005_);
if (lean_obj_tag(v___x_1007_) == 0)
{
lean_object* v_a_1008_; lean_object* v___x_1009_; 
v_a_1008_ = lean_ctor_get(v___x_1007_, 0);
lean_inc_n(v_a_1008_, 2);
lean_dec_ref_known(v___x_1007_, 1);
v___x_1009_ = l_Lean_Meta_letToHave(v_a_1008_, v___y_1002_, v___y_1003_, v___y_1004_, v___y_1005_);
if (lean_obj_tag(v___x_1009_) == 0)
{
lean_object* v_a_1010_; uint8_t v___x_1011_; 
v_a_1010_ = lean_ctor_get(v___x_1009_, 0);
lean_inc(v_a_1010_);
lean_dec_ref_known(v___x_1009_, 1);
v___x_1011_ = lean_expr_eqv(v_a_1008_, v_a_1010_);
lean_dec(v_a_1008_);
if (v___x_1011_ == 0)
{
lean_object* v___x_1012_; 
v___x_1012_ = l_Lean_Elab_Tactic_Conv_changeLhs(v_a_1010_, v___y_998_, v___y_999_, v___y_1000_, v___y_1001_, v___y_1002_, v___y_1003_, v___y_1004_, v___y_1005_);
return v___x_1012_;
}
else
{
lean_object* v___x_1013_; 
v___x_1013_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_999_, v___y_1002_, v___y_1003_, v___y_1004_, v___y_1005_);
if (lean_obj_tag(v___x_1013_) == 0)
{
lean_object* v_a_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; 
v_a_1014_ = lean_ctor_get(v___x_1013_, 0);
lean_inc(v_a_1014_);
lean_dec_ref_known(v___x_1013_, 1);
v___x_1015_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalLetToHave___lam__0___closed__1));
v___x_1016_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2___closed__2, &l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2___closed__2_once, _init_l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2___closed__2);
v___x_1017_ = l_Lean_Meta_throwTacticEx___redArg(v___x_1015_, v_a_1014_, v___x_1016_, v___y_1002_, v___y_1003_, v___y_1004_, v___y_1005_);
if (lean_obj_tag(v___x_1017_) == 0)
{
lean_object* v___x_1018_; 
lean_dec_ref_known(v___x_1017_, 1);
v___x_1018_ = l_Lean_Elab_Tactic_Conv_changeLhs(v_a_1010_, v___y_998_, v___y_999_, v___y_1000_, v___y_1001_, v___y_1002_, v___y_1003_, v___y_1004_, v___y_1005_);
return v___x_1018_;
}
else
{
lean_dec(v_a_1010_);
return v___x_1017_;
}
}
else
{
lean_object* v_a_1019_; lean_object* v___x_1021_; uint8_t v_isShared_1022_; uint8_t v_isSharedCheck_1026_; 
lean_dec(v_a_1010_);
v_a_1019_ = lean_ctor_get(v___x_1013_, 0);
v_isSharedCheck_1026_ = !lean_is_exclusive(v___x_1013_);
if (v_isSharedCheck_1026_ == 0)
{
v___x_1021_ = v___x_1013_;
v_isShared_1022_ = v_isSharedCheck_1026_;
goto v_resetjp_1020_;
}
else
{
lean_inc(v_a_1019_);
lean_dec(v___x_1013_);
v___x_1021_ = lean_box(0);
v_isShared_1022_ = v_isSharedCheck_1026_;
goto v_resetjp_1020_;
}
v_resetjp_1020_:
{
lean_object* v___x_1024_; 
if (v_isShared_1022_ == 0)
{
v___x_1024_ = v___x_1021_;
goto v_reusejp_1023_;
}
else
{
lean_object* v_reuseFailAlloc_1025_; 
v_reuseFailAlloc_1025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1025_, 0, v_a_1019_);
v___x_1024_ = v_reuseFailAlloc_1025_;
goto v_reusejp_1023_;
}
v_reusejp_1023_:
{
return v___x_1024_;
}
}
}
}
}
else
{
lean_object* v_a_1027_; lean_object* v___x_1029_; uint8_t v_isShared_1030_; uint8_t v_isSharedCheck_1034_; 
lean_dec(v_a_1008_);
v_a_1027_ = lean_ctor_get(v___x_1009_, 0);
v_isSharedCheck_1034_ = !lean_is_exclusive(v___x_1009_);
if (v_isSharedCheck_1034_ == 0)
{
v___x_1029_ = v___x_1009_;
v_isShared_1030_ = v_isSharedCheck_1034_;
goto v_resetjp_1028_;
}
else
{
lean_inc(v_a_1027_);
lean_dec(v___x_1009_);
v___x_1029_ = lean_box(0);
v_isShared_1030_ = v_isSharedCheck_1034_;
goto v_resetjp_1028_;
}
v_resetjp_1028_:
{
lean_object* v___x_1032_; 
if (v_isShared_1030_ == 0)
{
v___x_1032_ = v___x_1029_;
goto v_reusejp_1031_;
}
else
{
lean_object* v_reuseFailAlloc_1033_; 
v_reuseFailAlloc_1033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1033_, 0, v_a_1027_);
v___x_1032_ = v_reuseFailAlloc_1033_;
goto v_reusejp_1031_;
}
v_reusejp_1031_:
{
return v___x_1032_;
}
}
}
}
else
{
lean_object* v_a_1035_; lean_object* v___x_1037_; uint8_t v_isShared_1038_; uint8_t v_isSharedCheck_1042_; 
v_a_1035_ = lean_ctor_get(v___x_1007_, 0);
v_isSharedCheck_1042_ = !lean_is_exclusive(v___x_1007_);
if (v_isSharedCheck_1042_ == 0)
{
v___x_1037_ = v___x_1007_;
v_isShared_1038_ = v_isSharedCheck_1042_;
goto v_resetjp_1036_;
}
else
{
lean_inc(v_a_1035_);
lean_dec(v___x_1007_);
v___x_1037_ = lean_box(0);
v_isShared_1038_ = v_isSharedCheck_1042_;
goto v_resetjp_1036_;
}
v_resetjp_1036_:
{
lean_object* v___x_1040_; 
if (v_isShared_1038_ == 0)
{
v___x_1040_ = v___x_1037_;
goto v_reusejp_1039_;
}
else
{
lean_object* v_reuseFailAlloc_1041_; 
v_reuseFailAlloc_1041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1041_, 0, v_a_1035_);
v___x_1040_ = v_reuseFailAlloc_1041_;
goto v_reusejp_1039_;
}
v_reusejp_1039_:
{
return v___x_1040_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalLetToHave___lam__0___boxed(lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_){
_start:
{
lean_object* v_res_1052_; 
v_res_1052_ = l_Lean_Elab_Tactic_Conv_evalLetToHave___lam__0(v___y_1043_, v___y_1044_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_);
lean_dec(v___y_1050_);
lean_dec_ref(v___y_1049_);
lean_dec(v___y_1048_);
lean_dec_ref(v___y_1047_);
lean_dec(v___y_1046_);
lean_dec_ref(v___y_1045_);
lean_dec(v___y_1044_);
lean_dec_ref(v___y_1043_);
return v_res_1052_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalLetToHave(lean_object* v_x_1061_, lean_object* v_a_1062_, lean_object* v_a_1063_, lean_object* v_a_1064_, lean_object* v_a_1065_, lean_object* v_a_1066_, lean_object* v_a_1067_, lean_object* v_a_1068_, lean_object* v_a_1069_){
_start:
{
lean_object* v___x_1071_; uint8_t v___x_1072_; 
v___x_1071_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalLetToHave___closed__1));
v___x_1072_ = l_Lean_Syntax_isOfKind(v_x_1061_, v___x_1071_);
if (v___x_1072_ == 0)
{
lean_object* v___x_1073_; 
v___x_1073_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__0___redArg();
return v___x_1073_;
}
else
{
lean_object* v___f_1074_; lean_object* v___x_1075_; 
v___f_1074_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalLetToHave___closed__2));
v___x_1075_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_1074_, v_a_1062_, v_a_1063_, v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_, v_a_1068_, v_a_1069_);
return v___x_1075_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalLetToHave___boxed(lean_object* v_x_1076_, lean_object* v_a_1077_, lean_object* v_a_1078_, lean_object* v_a_1079_, lean_object* v_a_1080_, lean_object* v_a_1081_, lean_object* v_a_1082_, lean_object* v_a_1083_, lean_object* v_a_1084_, lean_object* v_a_1085_){
_start:
{
lean_object* v_res_1086_; 
v_res_1086_ = l_Lean_Elab_Tactic_Conv_evalLetToHave(v_x_1076_, v_a_1077_, v_a_1078_, v_a_1079_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_, v_a_1084_);
lean_dec(v_a_1084_);
lean_dec_ref(v_a_1083_);
lean_dec(v_a_1082_);
lean_dec_ref(v_a_1081_);
lean_dec(v_a_1080_);
lean_dec_ref(v_a_1079_);
lean_dec(v_a_1078_);
lean_dec_ref(v_a_1077_);
return v_res_1086_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLetToHave___regBuiltin_Lean_Elab_Tactic_Conv_evalLetToHave__1(){
_start:
{
lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; 
v___x_1095_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_1096_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalLetToHave___closed__1));
v___x_1097_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLetToHave___regBuiltin_Lean_Elab_Tactic_Conv_evalLetToHave__1___closed__1));
v___x_1098_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalLetToHave___boxed), 10, 0);
v___x_1099_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1095_, v___x_1096_, v___x_1097_, v___x_1098_);
return v___x_1099_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLetToHave___regBuiltin_Lean_Elab_Tactic_Conv_evalLetToHave__1___boxed(lean_object* v_a_1100_){
_start:
{
lean_object* v_res_1101_; 
v_res_1101_ = l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLetToHave___regBuiltin_Lean_Elab_Tactic_Conv_evalLetToHave__1();
return v_res_1101_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_Lets(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Conv_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Conv_Lets(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
